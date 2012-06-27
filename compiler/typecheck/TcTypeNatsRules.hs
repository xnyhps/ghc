module TcTypeNatsRules where

-- From other GHC locations
import Outputable ( ppr, vcat )
import SrcLoc   ( noSrcSpan )
import Var      ( Var, TyVar )
import TyCon    ( TyCon, tyConName )
import Coercion ( TypeNatCoAxiom (..), CoAxiomRule(..) )
import Type     ( Type, isNumLitTy, getTyVar_maybe, mkTyVarTy, mkNumLitTy
                , mkEqPred, mkTyConApp
                , splitTyConApp_maybe
                , eqType
                )
import PrelNames( typeNatLeqTyFamName
                , typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                , unboundKey
                )
import TysPrim  ( typeNatLeqTyCon
                , typeNatAddTyCon
                , typeNatMulTyCon
                , typeNatExpTyCon
                , tyVarList
                , typeNatKind
                )
import Name     ( mkInternalName )
import OccName  ( mkOccName, tcName )
import Unique   ( mkPreludeMiscIdUnique )
import Panic    ( panic )

-- From type checker
import TcType         ( TcPredType )
import TcRnTypes      ( Xi, Ct(..), ctEvidence, ctEvTerm, isGivenCt
                      , CtEvidence(..), CtLoc(..), SkolemInfo(..)
                      , mkNonCanonical
                      )
import TcTypeNatsEval ( minus, divide, logExact, rootExact )
import TcEvidence     ( EvTerm(..), TcCoercion (..)
                      , mkTcSymCo, mkTcTransCo
                      , evTermCoercion
                      )
import TcSMonad ( TcS, InertSet
                , getTcSInerts, foldFamHeadMap, inert_cans, inert_funeqs
                , updWorkListTcS, appendWorkListCt
                , traceTcS
                )

-- From base libraries
import Prelude hiding ( exp )
import Data.Maybe ( fromMaybe, maybeToList, listToMaybe, isNothing, catMaybes )
import qualified Data.IntMap as IMap
import qualified Data.Map    as Map
import qualified Data.IntSet as ISet
import Control.Monad ( msum, guard )


type TVar   = Int           -- ^ Names a term
type PVar   = Int           -- ^ Names a proof

data Term   = Var  !TVar    -- ^ Matches anything
            | Num  !Integer -- ^ Matches the given number constant
            | Bool !Bool    -- ^ Matches the given boolean constant
            | Con  !Var     -- ^ Matches a GHC variable (uninterpreted constant)
              deriving Eq

-- For functions, the result comes first:
-- For example `a + b ~ x` is represented as `Prop Add [x,a,b]`
-- XXX: This makes matching bellow a bit simpler, but maybe it is more confusing
-- than helpful?
data Prop   = Prop Op [Term]
data Op     = Eq | Leq | Add | Mul | Exp
              deriving (Eq,Ord)

data Rule   = Rule [(PVar,Prop)]    -- Named assumptions of the rule
                   Prop             -- Conclusion of the rule
                   Proof            -- Proof of conclusion (uses assumptions)

data Proof  = By TypeNatCoAxiom [Term] [ Proof ]
            | Assumed PVar
            | Proved EvTerm
            | Sym Proof | Trans Proof Proof   -- used in `funRule`

eq :: Term -> Term -> Prop
eq x y = Prop Eq [ x, y ]

leq :: Term -> Term -> Prop
leq x y = Prop Leq [ Bool True, x, y ]

add :: Term -> Term -> Term -> Prop
add x y z = Prop Add [ z, x, y ]

mul :: Term -> Term -> Term -> Prop
mul x y z = Prop Mul [ z, x, y ]

exp :: Term -> Term -> Term -> Prop
exp x y z = Prop Exp [ z, x, y ]





--------------------------------------------------------------------------------
fromXi :: Xi -> Maybe Term
fromXi t = msum [ Con `fmap` getTyVar_maybe t, Num `fmap` isNumLitTy t ]

fromCt :: Ct -> Maybe Prop
fromCt (CFunEqCan { cc_fun = tc, cc_tyargs = ts, cc_rhs = t }) =
  do o  <- op
     x  <- fromXi t
     xs <- mapM fromXi ts
     return (Prop o (x : xs))
  where
  op = case tyConName tc of
         name | name == typeNatAddTyFamName -> Just Add
              | name == typeNatMulTyFamName -> Just Mul
              | name == typeNatExpTyFamName -> Just Exp
              | name == typeNatLeqTyFamName -> Just Leq
              | otherwise                   -> Nothing

fromCt (CTyEqCan { cc_tyvar = x, cc_rhs = t }) =
  do y <- fromXi t
     return (Prop Eq [ Con x, y ])

fromCt _ = Nothing

toTcPredTy :: Prop -> TcPredType
toTcPredTy (Prop op ts) =
  case (op, map toXi ts) of
    (Eq,  [t1,t2])    -> mkEqPred t1 t2
    (Leq, [t1,t2,t3]) -> mkEqPred (mk typeNatLeqTyCon t2 t3) t1
    (Add, [t1,t2,t3]) -> mkEqPred (mk typeNatAddTyCon t2 t3) t1
    (Mul, [t1,t2,t3]) -> mkEqPred (mk typeNatMulTyCon t2 t3) t1
    (Exp, [t1,t2,t3]) -> mkEqPred (mk typeNatExpTyCon t2 t3) t1
    _                 -> panic "toTcPredTy: Unexpected Prop"
  where
  mk f a b = mkTyConApp f [a,b]

toEvTerm :: Proof -> EvTerm
toEvTerm proof  =
  case proof of
    By ax ts ps -> EvCoercion $ TcTypeNatCo ax (map toXi ts) (map toCoercion ps)
    Sym p       -> EvCoercion $ mkTcSymCo (toCoercion p)
    Trans p q   -> EvCoercion $ mkTcTransCo (toCoercion p) (toCoercion q)
    Proved t    -> t
    Assumed _   -> panic "Incomplete proof"

toCoercion :: Proof -> TcCoercion
toCoercion = evTermCoercion . toEvTerm

toXi :: Term -> Xi
toXi term =
  case term of
    Var _  -> panic "Incomplete term"
    Bool _ -> panic "XXX: Make boolean literal"
    Num n  -> mkNumLitTy n
    Con c  -> mkTyVarTy c


{- While the resulting constraints are mostly in canonical form,
sometimes they are not:  for example, we might get new work like this:

2 ~ 3

This indicates that someone gave us an inconsistent context,
and will be detected on the next iteration of the solver.
-}
toGivenCt :: (Proof,Prop) -> Ct
toGivenCt (proof,prop) = mkNonCanonical $
  Given { ctev_gloc = CtLoc UnkSkol noSrcSpan [] -- XXX: something better?
        , ctev_pred = toTcPredTy prop
        , ctev_evtm = toEvTerm proof
        }


--------------------------------------------------------------------------------



--------------------------------------------------------------------------------

-- XXX: We should be able to cope with some assumptions in backward
-- reasoning too.
bRules :: [Rule]
bRules = map (uncurry simpleRule)
  [ (TnLeq0    , leq n0 a)
  , (TnLeqRefl , leq a a)

  , (TnAdd0L   , add n0 a a)
  , (TnAdd0R   , add a n0 a)

  , (TnMul0L   , mul n0 a n0)
  , (TnMul0R   , mul a n0 n0)
  , (TnMul1L   , mul n1 a a)
  , (TnMul1R   , mul a n1 a)

  -- TnExp0L
  , (TnExp0R   , exp a n0 n1)
  , (TnExp1L   , exp n1 a n1)
  , (TnExp1R   , exp a n1 a)
  ]
  where a  = Var 0
        n0 = Num 0
        n1 = Num 1


fRules :: [Rule]
fRules =
  map funRule [ Add, Mul, Exp, Leq ]
  ++
  [ rule TnLeqASym    [ leq a b, leq b a ] $ eq a b
  , rule TnLeqTrans   [ leq a b, leq b c ] $ leq a c

  , rule TnAddComm    [ add a b c ] $ add b a c
  , rule TnMulComm    [ mul a b c ] $ mul b a c

  , rule TnAddCancelL [           add a b1 c, add a b2 c ] $ eq b1 b2
  , rule TnMulCancelL [ leq n1 a, mul a b1 c, mul a b2 c ] $ eq b1 b2
  , rule TnExpCancelL [ leq n2 a, exp a b1 c, exp a b2 c ] $ eq b1 b2

  , rule TnAddCancelR [           add a1 b c, add a2 b c ] $ eq a1 a2
  , rule TnMulCancelR [ leq n1 b, mul a1 b c, mul a2 b c ] $ eq a1 a2
  , rule TnExpCancelR [ leq n1 b, exp a1 b c, exp a2 b c ] $ eq a1 a2
  ]
  where
  a : a1 : a2 : b : b1 : b2 : c : _ = map Var [ 0 .. ]
  n1 = Num 1
  n2 = Num 2



-- | A smart constructor for easier rule constrction.
rule :: TypeNatCoAxiom -> [Prop] -> Prop -> Rule
rule ax asmps conc = Rule as conc $ By ax (map Var $ ISet.toList vs)
                                  $ map (Assumed . fst) as
  where
  as          = zip [ 0 .. ] asmps
  vs          = fvs asmps

simpleRule :: TypeNatCoAxiom -> Prop -> Rule
simpleRule ax p = rule ax [] p

{- This slightly duplicates the functionality of GHC's solver but
we have it here so that it can react with axioms.
For example, the following is justified using a fun-rule and an axiom:

(5 + 3 ~ x) => (x ~ 8)
like this:
(5 + 3 ~ x, 5 + 3 ~ 8) => (x ~ 8)
-}

-- p: a + b ~ c1, q: a + b ~ c2
-- sym p `trans` q
funRule :: Op -> Rule
funRule op = Rule [ (p, Prop op [ c1, a, b]), (q, Prop op [ c2, a, b ]) ]
                  (eq c1 c2)
                  (Trans (Sym (Assumed p)) (Assumed q))
  where a : b : c1 : c2 : _ = map Var [ 0 .. ]
        p : q : _           = [ 0 .. ]


--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
class ApSubst t => Match t where
  match :: t -> t -> Maybe Subst

instance Match Term where
  match t1 t2 | t1 == t2  = return IMap.empty
  match (Var a) t         = return (IMap.singleton a t)
  match t (Var a)         = return (IMap.singleton a t)
  match _ _               = Nothing

instance Match t => Match [t] where
  match [] [] = return IMap.empty
  match (x : xs) (y : ys) = do su1 <- match x y
                               su2 <- match (apSubst su1 xs) (apSubst su1 ys)
                               return (IMap.union su1 su2)
  match _ _ = Nothing

instance Match Prop where
  match (Prop x xs) (Prop y ys) = guard (x == y) >> match xs ys





--------------------------------------------------------------------------------


-- | Try to satisfy a rule assumption with an existing constraint.
usingCt :: Ct -> Prop -> [(Subst, Proof)]
usingCt ct q =
  maybeToList $
  do p  <- fromCt ct
     su <- match q p
     return (su, Proved $ ctEvTerm $ ctEvidence ct)

-- Assumes that the proof came from the inert set, and so it
-- contains no rule variables.
usingAsmps :: Asmps -> Prop -> [(Subst, Proof)]
usingAsmps asmps (Prop op ts) =
  do (proof,ts1) <- asmpsFor op asmps
     su <- maybeToList $ match ts ts1
     return (su, Proved proof)


-- | Try to stisfy a rule assumption with an axiom.
usingAxiom :: Prop -> [(Subst, Proof)]

usingAxiom (Prop op [r, Num a, Num b]) =
  maybeToList $
  do (na,ax) <- case op of
                  Add -> Just (Num  (a + b), TnAddDef a b)
                  Mul -> Just (Num  (a * b), TnMulDef a b)
                  Exp -> Just (Num  (a ^ b), TnExpDef a b)
                  Leq -> Just (Bool (a <= b), TnLeqDef a b)
                  Eq  -> Nothing

     su <- match r na
     return (su, By ax [] [])

usingAxiom (Prop op [Num r, a, Num b]) =
  maybeToList $
  do let mkAx ax mb = mb >>= \na -> Just (Num na, ax na b)
     (na,ax) <- case op of
                  Add -> mkAx TnAddDef (minus r b)
                  Mul -> mkAx TnMulDef (divide r b)
                  Exp -> mkAx TnExpDef (rootExact r b)
                  Leq -> Nothing
                  Eq  -> Nothing

     su <- match a na
     return (su, By ax [] [])

usingAxiom (Prop op [Num r, Num a, b]) =
  maybeToList $
  do let mkAx ax mb = mb >>= \nb -> Just (Num nb, ax a nb)
     (nb,ax) <- case op of
                  Add -> mkAx TnAddDef (minus r a)
                  Mul -> mkAx TnMulDef (divide r a)
                  Exp -> mkAx TnExpDef (logExact r a)
                  Leq -> Nothing
                  Eq  -> Nothing

     su <- match b nb
     return (su, By ax [] [])

usingAxiom _ = []


-- Currently, only using rules with no premises.
usingRule :: Rule -> Prop -> [(Subst, Proof)]
usingRule (Rule [] conc proof) p =
  maybeToList $
  do su <- match freshConc p
     return (su, freshProof)
  where
  (freshConc, freshProof) =
     case ISet.maxView (fvs p) of
       Just (n,_) ->
         let bump = 1 + n
         in (fresh bump conc, fresh bump proof)
       Nothing -> (conc, proof)

usingRule _ _ = []


specRule :: Rule -> (Prop -> [(Subst, Proof)]) -> [Rule]
specRule (Rule as c proof) tactic =
  do ((n,p), rest) <- choose as
     (su, aP)      <- tactic p
     return $ apSubst su $ Rule rest c $ define n aP proof


fireRules :: Asmps -> Ct -> [(Proof,Prop)]
fireRules asmps newFact = loop []
                        $ concatMap (`specRule` usingCt newFact) fRules
  where
  step r  = specRule r usingAxiom
         ++ [ r1 | b <- bRules, r1 <- specRule r (usingRule b) ]
         ++ [ r1 | r1 <- specRule r (usingAsmps asmps) ]

  loop done (Rule [] p proof : more) = loop ((proof,p) : done) more
  loop done (r : more)               = loop done (step r ++ more)
  loop done []                       = done


type Asmps = Map.Map Op [ (EvTerm, [Term]) ]

asmpsFor :: Op -> Asmps -> [ (EvTerm, [Term]) ]
asmpsFor op asmps = Map.findWithDefault [] op asmps

toAsmps :: Bool -> InertSet -> Asmps
toAsmps alsoWanted = foldFamHeadMap addAsmp Map.empty
                   . inert_funeqs
                   . inert_cans
  where
  addAsmp ct as = fromMaybe as $
                  do guard (isGivenCt ct || alsoWanted)
                     Prop op ts <- fromCt ct
                     let fact = (ctEvTerm (ctEvidence ct), ts)
                     return $ Map.insertWith (++) op [fact] as

computeNewGivenWork :: Ct -> TcS ()
computeNewGivenWork ct =
  do is <- getTcSInerts
     let newWork = map toGivenCt $ fireRules (toAsmps False is) ct
     traceTcS "TYPE NAT SOLVER NEW GIVENS:" (vcat $ map ppr newWork)
     updWorkListTcS (appendWorkListCt newWork)


--------------------------------------------------------------------------------

solve :: Ct -> Maybe EvTerm
solve ct =
  do p <- fromCt ct
     (_, p) <- listToMaybe $ msum $ usingAxiom p : map (`usingRule` p) bRules
     return (toEvTerm p)


impossible :: Ct -> Bool

impossible ct =
  case fromCt ct of
    Nothing   -> False
    Just prop ->
      case prop of
        Prop Leq [ Bool c, Num a, Num b ] -> c /= (a <= b)

        Prop Add [ Num c, Num a, _     ] -> isNothing (minus c a)
        Prop Add [ Num c, _    , Num b ] -> isNothing (minus c b)

        Prop Mul [ Num c, Num 0, _     ] -> not (c == 0)
        Prop Mul [ Num c, Num a, _     ] -> isNothing (divide c a)
        Prop Mul [ Num c, _    , Num 0 ] -> not (c == 0)
        Prop Mul [ Num c, _    , Num b ] -> isNothing (divide c b)

        Prop Exp [ Num c, Num 0, _     ] -> not (c == 0 || c == 1)
        Prop Exp [ Num c, Num 1, _     ] -> not (c == 1)
        Prop Exp [ Num c, Num a, _     ] -> isNothing (logExact c a)
        Prop Exp [ Num c, _    , Num 0 ] -> not (c == 1)
        Prop Exp [ Num c, _    , Num b ] -> isNothing (rootExact c b)

        _                                -> False



--------------------------------------------------------------------------------
type Subst  = IMap.IntMap Term  -- ^ Maps TVars to Terms

class ApSubst t where
  apSubst :: Subst -> t -> t

instance ApSubst t => ApSubst [t] where
  apSubst su ts             = map (apSubst su) ts

instance ApSubst Term where
  apSubst su term           = case term of
                                Var a -> fromMaybe term (IMap.lookup a su)
                                _     -> term

instance ApSubst Prop where
  apSubst su (Prop op ts)   = Prop op (apSubst su ts)

instance ApSubst Rule where
  apSubst su (Rule as c p)  = Rule [ (n, apSubst su a) | (n,a) <- as ]
                                   (apSubst su c) (apSubst su p)

instance ApSubst Proof where
  apSubst su (By ax ts ps)  = By ax (apSubst su ts) (apSubst su ps)
  apSubst _ (Proved v)      = Proved v
  apSubst _ (Assumed n)     = Assumed n
  apSubst su (Sym p)        = Sym (apSubst su p)
  apSubst su (Trans p q)    = Trans (apSubst su p) (apSubst su q)


-- | Define an assumption paramater in the proof of a rule.
define :: PVar -> Proof -> Proof -> Proof
define n p (Assumed m) | n == m   = p
define n p (By ax ts ps)          = By ax ts (map (define n p) ps)
define n p (Sym q)                = Sym (define n p q)
define n p (Trans q r)            = Trans (define n p q) (define n p r)
define _ _ p                      = p


-- Consider each element of the list (and the rest)
choose :: [a] -> [(a,[a])]
choose []       = []
choose (a : as) = (a, as) : [ (b, a : bs) | (b,bs) <- choose as ]


class FVS t where
  fvs :: t -> ISet.IntSet

instance FVS Term where
  fvs (Var x)     = ISet.singleton x
  fvs _           = ISet.empty

instance FVS t => FVS [t] where
  fvs ts          = ISet.unions (map fvs ts)

instance FVS Prop where
  fvs (Prop _ ts) = fvs ts


-- ^ Increments all variables, to get a fresh instance of something.
class Fresh t where
  fresh :: Int -> t -> t

instance Fresh Term where
  fresh n (Var x)       = Var (n + x)
  fresh _ t             = t

instance Fresh t => Fresh [t] where
  fresh n ts            = map (fresh n) ts

instance Fresh Prop where
  fresh n (Prop op ts)  = Prop op (fresh n ts)

instance Fresh Proof where
  fresh n proof =
    case proof of
      Sym p       -> Sym (fresh n p)
      Trans p q   -> Trans (fresh n p) (fresh n q)
      Proved x    -> Proved x
      Assumed x   -> Assumed x
      By a ts ps  -> By a (fresh n ts) (fresh n ps)



--------------------------------------------------------------------------------

mkAx :: Int -> String -> [TyVar] -> [(Type,Type)] -> Type -> Type -> CoAxiomRule
mkAx u n vs asmps lhs rhs = CoAxiomRule
  { co_axr_unique = mkAxUique u
  , co_axr_name   = mkAxName n
  , co_axr_tvs    = vs
  , co_axr_asmps  = asmps
  , co_axr_lhs    = lhs
  , co_axr_rhs    = rhs
  }
  where
  mkAxUique  = mkPreludeMiscIdUnique
  mkAxName x = mkInternalName unboundKey (mkOccName tcName x) noSrcSpan

mkAdd :: Type -> Type -> Type
mkAdd a b = mkTyConApp typeNatAddTyCon [a,b]

mkMul :: Type -> Type -> Type
mkMul a b = mkTyConApp typeNatMulTyCon [a,b]

mkExp :: Type -> Type -> Type
mkExp a b = mkTyConApp typeNatExpTyCon [a,b]

natVars :: [TyVar]
natVars = tyVarList typeNatKind


useAxiom :: CoAxiomRule -> [Type] -> [EvTerm] -> EvTerm
useAxiom ax ts ps = EvCoercion $ mk ax ts (map evTermCoercion ps)
  -- XXX: Change this after changing the constructor in "Coercion"
  where mk = undefined

--------------------------------------------------------------------------------

axAddDef :: Integer -> Integer -> CoAxiomRule
axAddDef a b = mkAx 1 "AddDef" [] []
             (mkAdd (mkNumLitTy a) (mkNumLitTy b)) (mkNumLitTy (a + b))

axMulDef :: Integer -> Integer -> CoAxiomRule
axMulDef a b = mkAx 2 "MulDef" [] []
             (mkMul (mkNumLitTy a) (mkNumLitTy b)) (mkNumLitTy (a * b))

axExpDef :: Integer -> Integer -> CoAxiomRule
axExpDef a b = mkAx 3 "ExpDef" [] []
             (mkExp (mkNumLitTy a) (mkNumLitTy b)) (mkNumLitTy (a ^ b))

axAddComm :: CoAxiomRule
axAddComm = mkAx 10 "AddComm" (take 3 natVars) [ (mkAdd a b, c) ] (mkAdd b a) c
  where a : b : c : _ = map mkTyVarTy natVars




--------------------------------------------------------------------------------

type SimpleSubst = [ (TyVar, Type) ]
data TypePat     = TPVar TyVar | TPCon TyCon [TypePat] | TPOther Type
type Eqn         = (TypePat, TypePat)

tpCon :: TyCon -> [TypePat] -> TypePat
tpCon tc tps = case check tps of
                 Just ts  -> TPOther $ mkTyConApp tc ts
                 Nothing  -> TPCon tc tps
  where
  check (TPOther x : xs)  = do ys <- check xs
                               return (x : ys)
  check (_ : _)           = Nothing
  check []                = return []



toTypePat :: [TyVar] -> Type -> TypePat
toTypePat as ty
  | Just x <- getTyVar_maybe ty, x `elem` as  = TPVar x
toTypePat as ty
  | Just (tc,ts) <- splitTyConApp_maybe ty = tpCon tc (map (toTypePat as) ts)
toTypePat _ ty  = TPOther ty    -- assumes no variables here.

-- Check to see if a type  macthes a type pattern.
matchType :: TypePat -> Type -> Maybe SimpleSubst
matchType (TPVar x) t2 = return [(x,t2)]
matchType (TPCon tc1 ts1) t2
  | Just (tc2,ts2) <- splitTyConApp_maybe t2
    = guard (tc1 == tc2) >> matchTypes ts1 ts2
matchType (TPOther t1) t2
  | eqType t1 t2  = return []
matchType _ _ = Nothing


-- Match a list of patterns agains a list of types.
matchTypes :: [TypePat] -> [Type] -> Maybe SimpleSubst
matchTypes [] []              = Just []
matchTypes (x : xs) (y : ys)  =
  do su1 <- matchType x y
     su2 <- matchTypes (apSimpSubst su1 xs) ys
     return (su1 ++ su2)
matchTypes _ _                = Nothing



class AppSimpSubst t where
  apSimpSubst :: SimpleSubst -> t -> t

instance AppSimpSubst a => AppSimpSubst [a] where
  apSimpSubst su = map (apSimpSubst su)

instance (AppSimpSubst a, AppSimpSubst b) => AppSimpSubst (a,b) where
  apSimpSubst su (x,y) = (apSimpSubst su x, apSimpSubst su y)

instance AppSimpSubst TypePat where
  apSimpSubst su t@(TPVar x)   = case lookup x su of
                                   Just t1 -> TPOther t1
                                   Nothing -> t
  apSimpSubst su (TPCon tc ts) = tpCon tc (apSimpSubst su ts)
  apSimpSubst _ t@(TPOther {}) = t


type Solver = Eqn -> Maybe (SimpleSubst, EvTerm)

-- Tries to instantuate the equation with the constraint.
byAsmp :: Ct -> Solver

byAsmp ct@(CFunEqCan { cc_fun = tc, cc_tyargs = ts, cc_rhs = t }) (lhs,rhs) =
  do su <- matchTypes [lhs, rhs] [ mkTyConApp tc ts, t ]
     return (su, ctEvTerm (ctEvidence ct))

byAsmp ct@(CTyEqCan { cc_tyvar = x, cc_rhs = t }) (lhs,rhs) =
  do su <- matchTypes [lhs, rhs] [ mkTyVarTy x, t ]
     return (su, ctEvTerm (ctEvidence ct))

byAsmp _ _ = Nothing



-- Check if we can solve the equation using one of the family of axioms.
byAxiom :: Solver

byAxiom (TPOther ty, TPVar r)
  | Just (tc,[tp1,tp2]) <- splitTyConApp_maybe ty
  , Just a <- isNumLitTy tp1, Just b <- isNumLitTy tp2

  = do (ax,op) <- case tyConName tc of
                    name | name == typeNatAddTyFamName -> Just (axAddDef, (+))
                         | name == typeNatMulTyFamName -> Just (axMulDef, (*))
                         | name == typeNatExpTyFamName -> Just (axExpDef, (^))
                    _ -> Nothing

       return ( [ (r, mkNumLitTy (op a b)) ], useAxiom (ax a b) [] [] )


byAxiom (TPCon tc [TPVar r,TPOther tp1], TPOther tp2)
  | Just b <- isNumLitTy tp1, Just c <- isNumLitTy tp2

  = do (ax,op) <- case tyConName tc of
                    n | n == typeNatAddTyFamName -> Just (axAddDef, minus)
                      | n == typeNatMulTyFamName -> Just (axMulDef, divide)
                      | n == typeNatExpTyFamName -> Just (axExpDef, rootExact)
                    _ -> Nothing
       a <- op c b
       return ( [ (r, mkNumLitTy a) ], useAxiom (ax a b) [] [] )


byAxiom (TPCon tc [TPOther tp1, TPVar r], TPOther tp2)
  | Just a <- isNumLitTy tp1, Just c <- isNumLitTy tp2

  = do (ax,op) <- case tyConName tc of
                    n | n == typeNatAddTyFamName -> Just (axAddDef, minus)
                      | n == typeNatMulTyFamName -> Just (axMulDef, divide)
                      | n == typeNatExpTyFamName -> Just (axExpDef, logExact)
                    _ -> Nothing
       b <- op c a
       return ([ (r, mkNumLitTy b) ], useAxiom (ax a b) [] [] )

byAxiom _ = Nothing


solveEqn :: [Ct] -> Eqn -> [(SimpleSubst, EvTerm)]
solveEqn cts ax = catMaybes (byAxiom ax : map (`byAsmp` ax) cts)

{- A (possibly over-compliacted) example illustrating how the
order in which we do the matching for the assumptions makes a difference
to the concusion of the rule.  I am not sure that at present we have rules
that are as complex.


asmps:
G: 2 + p = q1
G: 3 + p = q2

rule:
a ^ b = c, a + p = q1, b + p = q2, c + y = 10 => P ...

P { a = 2, b = 3, c = 8, y = 2 }
P { a = 3, b = 2, c = 9, y = 1 }
P { a = 2, b = 2, c = 4, y = 6 }
-}





