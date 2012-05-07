module TcTypeNatsRules where

-- From other GHC locations
import Var      ( Var, EqVar )
import TyCon    ( TyCon, tyConName )
import Coercion ( TypeNatCoAxiom (..) )
import Type     ( isNumLitTy, getTyVar_maybe, mkTyVarTy, mkNumLitTy )
import PrelNames( typeNatLeqTyFamName
                , typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                )
import Panic    ( panic )

-- From type checker
import TcRnTypes      ( Xi, Ct(..), ctId )
import TcTypeNatsEval ( minus, divide, logExact, rootExact )
import TcEvidence     ( TcCoercion (TcTypeNatCo)
                      , mkTcSymCo, mkTcTransCo, mkTcCoVarCo )

-- From base libraries
import Prelude hiding ( exp )
import Data.Maybe ( fromMaybe, maybeToList, isNothing )
import qualified Data.IntMap as IMap
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
              deriving Eq

data Rule   = Rule [(PVar,Prop)]    -- ^ Named assumptions of the rule
                   Prop             -- ^ Conclusion of the rule
                   Proof            -- ^ Proof of conclusion (uses assumptions)

data Proof  = By TypeNatCoAxiom [Term] [ Proof ]
            | Assumed PVar
            | Proved EqVar
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


toCoercion :: Proof -> TcCoercion
toCoercion proof  =
  case proof of
    By ax ts ps -> TcTypeNatCo ax (map toXi ts) (map toCoercion ps)
    Sym p       -> mkTcSymCo (toCoercion p)
    Trans p q   -> mkTcTransCo (toCoercion p) (toCoercion q)
    Proved ev   -> mkTcCoVarCo ev
    Assumed _   -> panic "Incomplete proof"

toXi :: Term -> Xi
toXi term =
  case term of
    Var _  -> panic "Incomplete term"
    Bool _ -> panic "XXX: Make boolean literal"
    Num n  -> mkNumLitTy n
    Con c  -> mkTyVarTy c


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
rule ax asmps conc
  | wellFormed = Rule as conc $ By ax (map Var $ ISet.toList vs)
                              $ map (Assumed . fst) as
  | otherwise  = panic "Malformed rule."
  where
  as          = zip [ 0 .. ] asmps
  vs          = fvs asmps

  wellFormed  = ISet.null (ISet.difference (fvs conc) vs)

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
  match _ _               = panic "matchTermTerm: unreachable"

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
usingAsmp :: Ct -> Prop -> Maybe (Subst, Proof)
usingAsmp ct q =
  do p  <- fromCt ct
     su <- match q p
     return (su, Proved (ctId ct))


-- | Try to stisfy a rule assumption with an axiom.
usingAxiom :: Prop -> Maybe (Subst, Proof)

usingAxiom (Prop op [r, Num a, Num b]) =
  do (na,ax) <- case op of
                  Add -> Just (Num  (a + b), TnAddDef a b)
                  Mul -> Just (Num  (a * b), TnMulDef a b)
                  Exp -> Just (Num  (a ^ b), TnExpDef a b)
                  Leq -> Just (Bool (a <= b), TnLeqDef a b)
                  Eq  -> Nothing

     su <- match r na
     return (su, By ax [] [])

usingAxiom (Prop op [Num r, a, Num b]) =
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
  do let mkAx ax mb = mb >>= \nb -> Just (Num nb, ax a nb)
     (nb,ax) <- case op of
                  Add -> mkAx TnAddDef (minus r a)
                  Mul -> mkAx TnMulDef (divide r a)
                  Exp -> mkAx TnExpDef (logExact r a)
                  Leq -> Nothing
                  Eq  -> Nothing

     su <- match b nb
     return (su, By ax [] [])

usingAxiom _ = Nothing


-- Currently, only using rules with no premises.
usingRule :: Rule -> Prop -> Maybe (Subst, Proof)
usingRule (Rule [] conc proof) p =
  do su <- match freshConc p
     return (su, freshProof)
  where
  (freshConc, freshProof) =
     case ISet.maxView (fvs p) of
       Just (n,_) ->
         let bump = 1 + n
         in (fresh bump conc, fresh bump proof)
       Nothing -> (conc, proof)

usingRule _ _ = Nothing


specRule :: Rule -> (Prop -> Maybe (Subst, Proof)) -> [Rule]
specRule (Rule as c proof) tactic =
  do ((n,p), rest) <- choose as
     (su, aP) <- maybeToList (tactic p)
     return $ apSubst su $ Rule rest c $ define n aP proof

--------------------------------------------------------------------------------

solve :: Ct -> Maybe TcCoercion
solve ct =
  do p <- fromCt ct
     (_, p) <- msum $ usingAxiom p : map (`usingRule` p) bRules
     return (toCoercion p)


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




