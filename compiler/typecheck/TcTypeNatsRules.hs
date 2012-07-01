module TcTypeNatsRules where

-- From other GHC locations
import Outputable ( ppr, vcat )
import SrcLoc   ( noSrcSpan )
import Var      ( Var, TyVar )
import TyCon    ( TyCon, tyConName )
import Coercion ( CoAxiomRule(..) )
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
import TysPrim  ( typeNatAddTyCon
                , typeNatMulTyCon
                , typeNatExpTyCon
                , tyVarList
                , typeNatKind
                )
import Name     ( mkSystemName )
import OccName  ( mkOccName, tcName )
import Unique   ( mkPreludeMiscIdUnique )
-- import Panic    ( panic )
import Bag      ( bagToList )

-- From type checker
import TcRnTypes      ( Xi, Ct(..), ctEvidence, ctEvTerm, isGivenCt
                      , CtEvidence(..), CtLoc(..), SkolemInfo(..)
                      , mkNonCanonical
                      )
import TcTypeNatsEval ( minus, divide, logExact, rootExact )
import TcEvidence     ( EvTerm(..)
                      , mkTcSymCo, mkTcTransCo
                      , evTermCoercion
                      , TcCoercion(TcTypeNatCo)
                      )
import TcSMonad ( TcS, InertSet
                , getTcSInerts, inert_cans, inert_funeqs
                , updWorkListTcS, appendWorkListCt
                , traceTcS
                , partCtFamHeadMap
                )

-- From base libraries
import Prelude hiding ( exp )
import Data.Maybe ( isNothing, mapMaybe )
import Data.List  ( sortBy )
import Data.Ord   ( comparing )
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




{-
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
-}

--------------------------------------------------------------------------------

solve :: Ct -> Maybe EvTerm
solve ct = msum $ solveWithAxiom ct : map (`solveWithRule` ct) bRules


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
  mkAxName x = mkSystemName unboundKey (mkOccName tcName x)

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
  where mk = TcTypeNatCo

--------------------------------------------------------------------------------

axName :: String -> Integer -> Integer -> String
axName x a b = x ++ "_" ++ show a ++ "_" ++ show b

axAddDef :: Integer -> Integer -> CoAxiomRule
axAddDef a b = mkAx 1 (axName "AddDef" a b) [] []
             (mkAdd (mkNumLitTy a) (mkNumLitTy b)) (mkNumLitTy (a + b))

axMulDef :: Integer -> Integer -> CoAxiomRule
axMulDef a b = mkAx 2 (axName "MulDef" a b) [] []
             (mkMul (mkNumLitTy a) (mkNumLitTy b)) (mkNumLitTy (a * b))

axExpDef :: Integer -> Integer -> CoAxiomRule
axExpDef a b = mkAx 3 (axName "ExpDef" a b) [] []
             (mkExp (mkNumLitTy a) (mkNumLitTy b)) (mkNumLitTy (a ^ b))


-- XXX: We should be able to cope with some assumptions in backward
-- reasoning too.
bRules :: [CoAxiomRule]
bRules =
  [ bRule 10 "Add0L" (mkAdd n0 a) a
  , bRule 11 "Add0R" (mkAdd a n0) a

  , bRule 12 "Mul0L" (mkMul n0 a) n0
  , bRule 13 "Mul0R" (mkMul a n0) n0
  , bRule 14 "Mul1L" (mkMul n1 a) a
  , bRule 15 "Mul1R" (mkMul a n1) a

  -- TnExp0L
  , bRule 17 "TnExp0R" (mkExp a n0) n1
  , bRule 18 "TnExp1L" (mkExp n1 a) n1
  , bRule 19 "TnExp1R" (mkExp a n1) a
  ]
  where
  bRule x y = mkAx x y (take 1 natVars) []
  a : _     = map mkTyVarTy natVars
  n0        = mkNumLitTy 0
  n1        = mkNumLitTy 1




axAddComm :: CoAxiomRule
axAddComm = mkAx 30 "AddComm" (take 3 natVars) [ (mkAdd a b, c) ] (mkAdd b a) c
  where a : b : c : _ = map mkTyVarTy natVars


theRules :: [CoAxiomRule]
theRules = []



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


byAxiom (TPOther ty, TPOther tp3)
  | Just (tc,[tp1,tp2]) <- splitTyConApp_maybe ty
  , Just a <- isNumLitTy tp1
  , Just b <- isNumLitTy tp2
  , Just c <- isNumLitTy tp3
  = do (ax,op) <- case tyConName tc of
                    n | n == typeNatAddTyFamName -> Just (axAddDef, (+))
                      | n == typeNatMulTyFamName -> Just (axMulDef, (*))
                      | n == typeNatExpTyFamName -> Just (axExpDef, (^))
                    _ -> Nothing
       guard (op a b == c)
       return ([], useAxiom (ax a b) [] [])

byAxiom _ = Nothing


{- A (possibly over-compliacted) example illustrating how the
order in which we do the matching for the assumptions makes a difference
to the conlusion of the rule.  I am not sure that at present we have rules
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



solveWithRule :: CoAxiomRule -> Ct -> Maybe EvTerm
solveWithRule r ct =
  do guard $ null $ co_axr_asmps r    -- Currently we just use simple axioms.
     let vs  = co_axr_tvs r
         lhs = toTypePat vs $ co_axr_lhs r
         rhs = toTypePat vs $ co_axr_rhs r
     (su,_) <- byAsmp ct (lhs,rhs)    -- Just for the instantiation
     tys <- mapM (`lookup` su) vs
     return (useAxiom r tys [])

solveWithAxiom :: Ct -> Maybe EvTerm
solveWithAxiom (CFunEqCan { cc_fun = tc, cc_tyargs = ts, cc_rhs = t }) =
  do ([],ev) <- byAxiom (TPOther (mkTyConApp tc ts), TPOther t)
     return ev
solveWithAxiom _ = Nothing

--------------------------------------------------------------------------------

data ActiveRule = AR
  { proof     :: [Type] -> [EvTerm] -> EvTerm
  , doneTys   :: [TypePat]
  , doneArgs  :: [(Int,EvTerm)]

  , todoArgs  :: [(Int,(TypePat,TypePat))]
    {- todoArgs ==
        [ (n, (cvt t1, cvt t2))
            | (n,(t1,t2)) <- zip [ 0 .. ] (co_axr_asmps axRule)
            , n `notElem` map fst doneArgs
            , let cvt = apSimpSubst doneArgs . toTypePat (co_axr_tvs axRule)
        ]
    -}

  , concl    :: (TypePat,TypePat)
  }


activate :: CoAxiomRule -> ActiveRule
activate r = AR
  { proof     = useAxiom r
  , doneTys   = map TPVar vs
  , doneArgs  = []
  , todoArgs  = zip [ 0 .. ] [ (cvt t1, cvt t2) | (t1,t2) <- co_axr_asmps r ]
  , concl     = (cvt (co_axr_lhs r), cvt (co_axr_rhs r))
  }
  where cvt = toTypePat vs
        vs  = co_axr_tvs r

-- p: a + b ~ c1, q: a + b ~ c2
-- sym p `trans` q
funRule :: TyCon -> ActiveRule
funRule tc = AR
  { proof     = \_ [p,q] -> EvCoercion
                          $ mkTcTransCo (mkTcSymCo $ evTermCoercion p)
                                        (evTermCoercion q)
  , doneTys   = map TPVar [ a, b, c1, c2 ]
  , doneArgs  = []
  , todoArgs  = [ (0, (TPCon tc [ TPVar a, TPVar b], TPVar c1))
                , (1, (TPCon tc [ TPVar a, TPVar b], TPVar c2)) ]
  , concl     = (TPVar c1, TPVar c2)
  }
  where a : b : c1 : c2 : _ = natVars


{- Check if the `ActiveRule` is completely instantiated and, if so,
compute the resulting equation and the evidence for it. -}
fireRule :: ActiveRule -> Maybe (EvTerm, Type, Type)
fireRule r =
  do guard $ null $ todoArgs r
     let (t1,t2) = concl r

     ts <- mapM cvt (doneTys r)
     lhs <- cvt t1
     rhs <- cvt t2
     let evs = map snd $ sortBy (comparing fst) $ doneArgs r

     return (proof r ts evs, lhs, rhs)

  where cvt (TPOther t) = Just t
        cvt _           = Nothing


-- Define one of the arguments of an active rule.
setArg :: Int -> (SimpleSubst, EvTerm) -> ActiveRule -> ActiveRule
setArg n (su,ev) r =
  AR { proof     = proof r
     , doneTys   = apSimpSubst su (doneTys r)
     , doneArgs  = (n,ev) : doneArgs r
     , todoArgs  = dropTodo (todoArgs r)
     , concl     = apSimpSubst su (concl r)
     }
  where
  -- Drop a solved argment, and instantiate the rest appropriately.
  dropTodo ((x,_) : rest)
    | n == x               = [ (x, apSimpSubst su eq) | (x,eq) <- rest ]
  dropTodo ((x,eq) : rest) = (x, apSimpSubst su eq) : dropTodo rest
  dropTodo []              = []


-- Try to solve one of the assumptions by axiom.
applyAxiom1 :: ActiveRule -> Maybe ActiveRule
applyAxiom1 r = msum $ map attempt $ todoArgs r
  where
  attempt (n,eq) = do soln <- byAxiom eq
                      return (setArg n soln r)

-- Try to satisfy some of the rule's assumptions by axiom.
applyAxiom :: ActiveRule -> ActiveRule
applyAxiom r = maybe r applyAxiom (applyAxiom1 r)

{- The various ways in which as assumption fits the arguments of a rule.
Note: currently, we use an assumption at most once per rule.
For example, assumption `p` will not make instantiations like `R(p,p)`.
-}
applyAsmp :: ActiveRule -> Ct -> [ActiveRule]
applyAsmp r ct =
  do -- Find places where this constraint might fit
     (n,soln) <- mapMaybe attempt (todoArgs r)
     return (setArg n soln r)
  where
  attempt (n,eq) = do ok <- byAsmp ct eq
                      return (n,ok)

interactActiveRules :: [ActiveRule] -> [Ct] -> [(EvTerm,Type,Type)]
interactActiveRules rs [] = mapMaybe fireRule rs
interactActiveRules rs (c : cs) = interactActiveRules newRs cs
  where
  newRs = [ r2 | r1 <- rs, r2 <- applyAsmp (applyAxiom r1) c ]

mkGivenCt :: (EvTerm,Type,Type) -> Ct
mkGivenCt (ev,t1,t2) = mkNonCanonical $
  Given { ctev_gloc = CtLoc UnkSkol noSrcSpan [] -- XXX: something better?
        , ctev_pred = mkEqPred t1 t2
        , ctev_evtm = ev
        }

-- Get the facts that are known for sure.
-- Note: currently we do not use the solved ones but we probably should.
getFacts :: TcS [Ct]
getFacts =
  do is <- getTcSInerts
     return $ bagToList $ fst $ partCtFamHeadMap isGivenCt
                              $ inert_funeqs $ inert_cans is

computeNewGivenWork :: Ct -> TcS ()
computeNewGivenWork ct =
  do asmps <- getFacts
     let active  = concatMap (`applyAsmp` ct) (map activate theRules)
         newWork = map mkGivenCt $ interactActiveRules active asmps
     traceTcS "TYPE NAT SOLVER NEW GIVENS:" (vcat $ map ppr newWork)
     updWorkListTcS (appendWorkListCt newWork)











