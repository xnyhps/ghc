module TcTypeNats where

import TcSMonad( TcS, emitFrozenError, setEvBind )
import TcCanonical( StopOrContinue(..) )
import TcRnTypes( Ct(..), isGiven, isWanted, ctEvidence, ctEvId )

import TcTypeNatsRules( bRules, theRules, axAddDef, axMulDef, axExpDef, natVars)

import PrelNames( typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                )

import Outputable ( ppr, vcat )
import SrcLoc   ( noSrcSpan )
import Var      ( TyVar )
import TyCon    ( TyCon, tyConName )
import Coercion ( CoAxiomRule(..) )
import Type     ( Type, isNumLitTy, getTyVar_maybe, mkTyVarTy, mkNumLitTy
                , mkEqPred, mkTyConApp
                , splitTyConApp_maybe
                , eqType
                )
import Bag      ( bagToList )

-- From type checker
import TcRnTypes      ( ctEvTerm, isGivenCt
                      , CtEvidence(..), CtLoc(..), SkolemInfo(..)
                      , mkNonCanonical
                      )
import TcTypeNatsEval ( minus, divide, logExact, rootExact )
import TcEvidence     ( EvTerm(..)
                      , evTermCoercion
                      , TcCoercion(TcTypeNatCo)
                      , mkTcSymCo, mkTcTransCo
                      )
import TcSMonad ( InertSet
                , getTcSInerts, inert_cans, inert_funeqs
                , updWorkListTcS, appendWorkListCt
                , traceTcS
                , partCtFamHeadMap
                )

-- From base libraries
import Data.Maybe ( isNothing, mapMaybe )
import Data.List  ( sortBy )
import Data.Ord   ( comparing )
import Control.Monad ( msum, guard )




--------------------------------------------------------------------------------

typeNatStage :: Ct -> TcS StopOrContinue
typeNatStage ct

  -- XXX: Probably need to add the 'ct' to somewhere
  | impossible ct =
      do emitFrozenError ev (cc_depth ct)
         return Stop

  | isGiven ev =
    case solve ct of
      Just _ -> return Stop                 -- trivial fact
      _      -> do computeNewGivenWork ct   -- add some new facts (if any)
                   return $ ContinueWith ct

  | isWanted ev =
    case solve ct of
      Just c  -> do setEvBind (ctEvId ev) c
                    return Stop
      Nothing -> return $ ContinueWith ct   --- XXX: Try improvement here

  -- XXX: TODO
  | otherwise = return $ ContinueWith ct


  where ev = ctEvidence ct


--------------------------------------------------------------------------------
solve :: Ct -> Maybe EvTerm
solve ct = msum $ solveWithAxiom ct : map (`solveWithRule` ct) bRules


impossible :: Ct -> Bool

impossible (CFunEqCan { cc_fun = tc, cc_tyargs = [t1,t2], cc_rhs = t3 })

  | name == typeNatAddTyFamName =
      case (mbA,mbB,mbC) of
        (Just a, _     , Just c) -> isNothing (minus c a)
        (_     , Just b, Just c) -> isNothing (minus c b)
        _                        -> False

  | name == typeNatMulTyFamName =
      case (mbA,mbB,mbC) of
        (Just 0, _    , Just c) -> not (c == 0)
        (Just a, _    , Just c) -> isNothing (divide c a)
        (_    , Just 0, Just c) -> not (c == 0)
        (_    , Just b, Just c) -> isNothing (divide c b)
        _                       -> False

  | name == typeNatExpTyFamName =
      case (mbA,mbB,mbC) of
        (Just 0, _     , Just c) -> not (c == 0 || c == 1)
        (Just 1, _     , Just c) -> not (c == 1)
        (Just a, _     , Just c) -> isNothing (logExact c a)
        (_     , Just 0, Just c) -> not (c == 1)
        (_     , Just b, Just c) -> isNothing (rootExact c b)
        _                        -> False

  where
  name = tyConName tc
  mbA  = isNumLitTy t1
  mbB  = isNumLitTy t2
  mbC  = isNumLitTy t3

impossible _ = False


--------------------------------------------------------------------------------

type SimpleSubst = [ (TyVar, Type) ]
type Eqn         = (TypePat, TypePat)

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



useAxiom :: CoAxiomRule -> [Type] -> [EvTerm] -> EvTerm
useAxiom ax ts ps = EvCoercion $ mk ax ts (map evTermCoercion ps)
  where mk = TcTypeNatCo



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



data TypePat     = TPVar TyVar | TPCon TyCon [TypePat] | TPOther Type

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






