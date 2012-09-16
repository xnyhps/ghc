module TcTypeNats where

import PrelNames( typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                , typeNatLeqTyFamName
                )


import Outputable ( ppr, pprWithCommas
                  , Outputable
                  , SDoc
                  , (<>), (<+>), text, vcat, parens
                  -- , showSDoc
                  , hsep
                  )
import SrcLoc   ( noSrcSpan )
import Var      ( TyVar )
import TyCon    ( TyCon, tyConName )
import Type     ( Type, isNumLitTy, getTyVar_maybe, isTyVarTy, mkNumLitTy
                , mkTyConApp
                , splitTyConApp_maybe
                , eqType, cmpType
                , CoAxiomRule, Eqn, co_axr_inst, co_axr_is_rule
                )
import TysWiredIn ( typeNatAddTyCon
                  , typeNatMulTyCon
                  , typeNatExpTyCon
                  , trueTy, falseTy
                  )
import Bag      ( bagToList )
import Panic    ( panic )
import Pair     (Pair(..))

-- From type checker
import TcTypeNatsRules( bRules, impRules, widenRules
                      , axAddDef, axMulDef, axExpDef, axLeqDef
                      , natVars, leqRefl, leqTrans, leq0, leqAsym)
import TcTypeNatsEval ( minus, divide, logExact, rootExact )
import TcCanonical( StopOrContinue(..) )
import TcRnTypes  ( Ct(..), isGiven, isWanted, ctEvidence, ctEvId
                  , ctEvTerm, isGivenCt
                  , CtEvidence(..), CtLoc(..), SkolemInfo(..)
                  , mkNonCanonical
                  , ctPred
                  -- , getWantedLoc
                  , isDerived
                  , isWantedCt
                  , CtOrigin(..), EqOrigin(..)
                  )
import TcType     ( mkTcEqPred )
import TcEvidence ( EvTerm(..)
                  , evTermCoercion
                  , TcCoercion(TcTypeNatCo)
                  , mkTcSymCo, mkTcTransCo
                  , tcCoercionKind
                  )
import TcSMonad ( TcS, emitFrozenError, setEvBind
                , InertSet
                , getTcSInerts, inert_cans, inert_funeqs
                , updWorkListTcS, appendWorkListCt
                , modifyInertTcS
                , traceTcS
                , partCtFamHeadMap
                )

-- From base libraries
import Data.Maybe ( isNothing, mapMaybe )
import Data.List  ( sortBy, partition, find )
import Data.Ord   ( comparing )
import Control.Monad ( msum, guard, when )
import qualified Data.Set as S
import qualified Data.Map as M

{-
-- Just fore debugging
import Debug.Trace
import DynFlags ( tracingDynFlags )

ppsh :: SDoc -> String
ppsh = showSDoc tracingDynFlags
-}

--------------------------------------------------------------------------------

typeNatStage :: Ct -> TcS StopOrContinue
typeNatStage ct

  -- XXX: Probably need to add the 'ct' to somewhere
  | impossible ct =
      do natTrace "impssoble: " (ppr ct)
         emitFrozenError ev (cc_depth ct)
         return Stop

  | isGiven ev =
    case solve ct of
      Just _ -> return Stop              -- trivial fact
      _      -> checkBad =<< computeNewGivenWork ct

  | isWanted ev =
    getEvCt >>= \asmps ->
    case deepSolve asmps ct of
      Just c  -> do natTrace "solved wanted: " (ppr ct)
                    setEvBind (ctEvId ev) c
                    return Stop
      Nothing -> do natTrace "failed to solve wanted: " (ppr ct)
                    reExamineWanteds asmps ct
                    checkBad =<< computeNewDerivedWork ct

  | otherwise =
    case solve ct of
      Just _  -> return Stop
      Nothing -> checkBad =<< computeNewDerivedWork ct


  where
  ev = ctEvidence ct
  checkBad bad
    | null bad  = return (ContinueWith ct)
    | otherwise = do natTrace "Contradictions:" (vcat $ map ppr bad)
                     emitFrozenError ev (cc_depth ct)
                     return Stop


{- We do this before adding a new wanted to the inert set.
The purpose is to check if the new wanted might help us solve
some of the existing wanted. -}
reExamineWanteds :: [Ct] -> Ct -> TcS ()
reExamineWanteds asmps0 newWanted = loop [] (newWanted : given) wanted
  where
  (given,wanted) = partition isGivenCt asmps0

  dropSolved s i = ((), i { inert_cans =
                             let ics = inert_cans i
                                 fs  = inert_funeqs ics
                                 shouldDrop c = isWantedCt c && getId c `elem` s
                                 (_,f1) = partCtFamHeadMap shouldDrop fs
                             in ics { inert_funeqs = f1 }
                          })

  getId = ctEvId . ctEvidence

  loop solved _ [] = modifyInertTcS (dropSolved solved)

  loop solved asmps (w : ws) =
    case deepSolve (ws ++ asmps) w of
      Just ev -> do natTrace "Solved wanted:" (ppr w)
                    let x = getId w
                    setEvBind x ev
                    loop (x : solved) asmps ws
      Nothing -> loop solved (w : asmps) ws


--------------------------------------------------------------------------------
solve :: Ct -> Maybe EvTerm
solve ct = msum $ solveWithAxiom ct : map (`solveWithRule` ct) bRules

deepSolve :: [Ct] -> Ct -> Maybe EvTerm
deepSolve asmps0 ct = msum [ solve ct
                           , solveLeq leq ct
                           , fmap ev (find this (widenAsmps asmps))
                           ]
  where
  ev   = ctEvTerm . ctEvidence
  this = sameCt ct
  (leq,asmps) = makeLeqModel asmps0


impossible :: Ct -> Bool

impossible (CFunEqCan { cc_fun = tc, cc_tyargs = [t1,t2], cc_rhs = t3 })

  | name == typeNatAddTyFamName =
      case (mbA,mbB,mbC) of
        (Just a, _     , Just c) -> isNothing (minus c a)
        (_     , Just b, Just c) -> isNothing (minus c b)
        (Just a, _     , _) | a > 0 -> eqType t2 t3
        (_     , Just b, _) | b > 0 -> eqType t1 t3
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

{- `TypePat`s are used in `ActiveRule`s to distinguish between the variables
bound by the rule, and other variables occuring in types.  For our purposes,
other variables in types are simply uninterpreted constants, while `TPVar`s
need to be instantiated for the rule to fire.

Invariant: The children of `TPCon` contain at least one variable.
`TPCon`s with no variables should be represened with type applications
in `TPOther`. -}

data TypePat     = TPVar TyVar | TPCon TyCon [TypePat] | TPOther Type

instance Outputable TypePat where
  ppr (TPVar x)     = text "?" <> ppr x
  ppr (TPCon x xs)  = ppr x <> parens (pprWithCommas ppr xs)
  ppr (TPOther x)   = ppr x


-- A smart constructor for the `TypePat` invariant.
tpCon :: TyCon -> [TypePat] -> TypePat
tpCon tc tps = case check tps of
                 Just ts  -> TPOther $ mkTyConApp tc ts
                 Nothing  -> TPCon tc tps
  where
  check (TPOther x : xs)  = do ys <- check xs
                               return (x : ys)
  check (_ : _)           = Nothing
  check []                = return []

-- Convert a `Type` to a `TypePat`, abstracting the given set of variables.
toTypePat :: [TyVar] -> Type -> TypePat
toTypePat as ty
  | Just x <- getTyVar_maybe ty, x `elem` as  = TPVar x
toTypePat as ty
  | Just (tc,ts) <- splitTyConApp_maybe ty = tpCon tc (map (toTypePat as) ts)
toTypePat _ ty  = TPOther ty




{- A `SimpSubst` instantiates the `TPVar`s in a rule.  Note that
the domain of the substitution is `TPVar`s but its codomain is types,
which may not mention `TPVar`s.  Thus `SimpSubst` are always idempotent
because---esentially---the RHS contains no free variables.  For example,
consider the substiution:

    [ ("x", TVar "x") ]

The `x` on the LHS refers to a variable bound by a rule, while
the `x` on the RHS refers to an uninterpreted constant.
-}

type SimpleSubst = [ (TyVar, Type) ]

-- Applying substitutions to (structures containing) `TypePat`s.
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




-- Check to see if a type macthes a type pattern.
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


--------------------------------------------------------------------------------

-- Tries to instantiate the equation with the constraint.
byAsmp :: Ct -> (TypePat, TypePat) -> Maybe (SimpleSubst, EvTerm)

byAsmp ct (lhs,rhs) =
  do ev <- ctEvTermMaybe ct
     (t1,t2) <- case ct of

                  CFunEqCan { cc_fun = tc, cc_tyargs = ts, cc_rhs = t } ->
                                                Just (mkTyConApp tc ts, t)

                  _ -> Nothing

     su <- matchTypes [lhs,rhs] [t1,t2]
     return (su, ev)


-- Check if we can solve the equation using one of the family of axioms.
byAxiom :: (TypePat, TypePat) -> Maybe (SimpleSubst, EvTerm)

byAxiom (TPOther ty, TPVar r)
  | Just (tc,[tp1,tp2]) <- splitTyConApp_maybe ty
  , Just a <- isNumLitTy tp1, Just b <- isNumLitTy tp2

  = do (ax,val) <-
          let num op  = mkNumLitTy (op a b)
              bool op = if op a b then trueTy else falseTy
          in case tyConName tc of
               name | name == typeNatAddTyFamName -> Just (axAddDef, num (+))
                    | name == typeNatMulTyFamName -> Just (axMulDef, num (*))
                    | name == typeNatExpTyFamName -> Just (axExpDef, num (^))
                    | name == typeNatLeqTyFamName -> Just (axLeqDef, bool (<=))
               _ -> Nothing

       return ( [ (r, val) ], useAxiom ax [tp1,tp2] [] )


byAxiom (TPCon tc [TPVar r,TPOther tp1], TPOther tp2)
  | Just b <- isNumLitTy tp1, Just c <- isNumLitTy tp2

  = do (ax,op) <- case tyConName tc of
                    n | n == typeNatAddTyFamName -> Just (axAddDef, minus)
                      | n == typeNatMulTyFamName -> Just (axMulDef, divide)
                      | n == typeNatExpTyFamName -> Just (axExpDef, rootExact)
                    _ -> Nothing
       a <- op c b
       let t = mkNumLitTy a
       return ( [ (r, t) ], useAxiom ax [t,tp1] [] )


byAxiom (TPCon tc [TPOther tp1, TPVar r], TPOther tp2)
  | Just a <- isNumLitTy tp1, Just c <- isNumLitTy tp2

  = do (ax,op) <- case tyConName tc of
                    n | n == typeNatAddTyFamName -> Just (axAddDef, minus)
                      | n == typeNatMulTyFamName -> Just (axMulDef, divide)
                      | n == typeNatExpTyFamName -> Just (axExpDef, logExact)
                    _ -> Nothing
       b <- op c a
       let t = mkNumLitTy b
       return ([ (r, t) ], useAxiom ax [tp1,t] [] )


byAxiom (TPOther ty, TPOther tp3)
  | Just (tc,[tp1,tp2]) <- splitTyConApp_maybe ty
  , Just _ <- isNumLitTy tp1, Just _ <- isNumLitTy tp2
  = do ax <- case tyConName tc of
               n | n == typeNatAddTyFamName -> Just axAddDef
                 | n == typeNatMulTyFamName -> Just axMulDef
                 | n == typeNatExpTyFamName -> Just axExpDef
                 | n == typeNatLeqTyFamName -> Just axLeqDef
               _ -> Nothing
       let ([],(_,r)) = co_axr_inst ax [tp1,tp2]
       guard (eqType r tp3)
       return ([], useAxiom ax [tp1,tp2] [])

byAxiom _ = Nothing

useAxiom :: CoAxiomRule -> [Type] -> [EvTerm] -> EvTerm
useAxiom ax ts ps = EvCoercion $ mk ax ts (map evTermCoercion ps)
  where mk = TcTypeNatCo



solveWithRule :: CoAxiomRule -> Ct -> Maybe EvTerm
solveWithRule r ct =
  do (vs,[],(a,b)) <- co_axr_is_rule r -- Currently we just use simple axioms.
     let lhs = toTypePat vs a
         rhs = toTypePat vs b
     (su,_) <- byAsmp ct (lhs,rhs)    -- Just for the instantiation
     tys <- mapM (`lookup` su) vs
     return (useAxiom r tys [])

solveWithAxiom :: Ct -> Maybe EvTerm
solveWithAxiom (CFunEqCan { cc_fun = tc, cc_tyargs = ts, cc_rhs = t }) =
  do ([],ev) <- byAxiom (TPOther (mkTyConApp tc ts), TPOther t)
     return ev
solveWithAxiom _ = Nothing

solveLeq :: LeqFacts -> Ct -> Maybe EvTerm
solveLeq m ct =
  do (t1,t2) <- isLeqCt ct
     isLeq m t1 t2

--------------------------------------------------------------------------------

-- An `ActiveRule` is a partially constructed proof for some predicate.
data ActiveRule = AR
  { isSym     :: Bool -- See Note [Symmetric Rules]

  -- This is the instantiation of the rule.
  , doneTys   :: [TypePat]

  -- These are equations that we already solved, and are ready to be used.
  -- The `Int` records the position of the evidence when the rule fires.
  , doneArgs  :: [(Int,EvTerm)]

  -- These are equations that we need to solve before the rule can fire.
  -- The `Int` records the position of the evidence when the rule fires.
  , todoArgs  :: [(Int,(TypePat,TypePat))]

  -- This is what we'll prove when the rule fires.
  , concl     :: (TypePat,TypePat)

  -- This is the evidence we'll use when the rule fires.
  , proof     :: [Type] -> [EvTerm] -> EvTerm

  }

instance Outputable ActiveRule where
  ppr r = args <+> text "=>" <+> eq (concl r)

    where eq (x,y) = ppr x <+> text "~" <+> ppr y
          todo (n, e) = (n, text"?:" <+> eq e)
          done (n, ev) = let Pair x y = tcCoercionKind (evTermCoercion ev)
                         in (n, text "!:" <+> eq (x,y))

          args = hsep
               $ map snd
               $ sortBy (comparing fst)
               $ map todo (todoArgs r) ++ map done (doneArgs r)

{- Note [Symmetric Rules]

For symmetric rules, we look for at most one argument that can be
satisfied by an assumption.  For example, the function rules are symmetric:

(a + b ~ c1, a + b ~ c2) => c1 ~ c2

Notice that if we have an assumtion that matches the first argument,
there is no point in checking if this same assumption matches the second
one because we would just end up with another way to prove the same thing.

-}

{-
instance Outputable ActiveRule where
  ppr r =
    braces (pprWithCommas ppr (doneTys r)) <+>
    parens (pprWithCommas ppArg (todoArgs r)) <+> text "=>" <+>
    ppEq (concl r)
    where
    ppArg (x,e) = ppr x <> colon <+> ppr e
    ppEq (a,b)  = ppr a <+> text "~" <+> ppr b
-}



-- Activate a rule for forward reasoning.
activate :: (Bool,CoAxiomRule) -> ActiveRule
activate (sym,r)
  | Just (vs,as,c) <- co_axr_is_rule r
  , let cvt         = toTypePat vs
        cvt2 (x,y)  = (cvt x, cvt y)
  = AR { isSym     = sym
       , proof     = useAxiom r
       , doneTys   = map TPVar vs
       , doneArgs  = []
       , todoArgs  = zip [ 0 .. ] (map cvt2 as)
       , concl     = cvt2 c
       }
activate _ = panic "Tried to activate a non-rule."


{- Try to activate a rule for backward reasoning, by matching
the conclusion with the given constraint. -}
activateBackward :: (Bool,CoAxiomRule) -> Ct -> Maybe ActiveRule
activateBackward r ct =
  do let act = activate r
     (su, _) <- byAsmp ct (concl act)
     return act { doneTys = apSimpSubst su (doneTys act) }





{- Function rules have this form:

    p: a + b ~ c1, q: a + b ~ c2
    sym p `trans` q : c1 ~ c2

The rest of GHC's constraint solver already knows about this type of
rule but we need them here too so that they can get interacted with
the infinite family of built-in axioms, thus performing evaluation.

For example, if we have `5 + 3 ~ x` we can use the fun-rule for `(+)`
to conclude that `x = 8`:

    (5 + 3 ~ x, 5 + 3 ~ 8) => (x ~ 8)
-}

funRule :: TyCon -> ActiveRule
funRule tc = AR
  { isSym     = True
  , proof     = \_ [p,q] -> EvCoercion
                          $ mkTcTransCo (mkTcSymCo $ evTermCoercion p)
                                        (evTermCoercion q)
  , doneTys   = map TPVar [ a, b, c1, c2 ]
  , doneArgs  = []
  , todoArgs  = [ (0, (TPCon tc [ TPVar a, TPVar b], TPVar c1))
                , (1, (TPCon tc [ TPVar a, TPVar b], TPVar c2)) ]
  , concl     = (TPVar c1, TPVar c2)
  }
  where a : b : c1 : c2 : _ = natVars



data RuleResult = RuleResult
  { conclusion       :: Eqn                 -- what we proved
  , evidence         :: [EvTerm] -> EvTerm  -- proof, given evidence for derived
  }


{- Check if the `ActiveRule` is completely instantiated and, if so,
compute the resulting equation and the evidence for it.

If some of the parameters for the equation were matched by
`Derived` constraints, then the evidence for the term will be parmatereized
by proofs for them.
-}
fireRule :: LeqFacts -> ActiveRule -> Maybe RuleResult
fireRule leq r =
  do doneSides <- mapM solveSide $ todoArgs r

     ts        <- mapM cvt (doneTys r)
     (lhs,rhs) <- cvt2 (concl r)
     guard $ not $ eqType lhs rhs   -- Not interested in trivial results.


     return RuleResult
       { conclusion = (lhs,rhs)
       , evidence = \_ -> proof r ts $ map snd $ sortBy (comparing fst)
                                     $ doneSides ++ doneArgs r
       }

  where
  cvt2 (x,y)      = do a <- cvt x
                       b <- cvt y
                       return (a,b)

  cvt (TPOther t) = Just t
  cvt _           = Nothing


  solveSide (n, eq) =
    do (x,y) <- isLeqEqn =<< cvt2 eq
       ev    <- isLeq leq x y
       return (n, ev)


eqnToCt :: Eqn -> Maybe EvTerm -> Ct
eqnToCt (lhs,rhs) evt
  | Just (tc,ts) <- splitTyConApp_maybe lhs =
      CFunEqCan { cc_ev = ev False, cc_depth = 0
                , cc_fun = tc, cc_tyargs = ts, cc_rhs = rhs }

  | Just x <- getTyVar_maybe lhs =
      CTyEqCan { cc_ev = ev False, cc_depth = 0, cc_tyvar = x, cc_rhs = rhs }

  | Just x <- getTyVar_maybe rhs =
      CTyEqCan { cc_ev = ev True, cc_depth = 0, cc_tyvar = x, cc_rhs = lhs }

  -- The only possibility here is something like: 2 ~ 3
  -- which means we've detected an error!
  | otherwise = mkNonCanonical (ev False)

  where
  ty = mkTcEqPred lhs rhs

  ev swap =
    case evt of
      Nothing -> Derived
        { ctev_wloc = CtLoc wloc noSrcSpan [], ctev_pred = ty }

      Just t  -> Given
        { ctev_gloc = CtLoc UnkSkol noSrcSpan []
        , ctev_pred = ty
        , ctev_evtm = if swap then EvCoercion $ mkTcSymCo $ evTermCoercion t
                              else t
        }

  -- XXX: This is somewhat bogus.
  wloc = TypeEqOrigin (UnifyOrigin lhs rhs)

ruleResultToGiven :: RuleResult -> Ct
ruleResultToGiven r = eqnToCt (conclusion r) (Just (evidence r []))

ruleResultToDerived :: RuleResult -> Ct
ruleResultToDerived r = eqnToCt (conclusion r) Nothing




-- Define one of the arguments of an active rule.
setArg :: Int -> (SimpleSubst, EvTerm) -> ActiveRule -> ActiveRule
setArg n (su,ev) r =
  AR { isSym     = isSym r
     , proof     = proof r
     , doneTys   = apSimpSubst su (doneTys r)
     , doneArgs  = (n,ev) : doneArgs r
     , todoArgs  = todo
     , concl     = apSimpSubst su (concl r)
     }
  where
  -- Remove the solved goal form the list of work.
  todo = case break ((n == ) . fst) $ inst $ todoArgs r of
           (as,_:bs) -> as++bs
           _         -> panic "setArg: Tried to set a non-existent param."

  inst xs = [ (x,apSimpSubst su y) | (x,y) <- xs ]

-- Try to solve one of the assumptions by axiom.
applyAxiom1 :: ActiveRule -> Maybe ActiveRule
applyAxiom1 r = msum $ map attempt $ todoArgs r
  where
  attempt (n,eq) = do (su,ev) <- byAxiom eq
                      return (setArg n (su, ev) r)

-- Try to satisfy some of the rule's assumptions by axiom.
applyAxiom :: ActiveRule -> ActiveRule
applyAxiom r = maybe r applyAxiom (applyAxiom1 r)

{- The various ways in which an assumption fits the arguments of a rule.
Note: currently, we use an assumption at most once per rule.
For example, assumption `p` will not make instantiations like `R(p,p)`.
-}
applyAsmp :: ActiveRule -> Ct -> [ActiveRule]
applyAsmp r ct =
  restrict $
  do -- Find places where this constraint might fit
     (n,soln) <- mapMaybe attempt (todoArgs r)
     return (setArg n soln r)
  where
  attempt (n,eq) = do ok <- byAsmp ct eq
                      return (n,ok)
  restrict | isSym r    = take 1
           | otherwise  = id


{- Does forward reasoning:  compute new facts by interacting
existing facts with a set of rules.

If `withEv` is `True`, then we generate given constraints,
otherwise they are derived. -}
interactActiveRules :: LeqFacts -> [ActiveRule] -> [Ct] -> [RuleResult]
interactActiveRules leq rs0 cs0 = loop (map applyAxiom rs0) cs0
  where
  loop rs []       = mapMaybe (fireRule leq) rs
  loop rs (c : cs) = let new = map applyAxiom (concatMap (`applyAsmp` c) rs)
                     in loop (new ++ rs) cs

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



--------------------------------------------------------------------------------

-- Get the facts that are known for sure.
-- Note: currently we do not use the solved ones but we probably should.
getFacts :: TcS [Ct]
getFacts =
  do is <- getTcSInerts
     return $ bagToList $ fst $ partCtFamHeadMap isGivenCt
                              $ inert_funeqs $ inert_cans is

-- Get constraints with evidence (given or wanted)
getEvCt:: TcS [Ct]
getEvCt =
  do is <- getTcSInerts
     return $ bagToList $ fst $ partCtFamHeadMap hasEv
                              $ inert_funeqs $ inert_cans is
  where hasEv c = isGivenCt c || isWantedCt c

sameCt :: Ct -> Ct -> Bool
sameCt c1 c2 = eqType (ctPred c1) (ctPred c2)

--------------------------------------------------------------------------------

{- Add a new constraint to the inert set.
The resulting constraints are return in `Given` form because they have
proofs.  When the new constraint was a "wanted", we discard the proofs
and convert them to "derived".

The first set of constraints are ones that indicate a contradiction
                                                          (e.g., 2 ~ 3).
The second set are "good" constraints (not obviously contradicting each other).
-}
interactCt :: Bool -> Ct -> [Ct] -> ([Ct],[Ct])
interactCt withEv ct asmps0
  | Just _ <- isLeqCt ct =
  let active  = map activate impRules
      -- XXX: We only really need to consider impRules that have
      -- a side condition.

      (leq, asmps) = makeLeqModel (ct : asmps0)
      newWork = interactActiveRules leq active asmps
  in partition isBad $ if withEv then map ruleResultToGiven newWork
                                 else map ruleResultToDerived newWork

  | otherwise =
  let active  = concatMap (`applyAsmp` ct)
              $ funRule typeNatAddTyCon
              : funRule typeNatMulTyCon
              : funRule typeNatExpTyCon
              : map activate (widen ++ impRules)

      (leq, asmps) = makeLeqModel asmps0
      newWork = interactActiveRules leq active asmps
  in partition isBad $ if withEv then map ruleResultToGiven newWork
                                 else map ruleResultToDerived newWork

 where
  -- XXX: why don't we do widening when computing derived?
  widen = if withEv then widenRules else []

  -- cf. `fireRule`: the only way to get a non-canonical constraint
  -- is if it impossible to solve.
  isBad (CNonCanonical {})  = True
  isBad _                   = False


-- Given a set of facts, apply forward reasoning using the "difficult"
-- rules to derive some additional facts.
-- NOTE: assumes that the initial set all have evidence
-- (i.e., they are either givens or wanted)
widenAsmps :: [Ct] -> [Ct]
widenAsmps asmps = step given wanted []

  where
  (given, wanted) = partition isGivenCt asmps

  known c cs  = any (sameCt c) cs

  step done [] [] = reverse done
  step done [] cs = step done (reverse cs) []
  step done (c : cs) ds
    | known c done  = step done cs ds
    | otherwise
      = let active = concatMap (`applyAsmp` c) $ map activate widenRules
            new = map ruleResultToGiven $ interactActiveRules leq active done
        in step (c : done) cs (new ++ ds)

  -- For the moment, widedning rules have no ordering side conditions.
  leq = noLeqFacts


--------------------------------------------------------------------------------


{- Compute additional givens, computed by combining this one with
existing givens.

Returns any obvious contradictions that we found.
-}
computeNewGivenWork :: Ct -> TcS [Ct]
computeNewGivenWork ct =
  do (bad,good) <- interactCt True ct `fmap` getFacts

     when (null bad) $
       do natTrace "New givens:" (vcat $ map ppr good)
          updWorkListTcS (appendWorkListCt good)

     return bad


{- Compute additional work, assuming that the wanted will stay for now.
The additional work is always "derived" (i.e., facts we can conclude
by interactig the constraint with existing constraints.

Returns any obvious contradictions that we found. -}

computeNewDerivedWork :: Ct -> TcS [Ct]
computeNewDerivedWork ct =
  do (bad,good) <- interactCt False ct `fmap` getEvCt

     when (null bad) $
       do natTrace "New derived:" (vcat $ map ppr good)
          updWorkListTcS (appendWorkListCt good)

     return bad


--------------------------------------------------------------------------------
-- Reasoning about order.


-- This is just here so that we can have an Ord instance on types,
-- so that we can store them in maps and sets
newtype LeqFacts = LeqFacts (M.Map LeqType LeqEdges)
newtype LeqType  = LeqType Type
data LeqEdge  = LeqEdge { leqProof :: EvTerm, leqTarget :: Type }
data LeqEdges = LeqEdges { leqAbove  :: S.Set LeqEdge  -- proof: here <= above
                         , leqBelow  :: S.Set LeqEdge  -- proof: below <= here
                         }

instance Eq LeqType  where LeqType x == LeqType y          = eqType x y
instance Ord LeqType where compare (LeqType x) (LeqType y) = cmpType x y

instance Eq LeqEdge where
  x == y  = eqType (leqTarget x) (leqTarget y)

instance Ord LeqEdge where
  compare x y = cmpType (leqTarget x) (leqTarget y)


leqNoEdges :: LeqEdges
leqNoEdges = LeqEdges { leqAbove = S.empty, leqBelow = S.empty }

noLeqFacts :: LeqFacts
noLeqFacts = LeqFacts M.empty

immAbove :: LeqFacts -> Type -> S.Set LeqEdge
immAbove (LeqFacts lm) t = case M.lookup (LeqType t) lm of
                             Just edges -> leqAbove edges
                             Nothing -> S.empty

immBelow :: LeqFacts -> Type -> S.Set LeqEdge
immBelow (LeqFacts lm) t = case M.lookup (LeqType t) lm of
                             Just edges -> leqBelow edges
                             Nothing -> S.empty

-- Try to find a path from one node to another.
leqReachable :: LeqFacts -> Type -> Type -> Maybe EvTerm
leqReachable m smaller larger =
  search S.empty (S.singleton LeqEdge { leqProof = useAxiom leqRefl [smaller] []
                                      , leqTarget = smaller })
  where
  search visited todo =
    do (LeqEdge { leqProof = pr, leqTarget = term }, rest) <- S.minView todo
       if term `eqType` larger
         then return pr
         else let updProof e = e { leqProof = useAxiom leqTrans
                                                [smaller,term,leqTarget e]
                                                [pr, leqProof e] }
                  new = S.mapMonotonic updProof (immAbove m term)
                  vis = S.insert (LeqType term) visited
                  notDone = S.filter (not . (`S.member` vis)
                                          . LeqType . leqTarget)
         in search vis (notDone new `S.union` notDone rest)

{-
The linking function is a bit complex because we keep the ordering database
minimal.

This diagram illustrates what we do when we link two nodes (leqLink).

We start with a situation like on the left, and we are adding an
edge from L to U.  The final result is illustrated on the right.

   Before    After

     a         a
    /|        /
   / |       /
  U  |      U\
  |  L        \L
  | /         /
  |/         /
  d         d

L: lower
U: upper
a: a member of "above uedges"  (uus)
d: a member of "below ledges"  (lls)
-}

{- XXX: It would be useful to return the edges that were removed because these
edges can be solved in term of the existing facts, so if some of them correspond
to wanted constrainst we can discharge them straight aways.   We still get
the same effect in `reExamineWanteds` but in a much less effecieant way. -}

leqLink :: EvTerm -> (Type,LeqEdges) -> (Type,LeqEdges) ->
                                      LeqFacts -> (LeqEdges,LeqEdges,LeqFacts)

leqLink ev (lower, ledges) (upper, uedges) m0 =

  let leqTgt      = LeqType . leqTarget

      uus         = S.mapMonotonic leqTgt (leqAbove uedges)
      lls         = S.mapMonotonic leqTgt (leqBelow ledges)

      rm x        = S.filter (not . (`S.member` x) . leqTgt)

      newLedges   = ledges { leqAbove =
                               S.insert (LeqEdge { leqProof  = ev
                                                 , leqTarget = upper
                                                 })
                               $ rm uus
                               $ leqAbove ledges
                           }
      newUedges   = uedges { leqBelow =
                               S.insert (LeqEdge { leqProof  = ev
                                                 , leqTarget = lower
                                                 })
                               $ rm lls
                               $ leqBelow uedges
                           }

{- The "undefined" in 'del' is OK because the proofs are not used in the
comparison and the set API seems to lack a function to get the same behavior.
Note that filter-ing is a little different because it has to traverse the
whole set while here we stop as soon as we found the element that is
to be removed. -}

      del x       = S.delete LeqEdge { leqTarget = x, leqProof = undefined }


      adjust f t (LeqFacts m) = LeqFacts (M.adjust f t m)
      insert k x (LeqFacts m) = LeqFacts (M.insert (LeqType k) x m)

      adjAbove    = adjust (\e -> e { leqAbove = del upper (leqAbove e) })
      adjBelow    = adjust (\e -> e { leqBelow = del lower (leqBelow e) })
      fold f xs x = S.fold f x xs

  in ( newLedges
     , newUedges
     , insert lower newLedges
     $ insert upper newUedges
     $ fold adjAbove lls
     $ fold adjBelow uus
       m0
     )

-- | Insert a new node in a collection of facts.
-- Returns the edges surrounding the new node.
--  * Variable nodes are always linked to 0 (directly or indirectly).
--  * Constant nodes are always linked to neighbouring constant nodes.
leqInsNode :: Type -> LeqFacts -> (LeqEdges, LeqFacts)
leqInsNode t model@(LeqFacts m0) =
  case M.splitLookup (LeqType t) m0 of
    (_, Just r, _)  -> (r, model)
    (left, Nothing, right) ->
      let new           = leqNoEdges
          ans1@(es1,m1) = ( new, LeqFacts (M.insert (LeqType t) new m0) )
      in case () of

           -- type variables get liked to 0
           _ | isTyVarTy t ->
             let zero         = mkNumLitTy 0
                 (zes,zm)     = leqInsNode zero m1    -- Should not modify es1
                 ax0          = useAxiom leq0 [t] []
                 (_, es2, m2) = leqLink ax0 (zero,zes) (t,es1) zm
             in (es2, m2)

           _ | Just _ <- isNumLitTy t ->

             -- link to a smaller constnat, if any
             let ans2@(es2, m2) =
                   case toNum M.findMax left of
                     Nothing -> ans1
                     Just (n,l)  ->
                       let (_,x,y) = leqLink (useAxiom axLeqDef [n,t] []) l (t,es1) m1
                       in (x,y)

             -- link to a larger constant, if any
             in case toNum M.findMin right of
                  Nothing -> ans2
                  Just (n,u)  ->
                    let (x,_,y) = leqLink (useAxiom axLeqDef [t,n] []) (t,es2) u m2
                    in (x,y)

           _ -> panic "leqInsNode: not constant or variable"

  where
  toNum f x = do guard (not (M.null x))
                 let (LeqType n,e) = f x
                 _ <- isNumLitTy n
                 return (n,(n,e))


isLeq :: LeqFacts -> Type -> Type -> Maybe EvTerm
isLeq m t1 t2 = leqReachable m2 t1 t2
  where (_,m1) = leqInsNode t1 m
        (_,m2) = leqInsNode t2 m1


-- | The result of trying to extend a collection of facts with a new one.
data AddLeqFact
  = LeqAdded LeqFacts   -- ^ The fact was added succesfully.
  | LeqAlreadyKnown     -- ^ The fact was not added because it was known.
  | LeqImproved EvTerm  -- ^ The fact was not added because there is
                        -- an equiavlent more useful fact.

-- | Try to add the fact that the first term is smaller then the second
-- (as evidenced by the proof).
addFact :: EvTerm -> Type -> Type -> LeqFacts -> AddLeqFact
addFact ev t1 t2 m0 =
  let (n1,m1)   = leqInsNode t1 m0
      (n2,m2)   = leqInsNode t2 m1

  in case leqReachable m2 t2 t1 of

       Nothing ->

         case leqReachable m2 t1 t2 of
           Nothing -> let (_,_,m3) = leqLink ev (t1,n1) (t2,n2) m2
                      in LeqAdded m3
           Just _  -> LeqAlreadyKnown

       {- We know the opposite: we don't add the fact
          but propose an equality instead. -}
       Just pOp -> LeqImproved (useAxiom leqAsym [t1,t2] [ev, pOp])

-- | Construct an ordering model and return the remaining, not-leq constraints.
makeLeqModel :: [Ct] -> (LeqFacts,[Ct])
makeLeqModel = foldr add (noLeqFacts,[])
  where
  add ct (m,rest)
    | Just (t1,t2) <- isLeqCt ct
    , Just ev      <- ctEvTermMaybe ct
    , LeqAdded m1  <- addFact ev t1 t2 m = (m1, rest)
  add ct (m,rest)                        = (m, ct : rest)

-- | Is this an `a <= b` constraint?
isLeqCt :: Ct -> Maybe (Type, Type)
isLeqCt (CFunEqCan { cc_fun = tc, cc_tyargs = [t1,t2], cc_rhs = t })
  | tyConName tc == typeNatLeqTyFamName && eqType t trueTy = Just (t1,t2)
isLeqCt _ = Nothing

isLeqEqn :: Eqn -> Maybe (Type,Type)
isLeqEqn (t1,t2) =
  do guard (eqType t2 trueTy)
     (tc,[x,y]) <- splitTyConApp_maybe t1
     guard (tyConName tc == typeNatLeqTyFamName)
     return (x,y)


-- | Get the evidence associated with a constraint, if any.
ctEvTermMaybe :: Ct -> Maybe EvTerm
ctEvTermMaybe ct =
  do let ev = ctEvidence ct
     guard $ not $ isDerived ev
     return (ctEvTerm ev)


--------------------------------------------------------------------------------

natTrace :: String -> SDoc -> TcS ()
natTrace x y = traceTcS ("[NATS] " ++ x) y


