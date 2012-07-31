module TcTypeNats where

import PrelNames( typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                , typeNatLeqTyFamName
                )


import Outputable ( ppr, pprWithCommas
                  , Outputable
                  , SDoc
                  , (<>), (<+>), colon, text, vcat, parens, braces
                  )
import SrcLoc   ( noSrcSpan )
import Var      ( TyVar )
import TyCon    ( TyCon, tyConName )
import Type     ( Type, isNumLitTy, getTyVar_maybe, mkNumLitTy
                , mkTyConApp
                , splitTyConApp_maybe
                , eqType, cmpType
                , CoAxiomRule, Eqn, co_axr_inst, co_axr_is_rule
                )
import TysWiredIn ( typeNatAddTyCon
                  , typeNatMulTyCon
                  , typeNatExpTyCon
                  , typeNatLeqTyCon
                  , trueTy, falseTy
                  )
import Bag      ( bagToList )
import Panic    ( panic )
import TrieMap  (TypeMap, emptyTM)

-- From type checker
import TcTypeNatsRules( bRules, impRules, widenRules
                      , axAddDef, axMulDef, axExpDef, axLeqDef
                      , natVars)
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
                  )
import TcSMonad ( TcS, emitFrozenError, setEvBind
                , InertSet
                , getTcSInerts, inert_cans, inert_funeqs
                , updWorkListTcS, appendWorkListCt
                , modifyInertTcS
                , traceTcS
                , partCtFamHeadMap
                , foldFamHeadMap
                )

-- From base libraries
import Data.Maybe ( isNothing, mapMaybe )
import Data.List  ( sortBy, partition, find )
import Data.Ord   ( comparing )
import Control.Monad ( msum, guard, when, mplus )
import qualified Data.Set as S

-- import Debug.Trace


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

{- XXX: This is not quite enough.  We really need to do some backward
reasoning also.

Example:

Assumptions: (2 <= x, x * a1 ~ c, x * a2 ~ c)
Conclusion needed:a1 ~ a2

If we had (1 <= x) in the assumptions, it would react with the the
two multiplications to cancel things out.  However, we have 2 <= x, instead.
We need to notice that this implies (1 <= x).  In the other implementation
this happened automatically because of the custom system for reasoning
about <=.
-}
deepSolve :: [Ct] -> Ct -> Maybe EvTerm
deepSolve asmps ct = solve ct `mplus` fmap ev (find this (widenAsmps asmps))
  where
  ev   = ctEvTerm . ctEvidence
  this = sameCt ct


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

The `x` on the RHS refers to a variable bound by a rule, while
the `x` on the LHS refers to an uninterpreted constant.
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
byAsmp :: Ct -> (TypePat, TypePat) -> Maybe (SimpleSubst, Maybe EvTerm)

byAsmp ct (lhs,rhs) =
  do (t1,t2) <- case ct of

                  CFunEqCan { cc_fun = tc, cc_tyargs = ts, cc_rhs = t } ->
                                                Just (mkTyConApp tc ts, t)

                  _ -> Nothing

     su <- matchTypes [lhs,rhs] [t1,t2]
     return (su, do let ev = ctEvidence ct
                    guard (not (isDerived ev))
                    return (ctEvTerm ev))



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

{-
solveWithAsmps :: [Ct] -> Ct -> Maybe EvTerm
solveWithAsmps asmps ct =
  do let rs = mapMaybe (`activateBackward` ct) backRules
     new <- listToMaybe (interactActiveRules rs asmps)
     undefined -- extract proof from constraint
-}

solveWithAxiom :: Ct -> Maybe EvTerm
solveWithAxiom (CFunEqCan { cc_fun = tc, cc_tyargs = ts, cc_rhs = t }) =
  do ([],ev) <- byAxiom (TPOther (mkTyConApp tc ts), TPOther t)
     return ev
solveWithAxiom _ = Nothing

--------------------------------------------------------------------------------

-- An `ActiveRule` is a partially constructed proof for some predicate.
data ActiveRule = AR
  { isSym     :: Bool -- See Note [Symmetric Rules]

  -- This is the instantiation of the rule.
  , doneTys   :: [TypePat]

  -- These are equations that we already solved, and are ready to be used.
  -- The `Int` records the position of the evidence when the rule fires.
  , doneArgs  :: [(Int,EvTerm)]

  {- These are equations that were solved using a `Derived` fact.
  If we are interested in the proof for this rule (i.e., we are
  not just computing another derived), then we need to find evidence
  for these. -}
  , subgoals  :: [(Int,(TypePat,TypePat))]

  -- These are equations that we need to solve before the rule can fire.
  -- The `Int` records the position of the evidence when the rule fires.
  , todoArgs  :: [(Int,(TypePat,TypePat))]

  -- This is what we'll prove when the rule fires.
  , concl     :: (TypePat,TypePat)

  -- This is the evidence we'll use when the rule fires.
  , proof     :: [Type] -> [EvTerm] -> EvTerm

  }

{- Note [Symmetric Rules]

For symmetric rules, we look for at most one argument that can be
satisfied by an assumption.  For example, the function rules are symmetric:

(a + b ~ c1, a + b ~ c2) => c1 ~ c2

Notice that if we have an assumtion that matches the first argument,
there is no point in checking if this same assumption matches the second
one because we would just end up with another way to prove the same thing.

-}

instance Outputable ActiveRule where
  ppr r =
    braces (pprWithCommas ppr (doneTys r)) <+>
    parens (pprWithCommas ppArg (todoArgs r)) <+> text "=>" <+>
    ppEq (concl r)
    where
    ppArg (x,e) = ppr x <> colon <+> ppr e
    ppEq (a,b)  = ppr a <+> text "~" <+> ppr b




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
       , subgoals  = []
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
  , subgoals  = []
  , todoArgs  = [ (0, (TPCon tc [ TPVar a, TPVar b], TPVar c1))
                , (1, (TPCon tc [ TPVar a, TPVar b], TPVar c2)) ]
  , concl     = (TPVar c1, TPVar c2)
  }
  where a : b : c1 : c2 : _ = natVars



data RuleResult = RuleResult
  { conclusion       :: Eqn                 -- what we proved
  , derived_subgoals :: [Eqn]               -- derived parameters used
  , evidence         :: [EvTerm] -> EvTerm  -- proof, given evidence for derived
  }


{- Check if the `ActiveRule` is completely instantiated and, if so,
compute the resulting equation and the evidence for it.

If some of the parameters for the equation were matched by
`Derived` constraints, then the evidence for the term will be parmatereized
by proofs for them.
-}
fireRule :: ActiveRule -> Maybe RuleResult
fireRule r =
  do guard $ null $ todoArgs r

     ts        <- mapM cvt (doneTys r)
     (lhs,rhs) <- cvt2 (concl r)
     let (locs,subs) = unzip (subgoals r)
     todo      <- mapM cvt2 subs

     guard $ not $ eqType lhs rhs   -- Not interested in trivial results.

     return RuleResult
       { conclusion = (lhs,rhs)
       , derived_subgoals = todo
       , evidence = \es -> proof r ts $ map snd $ sortBy (comparing fst)
                                      $ zip locs es ++ doneArgs r
       }

  where
  cvt2 (x,y)      = do a <- cvt x
                       b <- cvt y
                       return (a,b)

  cvt (TPOther t) = Just t
  cvt _           = Nothing

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
setArg :: Int -> (SimpleSubst, Maybe EvTerm) -> ActiveRule -> ActiveRule
setArg n (su,ev) r =
  AR { isSym     = isSym r
     , proof     = proof r
     , doneTys   = apSimpSubst su (doneTys r)
     , subgoals  = newSubgoals
     , doneArgs  = newDone
     , todoArgs  = todo
     , concl     = apSimpSubst su (concl r)
     }
  where
  -- Remove the solved goal form the list of work.
  -- Also looks up what was proved, in case we need to mark it as a subgoal.
  (goal, todo)  = case break ((n == ) . fst) $ inst $ todoArgs r of
                    (as,b:bs) -> (b,as++bs)
                    _ -> panic "setArg: Tried to set a non-existent param."

  -- XXX: Can the subgoals contain variables?
  (newSubgoals, newDone) =
    case ev of
      Nothing -> (goal : inst (subgoals r),         doneArgs r)
      Just e  -> (       inst (subgoals r), (n,e) : doneArgs r)

  inst xs = [ (x,apSimpSubst su y) | (x,y) <- xs ]

-- Try to solve one of the assumptions by axiom.
applyAxiom1 :: ActiveRule -> Maybe ActiveRule
applyAxiom1 r = msum $ map attempt $ todoArgs r
  where
  attempt (n,eq) = do (su,ev) <- byAxiom eq
                      return (setArg n (su, Just ev) r)

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
interactActiveRules :: [ActiveRule] -> [Ct] -> [RuleResult]
interactActiveRules rs0 cs0 = loop (map applyAxiom rs0) cs0
  where
  loop rs []       = mapMaybe fireRule rs
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

getEvCt:: TcS [Ct]
getEvCt =
  do is <- getTcSInerts
     return $ bagToList $ fst $ partCtFamHeadMap hasEv
                              $ inert_funeqs $ inert_cans is
  where hasEv c = isGivenCt c || isWantedCt c

getAllCts :: TcS [Ct]
getAllCts =
  do is <- getTcSInerts
     return $ foldFamHeadMap (:) [] $ inert_funeqs $ inert_cans is

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
interactCt withEv ct asmps =
  let active  = concatMap (`applyAsmp` ct)
              $ funRule typeNatAddTyCon
              : funRule typeNatMulTyCon
              : funRule typeNatExpTyCon
              : map activate (widen ++ impRules)

      newWork = interactActiveRules active asmps
  in partition isBad $ if withEv then map ruleResultToGiven newWork
                                 else map ruleResultToDerived newWork

 where
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

  where (given, wanted) = partition isGivenCt asmps

        known c cs  = any (sameCt c) cs

        step done [] [] = reverse done
        step done [] cs = step done (reverse cs) []
        step done (c : cs) ds
          | known c done  = step done cs ds
          | otherwise
            = let active = concatMap (`applyAsmp` c) $ map activate widenRules
                  new = map ruleResultToGiven $ interactActiveRules active done
              in step (c : done) cs (new ++ ds)


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
  do (bad,good) <- interactCt False ct `fmap` getAllCts

     when (null bad) $
       do natTrace "New derived:" (vcat $ map ppr good)
          updWorkListTcS (appendWorkListCt good)

     return bad


--------------------------------------------------------------------------------
-- Reasoning about order.

type LeqFacts = TypeMap LeqEdges
data LeqEdge  = LeqEdge { leqProof :: CtEvidence, leqTarget :: Type }
data LeqEdges = LeqEdges { leqAbove  :: S.Set LeqEdge  -- proof: here <= above
                         , leqBelow  :: S.Set LeqEdge  -- proof: below <= here
                         }

instance Eq LeqEdge where
  x == y  = eqType (leqTarget x) (leqTarget y)

instance Ord LeqEdge where
  compare x y = cmpType (leqTarget x) (leqTarget y)

nodeFacts :: Type -> LeqEdges -> [Ct]
nodeFacts x es = toFacts leqBelow lowerFact ++ toFacts leqAbove upperFact
  where
  toFacts list f  = map f $ S.toList $ list es

  upperFact f = mkL (leqProof f) x (leqTarget f)
  lowerFact f = mkL (leqProof f) (leqTarget f) x

  mkL e a b = CFunEqCan
                 { cc_ev = e, cc_depth = 0
                 , cc_fun = typeNatLeqTyCon, cc_tyargs = [a,b], cc_rhs = trueTy
                 }

noLeqEdges :: LeqEdges
noLeqEdges = LeqEdges { leqAbove = S.empty, leqBelow = S.empty }

noLeqFacts :: LeqFacts
noLeqFacts = emptyTM





--------------------------------------------------------------------------------

natTrace :: String -> SDoc -> TcS ()
natTrace x y = traceTcS ("[NATS] " ++ x) y

