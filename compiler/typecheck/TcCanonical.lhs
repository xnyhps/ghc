\begin{code}
module TcCanonical(
    canonicalize, 
    canOccursCheck, canEq, 
    rewriteWithFunDeps,
    emitFDWorkAsWanted, emitFDWorkAsDerived,
    StopOrContinue (..)
 ) where

#include "HsVersions.h"

import BasicTypes ()
import TcErrors
import TcRnTypes
import FunDeps
import qualified TcMType as TcM
import TcType
import Type
import Coercion
import Class
import TyCon
import TypeRep
import Name ()
import Var
import VarEnv
import Outputable
import Control.Monad    ( when, zipWithM, foldM )
import MonadUtils
import Control.Applicative ( (<|>) )

import VarSet

import HsBinds
import TcSMonad
import FastString
\end{code}


%************************************************************************
%*                                                                      *
%*                      The Canonicaliser                               *
%*                                                                      *
%************************************************************************

Note [Canonicalization]
~~~~~~~~~~~~~~~~~~~~~~~

Canonicalization converts a flat constraint to a canonical form. It is
unary (i.e. treats individual constraints one at a time), does not do
any zonking, but lives in TcS monad because it needs to create fresh
variables (for flattening) and consult the inerts (for efficiency).

The execution plan for canonicalization is the following:
 
  1) Decomposition of equalities happens as necessary until we reach a 
     variable or type family in one side. There is no decomposition step
     for other forms of constraints. 

  2) If, when we decompose, we discover a variable on the head then we 
     look at inert_eqs from the current inert for a substitution for this 
     variable and contine decomposing. Hence we lazily apply the inert 
     substitution if it is needed. 

  3) If no more decomposition is possible, we deeply apply the substitution
     from the inert_eqs and continue with flattening.

  4) During flattening, we examine whether we have already flattened some 
     function application by looking at all the CTyFunEqs with the same 
     function in the inert set. The reason for deeply applying the inert 
     substitution at step (3) is to maximise our chances of matching an 
     already flattened family application in the inert. 

The net result is that a constraint coming out of the canonicalization 
phase cannot be rewritten any further from the inerts (but maybe /it/ can 
rewrite an inert or still interact with an inert in a further phase in the
simplifier.

\begin{code}

-- Informative results of canonicalization
data StopOrContinue 
  = ContinueWith Ct   -- Either no canonicalization happened, or if some did 
                      -- happen, it is still safe to just keep going with this 
                      -- work item. 
  | Stop              -- Some canonicalization happened, extra work is now in 
                      -- the TcS WorkList. 

instance Outputable StopOrContinue where
  ppr Stop             = ptext (sLit "Stop")
  ppr (ContinueWith w) = ptext (sLit "ContinueWith") <+> ppr w


-- Top-level canonicalization
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
canonicalize :: Ct -> TcS StopOrContinue
canonicalize (CNonCanonical { cc_id = ev, cc_flavor = fl, cc_depth  = d })
  = go ev (predTypePredTree (evVarPred ev)) >> return Stop
    -- Must canonicalize so return Stop. 
    -- NB: Could be improved by returning ContinueWith in some cases. Not 
    --     clear yet if it will save us much so not doing this for now.
  where go ev (ClassPred {})   = canClass d fl ev
        go ev (EqPred ty1 ty2) = canEq    d fl ev ty1 ty2
        go ev (IPPred {})      = canIP    d fl ev
        go ev (TuplePred tys)
          | null tys = return ()
          | otherwise
          = do { evs <- zipWithM go_tup_one tys [0..]
               ; when (isWanted fl) $ setEvBind ev (EvTupleMk evs) }
        go ev (IrredPred ev_ty)    = canIrredEvidence d fl ev ev_ty

        go_tup_one ty n
          = do { ev' <- newEvVar (predTreePredType ty)
               ; when (isGivenOrSolved fl) $ setEvBind ev' (EvTupleSel ev n)
               ; go ev' ty
               ; return ev' }
canonicalize ct = return $ ContinueWith ct  -- Already canonical


-- Implicit Parameter Canonicalization
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
canIP :: SubGoalDepth -- Depth 
      -> CtFlavor -> EvVar -> TcS ()
-- Precondition: EvVar is implicit parameter evidence
canIP d fl v
  = do { ieqs <- getInertEqs
       ; v'   <- rewriteFromInertEqs ieqs fl v
       ; let (IPPred nm ty) = predTypePredTree (evVarPred v') 
       -- See Note [Canonical implicit parameter constraints] 
       -- to see why we don't flatten ty
       ; let ct = CIPCan { cc_id     = v'
                         , cc_flavor = fl
                         , cc_ip_nm  = nm
                         , cc_ip_ty  = ty
                         , cc_depth  = d } 
       ; updWorkListTcS (extendWorkListNonEq ct) }
         -- Emit canonical non-equality
\end{code}
Note [Canonical implicit parameter constraints]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The type in a canonical implicit parameter constraint doesn't need to
be a xi (type-function-free type) since we can defer the flattening
until checking this type for equality with another type.  If we
encounter two IP constraints with the same name, they MUST have the
same type, and at that point we can generate a flattened equality
constraint between the types.  (On the other hand, the types in two
class constraints for the same class MAY be equal, so they need to be
flattened in the first place to facilitate comparing them.)
\begin{code}

-- Class Canonicalization
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

canClass :: SubGoalDepth -- Depth
         -> CtFlavor -> EvVar -> TcS ()
-- Precondition: EvVar is class evidence 
canClass d fl v 
  = do { ieqs <- getInertEqs
               -- Rewrite from the inerts 
       ; v' <- rewriteFromInertEqs ieqs fl v
               -- Flatten type 
       ; (xi, co) <- flatten d fl (evVarPred v')

               -- Get the final type (after rewriting and flattening)
       ; let (ClassPred cls xis) = predTypePredTree xi

       ; v_new <- 
           if isReflCo co || isGivenOrSolved fl then return v'
           else do { v_new <- newEvVar xi
                   ; when (isWanted fl) $ 
                          setEvBind v' (EvCast v_new co)
                   ; when (isGivenOrSolved fl) $ 
                          setEvBind v_new (EvCast v' (mkSymCo co))
                   ; return v_new }

          -- Add superclasses of this one here, See Note [Adding superclasses]. 
          -- But only if we are not simplifying the LHS of a rule. 
       ; sctx <- getTcSContext
       ; when (not (simplEqsOnly sctx)) $ newSCWorkFromFlavored d v_new fl cls xis 

       ; let cdict = CDictCan { cc_id     = v_new 
                              , cc_flavor = fl
                              , cc_tyargs = xis
                              , cc_class  = cls
                              , cc_depth  = d }

       ; updWorkListTcS (extendWorkListNonEq cdict) }
\end{code}

Note [Adding superclasses]
~~~~~~~~~~~~~~~~~~~~~~~~~~ 
Since dictionaries are canonicalized only once in their lifetime, the
place to add their superclasses is canonicalisation (The alternative
would be to do it during constraint solving, but we'd have to be
extremely careful to not repeatedly introduced the same superclass in
our worklist). Here is what we do:

For Givens: 
       We add all their superclasses as Givens. 

For Wanteds: 
       Generally speaking we want to be able to add superclasses of 
       wanteds for two reasons:

       (1) Oportunities for improvement. Example: 
                  class (a ~ b) => C a b 
           Wanted constraint is: C alpha beta 
           We'd like to simply have C alpha alpha. Similar 
           situations arise in relation to functional dependencies. 
           
       (2) To have minimal constraints to quantify over: 
           For instance, if our wanted constraint is (Eq a, Ord a) 
           we'd only like to quantify over Ord a. 

       To deal with (1) above we only add the superclasses of wanteds
       which may lead to improvement, that is: equality superclasses or 
       superclasses with functional dependencies. 

       We deal with (2) completely independently in TcSimplify. See 
       Note [Minimize by SuperClasses] in TcSimplify. 


       Moreover, in all cases the extra improvement constraints are 
       Derived. Derived constraints have an identity (for now), but 
       we don't do anything with their evidence. For instance they 
       are never used to rewrite other constraints. 

       See also [New Wanted Superclass Work] in TcInteract. 


For Deriveds: 
       We do nothing.

Here's an example that demonstrates why we chose to NOT add
superclasses during simplification: [Comes from ticket #4497]
 
   class Num (RealOf t) => Normed t
   type family RealOf x

Assume the generated wanted constraint is: 
   RealOf e ~ e, Normed e 
If we were to be adding the superclasses during simplification we'd get: 
   Num uf, Normed e, RealOf e ~ e, RealOf e ~ uf 
==> 
   e ~ uf, Num uf, Normed e, RealOf e ~ e 
==> [Spontaneous solve] 
   Num uf, Normed uf, RealOf uf ~ uf 

While looks exactly like our original constraint. If we add the superclass again we'd loop. 
By adding superclasses definitely only once, during canonicalisation, this situation can't 
happen.

\begin{code}

newSCWorkFromFlavored :: SubGoalDepth -- Depth
                      -> EvVar -> CtFlavor -> Class -> [Xi] -> TcS ()
-- Returns superclasses, see Note [Adding superclasses]
newSCWorkFromFlavored d ev flavor cls xis 
  | isDerived flavor 
  = return ()  -- Deriveds don't yield more superclasses because we will
               -- add them transitively in the case of wanteds. 

  | Just gk <- isGiven_maybe flavor 
  = case gk of 
      GivenOrig -> do { let sc_theta = immSuperClasses cls xis 
                      ; sc_vars <- mapM newEvVar sc_theta
                      ; sc_cts <- zipWithM (\scv ev_trm -> 
                                                do { setEvBind scv ev_trm
                                                   ; return $ 
                                                     CNonCanonical { cc_id = scv
                                                                   , cc_flavor = flavor
                                                                   , cc_depth = d }}) 
                                           sc_vars [EvSuperClass ev n | n <- [0..]]

                        -- Emit now, canonicalize later in a lazier fashion
                      ; updWorkListTcS $ appendWorkListCt sc_cts }
      GivenSolved -> return ()
      -- Seems very dangerous to add the superclasses for dictionaries that may be 
      -- partially solved because we may end up with evidence loops.

  | isEmptyVarSet (tyVarsOfTypes xis)
  = return () -- Wanteds with no variables yield no deriveds.
              -- See Note [Improvement from Ground Wanteds]

  | otherwise -- Wanted case, just add those SC that can lead to improvement. 
  = do { let sc_rec_theta = transSuperClasses cls xis 
             impr_theta   = filter is_improvement_pty sc_rec_theta 
             Wanted wloc  = flavor
       ; sc_cts <- mapM (\pty -> do { scv <- newDerivedId pty 
                                    ; return $ 
                                      CNonCanonical { cc_id = scv
                                                    , cc_flavor = Derived wloc
                                                    , cc_depth = d} }) impr_theta
       ; updWorkListTcS $ appendWorkListCt sc_cts }

is_improvement_pty :: PredType -> Bool 
-- Either it's an equality, or has some functional dependency
is_improvement_pty ty = go (predTypePredTree ty)
  where
    go (EqPred {})         = True 
    go (ClassPred cls _ty) = not $ null fundeps
      where (_,fundeps,_,_,_,_) = classExtraBigSig cls
    go (IPPred {})         = False
    go (TuplePred ts)      = any go ts
    go (IrredPred {})      = True -- Might have equalities after reduction?
\end{code}



\begin{code}
-- Irreducibles canonicalization
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
canIrredEvidence :: SubGoalDepth -- Depth
                 -> CtFlavor -> EvVar -> TcType -> TcS ()
canIrredEvidence d fl v ty 
  = do { (xi,co) <- flatten d fl ty -- co :: xi ~ ty
       ; v_new <- if isReflCo co || isGivenOrSolved fl then return v
                  else do { v' <- newEvVar xi
                          ; when (isWanted fl) $ 
                            setEvBind v  (EvCast v' co)
                          ; when (isGivenOrSolved fl) $ 
                            setEvBind v' (EvCast v (mkSymCo co))
                          ; return v' }
       ; updWorkListTcS $ 
         extendWorkListNonEq (CIrredEvCan { cc_id     = v_new
                                          , cc_flavor = fl
                                          , cc_ty     = xi 
                                          , cc_depth  = d }) }
\end{code}

%************************************************************************
%*                                                                      *
%*        Flattening (eliminating all function symbols)                 *
%*                                                                      *
%************************************************************************

Note [Flattening]
~~~~~~~~~~~~~~~~~~~~
  flatten ty  ==>   (xi, cc)
    where
      xi has no type functions
      cc = Auxiliary given (equality) constraints constraining
           the fresh type variables in xi.  Evidence for these 
           is always the identity coercion, because internally the
           fresh flattening skolem variables are actually identified
           with the types they have been generated to stand in for.

Note that it is flatten's job to flatten *every type function it sees*.
flatten is only called on *arguments* to type functions, by canEqGiven.

Recall that in comments we use alpha[flat = ty] to represent a
flattening skolem variable alpha which has been generated to stand in
for ty.

----- Example of flattening a constraint: ------
  flatten (List (F (G Int)))  ==>  (xi, cc)
    where
      xi  = List alpha
      cc  = { G Int ~ beta[flat = G Int],
              F beta ~ alpha[flat = F beta] }
Here
  * alpha and beta are 'flattening skolem variables'.
  * All the constraints in cc are 'given', and all their coercion terms 
    are the identity.

NB: Flattening Skolems only occur in canonical constraints, which
are never zonked, so we don't need to worry about zonking doing
accidental unflattening.

Note that we prefer to leave type synonyms unexpanded when possible,
so when the flattener encounters one, it first asks whether its
transitive expansion contains any type function applications.  If so,
it expands the synonym and proceeds; if not, it simply returns the
unexpanded synonym.

TODO: caching the information about whether transitive synonym
expansions contain any type function applications would speed things
up a bit; right now we waste a lot of energy traversing the same types
multiple times.

\begin{code}

-- Flatten a bunch of types all at once.
flattenMany :: SubGoalDepth -- Depth
            -> CtFlavor -> [Type] -> TcS ([Xi], [LCoercion])
-- Coercions :: Xi ~ Type 
flattenMany d ctxt tys 
  = do { (xis, cos) <- mapAndUnzipM (flatten d ctxt) tys
       ; return (xis, cos) }

-- Flatten a type to get rid of type function applications, returning
-- the new type-function-free type, and a collection of new equality
-- constraints.  See Note [Flattening] for more detail.
flatten :: SubGoalDepth -- Depth
        -> CtFlavor -> TcType -> TcS (Xi, LCoercion)
-- Postcondition: Coercion :: Xi ~ TcType
flatten d ctxt ty 
  | Just ty' <- tcView ty
  = do { (xi, co) <- flatten d ctxt ty'
	-- Preserve type synonyms if possible
       ; if isReflCo co 
         then return (ty, mkReflCo ty) -- Importantly, not xi!
         else return (xi, co) 
       }

flatten _d _ v@(TyVarTy _)
  = return (v, mkReflCo v)

flatten d ctxt (AppTy ty1 ty2)
  = do { (xi1,co1) <- flatten d ctxt ty1
       ; (xi2,co2) <- flatten d ctxt ty2
       ; return (mkAppTy xi1 xi2, mkAppCo co1 co2) }

flatten d ctxt (FunTy ty1 ty2)
  = do { (xi1,co1) <- flatten d ctxt ty1
       ; (xi2,co2) <- flatten d ctxt ty2
       ; return (mkFunTy xi1 xi2, mkFunCo co1 co2) }

flatten d fl (TyConApp tc tys)
  -- For a normal type constructor or data family application, we just
  -- recursively flatten the arguments.
  | not (isSynFamilyTyCon tc)
    = do { (xis,cos) <- flattenMany d fl tys
         ; return (mkTyConApp tc xis, mkTyConAppCo tc cos) }

  -- Otherwise, it's a type function application, and we have to
  -- flatten it away as well, and generate a new given equality constraint
  -- between the application and a newly generated flattening skolem variable.
  | otherwise
  = ASSERT( tyConArity tc <= length tys )	-- Type functions are saturated
      do { (xis, cos) <- flattenMany d fl tys
         ; let (xi_args, xi_rest)  = splitAt (tyConArity tc) xis
	       	 -- The type function might be *over* saturated
		 -- in which case the remaining arguments should
		 -- be dealt with by AppTys
               fam_ty = mkTyConApp tc xi_args
         ; (ret_co, rhs_var, ct) <-
             do { is_cached <- getRelevantInertFunEq tc xi_args fl 
                ; case is_cached of 
                    Just (rhs_var,ret_eq) -> return (ret_eq, rhs_var, [])
                    Nothing
                        | isGivenOrSolved fl ->
                            do { rhs_var <- newFlattenSkolemTy fam_ty
                               ; eqv <- newGivenEqVar fam_ty rhs_var (mkReflCo fam_ty)
                               ; let ct = CFunEqCan { cc_id     = eqv
                                                    , cc_flavor = fl -- Given
                                                    , cc_fun    = tc 
                                                    , cc_tyargs = xi_args 
                                                    , cc_rhs    = rhs_var 
                                                    , cc_depth  = d }
                               ; return (mkEqVarLCo eqv, rhs_var, [ct]) }
                        | otherwise ->
                    -- Derived or Wanted: make a new /unification/ flatten variable
                            do { rhs_var <- newFlexiTcSTy (typeKind fam_ty)
                               ; eqv <- newEqVar fam_ty rhs_var
                               ; let ct = CFunEqCan { cc_id = eqv
                                                    , cc_flavor = mkWantedFlavor fl
                                                    -- Always Wanted, not Derived
                                                    , cc_fun = tc
                                                    , cc_tyargs = xi_args
                                                    , cc_rhs    = rhs_var 
                                                    , cc_depth  = d }
                               ; return (mkEqVarLCo eqv, rhs_var, [ct]) } }

           -- Emit the flat constraints
         ; updWorkListTcS (appendWorkListCt ct)

         ; let (cos_args, cos_rest) = splitAt (tyConArity tc) cos
         ; return ( foldl AppTy rhs_var xi_rest
                  , foldl AppCo (mkSymCo ret_co `mkTransCo` mkTyConAppCo tc cos_args)
                                cos_rest) }

flatten d ctxt ty@(ForAllTy {})
-- We allow for-alls when, but only when, no type function
-- applications inside the forall involve the bound type variables.
  = do { let (tvs, rho) = splitForAllTys ty
       ; when (under_families tvs rho) $ flattenForAllErrorTcS ctxt ty
       ; (rho', co) <- flatten d ctxt rho
       ; return (mkForAllTys tvs rho', foldr mkForAllCo co tvs) }

  where under_families tvs rho 
            = go (mkVarSet tvs) rho 
            where go _bound (TyVarTy _tv) = False
                  go bound (TyConApp tc tys)
                      | isSynFamilyTyCon tc
                      , (args,rest) <- splitAt (tyConArity tc) tys
                      = (tyVarsOfTypes args `intersectsVarSet` bound) || any (go bound) rest
                      | otherwise = any (go bound) tys
                  go bound (FunTy arg res)  = go bound arg || go bound res
                  go bound (AppTy fun arg)  = go bound fun || go bound arg
                  go bound (ForAllTy tv ty) = go (bound `extendVarSet` tv) ty

\end{code}


\begin{code}

-----------------
canEq :: SubGoalDepth 
      -> CtFlavor -> EqVar -> Type -> Type -> TcS ()
canEq _d fl eqv ty1 ty2
  | eqType ty1 ty2	-- Dealing with equality here avoids
    	     	 	-- later spurious occurs checks for a~a
  = when (isWanted fl) (setEqBind eqv (mkReflCo ty1))

-- If one side is a variable, orient and flatten, 
-- WITHOUT expanding type synonyms, so that we tend to 
-- substitute a ~ Age rather than a ~ Int when @type Age = Int@
canEq d fl eqv (TyVarTy tv) ty2 = canEqVarTop d fl eqv tv ty2 True 
canEq d fl eqv ty1 (TyVarTy tv) = canEqVarTop d fl eqv tv ty1 False

-- Split up an equality between function types into two equalities.
canEq d fl eqv (FunTy s1 t1) (FunTy s2 t2)
  = do { (argeqv, reseqv) <- 
             if isWanted fl then 
                 do { argeqv <- newEqVar s1 s2 
                    ; reseqv <- newEqVar t1 t2 
                    ; setEqBind eqv
                      (mkFunCo (mkEqVarLCo argeqv) (mkEqVarLCo reseqv))
                    ; return (argeqv,reseqv) } 
             else if isGivenOrSolved fl then 
                      do { argeqv <- newEqVar s1 s2
                         ; setEqBind argeqv (mkNthCo 0 (mkEqVarLCo eqv))
                         ; reseqv <- newEqVar t1 t2
                         ; setEqBind reseqv (mkNthCo 1 (mkEqVarLCo eqv))
                         ; return (argeqv,reseqv) } 

             else -- Derived 
                 do { argeqv <- newDerivedId (mkEqPred (s1, s2))
                    ; reseqv <- newDerivedId (mkEqPred (t1, t2))
                    ; return (argeqv, reseqv) }

       ; canEq d fl argeqv s1 s2 -- Inherit original kinds, depths, and locations
       ; canEq d fl reseqv t1 t2 }

canEq d fl eqv (TyConApp fn tys) _ty2 
  | isSynFamilyTyCon fn, length tys == tyConArity fn
  = do { untch <- getUntouchables 
       ; ieqs <- getInertEqs
       ; eqv' <- rewriteFromInertEqs ieqs fl eqv 
       ; let (EqPred ty1' ty2') = predTypePredTree (evVarPred eqv')
       ; canEqLeaf d untch fl eqv' (classify ty1') (classify ty2') } 

canEq d fl eqv _ty1 (TyConApp fn tys)
  | isSynFamilyTyCon fn, length tys == tyConArity fn
  = do { untch <- getUntouchables 
       ; ieqs <- getInertEqs
       ; eqv' <- rewriteFromInertEqs ieqs fl eqv 
       ; let (EqPred ty1' ty2') = predTypePredTree (evVarPred eqv')
       ; canEqLeaf d untch fl eqv' (classify ty1') (classify ty2') }

canEq d fl eqv (TyConApp tc1 tys1) (TyConApp tc2 tys2)
  | isDecomposableTyCon tc1 && isDecomposableTyCon tc2
  , tc1 == tc2
  , length tys1 == length tys2
  = -- Generate equalities for each of the corresponding arguments
    do { argeqvs 
             <- if isWanted fl then
                    do { argeqvs <- zipWithM newEqVar tys1 tys2
                       ; setEqBind eqv
                         (mkTyConAppCo tc1 (map mkEqVarLCo argeqvs))
                       ; return argeqvs }
                else if isGivenOrSolved fl then
                    let go_one ty1 ty2 n = do
                          argeqv <- newEqVar ty1 ty2
                          setEqBind argeqv (mkNthCo n (mkEqVarLCo eqv))
                          return argeqv
                    in zipWith3M go_one tys1 tys2 [0..]

                else -- Derived 
                    zipWithM (\t1 t2 -> newDerivedId (mkEqPred (t1, t2))) tys1 tys2

       ; _unused <- zipWith3M (canEq d fl) argeqvs tys1 tys2 
                   -- Bleah
       ; return () }

-- See Note [Equality between type applications]
--     Note [Care with type applications] in TcUnify
canEq d fl eqv ty1 ty2
  | Nothing <- tcView ty1  -- Naked applications ONLY
  , Nothing <- tcView ty2  -- See Note [Naked given applications]
  , Just (s1,t1) <- tcSplitAppTy_maybe ty1
  , Just (s2,t2) <- tcSplitAppTy_maybe ty2
    = if isWanted fl 
      then do { eqv1 <- newEqVar s1 s2 
              ; eqv2 <- newEqVar t1 t2 
              ; setEqBind eqv
                (mkAppCo (mkEqVarLCo eqv1) (mkEqVarLCo eqv2))
              ; canEq d fl eqv1 s1 s2 
              ; canEq d fl eqv2 t1 t2 } 

      else if isDerived fl 
      then do { eqv1 <- newDerivedId (mkEqPred (s1, s2))
              ; eqv2 <- newDerivedId (mkEqPred (t1, t2))
              ; canEq d fl eqv1 s1 s2 
              ; canEq d fl eqv2 t1 t2 }

      else traceTcS "canEq/(app case)" $
           text "Ommitting decomposition of given equality between: " 
                    <+> ppr ty1 <+> text "and" <+> ppr ty2
              -- We cannot decompose given applications
      	      -- because we no longer have 'left' and 'right'

canEq d fl eqv s1@(ForAllTy {}) s2@(ForAllTy {})
 | tcIsForAllTy s1, tcIsForAllTy s2, 
   Wanted {} <- fl 
 = canEqFailure d fl eqv
 | otherwise
 = traceTcS "Ommitting decomposition of given polytype equality" (pprEq s1 s2)

-- Finally expand any type synonym applications.
canEq d fl eqv ty1 ty2 | Just ty1' <- tcView ty1 = canEq d fl eqv ty1' ty2
canEq d fl eqv ty1 ty2 | Just ty2' <- tcView ty2 = canEq d fl eqv ty1 ty2'
canEq d fl eqv _ _                               = canEqFailure d fl eqv

canEqFailure :: SubGoalDepth 
             -> CtFlavor -> EvVar -> TcS ()
canEqFailure d fl eqv = emitFrozenError fl eqv d 
\end{code}

Note [Naked given applications]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider: 
   data A a 
   type T a = A a 
and the given equality:  
   [G] A a ~ T Int 
We will reach the case canEq where we do a tcSplitAppTy_maybe, but if
we dont have the guards (Nothing <- tcView ty1) (Nothing <- tcView
ty2) then the given equation is going to fall through and get
completely forgotten!

What we want instead is this clause to apply only when there is no
immediate top-level synonym; if there is one it will be later on
unfolded by the later stages of canEq.

Test-case is in typecheck/should_compile/GivenTypeSynonym.hs


Note [Equality between type applications]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we see an equality of the form s1 t1 ~ s2 t2 we can always split
it up into s1 ~ s2 /\ t1 ~ t2, since s1 and s2 can't be type
functions (type functions use the TyConApp constructor, which never
shows up as the LHS of an AppTy).  Other than type functions, types
in Haskell are always 

  (1) generative: a b ~ c d implies a ~ c, since different type
      constructors always generate distinct types

  (2) injective: a b ~ a d implies b ~ d; we never generate the
      same type from different type arguments.


Note [Canonical ordering for equality constraints]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Implemented as (<+=) below:

  - Type function applications always come before anything else.  
  - Variables always come before non-variables (other than type
      function applications).

Note that we don't need to unfold type synonyms on the RHS to check
the ordering; that is, in the rules above it's OK to consider only
whether something is *syntactically* a type function application or
not.  To illustrate why this is OK, suppose we have an equality of the
form 'tv ~ S a b c', where S is a type synonym which expands to a
top-level application of the type function F, something like

  type S a b c = F d e

Then to canonicalize 'tv ~ S a b c' we flatten the RHS, and since S's
expansion contains type function applications the flattener will do
the expansion and then generate a skolem variable for the type
function application, so we end up with something like this:

  tv ~ x
  F d e ~ x

where x is the skolem variable.  This is one extra equation than
absolutely necessary (we could have gotten away with just 'F d e ~ tv'
if we had noticed that S expanded to a top-level type function
application and flipped it around in the first place) but this way
keeps the code simpler.

Unlike the OutsideIn(X) draft of May 7, 2010, we do not care about the
ordering of tv ~ tv constraints.  There are several reasons why we
might:

  (1) In order to be able to extract a substitution that doesn't
      mention untouchable variables after we are done solving, we might
      prefer to put touchable variables on the left. However, in and
      of itself this isn't necessary; we can always re-orient equality
      constraints at the end if necessary when extracting a substitution.

  (2) To ensure termination we might think it necessary to put
      variables in lexicographic order. However, this isn't actually 
      necessary as outlined below.

While building up an inert set of canonical constraints, we maintain
the invariant that the equality constraints in the inert set form an
acyclic rewrite system when viewed as L-R rewrite rules.  Moreover,
the given constraints form an idempotent substitution (i.e. none of
the variables on the LHS occur in any of the RHS's, and type functions
never show up in the RHS at all), the wanted constraints also form an
idempotent substitution, and finally the LHS of a given constraint
never shows up on the RHS of a wanted constraint.  There may, however,
be a wanted LHS that shows up in a given RHS, since we do not rewrite
given constraints with wanted constraints.

Suppose we have an inert constraint set


  tg_1 ~ xig_1         -- givens
  tg_2 ~ xig_2
  ...
  tw_1 ~ xiw_1         -- wanteds
  tw_2 ~ xiw_2
  ...

where each t_i can be either a type variable or a type function
application. Now suppose we take a new canonical equality constraint,
t' ~ xi' (note among other things this means t' does not occur in xi')
and try to react it with the existing inert set.  We show by induction
on the number of t_i which occur in t' ~ xi' that this process will
terminate.

There are several ways t' ~ xi' could react with an existing constraint:

TODO: finish this proof.  The below was for the case where the entire
inert set is an idempotent subustitution...

(b) We could have t' = t_j for some j.  Then we obtain the new
    equality xi_j ~ xi'; note that neither xi_j or xi' contain t_j.  We
    now canonicalize the new equality, which may involve decomposing it
    into several canonical equalities, and recurse on these.  However,
    none of the new equalities will contain t_j, so they have fewer
    occurrences of the t_i than the original equation.

(a) We could have t_j occurring in xi' for some j, with t' /=
    t_j. Then we substitute xi_j for t_j in xi' and continue.  However,
    since none of the t_i occur in xi_j, we have decreased the
    number of t_i that occur in xi', since we eliminated t_j and did not
    introduce any new ones.

\begin{code}
data TypeClassifier 
  = FskCls TcTyVar      -- ^ Flatten skolem 
  | VarCls TcTyVar      -- ^ Non-flatten-skolem variable 
  | FunCls TyCon [Type] -- ^ Type function, exactly saturated
  | OtherCls TcType     -- ^ Neither of the above

unClassify :: TypeClassifier -> TcType
unClassify (VarCls tv)      = TyVarTy tv
unClassify (FskCls tv) = TyVarTy tv 
unClassify (FunCls fn tys)  = TyConApp fn tys
unClassify (OtherCls ty)    = ty

classify :: TcType -> TypeClassifier

classify (TyVarTy tv) 
  | isTcTyVar tv, 
    FlatSkol {} <- tcTyVarDetails tv = FskCls tv
  | otherwise                        = VarCls tv
classify (TyConApp tc tys) | isSynFamilyTyCon tc
                           , tyConArity tc == length tys
                           = FunCls tc tys
classify ty                | Just ty' <- tcView ty
	                   = case classify ty' of
                               OtherCls {} -> OtherCls ty
                               var_or_fn   -> var_or_fn
                           | otherwise 
                           = OtherCls ty

-- See note [Canonical ordering for equality constraints].
reOrient :: CtFlavor -> TypeClassifier -> TypeClassifier -> Bool	
-- (t1 `reOrient` t2) responds True 
--   iff we should flip to (t2~t1)
-- We try to say False if possible, to minimise evidence generation
--
-- Postcondition: After re-orienting, first arg is not OTherCls
reOrient _fl (OtherCls {}) (FunCls {})   = True
reOrient _fl (OtherCls {}) (FskCls {})   = True
reOrient _fl (OtherCls {}) (VarCls {})   = True
reOrient _fl (OtherCls {}) (OtherCls {}) = panic "reOrient"  -- One must be Var/Fun

reOrient _fl (FunCls {})   (VarCls _tv)  = False  
  -- But consider the following variation: isGiven fl && isMetaTyVar tv

  -- See Note [No touchables as FunEq RHS] in TcSMonad
reOrient _fl (FunCls {}) _                = False             -- Fun/Other on rhs

reOrient _fl (VarCls {}) (FunCls {})      = True 

reOrient _fl (VarCls {}) (FskCls {})      = False

reOrient _fl (VarCls {})  (OtherCls {})   = False
reOrient _fl (VarCls tv1)  (VarCls tv2)  
  | isMetaTyVar tv2 && not (isMetaTyVar tv1) = True 
  | otherwise                                = False 
  -- Just for efficiency, see CTyEqCan invariants 

reOrient _fl (FskCls {}) (VarCls tv2)     = isMetaTyVar tv2 
  -- Just for efficiency, see CTyEqCan invariants

reOrient _fl (FskCls {}) (FskCls {})     = False
reOrient _fl (FskCls {}) (FunCls {})     = True 
reOrient _fl (FskCls {}) (OtherCls {})   = False 

------------------

canEqVarTop :: SubGoalDepth -- Depth
            -> CtFlavor -> EqVar 
            -> TcTyVar -> Type 
            -> Bool -- True iff (eqv : tv ~ ty, False when (eqv : ty ~ tv) 
            -> TcS ()
canEqVarTop d fl eqv tv ty tv_left 
  = do { untch <- getUntouchables
       ; ieqs  <- getInertEqs 
       ; case lookupVarEnv (fst ieqs) tv of 
           Just (cc,co) | cc_flavor cc `canRewrite` fl -> 
                          -- co : tv ~ rhs 
              do { v_new <- newEqVar (cc_rhs cc) ty  -- v_new :: rhs ~ ty

                          -- Some careful coercion calculations below
                 ; let co_for_wanted 
                        | tv_left   = co `mkTransCo` mkEqVarLCo v_new
                                      -- tv ~ rhs ~ ty  
                        | otherwise = mkSymCo (mkEqVarLCo v_new) `mkTransCo` (mkSymCo co)
                                      -- ty ~ rhs ~ tv
                 ; let co_for_given 
                        | tv_left   = mkSymCo co `mkTransCo` mkEqVarLCo eqv
                                      -- rhs ~ tv ~ ty 
                        | otherwise = mkSymCo co `mkTransCo` mkSymCo (mkEqVarLCo eqv)
                                      -- rhs ~ tv ~ ty

                 ; when (isWanted fl) $ setEqBind eqv co_for_wanted
                 ; when (isGivenOrSolved fl) $ setEqBind v_new co_for_given 

                          -- Repeat!
                 ; canEq d fl v_new (cc_rhs cc) ty }

                -- Otherwise deeply rewrite (to maximise caching) and call canEqLeaf, 
                -- which will deal with flattening. 
           _ -> do { eqv' <- rewriteFromInertEqs ieqs fl eqv 
                   ; let (EqPred ty1' ty2') = predTypePredTree (evVarPred eqv')
                   ; canEqLeaf d untch fl eqv' (classify ty1') (classify ty2') }
       }
       -- NB: don't use VarCls directly because tv1 or tv2 may be scolems!

canEqLeaf :: SubGoalDepth -- Depth
          -> TcsUntouchables 
          -> CtFlavor -> EqVar 
          -> TypeClassifier -> TypeClassifier -> TcS ()
-- Canonicalizing "leaf" equality constraints which cannot be
-- decomposed further (ie one of the types is a variable or
-- saturated type function application).  

  -- Preconditions: 
  --    * one of the two arguments is not OtherCls
  --    * the two types are not equal (looking through synonyms)
canEqLeaf d _untch fl eqv cls1 cls2 
  | cls1 `re_orient` cls2
  = do { eqv' <- if isWanted fl 
                 then do { eqv' <- newEqVar s2 s1
                         ; setEqBind eqv (mkSymCo (mkEqVarLCo eqv'))
                         ; return eqv' } 
                 else if isGivenOrSolved fl then
                      do { eqv' <- newEqVar s2 s1
                         ; setEqBind eqv' (mkSymCo (mkEqVarLCo eqv))
                         ; return eqv' }
                          
                 else -- Derived
                     newDerivedId (mkEqPred (s2, s1))
       ; canEqLeafOriented d fl eqv' cls2 s1 }

  | otherwise
  = do { traceTcS "canEqLeaf" (ppr (unClassify cls1) $$ ppr (unClassify cls2))
       ; canEqLeafOriented d fl eqv cls1 s2 }
  where
    re_orient = reOrient fl 
    s1 = unClassify cls1  
    s2 = unClassify cls2  

------------------
canEqLeafOriented :: SubGoalDepth -- Depth
                  -> CtFlavor -> EqVar 
                  -> TypeClassifier -> TcType -> TcS ()
-- First argument is not OtherCls
canEqLeafOriented d fl eqv cls1@(FunCls fn tys1) s2         -- cv : F tys1
  | let k1 = kindAppResult (tyConKind fn) tys1,
    let k2 = typeKind s2, 
    not (k1 `compatKind` k2) -- Establish the kind invariant for CFunEqCan
  = canEqFailure d fl eqv
    -- Eagerly fails, see Note [Kind errors] in TcInteract

  | otherwise 
  = ASSERT2( isSynFamilyTyCon fn, ppr (unClassify cls1) )
    do { (xis1,cos1) <- flattenMany d fl tys1 -- Flatten type function arguments
                                              -- cos1 :: xis1 ~ tys1
       ; (xi2, co2) <- flatten d fl s2        -- Flatten entire RHS
                                              -- co2  :: xi2 ~ s2
       ; let no_flattening_happened = all isReflCo (co2:cos1)

       ; eqv_new <- if no_flattening_happened  || isGivenOrSolved fl 
                    then return eqv
                    else if isWanted fl then 
                          do { eqv' <- newEqVar (unClassify (FunCls fn xis1)) xi2

                             ; let -- cv' : F xis ~ xi2
                                   cv' = mkEqVarLCo eqv'
                                   -- fun_co :: F xis1 ~ F tys1
                                   fun_co = mkTyConAppCo fn cos1
                                   -- want_co :: F tys1 ~ s2
                                   want_co = mkSymCo fun_co
                                                `mkTransCo` cv'
                                                `mkTransCo` co2
                             ; setEqBind eqv want_co
                             ; return eqv' }
                    else -- Derived 
                        newDerivedId (mkEqPred (unClassify (FunCls fn xis1), xi2))

       ; let final_cc = CFunEqCan { cc_id     = eqv_new
                                  , cc_flavor = fl
                                  , cc_fun    = fn
                                  , cc_tyargs = xis1 
                                  , cc_rhs    = xi2 
                                  , cc_depth  = d }
       ; updWorkListTcS $ extendWorkListEq final_cc } 

-- Otherwise, we have a variable on the left, so call canEqLeafTyVarLeft
canEqLeafOriented d fl eqv (FskCls tv) s2 
  = canEqLeafTyVarLeft d fl eqv tv s2 
canEqLeafOriented d fl eqv (VarCls tv) s2 
  = canEqLeafTyVarLeft d fl eqv tv s2 
canEqLeafOriented _d _ eqv (OtherCls ty1) ty2 
  = pprPanic "canEqLeaf" (ppr eqv $$ ppr ty1 $$ ppr ty2)

canEqLeafTyVarLeft :: SubGoalDepth -- Depth
                   -> CtFlavor -> EqVar
                   -> TcTyVar -> TcType -> TcS ()
-- Establish invariants of CTyEqCans 
canEqLeafTyVarLeft d fl eqv tv s2       -- cv : tv ~ s2
  | not (k1 `compatKind` k2) -- Establish the kind invariant for CTyEqCan
  = canEqFailure d fl eqv
       -- Eagerly fails, see Note [Kind errors] in TcInteract
  | otherwise
  = do { (xi2, co) <- flatten d fl s2      -- Flatten RHS   co : xi2 ~ s2
       ; mxi2' <- canOccursCheck fl tv xi2 -- Do an occurs check, and return a possibly
                                           -- unfolded version of the RHS, if we had to 
                                           -- unfold any type synonyms to get rid of tv.
       ; case mxi2' of {
           Nothing   -> canEqFailure d fl eqv ;
           Just xi2' ->
    do { let no_flattening_happened = isReflCo co
       ; eqv_new <- if no_flattening_happened  || isGivenOrSolved fl 
                    then return eqv
                    else if isWanted fl then 
                          do { eqv' <- newEqVar (mkTyVarTy tv) xi2'  -- cv' : tv ~ xi2
                             ; setEqBind eqv $ mkTransCo (mkEqVarLCo eqv') co
                             ; return eqv' }
                    else -- Derived
                        newDerivedId (mkEqPred (mkTyVarTy tv, xi2'))

       ; let final_cc = CTyEqCan { cc_id     = eqv_new
                                 , cc_flavor = fl
                                 , cc_tyvar  = tv
                                 , cc_rhs    = xi2' 
                                 , cc_depth  = d }
       ; updWorkListTcS $ extendWorkListEq final_cc } } }
  where
    k1 = tyVarKind tv
    k2 = typeKind s2

-- See Note [Type synonyms and canonicalization].
-- Check whether the given variable occurs in the given type.  We may
-- have needed to do some type synonym unfolding in order to get rid
-- of the variable, so we also return the unfolded version of the
-- type, which is guaranteed to be syntactically free of the given
-- type variable.  If the type is already syntactically free of the
-- variable, then the same type is returned.
--
-- Precondition: the two types are not equal (looking though synonyms)
canOccursCheck :: CtFlavor -> TcTyVar -> Xi -> TcS (Maybe Xi)
canOccursCheck _gw tv xi = return (expandAway tv xi)
\end{code}

@expandAway tv xi@ expands synonyms in xi just enough to get rid of
occurrences of tv, if that is possible; otherwise, it returns Nothing.
For example, suppose we have
  type F a b = [a]
Then
  expandAway b (F Int b) = Just [Int]
but
  expandAway a (F a Int) = Nothing

We don't promise to do the absolute minimum amount of expanding
necessary, but we try not to do expansions we don't need to.  We
prefer doing inner expansions first.  For example,
  type F a b = (a, Int, a, [a])
  type G b   = Char
We have
  expandAway b (F (G b)) = F Char
even though we could also expand F to get rid of b.

\begin{code}
expandAway :: TcTyVar -> Xi -> Maybe Xi
expandAway tv t@(TyVarTy tv') 
  | tv == tv' = Nothing
  | otherwise = Just t
expandAway tv xi
  | not (tv `elemVarSet` tyVarsOfType xi) = Just xi
expandAway tv (AppTy ty1 ty2) 
  = do { ty1' <- expandAway tv ty1
       ; ty2' <- expandAway tv ty2 
       ; return (mkAppTy ty1' ty2') }
-- mkAppTy <$> expandAway tv ty1 <*> expandAway tv ty2
expandAway tv (FunTy ty1 ty2)
  = do { ty1' <- expandAway tv ty1 
       ; ty2' <- expandAway tv ty2 
       ; return (mkFunTy ty1' ty2') } 
-- mkFunTy <$> expandAway tv ty1 <*> expandAway tv ty2
expandAway tv ty@(ForAllTy {}) 
  = let (tvs,rho) = splitForAllTys ty
        tvs_knds  = map tyVarKind tvs 
    in if tv `elemVarSet` tyVarsOfTypes tvs_knds then
       -- Can't expand away the kinds unless we create 
       -- fresh variables which we don't want to do at this point.
           Nothing 
       else do { rho' <- expandAway tv rho
               ; return (mkForAllTys tvs rho') }
-- For a type constructor application, first try expanding away the
-- offending variable from the arguments.  If that doesn't work, next
-- see if the type constructor is a type synonym, and if so, expand
-- it and try again.
expandAway tv ty@(TyConApp tc tys)
  = (mkTyConApp tc <$> mapM (expandAway tv) tys) <|> (tcView ty >>= expandAway tv)

\end{code}

Note [Type synonyms and canonicalization]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We treat type synonym applications as xi types, that is, they do not
count as type function applications.  However, we do need to be a bit
careful with type synonyms: like type functions they may not be
generative or injective.  However, unlike type functions, they are
parametric, so there is no problem in expanding them whenever we see
them, since we do not need to know anything about their arguments in
order to expand them; this is what justifies not having to treat them
as specially as type function applications.  The thing that causes
some subtleties is that we prefer to leave type synonym applications
*unexpanded* whenever possible, in order to generate better error
messages.

If we encounter an equality constraint with type synonym applications
on both sides, or a type synonym application on one side and some sort
of type application on the other, we simply must expand out the type
synonyms in order to continue decomposing the equality constraint into
primitive equality constraints.  For example, suppose we have

  type F a = [Int]

and we encounter the equality

  F a ~ [b]

In order to continue we must expand F a into [Int], giving us the
equality

  [Int] ~ [b]

which we can then decompose into the more primitive equality
constraint

  Int ~ b.

However, if we encounter an equality constraint with a type synonym
application on one side and a variable on the other side, we should
NOT (necessarily) expand the type synonym, since for the purpose of
good error messages we want to leave type synonyms unexpanded as much
as possible.

However, there is a subtle point with type synonyms and the occurs
check that takes place for equality constraints of the form tv ~ xi.
As an example, suppose we have

  type F a = Int

and we come across the equality constraint

  a ~ F a

This should not actually fail the occurs check, since expanding out
the type synonym results in the legitimate equality constraint a ~
Int.  We must actually do this expansion, because unifying a with F a
will lead the type checker into infinite loops later.  Put another
way, canonical equality constraints should never *syntactically*
contain the LHS variable in the RHS type.  However, we don't always
need to expand type synonyms when doing an occurs check; for example,
the constraint

  a ~ F b

is obviously fine no matter what F expands to. And in this case we
would rather unify a with F b (rather than F b's expansion) in order
to get better error messages later.

So, when doing an occurs check with a type synonym application on the
RHS, we use some heuristics to find an expansion of the RHS which does
not contain the variable from the LHS.  In particular, given

  a ~ F t1 ... tn

we first try expanding each of the ti to types which no longer contain
a.  If this turns out to be impossible, we next try expanding F
itself, and so on.


%************************************************************************
%*                                                                      *
%*          Functional dependencies, instantiation of equations
%*                                                                      *
%************************************************************************

When we spot an equality arising from a functional dependency,
we now use that equality (a "wanted") to rewrite the work-item
constraint right away.  This avoids two dangers

 Danger 1: If we send the original constraint on down the pipeline
           it may react with an instance declaration, and in delicate
	   situations (when a Given overlaps with an instance) that
	   may produce new insoluble goals: see Trac #4952

 Danger 2: If we don't rewrite the constraint, it may re-react
           with the same thing later, and produce the same equality
           again --> termination worries.

To achieve this required some refactoring of FunDeps.lhs (nicer
now!).  

\begin{code}
rewriteWithFunDeps :: [Equation]
                   -> [Xi] 
                   -> WantedLoc 
                   -> TcS (Maybe ([Xi], [LCoercion], [(EvVar,WantedLoc)])) 
                                           -- Not quite a WantedEvVar unfortunately
                                           -- Because our intention could be to make 
                                           -- it derived at the end of the day
-- NB: The flavor of the returned EvVars will be decided by the caller
-- Post: returns no trivial equalities (identities)
rewriteWithFunDeps eqn_pred_locs xis wloc
 = do { fd_ev_poss <- mapM (instFunDepEqn wloc) eqn_pred_locs
      ; let fd_ev_pos :: [(Int,(EqVar,WantedLoc))]
            fd_ev_pos = concat fd_ev_poss
            (rewritten_xis, cos) = unzip (rewriteDictParams fd_ev_pos xis)
      ; if null fd_ev_pos then return Nothing
        else return (Just (rewritten_xis, cos, map snd fd_ev_pos)) }

instFunDepEqn :: WantedLoc -> Equation -> TcS [(Int,(EvVar,WantedLoc))]
-- Post: Returns the position index as well as the corresponding FunDep equality
instFunDepEqn wl (FDEqn { fd_qtvs = qtvs, fd_eqs = eqs
                        , fd_pred1 = d1, fd_pred2 = d2 })
  = do { let tvs = varSetElems qtvs
       ; tvs' <- mapM instFlexiTcS tvs
       ; let subst = zipTopTvSubst tvs (mkTyVarTys tvs')
       ; foldM (do_one subst) [] eqs }
  where 
    do_one subst ievs (FDEq { fd_pos = i, fd_ty_left = ty1, fd_ty_right = ty2 })
       = let sty1 = Type.substTy subst ty1 
             sty2 = Type.substTy subst ty2 
         in if eqType sty1 sty2 then return ievs -- Return no trivial equalities
            else do { eqv <- newEqVar sty1 sty2
                    ; let wl' = push_ctx wl 
                    ; return $ (i,(eqv,wl')):ievs }

    push_ctx :: WantedLoc -> WantedLoc 
    push_ctx loc = pushErrCtxt FunDepOrigin (False, mkEqnMsg d1 d2) loc

mkEqnMsg :: (TcPredType, SDoc) 
         -> (TcPredType, SDoc) -> TidyEnv -> TcM (TidyEnv, SDoc)
mkEqnMsg (pred1,from1) (pred2,from2) tidy_env
  = do  { zpred1 <- TcM.zonkTcPredType pred1
        ; zpred2 <- TcM.zonkTcPredType pred2
	; let { tpred1 = tidyType tidy_env zpred1
              ; tpred2 = tidyType tidy_env zpred2 }
	; let msg = vcat [ptext (sLit "When using functional dependencies to combine"),
			  nest 2 (sep [ppr tpred1 <> comma, nest 2 from1]), 
			  nest 2 (sep [ppr tpred2 <> comma, nest 2 from2])]
	; return (tidy_env, msg) }

rewriteDictParams :: [(Int,(EqVar,WantedLoc))] -- A set of coercions : (pos, ty' ~ ty)
                  -> [Type]                    -- A sequence of types: tys
                  -> [(Type,LCoercion)]      -- Returns: [(ty', co : ty' ~ ty)]
rewriteDictParams param_eqs tys
  = zipWith do_one tys [0..]
  where
    do_one :: Type -> Int -> (Type,LCoercion)
    do_one ty n = case lookup n param_eqs of
                    Just wev -> (get_fst_ty wev, mkEqVarLCo (fst wev))
                    Nothing  -> (ty,             mkReflCo ty)	-- Identity

    get_fst_ty (wev,_wloc) 
      | Just (ty1, _) <- getEqPredTys_maybe (evVarPred wev )
      = ty1
      | otherwise 
      = panic "rewriteDictParams: non equality fundep!?"

        
emitFDWork :: Bool
           -> [(EvVar,WantedLoc)] 
           -> SubGoalDepth -> TcS () 
emitFDWork as_wanted evlocs d 
  = updWorkListTcS (appendWorkListCt fd_cts)
  where fd_cts = map mk_fd_ct evlocs 
        mk_fl wl = if as_wanted then (Wanted wl) else (Derived wl)
        mk_fd_ct (v,wl) = CNonCanonical { cc_id = v
                                        , cc_flavor = mk_fl wl 
                                        , cc_depth = d }

emitFDWorkAsDerived, emitFDWorkAsWanted :: [(EvVar,WantedLoc)] 
                                        -> SubGoalDepth 
                                        -> TcS () 
emitFDWorkAsDerived = emitFDWork False
emitFDWorkAsWanted  = emitFDWork True 

\end{code}