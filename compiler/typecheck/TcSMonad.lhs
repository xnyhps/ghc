\begin{code}
-- Type definitions for the constraint solver
module TcSMonad ( 

       -- Canonical constraints, definition is now in TcRnTypes

    WorkList(..), isEmptyWorkList, emptyWorkList,
    workListFromEq, workListFromNonEq, workListFromCt, 
    extendWorkListEq, extendWorkListNonEq, extendWorkListCt, appendWorkListCt,
                    

    getTcSWorkList, updWorkListTcS, 

    Ct(..), Xi, tyVarsOfCt, tyVarsOfCts, tyVarsOfCDicts, 
    emitFrozenError,

    isWanted, isGivenOrSolved, isDerived,
    isGivenOrSolvedCt, isGivenCt_maybe, 
    isWantedCt, isDerivedCt, pprFlavorArising,

    isFlexiTcsTv,

    canRewrite, canSolve,
    combineCtLoc, mkSolvedFlavor, mkGivenFlavor,
    mkWantedFlavor,
    getWantedLoc,

    TcS, runTcS, failTcS, panicTcS, traceTcS, -- Basic functionality 
    traceFireTcS, bumpStepCountTcS, doWithInert,
{-     tryTcS, nestImplicTcS, recoverTcS, DV: Will figure out later -}
    wrapErrTcS, wrapWarnTcS,

    SimplContext(..), isInteractive, simplEqsOnly, performDefaulting,

       -- Creation of evidence variables
    newEvVar,
    newDerivedId, newGivenEqVar,
    newEqVar, newIPVar, newDictVar, newKindConstraint,

       -- Setting evidence variables 
    setEqBind,
    setIPBind,
    setDictBind,
    setEvBind,

    setWantedTyBind,

    getInstEnvs, getFamInstEnvs,                -- Getting the environments
    getTopEnv, getGblEnv, getTcEvBinds, getUntouchables,
    getTcEvBindsBag, getTcSContext, getTcSTyBinds, getTcSTyBindsMap,

    newFlattenSkolemTy,                         -- Flatten skolems 

        -- Inerts 
    InertSet(..), 
    getInertEqs, getRelevantInertFunEq, rewriteFromInertEqs, 
    tyVarsOfInert, emptyInert, getTcSInerts, updInertSet, extractUnsolved,
    extractUnsolvedTcS,
    updInertSetTcS, updInertSetTcS_, partitionCCanMap, partitionEqMap,
    getRelevantCts,
    CCanMap (..),


    instDFunTypes,                              -- Instantiation
    instDFunConstraints,          
    newFlexiTcSTy, instFlexiTcS,

    compatKind,

    TcsUntouchables,
    isTouchableMetaTyVar,
    isTouchableMetaTyVar_InRange, 

    getDefaultInfo, getDynFlags,

    matchClass, matchFam, MatchInstResult (..), 
    checkWellStagedDFun, 
    warnTcS,
    pprEq                                    -- Smaller utils, re-exported from TcM
                                             -- TODO (DV): these are only really used in the 
                                             -- instance matcher in TcSimplify. I am wondering
                                             -- if the whole instance matcher simply belongs
                                             -- here 
) where 

#include "HsVersions.h"

import HscTypes
import BasicTypes 

import Inst
import InstEnv 
import FamInst 
import FamInstEnv

import qualified TcRnMonad as TcM
import qualified TcMType as TcM
import qualified TcEnv as TcM 
       ( checkWellStaged, topIdLvl, tcLookupFamInst, tcGetDefaultTys )
import Kind
import TcType
import DynFlags

import Coercion
import Class
import TyCon
import TypeRep 

import Name
import Var
import VarEnv
import Outputable
import Bag
import MonadUtils
import VarSet
import Pair
import FastString

import HsBinds               -- for TcEvBinds stuff 
import Id 
import TcRnTypes
import Data.IORef

import Unique 
import UniqFM
import Maybes ( orElse )

#ifdef DEBUG
import StaticFlags( opt_PprStyle_Debug )
import Control.Monad( when )
#endif
\end{code}

\begin{code}
compatKind :: Kind -> Kind -> Bool
compatKind k1 k2 = k1 `isSubKind` k2 || k2 `isSubKind` k1 

\end{code}

%************************************************************************
%*									*
%*                            Worklists                                *
%*  Canonical and non-canonical constraints that the simplifier has to  *
%*  work on. Including their simplification depths.                     *
%*                                                                      *
%*									*
%************************************************************************

Note [WorkList]
~~~~~~~~~~~~~~~

A WorkList contains canonical and non-canonical items (of all flavors). 
Notice that each Ct now has a simplification depth. We may 
consider using this depth for prioritization as well in the future. 

As a simple form of priority queue, our worklist separates out
equalities (wl_eqs) from the rest of the canonical constraints, 
so that it's easier to deal with them first, but the separation 
is not strictly necessary. Notice that non-canonical constraints 
are also parts of the worklist. 

Note [NonCanonical Semantics]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Note that canonical constraints involve a CNonCanonical constructor. In the worklist
we use this constructor for constraints that have not yet been canonicalized such as 
   [Int] ~ [a] 
In other words, all constraints start life as NonCanonicals. 

On the other hand, in the Inert Set (see below) the presence of a NonCanonical somewhere
means that we have a ``frozen error''. 

NonCanonical constraints never interact directly with other constraints -- but they can
be rewritten by equalities (for instance if a non canonical exists in the inert, we'd 
better rewrite it as much as possible before reporting it as an error to the user)

\begin{code}

-- See Note [WorkList]
data WorkList = WorkList { wl_eqs  :: [Ct], wl_rest :: [Ct] }

extendWorkListEq :: Ct -> WorkList -> WorkList
-- Extension by equality
extendWorkListEq ct wl = wl { wl_eqs = ct : wl_eqs wl }

extendWorkListNonEq :: Ct -> WorkList -> WorkList
-- Extension by non equality
extendWorkListNonEq ct wl = wl { wl_rest = ct : wl_rest wl }

extendWorkListCt :: Ct -> WorkList -> WorkList
-- Agnostic
extendWorkListCt ct wl
 | isCoVar (cc_id ct) = extendWorkListEq ct wl
 | otherwise = extendWorkListNonEq ct wl

appendWorkListCt :: [Ct] -> WorkList -> WorkList
appendWorkListCt cts wl = foldr extendWorkListCt wl cts

isEmptyWorkList :: WorkList -> Bool
isEmptyWorkList wl = null (wl_eqs wl) &&  null (wl_rest wl)

emptyWorkList :: WorkList
emptyWorkList = WorkList { wl_eqs  = [], wl_rest = [] }

workListFromEq :: Ct -> WorkList
workListFromEq ct = WorkList { wl_eqs = [ct], wl_rest = [] }

workListFromNonEq :: Ct -> WorkList
workListFromNonEq ct = WorkList { wl_eqs = [], wl_rest = [ct] }

workListFromCt :: Ct -> WorkList
-- Agnostic 
workListFromCt ct | isCoVar (cc_id ct) = workListFromEq ct 
                  | otherwise          = workListFromNonEq ct

-- Pretty printing 
instance Outputable WorkList where 
  ppr wl = vcat [ text "WorkList (eqs)   = " <+> ppr (wl_eqs wl)
                , text "WorkList (rest)  = " <+> ppr (wl_rest wl)
                ]

\end{code}

%************************************************************************
%*									*
%*                            Inert sets                                *
%*                                                                      *
%*									*
%************************************************************************


Note [InertSet invariants]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
An InertSet is a bag of canonical constraints, with the following invariants:

  1 No two constraints react with each other. 
    
    A tricky case is when there exists a given (solved) dictionary 
    constraint and a wanted identical constraint in the inert set, but do 
    not react because reaction would create loopy dictionary evidence for 
    the wanted. See note [Recursive dictionaries]

  2 Given equalities form an idempotent substitution [none of the
    given LHS's occur in any of the given RHS's or reactant parts]

  3 Wanted equalities also form an idempotent substitution

  4 The entire set of equalities is acyclic.

  5 Wanted dictionaries are inert with the top-level axiom set 

  6 Equalities of the form tv1 ~ tv2 always have a touchable variable
    on the left (if possible).

  7 No wanted constraints tv1 ~ tv2 with tv1 touchable. Such constraints
    will be marked as solved right before being pushed into the inert set. 
    See note [Touchables and givens].

  8 No Given constraint mentions a touchable unification variable, but 
    Given/Solved may do so. 

  9 Given constraints will also have their superclasses in the inert set, 
    but Given/Solved will not. 
 
Note that 6 and 7 are /not/ enforced by canonicalization but rather by 
insertion in the inert list, ie by TcInteract. 

During the process of solving, the inert set will contain some
previously given constraints, some wanted constraints, and some given
constraints which have arisen from solving wanted constraints. For
now we do not distinguish between given and solved constraints.

Note that we must switch wanted inert items to given when going under an
implication constraint (when in top-level inference mode).

\begin{code}

data CCanMap a = CCanMap { cts_given   :: UniqFM Cts
                                          -- Invariant: all Given
                         , cts_derived :: UniqFM Cts 
                                          -- Invariant: all Derived
                         , cts_wanted  :: UniqFM Cts } 
                                          -- Invariant: all Wanted

cCanMapToBag :: CCanMap a -> Cts 
cCanMapToBag cmap = foldUFM unionBags rest_wder (cts_given cmap)
  where rest_wder = foldUFM unionBags rest_der  (cts_wanted cmap) 
        rest_der  = foldUFM unionBags emptyCts  (cts_derived cmap)

emptyCCanMap :: CCanMap a 
emptyCCanMap = CCanMap { cts_given = emptyUFM, cts_derived = emptyUFM, cts_wanted = emptyUFM } 

updCCanMap:: Uniquable a => (a,Ct) -> CCanMap a -> CCanMap a 
updCCanMap (a,ct) cmap 
  = case cc_flavor ct of 
      Wanted {}  -> cmap { cts_wanted  = insert_into (cts_wanted cmap)  } 
      Given {}   -> cmap { cts_given   = insert_into (cts_given cmap)   }
      Derived {} -> cmap { cts_derived = insert_into (cts_derived cmap) }
  where 
    insert_into m = addToUFM_C unionBags m a (singleCt ct)

getRelevantCts :: Uniquable a => a -> CCanMap a -> (Cts, CCanMap a) 
-- Gets the relevant constraints and returns the rest of the CCanMap
getRelevantCts a cmap 
    = let relevant = lookup (cts_wanted cmap) `unionBags`
                     lookup (cts_given cmap)  `unionBags`
                     lookup (cts_derived cmap) 
          residual_map = cmap { cts_wanted  = delFromUFM (cts_wanted cmap) a
                              , cts_given   = delFromUFM (cts_given cmap) a
                              , cts_derived = delFromUFM (cts_derived cmap) a }
      in (relevant, residual_map) 
  where
    lookup map = lookupUFM map a `orElse` emptyCts

partitionCCanMap :: (Ct -> Bool) -> CCanMap a -> (Cts,CCanMap a) 
-- All constraints that /match/ the predicate go in the bag, the rest remain in the map
partitionCCanMap pred cmap
  = let (ws_map,ws) = foldUFM_Directly aux (emptyUFM,emptyCts) (cts_wanted cmap) 
        (ds_map,ds) = foldUFM_Directly aux (emptyUFM,emptyCts) (cts_derived cmap)
        (gs_map,gs) = foldUFM_Directly aux (emptyUFM,emptyCts) (cts_given cmap) 
    in (ws `andCts` ds `andCts` gs, cmap { cts_wanted  = ws_map
                                         , cts_given   = gs_map
                                         , cts_derived = ds_map }) 
  where aux k this_cts (mp,acc_cts) = (new_mp, new_acc_cts)
                                    where new_mp      = addToUFM mp k cts_keep
                                          new_acc_cts = acc_cts `andCts` cts_out
                                          (cts_out, cts_keep) = partitionBag pred this_cts

partitionEqMap :: (Ct -> Bool) -> TyVarEnv (Ct,Coercion) -> (Cts, TyVarEnv (Ct,Coercion))
partitionEqMap pred isubst 
  = let eqs_out = foldVarEnv extend_if_pred emptyCts isubst
        eqs_in  = filterVarEnv_Directly (\_ (ct,_) -> not (pred ct)) isubst
    in (eqs_out, eqs_in)
  where extend_if_pred (ct,_) cts = if pred ct then extendCts cts ct else cts 


extractUnsolvedCMap :: CCanMap a -> (Cts, CCanMap a)
-- Gets the wanted or derived constraints and returns a residual
-- CCanMap with only givens.
extractUnsolvedCMap cmap =
  let wntd = foldUFM unionBags emptyCts (cts_wanted cmap)
      derd = foldUFM unionBags emptyCts (cts_derived cmap)
  in (wntd `unionBags` derd, 
      cmap { cts_wanted = emptyUFM, cts_derived = emptyUFM })

-- See Note [InertSet invariants]
data InertSet 
  = IS { inert_eqs     :: TyVarEnv (Ct,Coercion) 
         -- Must all be CTyEqCans! If an entry exists of the form: 
         --   a |-> ct,co
         -- Then ct = CTyEqCan { cc_tyvar = a, cc_rhs = xi } 
         -- And  co : a ~ xi
       , inert_eq_tvs  :: InScopeSet -- Invariant: superset of inert_eqs tvs

       , inert_dicts        :: CCanMap Class -- Dictionaries only, index is the class
          -- DV: Maybe later we want to reconsider using TypeMaps (coreSyn.TrieMap)

       , inert_ips          :: CCanMap (IPName Name)      -- Implicit parameters 
       , inert_funeqs       :: CCanMap TyCon              -- Type family equalities only, index is the type family
          -- DV: This is more ready to be used with TypeMaps (coreSyn.TrieMap)

               -- This representation allows us to quickly get to the relevant 
               -- inert constraints when interacting a work item with the inert set.

       , inert_irreds       :: Cts  -- Irreducible predicates
       , inert_frozen       :: Cts  -- All non-canonicals are kept here (as frozen errors) 
       }

tyVarsOfInert :: InertSet -> TcTyVarSet 
tyVarsOfInert (IS { inert_eqs    = _eqsubst
                  , inert_eq_tvs = inscope
                     -- inert_eq_tvs are always a superset of the tvs of inert_eqs 
                  , inert_dicts  = dictmap
                  , inert_ips    = ipmap
                  , inert_frozen = frozen
                  , inert_irreds = irreds
                  , inert_funeqs = funeqmap 
                  }) = tyVarsOfCts cts `unionVarSet` getInScopeVars inscope
  where
    cts = frozen `andCts` irreds `andCts`
          cCanMapToBag dictmap `andCts` cCanMapToBag ipmap `andCts` cCanMapToBag funeqmap

instance Outputable InertSet where
  ppr is = vcat [ vcat (map ppr (varEnvElts (inert_eqs is)))
                , vcat (map ppr (Bag.bagToList $ inert_irreds is)) 
                , vcat (map ppr (Bag.bagToList $ cCanMapToBag (inert_dicts is)))
                , vcat (map ppr (Bag.bagToList $ cCanMapToBag (inert_ips is))) 
                , vcat (map ppr (Bag.bagToList $ cCanMapToBag (inert_funeqs is)))
                , text "Frozen errors =" <+> -- Clearly print frozen errors
                    vcat (map ppr (Bag.bagToList $ inert_frozen is))
                , text "Warning: Not displaying cached (solved) non-canonicals."
                ]
                       
emptyInert :: InertSet
emptyInert = IS { inert_eqs     = emptyVarEnv
                , inert_eq_tvs  = emptyInScopeSet
                , inert_frozen  = emptyCts
                , inert_irreds  = emptyCts
                , inert_dicts   = emptyCCanMap
                , inert_ips     = emptyCCanMap
                , inert_funeqs  = emptyCCanMap }

type AtomicInert = Ct 

updInertSet :: InertSet -> AtomicInert -> InertSet 
-- Add a new inert element to the inert set. 
updInertSet is item 
  | isCTyEqCan item                     
  = let upd_err a b = pprPanic "updInertSet" $ 
                      vcat [text "Multiple inert equalities:", ppr a, ppr b]
        eqs'     = extendVarEnv_C upd_err (inert_eqs is)
                                          (cc_tyvar item)
                                          (item, mkEqVarLCo (cc_id item))
        inscope' = extendInScopeSetSet (inert_eq_tvs is) (tyVarsOfCt item)
    in is { inert_eqs = eqs', inert_eq_tvs = inscope' }

  | Just cls <- isCDictCan_Maybe item   -- Dictionary 
  = is { inert_dicts = updCCanMap (cls,item) (inert_dicts is) } 
  | Just x  <- isCIPCan_Maybe item      -- IP 
  = is { inert_ips   = updCCanMap (x,item) (inert_ips is) }  
  | isCIrredEvCan item                     -- Presently-irreducible evidence
  = is { inert_irreds = inert_irreds is `Bag.snocBag` item }

  | Just tc <- isCFunEqCan_Maybe item   -- Function equality 
  = is { inert_funeqs = updCCanMap (tc,item) (inert_funeqs is) }
  | otherwise 
  = is { inert_frozen = inert_frozen is `Bag.snocBag` item }

extractUnsolvedTcS :: TcS (InertSet,Cts,Cts) 
-- Extracts frozen errors and remaining unsolved and sets the 
-- inert set to be the remaining! 
extractUnsolvedTcS = 
  do { is <- getInertTcS 
     ; let (is',insol,unsol) <- extractUnsolved is
     ; updInertSetTcS_ (\_ -> is') 
     ; return (insol,unsol) }

extractUnsolved :: InertSet -> (InertSet, Cts, Cts)
-- Postcondition
-- -------------
-- When: 
--   (is_solved, frozen, cts) <- extractUnsolved inert
-- Then: 
-- -----------------------------------------------------------------------------
--  cts       |  The unsolved (Derived or Wanted only) residual 
--            |  canonical constraints, that is, no CNonCanonicals.
-- -----------|-----------------------------------------------------------------
--  frozen    | The CNonCanonicals of the original inert (frozen errors), 
--            | of all flavors
-- -----------|-----------------------------------------------------------------
--  is_solved | Whatever remains from the inert after removing the previous two. 
-- -----------------------------------------------------------------------------
extractUnsolved is@(IS {inert_eqs = eqs, inert_irreds = irreds}) 
  = let is_solved  = is { inert_eqs    = solved_eqs
                        , inert_eq_tvs = inert_eq_tvs is
                        , inert_dicts  = solved_dicts
                        , inert_ips    = solved_ips
                        , inert_irreds = solved_irreds
                        , inert_frozen = emptyCts
                        , inert_funeqs = solved_funeqs }
    in (is_solved, inert_frozen is, unsolved)

  where solved_eqs = filterVarEnv_Directly (\_ (ct,_) -> isGivenOrSolvedCt ct) eqs
        unsolved_eqs = foldVarEnv (\(ct,_co) cts -> cts `extendCts` ct) emptyCts $
                       eqs `minusVarEnv` solved_eqs

        (unsolved_irreds, solved_irreds) = Bag.partitionBag (not.isGivenOrSolvedCt) irreds
        (unsolved_ips, solved_ips)       = extractUnsolvedCMap (inert_ips is) 
        (unsolved_dicts, solved_dicts)   = extractUnsolvedCMap (inert_dicts is) 
        (unsolved_funeqs, solved_funeqs) = extractUnsolvedCMap (inert_funeqs is) 

        unsolved = unsolved_eqs `unionBags` unsolved_irreds `unionBags`
                   unsolved_ips `unionBags` unsolved_dicts `unionBags` unsolved_funeqs
\end{code}




%************************************************************************
%*									*
                    CtFlavor
         The "flavor" of a canonical constraint
%*									*
%************************************************************************

\begin{code}
getWantedLoc :: Ct -> WantedLoc
getWantedLoc ct 
  = ASSERT (isWanted (cc_flavor ct))
    case cc_flavor ct of 
      Wanted wl -> wl 
      _         -> pprPanic "Can't get WantedLoc of non-wanted constraint!" empty

isWantedCt :: Ct -> Bool
isWantedCt ct = isWanted (cc_flavor ct)
isDerivedCt :: Ct -> Bool
isDerivedCt ct = isDerived (cc_flavor ct)

isGivenCt_maybe :: Ct -> Maybe GivenKind
isGivenCt_maybe ct = isGiven_maybe (cc_flavor ct)

isGivenOrSolvedCt :: Ct -> Bool
isGivenOrSolvedCt ct = isGivenOrSolved (cc_flavor ct)


canSolve :: CtFlavor -> CtFlavor -> Bool 
-- canSolve ctid1 ctid2 
-- The constraint ctid1 can be used to solve ctid2 
-- "to solve" means a reaction where the active parts of the two constraints match.
--  active(F xis ~ xi) = F xis 
--  active(tv ~ xi)    = tv 
--  active(D xis)      = D xis 
--  active(IP nm ty)   = nm 
--
-- NB:  either (a `canSolve` b) or (b `canSolve` a) must hold
-----------------------------------------
canSolve (Given {})   _            = True 
canSolve (Wanted {})  (Derived {}) = True
canSolve (Wanted {})  (Wanted {})  = True
canSolve (Derived {}) (Derived {}) = True  -- Important: derived can't solve wanted/given
canSolve _ _ = False  	       	     	   -- (There is no *evidence* for a derived.)

canRewrite :: CtFlavor -> CtFlavor -> Bool 
-- canRewrite ctid1 ctid2 
-- The *equality_constraint* ctid1 can be used to rewrite inside ctid2 
canRewrite = canSolve 

combineCtLoc :: CtFlavor -> CtFlavor -> WantedLoc
-- Precondition: At least one of them should be wanted 
combineCtLoc (Wanted loc) _    = loc
combineCtLoc _ (Wanted loc)    = loc
combineCtLoc (Derived loc ) _  = loc
combineCtLoc _ (Derived loc )  = loc
combineCtLoc _ _ = panic "combineCtLoc: both given"

mkSolvedFlavor :: CtFlavor -> SkolemInfo -> CtFlavor
-- To be called when we actually solve a wanted/derived (perhaps leaving residual goals)
mkSolvedFlavor (Wanted  loc) sk  = Given (setCtLocOrigin loc sk) GivenSolved
mkSolvedFlavor (Derived loc) sk  = Given (setCtLocOrigin loc sk) GivenSolved
mkSolvedFlavor fl@(Given {}) _sk = pprPanic "Solving a given constraint!" $ ppr fl

mkGivenFlavor :: CtFlavor -> SkolemInfo -> CtFlavor
mkGivenFlavor (Wanted  loc) sk  = Given (setCtLocOrigin loc sk) GivenOrig
mkGivenFlavor (Derived loc) sk  = Given (setCtLocOrigin loc sk) GivenOrig
mkGivenFlavor fl@(Given {}) _sk = pprPanic "Solving a given constraint!" $ ppr fl

mkWantedFlavor :: CtFlavor -> CtFlavor
mkWantedFlavor (Wanted  loc) = Wanted loc
mkWantedFlavor (Derived loc) = Wanted loc
mkWantedFlavor fl@(Given {}) = pprPanic "mkWantedFlavor" (ppr fl)
\end{code}

%************************************************************************
%*									*
%*		The TcS solver monad                                    *
%*									*
%************************************************************************

Note [The TcS monad]
~~~~~~~~~~~~~~~~~~~~
The TcS monad is a weak form of the main Tc monad

All you can do is
    * fail
    * allocate new variables
    * fill in evidence variables

Filling in a dictionary evidence variable means to create a binding
for it, so TcS carries a mutable location where the binding can be
added.  This is initialised from the innermost implication constraint.

\begin{code}
data TcSEnv
  = TcSEnv { 
      tcs_ev_binds :: EvBindsVar,
          -- Evidence bindings

      tcs_ty_binds :: IORef (TyVarEnv (TcTyVar, TcType)),
          -- Global type bindings

      tcs_context :: SimplContext,
                     
      tcs_untch :: TcsUntouchables,

      tcs_ic_depth   :: Int,       -- Implication nesting depth
      tcs_count      :: IORef Int, -- Global step count

      tcs_inerts   :: IORef InertSet, -- Current inert set
      tcs_worklist :: IORef WorkList  -- Current worklist
    }

type TcsUntouchables = (Untouchables,TcTyVarSet)
-- Like the TcM Untouchables, 
-- but records extra TcsTv variables generated during simplification
-- See Note [Extra TcsTv untouchables] in TcSimplify
\end{code}

\begin{code}
data SimplContext
  = SimplInfer SDoc	   -- Inferring type of a let-bound thing
  | SimplRuleLhs RuleName  -- Inferring type of a RULE lhs
  | SimplInteractive	   -- Inferring type at GHCi prompt
  | SimplCheck SDoc	   -- Checking a type signature or RULE rhs

instance Outputable SimplContext where
  ppr (SimplInfer d)   = ptext (sLit "SimplInfer") <+> d
  ppr (SimplCheck d)   = ptext (sLit "SimplCheck") <+> d
  ppr (SimplRuleLhs n) = ptext (sLit "SimplRuleLhs") <+> doubleQuotes (ftext n)
  ppr SimplInteractive = ptext (sLit "SimplInteractive")

isInteractive :: SimplContext -> Bool
isInteractive SimplInteractive = True
isInteractive _                = False

simplEqsOnly :: SimplContext -> Bool
-- Simplify equalities only, not dictionaries
-- This is used for the LHS of rules; ee
-- Note [Simplifying RULE lhs constraints] in TcSimplify
simplEqsOnly (SimplRuleLhs {}) = True
simplEqsOnly _                 = False

performDefaulting :: SimplContext -> Bool
performDefaulting (SimplInfer {})   = False
performDefaulting (SimplRuleLhs {}) = False
performDefaulting SimplInteractive  = True
performDefaulting (SimplCheck {})   = True

---------------
newtype TcS a = TcS { unTcS :: TcSEnv -> TcM a } 

instance Functor TcS where
  fmap f m = TcS $ fmap f . unTcS m

instance Monad TcS where 
  return x  = TcS (\_ -> return x) 
  fail err  = TcS (\_ -> fail err) 
  m >>= k   = TcS (\ebs -> unTcS m ebs >>= \r -> unTcS (k r) ebs)

-- Basic functionality 
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
wrapTcS :: TcM a -> TcS a 
-- Do not export wrapTcS, because it promotes an arbitrary TcM to TcS,
-- and TcS is supposed to have limited functionality
wrapTcS = TcS . const -- a TcM action will not use the TcEvBinds

wrapErrTcS :: TcM a -> TcS a 
-- The thing wrapped should just fail
-- There's no static check; it's up to the user
-- Having a variant for each error message is too painful
wrapErrTcS = wrapTcS

wrapWarnTcS :: TcM a -> TcS a 
-- The thing wrapped should just add a warning, or no-op
-- There's no static check; it's up to the user
wrapWarnTcS = wrapTcS

failTcS, panicTcS :: SDoc -> TcS a
failTcS      = wrapTcS . TcM.failWith
panicTcS doc = pprPanic "TcCanonical" doc

traceTcS :: String -> SDoc -> TcS ()
traceTcS herald doc = TcS $ \_env -> TcM.traceTc herald doc

bumpStepCountTcS :: TcS ()
bumpStepCountTcS = TcS $ \env -> do { let ref = tcs_count env
                                    ; n <- TcM.readTcRef ref
                                    ; TcM.writeTcRef ref (n+1) }

traceFireTcS :: SubGoalDepth -> SDoc -> TcS ()
-- Dump a rule-firing trace
traceFireTcS depth doc 
  = TcS $ \env -> 
    TcM.ifDOptM Opt_D_dump_cs_trace $ 
    do { n <- TcM.readTcRef (tcs_count env)
       ; let msg = int n 
                <> text (replicate (tcs_ic_depth env) '>')
                <> brackets (int depth) <+> doc
       ; TcM.dumpTcRn msg }

doWithInert :: InertSet -> TcS a -> TcS a 
-- Just use this inert set to do stuff but pop back to the original inert in the end
doWithInert inert action
  = do { is_orig <- getInertTcS 
       ; updInertSetTcS_ (\_ -> inert) 
       ; res <- action
       ; updInertSetTcS_ (\_ -> is_orig) 
       ; return res } 


runTcS :: SimplContext
       -> Untouchables 	       -- Untouchables
       -> InertSet             -- Initial inert set
       -> WorkList             -- Initial work list
       -> TcS a		       -- What to run
       -> TcM (a, Bag EvBind)
runTcS context untouch is wl tcs 
  = do { ty_binds_var <- TcM.newTcRef emptyVarEnv
       ; ev_binds_var@(EvBindsVar evb_ref _) <- TcM.newTcEvBinds
       ; step_count <- TcM.newTcRef 0

       ; inert_var <- TcM.newTcRef is 
       ; wl_var <- TcM.newTcRef wl

       ; let env = TcSEnv { tcs_ev_binds = ev_binds_var
                          , tcs_ty_binds = ty_binds_var
                          , tcs_context  = context
                          , tcs_untch    = (untouch, emptyVarSet) -- No Tcs untouchables yet
			  , tcs_count    = step_count
			  , tcs_ic_depth = 0
                          , tcs_inerts   = inert_var
                          , tcs_worklist = wl_var }

	     -- Run the computation
       ; res <- unTcS tcs env
	     -- Perform the type unifications required
       ; ty_binds <- TcM.readTcRef ty_binds_var
       ; mapM_ do_unification (varEnvElts ty_binds)

#ifdef DEBUG
       ; count <- TcM.readTcRef step_count
       ; when (opt_PprStyle_Debug && count > 0) $
         TcM.debugDumpTcRn (ptext (sLit "Constraint solver steps =") 
                            <+> int count <+> ppr context)
#endif
             -- And return
       ; ev_binds      <- TcM.readTcRef evb_ref
       ; return (res, evBindMapBinds ev_binds) }
  where
    do_unification (tv,ty) = TcM.writeMetaTyVar tv ty

{- DV: The rest of the interface to the monad I will have to determine precisely
   when I refactor TcSimplify. Leaving commented out for now! 

nestImplicTcS :: EvBindsVar -> TcsUntouchables -> TcS a -> TcS a
nestImplicTcS ref (inner_range, inner_tcs) (TcS thing_inside)
  = TcS $ \ TcSEnv { tcs_ty_binds = ty_binds 
    	    	   , tcs_untch = (_outer_range, outer_tcs)
		   , tcs_count = count
		   , tcs_ic_depth = idepth
                   , tcs_context = ctxt 
                   , tcs_flat_map = orig_flat_cache_var
                   } ->
    do { let inner_untch = (inner_range, outer_tcs `unionVarSet` inner_tcs)
       		   -- The inner_range should be narrower than the outer one
		   -- (thus increasing the set of untouchables) but 
		   -- the inner Tcs-untouchables must be unioned with the
		   -- outer ones!

       ; orig_flat_cache <- TcM.readTcRef orig_flat_cache_var
       ; flat_cache_var  <- TcM.newTcRef orig_flat_cache
       -- One could be more conservative as well: 
       -- ; flat_cache_var  <- TcM.newTcRef emptyFlatCache 

                            -- Consider copying the results the tcs_flat_map of the 
                            -- incomping constraint, but we must make sure that we
                            -- have pushed everything in, which seems somewhat fragile
       ; let nest_env = TcSEnv { tcs_ev_binds = ref
                               , tcs_ty_binds = ty_binds
                               , tcs_untch    = inner_untch
                               , tcs_count    = count
                               , tcs_ic_depth = idepth+1
                               , tcs_context  = ctxtUnderImplic ctxt 
                               , tcs_flat_map = flat_cache_var }
       ; thing_inside nest_env }

recoverTcS :: TcS a -> TcS a -> TcS a
recoverTcS (TcS recovery_code) (TcS thing_inside)
  = TcS $ \ env ->
    TcM.recoverM (recovery_code env) (thing_inside env)

ctxtUnderImplic :: SimplContext -> SimplContext
-- See Note [Simplifying RULE lhs constraints] in TcSimplify
ctxtUnderImplic (SimplRuleLhs n) = SimplCheck (ptext (sLit "lhs of rule") 
                                               <+> doubleQuotes (ftext n))
ctxtUnderImplic ctxt              = ctxt

tryTcS :: TcS a -> TcS a
-- Like runTcS, but from within the TcS monad
-- Ignore all the evidence generated, and do not affect caller's evidence!
tryTcS tcs
  = TcS (\env -> do { ty_binds_var <- TcM.newTcRef emptyVarEnv
                    ; ev_binds_var <- TcM.newTcEvBinds
                    ; flat_cache_var <- TcM.newTcRef emptyFlatCache
                    ; let env1 = env { tcs_ev_binds = ev_binds_var
                                     , tcs_ty_binds = ty_binds_var
                                     , tcs_flat_map = flat_cache_var }
                   ; unTcS tcs env1 })
-}

-- Getters and setters of TcEnv fields
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- Getter of inerts and worklist
getTcSInertsRef :: TcS (IORef InertSet)
getTcSInertsRef = TcS (return . tcs_inerts)

getTcSWorkListRef :: TcS (IORef WorkList) 
getTcSWorkListRef = TcS (return . tcs_worklist) 

getTcSInerts :: TcS InertSet 
getTcSInerts = getTcSInertsRef >>= wrapTcS . (TcM.readTcRef) 

getTcSWorkList :: TcS WorkList
getTcSWorkList = getTcSWorkListRef >>= wrapTcS . (TcM.readTcRef) 

updWorkListTcS :: (WorkList -> WorkList) -> TcS () 
updWorkListTcS f 
  = do { wl_var <- getTcSWorkListRef 
       ; wl_curr <- wrapTcS (TcM.readTcRef wl_var)
       ; wrapTcS (TcM.writeTcRef wl_var (f wl_curr)) }

updInertSetTcS :: (InertSet -> (InertSet,a)) -> TcS a 
updInertSetTcS f 
  = do { is_var <- getTcSInertsRef
       ; is_curr <- wrapTcS (TcM.readTcRef is_var)
       ; let (is_new,ret) = f is_curr
       ; wrapTcS (TcM.writeTcRef is_var is_new) 
       ; return ret } 

updInertSetTcS_ :: (InertSet -> InertSet) -> TcS () 
updInertSetTcS_ f = updInertSetTcS (\x -> (f x,())) 

emitFrozenError :: CtFlavor -> EvVar -> SubGoalDepth -> TcS ()
-- Emits a non-canonical constraint that will stand for a frozen error in the inerts. 
emitFrozenError fl ev depth 
  = do { inert_ref <- getTcSInertsRef 
       ; inerts <- wrapTcS (TcM.readTcRef inert_ref)
       ; let ct = CNonCanonical { cc_id = ev
                                , cc_flavor = fl
                                , cc_depth = depth } 
             inerts_new = inerts { inert_frozen = extendCts (inert_frozen inerts) ct } 
       ; wrapTcS (TcM.writeTcRef inert_ref inerts_new) }

getDynFlags :: TcS DynFlags
getDynFlags = wrapTcS TcM.getDOpts

getTcSContext :: TcS SimplContext
getTcSContext = TcS (return . tcs_context)

getTcEvBinds :: TcS EvBindsVar
getTcEvBinds = TcS (return . tcs_ev_binds) 

getUntouchables :: TcS TcsUntouchables
getUntouchables = TcS (return . tcs_untch)

getTcSTyBinds :: TcS (IORef (TyVarEnv (TcTyVar, TcType)))
getTcSTyBinds = TcS (return . tcs_ty_binds)

getTcSTyBindsMap :: TcS (TyVarEnv (TcTyVar, TcType))
getTcSTyBindsMap = getTcSTyBinds >>= wrapTcS . (TcM.readTcRef) 


getTcEvBindsBag :: TcS EvBindMap
getTcEvBindsBag
  = do { EvBindsVar ev_ref _ <- getTcEvBinds 
       ; wrapTcS $ TcM.readTcRef ev_ref }

setEqBind :: EqVar -> LCoercion -> TcS () 
setEqBind eqv co = setEvBind eqv (EvCoercionBox co)

setWantedTyBind :: TcTyVar -> TcType -> TcS () 
-- Add a type binding
-- We never do this twice!
setWantedTyBind tv ty 
  = do { ref <- getTcSTyBinds
       ; wrapTcS $ 
         do { ty_binds <- TcM.readTcRef ref
#ifdef DEBUG
            ; TcM.checkErr (not (tv `elemVarEnv` ty_binds)) $
              vcat [ text "TERRIBLE ERROR: double set of meta type variable"
                   , ppr tv <+> text ":=" <+> ppr ty
                   , text "Old value =" <+> ppr (lookupVarEnv_NF ty_binds tv)]
#endif
            ; TcM.writeTcRef ref (extendVarEnv ty_binds tv (tv,ty)) } }

setIPBind :: EvVar -> EvTerm -> TcS () 
setIPBind = setEvBind 

setDictBind :: EvVar -> EvTerm -> TcS () 
setDictBind = setEvBind 

setEvBind :: EvVar -> EvTerm -> TcS () 
-- Internal
setEvBind ev t
  = do { tc_evbinds <- getTcEvBinds
       ; wrapTcS $ TcM.addTcEvBind tc_evbinds ev t }

warnTcS :: CtLoc orig -> Bool -> SDoc -> TcS ()
warnTcS loc warn_if doc 
  | warn_if   = wrapTcS $ TcM.setCtLoc loc $ TcM.addWarnTc doc
  | otherwise = return ()

getDefaultInfo ::  TcS (SimplContext, [Type], (Bool, Bool))
getDefaultInfo 
  = do { ctxt <- getTcSContext
       ; (tys, flags) <- wrapTcS (TcM.tcGetDefaultTys (isInteractive ctxt))
       ; return (ctxt, tys, flags) }

-- Just get some environments needed for instance looking up and matching
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

getInstEnvs :: TcS (InstEnv, InstEnv) 
getInstEnvs = wrapTcS $ Inst.tcGetInstEnvs 

getFamInstEnvs :: TcS (FamInstEnv, FamInstEnv) 
getFamInstEnvs = wrapTcS $ FamInst.tcGetFamInstEnvs

getTopEnv :: TcS HscEnv 
getTopEnv = wrapTcS $ TcM.getTopEnv 

getGblEnv :: TcS TcGblEnv 
getGblEnv = wrapTcS $ TcM.getGblEnv 

-- Various smaller utilities [TODO, maybe will be absorbed in the instance matcher]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

checkWellStagedDFun :: PredType -> DFunId -> WantedLoc -> TcS () 
checkWellStagedDFun pred dfun_id loc 
  = wrapTcS $ TcM.setCtLoc loc $ 
    do { use_stage <- TcM.getStage
       ; TcM.checkWellStaged pp_thing bind_lvl (thLevel use_stage) }
  where
    pp_thing = ptext (sLit "instance for") <+> quotes (ppr pred)
    bind_lvl = TcM.topIdLvl dfun_id

pprEq :: TcType -> TcType -> SDoc
pprEq ty1 ty2 = pprType $ mkEqPred (ty1,ty2)

isTouchableMetaTyVar :: TcTyVar -> TcS Bool
isTouchableMetaTyVar tv 
  = do { untch <- getUntouchables
       ; return $ isTouchableMetaTyVar_InRange untch tv } 

isTouchableMetaTyVar_InRange :: TcsUntouchables -> TcTyVar -> Bool 
isTouchableMetaTyVar_InRange (untch,untch_tcs) tv 
  = case tcTyVarDetails tv of 
      MetaTv TcsTv _ -> not (tv `elemVarSet` untch_tcs)
                        -- See Note [Touchable meta type variables] 
      MetaTv {}      -> inTouchableRange untch tv 
      _              -> False 


\end{code}


Note [Touchable meta type variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Meta type variables allocated *by the constraint solver itself* are always
touchable.  Example: 
   instance C a b => D [a] where...
if we use this instance declaration we "make up" a fresh meta type
variable for 'b', which we must later guess.  (Perhaps C has a
functional dependency.)  But since we aren't in the constraint *generator*
we can't allocate a Unique in the touchable range for this implication
constraint.  Instead, we mark it as a "TcsTv", which makes it always-touchable.


\begin{code}
-- Flatten skolems
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

newFlattenSkolemTy :: TcType -> TcS TcType
newFlattenSkolemTy ty = mkTyVarTy <$> newFlattenSkolemTyVar ty

newFlattenSkolemTyVar :: TcType -> TcS TcTyVar
newFlattenSkolemTyVar ty
  = do { tv <- wrapTcS $ do { uniq <- TcM.newUnique
                            ; let name = TcM.mkTcTyVarName uniq (fsLit "f")
                            ; return $ mkTcTyVar name (typeKind ty) (FlatSkol ty) } 
       ; traceTcS "New Flatten Skolem Born" $ 
           (ppr tv <+> text "[:= " <+> ppr ty <+> text "]")
       ; return tv }

-- Instantiations 
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

instDFunTypes :: [Either TyVar TcType] -> TcS [TcType] 
instDFunTypes mb_inst_tys 
  = mapM inst_tv mb_inst_tys
  where
    inst_tv :: Either TyVar TcType -> TcS Type
    inst_tv (Left tv)  = mkTyVarTy <$> instFlexiTcS tv
    inst_tv (Right ty) = return ty 

instDFunConstraints :: TcThetaType -> TcS [EvVar] 
instDFunConstraints preds = wrapTcS $ TcM.newWantedEvVars preds 


instFlexiTcS :: TyVar -> TcS TcTyVar 
-- Like TcM.instMetaTyVar but the variable that is created is always
-- touchable; we are supposed to guess its instantiation. 
-- See Note [Touchable meta type variables] 
instFlexiTcS tv = instFlexiTcSHelper (tyVarName tv) (tyVarKind tv) 

newFlexiTcSTy :: Kind -> TcS TcType  
newFlexiTcSTy knd 
  = wrapTcS $
    do { uniq <- TcM.newUnique 
       ; ref  <- TcM.newMutVar  Flexi 
       ; let name = TcM.mkTcTyVarName uniq (fsLit "uf")
       ; return $ mkTyVarTy (mkTcTyVar name knd (MetaTv TcsTv ref)) }

isFlexiTcsTv :: TyVar -> Bool
isFlexiTcsTv tv
  | not (isTcTyVar tv)                  = False
  | MetaTv TcsTv _ <- tcTyVarDetails tv = True
  | otherwise                           = False

newKindConstraint :: TcTyVar -> Kind -> TcS CoVar
-- Create new wanted CoVar that constrains the type to have the specified kind. 
newKindConstraint tv knd 
  = do { tv_k <- instFlexiTcSHelper (tyVarName tv) knd 
       ; let ty_k = mkTyVarTy tv_k
       ; eqv <- newEqVar (mkTyVarTy tv) ty_k
       ; return eqv }

instFlexiTcSHelper :: Name -> Kind -> TcS TcTyVar
instFlexiTcSHelper tvname tvkind
  = wrapTcS $ 
    do { uniq <- TcM.newUnique 
       ; ref  <- TcM.newMutVar  Flexi 
       ; let name = setNameUnique tvname uniq 
             kind = tvkind 
       ; return (mkTcTyVar name kind (MetaTv TcsTv ref)) }

-- Superclasses and recursive dictionaries 
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

newEvVar :: TcPredType -> TcS EvVar
newEvVar pty = wrapTcS $ TcM.newEvVar pty

newDerivedId :: TcPredType -> TcS EvVar 
newDerivedId pty = wrapTcS $ TcM.newEvVar pty

newGivenEqVar :: TcType -> TcType -> Coercion -> TcS EvVar 
-- Note we create immutable variables for given or derived, since we
-- must bind them to TcEvBinds (because their evidence may involve 
-- superclasses). However we should be able to override existing
-- 'derived' evidence, even in TcEvBinds 
newGivenEqVar ty1 ty2 co 
  = do { cv <- newEqVar ty1 ty2
       ; setEvBind cv (EvCoercionBox co) 
       ; return cv } 

newEqVar :: TcType -> TcType -> TcS EvVar
newEqVar ty1 ty2 = wrapTcS $ TcM.newEq ty1 ty2 

newIPVar :: IPName Name -> TcType -> TcS EvVar 
newIPVar nm ty = wrapTcS $ TcM.newIP nm ty 

newDictVar :: Class -> [TcType] -> TcS EvVar 
newDictVar cl tys = wrapTcS $ TcM.newDict cl tys 
\end{code} 


\begin{code} 
-- Matching and looking up classes and family instances
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

data MatchInstResult mi
  = MatchInstNo         -- No matching instance 
  | MatchInstSingle mi  -- Single matching instance
  | MatchInstMany       -- Multiple matching instances


matchClass :: Class -> [Type] -> TcS (MatchInstResult (DFunId, [Either TyVar TcType])) 
-- Look up a class constraint in the instance environment
matchClass clas tys
  = do	{ let pred = mkClassPred clas tys 
        ; instEnvs <- getInstEnvs
        ; case lookupInstEnv instEnvs clas tys of {
            ([], unifs, _)               -- Nothing matches  
                -> do { traceTcS "matchClass not matching"
                                 (vcat [ text "dict" <+> ppr pred, 
                                         text "unifs" <+> ppr unifs ]) 
                      ; return MatchInstNo  
                      } ;  
	    ([(ispec, inst_tys)], [], _) -- A single match 
		-> do	{ let dfun_id = is_dfun ispec
			; traceTcS "matchClass success"
				   (vcat [text "dict" <+> ppr pred, 
				          text "witness" <+> ppr dfun_id
                                           <+> ppr (idType dfun_id) ])
				  -- Record that this dfun is needed
                        ; return $ MatchInstSingle (dfun_id, inst_tys)
                        } ;
     	    (matches, unifs, _)          -- More than one matches 
		-> do	{ traceTcS "matchClass multiple matches, deferring choice"
			           (vcat [text "dict" <+> ppr pred,
				   	  text "matches" <+> ppr matches,
				   	  text "unifs" <+> ppr unifs])
                        ; return MatchInstMany 
		        }
	}
        }

matchFam :: TyCon -> [Type] -> TcS (Maybe (TyCon, [Type]))
matchFam tycon args = wrapTcS $ TcM.tcLookupFamInst tycon args
\end{code}


-- Rewriting with respect to the inert equalities 
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\begin{code}

getInertEqs :: TcS (TyVarEnv (Ct,Coercion), InScopeSet)
getInertEqs = do { inert <- getTcSInerts
                 ; return (inert_eqs inert, inert_eq_tvs inert) }

getRelevantInertFunEq :: TyCon -> [Xi] -> CtFlavor -> TcS (Maybe (Xi,Coercion)) 
-- Returns a coercion between (tc xi_args ~  xi) if such an inert item exists
getRelevantInertFunEq tc xi_args fl 
  = do { inert <- getTcSInerts
       ; let (fun_eq_relevants,_) = getRelevantCts tc (inert_funeqs inert)
       ; let acceptables = filterBag fun_match fun_eq_relevants
       ; case bagToList acceptables of 
           []     -> return Nothing
           (cc:_) -> return $ Just (cc_rhs cc, mkEqVarLCo (cc_id cc)) }
  where fun_match (CFunEqCan { cc_flavor = ifl, cc_tyargs = ixis }) 
            = eqTypes xi_args ixis && ifl `canRewrite` fl
        fun_match _ = False -- Should be an assertion failure, really


rewriteFromInertEqs :: (TyVarEnv (Ct,Coercion), InScopeSet)  
                    -- Precondition: Ct are CTyEqCans only!
                    -> CtFlavor 
                    -> EvVar 
                    -> TcS EvVar
rewriteFromInertEqs (subst,inscope) fl v 
  = do { let co = liftInertEqsPred subst inscope fl (evVarPred v) 
       ; if isReflCo co then return v 
         else do { v' <- newEvVar (pSnd (coercionKind co)) 
                 ; case fl of 
                     Wanted {}  -> setEvBind v (EvCast v' (mkSymCo co)) 
                     Given {}   -> setEvBind v' (EvCast v co) 
                     Derived {} -> return ()
                 ; return v' } }

-- See Note [LiftInertEqs] 
liftInertEqsPred :: TyVarEnv (Ct,Coercion) 
                 -> InScopeSet 
                 -> CtFlavor 
                 -> PredType -> Coercion 
liftInertEqsPred subst inscope fl pty
  = ty_cts_subst subst inscope fl pty

ty_cts_subst :: TyVarEnv (Ct,Coercion)
             -> InScopeSet -> CtFlavor -> Type -> Coercion 
ty_cts_subst subst inscope fl ty 
  = go ty 
  where go (TyVarTy tv)      = tyvar_cts_subst tv `orElse` Refl (TyVarTy tv)
        go (AppTy ty1 ty2)   = mkAppCo (go ty1) (go ty2) 
        go (TyConApp tc tys) = mkTyConAppCo tc (map go tys) 
        go (ForAllTy v ty)   = mkForAllCo v' $! (ty_cts_subst subst' inscope' fl ty)
                               where (subst',inscope',v') = upd_tyvar_bndr subst inscope v
        go (FunTy ty1 ty2)   = mkFunCo (go ty1) (go ty2) 

        tyvar_cts_subst tv  
          | Just (ct,co) <- lookupVarEnv subst tv, cc_flavor ct `canRewrite` fl  
          = Just co -- Warn: use cached, not cc_id directly, because of alpha-renamings!
          | otherwise = Nothing 

        upd_tyvar_bndr subst inscope v 
          = (new_subst, (inscope `extendInScopeSet` new_v), new_v)
          where new_subst 
                    | no_change = delVarEnv subst v
                        -- Otherwise we have to extend the environment with /something/. 
                        -- But we do not want to monadically create a new EvVar. So, we
                        -- create an 'unused_ct' but we cache reflexivity as the 
                        -- associated coercion. 
                    | otherwise = extendVarEnv subst v (unused_ct, Refl (TyVarTy new_v))

                no_change = new_v == v 
                new_v     = uniqAway inscope v 

                unused_ct = CTyEqCan { cc_id     = unused_evvar
                                     , cc_flavor = fl -- canRewrite is reflexive.
                                     , cc_tyvar  = v 
                                     , cc_rhs    = mkTyVarTy new_v 
                                     , cc_depth  = unused_depth }
                unused_depth = panic "ty_cts_subst: This depth should not be accessed!"
                unused_evvar = panic "ty_cts_subst: This var is just an alpha-renaming!"
\end{code}

Note [LiftInertEqsPred]
~~~~~~~~~~~~~~~~~~~~~~~ 
The function liftInertEqPred behaves almost like liftCoSubst (in
Coercion), but accepts a map TyVarEnv (Ct,Coercion) instead of a
LiftCoSubst. This data structure is more convenient to use since we
must apply the inert substitution /only/ if the inert equality 
`canRewrite` the work item. There's admittedly some duplication of 
functionality but it would be more tedious to cache and maintain 
different flavors of LiftCoSubst structures in the inerts. 

