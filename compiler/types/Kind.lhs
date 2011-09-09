%
% (c) The University of Glasgow 2006
%

\begin{code}
module Kind (
        -- * Main data type
        Kind, typeKind,

	-- Kinds
	liftedTypeKind, unliftedTypeKind, openTypeKind,
        argTypeKind, ubxTupleKind,
        mkArrowKind, mkArrowKinds,

        -- Kind constructors...
        liftedTypeKindTyCon, openTypeKindTyCon, unliftedTypeKindTyCon,
        argTypeKindTyCon, ubxTupleKindTyCon,

        -- Super Kinds
	tySuperKind, tySuperKindTyCon, 
        
	pprKind, pprParendKind,

        -- ** Deconstructing Kinds
        kindFunResult, kindAppResult, synTyConResKind,
        splitKindFunTys, splitKindFunTysN, splitKindFunTy_maybe,

        -- ** Predicates on Kinds
        isLiftedTypeKind, isUnliftedTypeKind, isOpenTypeKind,
        isUbxTupleKind, isArgTypeKind, isKind, isTySuperKind, 
        isSuperKind, isCoercionKind, 
        isLiftedTypeKindCon, noHashInKind,

        isSubArgTypeKind, isSubOpenTypeKind, isSubKind, defaultKind,
        isSubKindCon, isSubOpenTypeKindCon,

        -- ** Promotion related functions
        promoteType, isPromotableType, isPromotableKind

       ) where

#include "HsVersions.h"

import TypeRep
import TysPrim
import TyCon
import Type ( substKiWith, eqKind )
import Var
import VarSet
import PrelNames
import Outputable
\end{code}

%************************************************************************
%*									*
        Predicates over Kinds
%*									*
%************************************************************************

\begin{code}
isTySuperKind :: SuperKind -> Bool
isTySuperKind (TyConApp kc []) = kc `hasKey` tySuperKindTyConKey
isTySuperKind _                = False

-------------------
-- Lastly we need a few functions on Kinds

isLiftedTypeKindCon :: TyCon -> Bool
isLiftedTypeKindCon tc    = tc `hasKey` liftedTypeKindTyConKey

-- This checks that its argument does not contain # or (#).
-- It is used in tcTyVarBndrs.
noHashInKind :: Kind -> Bool
noHashInKind (TyVarTy {}) = True
noHashInKind (FunTy k1 k2) = noHashInKind k1 && noHashInKind k2
noHashInKind (ForAllTy _ ki) = noHashInKind ki
noHashInKind (TyConApp kc kis)
  =  not (kc `hasKey` unliftedTypeKindTyConKey)
  && not (kc `hasKey` ubxTupleKindTyConKey)
  && all noHashInKind kis
noHashInKind _ = panic "noHashInKind"
\end{code}

%************************************************************************
%*									*
        The kind of a type
%*									*
%************************************************************************

\begin{code}
typeKind :: Type -> Kind
typeKind _ty@(TyConApp tc tys) 
  = ASSERT2( not (tc `hasKey` eqPredPrimTyConKey) || length tys == 2, ppr _ty )
    	     -- Assertion checks for unsaturated application of (~)
	     -- See Note [The (~) TyCon] in TysPrim
    kindAppResult (tyConKind tc) tys

typeKind (PredTy pred)	      = predKind pred
typeKind (AppTy fun arg)      = kindAppResult (typeKind fun) [arg]
typeKind (ForAllTy _ ty)      = typeKind ty
typeKind (TyVarTy tyvar)      = tyVarKind tyvar
typeKind (FunTy _arg res)
    -- Hack alert.  The kind of (Int -> Int#) is liftedTypeKind (*), 
    --              not unliftedTypKind (#)
    -- The only things that can be after a function arrow are
    --   (a) types (of kind openTypeKind or its sub-kinds)
    --   (b) kinds (of super-kind TY) (e.g. * -> (* -> *))
    | isTySuperKind k         = k
    | otherwise               = ASSERT( isSubOpenTypeKind k) liftedTypeKind 
    where
      k = typeKind res

------------------
predKind :: PredType -> Kind
predKind (EqPred {}) = unliftedTypeKind	-- Coercions are unlifted
predKind (ClassP {}) = liftedTypeKind	-- Class and implicitPredicates are
predKind (IParam {}) = liftedTypeKind 	-- always represented by lifted types
\end{code}

%************************************************************************
%*									*
	Functions over Kinds		
%*									*
%************************************************************************

\begin{code}
-- | Essentially 'funResultTy' on kinds handling pi-types too
kindFunResult :: Kind -> Type -> Kind
kindFunResult (FunTy _ res) _ = res
kindFunResult (ForAllTy kv res) arg = substKiWith [kv] [arg] res
kindFunResult k _ = pprPanic "kindFunResult" (ppr k)

kindAppResult :: Kind -> [Type] -> Kind
kindAppResult k []     = k
kindAppResult k (a:as) = kindAppResult (kindFunResult k a) as

-- | Essentially 'splitFunTys' on kinds
splitKindFunTys :: Kind -> ([Kind],Kind)
splitKindFunTys (FunTy a r) = case splitKindFunTys r of
                              (as, k) -> (a:as, k)
splitKindFunTys k = ([], k)

splitKindFunTy_maybe :: Kind -> Maybe (Kind,Kind)
splitKindFunTy_maybe (FunTy a r) = Just (a,r)
splitKindFunTy_maybe _           = Nothing

-- | Essentially 'splitFunTysN' on kinds
splitKindFunTysN :: Int -> Kind -> ([Kind],Kind)
splitKindFunTysN 0 k           = ([], k)
splitKindFunTysN n (FunTy a r) = case splitKindFunTysN (n-1) r of
                                   (as, k) -> (a:as, k)
splitKindFunTysN n k = pprPanic "splitKindFunTysN" (ppr n <+> ppr k)

-- | Find the result 'Kind' of a type synonym, 
-- after applying it to its 'arity' number of type variables
-- Actually this function works fine on data types too, 
-- but they'd always return '*', so we never need to ask
synTyConResKind :: TyCon -> Kind
synTyConResKind tycon = kindAppResult (tyConKind tycon) (map mkTyVarTy (tyConTyVars tycon))

-- | See "Type#kind_subtyping" for details of the distinction between these 'Kind's
isUbxTupleKind, isOpenTypeKind, isArgTypeKind, isUnliftedTypeKind :: Kind -> Bool
isOpenTypeKindCon, isUbxTupleKindCon, isArgTypeKindCon,
        isUnliftedTypeKindCon, isSubArgTypeKindCon, isSubOpenTypeKindCon :: TyCon -> Bool

isOpenTypeKindCon tc    = tyConUnique tc == openTypeKindTyConKey

isOpenTypeKind (TyConApp tc _) = isOpenTypeKindCon tc
isOpenTypeKind _               = False

isUbxTupleKindCon tc = tyConUnique tc == ubxTupleKindTyConKey

isUbxTupleKind (TyConApp tc _) = isUbxTupleKindCon tc
isUbxTupleKind _               = False

isArgTypeKindCon tc = tyConUnique tc == argTypeKindTyConKey

isArgTypeKind (TyConApp tc _) = isArgTypeKindCon tc
isArgTypeKind _               = False

isUnliftedTypeKindCon tc = tyConUnique tc == unliftedTypeKindTyConKey

isUnliftedTypeKind (TyConApp tc _) = isUnliftedTypeKindCon tc
isUnliftedTypeKind _               = False

isSubOpenTypeKind :: Kind -> Bool
-- ^ True of any sub-kind of OpenTypeKind
isSubOpenTypeKind (TyConApp kc []) = isSubOpenTypeKindCon kc
isSubOpenTypeKind _                = False

isSubOpenTypeKindCon kc
  | isSubArgTypeKindCon kc   = True
  | isUbxTupleKindCon kc     = True
  | isOpenTypeKindCon kc     = True
  | otherwise                = False

isSubArgTypeKindCon kc
  | isUnliftedTypeKindCon kc = True
  | isLiftedTypeKindCon kc   = True
  | isArgTypeKindCon kc      = True
  | otherwise                = False

isSubArgTypeKind :: Kind -> Bool
-- ^ True of any sub-kind of ArgTypeKind 
isSubArgTypeKind (TyConApp kc []) = isSubArgTypeKindCon kc
isSubArgTypeKind _                = False

-- | Is this a super-kind (i.e. a type-of-kinds)?
isSuperKind :: Type -> Bool
isSuperKind (TyConApp (skc) []) = isSuperKindTyCon skc
isSuperKind _                   = False

-- | Is this a kind (i.e. a type-of-types)?
isKind :: Kind -> Bool
isKind k = isSuperKind (typeKind k)

isSubKind :: Kind -> Kind -> Bool
-- ^ @k1 \`isSubKind\` k2@ checks that @k1@ <: @k2@
isSubKind (TyConApp kc1 []) (TyConApp kc2 []) = kc1 `isSubKindCon` kc2
-- IA0: isSubKind (TyConApp kc1 k1s) (TyConApp kc2 k2s) = panic "IA0: isSubKind"  -- IA0_WHEN: *^n -> *
isSubKind (FunTy a1 r1) (FunTy a2 r2)	      = (a2 `isSubKind` a1) && (r1 `isSubKind` r2)
isSubKind (TyConApp kc1 k1s) (TyConApp kc2 k2s) =
  not (isSubOpenTypeKindCon kc1) && kc1 == kc2
  && length k1s == length k2s && all (uncurry eqKind) (zip k1s k2s)
isSubKind (ForAllTy {}) (ForAllTy {})         = panic "IA0: isSubKind on ForAllTy"
isSubKind _             _                     = False

isSubKindCon :: TyCon -> TyCon -> Bool
-- ^ @kc1 \`isSubKindCon\` kc2@ checks that @kc1@ <: @kc2@
isSubKindCon kc1 kc2
  | kc1 == kc2                                             = True
  | isSubArgTypeKindCon kc1   && isArgTypeKindCon kc2      = True
  | isSubOpenTypeKindCon kc1  && isOpenTypeKindCon kc2     = True
  | otherwise                                              = False

defaultKind :: Kind -> Kind
-- ^ Used when generalising: default kind ? and ?? to *. See "Type#kind_subtyping" for more
-- information on what that means

-- When we generalise, we make generic type variables whose kind is
-- simple (* or *->* etc).  So generic type variables (other than
-- built-in constants like 'error') always have simple kinds.  This is important;
-- consider
--	f x = True
-- We want f to get type
--	f :: forall (a::*). a -> Bool
-- Not 
--	f :: forall (a::??). a -> Bool
-- because that would allow a call like (f 3#) as well as (f True),
--and the calling conventions differ.  This defaulting is done in TcMType.zonkTcTyVarBndr.
defaultKind k 
  | isSubOpenTypeKind k = liftedTypeKind
  | isSubArgTypeKind k  = liftedTypeKind
  | otherwise        = k


-- About promoting a type to a kind

isPromotableType :: Type -> Bool
isPromotableType = go emptyVarSet
  where
    go vars (TyConApp tc tys) = ASSERT( not (isPromotedDataTyCon tc) ) all (go vars) tys
    go vars (FunTy arg res) = all (go vars) [arg,res]
    go vars (TyVarTy tvar) = tvar `elemVarSet` vars
    go vars (ForAllTy tvar ty) = isPromotableTyVar tvar && go (vars `extendVarSet` tvar) ty
    go _ _ = panic "IA0: isPromotableType"

isPromotableTyVar :: TyVar -> Bool
isPromotableTyVar = isLiftedTypeKind . varType

-- | Promotes a type to a kind. Assumes the argument is promotable.
promoteType :: Type -> Kind
promoteType (TyConApp tc tys) = mkTyConApp tc (map promoteType tys)
  -- T t1 .. tn  ~~>  'T k1 .. kn  where  ti ~~> ki
promoteType (FunTy arg res) = mkArrowKind (promoteType arg) (promoteType res)
  -- t1 -> t2  ~~>  k1 -> k2  where  ti ~~> ki
promoteType (TyVarTy tvar) = mkTyVarTy (promoteTyVar tvar)
  -- a :: *  ~~>  a :: BOX
promoteType (ForAllTy tvar ty) = ForAllTy (promoteTyVar tvar) (promoteType ty)
  -- forall (a :: *). t  ~~> forall (a :: BOX). k  where  t ~~> k
promoteType _ = panic "IA0: promoteType"

promoteTyVar :: TyVar -> KindVar
promoteTyVar tvar = mkKindVar (tyVarName tvar) tySuperKind

-- If kind is [ *^n -> * ] returns [ Just n ], else returns [ Nothing ]
isPromotableKind :: Kind -> Maybe Int
isPromotableKind kind =
  let (args, res) = splitKindFunTys kind in
  if all isLiftedTypeKind (res:args)
  then Just $ length args
  else Nothing

{- Note [Promoting a Type to a Kind]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We only promote the followings.
* Type variable
* Fully applied arrow type
* Fully applied type constructor of kind @*^n -> *@ (n >= 0)
* Polymorphic type with a type variable of kind star
-}


\end{code}

