module TcTypeNatsRules where

-- From other GHC locations
import Var      ( TyVar )
import Coercion ( CoAxiomRule(..) )
import Type     ( Type,  mkTyVarTy, mkNumLitTy, mkTyConApp )
import PrelNames( unboundKey )
import TysPrim  ( tyVarList
                , typeNatKind
                )
import TysWiredIn ( typeNatAddTyCon
                  , typeNatMulTyCon
                  , typeNatExpTyCon
                  )

import Name     ( mkSystemName )
import OccName  ( mkOccName, tcName )



mkAx :: String -> [TyVar] -> [(Type,Type)] -> Type -> Type -> CoAxiomRule
mkAx n vs asmps lhs rhs = CoAxiomRule
  { co_axr_name   = mkAxName n
  , co_axr_tvs    = vs
  , co_axr_asmps  = asmps
  , co_axr_lhs    = lhs
  , co_axr_rhs    = rhs
  }
  where
  mkAxName x = mkSystemName unboundKey (mkOccName tcName x)

mkAdd :: Type -> Type -> Type
mkAdd a b = mkTyConApp typeNatAddTyCon [a,b]

mkMul :: Type -> Type -> Type
mkMul a b = mkTyConApp typeNatMulTyCon [a,b]

mkExp :: Type -> Type -> Type
mkExp a b = mkTyConApp typeNatExpTyCon [a,b]

natVars :: [TyVar]
natVars = tyVarList typeNatKind


--------------------------------------------------------------------------------

axName :: String -> Integer -> Integer -> String
axName x a b = x ++ "_" ++ show a ++ "_" ++ show b

axAddDef :: Integer -> Integer -> CoAxiomRule
axAddDef a b = mkAx (axName "AddDef" a b) [] []
             (mkAdd (mkNumLitTy a) (mkNumLitTy b)) (mkNumLitTy (a + b))

axMulDef :: Integer -> Integer -> CoAxiomRule
axMulDef a b = mkAx (axName "MulDef" a b) [] []
             (mkMul (mkNumLitTy a) (mkNumLitTy b)) (mkNumLitTy (a * b))

axExpDef :: Integer -> Integer -> CoAxiomRule
axExpDef a b = mkAx (axName "ExpDef" a b) [] []
             (mkExp (mkNumLitTy a) (mkNumLitTy b)) (mkNumLitTy (a ^ b))


-- XXX: We should be able to cope with some assumptions in backward
-- reasoning too.
bRules :: [CoAxiomRule]
bRules =
  [ bRule "Add0L" (mkAdd n0 a) a
  , bRule "Add0R" (mkAdd a n0) a

  , bRule "Mul0L" (mkMul n0 a) n0
  , bRule "Mul0R" (mkMul a n0) n0
  , bRule "Mul1L" (mkMul n1 a) a
  , bRule "Mul1R" (mkMul a n1) a

  -- TnExp0L
  , bRule "TnExp0R" (mkExp a n0) n1
  , bRule "TnExp1L" (mkExp n1 a) n1
  , bRule "TnExp1R" (mkExp a n1) a
  ]
  where
  bRule y   = mkAx y (take 1 natVars) []
  a : _     = map mkTyVarTy natVars
  n0        = mkNumLitTy 0
  n1        = mkNumLitTy 1




theRules :: [(Bool,CoAxiomRule)]
theRules =
{-
  [ (True, mkAx "AddComm" (take 3 natVars) [ (mkAdd a b, c) ] (mkAdd b a) c)
  , (True, mkAx "MulComm" (take 3 natVars) [ (mkMul a b, c) ] (mkMul b a) c)
-}

  [ (True, mkAx "AddCancelL" (take 4 natVars)
            [ (mkAdd a b, d), (mkAdd a c, d) ] b c)

  , (True, mkAx "AddCancelR" (take 4 natVars)
            [ (mkAdd a c, d), (mkAdd b c, d) ] a b)
  ]

  where a : b : c : d : _ = map mkTyVarTy natVars



{-
fRules :: [Rule]
fRules =
  [ rule TnLeqASym    [ leq a b, leq b a ] $ eq a b
  , rule TnLeqTrans   [ leq a b, leq b c ] $ leq a c

  , rule TnMulCancelL [ leq n1 a, mul a b1 c, mul a b2 c ] $ eq b1 b2
  , rule TnExpCancelL [ leq n2 a, exp a b1 c, exp a b2 c ] $ eq b1 b2

  , rule TnMulCancelR [ leq n1 b, mul a1 b c, mul a2 b c ] $ eq a1 a2
  , rule TnExpCancelR [ leq n1 b, exp a1 b c, exp a2 b c ] $ eq a1 a2
  ]
  where
  a : a1 : a2 : b : b1 : b2 : c : _ = map Var [ 0 .. ]
  n1 = Num 1
  n2 = Num 2
-}


--------------------------------------------------------------------------------


{-

Consider a problem like this:

  [W] a + b ~ b + a

GHC de-sugars this into:

  [W] p: a + b ~ c
  [W] q: b + a ~ c

When we add the 2nd one, we should notice that it can be solved in terms
of the first one...
-}




