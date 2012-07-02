module TcTypeNatsRules where

-- From other GHC locations
import Var      ( TyVar )
import Coercion ( CoAxiomRule(..) )
import Type     ( Type,  mkTyVarTy, mkNumLitTy, mkTyConApp )
import PrelNames( unboundKey )
import TysPrim  ( typeNatAddTyCon
                , typeNatMulTyCon
                , typeNatExpTyCon
                , tyVarList
                , typeNatKind
                )
import Name     ( mkSystemName )
import OccName  ( mkOccName, tcName )
import Unique   ( mkPreludeMiscIdUnique )



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


