module TcTypeNatsRules where

-- From other GHC locations
import Var      ( TyVar )
import Coercion ( CoAxiomRule, Eqn, co_axr_rule, co_axr_tynum2_rule
                )
import Type     ( Type,  mkTyVarTy, mkNumLitTy, mkTyConApp )
import TysPrim  ( tyVarList
                , typeNatKind
                )
import TysWiredIn ( typeNatAddTyCon
                  , typeNatMulTyCon
                  , typeNatExpTyCon
                  , typeNatLeqTyCon
                  , trueTy, falseTy
                  )

import Name     ( Name, mkSystemName )
import OccName  ( mkOccName, tcName )
import Unique   ( mkAxiomRuleUnique )
import UniqFM   ( UniqFM, listToUFM )


mkAxName :: Int -> String -> Name
mkAxName n s = mkSystemName (mkAxiomRuleUnique n) (mkOccName tcName s)

mkAx :: Int -> String -> [TyVar] -> [Eqn] -> Eqn -> CoAxiomRule
mkAx n s = co_axr_rule (mkAxName n s)

mkDef :: Int -> String -> (Integer -> Integer -> Eqn) -> CoAxiomRule
mkDef n s = co_axr_tynum2_rule (mkAxName n s)


mkAdd :: Type -> Type -> Type
mkAdd a b = mkTyConApp typeNatAddTyCon [a,b]

mkMul :: Type -> Type -> Type
mkMul a b = mkTyConApp typeNatMulTyCon [a,b]

mkExp :: Type -> Type -> Type
mkExp a b = mkTyConApp typeNatExpTyCon [a,b]

mkLeq :: Type -> Type -> Type
mkLeq a b = mkTyConApp typeNatLeqTyCon [a,b]

natVars :: [TyVar]
natVars = tyVarList typeNatKind

mkBoolLiTy :: Bool -> Type
mkBoolLiTy b = if b then trueTy else falseTy

-- Just some sugar to make the rules a bit more readable
(===) :: Type -> Type -> Eqn
x === y = (x,y)

(<==) :: Type -> Type -> Eqn
x <== y = (mkLeq x y, trueTy)


--------------------------------------------------------------------------------

allRules :: UniqFM CoAxiomRule
allRules =
  let expand x = (x,x)
  in listToUFM $ map expand $
      [ axAddDef, axMulDef, axExpDef, axLeqDef ] ++
      bRules ++
      map snd theRules



--------------------------------------------------------------------------------
axAddDef :: CoAxiomRule
axAddDef = mkDef 0 "AddDef" $ \a b ->
             mkAdd (mkNumLitTy a) (mkNumLitTy b) === mkNumLitTy (a + b)

axMulDef :: CoAxiomRule
axMulDef = mkDef 1 "MulDef" $ \a b ->
             mkMul (mkNumLitTy a) (mkNumLitTy b) === mkNumLitTy (a * b)

axExpDef :: CoAxiomRule
axExpDef = mkDef 2 "ExpDef" $ \a b ->
             mkExp (mkNumLitTy a) (mkNumLitTy b) === mkNumLitTy (a ^ b)

axLeqDef :: CoAxiomRule
axLeqDef = mkDef 3 "LeqDef" $ \a b ->
             mkLeq (mkNumLitTy a) (mkNumLitTy b) === mkBoolLiTy (a <= b)


-- XXX: We should be able to cope with some assumptions in backward
-- reasoning too.
bRules :: [CoAxiomRule]
bRules =
  [ bRule 10 "Add0L" (mkAdd n0 a === a)
  , bRule 11 "Add0R" (mkAdd a n0 === a)

  , bRule 12 "Mul0L" (mkMul n0 a === n0)
  , bRule 13 "Mul0R" (mkMul a n0 === n0)
  , bRule 14 "Mul1L" (mkMul n1 a === a)
  , bRule 15 "Mul1R" (mkMul a n1 === a)

  -- TnExp0L:  (1 <= n) <= 0 ^ n ~ 0
  , bRule 17 "TnExp0R" (mkExp a n0 === n1)
  , bRule 18 "TnExp1L" (mkExp n1 a === n1)
  , bRule 19 "TnExp1R" (mkExp a n1 === a)

  , bRule 20 "Leq0"    (mkLeq n0 a === trueTy)
  , bRule 21 "LeqRefl" (mkLeq a a  === trueTy)
  ]
  where
  bRule s n = mkAx s n (take 1 natVars) []
  a : _     = map mkTyVarTy natVars
  n0        = mkNumLitTy 0
  n1        = mkNumLitTy 1




theRules :: [(Bool,CoAxiomRule)]
theRules =
{-
  [ (True, mkAx "AddComm" (take 3 natVars) [ (mkAdd a b, c) ] (mkAdd b a) c)
  , (True, mkAx "MulComm" (take 3 natVars) [ (mkMul a b, c) ] (mkMul b a) c)
-}

  [ (True, mkAx 30 "AddCancelL" (take 4 natVars)
            [ mkAdd a b === d, mkAdd a c === d ] (b === c))

  , (True, mkAx 31 "AddCancelR" (take 4 natVars)
            [ mkAdd a c === d, mkAdd b c === d ] (a === b))

  , (True, mkAx 32 "MulCancelL" (take 4 natVars)
            [ n1 <== a, mkMul a b === d, mkMul a c === d ] (b === c))

  , (True, mkAx 33 "MulCancelR" (take 4 natVars)
            [ n1 <== c, mkMul a c === d, mkMul b c === d ] (a === b))

  , (True, mkAx 34 "ExpCancelL" (take 4 natVars)
            [ n2 <== a, mkExp a b === d, mkExp a c === d ] (b === c))

  , (True, mkAx 35 "ExpCancelR" (take 4 natVars)
            [ n1 <== c, mkExp a c === d, mkExp b c === d ] (a === b))

  , (True, mkAx 36 "LeqASym" (take 2 natVars)
            [ a <== b, b <== a ] (a === b))

  ]

  where
  a : b : c : d : _ = map mkTyVarTy natVars
  n1 = mkNumLitTy 1
  n2 = mkNumLitTy 2


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




