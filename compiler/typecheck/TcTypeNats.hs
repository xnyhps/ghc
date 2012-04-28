module TcTypeNats where

import Data.Maybe(isNothing)

import TcRnTypes( Xi, Ct(..) )
import PrelNames( typeNatLeqClassName
                , typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                )
import TyCon(tyConName)
import Class(className)
import Type(isNumLitTy, eqType)

import TcTypeNatsEval (minus,divide,logExact,rootExact)
import TcTypeNatsRules()

--------------------------------------------------------------------------------
solve :: Ct -> Maybe Proof

solve (CDictCan { cc_class = cl, cc_tyargs = [t1,t2] })

  | className cl == typeNatLeqClassName =
    case () of
      _ | Just 0 <- isNumLitTy t1   -> Just $ byLeq0 t2
        | eqType t1 t2              -> Just $ byLeqRefl t1
        | Just a <- isNumLitTy t1
        , Just b <- isNumLitTy t2
        , a <= b                    -> Just $ byLeqDef a b

      _ -> Nothing


solve (CFunEqCan { cc_fun = tc, cc_tyargs = [t1,t2], cc_rhs = t3 })

  | tyConName tc == typeNatAddTyFamName =
    case () of
      _ | Just 0 <- isNumLitTy t1, eqType t2 t3 -> Just $ byAdd0_L t2

        | Just 0 <- isNumLitTy t2, eqType t1 t3 -> Just $ byAdd0_R t1

        | Just a <- isNumLitTy t1
        , Just b <- isNumLitTy t2
        , Just c <- isNumLitTy t3, a + b == c   -> Just $ byDefAdd a b

      _ -> Nothing


  | tyConName tc == typeNatMulTyFamName =
    case () of
      _ | Just 0 <- isNumLitTy t1
        , Just 0 <- isNumLitTy t3 -> Just $ byMul0_L t2

        | Just 0 <- isNumLitTy t2
        , Just 0 <- isNumLitTy t3 -> Just $ byMul0_R t2

        | Just 1 <- isNumLitTy t1, eqType t2 t3 -> Just $ byMul1_L t2

        | Just 1 <- isNumLitTy t2, eqType t1 t3 -> Just $ byMul1_R t2

        | Just a <- isNumLitTy t1
        , Just b <- isNumLitTy t2
        , Just c <- isNumLitTy t3, a * b == c   -> Just $ byDefMul a b

      _ -> Nothing


  | tyConName tc == typeNatExpTyFamName =
    case () of
      _ | Just 0 <- isNumLitTy t2
        , Just 1 <- isNumLitTy t3 -> Just $ byExp0_R t1

        | Just 1 <- isNumLitTy t2, eqType t1 t3 -> Just $ byExp1_R t1

        | Just 1 <- isNumLitTy t1
        , Just 1 <- isNumLitTy t3 -> Just $ byExp1_L t2

        | Just a <- isNumLitTy t1
        , Just b <- isNumLitTy t2
        , Just c <- isNumLitTy t3, a ^ b == c   -> Just $ byDefExp a b

      _ -> Nothing

solve _ = Nothing



impossible :: Ct -> Bool

impossible (CDictCan { cc_class = cl, cc_tyargs = [t1,t2] })
  | className cl == typeNatLeqClassName
  , Just a <- isNumLitTy t1
  , Just b <- isNumLitTy t2 = not (a <= b)


impossible (CFunEqCan { cc_fun = tc, cc_tyargs = [t1,t2], cc_rhs = t3 })

  | tyConName tc == typeNatAddTyFamName, Just b <- isNumLitTy t3 =
    case () of
      _ | Just a <- isNumLitTy t1 -> isNothing (minus b a)
        | Just a <- isNumLitTy t2 -> isNothing (minus b a)
      _                           -> False

  | tyConName tc == typeNatMulTyFamName, Just b <- isNumLitTy t3 =
    case () of
      _ | Just a <- isNumLitTy t1 ->
          case a of
            0 -> not (b == 0)
            _ -> isNothing (divide b a)

        | Just a <- isNumLitTy t2 ->
          case a of
             0 -> not (b == 0)
             _ -> isNothing (divide b a)

      _ -> False

  | tyConName tc == typeNatExpTyFamName, Just b <- isNumLitTy t3 =
    case () of
      _ | Just a <- isNumLitTy t1 ->
          case a of
            0 -> not (b == 0 || b == 1)
            1 -> not (b == 1)
            _ -> isNothing (logExact b a)

        | Just a <- isNumLitTy t2 ->
          case a of
            0 -> not (b == 1)
            _ -> isNothing (rootExact b a)

      _ -> False


impossible _ = False



--------------------------------------------------------------------------------
type Proof = ()


byDefAdd :: Integer -> Integer -> Proof
byDefAdd _ _  = ()

byDefMul :: Integer -> Integer -> Proof
byDefMul _ _  = ()

byDefExp :: Integer -> Integer -> Proof
byDefExp _ _  = ()

byLeqDef :: Integer -> Integer -> Proof
byLeqDef _ _  = ()


-- a <= a
byLeqRefl :: Xi -> Proof
byLeqRefl _ = ()

-- 0 <= a
byLeq0  :: Xi -> Proof
byLeq0 _ = ()

-- a + 0 = a
byAdd0_L :: Xi -> Proof
byAdd0_L _    = ()

-- 0 + a = a
byAdd0_R :: Xi -> Proof
byAdd0_R _    = ()

-- 0 * a = 0
byMul0_L :: Xi -> Proof
byMul0_L _    = ()

-- a * 0 = 0
byMul0_R :: Xi -> Proof
byMul0_R _    = ()

-- a * 1 = a
byMul1_R :: Xi -> Proof
byMul1_R _    = ()

-- 1 * a = a
byMul1_L :: Xi -> Proof
byMul1_L _    = ()

-- a ^ 0 = 1
byExp0_R :: Xi -> Proof
byExp0_R _ = ()

-- (1 <= a) => 0 ^ a = 0

-- 1 ^ a = 1
byExp1_L :: Xi -> Proof
byExp1_L _ = ()

-- a ^ 1 = a
byExp1_R :: Xi -> Proof
byExp1_R _ = ()




