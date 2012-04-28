module TcTypeNats where

import Data.Maybe(isNothing)
import Control.Monad(guard, msum, mzero, liftM2, liftM3)

import TcRnTypes( Xi, Ct(..) )
import PrelNames( typeNatLeqClassName
                , typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                )
import TyCon(tyConName)
import Class(className)
import Type(getTyVar_maybe, isNumLitTy, mkTyVarTy, mkNumLitTy)

import TcTypeNatsEval (minus,divide,logExact,rootExact)
import TcTypeNatsRules()
import Var(Var)

--------------------------------------------------------------------------------
data Term = V Var | N Integer
            deriving Eq

data Prop = Add Term Term Term
          | Mul Term Term Term
          | Exp Term Term Term
          | Leq Term Term
            deriving Eq

tyTerm :: Xi -> Maybe Term
tyTerm t = msum [ V `fmap` getTyVar_maybe t, N `fmap` isNumLitTy t ]

termTy :: Term -> Xi
termTy (V x) = mkTyVarTy x
termTy (N x) = mkNumLitTy x

ctProp :: Ct -> Maybe Prop
ctProp (CDictCan { cc_class = cl, cc_tyargs = [t1,t2] }) =
  do guard (className cl == typeNatLeqClassName)
     liftM2 Leq (tyTerm t1) (tyTerm t2)

ctProp (CFunEqCan { cc_fun = tc, cc_tyargs = [t1,t2], cc_rhs = t3 }) =
  msum [ do guard (tyConName tc == typeNatAddTyFamName)
            liftM3 Add (tyTerm t1) (tyTerm t2) (tyTerm t3)

       , do guard (tyConName tc == typeNatMulTyFamName)
            liftM3 Mul (tyTerm t1) (tyTerm t2) (tyTerm t3)

       , do guard (tyConName tc == typeNatExpTyFamName)
            liftM3 Exp (tyTerm t1) (tyTerm t2) (tyTerm t3)
       ]

ctProp _ = Nothing

--------------------------------------------------------------------------------
solve :: Ct -> Maybe Proof
solve ct =
  do prop <- ctProp ct
     case prop of

        Leq (N a) (N b) | a <= b            -> return $ byLeqDef a b
        Leq (N 0) (V b)                     -> return $ byLeq0 (V b)
        Leq (V a) (V b) | a == b            -> return $ byLeqRefl (V a)

        Add (N a) (N b) (N c) | a + b == c  -> return $ byDefAdd a b
        Add (N 0) (V b) (V c) | b == c      -> return $ byAdd0_L (V b)
        Add (V a) (N 0) (V c) | a == c      -> return $ byAdd0_R (V a)

        Mul (N a) (N b) (N c) | a * b == c  -> return $ byDefMul a b
        Mul (N 0) (V b) (N 0)               -> return $ byMul0_L (V b)
        Mul (V a) (N 0) (N 0)               -> return $ byMul0_R (V a)
        Mul (N 1) (V b) (V c) | b == c      -> return $ byMul1_L (V b)
        Mul (V a) (N 1) (V c) | a == c      -> return $ byMul1_R (V a)

        Exp (N a) (N b) (N c) | a ^ b == c  -> return $ byDefExp a b
        Exp (V a) (N 0) (N 1)               -> return $ byExp0_R (V a)
        Exp (V a) (N 1) (V c) | a == c      -> return $ byExp1_R (V a)
        Exp (N 1) (V b) (N 1)               -> return $ byExp1_L (V b)

        _                                   -> mzero





impossible :: Ct -> Bool

impossible ct =
  case ctProp ct of
    Nothing   -> False
    Just prop ->
      case prop of
        Leq (N a) (N b)       -> not (a <= b)

        Add (N a) _     (N c) -> isNothing (minus c a)
        Add _     (N b) (N c) -> isNothing (minus c b)

        Mul (N 0) _     (N c) -> not (c == 0)
        Mul (N a) _     (N c) -> isNothing (divide c a)
        Mul _     (N 0) (N c) -> not (c == 0)
        Mul _     (N b) (N c) -> isNothing (divide c b)

        Exp (N 0) _     (N c) -> not (c == 0 || c == 1)
        Exp (N 1) _     (N c) -> not (c == 1)
        Exp (N a) _     (N c) -> isNothing (logExact c a)
        Exp _     (N 0) (N c) -> not (c == 1)
        Exp _     (N b) (N c) -> isNothing (rootExact c b)

        _                     -> False



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
byLeqRefl :: Term -> Proof
byLeqRefl _ = ()

-- 0 <= a
byLeq0  :: Term -> Proof
byLeq0 _ = ()

-- a + 0 = a
byAdd0_L :: Term -> Proof
byAdd0_L _    = ()

-- 0 + a = a
byAdd0_R :: Term -> Proof
byAdd0_R _    = ()

-- 0 * a = 0
byMul0_L :: Term -> Proof
byMul0_L _    = ()

-- a * 0 = 0
byMul0_R :: Term -> Proof
byMul0_R _    = ()

-- a * 1 = a
byMul1_R :: Term -> Proof
byMul1_R _    = ()

-- 1 * a = a
byMul1_L :: Term -> Proof
byMul1_L _    = ()

-- a ^ 0 = 1
byExp0_R :: Term -> Proof
byExp0_R _ = ()

-- (1 <= a) => 0 ^ a = 0

-- 1 ^ a = 1
byExp1_L :: Term -> Proof
byExp1_L _ = ()

-- a ^ 1 = a
byExp1_R :: Term -> Proof
byExp1_R _ = ()




