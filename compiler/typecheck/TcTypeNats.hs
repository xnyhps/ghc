module TcTypeNats where

import Data.Maybe(isNothing)
import Control.Monad(guard, msum, mzero, liftM2, liftM3)

import Var(Var)
import PrelNames( typeNatLeqClassName
                , typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                )
import TyCon( tyConName )
import Class( className )
import Type( getTyVar_maybe, isNumLitTy, mkTyVarTy, mkNumLitTy )
import Coercion ( TypeNatCoAxiom(..) )

import TcSMonad( TcS, emitFrozenError, setEvBind )
import TcCanonical( StopOrContinue(..) )

import TcRnTypes( Xi, Ct(..), isGiven, isWanted, flav_evar )
import TcTypeNatsEval ( minus, divide, logExact, rootExact )
import TcTypeNatsRules()

import TcEvidence ( EvTerm(..), TcCoercion(..) )


--------------------------------------------------------------------------------

typeNatStage :: Ct -> TcS StopOrContinue
typeNatStage ct

  -- XXX: Probably need to add the 'ct' to somewhere
  | impossible ct =
      do emitFrozenError flav (cc_depth ct)
         return Stop

  | isGiven flav =
    case solve ct of
      Just _ -> return Stop                 -- trivial fact
      _      -> return $ ContinueWith ct    -- XXX: TODO (compute new work)

  | isWanted flav =
    case solve ct of
      Just c  -> do setEvBind (flav_evar flav) (EvCoercion c)
                    return Stop
      Nothing -> return $ ContinueWith ct   --- XXX: Try improvement here

  -- XXX: TODO
  | otherwise = return $ ContinueWith ct


  where flav = cc_flavor ct




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
solve :: Ct -> Maybe TcCoercion
solve ct =
  do prop <- ctProp ct
     case prop of

        Leq (N a) (N b) | a <= b            -> return $ by0 $ TnLeqDef a b
        Leq (N 0) (V b)                     -> return $ by1 TnLeq0 (V b)
        Leq (V a) (V b) | a == b            -> return $ by1 TnLeqRefl (V a)

        Add (N a) (N b) (N c) | a + b == c  -> return $ by0 $ TnAddDef a b
        Add (N 0) (V b) (V c) | b == c      -> return $ by1 TnAdd0L (V c)
        Add (V a) (N 0) (V c) | a == c      -> return $ by1 TnAdd0R (V c)

        Mul (N a) (N b) (N c) | a * b == c  -> return $ by0 $ TnMulDef a b
        Mul (N 0) (V b) (N 0)               -> return $ by1 TnMul0L (V b)
        Mul (V a) (N 0) (N 0)               -> return $ by1 TnMul0R (V a)
        Mul (N 1) (V b) (V c) | b == c      -> return $ by1 TnMul1L (V c)
        Mul (V a) (N 1) (V c) | a == c      -> return $ by1 TnMul1R (V c)

        Exp (N a) (N b) (N c) | a ^ b == c  -> return $ by0 $ TnExpDef a b
        Exp (V a) (N 0) (N 1)               -> return $ by1 TnExp0R (V a)
        Exp (V a) (N 1) (V c) | a == c      -> return $ by1 TnExp1R (V c)
        Exp (N 1) (V b) (N 1)               -> return $ by1 TnExp1L (V b)

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

by0 :: TypeNatCoAxiom -> TcCoercion
by0 c = TcTypeNatCo c [] []

by1 :: TypeNatCoAxiom -> Term -> TcCoercion
by1 c t = TcTypeNatCo c [ termTy t ] []

