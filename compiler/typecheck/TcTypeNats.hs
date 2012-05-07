module TcTypeNats where

import TcSMonad( TcS, emitFrozenError, setEvBind )
import TcCanonical( StopOrContinue(..) )
import TcEvidence ( EvTerm(..) )
import TcRnTypes( Ct(..), isGiven, isWanted, flav_evar )

import TcTypeNatsRules( solve, impossible )



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




