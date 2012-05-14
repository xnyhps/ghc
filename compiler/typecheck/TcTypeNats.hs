module TcTypeNats where

import TcSMonad( TcS, emitFrozenError, setEvBind )
import TcCanonical( StopOrContinue(..) )
import TcRnTypes( Ct(..), isGiven, isWanted, ctEvidence, ctEvId )

import TcTypeNatsRules( solve, impossible, computeNewGivenWork )



--------------------------------------------------------------------------------

typeNatStage :: Ct -> TcS StopOrContinue
typeNatStage ct

  -- XXX: Probably need to add the 'ct' to somewhere
  | impossible ct =
      do emitFrozenError ev (cc_depth ct)
         return Stop

  | isGiven ev =
    case solve ct of
      Just _ -> return Stop                 -- trivial fact
      _      -> do computeNewGivenWork ct   -- add some new facts (if any)
                   return $ ContinueWith ct

  | isWanted ev =
    case solve ct of
      Just c  -> do setEvBind (ctEvId ev) c
                    return Stop
      Nothing -> return $ ContinueWith ct   --- XXX: Try improvement here

  -- XXX: TODO
  | otherwise = return $ ContinueWith ct


  where ev = ctEvidence ct




