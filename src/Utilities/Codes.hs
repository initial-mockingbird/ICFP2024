{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
module Utilities.Codes where
import Zilly.Types (Symbol)
import Utilities.ShowM (ShowM)

-- | Server response content format
data ServerResponseCodes  
  = OK
  | ACK
  | ERROR

-- | Server notification content format
data ServerNotificationCodes
  = SYM
  | SYP
  | SYU
  | ASY


data ServerResponse m a where
  OKR    :: forall expression result m. (ShowM m expression,ShowM m result) => expression -> result -> ServerResponse m OK
  ACKR   :: forall action m. ShowM m action => action -> ServerResponse m ACK
  ERRORR :: Symbol -> ServerResponse m ERROR
