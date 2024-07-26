{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE KindSignatures           #-}
{-# LANGUAGE ImportQualifiedPost      #-}
{-# LANGUAGE TypeFamilies             #-}
module Utilities.Codes where
import Zilly.Types qualified as ZT
import Utilities.ShowM (ShowM)
import Data.Singletons.TH
import Prelude.Singletons 

$(singletons [d| 
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
  |])

data ServerResponse m a where
  OKR    :: forall expression result m. (ShowM m expression,ShowM m result) => expression -> result -> ServerResponse m OK
  ACKR   :: forall action m. ShowM m action => action -> ServerResponse m ACK
  ERRORR :: ZT.Symbol -> ServerResponse m ERROR
