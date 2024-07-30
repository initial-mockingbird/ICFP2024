{-# OPTIONS_GHC -ddump-splices        #-}
{-# OPTIONS_GHC -ddump-to-file        #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ImportQualifiedPost      #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE CPP                      #-}

#ifndef WASM
{-# LANGUAGE TemplateHaskell          #-}
#endif


module Utilities.Codes where
import Zilly.Types qualified as ZT
import Utilities.ShowM (ShowM)
import Prelude.Singletons 

#ifndef WASM
import Data.Singletons.TH
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
#else
data ServerResponseCodes = OK | ACK | ERROR
data ServerNotificationCodes
  = SYM | SYP | SYU | ASY
type OKSym0 :: ServerResponseCodes
type family OKSym0 :: ServerResponseCodes where
  OKSym0 = OK
type ACKSym0 :: ServerResponseCodes
type family ACKSym0 :: ServerResponseCodes where
  ACKSym0 = ACK
type ERRORSym0 :: ServerResponseCodes
type family ERRORSym0 :: ServerResponseCodes where
  ERRORSym0 = ERROR
type SYMSym0 :: ServerNotificationCodes
type family SYMSym0 :: ServerNotificationCodes where
  SYMSym0 = SYM
type SYPSym0 :: ServerNotificationCodes
type family SYPSym0 :: ServerNotificationCodes where
  SYPSym0 = SYP
type SYUSym0 :: ServerNotificationCodes
type family SYUSym0 :: ServerNotificationCodes where
  SYUSym0 = SYU
type ASYSym0 :: ServerNotificationCodes
type family ASYSym0 :: ServerNotificationCodes where
  ASYSym0 = ASY
data SServerResponseCodes :: ServerResponseCodes -> Type
  where
    SOK :: SServerResponseCodes (OK :: ServerResponseCodes)
    SACK :: SServerResponseCodes (ACK :: ServerResponseCodes)
    SERROR :: SServerResponseCodes (ERROR :: ServerResponseCodes)
type instance Sing @ServerResponseCodes = SServerResponseCodes
instance SingKind ServerResponseCodes where
  type Demote ServerResponseCodes = ServerResponseCodes
  fromSing SOK = OK
  fromSing SACK = ACK
  fromSing SERROR = ERROR
  toSing OK = SomeSing SOK
  toSing ACK = SomeSing SACK
  toSing ERROR = SomeSing SERROR
data SServerNotificationCodes :: ServerNotificationCodes
                                  -> Type
  where
    SSYM :: SServerNotificationCodes (SYM :: ServerNotificationCodes)
    SSYP :: SServerNotificationCodes (SYP :: ServerNotificationCodes)
    SSYU :: SServerNotificationCodes (SYU :: ServerNotificationCodes)
    SASY :: SServerNotificationCodes (ASY :: ServerNotificationCodes)
type instance Sing @ServerNotificationCodes = SServerNotificationCodes
instance SingKind ServerNotificationCodes where
  type Demote ServerNotificationCodes = ServerNotificationCodes
  fromSing SSYM = SYM
  fromSing SSYP = SYP
  fromSing SSYU = SYU
  fromSing SASY = ASY
  toSing SYM = SomeSing SSYM
  toSing SYP = SomeSing SSYP
  toSing SYU = SomeSing SSYU
  toSing ASY = SomeSing SASY
instance SingI OK where
  sing = SOK
instance SingI ACK where
  sing = SACK
instance SingI ERROR where
  sing = SERROR
instance SingI SYM where
  sing = SSYM
instance SingI SYP where
  sing = SSYP
instance SingI SYU where
  sing = SSYU
instance SingI ASY where
  sing = SASY
#endif
data ServerResponse m a where
  OKR    :: forall expression result m. (ShowM m expression,ShowM m result) => expression -> result -> ServerResponse m OK
  ACKR   :: forall action m. ShowM m action => action -> ServerResponse m ACK
  ERRORR :: ZT.Symbol -> ServerResponse m ERROR
