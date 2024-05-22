{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}



module ZT where

import Control.Concurrent
import Data.Proxy (Proxy)
import Control.Monad.IO.Class
import Data.Kind (Type)
import Data.Typeable 
import Data.Singletons.TH
import Data.Map (Map)
import Control.Monad.Reader
type Symbol = String

data Nat = Z | S Nat deriving (Eq,Show,Typeable)

$(genSingletons [''Nat])


fromSNat :: forall (n :: Nat). SNat n -> Nat
fromSNat = \case
  SZ -> Z
  SS s -> S . fromSNat $ s 

{- f :: forall (p :: Nat) (n :: SNat p) r. (forall n'. SNat n' -> r ) -> r
f g = undefined -}

data ZType a where
  ZTInt    :: ZType Int
  ZTFun    :: ZType a -> ZType b -> ZType (a -> b)
  ZTLazy   :: forall (n :: Nat) a. ZType a -> ZType (Lazy n a)
  ZTLazyES :: ZType a -> ZType (LazyES a)

class RValue m a b | m a -> b where
  rvalue :: m a -> m b

instance RValue m (Value a) (Value a) where
  rvalue = id

instance (MonadIO m, MonadFail m) => RValue m (Lazy (S n) a) (Lazy n a) where
 rvalue mx = do
  Lazyn my <- mx
  liftIO . readMVar $ my


instance (MonadIO m, MonadFail m) => RValue m (Lazy Z a) (Value a) where
 rvalue mx = do
  Lazy my <- mx
  fmap Value . liftIO . readMVar $ my


instance (MonadIO m, MonadFail m) => RValue m (LazyES a) (LazyES a) where
  rvalue mx = mx >>= \case 
    v@(LazyEV _) -> pure v
    LazyEL l -> case l of
      l'@(Lazy _)  -> LazyEV <$> rvalue (pure l')
      l'@(Lazyn _) -> LazyEL <$> rvalue (pure l')




--data LambdaClosure  e f = LambdaClosure e Symbol (f e)
--data FormulaClosure e f = FormulaClosure e (f e)


newtype Value a = Value a

-- ! Lazy levels are indexed by a natural number.
data Lazy (n :: Nat) (a :: Type) where
  Lazy  :: MVar a -> Lazy Z a
  Lazyn :: MVar (Lazy n a) -> Lazy (S n) a

-- | Lazy* "hides" the Lazy indexing.
data LazyES (a :: Type) where
  LazyEL :: Lazy n a -> LazyES a
  LazyEV :: Value a -> LazyES a

{-| Zilly expression Language with generalized operators. 

Some examples:

  * @Minus (Val _) (Val _)        :: E env m (Value Int)@
  * @Minus (Val _) (Lazy 3 _)     :: E env m (Lazy 3 _)@
  * @Minus (Lazy 3 _) (Lazy 10 _) :: E env m (Lazy 10 _)@
  * @Minus (LazyES _) (Lazy 10 _) :: E env m (LazyES  _)@
 
|-}
data E (env :: Type) (m :: Type -> Type) (a :: Type) where
  Val   :: Int -> E env m (Value Int)
  Var   :: MonadReader env m => m a -> E env m a
  Minus :: 
    ( RValue m a c0
    , RValue m b c1
    , r ~ UpperBound c0 c1 
    )
    => E env m a -> E env m b -> E env m r
  Less :: 
    ( RValue m a c0
    , RValue m b c1
    , r ~ UpperBound c0 c1 
    )
    => E env m a -> E env m b -> E env m r
  If    ::
    ( RValue m x0 (Value Int)
    , RValue m x1 c0
    , RValue m x2 c1
    , r ~ UpperBound c0 c1
    )
    => E env m x0 -> E env m x1 -> E env m x2 -> E env m r
  Lambda :: m a -> E env m b -> E env m (a -> b)
  --LambdaClosure :: E env m (a -> b) -> 
  

  

type family ETypeRep (x :: Type) :: Type where
  ETypeRep (E env m Int) = ZType Int
  --ETypeRep (Var e) = ETypeRep e

type family Max (x :: Nat) (y :: Nat) :: Nat where
  Max Z x = Z
  Max x Z = Z
  Max (S x) (S y) = S (Max x y)
  --EType (Var e) = EType e

type family UpperBound (x :: Type) (y :: Type) :: Type where
  UpperBound (Lazy n a) (Lazy m a) = Lazy (Max n m) a
  UpperBound (LazyES a) x = LazyES a
  UpperBound x (LazyES a) = LazyES a
  UpperBound (Value a) (f a) = f a
  UpperBound (f a) (Value a) = f a



  
  --Var :: E env m a -> E env m a






