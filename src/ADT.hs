{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImportQualifiedPost #-}

module ADT where

import Lensy
import Control.Monad.IO.Class
import Data.Kind (Type)
import Data.Typeable hiding (cast)
import Control.Monad.Reader 


import Control.Monad
import Unsafe.Coerce (unsafeCoerce)
import ShowM
import Control.Applicative
import Lensy

--------------------------
-- Aux Functions
--------------------------



connector :: Int -> Bool
connector = (> 0)

rConnector :: Bool -> Int
rConnector = \case
  True -> 1
  False -> -1

cTrue :: (ShowM m env) => E env m (Value Int)
cTrue = Val (rConnector True)

cFalse :: (ShowM m env) => E env m (Value Int)
cFalse = Val (rConnector False)

cvalue :: (MonadReader env m, Alternative m) => LensyM' m env a -> m a
cvalue l = ask >>= viewyM' l
  



--------------------------
-- Types
--------------------------

type ADTContext m env =
  ( MonadIO m
  , Typeable m
  , Typeable env
  --, Interpreter m env
  , MonadReader env m
  , Alternative m
  )



type Symbol = String

--------------------------
-- Classes
--------------------------

class  RValue m a b | a -> m b where
  rvalue :: a -> m b

class  (Typeable b) => Cast m env a b | a -> m env b where
  cast ::  a -> m (UpperBound env a b)

class Interpreter m env | m -> env where
  interpret :: E env m a -> m a


--------------------------
-- Tags
--------------------------


{- newtype Value a = Value (Identity a)
  deriving newtype (Eq, Ord, Show, Num, Functor, Applicative, Typeable)

data Lazy (a :: Type) = BLazy a | Lazy (Lazy a)
  deriving (Functor)

-- | Lazy star
data LazyS (a :: Type) where
  LazyEL :: (BaseType a ~ b) => Lazy a -> LazyS b
  LazyEV :: Value a -> LazyS (Value a) -}

data Value a

data Lazy (a :: Type)

-- | Lazy star
data LazyS (a :: Type)

--------------------------
-- Expression language
--------------------------

{-| Zilly expression Language. |-}
data  E (env :: Type) (m :: Type -> Type) (a :: Type) where
  Val   :: ShowM m env
    => Int -> E env m (Value Int)
  Var   :: forall a m env. 
    ( ShowM m env
    , ShowM m (E env m a)
    )
    => LensyM' m env (E env m a) -> E env m a
  Minus :: forall m a b env.
    ( RValue m (E env m a) (E env m (Value Int))
    , RValue m (E env m b) (E env m (Value Int))
    , ShowM m (E env m a)
    , ShowM m (E env m b)
    , ShowM m (E env m (Value Int))
    , ShowM m env
    )
    => E env m a -> E env m b -> E env m (Value Int)
  Less ::
    ( RValue m (E env m a) (E env m (Value Int))
    , RValue m (E env m b) (E env m (Value Int))
    , ShowM m (E env m a)
    , ShowM m (E env m b)
    , ShowM m (E env m (Value Int))
    , ShowM m env
    )
    => E env m a -> E env m b -> E env m (Value Int)
  If    :: forall c0 c1 x1 x2 x0 r env m.
    ( RValue m (E env m x0) (E env m (Value Int))
    , RValue m (E env m x1) (E env m c0)
    , RValue m (E env m x2) (E env m c1)
    , Cast m env (E env m c0) (UpperBound env (E env m c0) (E env m c1))
    , Cast m env (E env m c1) (UpperBound env (E env m c0) (E env m c1))
    , E env m r ~ UpperBound env (E env m c0) (E env m c1)
    , ShowM m (E env m x0)
    , ShowM m (E env m x1)
    , ShowM m (E env m x2)
    , ShowM m env
    , ShowM m (E env m r)
    )
    => E env m x0 -> E env m x1 -> E env m x2 -> E env m r
  Lambda  :: forall a b c m env.
    ( RValue m (E env m b) (E env m c)
    , ShowM m (E env m b)
    , ShowM m (E env m c)
    , ShowM m env
    , Typeable b
    , Typeable c
    , Typeable a
    , ShowM m (E env m (Value (a -> c)))
    )
    => LensyM' m env (E env m a) -> E env m b -> E env m (Value (a -> c))
  LambdaC ::
    ( RValue m (E env m b) (E env m c)
    , ShowM m (E env m b)
    , ShowM m (E env m c)
    , ShowM m env
    , ShowM m (E env m (Value (a -> c)))
    )
    => (E env m a -> m (E env m c)) 
    -> (env, LensyM' m env (E env m a), E env m b) 
    -> E env m (Value (a -> c))
  App :: forall f x b arg m env.
    ( RValue m f (E env m (Value (arg -> b)))
    , RValue m (E env m x) (E env m arg)
    , ShowM m f
    , ShowM m (E env m x)
    , ShowM m env
    , ShowM m (E env m (Value (arg -> b)))
    , ShowM m (E env m arg) -- !
    , ShowM m (E env m b)
    )
    => f -> E env m x -> E env m b

  Defer :: forall a env m b.
    ( RValue m (E env m a) (E env m b)
    , ShowM m (E env m a)
    , ShowM m env
    )
    => E env m a -> E env m (Lazy a)
  Closure ::
    ( ShowM m (E env m  a)
    , ShowM m env
    )
    => (E env m a,env) -> E env m a
  ValueC :: 
    ( ShowM m env
    , ShowM m (E env m (Value a))
    ) 
    => (E env m (Value a), env) -> E env m (Value a)

deriving instance Typeable (E env m a)


--------------------------
-- Aux type families
--------------------------

type family BaseType (a :: Type) :: Type where
  --BaseType (Value (LClosure env (a -> b))) = Value (a -> b)
  BaseType (Value a)    = (Value a)
  BaseType (Lazy a)   = BaseType a
  BaseType (LazyS a)  = BaseType a

type family UpperBound (env :: Type) (x :: Type) (y :: Type) :: Type where
  UpperBound env (Lazy a) (Lazy b) = Lazy (UpperBound env (BaseType a) (BaseType b))
  UpperBound env (Value a) (f b) = f (UpperBound env a b)
  UpperBound env (f a) (Value b) = f (UpperBound env a b)
  UpperBound _   a     a         = a


------------------------------------
-- Proofs regarding type families
------------------------------------

safeCoerce :: forall a b. (a ~ b) => a -> b
safeCoerce = unsafeCoerce

commute :: UpperBound env c0 c1 -> UpperBound env c1 c0
commute = unsafeCoerce

idempotency ::  UpperBound env c0 c0 -> c0
idempotency = unsafeCoerce

reflexivity :: forall {c0} env . c0 -> UpperBound env c0 c0
reflexivity = unsafeCoerce

leftAssociate :: UpperBound env c0 (UpperBound env c1 c2) ->  UpperBound env (UpperBound env c0 c1) c2
leftAssociate = unsafeCoerce

lSubstitution :: forall a0 a1 env b. (a0 -> a1) -> UpperBound env a0 b -> UpperBound env a1 b
lSubstitution = unsafeCoerce

rSubstitution :: (a0 -> a1) -> UpperBound env b a0 -> UpperBound env b a1
rSubstitution = unsafeCoerce

labsortion :: forall env c0 c1. UpperBound env c0 (UpperBound env c0 c1) -> UpperBound env c0 c1
labsortion
  = lSubstitution @_ @_ @env @c1
    (idempotency @env @c0)
  . leftAssociate @env @c0 @c0 @c1

labsortion' :: forall env c0 c1. UpperBound env c1 (UpperBound env c0 c1)  -> UpperBound env c0 c1
labsortion'
  = commute @env @c1 @c0
  . labsortion @env @c1 @c0
  . rSubstitution @_ @_ @env @c1 (commute @env @c0 @c1)


--------------------------
-- R-Value Instances
--------------------------



instance
  ( ADTContext m env
  , ShowM m (E env m (Value Int))

  ) =>  RValue m 
    (E env m (Value a)) 
    (E env m (Value a)) where
  rvalue (Val n) = pure (Val n)
  rvalue (ValueC (e,gamma)) = localM (pure . const gamma) $ rvalue e
  rvalue (Minus a b) = (,) <$> rvalue a <*> rvalue b >>= \case
    (Val a', Val b') -> pure $ Val (a' - b')
    (a',b') -> liftA2 Minus  (rvalue a') (rvalue b') >>= rvalue
  rvalue (Less a b) = (,) <$> rvalue a <*> rvalue b >>= \case
    (Val a', Val b') -> pure $ Val (rConnector $ a' < b')
    (a',b') -> liftA2 Less  (rvalue a') (rvalue b') >>= rvalue
  rvalue (App f a) = rvalue f >>= \case
    LambdaC _ (gamma, x, t) -> do
      arg <-  rvalue a
      t'  <- localM (setyMF' x arg . const gamma) $ rvalue t
      gamma' <- setyMF' x arg gamma
      pure $ Closure (t',gamma')
    f' ->  rvalue $ App f' a
  rvalue x@(Var {}) = genRVar x
  rvalue e@(If {}) = genRVIf e
  rvalue (LambdaC f gamma) = do 
    pure $ LambdaC f gamma
  rvalue (Lambda x t) = do
    gamma <- ask
    let f arg = localM (setyMF' x arg . const gamma) $ rvalue t
    pure $ LambdaC f (gamma,x,t)
  rvalue (Closure (e,gamma)) = localM (pure . const gamma) $ rvalue e

-- | Lazy <a> are reduced to a
instance
  ( ADTContext m env
  , ShowM m (E env m (Value Int))
  )
  => RValue m 
    (E env m (Lazy (Value a))) 
    (E env m (Value a)) where
  rvalue (Defer v) = do
    gamma <- ask 
    pure $ Closure (v,gamma)
  rvalue (App f a) = rvalue f >>= \case
    LambdaC _ (gamma, x, t) -> do
      arg <-  rvalue a
      t'  <- localM (setyMF' x arg . const gamma) $ rvalue t
      gamma' <- setyMF' x arg gamma
      rvalue $ Closure (t',gamma')
    f' ->  rvalue $ App f' a
  rvalue (Closure (e,gamma)) = localM (pure . const gamma) $ rvalue e
  rvalue x@(Var {}) = genRVar x
  rvalue e@(If {})  = genRVIf e


instance
  ( ADTContext m env
  , ShowM m (E env m (Value Int))
  , ShowM m (E env m a)
  , ShowM m (E env m (Lazy a))
  )
  => RValue m 
    (E env m (Lazy (Lazy a))) 
    (E env m (Lazy a)) where
  rvalue (Defer v) = do
    gamma <- ask 
    pure $ Closure (v,gamma)
  rvalue (Var x) = rvalue <=< cvalue $ x
  rvalue (If cond t f) = genRVIf (If cond t f)
  rvalue (App f a) = rvalue (App f a)
  rvalue (Closure (e :: E env m (Lazy (Lazy a)), gamma)) = do 
    e' <- localM (pure . const gamma) $ rvalue e
    pure $ Closure (e',gamma)
------------------------------
-- Generic R-Value Functions
------------------------------

genRVar :: (ADTContext m env, RValue m (E env m a) c) => E env m a -> m c
genRVar (Var x) = rvalue <=< cvalue $ x
genRVar _ = undefined


genRVIf ::forall m env a b.
  ( ADTContext m env
  , RValue m (E env m a) b
  , ShowM m (E env m (Value Int))
  )
  => E env m a -> m b
genRVIf (If @c0 @c1 cond t f) = rvalue cond >>= \case
    Val (connector -> True) -> do
      x <- rvalue t
      g <- labsortion @env @(E env m c0) @(E env m c1) . safeCoerce
        <$> cast @m @env @(E env m c0) @(UpperBound env (E env m c0) (E env m c1)) x
      rvalue g
    Val (connector -> False) -> do
      x <- rvalue f
      g <- labsortion' @env @(E env m c0) @(E env m c1) . safeCoerce
        <$> cast @m @env @(E env m c1) @(UpperBound env (E env m c0) (E env m c1)) x
      rvalue g
    c' -> rvalue (If c' t f)
genRVIf _ = undefined

--------------------------
-- Cast Instances
--------------------------

instance (Applicative m, Typeable m, Typeable env,  Typeable (Value a))
  => Cast m env (E env m (Value a)) (E env m (Value a)) where
  cast = pure . reflexivity

--------------------------
-- Num Instance
--------------------------

{- instance (ADTContext m env, ShowMContext m env) => Num (E env m (Value Int)) where
  (+) = error "Not implemented"
  (*) = error "Not implemented"
  (-) = error "Not implemented"
  abs = error "Not implemented"
  signum = error "Not implemented"
  fromInteger = Val . fromInteger -}