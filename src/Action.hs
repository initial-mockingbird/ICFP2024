{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Action where

import Lensy
import ADT
import Data.Kind (Type)
import Control.Monad.IO.Class
import Control.Monad.Reader
import VarMap
import TypedMap
import Data.Typeable
import ShowM
import Data.Foldable
import Control.Monad

type ShowMContext m env =
  ( ShowM m env
  , forall a. ShowM m (E env m a)
  , forall a. ShowM m (A env m a)
  )

infix 0 :=
infix 0 :=.
data A (env :: Type) (m :: Type -> Type) (r :: Type) where
  (:=) :: forall x a m env.
    ( Typeable x
    , Typeable a
    , RValue m (E env m x) a
    --, SetEnv m env a
    ) 
    =>  LensyM' m env a -> E env m x -> A env m ()
  (:=.) :: forall x a m env.
    ( Typeable x
    , Typeable a
    , RValue m (E env m x) a
    --, SetEnv m env a
    ) 
    => LensyM' m env a -> E env m x -> A env m ()
  Print :: 
    ( RValue m (E env m a) b
    , ShowM m b
    )
    => E env m a -> A env m ()

{- class SetEnv (m :: Type -> Type) (env :: Type) (a :: Type) where
  setEnv :: Lensy env a -> a -> m b -> m b -}

class Execute (m :: Type -> Type) where
  type EnvType m :: Type
  execInstruction :: A (EnvType m) m a -> m (String, EnvType m)

instance 
  ( ADTContext m TypeRepMap
  , ShowM m (A TypeRepMap m ())
  ) => Execute m  where 
  type EnvType m = TypeRepMap
  execInstruction ((:=) @_ @x' x e) = do
    gamma <- ask
    --put =<< declare @(E TypeRepMap m x') (varNameM' x) gamma
    rve <- localM (declare @x' (varNameM' x) . const gamma) $ rvalue e
    gamma' <- insert (varNameM' x) rve =<< ask
    s <- showM (x := e)
    pure ("<ACK: " <> s <> " ===> OK>",gamma')
  execInstruction ((:=.) x e) = do
    rve <- rvalue e
    gamma <- ask
    gamma' <- insert (varNameM' x) rve gamma
    s <- showM (x :=. e)
    pure ("<ACK: " <> s <> " ===> OK>",gamma')
  execInstruction (Print e) = do
    rve <- rvalue e
    s  <- showM (Print e)
    s' <- showM rve
    gamma <- ask 
    pure ("<ACK: " <> s <> " ===> " <> s' <> ">", gamma)



execProgram :: forall t m a.
  ( Traversable t
  , Execute m, ADTContext m TypeRepMap
  , ShowM m (A TypeRepMap m a)
  )
  => t (A TypeRepMap m a) -> m ()
execProgram = void . foldM (\env a -> local (const env) $ f a) (empty)
  where
    f :: A TypeRepMap m a -> m TypeRepMap
    f a = do
      (s,env) <- execInstruction a
      liftIO . putStrLn <=< showM $ a 
      liftIO $ putStrLn s 
      pure env
      





  