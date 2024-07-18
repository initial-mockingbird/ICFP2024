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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Zilly.Action where

import Utilities.LensM
import Zilly.ADT
import Zilly.Expressions
import Zilly.Types
import Zilly.RValue
import Utilities.TypedMap
import Utilities.ShowM
import Control.Monad.Reader

import Data.Kind (Type)
import Control.Monad.IO.Class
import Control.Monad
import Prelude.Singletons (SingI)
import Debug.Trace (trace)
import Control.Applicative (Alternative)

type ShowMContext m env =
  ( ShowMContextE m env
  , forall a. ShowM m (A env m a)
  )



infix 0 :=
infix 0 :=.
data A (env :: Type) (m :: Type -> Type) r where
  (:=) :: forall (var :: Types) (e :: Types) m env.
    ( SingI var
    , SingI e
    , RValue (E ExprTag env m) var m
    , RValue (E ExprTag env m) e m
    , UpperBound (RValueT (E ExprTag env m) var) (RValueT (E ExprTag env m) e) ~ Just (RValueT (E ExprTag env m) var)
    ) 
    =>  LensM m env (E ExprTag env m var) -> E ExprTag env m e -> A env m '()
  (:=.) :: forall (var :: Types) (e :: Types) m env.
    ( SingI var
    , SingI e
    , RValue (E ExprTag env m) var m
    , RValue (E ExprTag env m) e m
    , UpperBound (RValueT (E ExprTag env m) var) (RValueT (E ExprTag env m) e) ~ Just (RValueT (E ExprTag env m) var)
    ) 
    => LensM m env (E ExprTag env m var) -> E ExprTag env m e -> A env m '()
  Print :: 
    ( ShowMContextE m env
    , SingI a
    , RValue (E ExprTag env m) a m
    )
    => E ExprTag env m a -> A env m '()

{- class SetEnv (m :: Type -> Type) (env :: Type) (a :: Type) where
  setEnv :: Lensy env a -> a -> m b -> m b -}

class Execute (m :: Type -> Type) where
  type EnvType m :: Type
  execInstruction :: A (EnvType m) m a -> m (String, EnvType m)

instance 
  ( MonadIO m
  , MonadReader (TypeRepMap m ExprTag) m
  , Alternative m
  , ShowM m (TypeRepMap m ExprTag)
  , forall a. ShowM m (A (TypeRepMap m ExprTag) m a)
  , forall a. ShowM m (E ExprTag (TypeRepMap m ExprTag) m a)
  ) => Execute m  where 
  type EnvType m = (TypeRepMap m ExprTag)
  execInstruction ((:=) @var @e var e) 
    = withSingIRType @var @(E ExprTag (EnvType m) m)
    $ withSingIRType @e @(E ExprTag (EnvType m) m)
    $ ubIsCommutative @(RValueT (E ExprTag (EnvType m) m) var) @(RValueT (E ExprTag (EnvType m) m) e)
    $ do
    gamma  <- declare @(RValueT (E ExprTag (EnvType m) m) var) @m @ExprTag (varNameM var) =<< ask
    rve    <- local (const gamma) $ rvalue e
    gamma' <- case upcast @(RValueT (E ExprTag (EnvType m) m) e) @(RValueT (E ExprTag (EnvType m) m) var) @(EnvType m) @m rve of
      SameTypeUB  rve'     -> insert @(RValueT (E ExprTag (EnvType m) m) var) @m @ExprTag (varNameM var) rve' gamma
      RightUB     rve'     -> insert @(RValueT (E ExprTag (EnvType m) m) var) (varNameM var) rve' gamma
      LeftUB      rve'     -> insert @(RValueT (E ExprTag (EnvType m) m) var) (varNameM var) rve' gamma
      SomethingElseUB rve' -> insert @(RValueT (E ExprTag (EnvType m) m) var) (varNameM var) rve' gamma

    s <- showM (var := e)
    pure ("<ACK: " <> s <> " ===> OK>",gamma')
  execInstruction ((:=.) @var @e var e) 
    = withSingIRType @var @(E ExprTag (EnvType m) m)
    $ withSingIRType @e @(E ExprTag (EnvType m) m)
    $ ubIsCommutative @(RValueT (E ExprTag (EnvType m) m) var) @(RValueT (E ExprTag (EnvType m) m) e)
    $ do
    gamma  <- ask
    rve    <- local (const gamma) $ rvalue e
    gamma' <- case upcast @(RValueT (E ExprTag (EnvType m) m) e) @(RValueT (E ExprTag (EnvType m) m) var) @(EnvType m) @m rve of
      SameTypeUB  rve'     -> insert @(RValueT (E ExprTag (EnvType m) m) var) @m @ExprTag (varNameM var) rve' gamma
      RightUB     rve'     -> insert @(RValueT (E ExprTag (EnvType m) m) var) (varNameM var) rve' gamma
      LeftUB      rve'     -> insert @(RValueT (E ExprTag (EnvType m) m) var) (varNameM var) rve' gamma
      SomethingElseUB rve' -> insert @(RValueT (E ExprTag (EnvType m) m) var) (varNameM var) rve' gamma

    s <- showM (var := e)
    pure ("<ACK: " <> s <> " ===> OK>",gamma')
  execInstruction (Print @_ @_ @e e) = withSingIRType @e $ do
    rve <- rvalue e
    s  <- showM (Print e)
    s' <- showM rve
    gamma <- ask 
    pure ("<ACK: " <> s <> " ===> " <> s' <> ">", gamma) 



execProgram :: forall t m a.
  ( Traversable t
  , Execute m
  , MonadIO m
  , Alternative m
  , ShowM m (A (TypeRepMap m ExprTag) m a)
  , MonadReader (TypeRepMap m ExprTag) m
  )
  => t (A (TypeRepMap m ExprTag) m a) -> m ()
execProgram = void . foldM (\env a -> local (const env) $ f a) empty
  where
    f :: A (TypeRepMap m ExprTag) m a -> m (TypeRepMap m ExprTag)
    f a = do
      (s,env) <- execInstruction a
      liftIO . putStrLn <=< showM $ a 
      liftIO $ putStrLn s 
      pure env
      

  