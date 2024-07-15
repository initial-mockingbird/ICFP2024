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

module Action2 where

import Lensy2
import ADT2
import Data.Kind (Type)
import Control.Monad.IO.Class
import Control.Monad.Reader
import TypedMap2
import ShowM
import Control.Monad
import Prelude.Singletons (SingI)
import Debug.Trace (trace)

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
    , RValue var
    , RValue e
    , UpperBound' (RValueT var) (RValueT e) ~ Just (RValueT var)
    ) 
    =>  LensyM' m env (E env m var) -> E env m e -> A env m '()
  (:=.) :: forall (x :: Types) m env.
    ( SingI x
    , RValue x
    ) 
    => LensyM' m env (E env m x) -> E env m x -> A env m '()
  Print :: 
    ( ShowMContextE m env
    , SingI a
    , RValue a
    )
    => E env m a -> A env m '()

{- class SetEnv (m :: Type -> Type) (env :: Type) (a :: Type) where
  setEnv :: Lensy env a -> a -> m b -> m b -}

class Execute (m :: Type -> Type) where
  type EnvType m :: Type
  execInstruction :: A (EnvType m) m a -> m (String, EnvType m)

instance 
  ( ADTContext m (TypeRepMap m)
  , ShowMContext m (TypeRepMap m)
  ) => Execute m  where 
  type EnvType m = (TypeRepMap m)
  execInstruction ((:=) @var @e var e) 
    = withSingIRType @var
    $ withSingIRType @e
    $ upperBoundIsCommutative @(RValueT var) @(RValueT e)
    $ do
    gamma  <- declare @(RValueT var) (varNameM' var) =<< ask
    rve    <- local (const gamma) $ rvalue e
    gamma' <- case upcast'' @(RValueT e) @(RValueT var) rve of
      SameTypeUB  rve'     -> insert @(RValueT var) (varNameM' var) rve' gamma
      RightUB     rve'     -> insert @(RValueT var) (varNameM' var) rve' gamma
      LeftUB      rve'     -> insert @(RValueT var) (varNameM' var) rve' gamma
      SomethingElseUB rve' -> insert @(RValueT var) (varNameM' var) rve' gamma
      -- NonExistentUB -> error "impossible case"
    s <- showM (var := e)
    pure ("<ACK: " <> s <> " ===> OK>",gamma')
  execInstruction ((:=.) @x x e) 
    = withSingIRType @x 
    $ do
    trace "INSIDE ASSIGN" pure ()
    rve <- rvalue e
    gamma <- ask
    gamma' <- insert (varNameM' x) rve gamma
    s <- showM (x :=. e)
    pure ("<ACK: " <> s <> " ===> OK>",gamma')
  execInstruction (Print @_ @_ @e e) = withSingIRType @e $ do
    rve <- rvalue e
    s  <- showM (Print e)
    s' <- showM rve
    gamma <- ask 
    pure ("<ACK: " <> s <> " ===> " <> s' <> ">", gamma) 



execProgram :: forall t m a.
  ( Traversable t
  , Execute m, ADTContext m (TypeRepMap m)
  , ShowM m (A (TypeRepMap m) m a)
  )
  => t (A (TypeRepMap m) m a) -> m ()
execProgram = void . foldM (\env a -> local (const env) $ f a) empty
  where
    f :: A (TypeRepMap m) m a -> m (TypeRepMap m)
    f a = do
      (s,env) <- execInstruction a
      liftIO . putStrLn <=< showM $ a 
      liftIO $ putStrLn s 
      pure env
      

  