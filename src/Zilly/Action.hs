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
import Zilly.Upcast
import Zilly.Interpreter
import Utilities.TypedMap
import Utilities.ShowM
import Control.Monad.Reader

import Data.Kind (Type)
import Control.Monad.IO.Class
import Control.Monad
import Prelude.Singletons (SingI)
import Debug.Trace (trace)
import Control.Applicative (Alternative)
import Data.Singletons (SingI(..))


data ActionTag

type family AssocActionTag (ctx :: Type) :: Type
type instance AssocActionTag ActionTag = ExprTag


infix 0 :=
infix 0 :=.
data A ctx r where
  (:=) :: forall {m} {env} {ctx} actx (var :: Types) (e :: Types) .
    ( AssocActionTag actx ~ ctx
    , AssocCtxMonad ctx ~ m
    , Gamma m ~ env
    , SingI var
    , SingI e
    , RValue ctx var
    , RValue ctx e
    , UpperBound (RValueT var) (RValueT  e) ~ Just (RValueT var)
    ) 
    =>  LensM m (E ctx var) -> E ctx  e -> A actx '()
  (:=.) :: forall {m} {env} {ctx} actx (var :: Types) (e :: Types) .
    ( AssocActionTag actx ~ ctx
    , AssocCtxMonad ctx ~ m
    , Gamma m ~ env
    , SingI var
    , SingI e
    , RValue ctx var
    , RValue ctx e
    , UpperBound (RValueT var) (RValueT  e) ~ Just (RValueT var)
    ) 
    =>  LensM m (E ctx var) -> E ctx  e -> A actx '()
  Print :: forall {ctx} actx a.
    ( AssocActionTag actx ~ ctx
    , SingI a
    , RValue ctx a
    )
    => E ctx a -> A actx '()
  OfExpr :: forall {ctx} actx a.
    ( AssocActionTag actx ~ ctx
    , SingI a
    , RValue ctx a
    )
    => E ctx a -> A actx '()
  

{- class SetEnv (m :: Type -> Type) (env :: Type) (a :: Type) where
  setEnv :: Lensy env a -> a -> m b -> m b -}

class Execute actx where
  execInstruction :: forall {ctx} {m} {env} a. 
    ( AssocActionTag actx ~ ctx
    , AssocCtxMonad ctx ~ m
    , Gamma m ~ env
    ) => A actx a -> m (A actx a, env)

instance  Execute ActionTag  where 
  execInstruction ((:=) @_ @var @e var e) 
    = withSingIRType @var
    $ withSingIRType @e
    $ ubIsCommutative @(RValueT var) @(RValueT e)
    $ do
    gamma  <- declare @(RValueT var) @ExprTag (varNameM var) =<< ask
    rve    <- local (const gamma) $ rvalue e
    gamma' <- case upcast @ExprTag @(RValueT e) @(RValueT  var) UpcastE rve of
      SameTypeUB  rve'     -> insert @(RValueT var) @ExprTag (varNameM var) rve' gamma
      RightUB     rve'     -> insert @(RValueT var) (varNameM var) rve' gamma
      LeftUB      rve'     -> insert @(RValueT var) (varNameM var) rve' gamma
      SomethingElseUB rve' -> insert @(RValueT var) (varNameM var) rve' gamma
    pure (var := e,gamma')
  execInstruction ((:=.) @_ @var @e var e) 
    = withSingIRType @var 
    $ withSingIRType @e 
    $ ubIsCommutative @(RValueT var) @(RValueT e)
    $ do
    gamma  <- ask
    rve    <- local (const gamma) $ rvalue e
    gamma' <- case upcast @ExprTag @(RValueT  e) @(RValueT  var) UpcastE rve of
      SameTypeUB  rve'     -> insert @(RValueT  var) @ExprTag (varNameM var) rve' gamma
      RightUB     rve'     -> insert @(RValueT  var) (varNameM var) rve' gamma
      LeftUB      rve'     -> insert @(RValueT  var) (varNameM var) rve' gamma
      SomethingElseUB rve' -> insert @(RValueT  var) (varNameM var) rve' gamma
    pure (var :=. e,gamma')
  execInstruction (OfExpr @_ @e e) 
    = withSingIRType @e
    $ withRVType @(AssocActionTag ActionTag) (sing @(RValueT e))
    $ do
    rve <- rvalue e
    gamma <- ask 
    pure (OfExpr rve, gamma)
  execInstruction (Print @_ @e e) 
    = withSingIRType @e 
    $ withRVType @(AssocActionTag ActionTag) (sing @(RValueT e))
    $ do
    rve <- rvalue e
    gamma <- ask 
    pure (Print rve, gamma)


{-
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
      pure env -}
      

  