{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
module Zilly.Interpreter where


import Utilities.TypedMap
import Utilities.LensM
import Zilly.ADT
import Zilly.RValue
import Zilly.Types

import Control.Monad.Reader


import Control.Monad
import Control.Applicative (Alternative)


{- type Env = TypeRepMap BaseInterpreter ExprTag
newtype BaseInterpreter a = BI { runBI :: ReaderT Env IO a} 
  deriving newtype (Functor,Applicative, Alternative, Monad,MonadIO,MonadFail,MonadReader Env) -}

newtype TaggedInterpreter ctx a = TI { runTI :: ReaderT (Gamma (AssocCtxMonad ctx)) IO a} 
  deriving newtype 
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadIO
    , MonadFail
    )

instance (Gamma (AssocCtxMonad ctx) ~ TypeRepMap ctx) =>  MonadReader (TypeRepMap ctx) (TaggedInterpreter ctx) where
  ask = TI ask
  local f = TI . local f . runTI



{- 


run :: BaseInterpreter a -> IO a
run = flip runReaderT  env . runBI
  where
    {- !env = insert "x" (35  :: Value Int) 
        $ insert "y" (5000 :: Value Int)
        $ insert "z" (13 :: Value Int)
        $ empty -}
    env = empty

printProgram :: ShowM BaseInterpreter a => a -> IO ()
printProgram = putStrLn <=< run . showM 

printAndExec :: Traversable t => t (A (TypeRepMap BaseInterpreter ExprTag) BaseInterpreter a) -> IO ()
printAndExec = run . execProgram -}