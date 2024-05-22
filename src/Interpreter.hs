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
module Interpreter where

import ADT
import TypedMap
import Control.Monad.Reader
import Control.Lens.Lens
import Control.Lens.Getter
import Control.Lens.Setter
import Data.Coerce (coerce)
import Data.Functor.Identity
import Lensy
import Control.Concurrent.MVar
import Control.Monad
import Data.Typeable hiding (cast)

import Data.Foldable
import Control.Exception (catch, SomeException)
import ShowM
import Action
import Control.Monad.State 
import Control.Applicative (Alternative)

type Env = TypeRepMap
newtype BaseInterpreter a = BI { runBI :: ReaderT Env IO a} 
  deriving newtype (Functor,Applicative, Alternative, Monad,MonadIO,MonadFail,MonadReader Env)


instance ShowM BaseInterpreter (E Env BaseInterpreter a) where

  showsPrecM p = \case
    Val n -> showsPrecM p n
    ValueC (e,env) -> showStringM "<" <=< showsPrecM 10 env <=< showStringM "," <=< showsPrecM p e <=< showStringM ">"
    Var x -> showsPrecM p . UT . varNameM' $ x
    Minus a b -> showParenM (p > 6) $ showsPrecM 6 a <=< showStringM " - " <=< showsPrecM 7 b
    Less a b -> showParenM (p > 10) $ showsPrecM 4 a <=< showStringM " < " <=< showsPrecM 5 b
    If c t f -> showParenM (p > 10) $ showStringM "if " <=< showsM c <=< showStringM " then " <=< showsM t <=< showStringM " else " <=< showsM f
    Lambda x t -> showParenM (p > 9) $ showStringM "λ " <=< showsPrecM 10 (UT . varNameM' $ x) <=< showStringM " -> " <=<  showsPrecM 0 t
    LambdaC _ (env,x,t) -> showParenM (p > 9) $ showsPrecM 10 env <=<  showStringM "λ " <=< showsPrecM 10 (UT . varNameM' $ x) <=< showStringM " -> " <=< showsPrecM 10 t
 
    App f a -> showParenM (p > 10) $ showsPrecM 10 f <=< showCharM ' ' <=< showsPrecM 11 a
    Defer v -> showStringM "'" <=< showsPrecM 11 v <=< showStringM "'"
    Closure (e,env) -> showCharM '<' <=< showsPrecM 10 e <=< showStringM  ", " <=< showsPrecM 10 env <=< showCharM '>'

instance ShowM BaseInterpreter (A Env BaseInterpreter a) where 
  showsPrecM p = \case
    (:=) @ltype @_ x e  -> showStringM (show . typeRep $ Proxy @ltype) <=< showCharM ' ' <=< (showsPrecM p . UT . varNameM') x <=< showStringM " := " <=< showsM e
    (:=.) x e -> (showsPrecM p . UT . varNameM') x <=< showStringM " := " <=< showsM e
    Print e   -> showStringM "print " <=< showsPrecM 10 e

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

printAndExec :: Traversable t => t (A TypeRepMap BaseInterpreter a) -> IO ()
printAndExec = run . execProgram