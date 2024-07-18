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
import Zilly.Expressions
import Zilly.RValue
import Zilly.Types
import Zilly.Action
import Utilities.ShowM
import Control.Monad.Reader


import Control.Monad
import Control.Applicative (Alternative)

type Env = TypeRepMap BaseInterpreter ExprTag
newtype BaseInterpreter a = BI { runBI :: ReaderT Env IO a} 
  deriving newtype (Functor,Applicative, Alternative, Monad,MonadIO,MonadFail,MonadReader Env)


instance ShowM BaseInterpreter (E ExprTag Env BaseInterpreter a) where

  showsPrecM p = \case
    Val _ n -> showsPrecM p n
    ValueC _ (e,env) -> showStringM "<" <=< showStringM "," <=< showsPrecM p e <=< showStringM ">" -- showStringM "<" <=< showsPrecM 10 env <=< showStringM "," <=< showsPrecM p e <=< showStringM ">"
    Var _ x -> showsPrecM p . UT . varNameM $ x
    Minus _ a b -> showParenM (p > 6) $ showsPrecM 6 a <=< showStringM " - " <=< showsPrecM 7 b
    Less _ a b -> showParenM (p > 10) $ showsPrecM 4 a <=< showStringM " < " <=< showsPrecM 5 b
    If _ c t f -> showParenM (p > 10) $ showStringM "if " <=< showsM c <=< showStringM " then " <=< showsM t <=< showStringM " else " <=< showsM f
    Lambda _ x t -> showParenM (p > 9) $ showStringM "λ " <=< showsPrecM 10 (UT . varNameM $ x) <=< showStringM " -> " <=<  showsPrecM 0 t
    LambdaC _ (env,x,t) -> showParenM (p > 9) $  showStringM "λ " <=< showsPrecM 10 (UT . varNameM $ x) <=< showStringM " -> " <=< showsPrecM 10 t -- -> showParenM (p > 9) $ showsPrecM 10 env <=<  showStringM "λ " <=< showsPrecM 10 (UT . varNameM $ x) <=< showStringM " -> " <=< showsPrecM 10 t
 
    App _ f a -> showParenM (p > 10) $ showsPrecM 10 f <=< showCharM ' ' <=< showsPrecM 11 a
    Defer _ v -> showStringM "'" <=< showsPrecM 11 v <=< showStringM "'"
    Closure _ (e,env) -> showsPrecM 10 e -- showCharM '<' <=< showsPrecM 10 e <=< showStringM  ", " <=< showsPrecM 10 env <=< showCharM '>'
    Formula _ e -> showStringM "Formula " <=< (showsPrecM 11 . UT . varNameM) e
    -- FEval  _ -> undefined
    -- DeferS _ -> undefined
    Subtyped _ e -> showStringM "Subtyped " <=< showsPrecM 10 e
    Exp _ -> showStringM "no additional extensions"
    
instance ShowM BaseInterpreter (A Env BaseInterpreter a) where 
  showsPrecM p = \case
    (:=) @ltype @_ x e
      -> showStringM (withShow @ltype)
      <=< showCharM ' '
      <=< (showsPrecM p . UT . varNameM) x
      <=< showStringM " := "
      <=< showsM e
    (:=.) x e -> (showsPrecM p . UT . varNameM @BaseInterpreter ) x <=< showStringM " := " <=< showsM e
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

printAndExec :: Traversable t => t (A (TypeRepMap BaseInterpreter ExprTag) BaseInterpreter a) -> IO ()
printAndExec = run . execProgram