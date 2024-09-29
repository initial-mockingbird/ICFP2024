{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
Module      : Zilly.ADT.Expression
Description : Main Expression Tree a la Trees that grow for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Check
@@
@article{najd2016trees,
  title={Trees that grow},
  author={Najd, Shayan and Jones, Simon Peyton},
  journal={arXiv preprint arXiv:1610.04799},
  year={2016}
}
@@
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/trees-that-grow.pdf

-}
module Zilly.ADT.ExpressionPlus where

import Zilly.Types
import Utilities.LensM
import Data.Kind (Type, Constraint)
import Data.Function.Singletons
import Data.Coerce 
import Data.Singletons (SingI)
type family AssocCtxMonad (ctx :: Type) :: (Type -> Type)



{-| Zilly expression Language. |-}
data  E (ctx :: Type) (a :: Types) where
  Val      :: (BasicType a)       => ValX ctx -> HashType a -> E ctx (Value a)
  Var      :: VarX ctx a          -> LensM (AssocCtxMonad ctx) (E ctx a) -> E ctx a
  If       :: IfX ctx x0 x1 x2 x3 -> E ctx x0 -> E ctx x1 -> E ctx x2 -> E ctx x3
  Lambda   :: LambdaX ctx a b     -> LensM (AssocCtxMonad ctx) (E ctx a) -> E ctx b  -> E ctx (a ~> b)
  Defer    :: DeferX ctx a        -> E ctx a -> E ctx (Lazy a)
  Formula  :: FormulaX ctx a      -> LensM (AssocCtxMonad ctx) (E ctx a) -> E ctx (Lazy a)
  Exp      :: ExpX ctx a          -> E ctx a
  Closure  :: ClosureX ctx a      -> (E ctx a,Gamma (AssocCtxMonad ctx)) -> E ctx a
  LambdaC  :: LambdaCX ctx a b    -> (Gamma (AssocCtxMonad ctx), LensM (AssocCtxMonad ctx) (E ctx a), E ctx b) -> E ctx (a ~> b)
  ValueC   :: ValueCX ctx a       -> (E ctx (Value a), Gamma (AssocCtxMonad ctx)) -> E ctx (Value a)
  Subtyped :: SubtypedX ctx a b   -> E ctx a -> E ctx b
  App     :: forall ctx f x b arg. AppX ctx f x arg b -> E ctx f -> E ctx x -> E ctx b
  

type family ValX      (ctx :: Type) :: Type
type family ValueCX   (ctx :: Type) (a :: Types0):: Type
type family ClosureX  (ctx :: Type) (a :: Types) :: Type
type family VarX      (ctx :: Type) (a :: Types) :: Type
type family DeferX    (ctx :: Type) (a :: Types) :: Type
type family FormulaX  (ctx :: Type) (a :: Types) :: Type
type family ExpX      (ctx :: Type) (a :: Types) :: Type
type family LambdaCX  (ctx :: Type) (a :: Types) (b :: Types) :: Type
type family SubtypedX (ctx :: Type) (a :: Types) (b :: Types) :: Type
type family LambdaX   (ctx :: Type) (a :: Types) (b :: Types) :: Type
type family AppX      (ctx :: Type) (f :: Types ) (x :: Types ) (arg :: Types) (b :: Types ) :: Type
type family IfX       (ctx :: Type) (x0 :: Types) (x1 :: Types) (x2 :: Types ) (x3 :: Types) :: Type


-------------------
-- Proofs
-------------------

class (forall a. psi (f a)) => C psi f 
instance (forall a. psi (f a)) => C psi f

class (forall a. psi (f $ a)) => CS psi f 
instance (forall a. psi (f $ a)) => CS psi f

