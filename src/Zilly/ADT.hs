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

{-|
Module      : Zilly.ADT
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
module Zilly.ADT where

import Zilly.Types
import Utilities.LensM
import Data.Kind (Type)



{-| Zilly expression Language. |-}
data  E (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) where
  Val     :: ValX ctx env m -> Int -> E ctx env m (Value Z)
  Var     :: VarX ctx env m a -> LensM m env (E ctx env m a) -> E ctx env m a
  Minus   :: MinusX ctx env m a b -> E ctx env m a -> E ctx env m b -> E ctx env m (Value Z)
  Less    :: LessX ctx env m a b -> E ctx env m a -> E ctx env m b -> E ctx env m (Value Z)
  If      :: IfX ctx env m x0 x1 x2 x3 -> E ctx env m x0 -> E ctx env m x1 -> E ctx env m x2 -> E ctx env m x3
  Lambda  :: LambdaX ctx env m a b -> LensM m env (E ctx env m a) -> E ctx env m b  -> E ctx env m (a ~> b)
  App     :: forall ctx f x b arg m env. AppX ctx env m f x arg b -> E ctx env m f -> E ctx env m x -> E ctx env m b
  Defer   :: DeferX ctx env m a -> E ctx env m a -> E ctx env m (Lazy a)
  Formula :: FormulaX ctx env m a -> LensM m env (E ctx env m a) -> E ctx env m (Lazy a)
  Exp     :: ExpX ctx env m a -> E ctx env m a

  Closure  :: ClosureX ctx env m a -> (E ctx env m a,env) -> E ctx env m a
  LambdaC  :: LambdaCX ctx env m a b -> (env, LensM m env (E ctx env m a), E ctx env m b) -> E ctx env m (a ~> b)
  ValueC   :: ValueCX ctx env m a -> (E ctx env m (Value a), env) -> E ctx env m (Value a)
  Subtyped :: SubtypedX ctx env m a b -> E ctx env m a -> E ctx env m b


type family ValX      (ctx :: Type) (env :: Type) (m :: Type -> Type) :: Type
type family ValueCX   (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types0):: Type
type family ClosureX  (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) :: Type
type family VarX      (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) :: Type
type family DeferX    (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) :: Type
type family FormulaX  (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) :: Type
type family ExpX      (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) :: Type
type family LambdaCX  (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) (b :: Types) :: Type
type family SubtypedX (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) (b :: Types) :: Type
type family MinusX    (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) (b :: Types) :: Type
type family LessX     (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) (b :: Types) :: Type
type family LambdaX   (ctx :: Type) (env :: Type) (m :: Type -> Type) (a :: Types) (b :: Types) :: Type
type family AppX      (ctx :: Type) (env :: Type) (m :: Type -> Type) (f :: Types ) (x :: Types ) (arg :: Types) (b :: Types ) :: Type
type family IfX       (ctx :: Type) (env :: Type) (m :: Type -> Type) (x0 :: Types) (x1 :: Types) (x2 :: Types ) (x3 :: Types) :: Type



  {- Closure  :: (E ctx env m a,env) -> E ctx env m a
  LambdaC  :: (env, LensM m env (E ctx env m a), E ctx env m b) -> E ctx env m (a ~> b)
  ValueC   :: (E ctx env m (Value a), env) -> E ctx env m (Value a)
  Subtyped :: E ctx env m a -> E ctx env m b
  DeferS   :: E ctx env m a -> E ctx env m (LazyS b) 
  FEval    :: E ctx env m a -> E ctx env m (Value b)  -}

-------------------
-- Proofs
-------------------

data Proof psi a where
 Proof :: psi a => Proof psi a

data Proof2 psi a b where
  Proof2 :: psi a b => Proof2 psi a b

data Proof' psi (m :: Type -> Type) where
  P' :: psi m => Proof' psi m

data ProofMR psi (a :: Type) (m :: Type -> Type) where
  PMR :: psi a m => ProofMR psi a m

data Proof2' psi (a :: Type -> Type) b where
  P2' :: psi a b => Proof2' psi a b

data ProofFA psi (m :: Type -> Type) (f :: Types -> Type) where
  PFA :: forall (a :: Types) psi m f. psi m (f a) => ProofFA psi m f

data ProofRV psi (f :: Types -> Type) (a :: Types) (m :: Type -> Type) where
  PRV :: psi f a m => ProofRV psi f a m

data ProofS psi (a :: Types) where
  PS :: psi a => ProofS psi a

-- UpperBound' (RValueT a) b ~ Just b
data ProofUB (a :: Types) (b :: Types) (c :: Types) where
  PUB :: UpperBound a b ~ Just c => ProofUB a b c

data ProofEQ psi (a :: Types) (b :: Types) where
  PEQ :: psi a b => ProofEQ psi a b

