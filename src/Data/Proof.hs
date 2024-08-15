{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE GADTs                 #-}
module Data.Proof where

import Data.Function.Singletons
import Data.Kind (Type, Constraint)

class (forall a. psi (f a)) => C psi f 
instance (forall a. psi (f a)) => C psi f

class (forall a. psi (f $ a)) => CS psi f 
instance (forall a. psi (f $ a)) => CS psi f

data Proof (c :: Constraint) where 
  Proof :: c => Proof c   