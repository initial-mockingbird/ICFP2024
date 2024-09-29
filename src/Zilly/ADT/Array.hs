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
module Zilly.ADT.Array where

import Zilly.Types
import Data.Kind (Type)
import Data.Sequence

{-| Zilly expression Language. |-}
data  Array (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) where
  ArrayLiteral :: ArrayLiteralX f ctx a -> Seq (f ctx a) -> Array f ctx a
  ArrayExp     :: ArrayExpX f ctx a -> Array f ctx a 

type family ArrayLiteralX  (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family ArrayExpX      (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) :: Type
