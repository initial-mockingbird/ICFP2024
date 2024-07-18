{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-|
Module      : Zilly Contexts
Description : Useful Contexts for Expressions, Actions, and the like
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Zilly.Contexts where


import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Reader 
import ShowM
import Zilly.Types
import Data.Kind (Type)



type EContext m env =
  ( MonadIO m
  --, Interpreter m env
  , MonadReader env m
  , Alternative m
  )

type ShowMContext (f :: Type -> (Type -> Type) -> Types -> Type) m env =
  ( ShowM m env
  , forall a. ShowM m (f env m a)
  )


