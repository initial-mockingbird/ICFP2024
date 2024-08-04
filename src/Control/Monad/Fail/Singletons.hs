{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Fail.Singletons
-- Copyright   :  (C) 2019 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted and singled versions of the 'MonadFail' type class.
--
----------------------------------------------------------------------------

module Control.Monad.Fail.Singletons (
  PMonadFail(..), SMonadFail(..),

  -- * Defunctionalization symbols
  FailSym0, FailSym1
  ) where

import Control.Monad.Singletons.Internal
import Data.Kind
import Data.Singletons.Base.Instances
import Data.Singletons.TH

type FailSym0 :: forall (m_a1xQy :: Type -> Type)
                        a_a1xQz. (~>) [Char] (m_a1xQy a_a1xQz)
data FailSym0 :: (~>) [Char] (m_a1xQy a_a1xQz)
  where
    FailSym0KindInference :: SameKind (Apply FailSym0 arg_a1xQP) (FailSym1 arg_a1xQP) =>
                              FailSym0 a6989586621679378248
type instance Apply @[Char] @(m_a1xQy a_a1xQz) FailSym0 a6989586621679378248 = Fail a6989586621679378248
instance SuppressUnusedWarnings FailSym0 where
  suppressUnusedWarnings = snd ((,) FailSym0KindInference ())
type FailSym1 :: forall (m_a1xQy :: Type -> Type) a_a1xQz. [Char]
                                                            -> m_a1xQy a_a1xQz
type family FailSym1 @(m_a1xQy :: Type
                                  -> Type) @a_a1xQz (a6989586621679378248 :: [Char]) :: m_a1xQy a_a1xQz where
  FailSym1 a6989586621679378248 = Fail a6989586621679378248
type PMonadFail :: (Type -> Type) -> Constraint
class PMonadFail m_a1xQy where
  type family Fail (arg_a1xQO :: [Char]) :: m_a1xQy a_a1xQz
type Fail_6989586621679378250 :: forall a_a1xQz. [Char]
                                                  -> Maybe a_a1xQz
type family Fail_6989586621679378250 @a_a1xQz (a_a1xQU :: [Char]) :: Maybe a_a1xQz where
  Fail_6989586621679378250 @a_a1xQz _ = NothingSym0
instance PMonadFail Maybe where
  type Fail a_a1xQR = Fail_6989586621679378250 a_a1xQR
type Fail_6989586621679378256 :: forall a_a1xQz. [Char]
                                                  -> [a_a1xQz]
type family Fail_6989586621679378256 @a_a1xQz (a_a1xR0 :: [Char]) :: [a_a1xQz] where
  Fail_6989586621679378256 @a_a1xQz _ = NilSym0
instance PMonadFail [] where
  type Fail a_a1xQX = Fail_6989586621679378256 a_a1xQX
class SMonad m_a1xQy => SMonadFail m_a1xQy where
  sFail ::
    (forall (t_a1xR3 :: [Char]).
      Sing t_a1xR3 -> Sing (Fail t_a1xR3 :: m_a1xQy a_a1xQz) :: Type)
instance SMonadFail Maybe where
  sFail _ = SNothing
instance SMonadFail [] where
  sFail _ = SNil
type SMonadFail :: (Type -> Type) -> Constraint
instance SMonadFail m_a1xQy =>
          SingI (FailSym0 :: (~>) [Char] (m_a1xQy a_a1xQz)) where
  sing = singFun1 @FailSym0 sFail
