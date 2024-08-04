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
-- Module      :  Data.Singletons.Base.TypeError
-- Copyright   :  (C) 2023 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines a replacement for the promoted @Error@ function whose argument is
-- kind-polymorphic.
--
----------------------------------------------------------------------------
module Data.Singletons.Base.PolyError (PolyError) where

import Data.Singletons.TH
import Data.Kind (Type)

-- | Like @Error@ from "GHC.TypeLits.Singletons", but with an argument that is
-- generalized to be kind-polymorphic. This allows passing additional
-- information to the error besides raw @Symbol@s.
type PolyError :: a -> b
type family PolyError (arg :: a) :: b where {}
type PolyErrorSym0 :: forall (a_aX2 :: Type)
                                 (b_aX3 :: Type). (~>) a_aX2 b_aX3
data PolyErrorSym0 :: (~>) a_aX2 b_aX3
  where
    PolyErrorSym0KindInference :: SameKind (Apply PolyErrorSym0 arg_a2N0) (PolyErrorSym1 arg_a2N0) =>
                                  PolyErrorSym0 a6989586621679020519
type instance Apply @a_aX2 @b_aX3 PolyErrorSym0 a6989586621679020519 = PolyError a6989586621679020519
instance SuppressUnusedWarnings PolyErrorSym0 where
  suppressUnusedWarnings = snd ((,) PolyErrorSym0KindInference ())
type PolyErrorSym1 :: forall (a_aX2 :: Type) (b_aX3 :: Type). a_aX2
                                                              -> b_aX3
type family PolyErrorSym1 @(a_aX2 :: Type) @(b_aX3 :: Type) (a6989586621679020519 :: a_aX2) :: b_aX3 where
  PolyErrorSym1 a6989586621679020519 = PolyError a6989586621679020519

