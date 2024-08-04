{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
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
-- Module      :  Data.String.Singletons
-- Copyright   :  (C) 2017 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines and exports a promoted and singled version of the 'IsString'
-- type class from "Data.String".
----------------------------------------------------------------------------

module Data.String.Singletons (
  PIsString(..), SIsString(..),

  -- ** Defunctionalization symbols
  FromStringSym0, FromStringSym1
  ) where

import Data.Functor.Const
import Data.Functor.Const.Singletons
import Data.Functor.Identity
import Data.Functor.Identity.Singletons
import Data.Singletons.TH
import GHC.TypeLits (Symbol)
import GHC.TypeLits.Singletons ()   -- for the IsString instance!
import Data.Kind (Type)

type FromStringSym0 :: forall a_a2dsh. (~>) Symbol a_a2dsh
data FromStringSym0 :: (~>) Symbol a_a2dsh
  where
    FromStringSym0KindInference :: SameKind (Apply FromStringSym0 arg_a2dsE) (FromStringSym1 arg_a2dsE) =>
                                    FromStringSym0 a6989586621679538197
type instance Apply @Symbol @a_a2dsh FromStringSym0 a6989586621679538197 = FromString a6989586621679538197
instance SuppressUnusedWarnings FromStringSym0 where
  suppressUnusedWarnings = snd ((,) FromStringSym0KindInference ())
type FromStringSym1 :: forall a_a2dsh. Symbol -> a_a2dsh
type family FromStringSym1 @a_a2dsh (a6989586621679538197 :: Symbol) :: a_a2dsh where
  FromStringSym1 a6989586621679538197 = FromString a6989586621679538197
class PIsString a_a2dsh where
  type family FromString (arg_a2dsD :: Symbol) :: a_a2dsh
type FromString_6989586621679538199 :: forall a_a2dsi
                                              k_a2dsk
                                              (b_a2dsj :: k_a2dsk). Symbol
                                                                    -> Const a_a2dsi (b_a2dsj :: k_a2dsk)
type family FromString_6989586621679538199 @a_a2dsi @k_a2dsk @(b_a2dsj :: k_a2dsk) (a_a2dsJ :: Symbol) :: Const a_a2dsi (b_a2dsj :: k_a2dsk) where
  FromString_6989586621679538199 @a_a2dsi @k_a2dsk @b_a2dsj (x_a2dsM :: Symbol) = Apply ConstSym0 (Apply FromStringSym0 x_a2dsM)
instance PIsString (Const a_a2dsi (b_a2dsj :: k_a2dsk)) where
  type FromString a_a2dsG = FromString_6989586621679538199 a_a2dsG
type FromString_6989586621679538206 :: forall a_a2dsm. Symbol
                                                        -> Identity a_a2dsm
type family FromString_6989586621679538206 @a_a2dsm (a_a2dsQ :: Symbol) :: Identity a_a2dsm where
  FromString_6989586621679538206 @a_a2dsm (x_a2dsT :: Symbol) = Apply IdentitySym0 (Apply FromStringSym0 x_a2dsT)
instance PIsString (Identity a_a2dsm) where
  type FromString a_a2dsN = FromString_6989586621679538206 a_a2dsN
class SIsString a_a2dsh where
  sFromString ::
    (forall (t_a2dsU :: Symbol).
      Sing t_a2dsU -> Sing (FromString t_a2dsU :: a_a2dsh) :: Type)
instance SIsString a_a2dsi =>
          SIsString (Const a_a2dsi (b_a2dsj :: k_a2dsk)) where
  sFromString (sX :: Sing x_a2dsM)
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (singFun1 @FromStringSym0 sFromString) sX)
instance SIsString a_a2dsm => SIsString (Identity a_a2dsm) where
  sFromString (sX :: Sing x_a2dsT)
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (singFun1 @FromStringSym0 sFromString) sX)
instance SIsString a_a2dsh =>
          SingI (FromStringSym0 :: (~>) Symbol a_a2dsh) where
  sing = singFun1 @FromStringSym0 sFromString


-- PIsString instance
instance PIsString Symbol where
  type FromString a = a

-- SIsString instance
instance SIsString Symbol where
  sFromString x = x
