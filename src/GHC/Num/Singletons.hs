{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NoStarIsType #-}

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
-- Module      :  GHC.Num.Singletons
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines and exports promoted and singleton versions of definitions from
-- "GHC.Num".
--
-- Be warned that some of the associated type families in the 'PNum' class
-- (@(+)@, @(-)@, and @(*)@) clash with their counterparts for 'Natural' in the
-- "GHC.TypeLits" module.
----------------------------------------------------------------------------

module GHC.Num.Singletons (
  PNum(..), SNum(..), Subtract, sSubtract,

  -- ** Defunctionalization symbols
  type (+@#@$), type (+@#@$$), type (+@#@$$$),
  type (-@#@$), type (-@#@$$), type (-@#@$$$),
  type (*@#@$), type (*@#@$$), type (*@#@$$$),
  NegateSym0, NegateSym1,
  AbsSym0, AbsSym1,
  SignumSym0, SignumSym1,
  FromIntegerSym0, FromIntegerSym1,
  SubtractSym0, SubtractSym1, SubtractSym2
  ) where

import Data.Ord (Down(..))
import Data.Ord.Singletons
import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.TH
import GHC.TypeLits.Singletons.Internal
import qualified GHC.TypeNats as TN
import Unsafe.Coerce
import Data.Kind (Type)

type SubtractSym0 :: (~>) a_a1IHV ((~>) a_a1IHV a_a1IHV)
data SubtractSym0 :: (~>) a_a1IHV ((~>) a_a1IHV a_a1IHV)
  where
    SubtractSym0KindInference :: SameKind (Apply SubtractSym0 arg_a1IIr) (SubtractSym1 arg_a1IIr) =>
                                  SubtractSym0 a6989586621679420012
type instance Apply @a_a1IHV @((~>) a_a1IHV a_a1IHV) SubtractSym0 a6989586621679420012 = SubtractSym1 a6989586621679420012
instance SuppressUnusedWarnings SubtractSym0 where
  suppressUnusedWarnings = snd ((,) SubtractSym0KindInference ())
type SubtractSym1 :: a_a1IHV -> (~>) a_a1IHV a_a1IHV
data SubtractSym1 (a6989586621679420012 :: a_a1IHV) :: (~>) a_a1IHV a_a1IHV
  where
    SubtractSym1KindInference :: SameKind (Apply (SubtractSym1 a6989586621679420012) arg_a1IIr) (SubtractSym2 a6989586621679420012 arg_a1IIr) =>
                                  SubtractSym1 a6989586621679420012 a6989586621679420013
type instance Apply @a_a1IHV @a_a1IHV (SubtractSym1 a6989586621679420012) a6989586621679420013 = Subtract a6989586621679420012 a6989586621679420013
instance SuppressUnusedWarnings (SubtractSym1 a6989586621679420012) where
  suppressUnusedWarnings = snd ((,) SubtractSym1KindInference ())
type SubtractSym2 :: a_a1IHV -> a_a1IHV -> a_a1IHV
type family SubtractSym2 @a_a1IHV (a6989586621679420012 :: a_a1IHV) (a6989586621679420013 :: a_a1IHV) :: a_a1IHV where
  SubtractSym2 a6989586621679420012 a6989586621679420013 = Subtract a6989586621679420012 a6989586621679420013
type Subtract :: a_a1IHV -> a_a1IHV -> a_a1IHV
type family Subtract @a_a1IHV (a_a1IIp :: a_a1IHV) (a_a1IIq :: a_a1IHV) :: a_a1IHV where
  Subtract x_a1IIu y_a1IIv = Apply (Apply (-@#@$) y_a1IIv) x_a1IIu
type (+@#@$) :: forall a_a1II5. (~>) a_a1II5 ((~>) a_a1II5 a_a1II5)
data (+@#@$) :: (~>) a_a1II5 ((~>) a_a1II5 a_a1II5)
  where
    (:+@#@$###) :: SameKind (Apply (+@#@$) arg_a1IIy) ((+@#@$$) arg_a1IIy) =>
                    (+@#@$) a6989586621679420019
type instance Apply @a_a1II5 @((~>) a_a1II5 a_a1II5) (+@#@$) a6989586621679420019 = (+@#@$$) a6989586621679420019
instance SuppressUnusedWarnings (+@#@$) where
  suppressUnusedWarnings = snd ((,) (:+@#@$###) ())
infixl 6 +@#@$
type (+@#@$$) :: forall a_a1II5. a_a1II5 -> (~>) a_a1II5 a_a1II5
data (+@#@$$) (a6989586621679420019 :: a_a1II5) :: (~>) a_a1II5 a_a1II5
  where
    (:+@#@$$###) :: SameKind (Apply ((+@#@$$) a6989586621679420019) arg_a1IIy) ((+@#@$$$) a6989586621679420019 arg_a1IIy) =>
                    (+@#@$$) a6989586621679420019 a6989586621679420020
type instance Apply @a_a1II5 @a_a1II5 ((+@#@$$) a6989586621679420019) a6989586621679420020 = (+) a6989586621679420019 a6989586621679420020
instance SuppressUnusedWarnings ((+@#@$$) a6989586621679420019) where
  suppressUnusedWarnings = snd ((,) (:+@#@$$###) ())
infixl 6 +@#@$$
type (+@#@$$$) :: forall a_a1II5. a_a1II5 -> a_a1II5 -> a_a1II5
type family (+@#@$$$) @a_a1II5 (a6989586621679420019 :: a_a1II5) (a6989586621679420020 :: a_a1II5) :: a_a1II5 where
  (+@#@$$$) a6989586621679420019 a6989586621679420020 = (+) a6989586621679420019 a6989586621679420020
infixl 6 +@#@$$$
type (-@#@$) :: forall a_a1II5. (~>) a_a1II5 ((~>) a_a1II5 a_a1II5)
data (-@#@$) :: (~>) a_a1II5 ((~>) a_a1II5 a_a1II5)
  where
    (:-@#@$###) :: SameKind (Apply (-@#@$) arg_a1IID) ((-@#@$$) arg_a1IID) =>
                    (-@#@$) a6989586621679420024
type instance Apply @a_a1II5 @((~>) a_a1II5 a_a1II5) (-@#@$) a6989586621679420024 = (-@#@$$) a6989586621679420024
instance SuppressUnusedWarnings (-@#@$) where
  suppressUnusedWarnings = snd ((,) (:-@#@$###) ())
infixl 6 -@#@$
type (-@#@$$) :: forall a_a1II5. a_a1II5 -> (~>) a_a1II5 a_a1II5
data (-@#@$$) (a6989586621679420024 :: a_a1II5) :: (~>) a_a1II5 a_a1II5
  where
    (:-@#@$$###) :: SameKind (Apply ((-@#@$$) a6989586621679420024) arg_a1IID) ((-@#@$$$) a6989586621679420024 arg_a1IID) =>
                    (-@#@$$) a6989586621679420024 a6989586621679420025
type instance Apply @a_a1II5 @a_a1II5 ((-@#@$$) a6989586621679420024) a6989586621679420025 = (-) a6989586621679420024 a6989586621679420025
instance SuppressUnusedWarnings ((-@#@$$) a6989586621679420024) where
  suppressUnusedWarnings = snd ((,) (:-@#@$$###) ())
infixl 6 -@#@$$
type (-@#@$$$) :: forall a_a1II5. a_a1II5 -> a_a1II5 -> a_a1II5
type family (-@#@$$$) @a_a1II5 (a6989586621679420024 :: a_a1II5) (a6989586621679420025 :: a_a1II5) :: a_a1II5 where
  (-@#@$$$) a6989586621679420024 a6989586621679420025 = (-) a6989586621679420024 a6989586621679420025
infixl 6 -@#@$$$
type (*@#@$) :: forall a_a1II5. (~>) a_a1II5 ((~>) a_a1II5 a_a1II5)
data (*@#@$) :: (~>) a_a1II5 ((~>) a_a1II5 a_a1II5)
  where
    (:*@#@$###) :: SameKind (Apply (*@#@$) arg_a1III) ((*@#@$$) arg_a1III) =>
                    (*@#@$) a6989586621679420029
type instance Apply @a_a1II5 @((~>) a_a1II5 a_a1II5) (*@#@$) a6989586621679420029 = (*@#@$$) a6989586621679420029
instance SuppressUnusedWarnings (*@#@$) where
  suppressUnusedWarnings = snd ((,) (:*@#@$###) ())
infixl 7 *@#@$
type (*@#@$$) :: forall a_a1II5. a_a1II5 -> (~>) a_a1II5 a_a1II5
data (*@#@$$) (a6989586621679420029 :: a_a1II5) :: (~>) a_a1II5 a_a1II5
  where
    (:*@#@$$###) :: SameKind (Apply ((*@#@$$) a6989586621679420029) arg_a1III) ((*@#@$$$) a6989586621679420029 arg_a1III) =>
                    (*@#@$$) a6989586621679420029 a6989586621679420030
type instance Apply @a_a1II5 @a_a1II5 ((*@#@$$) a6989586621679420029) a6989586621679420030 = (*) a6989586621679420029 a6989586621679420030
instance SuppressUnusedWarnings ((*@#@$$) a6989586621679420029) where
  suppressUnusedWarnings = snd ((,) (:*@#@$$###) ())
infixl 7 *@#@$$
type (*@#@$$$) :: forall a_a1II5. a_a1II5 -> a_a1II5 -> a_a1II5
type family (*@#@$$$) @a_a1II5 (a6989586621679420029 :: a_a1II5) (a6989586621679420030 :: a_a1II5) :: a_a1II5 where
  (*@#@$$$) a6989586621679420029 a6989586621679420030 = (*) a6989586621679420029 a6989586621679420030
infixl 7 *@#@$$$
type NegateSym0 :: forall a_a1II5. (~>) a_a1II5 a_a1II5
data NegateSym0 :: (~>) a_a1II5 a_a1II5
  where
    NegateSym0KindInference :: SameKind (Apply NegateSym0 arg_a1IIM) (NegateSym1 arg_a1IIM) =>
                                NegateSym0 a6989586621679420033
type instance Apply @a_a1II5 @a_a1II5 NegateSym0 a6989586621679420033 = Negate a6989586621679420033
instance SuppressUnusedWarnings NegateSym0 where
  suppressUnusedWarnings = snd ((,) NegateSym0KindInference ())
type NegateSym1 :: forall a_a1II5. a_a1II5 -> a_a1II5
type family NegateSym1 @a_a1II5 (a6989586621679420033 :: a_a1II5) :: a_a1II5 where
  NegateSym1 a6989586621679420033 = Negate a6989586621679420033
type AbsSym0 :: forall a_a1II5. (~>) a_a1II5 a_a1II5
data AbsSym0 :: (~>) a_a1II5 a_a1II5
  where
    AbsSym0KindInference :: SameKind (Apply AbsSym0 arg_a1IIP) (AbsSym1 arg_a1IIP) =>
                            AbsSym0 a6989586621679420036
type instance Apply @a_a1II5 @a_a1II5 AbsSym0 a6989586621679420036 = Abs a6989586621679420036
instance SuppressUnusedWarnings AbsSym0 where
  suppressUnusedWarnings = snd ((,) AbsSym0KindInference ())
type AbsSym1 :: forall a_a1II5. a_a1II5 -> a_a1II5
type family AbsSym1 @a_a1II5 (a6989586621679420036 :: a_a1II5) :: a_a1II5 where
  AbsSym1 a6989586621679420036 = Abs a6989586621679420036
type SignumSym0 :: forall a_a1II5. (~>) a_a1II5 a_a1II5
data SignumSym0 :: (~>) a_a1II5 a_a1II5
  where
    SignumSym0KindInference :: SameKind (Apply SignumSym0 arg_a1IIS) (SignumSym1 arg_a1IIS) =>
                                SignumSym0 a6989586621679420039
type instance Apply @a_a1II5 @a_a1II5 SignumSym0 a6989586621679420039 = Signum a6989586621679420039
instance SuppressUnusedWarnings SignumSym0 where
  suppressUnusedWarnings = snd ((,) SignumSym0KindInference ())
type SignumSym1 :: forall a_a1II5. a_a1II5 -> a_a1II5
type family SignumSym1 @a_a1II5 (a6989586621679420039 :: a_a1II5) :: a_a1II5 where
  SignumSym1 a6989586621679420039 = Signum a6989586621679420039
type FromIntegerSym0 :: forall a_a1II5. (~>) Natural a_a1II5
data FromIntegerSym0 :: (~>) Natural a_a1II5
  where
    FromIntegerSym0KindInference :: SameKind (Apply FromIntegerSym0 arg_a1IIV) (FromIntegerSym1 arg_a1IIV) =>
                                    FromIntegerSym0 a6989586621679420042
type instance Apply @Natural @a_a1II5 FromIntegerSym0 a6989586621679420042 = FromInteger a6989586621679420042
instance SuppressUnusedWarnings FromIntegerSym0 where
  suppressUnusedWarnings = snd ((,) FromIntegerSym0KindInference ())
type FromIntegerSym1 :: forall a_a1II5. Natural -> a_a1II5
type family FromIntegerSym1 @a_a1II5 (a6989586621679420042 :: Natural) :: a_a1II5 where
  FromIntegerSym1 a6989586621679420042 = FromInteger a6989586621679420042
type TFHelper_6989586621679420045 :: forall a_a1II5. a_a1II5
                                                      -> a_a1II5 -> a_a1II5
type family TFHelper_6989586621679420045 @a_a1II5 (a_a1IJ1 :: a_a1II5) (a_a1IJ2 :: a_a1II5) :: a_a1II5 where
  TFHelper_6989586621679420045 @a_a1II5 (x_a1IJ6 :: a_a1II5) (y_a1IJ7 :: a_a1II5) = Apply (Apply (+@#@$) x_a1IJ6) (Apply NegateSym0 y_a1IJ7)
type Negate_6989586621679420055 :: forall a_a1II5. a_a1II5
                                                    -> a_a1II5
type family Negate_6989586621679420055 @a_a1II5 (a_a1IJb :: a_a1II5) :: a_a1II5 where
  Negate_6989586621679420055 @a_a1II5 (x_a1IJe :: a_a1II5) = Apply (Apply (-@#@$) (FromInteger 0)) x_a1IJe
class PNum a_a1II5 where
  type family (+) (arg_a1IIw :: a_a1II5) (arg_a1IIx :: a_a1II5) :: a_a1II5
  type family (-) (arg_a1IIB :: a_a1II5) (arg_a1IIC :: a_a1II5) :: a_a1II5
  type family (*) (arg_a1IIG :: a_a1II5) (arg_a1IIH :: a_a1II5) :: a_a1II5
  type family Negate (arg_a1IIL :: a_a1II5) :: a_a1II5
  type family Abs (arg_a1IIO :: a_a1II5) :: a_a1II5
  type family Signum (arg_a1IIR :: a_a1II5) :: a_a1II5
  type family FromInteger (arg_a1IIU :: Natural) :: a_a1II5
  type (-) a_a1IIX a_a1IIY = TFHelper_6989586621679420045 a_a1IIX a_a1IIY
  type Negate a_a1IJ8 = Negate_6989586621679420055 a_a1IJ8
  infixl 6 +
  infixl 6 -
  infixl 7 *
type TFHelper_6989586621679420063 :: forall a_a1IIb. Down a_a1IIb
                                                      -> Down a_a1IIb -> Down a_a1IIb
type family TFHelper_6989586621679420063 @a_a1IIb (a_a1IJj :: Down a_a1IIb) (a_a1IJk :: Down a_a1IIb) :: Down a_a1IIb where
  TFHelper_6989586621679420063 @a_a1IIb ('Down a_a1IJo :: Down a_a1IIb) ('Down b_a1IJp :: Down a_a1IIb) = Apply DownSym0 (Apply (Apply (+@#@$) a_a1IJo) b_a1IJp)
type TFHelper_6989586621679420074 :: forall a_a1IIb. Down a_a1IIb
                                                      -> Down a_a1IIb -> Down a_a1IIb
type family TFHelper_6989586621679420074 @a_a1IIb (a_a1IJu :: Down a_a1IIb) (a_a1IJv :: Down a_a1IIb) :: Down a_a1IIb where
  TFHelper_6989586621679420074 @a_a1IIb ('Down a_a1IJz :: Down a_a1IIb) ('Down b_a1IJA :: Down a_a1IIb) = Apply DownSym0 (Apply (Apply (-@#@$) a_a1IJz) b_a1IJA)
type TFHelper_6989586621679420085 :: forall a_a1IIb. Down a_a1IIb
                                                      -> Down a_a1IIb -> Down a_a1IIb
type family TFHelper_6989586621679420085 @a_a1IIb (a_a1IJF :: Down a_a1IIb) (a_a1IJG :: Down a_a1IIb) :: Down a_a1IIb where
  TFHelper_6989586621679420085 @a_a1IIb ('Down a_a1IJK :: Down a_a1IIb) ('Down b_a1IJL :: Down a_a1IIb) = Apply DownSym0 (Apply (Apply (*@#@$) a_a1IJK) b_a1IJL)
type Negate_6989586621679420095 :: forall a_a1IIb. Down a_a1IIb
                                                    -> Down a_a1IIb
type family Negate_6989586621679420095 @a_a1IIb (a_a1IJP :: Down a_a1IIb) :: Down a_a1IIb where
  Negate_6989586621679420095 @a_a1IIb ('Down a_a1IJS :: Down a_a1IIb) = Apply DownSym0 (Apply NegateSym0 a_a1IJS)
type Abs_6989586621679420102 :: forall a_a1IIb. Down a_a1IIb
                                                -> Down a_a1IIb
type family Abs_6989586621679420102 @a_a1IIb (a_a1IJW :: Down a_a1IIb) :: Down a_a1IIb where
  Abs_6989586621679420102 @a_a1IIb ('Down a_a1IJZ :: Down a_a1IIb) = Apply DownSym0 (Apply AbsSym0 a_a1IJZ)
type Signum_6989586621679420109 :: forall a_a1IIb. Down a_a1IIb
                                                    -> Down a_a1IIb
type family Signum_6989586621679420109 @a_a1IIb (a_a1IK3 :: Down a_a1IIb) :: Down a_a1IIb where
  Signum_6989586621679420109 @a_a1IIb ('Down a_a1IK6 :: Down a_a1IIb) = Apply DownSym0 (Apply SignumSym0 a_a1IK6)
type FromInteger_6989586621679420116 :: forall a_a1IIb. Natural
                                                        -> Down a_a1IIb
type family FromInteger_6989586621679420116 @a_a1IIb (a_a1IKa :: Natural) :: Down a_a1IIb where
  FromInteger_6989586621679420116 @a_a1IIb (n_a1IKd :: Natural) = Apply DownSym0 (Apply FromIntegerSym0 n_a1IKd)
instance PNum (Down a_a1IIb) where
  type (+) a_a1IJf a_a1IJg = TFHelper_6989586621679420063 a_a1IJf a_a1IJg
  type (-) a_a1IJq a_a1IJr = TFHelper_6989586621679420074 a_a1IJq a_a1IJr
  type (*) a_a1IJB a_a1IJC = TFHelper_6989586621679420085 a_a1IJB a_a1IJC
  type Negate a_a1IJM = Negate_6989586621679420095 a_a1IJM
  type Abs a_a1IJT = Abs_6989586621679420102 a_a1IJT
  type Signum a_a1IK0 = Signum_6989586621679420109 a_a1IK0
  type FromInteger a_a1IK7 = FromInteger_6989586621679420116 a_a1IK7
sSubtract ::
  (forall (t_a1IKe :: a_a1IHV) (t_a1IKf :: a_a1IHV).
    SNum a_a1IHV =>
    Sing t_a1IKe
    -> Sing t_a1IKf
      -> Sing (Subtract t_a1IKe t_a1IKf :: a_a1IHV) :: Type)
sSubtract (sX :: Sing x_a1IIu) (sY :: Sing y_a1IIv)
  = applySing (applySing (singFun2 @(-@#@$) (%-)) sY) sX
instance SNum a_a1IHV =>
          SingI (SubtractSym0 :: (~>) a_a1IHV ((~>) a_a1IHV a_a1IHV)) where
  sing = singFun2 @SubtractSym0 sSubtract
instance (SNum a_a1IHV, SingI d_a1IKg) =>
          SingI (SubtractSym1 (d_a1IKg :: a_a1IHV) :: (~>) a_a1IHV a_a1IHV) where
  sing
    = singFun1
        @(SubtractSym1 (d_a1IKg :: a_a1IHV)) (sSubtract (sing @d_a1IKg))
instance SNum a_a1IHV =>
          SingI1 (SubtractSym1 :: a_a1IHV -> (~>) a_a1IHV a_a1IHV) where
  liftSing (s_a1IKi :: Sing (d_a1IKg :: a_a1IHV))
    = singFun1 @(SubtractSym1 (d_a1IKg :: a_a1IHV)) (sSubtract s_a1IKi)
class SNum a_a1II5 where
  (%+) ::
    (forall (t_a1IKj :: a_a1II5) (t_a1IKk :: a_a1II5).
      Sing t_a1IKj
      -> Sing t_a1IKk -> Sing ((+) t_a1IKj t_a1IKk :: a_a1II5) :: Type)
  (%-) ::
    (forall (t_a1IKo :: a_a1II5) (t_a1IKp :: a_a1II5).
      Sing t_a1IKo
      -> Sing t_a1IKp -> Sing ((-) t_a1IKo t_a1IKp :: a_a1II5) :: Type)
  (%*) ::
    (forall (t_a1IKt :: a_a1II5) (t_a1IKu :: a_a1II5).
      Sing t_a1IKt
      -> Sing t_a1IKu -> Sing ((*) t_a1IKt t_a1IKu :: a_a1II5) :: Type)
  sNegate ::
    (forall (t_a1IKy :: a_a1II5).
      Sing t_a1IKy -> Sing (Negate t_a1IKy :: a_a1II5) :: Type)
  sAbs ::
    (forall (t_a1IKA :: a_a1II5).
      Sing t_a1IKA -> Sing (Abs t_a1IKA :: a_a1II5) :: Type)
  sSignum ::
    (forall (t_a1IKC :: a_a1II5).
      Sing t_a1IKC -> Sing (Signum t_a1IKC :: a_a1II5) :: Type)
  sFromInteger ::
    (forall (t_a1IKE :: Natural).
      Sing t_a1IKE -> Sing (FromInteger t_a1IKE :: a_a1II5) :: Type)
  infixl 6 %+
  infixl 6 %-
  infixl 7 %*
  default (%-) ::
            (forall (t_a1IKo :: a_a1II5) (t_a1IKp :: a_a1II5).
              (((-) t_a1IKo t_a1IKp :: a_a1II5)
              ~ TFHelper_6989586621679420045 t_a1IKo t_a1IKp) =>
              Sing t_a1IKo
              -> Sing t_a1IKp -> Sing ((-) t_a1IKo t_a1IKp :: a_a1II5) :: Type)
  default sNegate ::
            (forall (t_a1IKy :: a_a1II5).
              ((Negate t_a1IKy :: a_a1II5)
              ~ Negate_6989586621679420055 t_a1IKy) =>
              Sing t_a1IKy -> Sing (Negate t_a1IKy :: a_a1II5) :: Type)
  (%-) (sX :: Sing x_a1IJ6) (sY :: Sing y_a1IJ7)
    = applySing
        (applySing (singFun2 @(+@#@$) (%+)) sX)
        (applySing (singFun1 @NegateSym0 sNegate) sY)
  sNegate (sX :: Sing x_a1IJe)
    = applySing
        (applySing
            (singFun2 @(-@#@$) (%-)) (sFromInteger (sing :: Sing 0)))
        sX
instance SNum a_a1IIb => SNum (Down a_a1IIb) where
  (%+) (SDown (sA :: Sing a_a1IJo)) (SDown (sB :: Sing b_a1IJp))
    = applySing
        (singFun1 @DownSym0 SDown)
        (applySing (applySing (singFun2 @(+@#@$) (%+)) sA) sB)
  (%-) (SDown (sA :: Sing a_a1IJz)) (SDown (sB :: Sing b_a1IJA))
    = applySing
        (singFun1 @DownSym0 SDown)
        (applySing (applySing (singFun2 @(-@#@$) (%-)) sA) sB)
  (%*) (SDown (sA :: Sing a_a1IJK)) (SDown (sB :: Sing b_a1IJL))
    = applySing
        (singFun1 @DownSym0 SDown)
        (applySing (applySing (singFun2 @(*@#@$) (%*)) sA) sB)
  sNegate (SDown (sA :: Sing a_a1IJS))
    = applySing
        (singFun1 @DownSym0 SDown)
        (applySing (singFun1 @NegateSym0 sNegate) sA)
  sAbs (SDown (sA :: Sing a_a1IJZ))
    = applySing
        (singFun1 @DownSym0 SDown) (applySing (singFun1 @AbsSym0 sAbs) sA)
  sSignum (SDown (sA :: Sing a_a1IK6))
    = applySing
        (singFun1 @DownSym0 SDown)
        (applySing (singFun1 @SignumSym0 sSignum) sA)
  sFromInteger (sN :: Sing n_a1IKd)
    = applySing
        (singFun1 @DownSym0 SDown)
        (applySing (singFun1 @FromIntegerSym0 sFromInteger) sN)
instance SNum a_a1II5 =>
          SingI ((+@#@$) :: (~>) a_a1II5 ((~>) a_a1II5 a_a1II5)) where
  sing = singFun2 @(+@#@$) (%+)
instance (SNum a_a1II5, SingI d_a1IKl) =>
          SingI ((+@#@$$) (d_a1IKl :: a_a1II5) :: (~>) a_a1II5 a_a1II5) where
  sing
    = singFun1 @((+@#@$$) (d_a1IKl :: a_a1II5)) ((%+) (sing @d_a1IKl))
instance SNum a_a1II5 =>
          SingI1 ((+@#@$$) :: a_a1II5 -> (~>) a_a1II5 a_a1II5) where
  liftSing (s_a1IKn :: Sing (d_a1IKl :: a_a1II5))
    = singFun1 @((+@#@$$) (d_a1IKl :: a_a1II5)) ((%+) s_a1IKn)
instance SNum a_a1II5 =>
          SingI ((-@#@$) :: (~>) a_a1II5 ((~>) a_a1II5 a_a1II5)) where
  sing = singFun2 @(-@#@$) (%-)
instance (SNum a_a1II5, SingI d_a1IKq) =>
          SingI ((-@#@$$) (d_a1IKq :: a_a1II5) :: (~>) a_a1II5 a_a1II5) where
  sing
    = singFun1 @((-@#@$$) (d_a1IKq :: a_a1II5)) ((%-) (sing @d_a1IKq))
instance SNum a_a1II5 =>
          SingI1 ((-@#@$$) :: a_a1II5 -> (~>) a_a1II5 a_a1II5) where
  liftSing (s_a1IKs :: Sing (d_a1IKq :: a_a1II5))
    = singFun1 @((-@#@$$) (d_a1IKq :: a_a1II5)) ((%-) s_a1IKs)
instance SNum a_a1II5 =>
          SingI ((*@#@$) :: (~>) a_a1II5 ((~>) a_a1II5 a_a1II5)) where
  sing = singFun2 @(*@#@$) (%*)
instance (SNum a_a1II5, SingI d_a1IKv) =>
          SingI ((*@#@$$) (d_a1IKv :: a_a1II5) :: (~>) a_a1II5 a_a1II5) where
  sing
    = singFun1 @((*@#@$$) (d_a1IKv :: a_a1II5)) ((%*) (sing @d_a1IKv))
instance SNum a_a1II5 =>
          SingI1 ((*@#@$$) :: a_a1II5 -> (~>) a_a1II5 a_a1II5) where
  liftSing (s_a1IKx :: Sing (d_a1IKv :: a_a1II5))
    = singFun1 @((*@#@$$) (d_a1IKv :: a_a1II5)) ((%*) s_a1IKx)
instance SNum a_a1II5 =>
          SingI (NegateSym0 :: (~>) a_a1II5 a_a1II5) where
  sing = singFun1 @NegateSym0 sNegate
instance SNum a_a1II5 =>
          SingI (AbsSym0 :: (~>) a_a1II5 a_a1II5) where
  sing = singFun1 @AbsSym0 sAbs
instance SNum a_a1II5 =>
          SingI (SignumSym0 :: (~>) a_a1II5 a_a1II5) where
  sing = singFun1 @SignumSym0 sSignum
instance SNum a_a1II5 =>
          SingI (FromIntegerSym0 :: (~>) Natural a_a1II5) where
  sing = singFun1 @FromIntegerSym0 sFromInteger

-- PNum instance
type SignumNat :: Natural -> Natural
type family SignumNat a where
  SignumNat 0 = 0
  SignumNat x = 1

instance PNum Natural where
  type a + b = a TN.+ b
  type a - b = a TN.- b
  type a * b = a TN.* b
  type Negate (a :: Natural) = Error "Cannot negate a natural number"
  type Abs (a :: Natural) = a
  type Signum a = SignumNat a
  type FromInteger a = a

-- SNum instance
instance SNum Natural where
  sa %+ sb =
    let a = fromSing sa
        b = fromSing sb
    in TN.withSomeSNat (a + b) unsafeCoerce

  sa %- sb =
    let a = fromSing sa
        b = fromSing sb
    in TN.withSomeSNat (a - b) unsafeCoerce

  sa %* sb =
    let a = fromSing sa
        b = fromSing sb
    in TN.withSomeSNat (a * b) unsafeCoerce

  sNegate _ = error "Cannot call sNegate on a natural number singleton."

  sAbs x = x

  sSignum sx =
    case sx %~ (sing :: Sing 0) of
      Proved Refl -> sing :: Sing 0
      Disproved _ -> unsafeCoerce (sing :: Sing 1)

  sFromInteger x = x
