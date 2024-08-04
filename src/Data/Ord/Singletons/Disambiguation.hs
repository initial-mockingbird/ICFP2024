{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
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
-- Module      :  Data.Ord.Singletons.Disambiguation
-- Copyright   :  (C) 2019 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Provides aliases for 'Min' and 'Max' that do not clash with the data
-- types of the same names in "Data.Semigroup.Singletons".
--
----------------------------------------------------------------------------

module Data.Ord.Singletons.Disambiguation where

import Data.Ord.Singletons
import Data.Singletons.TH
    ( SuppressUnusedWarnings(..),
      Apply,
      SameKind,
      singFun1,
      singFun2,
      SLambda(applySing),
      SingI(..),
      SingI1(..),
      type (~>) )
import Data.Kind (Type)

-- We need these in Data.Semigroup.Singletons, as we need to promote
-- code that simultaneously uses the Min/Max constructors and the min/max
-- functions, which have clashing defunctionalization symbol names. Our
-- workaround is to simply define synonyms for min/max and use those instead.
min_ :: Ord a_a13tX => a_a13tX -> a_a13tX -> a_a13tX
max_ :: Ord a_a13tX => a_a13tX -> a_a13tX -> a_a13tX
min_ = min
max_ = max
type Max_Sym0 :: (~>) a_a13tX ((~>) a_a13tX a_a13tX)
data Max_Sym0 :: (~>) a_a13tX ((~>) a_a13tX a_a13tX)
  where
    Max_Sym0KindInference :: SameKind (Apply Max_Sym0 arg_a13uf) (Max_Sym1 arg_a13uf) =>
                              Max_Sym0 a6989586621679261528
type instance Apply @a_a13tX @((~>) a_a13tX a_a13tX) Max_Sym0 a6989586621679261528 = Max_Sym1 a6989586621679261528
instance SuppressUnusedWarnings Max_Sym0 where
  suppressUnusedWarnings = snd ((,) Max_Sym0KindInference ())
type Max_Sym1 :: a_a13tX -> (~>) a_a13tX a_a13tX
data Max_Sym1 (a6989586621679261528 :: a_a13tX) :: (~>) a_a13tX a_a13tX
  where
    Max_Sym1KindInference :: SameKind (Apply (Max_Sym1 a6989586621679261528) arg_a13uf) (Max_Sym2 a6989586621679261528 arg_a13uf) =>
                              Max_Sym1 a6989586621679261528 a6989586621679261529
type instance Apply @a_a13tX @a_a13tX (Max_Sym1 a6989586621679261528) a6989586621679261529 = Max_ a6989586621679261528 a6989586621679261529
instance SuppressUnusedWarnings (Max_Sym1 a6989586621679261528) where
  suppressUnusedWarnings = snd ((,) Max_Sym1KindInference ())
type Max_Sym2 :: a_a13tX -> a_a13tX -> a_a13tX
type family Max_Sym2 @a_a13tX (a6989586621679261528 :: a_a13tX) (a6989586621679261529 :: a_a13tX) :: a_a13tX where
  Max_Sym2 a6989586621679261528 a6989586621679261529 = Max_ a6989586621679261528 a6989586621679261529
type Min_Sym0 :: (~>) a_a13tX ((~>) a_a13tX a_a13tX)
data Min_Sym0 :: (~>) a_a13tX ((~>) a_a13tX a_a13tX)
  where
    Min_Sym0KindInference :: SameKind (Apply Min_Sym0 arg_a13uq) (Min_Sym1 arg_a13uq) =>
                              Min_Sym0 a6989586621679261539
type instance Apply @a_a13tX @((~>) a_a13tX a_a13tX) Min_Sym0 a6989586621679261539 = Min_Sym1 a6989586621679261539
instance SuppressUnusedWarnings Min_Sym0 where
  suppressUnusedWarnings = snd ((,) Min_Sym0KindInference ())
type Min_Sym1 :: a_a13tX -> (~>) a_a13tX a_a13tX
data Min_Sym1 (a6989586621679261539 :: a_a13tX) :: (~>) a_a13tX a_a13tX
  where
    Min_Sym1KindInference :: SameKind (Apply (Min_Sym1 a6989586621679261539) arg_a13uq) (Min_Sym2 a6989586621679261539 arg_a13uq) =>
                              Min_Sym1 a6989586621679261539 a6989586621679261540
type instance Apply @a_a13tX @a_a13tX (Min_Sym1 a6989586621679261539) a6989586621679261540 = Min_ a6989586621679261539 a6989586621679261540
instance SuppressUnusedWarnings (Min_Sym1 a6989586621679261539) where
  suppressUnusedWarnings = snd ((,) Min_Sym1KindInference ())
type Min_Sym2 :: a_a13tX -> a_a13tX -> a_a13tX
type family Min_Sym2 @a_a13tX (a6989586621679261539 :: a_a13tX) (a6989586621679261540 :: a_a13tX) :: a_a13tX where
  Min_Sym2 a6989586621679261539 a6989586621679261540 = Min_ a6989586621679261539 a6989586621679261540
type Max_ :: a_a13tX -> a_a13tX -> a_a13tX
type family Max_ @a_a13tX (a_a13ud :: a_a13tX) (a_a13ue :: a_a13tX) :: a_a13tX where
  Max_ a_6989586621679261521_a13ui a_6989586621679261523_a13uj = Apply (Apply MaxSym0 a_6989586621679261521_a13ui) a_6989586621679261523_a13uj
type Min_ :: a_a13tX -> a_a13tX -> a_a13tX
type family Min_ @a_a13tX (a_a13uo :: a_a13tX) (a_a13up :: a_a13tX) :: a_a13tX where
  Min_ a_6989586621679261532_a13ut a_6989586621679261534_a13uu = Apply (Apply MinSym0 a_6989586621679261532_a13ut) a_6989586621679261534_a13uu
sMax_ ::
  (forall (t_a13uv :: a_a13tX) (t_a13uw :: a_a13tX).
    SOrd a_a13tX =>
    Sing t_a13uv
    -> Sing t_a13uw -> Sing (Max_ t_a13uv t_a13uw :: a_a13tX) :: Type)
sMin_ ::
  (forall (t_a13uA :: a_a13tX) (t_a13uB :: a_a13tX).
    SOrd a_a13tX =>
    Sing t_a13uA
    -> Sing t_a13uB -> Sing (Min_ t_a13uA t_a13uB :: a_a13tX) :: Type)
sMax_
  (sA_6989586621679261521 :: Sing a_6989586621679261521_a13ui)
  (sA_6989586621679261523 :: Sing a_6989586621679261523_a13uj)
  = applySing
      (applySing (singFun2 @MaxSym0 sMax) sA_6989586621679261521)
      sA_6989586621679261523
sMin_
  (sA_6989586621679261532 :: Sing a_6989586621679261532_a13ut)
  (sA_6989586621679261534 :: Sing a_6989586621679261534_a13uu)
  = applySing
      (applySing (singFun2 @MinSym0 sMin) sA_6989586621679261532)
      sA_6989586621679261534
instance SOrd a_a13tX =>
          SingI (Max_Sym0 :: (~>) a_a13tX ((~>) a_a13tX a_a13tX)) where
  sing = singFun2 @Max_Sym0 sMax_
instance (SOrd a_a13tX, SingI d_a13ux) =>
          SingI (Max_Sym1 (d_a13ux :: a_a13tX) :: (~>) a_a13tX a_a13tX) where
  sing
    = singFun1 @(Max_Sym1 (d_a13ux :: a_a13tX)) (sMax_ (sing @d_a13ux))
instance SOrd a_a13tX =>
          SingI1 (Max_Sym1 :: a_a13tX -> (~>) a_a13tX a_a13tX) where
  liftSing (s_a13uz :: Sing (d_a13ux :: a_a13tX))
    = singFun1 @(Max_Sym1 (d_a13ux :: a_a13tX)) (sMax_ s_a13uz)
instance SOrd a_a13tX =>
          SingI (Min_Sym0 :: (~>) a_a13tX ((~>) a_a13tX a_a13tX)) where
  sing = singFun2 @Min_Sym0 sMin_
instance (SOrd a_a13tX, SingI d_a13uC) =>
          SingI (Min_Sym1 (d_a13uC :: a_a13tX) :: (~>) a_a13tX a_a13tX) where
  sing
    = singFun1 @(Min_Sym1 (d_a13uC :: a_a13tX)) (sMin_ (sing @d_a13uC))
instance SOrd a_a13tX =>
          SingI1 (Min_Sym1 :: a_a13tX -> (~>) a_a13tX a_a13tX) where
  liftSing (s_a13uE :: Sing (d_a13uC :: a_a13tX))
    = singFun1 @(Min_Sym1 (d_a13uC :: a_a13tX)) (sMin_ s_a13uE)

