{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}

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
-- Module      :  Data.Ord.Singletons
-- Copyright   :  (C) 2013 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted version of Ord, 'POrd', and the singleton version,
-- 'SOrd'.
--
-----------------------------------------------------------------------------

module Data.Ord.Singletons (
  POrd(..), SOrd(..),

  Comparing, sComparing,

  Sing, SOrdering(..), SDown(..), GetDown, sGetDown,

  -- ** Defunctionalization symbols
  LTSym0, EQSym0, GTSym0,
  CompareSym0, CompareSym1, CompareSym2,
  type (<@#@$),  type (<@#@$$),  type (<@#@$$$),
  type (<=@#@$), type (<=@#@$$), type (<=@#@$$$),
  type (>@#@$),  type (>@#@$$),  type (>@#@$$$),
  type (>=@#@$), type (>=@#@$$), type (>=@#@$$$),
  MaxSym0, MaxSym1, MaxSym2,
  MinSym0, MinSym1, MinSym2,
  ComparingSym0, ComparingSym1, ComparingSym2, ComparingSym3,
  DownSym0, DownSym1,
  GetDownSym0, GetDownSym1
  ) where

import Data.Eq.Singletons
import Data.Ord (Down(..))
import Data.Semigroup.Singletons.Internal.Classes
import Data.Singletons.Base.Instances

import Data.Singletons.TH
import Data.Kind (Type)
import qualified Data.Type.Equality
import qualified Data.Type.Coercion
import qualified Data.Singletons.Decide
import qualified Data.Functor.Identity
import GHC.Base

type ComparingSym0 :: (~>) ((~>) b_aNTW a_aNTV) ((~>) b_aNTW ((~>) b_aNTW Ordering))
data ComparingSym0 :: (~>) ((~>) b_aNTW a_aNTV) ((~>) b_aNTW ((~>) b_aNTW Ordering))
  where
    ComparingSym0KindInference :: SameKind (Apply ComparingSym0 arg_aOpR) (ComparingSym1 arg_aOpR) =>
                                  ComparingSym0 a6989586621679203596
type instance Apply @((~>) b_aNTW a_aNTV) @((~>) b_aNTW ((~>) b_aNTW Ordering)) ComparingSym0 a6989586621679203596 = ComparingSym1 a6989586621679203596
instance SuppressUnusedWarnings ComparingSym0 where
  suppressUnusedWarnings = snd ((,) ComparingSym0KindInference ())
type ComparingSym1 :: (~>) b_aNTW a_aNTV
                      -> (~>) b_aNTW ((~>) b_aNTW Ordering)
data ComparingSym1 (a6989586621679203596 :: (~>) b_aNTW a_aNTV) :: (~>) b_aNTW ((~>) b_aNTW Ordering)
  where
    ComparingSym1KindInference :: SameKind (Apply (ComparingSym1 a6989586621679203596) arg_aOpR) (ComparingSym2 a6989586621679203596 arg_aOpR) =>
                                  ComparingSym1 a6989586621679203596 a6989586621679203597
type instance Apply @b_aNTW @((~>) b_aNTW Ordering) (ComparingSym1 a6989586621679203596) a6989586621679203597 = ComparingSym2 a6989586621679203596 a6989586621679203597
instance SuppressUnusedWarnings (ComparingSym1 a6989586621679203596) where
  suppressUnusedWarnings = snd ((,) ComparingSym1KindInference ())
type ComparingSym2 :: (~>) b_aNTW a_aNTV
                      -> b_aNTW -> (~>) b_aNTW Ordering
data ComparingSym2 (a6989586621679203596 :: (~>) b_aNTW a_aNTV) (a6989586621679203597 :: b_aNTW) :: (~>) b_aNTW Ordering
  where
    ComparingSym2KindInference :: SameKind (Apply (ComparingSym2 a6989586621679203596 a6989586621679203597) arg_aOpR) (ComparingSym3 a6989586621679203596 a6989586621679203597 arg_aOpR) =>
                                  ComparingSym2 a6989586621679203596 a6989586621679203597 a6989586621679203598
type instance Apply @b_aNTW @Ordering (ComparingSym2 a6989586621679203596 a6989586621679203597) a6989586621679203598 = Comparing a6989586621679203596 a6989586621679203597 a6989586621679203598
instance SuppressUnusedWarnings (ComparingSym2 a6989586621679203596 a6989586621679203597) where
  suppressUnusedWarnings = snd ((,) ComparingSym2KindInference ())
type ComparingSym3 :: (~>) b_aNTW a_aNTV
                      -> b_aNTW -> b_aNTW -> Ordering
type family ComparingSym3 @b_aNTW @a_aNTV (a6989586621679203596 :: (~>) b_aNTW a_aNTV) (a6989586621679203597 :: b_aNTW) (a6989586621679203598 :: b_aNTW) :: Ordering where
  ComparingSym3 a6989586621679203596 a6989586621679203597 a6989586621679203598 = Comparing a6989586621679203596 a6989586621679203597 a6989586621679203598
type Comparing :: (~>) b_aNTW a_aNTV
                  -> b_aNTW -> b_aNTW -> Ordering
type family Comparing @b_aNTW @a_aNTV (a_aOpO :: (~>) b_aNTW a_aNTV) (a_aOpP :: b_aNTW) (a_aOpQ :: b_aNTW) :: Ordering where
  Comparing p_aOpV x_aOpW y_aOpX = Apply (Apply CompareSym0 (Apply p_aOpV x_aOpW)) (Apply p_aOpV y_aOpX)
type CompareSym0 :: forall a_aNU6. (~>) a_aNU6 ((~>) a_aNU6 Ordering)
data CompareSym0 :: (~>) a_aNU6 ((~>) a_aNU6 Ordering)
  where
    CompareSym0KindInference :: SameKind (Apply CompareSym0 arg_aOq0) (CompareSym1 arg_aOq0) =>
                                CompareSym0 a6989586621679203605
type instance Apply @a_aNU6 @((~>) a_aNU6 Ordering) CompareSym0 a6989586621679203605 = CompareSym1 a6989586621679203605
instance SuppressUnusedWarnings CompareSym0 where
  suppressUnusedWarnings = snd ((,) CompareSym0KindInference ())
type CompareSym1 :: forall a_aNU6. a_aNU6 -> (~>) a_aNU6 Ordering
data CompareSym1 (a6989586621679203605 :: a_aNU6) :: (~>) a_aNU6 Ordering
  where
    CompareSym1KindInference :: SameKind (Apply (CompareSym1 a6989586621679203605) arg_aOq0) (CompareSym2 a6989586621679203605 arg_aOq0) =>
                                CompareSym1 a6989586621679203605 a6989586621679203606
type instance Apply @a_aNU6 @Ordering (CompareSym1 a6989586621679203605) a6989586621679203606 = Compare a6989586621679203605 a6989586621679203606
instance SuppressUnusedWarnings (CompareSym1 a6989586621679203605) where
  suppressUnusedWarnings = snd ((,) CompareSym1KindInference ())
type CompareSym2 :: forall a_aNU6. a_aNU6 -> a_aNU6 -> Ordering
type family CompareSym2 @a_aNU6 (a6989586621679203605 :: a_aNU6) (a6989586621679203606 :: a_aNU6) :: Ordering where
  CompareSym2 a6989586621679203605 a6989586621679203606 = Compare a6989586621679203605 a6989586621679203606
type (<@#@$) :: forall a_aNU6. (~>) a_aNU6 ((~>) a_aNU6 Bool)
data (<@#@$) :: (~>) a_aNU6 ((~>) a_aNU6 Bool)
  where
    (:<@#@$###) :: SameKind (Apply (<@#@$) arg_aOq5) ((<@#@$$) arg_aOq5) =>
                    (<@#@$) a6989586621679203610
type instance Apply @a_aNU6 @((~>) a_aNU6 Bool) (<@#@$) a6989586621679203610 = (<@#@$$) a6989586621679203610
instance SuppressUnusedWarnings (<@#@$) where
  suppressUnusedWarnings = snd ((,) (:<@#@$###) ())
infix 4 <@#@$
type (<@#@$$) :: forall a_aNU6. a_aNU6 -> (~>) a_aNU6 Bool
data (<@#@$$) (a6989586621679203610 :: a_aNU6) :: (~>) a_aNU6 Bool
  where
    (:<@#@$$###) :: SameKind (Apply ((<@#@$$) a6989586621679203610) arg_aOq5) ((<@#@$$$) a6989586621679203610 arg_aOq5) =>
                    (<@#@$$) a6989586621679203610 a6989586621679203611
type instance Apply @a_aNU6 @Bool ((<@#@$$) a6989586621679203610) a6989586621679203611 = (<) a6989586621679203610 a6989586621679203611
instance SuppressUnusedWarnings ((<@#@$$) a6989586621679203610) where
  suppressUnusedWarnings = snd ((,) (:<@#@$$###) ())
infix 4 <@#@$$
type (<@#@$$$) :: forall a_aNU6. a_aNU6 -> a_aNU6 -> Bool
type family (<@#@$$$) @a_aNU6 (a6989586621679203610 :: a_aNU6) (a6989586621679203611 :: a_aNU6) :: Bool where
  (<@#@$$$) a6989586621679203610 a6989586621679203611 = (<) a6989586621679203610 a6989586621679203611
infix 4 <@#@$$$
type (<=@#@$) :: forall a_aNU6. (~>) a_aNU6 ((~>) a_aNU6 Bool)
data (<=@#@$) :: (~>) a_aNU6 ((~>) a_aNU6 Bool)
  where
    (:<=@#@$###) :: SameKind (Apply (<=@#@$) arg_aOqa) ((<=@#@$$) arg_aOqa) =>
                    (<=@#@$) a6989586621679203615
type instance Apply @a_aNU6 @((~>) a_aNU6 Bool) (<=@#@$) a6989586621679203615 = (<=@#@$$) a6989586621679203615
instance SuppressUnusedWarnings (<=@#@$) where
  suppressUnusedWarnings = snd ((,) (:<=@#@$###) ())
infix 4 <=@#@$
type (<=@#@$$) :: forall a_aNU6. a_aNU6 -> (~>) a_aNU6 Bool
data (<=@#@$$) (a6989586621679203615 :: a_aNU6) :: (~>) a_aNU6 Bool
  where
    (:<=@#@$$###) :: SameKind (Apply ((<=@#@$$) a6989586621679203615) arg_aOqa) ((<=@#@$$$) a6989586621679203615 arg_aOqa) =>
                      (<=@#@$$) a6989586621679203615 a6989586621679203616
type instance Apply @a_aNU6 @Bool ((<=@#@$$) a6989586621679203615) a6989586621679203616 = (<=) a6989586621679203615 a6989586621679203616
instance SuppressUnusedWarnings ((<=@#@$$) a6989586621679203615) where
  suppressUnusedWarnings = snd ((,) (:<=@#@$$###) ())
infix 4 <=@#@$$
type (<=@#@$$$) :: forall a_aNU6. a_aNU6 -> a_aNU6 -> Bool
type family (<=@#@$$$) @a_aNU6 (a6989586621679203615 :: a_aNU6) (a6989586621679203616 :: a_aNU6) :: Bool where
  (<=@#@$$$) a6989586621679203615 a6989586621679203616 = (<=) a6989586621679203615 a6989586621679203616
infix 4 <=@#@$$$
type (>@#@$) :: forall a_aNU6. (~>) a_aNU6 ((~>) a_aNU6 Bool)
data (>@#@$) :: (~>) a_aNU6 ((~>) a_aNU6 Bool)
  where
    (:>@#@$###) :: SameKind (Apply (>@#@$) arg_aOqf) ((>@#@$$) arg_aOqf) =>
                    (>@#@$) a6989586621679203620
type instance Apply @a_aNU6 @((~>) a_aNU6 Bool) (>@#@$) a6989586621679203620 = (>@#@$$) a6989586621679203620
instance SuppressUnusedWarnings (>@#@$) where
  suppressUnusedWarnings = snd ((,) (:>@#@$###) ())
infix 4 >@#@$
type (>@#@$$) :: forall a_aNU6. a_aNU6 -> (~>) a_aNU6 Bool
data (>@#@$$) (a6989586621679203620 :: a_aNU6) :: (~>) a_aNU6 Bool
  where
    (:>@#@$$###) :: SameKind (Apply ((>@#@$$) a6989586621679203620) arg_aOqf) ((>@#@$$$) a6989586621679203620 arg_aOqf) =>
                    (>@#@$$) a6989586621679203620 a6989586621679203621
type instance Apply @a_aNU6 @Bool ((>@#@$$) a6989586621679203620) a6989586621679203621 = (>) a6989586621679203620 a6989586621679203621
instance SuppressUnusedWarnings ((>@#@$$) a6989586621679203620) where
  suppressUnusedWarnings = snd ((,) (:>@#@$$###) ())
infix 4 >@#@$$
type (>@#@$$$) :: forall a_aNU6. a_aNU6 -> a_aNU6 -> Bool
type family (>@#@$$$) @a_aNU6 (a6989586621679203620 :: a_aNU6) (a6989586621679203621 :: a_aNU6) :: Bool where
  (>@#@$$$) a6989586621679203620 a6989586621679203621 = (>) a6989586621679203620 a6989586621679203621
infix 4 >@#@$$$
type (>=@#@$) :: forall a_aNU6. (~>) a_aNU6 ((~>) a_aNU6 Bool)
data (>=@#@$) :: (~>) a_aNU6 ((~>) a_aNU6 Bool)
  where
    (:>=@#@$###) :: SameKind (Apply (>=@#@$) arg_aOqk) ((>=@#@$$) arg_aOqk) =>
                    (>=@#@$) a6989586621679203625
type instance Apply @a_aNU6 @((~>) a_aNU6 Bool) (>=@#@$) a6989586621679203625 = (>=@#@$$) a6989586621679203625
instance SuppressUnusedWarnings (>=@#@$) where
  suppressUnusedWarnings = snd ((,) (:>=@#@$###) ())
infix 4 >=@#@$
type (>=@#@$$) :: forall a_aNU6. a_aNU6 -> (~>) a_aNU6 Bool
data (>=@#@$$) (a6989586621679203625 :: a_aNU6) :: (~>) a_aNU6 Bool
  where
    (:>=@#@$$###) :: SameKind (Apply ((>=@#@$$) a6989586621679203625) arg_aOqk) ((>=@#@$$$) a6989586621679203625 arg_aOqk) =>
                      (>=@#@$$) a6989586621679203625 a6989586621679203626
type instance Apply @a_aNU6 @Bool ((>=@#@$$) a6989586621679203625) a6989586621679203626 = (>=) a6989586621679203625 a6989586621679203626
instance SuppressUnusedWarnings ((>=@#@$$) a6989586621679203625) where
  suppressUnusedWarnings = snd ((,) (:>=@#@$$###) ())
infix 4 >=@#@$$
type (>=@#@$$$) :: forall a_aNU6. a_aNU6 -> a_aNU6 -> Bool
type family (>=@#@$$$) @a_aNU6 (a6989586621679203625 :: a_aNU6) (a6989586621679203626 :: a_aNU6) :: Bool where
  (>=@#@$$$) a6989586621679203625 a6989586621679203626 = (>=) a6989586621679203625 a6989586621679203626
infix 4 >=@#@$$$
type MaxSym0 :: forall a_aNU6. (~>) a_aNU6 ((~>) a_aNU6 a_aNU6)
data MaxSym0 :: (~>) a_aNU6 ((~>) a_aNU6 a_aNU6)
  where
    MaxSym0KindInference :: SameKind (Apply MaxSym0 arg_aOqp) (MaxSym1 arg_aOqp) =>
                            MaxSym0 a6989586621679203630
type instance Apply @a_aNU6 @((~>) a_aNU6 a_aNU6) MaxSym0 a6989586621679203630 = MaxSym1 a6989586621679203630
instance SuppressUnusedWarnings MaxSym0 where
  suppressUnusedWarnings = snd ((,) MaxSym0KindInference ())
type MaxSym1 :: forall a_aNU6. a_aNU6 -> (~>) a_aNU6 a_aNU6
data MaxSym1 (a6989586621679203630 :: a_aNU6) :: (~>) a_aNU6 a_aNU6
  where
    MaxSym1KindInference :: SameKind (Apply (MaxSym1 a6989586621679203630) arg_aOqp) (MaxSym2 a6989586621679203630 arg_aOqp) =>
                            MaxSym1 a6989586621679203630 a6989586621679203631
type instance Apply @a_aNU6 @a_aNU6 (MaxSym1 a6989586621679203630) a6989586621679203631 = Max a6989586621679203630 a6989586621679203631
instance SuppressUnusedWarnings (MaxSym1 a6989586621679203630) where
  suppressUnusedWarnings = snd ((,) MaxSym1KindInference ())
type MaxSym2 :: forall a_aNU6. a_aNU6 -> a_aNU6 -> a_aNU6
type family MaxSym2 @a_aNU6 (a6989586621679203630 :: a_aNU6) (a6989586621679203631 :: a_aNU6) :: a_aNU6 where
  MaxSym2 a6989586621679203630 a6989586621679203631 = Max a6989586621679203630 a6989586621679203631
type MinSym0 :: forall a_aNU6. (~>) a_aNU6 ((~>) a_aNU6 a_aNU6)
data MinSym0 :: (~>) a_aNU6 ((~>) a_aNU6 a_aNU6)
  where
    MinSym0KindInference :: SameKind (Apply MinSym0 arg_aOqu) (MinSym1 arg_aOqu) =>
                            MinSym0 a6989586621679203635
type instance Apply @a_aNU6 @((~>) a_aNU6 a_aNU6) MinSym0 a6989586621679203635 = MinSym1 a6989586621679203635
instance SuppressUnusedWarnings MinSym0 where
  suppressUnusedWarnings = snd ((,) MinSym0KindInference ())
type MinSym1 :: forall a_aNU6. a_aNU6 -> (~>) a_aNU6 a_aNU6
data MinSym1 (a6989586621679203635 :: a_aNU6) :: (~>) a_aNU6 a_aNU6
  where
    MinSym1KindInference :: SameKind (Apply (MinSym1 a6989586621679203635) arg_aOqu) (MinSym2 a6989586621679203635 arg_aOqu) =>
                            MinSym1 a6989586621679203635 a6989586621679203636
type instance Apply @a_aNU6 @a_aNU6 (MinSym1 a6989586621679203635) a6989586621679203636 = Min a6989586621679203635 a6989586621679203636
instance SuppressUnusedWarnings (MinSym1 a6989586621679203635) where
  suppressUnusedWarnings = snd ((,) MinSym1KindInference ())
type MinSym2 :: forall a_aNU6. a_aNU6 -> a_aNU6 -> a_aNU6
type family MinSym2 @a_aNU6 (a6989586621679203635 :: a_aNU6) (a6989586621679203636 :: a_aNU6) :: a_aNU6 where
  MinSym2 a6989586621679203635 a6989586621679203636 = Min a6989586621679203635 a6989586621679203636
type family LamCases_6989586621679203650_aOqL a6989586621679201626 (x6989586621679203646 :: a6989586621679201626) (y6989586621679203647 :: a6989586621679201626) a_6989586621679203652_aOqN where
  LamCases_6989586621679203650_aOqL a_aNU6 x_aOqG y_aOqH 'True = LTSym0
  LamCases_6989586621679203650_aOqL a_aNU6 x_aOqG y_aOqH 'False = GTSym0
data LamCases_6989586621679203650Sym0 a6989586621679201626 (x6989586621679203646 :: a6989586621679201626) (y6989586621679203647 :: a6989586621679201626) a_69895866216792036526989586621679203653
  where
    LamCases_6989586621679203650Sym0KindInference :: SameKind (Apply (LamCases_6989586621679203650Sym0 a6989586621679201626 x6989586621679203646 y6989586621679203647) arg_aOqO) (LamCases_6989586621679203650Sym1 a6989586621679201626 x6989586621679203646 y6989586621679203647 arg_aOqO) =>
                                                      LamCases_6989586621679203650Sym0 a6989586621679201626 x6989586621679203646 y6989586621679203647 a_69895866216792036526989586621679203653
type instance Apply @_ @_ (LamCases_6989586621679203650Sym0 a6989586621679201626 x6989586621679203646 y6989586621679203647) a_69895866216792036526989586621679203653 = LamCases_6989586621679203650_aOqL a6989586621679201626 x6989586621679203646 y6989586621679203647 a_69895866216792036526989586621679203653
instance SuppressUnusedWarnings (LamCases_6989586621679203650Sym0 a6989586621679201626 x6989586621679203646 y6989586621679203647) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679203650Sym0KindInference ())
type family LamCases_6989586621679203650Sym1 a6989586621679201626 (x6989586621679203646 :: a6989586621679201626) (y6989586621679203647 :: a6989586621679201626) a_69895866216792036526989586621679203653 where
  LamCases_6989586621679203650Sym1 a6989586621679201626 x6989586621679203646 y6989586621679203647 a_69895866216792036526989586621679203653 = LamCases_6989586621679203650_aOqL a6989586621679201626 x6989586621679203646 y6989586621679203647 a_69895866216792036526989586621679203653
type family LamCases_6989586621679203648_aOqJ a6989586621679201626 (x6989586621679203646 :: a6989586621679201626) (y6989586621679203647 :: a6989586621679201626) a_6989586621679203655_aOqQ where
  LamCases_6989586621679203648_aOqJ a_aNU6 x_aOqG y_aOqH 'True = EQSym0
  LamCases_6989586621679203648_aOqJ a_aNU6 x_aOqG y_aOqH 'False = Apply (LamCases_6989586621679203650Sym0 a_aNU6 x_aOqG y_aOqH) (Apply (Apply (<=@#@$) x_aOqG) y_aOqH)
data LamCases_6989586621679203648Sym0 a6989586621679201626 (x6989586621679203646 :: a6989586621679201626) (y6989586621679203647 :: a6989586621679201626) a_69895866216792036556989586621679203656
  where
    LamCases_6989586621679203648Sym0KindInference :: SameKind (Apply (LamCases_6989586621679203648Sym0 a6989586621679201626 x6989586621679203646 y6989586621679203647) arg_aOqR) (LamCases_6989586621679203648Sym1 a6989586621679201626 x6989586621679203646 y6989586621679203647 arg_aOqR) =>
                                                      LamCases_6989586621679203648Sym0 a6989586621679201626 x6989586621679203646 y6989586621679203647 a_69895866216792036556989586621679203656
type instance Apply @_ @_ (LamCases_6989586621679203648Sym0 a6989586621679201626 x6989586621679203646 y6989586621679203647) a_69895866216792036556989586621679203656 = LamCases_6989586621679203648_aOqJ a6989586621679201626 x6989586621679203646 y6989586621679203647 a_69895866216792036556989586621679203656
instance SuppressUnusedWarnings (LamCases_6989586621679203648Sym0 a6989586621679201626 x6989586621679203646 y6989586621679203647) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679203648Sym0KindInference ())
type family LamCases_6989586621679203648Sym1 a6989586621679201626 (x6989586621679203646 :: a6989586621679201626) (y6989586621679203647 :: a6989586621679201626) a_69895866216792036556989586621679203656 where
  LamCases_6989586621679203648Sym1 a6989586621679201626 x6989586621679203646 y6989586621679203647 a_69895866216792036556989586621679203656 = LamCases_6989586621679203648_aOqJ a6989586621679201626 x6989586621679203646 y6989586621679203647 a_69895866216792036556989586621679203656
type Compare_6989586621679203639 :: forall a_aNU6. a_aNU6
                                                    -> a_aNU6 -> Ordering
type family Compare_6989586621679203639 @a_aNU6 (a_aOqB :: a_aNU6) (a_aOqC :: a_aNU6) :: Ordering where
  Compare_6989586621679203639 @a_aNU6 (x_aOqG :: a_aNU6) (y_aOqH :: a_aNU6) = Apply (LamCases_6989586621679203648Sym0 a_aNU6 x_aOqG y_aOqH) (Apply (Apply (==@#@$) x_aOqG) y_aOqH)
type family LamCases_6989586621679203669_aOr4 a6989586621679201626 (x6989586621679203667 :: a6989586621679201626) (y6989586621679203668 :: a6989586621679201626) a_6989586621679203671_aOr6 where
  LamCases_6989586621679203669_aOr4 a_aNU6 x_aOr1 y_aOr2 'LT = TrueSym0
  LamCases_6989586621679203669_aOr4 a_aNU6 x_aOr1 y_aOr2 'EQ = FalseSym0
  LamCases_6989586621679203669_aOr4 a_aNU6 x_aOr1 y_aOr2 'GT = FalseSym0
data LamCases_6989586621679203669Sym0 a6989586621679201626 (x6989586621679203667 :: a6989586621679201626) (y6989586621679203668 :: a6989586621679201626) a_69895866216792036716989586621679203672
  where
    LamCases_6989586621679203669Sym0KindInference :: SameKind (Apply (LamCases_6989586621679203669Sym0 a6989586621679201626 x6989586621679203667 y6989586621679203668) arg_aOr7) (LamCases_6989586621679203669Sym1 a6989586621679201626 x6989586621679203667 y6989586621679203668 arg_aOr7) =>
                                                      LamCases_6989586621679203669Sym0 a6989586621679201626 x6989586621679203667 y6989586621679203668 a_69895866216792036716989586621679203672
type instance Apply @_ @_ (LamCases_6989586621679203669Sym0 a6989586621679201626 x6989586621679203667 y6989586621679203668) a_69895866216792036716989586621679203672 = LamCases_6989586621679203669_aOr4 a6989586621679201626 x6989586621679203667 y6989586621679203668 a_69895866216792036716989586621679203672
instance SuppressUnusedWarnings (LamCases_6989586621679203669Sym0 a6989586621679201626 x6989586621679203667 y6989586621679203668) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679203669Sym0KindInference ())
type family LamCases_6989586621679203669Sym1 a6989586621679201626 (x6989586621679203667 :: a6989586621679201626) (y6989586621679203668 :: a6989586621679201626) a_69895866216792036716989586621679203672 where
  LamCases_6989586621679203669Sym1 a6989586621679201626 x6989586621679203667 y6989586621679203668 a_69895866216792036716989586621679203672 = LamCases_6989586621679203669_aOr4 a6989586621679201626 x6989586621679203667 y6989586621679203668 a_69895866216792036716989586621679203672
type TFHelper_6989586621679203660 :: forall a_aNU6. a_aNU6
                                                    -> a_aNU6 -> Bool
type family TFHelper_6989586621679203660 @a_aNU6 (a_aOqW :: a_aNU6) (a_aOqX :: a_aNU6) :: Bool where
  TFHelper_6989586621679203660 @a_aNU6 (x_aOr1 :: a_aNU6) (y_aOr2 :: a_aNU6) = Apply (LamCases_6989586621679203669Sym0 a_aNU6 x_aOr1 y_aOr2) (Apply (Apply CompareSym0 x_aOr1) y_aOr2)
type family LamCases_6989586621679203685_aOrk a6989586621679201626 (x6989586621679203683 :: a6989586621679201626) (y6989586621679203684 :: a6989586621679201626) a_6989586621679203687_aOrm where
  LamCases_6989586621679203685_aOrk a_aNU6 x_aOrh y_aOri 'LT = TrueSym0
  LamCases_6989586621679203685_aOrk a_aNU6 x_aOrh y_aOri 'EQ = TrueSym0
  LamCases_6989586621679203685_aOrk a_aNU6 x_aOrh y_aOri 'GT = FalseSym0
data LamCases_6989586621679203685Sym0 a6989586621679201626 (x6989586621679203683 :: a6989586621679201626) (y6989586621679203684 :: a6989586621679201626) a_69895866216792036876989586621679203688
  where
    LamCases_6989586621679203685Sym0KindInference :: SameKind (Apply (LamCases_6989586621679203685Sym0 a6989586621679201626 x6989586621679203683 y6989586621679203684) arg_aOrn) (LamCases_6989586621679203685Sym1 a6989586621679201626 x6989586621679203683 y6989586621679203684 arg_aOrn) =>
                                                      LamCases_6989586621679203685Sym0 a6989586621679201626 x6989586621679203683 y6989586621679203684 a_69895866216792036876989586621679203688
type instance Apply @_ @_ (LamCases_6989586621679203685Sym0 a6989586621679201626 x6989586621679203683 y6989586621679203684) a_69895866216792036876989586621679203688 = LamCases_6989586621679203685_aOrk a6989586621679201626 x6989586621679203683 y6989586621679203684 a_69895866216792036876989586621679203688
instance SuppressUnusedWarnings (LamCases_6989586621679203685Sym0 a6989586621679201626 x6989586621679203683 y6989586621679203684) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679203685Sym0KindInference ())
type family LamCases_6989586621679203685Sym1 a6989586621679201626 (x6989586621679203683 :: a6989586621679201626) (y6989586621679203684 :: a6989586621679201626) a_69895866216792036876989586621679203688 where
  LamCases_6989586621679203685Sym1 a6989586621679201626 x6989586621679203683 y6989586621679203684 a_69895866216792036876989586621679203688 = LamCases_6989586621679203685_aOrk a6989586621679201626 x6989586621679203683 y6989586621679203684 a_69895866216792036876989586621679203688
type TFHelper_6989586621679203676 :: forall a_aNU6. a_aNU6
                                                    -> a_aNU6 -> Bool
type family TFHelper_6989586621679203676 @a_aNU6 (a_aOrc :: a_aNU6) (a_aOrd :: a_aNU6) :: Bool where
  TFHelper_6989586621679203676 @a_aNU6 (x_aOrh :: a_aNU6) (y_aOri :: a_aNU6) = Apply (LamCases_6989586621679203685Sym0 a_aNU6 x_aOrh y_aOri) (Apply (Apply CompareSym0 x_aOrh) y_aOri)
type family LamCases_6989586621679203701_aOrA a6989586621679201626 (x6989586621679203699 :: a6989586621679201626) (y6989586621679203700 :: a6989586621679201626) a_6989586621679203703_aOrC where
  LamCases_6989586621679203701_aOrA a_aNU6 x_aOrx y_aOry 'LT = FalseSym0
  LamCases_6989586621679203701_aOrA a_aNU6 x_aOrx y_aOry 'EQ = FalseSym0
  LamCases_6989586621679203701_aOrA a_aNU6 x_aOrx y_aOry 'GT = TrueSym0
data LamCases_6989586621679203701Sym0 a6989586621679201626 (x6989586621679203699 :: a6989586621679201626) (y6989586621679203700 :: a6989586621679201626) a_69895866216792037036989586621679203704
  where
    LamCases_6989586621679203701Sym0KindInference :: SameKind (Apply (LamCases_6989586621679203701Sym0 a6989586621679201626 x6989586621679203699 y6989586621679203700) arg_aOrD) (LamCases_6989586621679203701Sym1 a6989586621679201626 x6989586621679203699 y6989586621679203700 arg_aOrD) =>
                                                      LamCases_6989586621679203701Sym0 a6989586621679201626 x6989586621679203699 y6989586621679203700 a_69895866216792037036989586621679203704
type instance Apply @_ @_ (LamCases_6989586621679203701Sym0 a6989586621679201626 x6989586621679203699 y6989586621679203700) a_69895866216792037036989586621679203704 = LamCases_6989586621679203701_aOrA a6989586621679201626 x6989586621679203699 y6989586621679203700 a_69895866216792037036989586621679203704
instance SuppressUnusedWarnings (LamCases_6989586621679203701Sym0 a6989586621679201626 x6989586621679203699 y6989586621679203700) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679203701Sym0KindInference ())
type family LamCases_6989586621679203701Sym1 a6989586621679201626 (x6989586621679203699 :: a6989586621679201626) (y6989586621679203700 :: a6989586621679201626) a_69895866216792037036989586621679203704 where
  LamCases_6989586621679203701Sym1 a6989586621679201626 x6989586621679203699 y6989586621679203700 a_69895866216792037036989586621679203704 = LamCases_6989586621679203701_aOrA a6989586621679201626 x6989586621679203699 y6989586621679203700 a_69895866216792037036989586621679203704
type TFHelper_6989586621679203692 :: forall a_aNU6. a_aNU6
                                                    -> a_aNU6 -> Bool
type family TFHelper_6989586621679203692 @a_aNU6 (a_aOrs :: a_aNU6) (a_aOrt :: a_aNU6) :: Bool where
  TFHelper_6989586621679203692 @a_aNU6 (x_aOrx :: a_aNU6) (y_aOry :: a_aNU6) = Apply (LamCases_6989586621679203701Sym0 a_aNU6 x_aOrx y_aOry) (Apply (Apply CompareSym0 x_aOrx) y_aOry)
type family LamCases_6989586621679203717_aOrQ a6989586621679201626 (x6989586621679203715 :: a6989586621679201626) (y6989586621679203716 :: a6989586621679201626) a_6989586621679203719_aOrS where
  LamCases_6989586621679203717_aOrQ a_aNU6 x_aOrN y_aOrO 'LT = FalseSym0
  LamCases_6989586621679203717_aOrQ a_aNU6 x_aOrN y_aOrO 'EQ = TrueSym0
  LamCases_6989586621679203717_aOrQ a_aNU6 x_aOrN y_aOrO 'GT = TrueSym0
data LamCases_6989586621679203717Sym0 a6989586621679201626 (x6989586621679203715 :: a6989586621679201626) (y6989586621679203716 :: a6989586621679201626) a_69895866216792037196989586621679203720
  where
    LamCases_6989586621679203717Sym0KindInference :: SameKind (Apply (LamCases_6989586621679203717Sym0 a6989586621679201626 x6989586621679203715 y6989586621679203716) arg_aOrT) (LamCases_6989586621679203717Sym1 a6989586621679201626 x6989586621679203715 y6989586621679203716 arg_aOrT) =>
                                                      LamCases_6989586621679203717Sym0 a6989586621679201626 x6989586621679203715 y6989586621679203716 a_69895866216792037196989586621679203720
type instance Apply @_ @_ (LamCases_6989586621679203717Sym0 a6989586621679201626 x6989586621679203715 y6989586621679203716) a_69895866216792037196989586621679203720 = LamCases_6989586621679203717_aOrQ a6989586621679201626 x6989586621679203715 y6989586621679203716 a_69895866216792037196989586621679203720
instance SuppressUnusedWarnings (LamCases_6989586621679203717Sym0 a6989586621679201626 x6989586621679203715 y6989586621679203716) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679203717Sym0KindInference ())
type family LamCases_6989586621679203717Sym1 a6989586621679201626 (x6989586621679203715 :: a6989586621679201626) (y6989586621679203716 :: a6989586621679201626) a_69895866216792037196989586621679203720 where
  LamCases_6989586621679203717Sym1 a6989586621679201626 x6989586621679203715 y6989586621679203716 a_69895866216792037196989586621679203720 = LamCases_6989586621679203717_aOrQ a6989586621679201626 x6989586621679203715 y6989586621679203716 a_69895866216792037196989586621679203720
type TFHelper_6989586621679203708 :: forall a_aNU6. a_aNU6
                                                    -> a_aNU6 -> Bool
type family TFHelper_6989586621679203708 @a_aNU6 (a_aOrI :: a_aNU6) (a_aOrJ :: a_aNU6) :: Bool where
  TFHelper_6989586621679203708 @a_aNU6 (x_aOrN :: a_aNU6) (y_aOrO :: a_aNU6) = Apply (LamCases_6989586621679203717Sym0 a_aNU6 x_aOrN y_aOrO) (Apply (Apply CompareSym0 x_aOrN) y_aOrO)
type family LamCases_6989586621679203733_aOs6 a6989586621679201626 (x6989586621679203731 :: a6989586621679201626) (y6989586621679203732 :: a6989586621679201626) a_6989586621679203735_aOs8 where
  LamCases_6989586621679203733_aOs6 a_aNU6 x_aOs3 y_aOs4 'True = y_aOs4
  LamCases_6989586621679203733_aOs6 a_aNU6 x_aOs3 y_aOs4 'False = x_aOs3
data LamCases_6989586621679203733Sym0 a6989586621679201626 (x6989586621679203731 :: a6989586621679201626) (y6989586621679203732 :: a6989586621679201626) a_69895866216792037356989586621679203736
  where
    LamCases_6989586621679203733Sym0KindInference :: SameKind (Apply (LamCases_6989586621679203733Sym0 a6989586621679201626 x6989586621679203731 y6989586621679203732) arg_aOs9) (LamCases_6989586621679203733Sym1 a6989586621679201626 x6989586621679203731 y6989586621679203732 arg_aOs9) =>
                                                      LamCases_6989586621679203733Sym0 a6989586621679201626 x6989586621679203731 y6989586621679203732 a_69895866216792037356989586621679203736
type instance Apply @_ @_ (LamCases_6989586621679203733Sym0 a6989586621679201626 x6989586621679203731 y6989586621679203732) a_69895866216792037356989586621679203736 = LamCases_6989586621679203733_aOs6 a6989586621679201626 x6989586621679203731 y6989586621679203732 a_69895866216792037356989586621679203736
instance SuppressUnusedWarnings (LamCases_6989586621679203733Sym0 a6989586621679201626 x6989586621679203731 y6989586621679203732) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679203733Sym0KindInference ())
type family LamCases_6989586621679203733Sym1 a6989586621679201626 (x6989586621679203731 :: a6989586621679201626) (y6989586621679203732 :: a6989586621679201626) a_69895866216792037356989586621679203736 where
  LamCases_6989586621679203733Sym1 a6989586621679201626 x6989586621679203731 y6989586621679203732 a_69895866216792037356989586621679203736 = LamCases_6989586621679203733_aOs6 a6989586621679201626 x6989586621679203731 y6989586621679203732 a_69895866216792037356989586621679203736
type Max_6989586621679203724 :: forall a_aNU6. a_aNU6
                                                -> a_aNU6 -> a_aNU6
type family Max_6989586621679203724 @a_aNU6 (a_aOrY :: a_aNU6) (a_aOrZ :: a_aNU6) :: a_aNU6 where
  Max_6989586621679203724 @a_aNU6 (x_aOs3 :: a_aNU6) (y_aOs4 :: a_aNU6) = Apply (LamCases_6989586621679203733Sym0 a_aNU6 x_aOs3 y_aOs4) (Apply (Apply (<=@#@$) x_aOs3) y_aOs4)
type family LamCases_6989586621679203749_aOsm a6989586621679201626 (x6989586621679203747 :: a6989586621679201626) (y6989586621679203748 :: a6989586621679201626) a_6989586621679203751_aOso where
  LamCases_6989586621679203749_aOsm a_aNU6 x_aOsj y_aOsk 'True = x_aOsj
  LamCases_6989586621679203749_aOsm a_aNU6 x_aOsj y_aOsk 'False = y_aOsk
data LamCases_6989586621679203749Sym0 a6989586621679201626 (x6989586621679203747 :: a6989586621679201626) (y6989586621679203748 :: a6989586621679201626) a_69895866216792037516989586621679203752
  where
    LamCases_6989586621679203749Sym0KindInference :: SameKind (Apply (LamCases_6989586621679203749Sym0 a6989586621679201626 x6989586621679203747 y6989586621679203748) arg_aOsp) (LamCases_6989586621679203749Sym1 a6989586621679201626 x6989586621679203747 y6989586621679203748 arg_aOsp) =>
                                                      LamCases_6989586621679203749Sym0 a6989586621679201626 x6989586621679203747 y6989586621679203748 a_69895866216792037516989586621679203752
type instance Apply @_ @_ (LamCases_6989586621679203749Sym0 a6989586621679201626 x6989586621679203747 y6989586621679203748) a_69895866216792037516989586621679203752 = LamCases_6989586621679203749_aOsm a6989586621679201626 x6989586621679203747 y6989586621679203748 a_69895866216792037516989586621679203752
instance SuppressUnusedWarnings (LamCases_6989586621679203749Sym0 a6989586621679201626 x6989586621679203747 y6989586621679203748) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679203749Sym0KindInference ())
type family LamCases_6989586621679203749Sym1 a6989586621679201626 (x6989586621679203747 :: a6989586621679201626) (y6989586621679203748 :: a6989586621679201626) a_69895866216792037516989586621679203752 where
  LamCases_6989586621679203749Sym1 a6989586621679201626 x6989586621679203747 y6989586621679203748 a_69895866216792037516989586621679203752 = LamCases_6989586621679203749_aOsm a6989586621679201626 x6989586621679203747 y6989586621679203748 a_69895866216792037516989586621679203752
type Min_6989586621679203740 :: forall a_aNU6. a_aNU6
                                                -> a_aNU6 -> a_aNU6
type family Min_6989586621679203740 @a_aNU6 (a_aOse :: a_aNU6) (a_aOsf :: a_aNU6) :: a_aNU6 where
  Min_6989586621679203740 @a_aNU6 (x_aOsj :: a_aNU6) (y_aOsk :: a_aNU6) = Apply (LamCases_6989586621679203749Sym0 a_aNU6 x_aOsj y_aOsk) (Apply (Apply (<=@#@$) x_aOsj) y_aOsk)
class POrd a_aNU6 where
  type family Compare (arg_aOpY :: a_aNU6) (arg_aOpZ :: a_aNU6) :: Ordering
  type family (<) (arg_aOq3 :: a_aNU6) (arg_aOq4 :: a_aNU6) :: Bool
  type family (<=) (arg_aOq8 :: a_aNU6) (arg_aOq9 :: a_aNU6) :: Bool
  type family (>) (arg_aOqd :: a_aNU6) (arg_aOqe :: a_aNU6) :: Bool
  type family (>=) (arg_aOqi :: a_aNU6) (arg_aOqj :: a_aNU6) :: Bool
  type family Max (arg_aOqn :: a_aNU6) (arg_aOqo :: a_aNU6) :: a_aNU6
  type family Min (arg_aOqs :: a_aNU6) (arg_aOqt :: a_aNU6) :: a_aNU6
  type Compare a_aOqx a_aOqy = Compare_6989586621679203639 a_aOqx a_aOqy
  type (<) a_aOqS a_aOqT = TFHelper_6989586621679203660 a_aOqS a_aOqT
  type (<=) a_aOr8 a_aOr9 = TFHelper_6989586621679203676 a_aOr8 a_aOr9
  type (>) a_aOro a_aOrp = TFHelper_6989586621679203692 a_aOro a_aOrp
  type (>=) a_aOrE a_aOrF = TFHelper_6989586621679203708 a_aOrE a_aOrF
  type Max a_aOrU a_aOrV = Max_6989586621679203724 a_aOrU a_aOrV
  type Min a_aOsa a_aOsb = Min_6989586621679203740 a_aOsa a_aOsb
  infix 4 <=
  infix 4 <
  infix 4 >
  infix 4 >=
sComparing ::
  (forall (t_aOsq :: (~>) b_aNTW a_aNTV)
          (t_aOsr :: b_aNTW)
          (t_aOss :: b_aNTW).
    SOrd a_aNTV =>
    Sing t_aOsq
    -> Sing t_aOsr
      -> Sing t_aOss
          -> Sing (Comparing t_aOsq t_aOsr t_aOss :: Ordering) :: Type)
sComparing
  (sP :: Sing p_aOpV)
  (sX :: Sing x_aOpW)
  (sY :: Sing y_aOpX)
  = applySing
      (applySing (singFun2 @CompareSym0 sCompare) (applySing sP sX))
      (applySing sP sY)
instance SOrd a_aNTV =>
          SingI (ComparingSym0 :: (~>) ((~>) b_aNTW a_aNTV) ((~>) b_aNTW ((~>) b_aNTW Ordering))) where
  sing = singFun3 @ComparingSym0 sComparing
instance (SOrd a_aNTV, SingI d_aOst) =>
          SingI (ComparingSym1 (d_aOst :: (~>) b_aNTW a_aNTV) :: (~>) b_aNTW ((~>) b_aNTW Ordering)) where
  sing
    = singFun2
        @(ComparingSym1 (d_aOst :: (~>) b_aNTW a_aNTV))
        (sComparing (sing @d_aOst))
instance SOrd a_aNTV =>
          SingI1 (ComparingSym1 :: (~>) b_aNTW a_aNTV
                                  -> (~>) b_aNTW ((~>) b_aNTW Ordering)) where
  liftSing (s_aOsz :: Sing (d_aOst :: (~>) b_aNTW a_aNTV))
    = singFun2
        @(ComparingSym1 (d_aOst :: (~>) b_aNTW a_aNTV)) (sComparing s_aOsz)
instance (SOrd a_aNTV, SingI d_aOst, SingI d_aOsu) =>
          SingI (ComparingSym2 (d_aOst :: (~>) b_aNTW a_aNTV) (d_aOsu :: b_aNTW) :: (~>) b_aNTW Ordering) where
  sing
    = singFun1
        @(ComparingSym2 (d_aOst :: (~>) b_aNTW a_aNTV) (d_aOsu :: b_aNTW))
        (sComparing (sing @d_aOst) (sing @d_aOsu))
instance (SOrd a_aNTV, SingI d_aOst) =>
          SingI1 (ComparingSym2 (d_aOst :: (~>) b_aNTW a_aNTV) :: b_aNTW
                                                                  -> (~>) b_aNTW Ordering) where
  liftSing (s_aOsw :: Sing (d_aOsu :: b_aNTW))
    = singFun1
        @(ComparingSym2 (d_aOst :: (~>) b_aNTW a_aNTV) (d_aOsu :: b_aNTW))
        (sComparing (sing @d_aOst) s_aOsw)
instance SOrd a_aNTV =>
          SingI2 (ComparingSym2 :: (~>) b_aNTW a_aNTV
                                  -> b_aNTW -> (~>) b_aNTW Ordering) where
  liftSing2
    (s_aOsx :: Sing (d_aOst :: (~>) b_aNTW a_aNTV))
    (s_aOsy :: Sing (d_aOsu :: b_aNTW))
    = singFun1
        @(ComparingSym2 (d_aOst :: (~>) b_aNTW a_aNTV) (d_aOsu :: b_aNTW))
        (sComparing s_aOsx s_aOsy)
class SEq a_aNU6 => SOrd a_aNU6 where
  sCompare ::
    (forall (t_aOsA :: a_aNU6) (t_aOsB :: a_aNU6).
      Sing t_aOsA
      -> Sing t_aOsB -> Sing (Compare t_aOsA t_aOsB :: Ordering) :: Type)
  (%<) ::
    (forall (t_aOsF :: a_aNU6) (t_aOsG :: a_aNU6).
      Sing t_aOsF
      -> Sing t_aOsG -> Sing ((<) t_aOsF t_aOsG :: Bool) :: Type)
  (%<=) ::
    (forall (t_aOsK :: a_aNU6) (t_aOsL :: a_aNU6).
      Sing t_aOsK
      -> Sing t_aOsL -> Sing ((<=) t_aOsK t_aOsL :: Bool) :: Type)
  (%>) ::
    (forall (t_aOsP :: a_aNU6) (t_aOsQ :: a_aNU6).
      Sing t_aOsP
      -> Sing t_aOsQ -> Sing ((>) t_aOsP t_aOsQ :: Bool) :: Type)
  (%>=) ::
    (forall (t_aOsU :: a_aNU6) (t_aOsV :: a_aNU6).
      Sing t_aOsU
      -> Sing t_aOsV -> Sing ((>=) t_aOsU t_aOsV :: Bool) :: Type)
  sMax ::
    (forall (t_aOsZ :: a_aNU6) (t_aOt0 :: a_aNU6).
      Sing t_aOsZ
      -> Sing t_aOt0 -> Sing (Max t_aOsZ t_aOt0 :: a_aNU6) :: Type)
  sMin ::
    (forall (t_aOt4 :: a_aNU6) (t_aOt5 :: a_aNU6).
      Sing t_aOt4
      -> Sing t_aOt5 -> Sing (Min t_aOt4 t_aOt5 :: a_aNU6) :: Type)
  infix 4 %<=
  infix 4 %<
  infix 4 %>
  infix 4 %>=
  default sCompare ::
            (forall (t_aOsA :: a_aNU6) (t_aOsB :: a_aNU6).
              ((Compare t_aOsA t_aOsB :: Ordering)
              ~ Compare_6989586621679203639 t_aOsA t_aOsB) =>
              Sing t_aOsA
              -> Sing t_aOsB -> Sing (Compare t_aOsA t_aOsB :: Ordering) :: Type)
  default (%<) ::
            (forall (t_aOsF :: a_aNU6) (t_aOsG :: a_aNU6).
              (((<) t_aOsF t_aOsG :: Bool)
              ~ TFHelper_6989586621679203660 t_aOsF t_aOsG) =>
              Sing t_aOsF
              -> Sing t_aOsG -> Sing ((<) t_aOsF t_aOsG :: Bool) :: Type)
  default (%<=) ::
            (forall (t_aOsK :: a_aNU6) (t_aOsL :: a_aNU6).
              (((<=) t_aOsK t_aOsL :: Bool)
              ~ TFHelper_6989586621679203676 t_aOsK t_aOsL) =>
              Sing t_aOsK
              -> Sing t_aOsL -> Sing ((<=) t_aOsK t_aOsL :: Bool) :: Type)
  default (%>) ::
            (forall (t_aOsP :: a_aNU6) (t_aOsQ :: a_aNU6).
              (((>) t_aOsP t_aOsQ :: Bool)
              ~ TFHelper_6989586621679203692 t_aOsP t_aOsQ) =>
              Sing t_aOsP
              -> Sing t_aOsQ -> Sing ((>) t_aOsP t_aOsQ :: Bool) :: Type)
  default (%>=) ::
            (forall (t_aOsU :: a_aNU6) (t_aOsV :: a_aNU6).
              (((>=) t_aOsU t_aOsV :: Bool)
              ~ TFHelper_6989586621679203708 t_aOsU t_aOsV) =>
              Sing t_aOsU
              -> Sing t_aOsV -> Sing ((>=) t_aOsU t_aOsV :: Bool) :: Type)
  default sMax ::
            (forall (t_aOsZ :: a_aNU6) (t_aOt0 :: a_aNU6).
              ((Max t_aOsZ t_aOt0 :: a_aNU6)
              ~ Max_6989586621679203724 t_aOsZ t_aOt0) =>
              Sing t_aOsZ
              -> Sing t_aOt0 -> Sing (Max t_aOsZ t_aOt0 :: a_aNU6) :: Type)
  default sMin ::
            (forall (t_aOt4 :: a_aNU6) (t_aOt5 :: a_aNU6).
              ((Min t_aOt4 t_aOt5 :: a_aNU6)
              ~ Min_6989586621679203740 t_aOt4 t_aOt5) =>
              Sing t_aOt4
              -> Sing t_aOt5 -> Sing (Min t_aOt4 t_aOt5 :: a_aNU6) :: Type)
  sCompare (sX :: Sing x_aOqG) (sY :: Sing y_aOqH)
    = applySing
        (singFun1
            @(LamCases_6989586621679203648Sym0 a_aNU6 x_aOqG y_aOqH)
            (\cases
              STrue -> SEQ
              SFalse
                -> applySing
                      (singFun1
                        @(LamCases_6989586621679203650Sym0 a_aNU6 x_aOqG y_aOqH)
                        (\cases
                            STrue -> SLT
                            SFalse -> SGT))
                      (applySing (applySing (singFun2 @(<=@#@$) (%<=)) sX) sY)))
        (applySing (applySing (singFun2 @(==@#@$) (%==)) sX) sY)
  (%<) (sX :: Sing x_aOr1) (sY :: Sing y_aOr2)
    = applySing
        (singFun1
            @(LamCases_6989586621679203669Sym0 a_aNU6 x_aOr1 y_aOr2)
            (\cases
              SLT -> STrue
              SEQ -> SFalse
              SGT -> SFalse))
        (applySing (applySing (singFun2 @CompareSym0 sCompare) sX) sY)
  (%<=) (sX :: Sing x_aOrh) (sY :: Sing y_aOri)
    = applySing
        (singFun1
            @(LamCases_6989586621679203685Sym0 a_aNU6 x_aOrh y_aOri)
            (\cases
              SLT -> STrue
              SEQ -> STrue
              SGT -> SFalse))
        (applySing (applySing (singFun2 @CompareSym0 sCompare) sX) sY)
  (%>) (sX :: Sing x_aOrx) (sY :: Sing y_aOry)
    = applySing
        (singFun1
            @(LamCases_6989586621679203701Sym0 a_aNU6 x_aOrx y_aOry)
            (\cases
              SLT -> SFalse
              SEQ -> SFalse
              SGT -> STrue))
        (applySing (applySing (singFun2 @CompareSym0 sCompare) sX) sY)
  (%>=) (sX :: Sing x_aOrN) (sY :: Sing y_aOrO)
    = applySing
        (singFun1
            @(LamCases_6989586621679203717Sym0 a_aNU6 x_aOrN y_aOrO)
            (\cases
              SLT -> SFalse
              SEQ -> STrue
              SGT -> STrue))
        (applySing (applySing (singFun2 @CompareSym0 sCompare) sX) sY)
  sMax (sX :: Sing x_aOs3) (sY :: Sing y_aOs4)
    = applySing
        (singFun1
            @(LamCases_6989586621679203733Sym0 a_aNU6 x_aOs3 y_aOs4)
            (\cases
              STrue -> sY
              SFalse -> sX))
        (applySing (applySing (singFun2 @(<=@#@$) (%<=)) sX) sY)
  sMin (sX :: Sing x_aOsj) (sY :: Sing y_aOsk)
    = applySing
        (singFun1
            @(LamCases_6989586621679203749Sym0 a_aNU6 x_aOsj y_aOsk)
            (\cases
              STrue -> sX
              SFalse -> sY))
        (applySing (applySing (singFun2 @(<=@#@$) (%<=)) sX) sY)
instance SOrd a_aNU6 =>
          SingI (CompareSym0 :: (~>) a_aNU6 ((~>) a_aNU6 Ordering)) where
  sing = singFun2 @CompareSym0 sCompare
instance (SOrd a_aNU6, SingI d_aOsC) =>
          SingI (CompareSym1 (d_aOsC :: a_aNU6) :: (~>) a_aNU6 Ordering) where
  sing
    = singFun1
        @(CompareSym1 (d_aOsC :: a_aNU6)) (sCompare (sing @d_aOsC))
instance SOrd a_aNU6 =>
          SingI1 (CompareSym1 :: a_aNU6 -> (~>) a_aNU6 Ordering) where
  liftSing (s_aOsE :: Sing (d_aOsC :: a_aNU6))
    = singFun1 @(CompareSym1 (d_aOsC :: a_aNU6)) (sCompare s_aOsE)
instance SOrd a_aNU6 =>
          SingI ((<@#@$) :: (~>) a_aNU6 ((~>) a_aNU6 Bool)) where
  sing = singFun2 @(<@#@$) (%<)
instance (SOrd a_aNU6, SingI d_aOsH) =>
          SingI ((<@#@$$) (d_aOsH :: a_aNU6) :: (~>) a_aNU6 Bool) where
  sing
    = singFun1 @((<@#@$$) (d_aOsH :: a_aNU6)) ((%<) (sing @d_aOsH))
instance SOrd a_aNU6 =>
          SingI1 ((<@#@$$) :: a_aNU6 -> (~>) a_aNU6 Bool) where
  liftSing (s_aOsJ :: Sing (d_aOsH :: a_aNU6))
    = singFun1 @((<@#@$$) (d_aOsH :: a_aNU6)) ((%<) s_aOsJ)
instance SOrd a_aNU6 =>
          SingI ((<=@#@$) :: (~>) a_aNU6 ((~>) a_aNU6 Bool)) where
  sing = singFun2 @(<=@#@$) (%<=)
instance (SOrd a_aNU6, SingI d_aOsM) =>
          SingI ((<=@#@$$) (d_aOsM :: a_aNU6) :: (~>) a_aNU6 Bool) where
  sing
    = singFun1 @((<=@#@$$) (d_aOsM :: a_aNU6)) ((%<=) (sing @d_aOsM))
instance SOrd a_aNU6 =>
          SingI1 ((<=@#@$$) :: a_aNU6 -> (~>) a_aNU6 Bool) where
  liftSing (s_aOsO :: Sing (d_aOsM :: a_aNU6))
    = singFun1 @((<=@#@$$) (d_aOsM :: a_aNU6)) ((%<=) s_aOsO)
instance SOrd a_aNU6 =>
          SingI ((>@#@$) :: (~>) a_aNU6 ((~>) a_aNU6 Bool)) where
  sing = singFun2 @(>@#@$) (%>)
instance (SOrd a_aNU6, SingI d_aOsR) =>
          SingI ((>@#@$$) (d_aOsR :: a_aNU6) :: (~>) a_aNU6 Bool) where
  sing
    = singFun1 @((>@#@$$) (d_aOsR :: a_aNU6)) ((%>) (sing @d_aOsR))
instance SOrd a_aNU6 =>
          SingI1 ((>@#@$$) :: a_aNU6 -> (~>) a_aNU6 Bool) where
  liftSing (s_aOsT :: Sing (d_aOsR :: a_aNU6))
    = singFun1 @((>@#@$$) (d_aOsR :: a_aNU6)) ((%>) s_aOsT)
instance SOrd a_aNU6 =>
          SingI ((>=@#@$) :: (~>) a_aNU6 ((~>) a_aNU6 Bool)) where
  sing = singFun2 @(>=@#@$) (%>=)
instance (SOrd a_aNU6, SingI d_aOsW) =>
          SingI ((>=@#@$$) (d_aOsW :: a_aNU6) :: (~>) a_aNU6 Bool) where
  sing
    = singFun1 @((>=@#@$$) (d_aOsW :: a_aNU6)) ((%>=) (sing @d_aOsW))
instance SOrd a_aNU6 =>
          SingI1 ((>=@#@$$) :: a_aNU6 -> (~>) a_aNU6 Bool) where
  liftSing (s_aOsY :: Sing (d_aOsW :: a_aNU6))
    = singFun1 @((>=@#@$$) (d_aOsW :: a_aNU6)) ((%>=) s_aOsY)
instance SOrd a_aNU6 =>
          SingI (MaxSym0 :: (~>) a_aNU6 ((~>) a_aNU6 a_aNU6)) where
  sing = singFun2 @MaxSym0 sMax
instance (SOrd a_aNU6, SingI d_aOt1) =>
          SingI (MaxSym1 (d_aOt1 :: a_aNU6) :: (~>) a_aNU6 a_aNU6) where
  sing = singFun1 @(MaxSym1 (d_aOt1 :: a_aNU6)) (sMax (sing @d_aOt1))
instance SOrd a_aNU6 =>
          SingI1 (MaxSym1 :: a_aNU6 -> (~>) a_aNU6 a_aNU6) where
  liftSing (s_aOt3 :: Sing (d_aOt1 :: a_aNU6))
    = singFun1 @(MaxSym1 (d_aOt1 :: a_aNU6)) (sMax s_aOt3)
instance SOrd a_aNU6 =>
          SingI (MinSym0 :: (~>) a_aNU6 ((~>) a_aNU6 a_aNU6)) where
  sing = singFun2 @MinSym0 sMin
instance (SOrd a_aNU6, SingI d_aOt6) =>
          SingI (MinSym1 (d_aOt6 :: a_aNU6) :: (~>) a_aNU6 a_aNU6) where
  sing = singFun1 @(MinSym1 (d_aOt6 :: a_aNU6)) (sMin (sing @d_aOt6))
instance SOrd a_aNU6 =>
          SingI1 (MinSym1 :: a_aNU6 -> (~>) a_aNU6 a_aNU6) where
  liftSing (s_aOt8 :: Sing (d_aOt6 :: a_aNU6))
    = singFun1 @(MinSym1 (d_aOt6 :: a_aNU6)) (sMin s_aOt8)

type DownSym0 :: forall (a_aOpE :: Type). (~>) a_aOpE (Down a_aOpE)
data DownSym0 :: (~>) a_aOpE (Down a_aOpE)
  where
    DownSym0KindInference :: SameKind (Apply DownSym0 arg_aQGB) (DownSym1 arg_aQGB) =>
                              DownSym0 a6989586621679212322
type instance Apply @a_aOpE @(Down a_aOpE) DownSym0 a6989586621679212322 = 'Down a6989586621679212322
instance SuppressUnusedWarnings DownSym0 where
  suppressUnusedWarnings = snd ((,) DownSym0KindInference ())
type DownSym1 :: forall (a_aOpE :: Type). a_aOpE -> Down a_aOpE
type family DownSym1 @(a_aOpE :: Type) (a6989586621679212322 :: a_aOpE) :: Down a_aOpE where
  DownSym1 a6989586621679212322 = 'Down a6989586621679212322
type GetDownSym0 :: forall (a_aOpE :: Type). (~>) (Down a_aOpE) a_aOpE
data GetDownSym0 :: (~>) (Down a_aOpE) a_aOpE
  where
    GetDownSym0KindInference :: SameKind (Apply GetDownSym0 arg_aQGE) (GetDownSym1 arg_aQGE) =>
                                GetDownSym0 a6989586621679212325
type instance Apply @(Down a_aOpE) @a_aOpE GetDownSym0 a6989586621679212325 = GetDown a6989586621679212325
instance SuppressUnusedWarnings GetDownSym0 where
  suppressUnusedWarnings = snd ((,) GetDownSym0KindInference ())
type GetDownSym1 :: forall (a_aOpE :: Type). Down a_aOpE -> a_aOpE
type family GetDownSym1 @(a_aOpE :: Type) (a6989586621679212325 :: Down a_aOpE) :: a_aOpE where
  GetDownSym1 a6989586621679212325 = GetDown a6989586621679212325
type GetDown :: forall (a_aOpE :: Type). Down a_aOpE -> a_aOpE
type family GetDown @(a_aOpE :: Type) (a_aQGD :: Down a_aOpE) :: a_aOpE where
  GetDown @a_aOpE ('Down field_aQGG :: Down a_aOpE) = field_aQGG
sGetDown ::
  forall (a_aOpE :: Type) (t_aQGH :: Down a_aOpE). Sing t_aQGH
                                                    -> Sing (GetDown t_aQGH :: a_aOpE)
sGetDown (SDown (sField :: Sing field_aQGG)) = sField
instance SingI (GetDownSym0 :: (~>) (Down a_aOpE) a_aOpE) where
  sing = singFun1 @GetDownSym0 sGetDown
type SDown :: forall (a_aOpE :: Type). Down a_aOpE -> Type
data SDown :: forall (a_aOpE :: Type). Down a_aOpE -> Type
  where
    SDown :: forall (a_aOpE :: Type) (n_aQGJ :: a_aOpE).
              (Sing n_aQGJ) -> SDown ('Down n_aQGJ :: Down a_aOpE)
type instance Sing @(Down a_aOpE) = SDown
instance SingKind a_aOpE => SingKind (Down a_aOpE) where
  type Demote (Down a_aOpE) = Down (Demote a_aOpE)
  fromSing (SDown b_aQGL) = Down (fromSing b_aQGL)
  toSing (Down (b_aQGN :: Demote a_aOpE))
    = (\cases (SomeSing c_aQGO) -> SomeSing (SDown c_aQGO))
        (toSing b_aQGN :: SomeSing a_aOpE)
instance SingI n_aQGJ => SingI ('Down (n_aQGJ :: a_aOpE)) where
  sing = SDown sing
instance SingI1 'Down where
  liftSing = SDown
instance SingI (DownSym0 :: (~>) a_aOpE (Down a_aOpE)) where
  sing = singFun1 @DownSym0 SDown

type TFHelper_6989586621679215099 :: forall a_aQWZ. Down a_aQWZ
                                                        -> Down a_aQWZ -> Bool
type family TFHelper_6989586621679215099 @a_aQWZ (a_aRpr :: Down a_aQWZ) (a_aRps :: Down a_aQWZ) :: Bool where
  TFHelper_6989586621679215099 @a_aQWZ ('Down a_6989586621679214835_aRpw :: Down a_aQWZ) ('Down b_6989586621679214837_aRpx :: Down a_aQWZ) = Apply (Apply (==@#@$) a_6989586621679214835_aRpw) b_6989586621679214837_aRpx
instance PEq (Down a_aQWZ) where
  type (==) a_aRpn a_aRpo = TFHelper_6989586621679215099 a_aRpn a_aRpo
type Compare_6989586621679215110 :: forall a_aQX0. Down a_aQX0
                                                    -> Down a_aQX0 -> Ordering
type family Compare_6989586621679215110 @a_aQX0 (a_aRpC :: Down a_aQX0) (a_aRpD :: Down a_aQX0) :: Ordering where
  Compare_6989586621679215110 @a_aQX0 ('Down x_aRpH :: Down a_aQX0) ('Down y_aRpI :: Down a_aQX0) = Apply (Apply CompareSym0 y_aRpI) x_aRpH
instance POrd (Down a_aQX0) where
  type Compare a_aRpy a_aRpz = Compare_6989586621679215110 a_aRpy a_aRpz
type TFHelper_6989586621679215289 :: forall a_aQX3. Down a_aQX3
                                                    -> Down a_aQX3 -> Down a_aQX3
type family TFHelper_6989586621679215289 @a_aQX3 (a_aRsv :: Down a_aQX3) (a_aRsw :: Down a_aQX3) :: Down a_aQX3 where
  TFHelper_6989586621679215289 @a_aQX3 ('Down a_aRsA :: Down a_aQX3) ('Down b_aRsB :: Down a_aQX3) = Apply DownSym0 (Apply (Apply (<>@#@$) a_aRsA) b_aRsB)
instance PSemigroup (Down a_aQX3) where
  type (<>) a_aRsr a_aRss = TFHelper_6989586621679215289 a_aRsr a_aRss
instance SEq a_aQWZ => SEq (Down a_aQWZ) where
  (%==)
    (SDown (sA_6989586621679214835 :: Sing a_6989586621679214835_aRpw))
    (SDown (sB_6989586621679214837 :: Sing b_6989586621679214837_aRpx))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679214835)
        sB_6989586621679214837
instance SOrd a_aQX0 => SOrd (Down a_aQX0) where
  sCompare (SDown (sX :: Sing x_aRpH)) (SDown (sY :: Sing y_aRpI))
    = applySing (applySing (singFun2 @CompareSym0 sCompare) sY) sX
instance SSemigroup a_aQX3 => SSemigroup (Down a_aQX3) where
  (%<>) (SDown (sA :: Sing a_aRsA)) (SDown (sB :: Sing b_aRsB))
    = applySing
        (singFun1 @DownSym0 SDown)
        (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sA) sB)
instance SDecide a_aQWZ => SDecide (Down a_aQWZ) where
  (%~) (SDown a_aRsG) (SDown b_aRsH)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_aRsI)
            -> Disproved (\cases Refl -> contra_aRsI Refl))
        ((%~) a_aRsG b_aRsH)
instance Eq (SDown (z_aRsJ :: Down a_aQWZ)) where
  (==) _ _ = True
instance SDecide a_aQWZ =>
          Data.Type.Equality.TestEquality (SDown :: Down a_aQWZ
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_aQWZ =>
          Data.Type.Coercion.TestCoercion (SDown :: Down a_aQWZ
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion

type Compare_6989586621679216434 :: forall a_11. Maybe a_11
                                                     -> Maybe a_11 -> Ordering
type family Compare_6989586621679216434 @a_11 (a_aRKY :: Maybe a_11) (a_aRKZ :: Maybe a_11) :: Ordering where
  Compare_6989586621679216434 @a_11 ('Nothing :: Maybe a_11) ('Nothing :: Maybe a_11) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) NilSym0
  Compare_6989586621679216434 @a_11 ('Just a_6989586621679216428_aRL3 :: Maybe a_11) ('Just b_6989586621679216430_aRL4 :: Maybe a_11) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679216428_aRL3) b_6989586621679216430_aRL4)) NilSym0)
  Compare_6989586621679216434 @a_11 ('Nothing :: Maybe a_11) ('Just _ :: Maybe a_11) = LTSym0
  Compare_6989586621679216434 @a_11 ('Just _ :: Maybe a_11) ('Nothing :: Maybe a_11) = GTSym0
instance POrd (Maybe a_11) where
  type Compare a_aRKU a_aRKV = Compare_6989586621679216434 a_aRKU a_aRKV
instance SOrd a_11 => SOrd (Maybe a_11) where
  sCompare SNothing SNothing
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        SNil
  sCompare
    (SJust (sA_6989586621679216428 :: Sing a_6989586621679216428_aRL3))
    (SJust (sB_6989586621679216430 :: Sing b_6989586621679216430_aRL4))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679216428)
                  sB_6989586621679216430))
            SNil)
  sCompare SNothing (SJust _) = SLT
  sCompare (SJust _) SNothing = SGT
type Compare_6989586621679217060 :: forall a_11. [a_11]
                                                  -> [a_11] -> Ordering
type family Compare_6989586621679217060 @a_11 (a_aRV4 :: [a_11]) (a_aRV5 :: [a_11]) :: Ordering where
  Compare_6989586621679217060 @a_11 ('[] :: [a_11]) ('[] :: [a_11]) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) NilSym0
  Compare_6989586621679217060 @a_11 ('(:) a_6989586621679217050_aRV9 a_6989586621679217052_aRVa :: [a_11]) ('(:) b_6989586621679217054_aRVb b_6989586621679217056_aRVc :: [a_11]) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217050_aRV9) b_6989586621679217054_aRVb)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217052_aRVa) b_6989586621679217056_aRVc)) NilSym0))
  Compare_6989586621679217060 @a_11 ('[] :: [a_11]) ('(:) _ _ :: [a_11]) = LTSym0
  Compare_6989586621679217060 @a_11 ('(:) _ _ :: [a_11]) ('[] :: [a_11]) = GTSym0
instance POrd [a_11] where
  type Compare a_aRV0 a_aRV1 = Compare_6989586621679217060 a_aRV0 a_aRV1
instance (SOrd a_11, SOrd [a_11]) => SOrd [a_11] where
  sCompare SNil SNil
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        SNil
  sCompare
    (SCons (sA_6989586621679217050 :: Sing a_6989586621679217050_aRV9)
            (sA_6989586621679217052 :: Sing a_6989586621679217052_aRVa))
    (SCons (sB_6989586621679217054 :: Sing b_6989586621679217054_aRVb)
            (sB_6989586621679217056 :: Sing b_6989586621679217056_aRVc))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217050)
                  sB_6989586621679217054))
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing
                    (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217052)
                    sB_6989586621679217056))
              SNil))
  sCompare SNil (SCons _ _) = SLT
  sCompare (SCons _ _) SNil = SGT
type Compare_6989586621679217101 :: forall a_a8ep
                                            b_a8eq. Either a_a8ep b_a8eq
                                                    -> Either a_a8ep b_a8eq -> Ordering
type family Compare_6989586621679217101 @a_a8ep @b_a8eq (a_aRVJ :: Either a_a8ep b_a8eq) (a_aRVK :: Either a_a8ep b_a8eq) :: Ordering where
  Compare_6989586621679217101 @a_a8ep @b_a8eq ('Left a_6989586621679217091_aRVO :: Either a_a8ep b_a8eq) ('Left b_6989586621679217093_aRVP :: Either a_a8ep b_a8eq) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217091_aRVO) b_6989586621679217093_aRVP)) NilSym0)
  Compare_6989586621679217101 @a_a8ep @b_a8eq ('Right a_6989586621679217095_aRVQ :: Either a_a8ep b_a8eq) ('Right b_6989586621679217097_aRVR :: Either a_a8ep b_a8eq) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217095_aRVQ) b_6989586621679217097_aRVR)) NilSym0)
  Compare_6989586621679217101 @a_a8ep @b_a8eq ('Left _ :: Either a_a8ep b_a8eq) ('Right _ :: Either a_a8ep b_a8eq) = LTSym0
  Compare_6989586621679217101 @a_a8ep @b_a8eq ('Right _ :: Either a_a8ep b_a8eq) ('Left _ :: Either a_a8ep b_a8eq) = GTSym0
instance POrd (Either a_a8ep b_a8eq) where
  type Compare a_aRVF a_aRVG = Compare_6989586621679217101 a_aRVF a_aRVG
instance (SOrd a_a8ep, SOrd b_a8eq) =>
          SOrd (Either a_a8ep b_a8eq) where
  sCompare
    (SLeft (sA_6989586621679217091 :: Sing a_6989586621679217091_aRVO))
    (SLeft (sB_6989586621679217093 :: Sing b_6989586621679217093_aRVP))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217091)
                  sB_6989586621679217093))
            SNil)
  sCompare
    (SRight (sA_6989586621679217095 :: Sing a_6989586621679217095_aRVQ))
    (SRight (sB_6989586621679217097 :: Sing b_6989586621679217097_aRVR))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217095)
                  sB_6989586621679217097))
            SNil)
  sCompare (SLeft _) (SRight _) = SLT
  sCompare (SRight _) (SLeft _) = SGT
type Compare_6989586621679217125 :: forall a_a8fb. NonEmpty a_a8fb
                                                    -> NonEmpty a_a8fb -> Ordering
type family Compare_6989586621679217125 @a_a8fb (a_aRW7 :: NonEmpty a_a8fb) (a_aRW8 :: NonEmpty a_a8fb) :: Ordering where
  Compare_6989586621679217125 @a_a8fb ('(:|) a_6989586621679217115_aRWc a_6989586621679217117_aRWd :: NonEmpty a_a8fb) ('(:|) b_6989586621679217119_aRWe b_6989586621679217121_aRWf :: NonEmpty a_a8fb) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217115_aRWc) b_6989586621679217119_aRWe)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217117_aRWd) b_6989586621679217121_aRWf)) NilSym0))
instance POrd (NonEmpty a_a8fb) where
  type Compare a_aRW3 a_aRW4 = Compare_6989586621679217125 a_aRW3 a_aRW4
instance (SOrd a_a8fb, SOrd [a_a8fb]) =>
          SOrd (NonEmpty a_a8fb) where
  sCompare
    ((:%|) (sA_6989586621679217115 :: Sing a_6989586621679217115_aRWc)
            (sA_6989586621679217117 :: Sing a_6989586621679217117_aRWd))
    ((:%|) (sB_6989586621679217119 :: Sing b_6989586621679217119_aRWe)
            (sB_6989586621679217121 :: Sing b_6989586621679217121_aRWf))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217115)
                  sB_6989586621679217119))
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing
                    (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217117)
                    sB_6989586621679217121))
              SNil))
type Compare_6989586621679217138 :: Void -> Void -> Ordering
type family Compare_6989586621679217138 (a_aRWk :: Void) (a_aRWl :: Void) :: Ordering where
  Compare_6989586621679217138 _ _ = EQSym0
instance POrd Void where
  type Compare a_aRWg a_aRWh = Compare_6989586621679217138 a_aRWg a_aRWh
instance SOrd Void where
  sCompare _ _ = SEQ
type Compare_6989586621679217161 :: forall a_11 b_12. (a_11, b_12)
                                                      -> (a_11, b_12) -> Ordering
type family Compare_6989586621679217161 @a_11 @b_12 (a_aRWH :: (a_11,
                                                                b_12)) (a_aRWI :: (a_11,
                                                                                    b_12)) :: Ordering where
  Compare_6989586621679217161 @a_11 @b_12 ('(a_6989586621679217151_aRWM,
                                              a_6989586621679217153_aRWN) :: (a_11,
                                                                              b_12)) ('(b_6989586621679217155_aRWO,
                                                                                        b_6989586621679217157_aRWP) :: (a_11,
                                                                                                                        b_12)) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217151_aRWM) b_6989586621679217155_aRWO)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217153_aRWN) b_6989586621679217157_aRWP)) NilSym0))
instance POrd (a_11, b_12) where
  type Compare a_aRWD a_aRWE = Compare_6989586621679217161 a_aRWD a_aRWE
instance (SOrd a_11, SOrd b_12) => SOrd (a_11, b_12) where
  sCompare
    (STuple2 (sA_6989586621679217151 :: Sing a_6989586621679217151_aRWM)
              (sA_6989586621679217153 :: Sing a_6989586621679217153_aRWN))
    (STuple2 (sB_6989586621679217155 :: Sing b_6989586621679217155_aRWO)
              (sB_6989586621679217157 :: Sing b_6989586621679217157_aRWP))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217151)
                  sB_6989586621679217155))
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing
                    (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217153)
                    sB_6989586621679217157))
              SNil))
type Compare_6989586621679217195 :: forall a_11 b_12 c_13. (a_11,
                                                            b_12, c_13)
                                                            -> (a_11, b_12, c_13) -> Ordering
type family Compare_6989586621679217195 @a_11 @b_12 @c_13 (a_aRXf :: (a_11,
                                                                      b_12,
                                                                      c_13)) (a_aRXg :: (a_11,
                                                                                          b_12,
                                                                                          c_13)) :: Ordering where
  Compare_6989586621679217195 @a_11 @b_12 @c_13 ('(a_6989586621679217181_aRXk,
                                                    a_6989586621679217183_aRXl,
                                                    a_6989586621679217185_aRXm) :: (a_11, b_12,
                                                                                    c_13)) ('(b_6989586621679217187_aRXn,
                                                                                              b_6989586621679217189_aRXo,
                                                                                              b_6989586621679217191_aRXp) :: (a_11,
                                                                                                                              b_12,
                                                                                                                              c_13)) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217181_aRXk) b_6989586621679217187_aRXn)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217183_aRXl) b_6989586621679217189_aRXo)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217185_aRXm) b_6989586621679217191_aRXp)) NilSym0)))
instance POrd (a_11, b_12, c_13) where
  type Compare a_aRXb a_aRXc = Compare_6989586621679217195 a_aRXb a_aRXc
instance (SOrd a_11, SOrd b_12, SOrd c_13) =>
          SOrd (a_11, b_12, c_13) where
  sCompare
    (STuple3 (sA_6989586621679217181 :: Sing a_6989586621679217181_aRXk)
              (sA_6989586621679217183 :: Sing a_6989586621679217183_aRXl)
              (sA_6989586621679217185 :: Sing a_6989586621679217185_aRXm))
    (STuple3 (sB_6989586621679217187 :: Sing b_6989586621679217187_aRXn)
              (sB_6989586621679217189 :: Sing b_6989586621679217189_aRXo)
              (sB_6989586621679217191 :: Sing b_6989586621679217191_aRXp))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217181)
                  sB_6989586621679217187))
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing
                    (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217183)
                    sB_6989586621679217189))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing
                        (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217185)
                        sB_6989586621679217191))
                  SNil)))
type Compare_6989586621679217238 :: forall a_11
                                            b_12
                                            c_13
                                            d_14. (a_11, b_12, c_13, d_14)
                                                  -> (a_11, b_12, c_13, d_14) -> Ordering
type family Compare_6989586621679217238 @a_11 @b_12 @c_13 @d_14 (a_aRXW :: (a_11,
                                                                            b_12, c_13,
                                                                            d_14)) (a_aRXX :: (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14)) :: Ordering where
  Compare_6989586621679217238 @a_11 @b_12 @c_13 @d_14 ('(a_6989586621679217220_aRY1,
                                                          a_6989586621679217222_aRY2,
                                                          a_6989586621679217224_aRY3,
                                                          a_6989586621679217226_aRY4) :: (a_11,
                                                                                          b_12,
                                                                                          c_13,
                                                                                          d_14)) ('(b_6989586621679217228_aRY5,
                                                                                                    b_6989586621679217230_aRY6,
                                                                                                    b_6989586621679217232_aRY7,
                                                                                                    b_6989586621679217234_aRY8) :: (a_11,
                                                                                                                                    b_12,
                                                                                                                                    c_13,
                                                                                                                                    d_14)) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217220_aRY1) b_6989586621679217228_aRY5)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217222_aRY2) b_6989586621679217230_aRY6)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217224_aRY3) b_6989586621679217232_aRY7)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217226_aRY4) b_6989586621679217234_aRY8)) NilSym0))))
instance POrd (a_11, b_12, c_13, d_14) where
  type Compare a_aRXS a_aRXT = Compare_6989586621679217238 a_aRXS a_aRXT
instance (SOrd a_11, SOrd b_12, SOrd c_13, SOrd d_14) =>
          SOrd (a_11, b_12, c_13, d_14) where
  sCompare
    (STuple4 (sA_6989586621679217220 :: Sing a_6989586621679217220_aRY1)
              (sA_6989586621679217222 :: Sing a_6989586621679217222_aRY2)
              (sA_6989586621679217224 :: Sing a_6989586621679217224_aRY3)
              (sA_6989586621679217226 :: Sing a_6989586621679217226_aRY4))
    (STuple4 (sB_6989586621679217228 :: Sing b_6989586621679217228_aRY5)
              (sB_6989586621679217230 :: Sing b_6989586621679217230_aRY6)
              (sB_6989586621679217232 :: Sing b_6989586621679217232_aRY7)
              (sB_6989586621679217234 :: Sing b_6989586621679217234_aRY8))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217220)
                  sB_6989586621679217228))
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing
                    (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217222)
                    sB_6989586621679217230))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing
                        (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217224)
                        sB_6989586621679217232))
                  (applySing
                    (applySing
                        (singFun2 @(:@#@$) SCons)
                        (applySing
                          (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217226)
                          sB_6989586621679217234))
                    SNil))))
type Compare_6989586621679217290 :: forall a_11
                                            b_12
                                            c_13
                                            d_14
                                            e_15. (a_11, b_12, c_13, d_14, e_15)
                                                  -> (a_11, b_12, c_13, d_14, e_15) -> Ordering
type family Compare_6989586621679217290 @a_11 @b_12 @c_13 @d_14 @e_15 (a_aRYM :: (a_11,
                                                                                  b_12, c_13,
                                                                                  d_14,
                                                                                  e_15)) (a_aRYN :: (a_11,
                                                                                                      b_12,
                                                                                                      c_13,
                                                                                                      d_14,
                                                                                                      e_15)) :: Ordering where
  Compare_6989586621679217290 @a_11 @b_12 @c_13 @d_14 @e_15 ('(a_6989586621679217268_aRYR,
                                                                a_6989586621679217270_aRYS,
                                                                a_6989586621679217272_aRYT,
                                                                a_6989586621679217274_aRYU,
                                                                a_6989586621679217276_aRYV) :: (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14,
                                                                                                e_15)) ('(b_6989586621679217278_aRYW,
                                                                                                          b_6989586621679217280_aRYX,
                                                                                                          b_6989586621679217282_aRYY,
                                                                                                          b_6989586621679217284_aRYZ,
                                                                                                          b_6989586621679217286_aRZ0) :: (a_11,
                                                                                                                                          b_12,
                                                                                                                                          c_13,
                                                                                                                                          d_14,
                                                                                                                                          e_15)) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217268_aRYR) b_6989586621679217278_aRYW)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217270_aRYS) b_6989586621679217280_aRYX)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217272_aRYT) b_6989586621679217282_aRYY)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217274_aRYU) b_6989586621679217284_aRYZ)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217276_aRYV) b_6989586621679217286_aRZ0)) NilSym0)))))
instance POrd (a_11, b_12, c_13, d_14, e_15) where
  type Compare a_aRYI a_aRYJ = Compare_6989586621679217290 a_aRYI a_aRYJ
instance (SOrd a_11, SOrd b_12, SOrd c_13, SOrd d_14, SOrd e_15) =>
          SOrd (a_11, b_12, c_13, d_14, e_15) where
  sCompare
    (STuple5 (sA_6989586621679217268 :: Sing a_6989586621679217268_aRYR)
              (sA_6989586621679217270 :: Sing a_6989586621679217270_aRYS)
              (sA_6989586621679217272 :: Sing a_6989586621679217272_aRYT)
              (sA_6989586621679217274 :: Sing a_6989586621679217274_aRYU)
              (sA_6989586621679217276 :: Sing a_6989586621679217276_aRYV))
    (STuple5 (sB_6989586621679217278 :: Sing b_6989586621679217278_aRYW)
              (sB_6989586621679217280 :: Sing b_6989586621679217280_aRYX)
              (sB_6989586621679217282 :: Sing b_6989586621679217282_aRYY)
              (sB_6989586621679217284 :: Sing b_6989586621679217284_aRYZ)
              (sB_6989586621679217286 :: Sing b_6989586621679217286_aRZ0))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217268)
                  sB_6989586621679217278))
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing
                    (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217270)
                    sB_6989586621679217280))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing
                        (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217272)
                        sB_6989586621679217282))
                  (applySing
                    (applySing
                        (singFun2 @(:@#@$) SCons)
                        (applySing
                          (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217274)
                          sB_6989586621679217284))
                    (applySing
                        (applySing
                          (singFun2 @(:@#@$) SCons)
                          (applySing
                              (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217276)
                              sB_6989586621679217286))
                        SNil)))))
type Compare_6989586621679217351 :: forall a_11
                                            b_12
                                            c_13
                                            d_14
                                            e_15
                                            f_16. (a_11, b_12, c_13, d_14, e_15, f_16)
                                                  -> (a_11, b_12, c_13, d_14, e_15, f_16)
                                                    -> Ordering
type family Compare_6989586621679217351 @a_11 @b_12 @c_13 @d_14 @e_15 @f_16 (a_aRZL :: (a_11,
                                                                                        b_12,
                                                                                        c_13,
                                                                                        d_14,
                                                                                        e_15,
                                                                                        f_16)) (a_aRZM :: (a_11,
                                                                                                            b_12,
                                                                                                            c_13,
                                                                                                            d_14,
                                                                                                            e_15,
                                                                                                            f_16)) :: Ordering where
  Compare_6989586621679217351 @a_11 @b_12 @c_13 @d_14 @e_15 @f_16 ('(a_6989586621679217325_aRZQ,
                                                                      a_6989586621679217327_aRZR,
                                                                      a_6989586621679217329_aRZS,
                                                                      a_6989586621679217331_aRZT,
                                                                      a_6989586621679217333_aRZU,
                                                                      a_6989586621679217335_aRZV) :: (a_11,
                                                                                                      b_12,
                                                                                                      c_13,
                                                                                                      d_14,
                                                                                                      e_15,
                                                                                                      f_16)) ('(b_6989586621679217337_aRZW,
                                                                                                                b_6989586621679217339_aRZX,
                                                                                                                b_6989586621679217341_aRZY,
                                                                                                                b_6989586621679217343_aRZZ,
                                                                                                                b_6989586621679217345_aS00,
                                                                                                                b_6989586621679217347_aS01) :: (a_11,
                                                                                                                                                b_12,
                                                                                                                                                c_13,
                                                                                                                                                d_14,
                                                                                                                                                e_15,
                                                                                                                                                f_16)) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217325_aRZQ) b_6989586621679217337_aRZW)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217327_aRZR) b_6989586621679217339_aRZX)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217329_aRZS) b_6989586621679217341_aRZY)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217331_aRZT) b_6989586621679217343_aRZZ)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217333_aRZU) b_6989586621679217345_aS00)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217335_aRZV) b_6989586621679217347_aS01)) NilSym0))))))
instance POrd (a_11, b_12, c_13, d_14, e_15, f_16) where
  type Compare a_aRZH a_aRZI = Compare_6989586621679217351 a_aRZH a_aRZI
instance (SOrd a_11,
          SOrd b_12,
          SOrd c_13,
          SOrd d_14,
          SOrd e_15,
          SOrd f_16) =>
          SOrd (a_11, b_12, c_13, d_14, e_15, f_16) where
  sCompare
    (STuple6 (sA_6989586621679217325 :: Sing a_6989586621679217325_aRZQ)
              (sA_6989586621679217327 :: Sing a_6989586621679217327_aRZR)
              (sA_6989586621679217329 :: Sing a_6989586621679217329_aRZS)
              (sA_6989586621679217331 :: Sing a_6989586621679217331_aRZT)
              (sA_6989586621679217333 :: Sing a_6989586621679217333_aRZU)
              (sA_6989586621679217335 :: Sing a_6989586621679217335_aRZV))
    (STuple6 (sB_6989586621679217337 :: Sing b_6989586621679217337_aRZW)
              (sB_6989586621679217339 :: Sing b_6989586621679217339_aRZX)
              (sB_6989586621679217341 :: Sing b_6989586621679217341_aRZY)
              (sB_6989586621679217343 :: Sing b_6989586621679217343_aRZZ)
              (sB_6989586621679217345 :: Sing b_6989586621679217345_aS00)
              (sB_6989586621679217347 :: Sing b_6989586621679217347_aS01))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217325)
                  sB_6989586621679217337))
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing
                    (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217327)
                    sB_6989586621679217339))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing
                        (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217329)
                        sB_6989586621679217341))
                  (applySing
                    (applySing
                        (singFun2 @(:@#@$) SCons)
                        (applySing
                          (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217331)
                          sB_6989586621679217343))
                    (applySing
                        (applySing
                          (singFun2 @(:@#@$) SCons)
                          (applySing
                              (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217333)
                              sB_6989586621679217345))
                        (applySing
                          (applySing
                              (singFun2 @(:@#@$) SCons)
                              (applySing
                                (applySing
                                    (singFun2 @CompareSym0 sCompare) sA_6989586621679217335)
                                sB_6989586621679217347))
                          SNil))))))
type Compare_6989586621679217421 :: forall a_11
                                            b_12
                                            c_13
                                            d_14
                                            e_15
                                            f_16
                                            g_17. (a_11, b_12, c_13, d_14, e_15, f_16, g_17)
                                                  -> (a_11, b_12, c_13, d_14, e_15, f_16, g_17)
                                                    -> Ordering
type family Compare_6989586621679217421 @a_11 @b_12 @c_13 @d_14 @e_15 @f_16 @g_17 (a_aS0T :: (a_11,
                                                                                              b_12,
                                                                                              c_13,
                                                                                              d_14,
                                                                                              e_15,
                                                                                              f_16,
                                                                                              g_17)) (a_aS0U :: (a_11,
                                                                                                                  b_12,
                                                                                                                  c_13,
                                                                                                                  d_14,
                                                                                                                  e_15,
                                                                                                                  f_16,
                                                                                                                  g_17)) :: Ordering where
  Compare_6989586621679217421 @a_11 @b_12 @c_13 @d_14 @e_15 @f_16 @g_17 ('(a_6989586621679217391_aS0Y,
                                                                            a_6989586621679217393_aS0Z,
                                                                            a_6989586621679217395_aS10,
                                                                            a_6989586621679217397_aS11,
                                                                            a_6989586621679217399_aS12,
                                                                            a_6989586621679217401_aS13,
                                                                            a_6989586621679217403_aS14) :: (a_11,
                                                                                                            b_12,
                                                                                                            c_13,
                                                                                                            d_14,
                                                                                                            e_15,
                                                                                                            f_16,
                                                                                                            g_17)) ('(b_6989586621679217405_aS15,
                                                                                                                      b_6989586621679217407_aS16,
                                                                                                                      b_6989586621679217409_aS17,
                                                                                                                      b_6989586621679217411_aS18,
                                                                                                                      b_6989586621679217413_aS19,
                                                                                                                      b_6989586621679217415_aS1a,
                                                                                                                      b_6989586621679217417_aS1b) :: (a_11,
                                                                                                                                                      b_12,
                                                                                                                                                      c_13,
                                                                                                                                                      d_14,
                                                                                                                                                      e_15,
                                                                                                                                                      f_16,
                                                                                                                                                      g_17)) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217391_aS0Y) b_6989586621679217405_aS15)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217393_aS0Z) b_6989586621679217407_aS16)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217395_aS10) b_6989586621679217409_aS17)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217397_aS11) b_6989586621679217411_aS18)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217399_aS12) b_6989586621679217413_aS19)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217401_aS13) b_6989586621679217415_aS1a)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217403_aS14) b_6989586621679217417_aS1b)) NilSym0)))))))
instance POrd (a_11, b_12, c_13, d_14, e_15, f_16, g_17) where
  type Compare a_aS0P a_aS0Q = Compare_6989586621679217421 a_aS0P a_aS0Q
instance (SOrd a_11,
          SOrd b_12,
          SOrd c_13,
          SOrd d_14,
          SOrd e_15,
          SOrd f_16,
          SOrd g_17) =>
          SOrd (a_11, b_12, c_13, d_14, e_15, f_16, g_17) where
  sCompare
    (STuple7 (sA_6989586621679217391 :: Sing a_6989586621679217391_aS0Y)
              (sA_6989586621679217393 :: Sing a_6989586621679217393_aS0Z)
              (sA_6989586621679217395 :: Sing a_6989586621679217395_aS10)
              (sA_6989586621679217397 :: Sing a_6989586621679217397_aS11)
              (sA_6989586621679217399 :: Sing a_6989586621679217399_aS12)
              (sA_6989586621679217401 :: Sing a_6989586621679217401_aS13)
              (sA_6989586621679217403 :: Sing a_6989586621679217403_aS14))
    (STuple7 (sB_6989586621679217405 :: Sing b_6989586621679217405_aS15)
              (sB_6989586621679217407 :: Sing b_6989586621679217407_aS16)
              (sB_6989586621679217409 :: Sing b_6989586621679217409_aS17)
              (sB_6989586621679217411 :: Sing b_6989586621679217411_aS18)
              (sB_6989586621679217413 :: Sing b_6989586621679217413_aS19)
              (sB_6989586621679217415 :: Sing b_6989586621679217415_aS1a)
              (sB_6989586621679217417 :: Sing b_6989586621679217417_aS1b))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217391)
                  sB_6989586621679217405))
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing
                    (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217393)
                    sB_6989586621679217407))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing
                        (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217395)
                        sB_6989586621679217409))
                  (applySing
                    (applySing
                        (singFun2 @(:@#@$) SCons)
                        (applySing
                          (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217397)
                          sB_6989586621679217411))
                    (applySing
                        (applySing
                          (singFun2 @(:@#@$) SCons)
                          (applySing
                              (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217399)
                              sB_6989586621679217413))
                        (applySing
                          (applySing
                              (singFun2 @(:@#@$) SCons)
                              (applySing
                                (applySing
                                    (singFun2 @CompareSym0 sCompare) sA_6989586621679217401)
                                sB_6989586621679217415))
                          (applySing
                              (applySing
                                (singFun2 @(:@#@$) SCons)
                                (applySing
                                    (applySing
                                      (singFun2 @CompareSym0 sCompare) sA_6989586621679217403)
                                    sB_6989586621679217417))
                              SNil)))))))
type Compare_6989586621679217451 :: forall a_a8sO. Data.Functor.Identity.Identity a_a8sO
                                                    -> Data.Functor.Identity.Identity a_a8sO
                                                      -> Ordering
type family Compare_6989586621679217451 @a_a8sO (a_aS1n :: Data.Functor.Identity.Identity a_a8sO) (a_aS1o :: Data.Functor.Identity.Identity a_a8sO) :: Ordering where
  Compare_6989586621679217451 @a_a8sO ('Data.Functor.Identity.Identity a_6989586621679217445_aS1s :: Data.Functor.Identity.Identity a_a8sO) ('Data.Functor.Identity.Identity b_6989586621679217447_aS1t :: Data.Functor.Identity.Identity a_a8sO) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679217445_aS1s) b_6989586621679217447_aS1t)) NilSym0)
instance POrd (Data.Functor.Identity.Identity a_a8sO) where
  type Compare a_aS1j a_aS1k = Compare_6989586621679217451 a_aS1j a_aS1k
instance SOrd a_a8sO =>
          SOrd (Data.Functor.Identity.Identity a_a8sO) where
  sCompare
    (SIdentity (sA_6989586621679217445 :: Sing a_6989586621679217445_aS1s))
    (SIdentity (sB_6989586621679217447 :: Sing b_6989586621679217447_aS1t))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679217445)
                  sB_6989586621679217447))
            SNil)
type Compare_6989586621679217462 :: Bool -> Bool -> Ordering
type family Compare_6989586621679217462 (a_aS1y :: Bool) (a_aS1z :: Bool) :: Ordering where
  Compare_6989586621679217462 'False 'False = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) NilSym0
  Compare_6989586621679217462 'True 'True = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) NilSym0
  Compare_6989586621679217462 'False 'True = LTSym0
  Compare_6989586621679217462 'True 'False = GTSym0
instance POrd Bool where
  type Compare a_aS1u a_aS1v = Compare_6989586621679217462 a_aS1u a_aS1v
instance SOrd Bool where
  sCompare SFalse SFalse
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        SNil
  sCompare STrue STrue
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        SNil
  sCompare SFalse STrue = SLT
  sCompare STrue SFalse = SGT
type Compare_6989586621679217471 :: Ordering
                                    -> Ordering -> Ordering
type family Compare_6989586621679217471 (a_aS1H :: Ordering) (a_aS1I :: Ordering) :: Ordering where
  Compare_6989586621679217471 'LT 'LT = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) NilSym0
  Compare_6989586621679217471 'EQ 'EQ = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) NilSym0
  Compare_6989586621679217471 'GT 'GT = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) NilSym0
  Compare_6989586621679217471 'LT 'EQ = LTSym0
  Compare_6989586621679217471 'LT 'GT = LTSym0
  Compare_6989586621679217471 'EQ 'LT = GTSym0
  Compare_6989586621679217471 'EQ 'GT = LTSym0
  Compare_6989586621679217471 'GT 'LT = GTSym0
  Compare_6989586621679217471 'GT 'EQ = GTSym0
instance POrd Ordering where
  type Compare a_aS1D a_aS1E = Compare_6989586621679217471 a_aS1D a_aS1E
instance SOrd Ordering where
  sCompare SLT SLT
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        SNil
  sCompare SEQ SEQ
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        SNil
  sCompare SGT SGT
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        SNil
  sCompare SLT SEQ = SLT
  sCompare SLT SGT = SLT
  sCompare SEQ SLT = SGT
  sCompare SEQ SGT = SLT
  sCompare SGT SLT = SGT
  sCompare SGT SEQ = SGT
type Compare_6989586621679217480 :: () -> () -> Ordering
type family Compare_6989586621679217480 (a_aS1Q :: ()) (a_aS1R :: ()) :: Ordering where
  Compare_6989586621679217480 '() '() = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) NilSym0
instance POrd () where
  type Compare a_aS1M a_aS1N = Compare_6989586621679217480 a_aS1M a_aS1N
instance SOrd () where
  sCompare STuple0 STuple0
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        SNil

