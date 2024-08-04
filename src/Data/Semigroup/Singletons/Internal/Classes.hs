{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}

{-# LANGUAGE TypeAbstractions #-}
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
-- Module      :  Data.Semigroup.Singletons.Internal.Classes
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted version of 'Semigroup', 'PSemigroup'; the
-- singleton version, 'SSemigroup'; and instances thereof for various data
-- types in @base@. These are reexported from the "Data.Semigroup" module or
-- imported directly by some other modules.
--
-- This module exists to avoid import cycles with
-- "Data.Ord.Singletons".
--
----------------------------------------------------------------------------

module Data.Semigroup.Singletons.Internal.Classes where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Singletons.Base.Instances
import Data.Singletons.TH
import GHC.Base.Singletons
import Data.Kind (Type)

type (<>@#@$) :: forall a_aKib. (~>) a_aKib ((~>) a_aKib a_aKib)
data (<>@#@$) :: (~>) a_aKib ((~>) a_aKib a_aKib)
  where
    (:<>@#@$###) :: SameKind (Apply (<>@#@$) arg_aKlw) ((<>@#@$$) arg_aKlw) =>
                    (<>@#@$) a6989586621679187951
type instance Apply @a_aKib @((~>) a_aKib a_aKib) (<>@#@$) a6989586621679187951 = (<>@#@$$) a6989586621679187951
instance SuppressUnusedWarnings (<>@#@$) where
  suppressUnusedWarnings = snd ((,) (:<>@#@$###) ())
infixr 6 <>@#@$
type (<>@#@$$) :: forall a_aKib. a_aKib -> (~>) a_aKib a_aKib
data (<>@#@$$) (a6989586621679187951 :: a_aKib) :: (~>) a_aKib a_aKib
  where
    (:<>@#@$$###) :: SameKind (Apply ((<>@#@$$) a6989586621679187951) arg_aKlw) ((<>@#@$$$) a6989586621679187951 arg_aKlw) =>
                      (<>@#@$$) a6989586621679187951 a6989586621679187952
type instance Apply @a_aKib @a_aKib ((<>@#@$$) a6989586621679187951) a6989586621679187952 = (<>) a6989586621679187951 a6989586621679187952
instance SuppressUnusedWarnings ((<>@#@$$) a6989586621679187951) where
  suppressUnusedWarnings = snd ((,) (:<>@#@$$###) ())
infixr 6 <>@#@$$
type (<>@#@$$$) :: forall a_aKib. a_aKib -> a_aKib -> a_aKib
type family (<>@#@$$$) @a_aKib (a6989586621679187951 :: a_aKib) (a6989586621679187952 :: a_aKib) :: a_aKib where
  (<>@#@$$$) a6989586621679187951 a6989586621679187952 = (<>) a6989586621679187951 a6989586621679187952
infixr 6 <>@#@$$$
type SconcatSym0 :: forall a_aKib. (~>) (NonEmpty a_aKib) a_aKib
data SconcatSym0 :: (~>) (NonEmpty a_aKib) a_aKib
  where
    SconcatSym0KindInference :: SameKind (Apply SconcatSym0 arg_aKlA) (SconcatSym1 arg_aKlA) =>
                                SconcatSym0 a6989586621679187955
type instance Apply @(NonEmpty a_aKib) @a_aKib SconcatSym0 a6989586621679187955 = Sconcat a6989586621679187955
instance SuppressUnusedWarnings SconcatSym0 where
  suppressUnusedWarnings = snd ((,) SconcatSym0KindInference ())
type SconcatSym1 :: forall a_aKib. NonEmpty a_aKib -> a_aKib
type family SconcatSym1 @a_aKib (a6989586621679187955 :: NonEmpty a_aKib) :: a_aKib where
  SconcatSym1 a6989586621679187955 = Sconcat a6989586621679187955
data Let6989586621679187964GoSym0 a6989586621679187743 a6989586621679187962 as6989586621679187963 :: (~>) a6989586621679187743 ((~>) [a6989586621679187743] a6989586621679187743)
  where
    Let6989586621679187964GoSym0KindInference :: SameKind (Apply (Let6989586621679187964GoSym0 a6989586621679187743 a6989586621679187962 as6989586621679187963) arg_aKlN) (Let6989586621679187964GoSym1 a6989586621679187743 a6989586621679187962 as6989586621679187963 arg_aKlN) =>
                                                  Let6989586621679187964GoSym0 a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965
type instance Apply @a6989586621679187743 @((~>) [a6989586621679187743] a6989586621679187743) (Let6989586621679187964GoSym0 a6989586621679187743 a6989586621679187962 as6989586621679187963) a6989586621679187965 = Let6989586621679187964GoSym1 a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965
instance SuppressUnusedWarnings (Let6989586621679187964GoSym0 a6989586621679187743 a6989586621679187962 as6989586621679187963) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679187964GoSym0KindInference ())
data Let6989586621679187964GoSym1 a6989586621679187743 a6989586621679187962 as6989586621679187963 (a6989586621679187965 :: a6989586621679187743) :: (~>) [a6989586621679187743] a6989586621679187743
  where
    Let6989586621679187964GoSym1KindInference :: SameKind (Apply (Let6989586621679187964GoSym1 a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965) arg_aKlN) (Let6989586621679187964GoSym2 a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965 arg_aKlN) =>
                                                  Let6989586621679187964GoSym1 a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965 a6989586621679187966
type instance Apply @[a6989586621679187743] @a6989586621679187743 (Let6989586621679187964GoSym1 a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965) a6989586621679187966 = Let6989586621679187964Go a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965 a6989586621679187966
instance SuppressUnusedWarnings (Let6989586621679187964GoSym1 a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679187964GoSym1KindInference ())
type family Let6989586621679187964GoSym2 a6989586621679187743 a6989586621679187962 as6989586621679187963 (a6989586621679187965 :: a6989586621679187743) (a6989586621679187966 :: [a6989586621679187743]) :: a6989586621679187743 where
  Let6989586621679187964GoSym2 a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965 a6989586621679187966 = Let6989586621679187964Go a6989586621679187743 a6989586621679187962 as6989586621679187963 a6989586621679187965 a6989586621679187966
type family Let6989586621679187964Go a6989586621679187743 a6989586621679187962 as6989586621679187963 (a_aKlL :: a6989586621679187743) (a_aKlM :: [a6989586621679187743]) :: a6989586621679187743 where
  Let6989586621679187964Go a_aKib a_aKlI as_aKlJ b_aKlO ('(:) c_aKlP cs_aKlQ) = Apply (Apply (<>@#@$) b_aKlO) (Apply (Apply (Let6989586621679187964GoSym0 a_aKib a_aKlI as_aKlJ) c_aKlP) cs_aKlQ)
  Let6989586621679187964Go a_aKib a_aKlI as_aKlJ b_aKlR '[] = b_aKlR
type Sconcat_6989586621679187957 :: forall a_aKib. NonEmpty a_aKib
                                                    -> a_aKib
type family Sconcat_6989586621679187957 @a_aKib (a_aKlF :: NonEmpty a_aKib) :: a_aKib where
  Sconcat_6989586621679187957 @a_aKib ('(:|) a_aKlI as_aKlJ :: NonEmpty a_aKib) = Apply (Apply (Let6989586621679187964GoSym0 a_aKib a_aKlI as_aKlJ) a_aKlI) as_aKlJ
class PSemigroup a_aKib where
  type family (<>) (arg_aKlu :: a_aKib) (arg_aKlv :: a_aKib) :: a_aKib
  type family Sconcat (arg_aKlz :: NonEmpty a_aKib) :: a_aKib
  type Sconcat a_aKlC = Sconcat_6989586621679187957 a_aKlC
  infixr 6 <>
type TFHelper_6989586621679187974 :: forall a_aKij. [a_aKij]
                                                    -> [a_aKij] -> [a_aKij]
type family TFHelper_6989586621679187974 @a_aKij (a_aKm0 :: [a_aKij]) (a_aKm1 :: [a_aKij]) :: [a_aKij] where
  TFHelper_6989586621679187974 @a_aKij (a_6989586621679187976_aKm5 :: [a_aKij]) (a_6989586621679187978_aKm6 :: [a_aKij]) = Apply (Apply (++@#@$) a_6989586621679187976_aKm5) a_6989586621679187978_aKm6
instance PSemigroup [a_aKij] where
  type (<>) a_aKlS a_aKlT = TFHelper_6989586621679187974 a_aKlS a_aKlT
type TFHelper_6989586621679187989 :: forall a_aKik. NonEmpty a_aKik
                                                    -> NonEmpty a_aKik -> NonEmpty a_aKik
type family TFHelper_6989586621679187989 @a_aKik (a_aKmb :: NonEmpty a_aKik) (a_aKmc :: NonEmpty a_aKik) :: NonEmpty a_aKik where
  TFHelper_6989586621679187989 @a_aKik ('(:|) a_aKmg as_aKmh :: NonEmpty a_aKik) ('(:|) b_aKmi bs_aKmj :: NonEmpty a_aKik) = Apply (Apply (:|@#@$) a_aKmg) (Apply (Apply (++@#@$) as_aKmh) (Apply (Apply (:@#@$) b_aKmi) bs_aKmj))
instance PSemigroup (NonEmpty a_aKik) where
  type (<>) a_aKm7 a_aKm8 = TFHelper_6989586621679187989 a_aKm7 a_aKm8
type family LamCases_6989586621679188011_aKmw a6989586621679187758 b6989586621679187757 (f6989586621679188009 :: (~>) a6989586621679187758 b6989586621679187757) (g6989586621679188010 :: (~>) a6989586621679187758 b6989586621679187757) a_6989586621679188014_aKmz where
  LamCases_6989586621679188011_aKmw a_aKiq b_aKip f_aKmt g_aKmu x_aKmx = Apply (Apply (<>@#@$) (Apply f_aKmt x_aKmx)) (Apply g_aKmu x_aKmx)
data LamCases_6989586621679188011Sym0 a6989586621679187758 b6989586621679187757 (f6989586621679188009 :: (~>) a6989586621679187758 b6989586621679187757) (g6989586621679188010 :: (~>) a6989586621679187758 b6989586621679187757) a_69895866216791880146989586621679188015
  where
    LamCases_6989586621679188011Sym0KindInference :: SameKind (Apply (LamCases_6989586621679188011Sym0 a6989586621679187758 b6989586621679187757 f6989586621679188009 g6989586621679188010) arg_aKmA) (LamCases_6989586621679188011Sym1 a6989586621679187758 b6989586621679187757 f6989586621679188009 g6989586621679188010 arg_aKmA) =>
                                                      LamCases_6989586621679188011Sym0 a6989586621679187758 b6989586621679187757 f6989586621679188009 g6989586621679188010 a_69895866216791880146989586621679188015
type instance Apply @_ @_ (LamCases_6989586621679188011Sym0 a6989586621679187758 b6989586621679187757 f6989586621679188009 g6989586621679188010) a_69895866216791880146989586621679188015 = LamCases_6989586621679188011_aKmw a6989586621679187758 b6989586621679187757 f6989586621679188009 g6989586621679188010 a_69895866216791880146989586621679188015
instance SuppressUnusedWarnings (LamCases_6989586621679188011Sym0 a6989586621679187758 b6989586621679187757 f6989586621679188009 g6989586621679188010) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679188011Sym0KindInference ())
type family LamCases_6989586621679188011Sym1 a6989586621679187758 b6989586621679187757 (f6989586621679188009 :: (~>) a6989586621679187758 b6989586621679187757) (g6989586621679188010 :: (~>) a6989586621679187758 b6989586621679187757) a_69895866216791880146989586621679188015 where
  LamCases_6989586621679188011Sym1 a6989586621679187758 b6989586621679187757 f6989586621679188009 g6989586621679188010 a_69895866216791880146989586621679188015 = LamCases_6989586621679188011_aKmw a6989586621679187758 b6989586621679187757 f6989586621679188009 g6989586621679188010 a_69895866216791880146989586621679188015
type TFHelper_6989586621679188002 :: forall a_aKiq
                                            b_aKip. (~>) a_aKiq b_aKip
                                                    -> (~>) a_aKiq b_aKip -> (~>) a_aKiq b_aKip
type family TFHelper_6989586621679188002 @a_aKiq @b_aKip (a_aKmo :: (~>) a_aKiq b_aKip) (a_aKmp :: (~>) a_aKiq b_aKip) :: (~>) a_aKiq b_aKip where
  TFHelper_6989586621679188002 @a_aKiq @b_aKip (f_aKmt :: (~>) a_aKiq b_aKip) (g_aKmu :: (~>) a_aKiq b_aKip) = LamCases_6989586621679188011Sym0 a_aKiq b_aKip f_aKmt g_aKmu
instance PSemigroup ((~>) a_aKiq b_aKip) where
  type (<>) a_aKmk a_aKml = TFHelper_6989586621679188002 a_aKmk a_aKml
type TFHelper_6989586621679188019 :: () -> () -> ()
type family TFHelper_6989586621679188019 (a_aKmF :: ()) (a_aKmG :: ()) :: () where
  TFHelper_6989586621679188019 _ _ = Tuple0Sym0
type Sconcat_6989586621679188027 :: NonEmpty () -> ()
type family Sconcat_6989586621679188027 (a_aKmN :: NonEmpty ()) :: () where
  Sconcat_6989586621679188027 _ = Tuple0Sym0
instance PSemigroup () where
  type (<>) a_aKmB a_aKmC = TFHelper_6989586621679188019 a_aKmB a_aKmC
  type Sconcat a_aKmK = Sconcat_6989586621679188027 a_aKmK
type TFHelper_6989586621679188034 :: forall a_aKiu b_aKiv. (a_aKiu,
                                                            b_aKiv)
                                                            -> (a_aKiu, b_aKiv)
                                                              -> (a_aKiu, b_aKiv)
type family TFHelper_6989586621679188034 @a_aKiu @b_aKiv (a_aKmU :: (a_aKiu,
                                                                      b_aKiv)) (a_aKmV :: (a_aKiu,
                                                                                          b_aKiv)) :: (a_aKiu,
                                                                                                        b_aKiv) where
  TFHelper_6989586621679188034 @a_aKiu @b_aKiv ('(a_aKmZ,
                                                  b_aKn0) :: (a_aKiu, b_aKiv)) ('(a'_aKn1,
                                                                                  b'_aKn2) :: (a_aKiu,
                                                                                                b_aKiv)) = Apply (Apply Tuple2Sym0 (Apply (Apply (<>@#@$) a_aKmZ) a'_aKn1)) (Apply (Apply (<>@#@$) b_aKn0) b'_aKn2)
instance PSemigroup (a_aKiu, b_aKiv) where
  type (<>) a_aKmQ a_aKmR = TFHelper_6989586621679188034 a_aKmQ a_aKmR
type TFHelper_6989586621679188047 :: forall a_aKiA
                                            b_aKiB
                                            c_aKiC. (a_aKiA, b_aKiB, c_aKiC)
                                                    -> (a_aKiA, b_aKiB, c_aKiC)
                                                        -> (a_aKiA, b_aKiB, c_aKiC)
type family TFHelper_6989586621679188047 @a_aKiA @b_aKiB @c_aKiC (a_aKn7 :: (a_aKiA,
                                                                              b_aKiB,
                                                                              c_aKiC)) (a_aKn8 :: (a_aKiA,
                                                                                                  b_aKiB,
                                                                                                  c_aKiC)) :: (a_aKiA,
                                                                                                                b_aKiB,
                                                                                                                c_aKiC) where
  TFHelper_6989586621679188047 @a_aKiA @b_aKiB @c_aKiC ('(a_aKnc,
                                                          b_aKnd,
                                                          c_aKne) :: (a_aKiA, b_aKiB,
                                                                      c_aKiC)) ('(a'_aKnf,
                                                                                  b'_aKng,
                                                                                  c'_aKnh) :: (a_aKiA,
                                                                                                b_aKiB,
                                                                                                c_aKiC)) = Apply (Apply (Apply Tuple3Sym0 (Apply (Apply (<>@#@$) a_aKnc) a'_aKnf)) (Apply (Apply (<>@#@$) b_aKnd) b'_aKng)) (Apply (Apply (<>@#@$) c_aKne) c'_aKnh)
instance PSemigroup (a_aKiA, b_aKiB, c_aKiC) where
  type (<>) a_aKn3 a_aKn4 = TFHelper_6989586621679188047 a_aKn3 a_aKn4
type TFHelper_6989586621679188062 :: forall a_aKiJ
                                            b_aKiK
                                            c_aKiL
                                            d_aKiM. (a_aKiJ, b_aKiK, c_aKiL, d_aKiM)
                                                    -> (a_aKiJ, b_aKiK, c_aKiL, d_aKiM)
                                                        -> (a_aKiJ, b_aKiK, c_aKiL, d_aKiM)
type family TFHelper_6989586621679188062 @a_aKiJ @b_aKiK @c_aKiL @d_aKiM (a_aKnm :: (a_aKiJ,
                                                                                      b_aKiK,
                                                                                      c_aKiL,
                                                                                      d_aKiM)) (a_aKnn :: (a_aKiJ,
                                                                                                          b_aKiK,
                                                                                                          c_aKiL,
                                                                                                          d_aKiM)) :: (a_aKiJ,
                                                                                                                        b_aKiK,
                                                                                                                        c_aKiL,
                                                                                                                        d_aKiM) where
  TFHelper_6989586621679188062 @a_aKiJ @b_aKiK @c_aKiL @d_aKiM ('(a_aKnr,
                                                                  b_aKns,
                                                                  c_aKnt,
                                                                  d_aKnu) :: (a_aKiJ, b_aKiK,
                                                                              c_aKiL,
                                                                              d_aKiM)) ('(a'_aKnv,
                                                                                          b'_aKnw,
                                                                                          c'_aKnx,
                                                                                          d'_aKny) :: (a_aKiJ,
                                                                                                        b_aKiK,
                                                                                                        c_aKiL,
                                                                                                        d_aKiM)) = Apply (Apply (Apply (Apply Tuple4Sym0 (Apply (Apply (<>@#@$) a_aKnr) a'_aKnv)) (Apply (Apply (<>@#@$) b_aKns) b'_aKnw)) (Apply (Apply (<>@#@$) c_aKnt) c'_aKnx)) (Apply (Apply (<>@#@$) d_aKnu) d'_aKny)
instance PSemigroup (a_aKiJ, b_aKiK, c_aKiL, d_aKiM) where
  type (<>) a_aKni a_aKnj = TFHelper_6989586621679188062 a_aKni a_aKnj
type TFHelper_6989586621679188079 :: forall a_aKiV
                                            b_aKiW
                                            c_aKiX
                                            d_aKiY
                                            e_aKiZ. (a_aKiV, b_aKiW, c_aKiX, d_aKiY, e_aKiZ)
                                                    -> (a_aKiV, b_aKiW, c_aKiX, d_aKiY, e_aKiZ)
                                                        -> (a_aKiV, b_aKiW, c_aKiX, d_aKiY,
                                                            e_aKiZ)
type family TFHelper_6989586621679188079 @a_aKiV @b_aKiW @c_aKiX @d_aKiY @e_aKiZ (a_aKnD :: (a_aKiV,
                                                                                              b_aKiW,
                                                                                              c_aKiX,
                                                                                              d_aKiY,
                                                                                              e_aKiZ)) (a_aKnE :: (a_aKiV,
                                                                                                                  b_aKiW,
                                                                                                                  c_aKiX,
                                                                                                                  d_aKiY,
                                                                                                                  e_aKiZ)) :: (a_aKiV,
                                                                                                                                b_aKiW,
                                                                                                                                c_aKiX,
                                                                                                                                d_aKiY,
                                                                                                                                e_aKiZ) where
  TFHelper_6989586621679188079 @a_aKiV @b_aKiW @c_aKiX @d_aKiY @e_aKiZ ('(a_aKnI,
                                                                          b_aKnJ,
                                                                          c_aKnK,
                                                                          d_aKnL,
                                                                          e_aKnM) :: (a_aKiV,
                                                                                      b_aKiW,
                                                                                      c_aKiX,
                                                                                      d_aKiY,
                                                                                      e_aKiZ)) ('(a'_aKnN,
                                                                                                  b'_aKnO,
                                                                                                  c'_aKnP,
                                                                                                  d'_aKnQ,
                                                                                                  e'_aKnR) :: (a_aKiV,
                                                                                                                b_aKiW,
                                                                                                                c_aKiX,
                                                                                                                d_aKiY,
                                                                                                                e_aKiZ)) = Apply (Apply (Apply (Apply (Apply Tuple5Sym0 (Apply (Apply (<>@#@$) a_aKnI) a'_aKnN)) (Apply (Apply (<>@#@$) b_aKnJ) b'_aKnO)) (Apply (Apply (<>@#@$) c_aKnK) c'_aKnP)) (Apply (Apply (<>@#@$) d_aKnL) d'_aKnQ)) (Apply (Apply (<>@#@$) e_aKnM) e'_aKnR)
instance PSemigroup (a_aKiV, b_aKiW, c_aKiX, d_aKiY, e_aKiZ) where
  type (<>) a_aKnz a_aKnA = TFHelper_6989586621679188079 a_aKnz a_aKnA
type TFHelper_6989586621679188098 :: Ordering
                                      -> Ordering -> Ordering
type family TFHelper_6989586621679188098 (a_aKnW :: Ordering) (a_aKnX :: Ordering) :: Ordering where
  TFHelper_6989586621679188098 'LT _ = LTSym0
  TFHelper_6989586621679188098 'EQ y_aKo1 = y_aKo1
  TFHelper_6989586621679188098 'GT _ = GTSym0
instance PSemigroup Ordering where
  type (<>) a_aKnS a_aKnT = TFHelper_6989586621679188098 a_aKnS a_aKnT
type TFHelper_6989586621679188108 :: forall a_aKjb. Maybe a_aKjb
                                                    -> Maybe a_aKjb -> Maybe a_aKjb
type family TFHelper_6989586621679188108 @a_aKjb (a_aKo6 :: Maybe a_aKjb) (a_aKo7 :: Maybe a_aKjb) :: Maybe a_aKjb where
  TFHelper_6989586621679188108 @a_aKjb ('Nothing :: Maybe a_aKjb) (b_aKob :: Maybe a_aKjb) = b_aKob
  TFHelper_6989586621679188108 @a_aKjb (a_aKoc :: Maybe a_aKjb) ('Nothing :: Maybe a_aKjb) = a_aKoc
  TFHelper_6989586621679188108 @a_aKjb ('Just a_aKod :: Maybe a_aKjb) ('Just b_aKoe :: Maybe a_aKjb) = Apply JustSym0 (Apply (Apply (<>@#@$) a_aKod) b_aKoe)
instance PSemigroup (Maybe a_aKjb) where
  type (<>) a_aKo2 a_aKo3 = TFHelper_6989586621679188108 a_aKo2 a_aKo3
type family Let6989586621679188130ASym0 a6989586621679187810 b6989586621679187811 wild_69895866216791878196989586621679188129 where
  Let6989586621679188130ASym0 a6989586621679187810 b6989586621679187811 wild_69895866216791878196989586621679188129 = Let6989586621679188130A a6989586621679187810 b6989586621679187811 wild_69895866216791878196989586621679188129
type family Let6989586621679188130A a6989586621679187810 b6989586621679187811 wild_69895866216791878196989586621679188129 where
  Let6989586621679188130A a_aKjg b_aKjh wild_6989586621679187819_aKop = Apply RightSym0 wild_6989586621679187819_aKop
type TFHelper_6989586621679188121 :: forall a_aKjg
                                            b_aKjh. Either a_aKjg b_aKjh
                                                    -> Either a_aKjg b_aKjh
                                                        -> Either a_aKjg b_aKjh
type family TFHelper_6989586621679188121 @a_aKjg @b_aKjh (a_aKoj :: Either a_aKjg b_aKjh) (a_aKok :: Either a_aKjg b_aKjh) :: Either a_aKjg b_aKjh where
  TFHelper_6989586621679188121 @a_aKjg @b_aKjh ('Left _ :: Either a_aKjg b_aKjh) (b_aKoo :: Either a_aKjg b_aKjh) = b_aKoo
  TFHelper_6989586621679188121 @a_aKjg @b_aKjh ('Right wild_6989586621679187819_aKop :: Either a_aKjg b_aKjh) (_ :: Either a_aKjg b_aKjh) = Let6989586621679188130ASym0 a_aKjg b_aKjh wild_6989586621679187819_aKop
instance PSemigroup (Either a_aKjg b_aKjh) where
  type (<>) a_aKof a_aKog = TFHelper_6989586621679188121 a_aKof a_aKog
type TFHelper_6989586621679188134 :: Void -> Void -> Void
type family TFHelper_6989586621679188134 (a_aKow :: Void) (a_aKox :: Void) :: Void where
  TFHelper_6989586621679188134 a_aKoB _ = a_aKoB
instance PSemigroup Void where
  type (<>) a_aKos a_aKot = TFHelper_6989586621679188134 a_aKos a_aKot
class SSemigroup a_aKib where
  (%<>) ::
    (forall (t_aKoC :: a_aKib) (t_aKoD :: a_aKib).
      Sing t_aKoC
      -> Sing t_aKoD -> Sing ((<>) t_aKoC t_aKoD :: a_aKib) :: Type)
  sSconcat ::
    (forall (t_aKoH :: NonEmpty a_aKib).
      Sing t_aKoH -> Sing (Sconcat t_aKoH :: a_aKib) :: Type)
  infixr 6 %<>
  default sSconcat ::
            (forall (t_aKoH :: NonEmpty a_aKib).
              ((Sconcat t_aKoH :: a_aKib)
              ~ Sconcat_6989586621679187957 t_aKoH) =>
              Sing t_aKoH -> Sing (Sconcat t_aKoH :: a_aKib) :: Type)
  sSconcat ((:%|) (sA :: Sing a_aKlI) (sAs :: Sing as_aKlJ))
    = let
        sGo ::
          (forall (t_aKoJ :: a_aKib) (t_aKoK :: [a_aKib]).
            Sing t_aKoJ
            -> Sing t_aKoK
              -> Sing (Let6989586621679187964Go a_aKib a_aKlI as_aKlJ t_aKoJ t_aKoK :: a_aKib) :: Type)
        sGo
          (sB :: Sing b_aKlO)
          (SCons (sC :: Sing c_aKlP) (sCs :: Sing cs_aKlQ))
          = applySing
              (applySing (singFun2 @(<>@#@$) (%<>)) sB)
              (applySing
                  (applySing
                    (singFun2
                        @(Let6989586621679187964GoSym0 a_aKib a_aKlI as_aKlJ) sGo)
                    sC)
                  sCs)
        sGo (sB :: Sing b_aKlR) SNil = sB
      in
        applySing
          (applySing
              (singFun2
                @(Let6989586621679187964GoSym0 a_aKib a_aKlI as_aKlJ) sGo)
              sA)
          sAs
instance SSemigroup [a_aKij] where
  (%<>)
    (sA_6989586621679187976 :: Sing a_6989586621679187976_aKm5)
    (sA_6989586621679187978 :: Sing a_6989586621679187978_aKm6)
    = applySing
        (applySing (singFun2 @(++@#@$) (%++)) sA_6989586621679187976)
        sA_6989586621679187978
instance SSemigroup (NonEmpty a_aKik) where
  (%<>)
    ((:%|) (sA :: Sing a_aKmg) (sAs :: Sing as_aKmh))
    ((:%|) (sB :: Sing b_aKmi) (sBs :: Sing bs_aKmj))
    = applySing
        (applySing (singFun2 @(:|@#@$) (:%|)) sA)
        (applySing
            (applySing (singFun2 @(++@#@$) (%++)) sAs)
            (applySing (applySing (singFun2 @(:@#@$) SCons) sB) sBs))
instance SSemigroup b_aKip => SSemigroup ((~>) a_aKiq b_aKip) where
  (%<>) (sF :: Sing f_aKmt) (sG :: Sing g_aKmu)
    = singFun1
        @(LamCases_6989586621679188011Sym0 a_aKiq b_aKip f_aKmt g_aKmu)
        (\cases
            (sX :: Sing x_aKmx)
              -> applySing
                  (applySing (singFun2 @(<>@#@$) (%<>)) (applySing sF sX))
                  (applySing sG sX))
instance SSemigroup () where
  (%<>) _ _ = STuple0
  sSconcat _ = STuple0
instance (SSemigroup a_aKiu, SSemigroup b_aKiv) =>
          SSemigroup (a_aKiu, b_aKiv) where
  (%<>)
    (STuple2 (sA :: Sing a_aKmZ) (sB :: Sing b_aKn0))
    (STuple2 (sA' :: Sing a'_aKn1) (sB' :: Sing b'_aKn2))
    = applySing
        (applySing
            (singFun2 @Tuple2Sym0 STuple2)
            (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sA) sA'))
        (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sB) sB')
instance (SSemigroup a_aKiA,
          SSemigroup b_aKiB,
          SSemigroup c_aKiC) =>
          SSemigroup (a_aKiA, b_aKiB, c_aKiC) where
  (%<>)
    (STuple3 (sA :: Sing a_aKnc) (sB :: Sing b_aKnd)
              (sC :: Sing c_aKne))
    (STuple3 (sA' :: Sing a'_aKnf) (sB' :: Sing b'_aKng)
              (sC' :: Sing c'_aKnh))
    = applySing
        (applySing
            (applySing
              (singFun3 @Tuple3Sym0 STuple3)
              (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sA) sA'))
            (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sB) sB'))
        (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sC) sC')
instance (SSemigroup a_aKiJ,
          SSemigroup b_aKiK,
          SSemigroup c_aKiL,
          SSemigroup d_aKiM) =>
          SSemigroup (a_aKiJ, b_aKiK, c_aKiL, d_aKiM) where
  (%<>)
    (STuple4 (sA :: Sing a_aKnr) (sB :: Sing b_aKns)
              (sC :: Sing c_aKnt) (sD :: Sing d_aKnu))
    (STuple4 (sA' :: Sing a'_aKnv) (sB' :: Sing b'_aKnw)
              (sC' :: Sing c'_aKnx) (sD' :: Sing d'_aKny))
    = applySing
        (applySing
            (applySing
              (applySing
                  (singFun4 @Tuple4Sym0 STuple4)
                  (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sA) sA'))
              (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sB) sB'))
            (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sC) sC'))
        (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sD) sD')
instance (SSemigroup a_aKiV,
          SSemigroup b_aKiW,
          SSemigroup c_aKiX,
          SSemigroup d_aKiY,
          SSemigroup e_aKiZ) =>
          SSemigroup (a_aKiV, b_aKiW, c_aKiX, d_aKiY, e_aKiZ) where
  (%<>)
    (STuple5 (sA :: Sing a_aKnI) (sB :: Sing b_aKnJ)
              (sC :: Sing c_aKnK) (sD :: Sing d_aKnL) (sE :: Sing e_aKnM))
    (STuple5 (sA' :: Sing a'_aKnN) (sB' :: Sing b'_aKnO)
              (sC' :: Sing c'_aKnP) (sD' :: Sing d'_aKnQ) (sE' :: Sing e'_aKnR))
    = applySing
        (applySing
            (applySing
              (applySing
                  (applySing
                    (singFun5 @Tuple5Sym0 STuple5)
                    (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sA) sA'))
                  (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sB) sB'))
              (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sC) sC'))
            (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sD) sD'))
        (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sE) sE')
instance SSemigroup Ordering where
  (%<>) SLT _ = SLT
  (%<>) SEQ (sY :: Sing y_aKo1) = sY
  (%<>) SGT _ = SGT
instance SSemigroup a_aKjb => SSemigroup (Maybe a_aKjb) where
  (%<>) SNothing (sB :: Sing b_aKob) = sB
  (%<>) (sA :: Sing a_aKoc) SNothing = sA
  (%<>) (SJust (sA :: Sing a_aKod)) (SJust (sB :: Sing b_aKoe))
    = applySing
        (singFun1 @JustSym0 SJust)
        (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sA) sB)
instance SSemigroup (Either a_aKjg b_aKjh) where
  (%<>) (SLeft _) (sB :: Sing b_aKoo) = sB
  (%<>)
    (SRight (sWild_6989586621679187819 :: Sing wild_6989586621679187819_aKop))
    _
    = let
        sA ::
          Sing @_ (Let6989586621679188130A a_aKjg b_aKjh wild_6989586621679187819_aKop)
        sA
          = applySing (singFun1 @RightSym0 SRight) sWild_6989586621679187819
      in sA
instance SSemigroup Void where
  (%<>) (sA :: Sing a_aKoB) _ = sA
instance SSemigroup a_aKib =>
          SingI ((<>@#@$) :: (~>) a_aKib ((~>) a_aKib a_aKib)) where
  sing = singFun2 @(<>@#@$) (%<>)
instance (SSemigroup a_aKib, SingI d_aKoE) =>
          SingI ((<>@#@$$) (d_aKoE :: a_aKib) :: (~>) a_aKib a_aKib) where
  sing
    = singFun1 @((<>@#@$$) (d_aKoE :: a_aKib)) ((%<>) (sing @d_aKoE))
instance SSemigroup a_aKib =>
          SingI1 ((<>@#@$$) :: a_aKib -> (~>) a_aKib a_aKib) where
  liftSing (s_aKoG :: Sing (d_aKoE :: a_aKib))
    = singFun1 @((<>@#@$$) (d_aKoE :: a_aKib)) ((%<>) s_aKoG)
instance SSemigroup a_aKib =>
          SingI (SconcatSym0 :: (~>) (NonEmpty a_aKib) a_aKib) where
  sing = singFun1 @SconcatSym0 sSconcat
