{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
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
-- Module      :  Data.Maybe.Singletons
-- Copyright   :  (C) 2013-2014 Richard Eisenberg, Jan Stolarek
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines functions and datatypes relating to the singleton for 'Maybe',
-- including singled versions of all the definitions in @Data.Maybe@.
--
-- Because many of these definitions are produced by Template Haskell,
-- it is not possible to create proper Haddock documentation. Please look
-- up the corresponding operation in @Data.Maybe@. Also, please excuse
-- the apparent repeated variable names. This is due to an interaction
-- between Template Haskell and Haddock.
--
----------------------------------------------------------------------------


module Data.Maybe.Singletons (
  -- The 'Maybe' singleton
  Sing, SMaybe(..),

  -- * Singletons from @Data.Maybe@
  maybe_, Maybe_, sMaybe_,
  -- | The preceding two definitions are derived from the function 'maybe' in
  -- @Data.Maybe@. The extra underscore is to avoid name clashes with the type
  -- 'Maybe'.

  IsJust, sIsJust, IsNothing, sIsNothing,
  FromJust, sFromJust, FromMaybe, sFromMaybe, ListToMaybe, sListToMaybe,
  MaybeToList, sMaybeToList, CatMaybes, sCatMaybes, MapMaybe, sMapMaybe,

  -- * Defunctionalization symbols
  NothingSym0, JustSym0, JustSym1,

  Maybe_Sym0, Maybe_Sym1, Maybe_Sym2, Maybe_Sym3,
  IsJustSym0, IsJustSym1, IsNothingSym0, IsNothingSym1,
  FromJustSym0, FromJustSym1, FromMaybeSym0, FromMaybeSym1, FromMaybeSym2,
  ListToMaybeSym0, ListToMaybeSym1, MaybeToListSym0, MaybeToListSym1,
  CatMaybesSym0, CatMaybesSym1, MapMaybeSym0, MapMaybeSym1, MapMaybeSym2
  ) where

import Data.Singletons.Base.Instances
import Data.Singletons.TH
import GHC.TypeLits.Singletons
import Data.Kind (Type)

maybe_ ::
      b_a1G3d -> (a_a1G3e -> b_a1G3d) -> Maybe a_a1G3e -> b_a1G3d
maybe_ n_a1G3g _ Nothing = n_a1G3g
maybe_ _ f_a1G3h (Just x_a1G3i) = f_a1G3h x_a1G3i
type Maybe_Sym0 :: (~>) b_a1G3d ((~>) ((~>) a_a1G3e b_a1G3d) ((~>) (Maybe a_a1G3e) b_a1G3d))
data Maybe_Sym0 :: (~>) b_a1G3d ((~>) ((~>) a_a1G3e b_a1G3d) ((~>) (Maybe a_a1G3e) b_a1G3d))
  where
    Maybe_Sym0KindInference :: SameKind (Apply Maybe_Sym0 arg_a1G3y) (Maybe_Sym1 arg_a1G3y) =>
                                Maybe_Sym0 a6989586621679409789
type instance Apply @b_a1G3d @((~>) ((~>) a_a1G3e b_a1G3d) ((~>) (Maybe a_a1G3e) b_a1G3d)) Maybe_Sym0 a6989586621679409789 = Maybe_Sym1 a6989586621679409789
instance SuppressUnusedWarnings Maybe_Sym0 where
  suppressUnusedWarnings = snd ((,) Maybe_Sym0KindInference ())
type Maybe_Sym1 :: b_a1G3d
                    -> (~>) ((~>) a_a1G3e b_a1G3d) ((~>) (Maybe a_a1G3e) b_a1G3d)
data Maybe_Sym1 (a6989586621679409789 :: b_a1G3d) :: (~>) ((~>) a_a1G3e b_a1G3d) ((~>) (Maybe a_a1G3e) b_a1G3d)
  where
    Maybe_Sym1KindInference :: SameKind (Apply (Maybe_Sym1 a6989586621679409789) arg_a1G3y) (Maybe_Sym2 a6989586621679409789 arg_a1G3y) =>
                                Maybe_Sym1 a6989586621679409789 a6989586621679409790
type instance Apply @((~>) a_a1G3e b_a1G3d) @((~>) (Maybe a_a1G3e) b_a1G3d) (Maybe_Sym1 a6989586621679409789) a6989586621679409790 = Maybe_Sym2 a6989586621679409789 a6989586621679409790
instance SuppressUnusedWarnings (Maybe_Sym1 a6989586621679409789) where
  suppressUnusedWarnings = snd ((,) Maybe_Sym1KindInference ())
type Maybe_Sym2 :: b_a1G3d
                    -> (~>) a_a1G3e b_a1G3d -> (~>) (Maybe a_a1G3e) b_a1G3d
data Maybe_Sym2 (a6989586621679409789 :: b_a1G3d) (a6989586621679409790 :: (~>) a_a1G3e b_a1G3d) :: (~>) (Maybe a_a1G3e) b_a1G3d
  where
    Maybe_Sym2KindInference :: SameKind (Apply (Maybe_Sym2 a6989586621679409789 a6989586621679409790) arg_a1G3y) (Maybe_Sym3 a6989586621679409789 a6989586621679409790 arg_a1G3y) =>
                                Maybe_Sym2 a6989586621679409789 a6989586621679409790 a6989586621679409791
type instance Apply @(Maybe a_a1G3e) @b_a1G3d (Maybe_Sym2 a6989586621679409789 a6989586621679409790) a6989586621679409791 = Maybe_ a6989586621679409789 a6989586621679409790 a6989586621679409791
instance SuppressUnusedWarnings (Maybe_Sym2 a6989586621679409789 a6989586621679409790) where
  suppressUnusedWarnings = snd ((,) Maybe_Sym2KindInference ())
type Maybe_Sym3 :: b_a1G3d
                    -> (~>) a_a1G3e b_a1G3d -> Maybe a_a1G3e -> b_a1G3d
type family Maybe_Sym3 @b_a1G3d @a_a1G3e (a6989586621679409789 :: b_a1G3d) (a6989586621679409790 :: (~>) a_a1G3e b_a1G3d) (a6989586621679409791 :: Maybe a_a1G3e) :: b_a1G3d where
  Maybe_Sym3 a6989586621679409789 a6989586621679409790 a6989586621679409791 = Maybe_ a6989586621679409789 a6989586621679409790 a6989586621679409791
type Maybe_ :: b_a1G3d
                -> (~>) a_a1G3e b_a1G3d -> Maybe a_a1G3e -> b_a1G3d
type family Maybe_ @b_a1G3d @a_a1G3e (a_a1G3v :: b_a1G3d) (a_a1G3w :: (~>) a_a1G3e b_a1G3d) (a_a1G3x :: Maybe a_a1G3e) :: b_a1G3d where
  Maybe_ n_a1G3C _ 'Nothing = n_a1G3C
  Maybe_ _ f_a1G3D ('Just x_a1G3E) = Apply f_a1G3D x_a1G3E
sMaybe_ ::
  (forall (t_a1G3F :: b_a1G3d)
          (t_a1G3G :: (~>) a_a1G3e b_a1G3d)
          (t_a1G3H :: Maybe a_a1G3e).
    Sing t_a1G3F
    -> Sing t_a1G3G
      -> Sing t_a1G3H
          -> Sing (Maybe_ t_a1G3F t_a1G3G t_a1G3H :: b_a1G3d) :: Type)
sMaybe_ (sN :: Sing n_a1G3C) _ SNothing = sN
sMaybe_ _ (sF :: Sing f_a1G3D) (SJust (sX :: Sing x_a1G3E))
  = applySing sF sX
instance SingI (Maybe_Sym0 :: (~>) b_a1G3d ((~>) ((~>) a_a1G3e b_a1G3d) ((~>) (Maybe a_a1G3e) b_a1G3d))) where
  sing = singFun3 @Maybe_Sym0 sMaybe_
instance SingI d_a1G3I =>
          SingI (Maybe_Sym1 (d_a1G3I :: b_a1G3d) :: (~>) ((~>) a_a1G3e b_a1G3d) ((~>) (Maybe a_a1G3e) b_a1G3d)) where
  sing
    = singFun2
        @(Maybe_Sym1 (d_a1G3I :: b_a1G3d)) (sMaybe_ (sing @d_a1G3I))
instance SingI1 (Maybe_Sym1 :: b_a1G3d
                                -> (~>) ((~>) a_a1G3e b_a1G3d) ((~>) (Maybe a_a1G3e) b_a1G3d)) where
  liftSing (s_a1G3O :: Sing (d_a1G3I :: b_a1G3d))
    = singFun2 @(Maybe_Sym1 (d_a1G3I :: b_a1G3d)) (sMaybe_ s_a1G3O)
instance (SingI d_a1G3I, SingI d_a1G3J) =>
          SingI (Maybe_Sym2 (d_a1G3I :: b_a1G3d) (d_a1G3J :: (~>) a_a1G3e b_a1G3d) :: (~>) (Maybe a_a1G3e) b_a1G3d) where
  sing
    = singFun1
        @(Maybe_Sym2 (d_a1G3I :: b_a1G3d) (d_a1G3J :: (~>) a_a1G3e b_a1G3d))
        (sMaybe_ (sing @d_a1G3I) (sing @d_a1G3J))
instance SingI d_a1G3I =>
          SingI1 (Maybe_Sym2 (d_a1G3I :: b_a1G3d) :: (~>) a_a1G3e b_a1G3d
                                                    -> (~>) (Maybe a_a1G3e) b_a1G3d) where
  liftSing (s_a1G3L :: Sing (d_a1G3J :: (~>) a_a1G3e b_a1G3d))
    = singFun1
        @(Maybe_Sym2 (d_a1G3I :: b_a1G3d) (d_a1G3J :: (~>) a_a1G3e b_a1G3d))
        (sMaybe_ (sing @d_a1G3I) s_a1G3L)
instance SingI2 (Maybe_Sym2 :: b_a1G3d
                                -> (~>) a_a1G3e b_a1G3d -> (~>) (Maybe a_a1G3e) b_a1G3d) where
  liftSing2
    (s_a1G3M :: Sing (d_a1G3I :: b_a1G3d))
    (s_a1G3N :: Sing (d_a1G3J :: (~>) a_a1G3e b_a1G3d))
    = singFun1
        @(Maybe_Sym2 (d_a1G3I :: b_a1G3d) (d_a1G3J :: (~>) a_a1G3e b_a1G3d))
        (sMaybe_ s_a1G3M s_a1G3N)
type family Let6989586621679411848RsSym0 (f6989586621679411845 :: (~>) a6989586621679411695 (Maybe b6989586621679411696)) x6989586621679411846 xs6989586621679411847 where
      Let6989586621679411848RsSym0 f6989586621679411845 x6989586621679411846 xs6989586621679411847 = Let6989586621679411848Rs f6989586621679411845 x6989586621679411846 xs6989586621679411847
type family Let6989586621679411848Rs (f6989586621679411845 :: (~>) a6989586621679411695 (Maybe b6989586621679411696)) x6989586621679411846 xs6989586621679411847 where
  Let6989586621679411848Rs f_a1GAJ x_a1GAK xs_a1GAL = Apply (Apply MapMaybeSym0 f_a1GAJ) xs_a1GAL
type family LamCases_6989586621679411850_a1GAP (f6989586621679411845 :: (~>) a6989586621679411695 (Maybe b6989586621679411696)) x6989586621679411846 xs6989586621679411847 a_6989586621679411853_a1GAS where
  LamCases_6989586621679411850_a1GAP f_a1GAJ x_a1GAK xs_a1GAL 'Nothing = Let6989586621679411848RsSym0 f_a1GAJ x_a1GAK xs_a1GAL
  LamCases_6989586621679411850_a1GAP f_a1GAJ x_a1GAK xs_a1GAL ('Just r_a1GAQ) = Apply (Apply (:@#@$) r_a1GAQ) (Let6989586621679411848RsSym0 f_a1GAJ x_a1GAK xs_a1GAL)
data LamCases_6989586621679411850Sym0 (f6989586621679411845 :: (~>) a6989586621679411695 (Maybe b6989586621679411696)) x6989586621679411846 xs6989586621679411847 a_69895866216794118536989586621679411854
  where
    LamCases_6989586621679411850Sym0KindInference :: SameKind (Apply (LamCases_6989586621679411850Sym0 f6989586621679411845 x6989586621679411846 xs6989586621679411847) arg_a1GAT) (LamCases_6989586621679411850Sym1 f6989586621679411845 x6989586621679411846 xs6989586621679411847 arg_a1GAT) =>
                                                      LamCases_6989586621679411850Sym0 f6989586621679411845 x6989586621679411846 xs6989586621679411847 a_69895866216794118536989586621679411854
type instance Apply @_ @_ (LamCases_6989586621679411850Sym0 f6989586621679411845 x6989586621679411846 xs6989586621679411847) a_69895866216794118536989586621679411854 = LamCases_6989586621679411850_a1GAP f6989586621679411845 x6989586621679411846 xs6989586621679411847 a_69895866216794118536989586621679411854
instance SuppressUnusedWarnings (LamCases_6989586621679411850Sym0 f6989586621679411845 x6989586621679411846 xs6989586621679411847) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679411850Sym0KindInference ())
type family LamCases_6989586621679411850Sym1 (f6989586621679411845 :: (~>) a6989586621679411695 (Maybe b6989586621679411696)) x6989586621679411846 xs6989586621679411847 a_69895866216794118536989586621679411854 where
  LamCases_6989586621679411850Sym1 f6989586621679411845 x6989586621679411846 xs6989586621679411847 a_69895866216794118536989586621679411854 = LamCases_6989586621679411850_a1GAP f6989586621679411845 x6989586621679411846 xs6989586621679411847 a_69895866216794118536989586621679411854
type family LamCases_6989586621679411877_a1GBg (d6989586621679411875 :: a6989586621679411700) (x6989586621679411876 :: Maybe a6989586621679411700) a_6989586621679411880_a1GBj where
  LamCases_6989586621679411877_a1GBg d_a1GBd x_a1GBe 'Nothing = d_a1GBd
  LamCases_6989586621679411877_a1GBg d_a1GBd x_a1GBe ('Just v_a1GBh) = v_a1GBh
data LamCases_6989586621679411877Sym0 (d6989586621679411875 :: a6989586621679411700) (x6989586621679411876 :: Maybe a6989586621679411700) a_69895866216794118806989586621679411881
  where
    LamCases_6989586621679411877Sym0KindInference :: SameKind (Apply (LamCases_6989586621679411877Sym0 d6989586621679411875 x6989586621679411876) arg_a1GBk) (LamCases_6989586621679411877Sym1 d6989586621679411875 x6989586621679411876 arg_a1GBk) =>
                                                      LamCases_6989586621679411877Sym0 d6989586621679411875 x6989586621679411876 a_69895866216794118806989586621679411881
type instance Apply @_ @_ (LamCases_6989586621679411877Sym0 d6989586621679411875 x6989586621679411876) a_69895866216794118806989586621679411881 = LamCases_6989586621679411877_a1GBg d6989586621679411875 x6989586621679411876 a_69895866216794118806989586621679411881
instance SuppressUnusedWarnings (LamCases_6989586621679411877Sym0 d6989586621679411875 x6989586621679411876) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679411877Sym0KindInference ())
type family LamCases_6989586621679411877Sym1 (d6989586621679411875 :: a6989586621679411700) (x6989586621679411876 :: Maybe a6989586621679411700) a_69895866216794118806989586621679411881 where
  LamCases_6989586621679411877Sym1 d6989586621679411875 x6989586621679411876 a_69895866216794118806989586621679411881 = LamCases_6989586621679411877_a1GBg d6989586621679411875 x6989586621679411876 a_69895866216794118806989586621679411881
type MapMaybeSym0 :: (~>) ((~>) a_a1Gyj (Maybe b_a1Gyk)) ((~>) [a_a1Gyj] [b_a1Gyk])
data MapMaybeSym0 :: (~>) ((~>) a_a1Gyj (Maybe b_a1Gyk)) ((~>) [a_a1Gyj] [b_a1Gyk])
  where
    MapMaybeSym0KindInference :: SameKind (Apply MapMaybeSym0 arg_a1GAG) (MapMaybeSym1 arg_a1GAG) =>
                                  MapMaybeSym0 a6989586621679411843
type instance Apply @((~>) a_a1Gyj (Maybe b_a1Gyk)) @((~>) [a_a1Gyj] [b_a1Gyk]) MapMaybeSym0 a6989586621679411843 = MapMaybeSym1 a6989586621679411843
instance SuppressUnusedWarnings MapMaybeSym0 where
  suppressUnusedWarnings = snd ((,) MapMaybeSym0KindInference ())
type MapMaybeSym1 :: (~>) a_a1Gyj (Maybe b_a1Gyk)
                      -> (~>) [a_a1Gyj] [b_a1Gyk]
data MapMaybeSym1 (a6989586621679411843 :: (~>) a_a1Gyj (Maybe b_a1Gyk)) :: (~>) [a_a1Gyj] [b_a1Gyk]
  where
    MapMaybeSym1KindInference :: SameKind (Apply (MapMaybeSym1 a6989586621679411843) arg_a1GAG) (MapMaybeSym2 a6989586621679411843 arg_a1GAG) =>
                                  MapMaybeSym1 a6989586621679411843 a6989586621679411844
type instance Apply @[a_a1Gyj] @[b_a1Gyk] (MapMaybeSym1 a6989586621679411843) a6989586621679411844 = MapMaybe a6989586621679411843 a6989586621679411844
instance SuppressUnusedWarnings (MapMaybeSym1 a6989586621679411843) where
  suppressUnusedWarnings = snd ((,) MapMaybeSym1KindInference ())
type MapMaybeSym2 :: (~>) a_a1Gyj (Maybe b_a1Gyk)
                      -> [a_a1Gyj] -> [b_a1Gyk]
type family MapMaybeSym2 @a_a1Gyj @b_a1Gyk (a6989586621679411843 :: (~>) a_a1Gyj (Maybe b_a1Gyk)) (a6989586621679411844 :: [a_a1Gyj]) :: [b_a1Gyk] where
  MapMaybeSym2 a6989586621679411843 a6989586621679411844 = MapMaybe a6989586621679411843 a6989586621679411844
type CatMaybesSym0 :: (~>) [Maybe a_a1Gyl] [a_a1Gyl]
data CatMaybesSym0 :: (~>) [Maybe a_a1Gyl] [a_a1Gyl]
  where
    CatMaybesSym0KindInference :: SameKind (Apply CatMaybesSym0 arg_a1GAV) (CatMaybesSym1 arg_a1GAV) =>
                                  CatMaybesSym0 a6989586621679411858
type instance Apply @[Maybe a_a1Gyl] @[a_a1Gyl] CatMaybesSym0 a6989586621679411858 = CatMaybes a6989586621679411858
instance SuppressUnusedWarnings CatMaybesSym0 where
  suppressUnusedWarnings = snd ((,) CatMaybesSym0KindInference ())
type CatMaybesSym1 :: [Maybe a_a1Gyl] -> [a_a1Gyl]
type family CatMaybesSym1 @a_a1Gyl (a6989586621679411858 :: [Maybe a_a1Gyl]) :: [a_a1Gyl] where
  CatMaybesSym1 a6989586621679411858 = CatMaybes a6989586621679411858
type ListToMaybeSym0 :: (~>) [a_a1Gym] (Maybe a_a1Gym)
data ListToMaybeSym0 :: (~>) [a_a1Gym] (Maybe a_a1Gym)
  where
    ListToMaybeSym0KindInference :: SameKind (Apply ListToMaybeSym0 arg_a1GB1) (ListToMaybeSym1 arg_a1GB1) =>
                                    ListToMaybeSym0 a6989586621679411864
type instance Apply @[a_a1Gym] @(Maybe a_a1Gym) ListToMaybeSym0 a6989586621679411864 = ListToMaybe a6989586621679411864
instance SuppressUnusedWarnings ListToMaybeSym0 where
  suppressUnusedWarnings = snd ((,) ListToMaybeSym0KindInference ())
type ListToMaybeSym1 :: [a_a1Gym] -> Maybe a_a1Gym
type family ListToMaybeSym1 @a_a1Gym (a6989586621679411864 :: [a_a1Gym]) :: Maybe a_a1Gym where
  ListToMaybeSym1 a6989586621679411864 = ListToMaybe a6989586621679411864
type MaybeToListSym0 :: (~>) (Maybe a_a1Gyn) [a_a1Gyn]
data MaybeToListSym0 :: (~>) (Maybe a_a1Gyn) [a_a1Gyn]
  where
    MaybeToListSym0KindInference :: SameKind (Apply MaybeToListSym0 arg_a1GB5) (MaybeToListSym1 arg_a1GB5) =>
                                    MaybeToListSym0 a6989586621679411868
type instance Apply @(Maybe a_a1Gyn) @[a_a1Gyn] MaybeToListSym0 a6989586621679411868 = MaybeToList a6989586621679411868
instance SuppressUnusedWarnings MaybeToListSym0 where
  suppressUnusedWarnings = snd ((,) MaybeToListSym0KindInference ())
type MaybeToListSym1 :: Maybe a_a1Gyn -> [a_a1Gyn]
type family MaybeToListSym1 @a_a1Gyn (a6989586621679411868 :: Maybe a_a1Gyn) :: [a_a1Gyn] where
  MaybeToListSym1 a6989586621679411868 = MaybeToList a6989586621679411868
type FromMaybeSym0 :: (~>) a_a1Gyo ((~>) (Maybe a_a1Gyo) a_a1Gyo)
data FromMaybeSym0 :: (~>) a_a1Gyo ((~>) (Maybe a_a1Gyo) a_a1Gyo)
  where
    FromMaybeSym0KindInference :: SameKind (Apply FromMaybeSym0 arg_a1GBa) (FromMaybeSym1 arg_a1GBa) =>
                                  FromMaybeSym0 a6989586621679411873
type instance Apply @a_a1Gyo @((~>) (Maybe a_a1Gyo) a_a1Gyo) FromMaybeSym0 a6989586621679411873 = FromMaybeSym1 a6989586621679411873
instance SuppressUnusedWarnings FromMaybeSym0 where
  suppressUnusedWarnings = snd ((,) FromMaybeSym0KindInference ())
type FromMaybeSym1 :: a_a1Gyo -> (~>) (Maybe a_a1Gyo) a_a1Gyo
data FromMaybeSym1 (a6989586621679411873 :: a_a1Gyo) :: (~>) (Maybe a_a1Gyo) a_a1Gyo
  where
    FromMaybeSym1KindInference :: SameKind (Apply (FromMaybeSym1 a6989586621679411873) arg_a1GBa) (FromMaybeSym2 a6989586621679411873 arg_a1GBa) =>
                                  FromMaybeSym1 a6989586621679411873 a6989586621679411874
type instance Apply @(Maybe a_a1Gyo) @a_a1Gyo (FromMaybeSym1 a6989586621679411873) a6989586621679411874 = FromMaybe a6989586621679411873 a6989586621679411874
instance SuppressUnusedWarnings (FromMaybeSym1 a6989586621679411873) where
  suppressUnusedWarnings = snd ((,) FromMaybeSym1KindInference ())
type FromMaybeSym2 :: a_a1Gyo -> Maybe a_a1Gyo -> a_a1Gyo
type family FromMaybeSym2 @a_a1Gyo (a6989586621679411873 :: a_a1Gyo) (a6989586621679411874 :: Maybe a_a1Gyo) :: a_a1Gyo where
  FromMaybeSym2 a6989586621679411873 a6989586621679411874 = FromMaybe a6989586621679411873 a6989586621679411874
type FromJustSym0 :: (~>) (Maybe a_a1Gyp) a_a1Gyp
data FromJustSym0 :: (~>) (Maybe a_a1Gyp) a_a1Gyp
  where
    FromJustSym0KindInference :: SameKind (Apply FromJustSym0 arg_a1GBm) (FromJustSym1 arg_a1GBm) =>
                                  FromJustSym0 a6989586621679411885
type instance Apply @(Maybe a_a1Gyp) @a_a1Gyp FromJustSym0 a6989586621679411885 = FromJust a6989586621679411885
instance SuppressUnusedWarnings FromJustSym0 where
  suppressUnusedWarnings = snd ((,) FromJustSym0KindInference ())
type FromJustSym1 :: Maybe a_a1Gyp -> a_a1Gyp
type family FromJustSym1 @a_a1Gyp (a6989586621679411885 :: Maybe a_a1Gyp) :: a_a1Gyp where
  FromJustSym1 a6989586621679411885 = FromJust a6989586621679411885
type IsNothingSym0 :: (~>) (Maybe a_a1Gyq) Bool
data IsNothingSym0 :: (~>) (Maybe a_a1Gyq) Bool
  where
    IsNothingSym0KindInference :: SameKind (Apply IsNothingSym0 arg_a1GBq) (IsNothingSym1 arg_a1GBq) =>
                                  IsNothingSym0 a6989586621679411889
type instance Apply @(Maybe a_a1Gyq) @Bool IsNothingSym0 a6989586621679411889 = IsNothing a6989586621679411889
instance SuppressUnusedWarnings IsNothingSym0 where
  suppressUnusedWarnings = snd ((,) IsNothingSym0KindInference ())
type IsNothingSym1 :: Maybe a_a1Gyq -> Bool
type family IsNothingSym1 @a_a1Gyq (a6989586621679411889 :: Maybe a_a1Gyq) :: Bool where
  IsNothingSym1 a6989586621679411889 = IsNothing a6989586621679411889
type IsJustSym0 :: (~>) (Maybe a_a1Gyr) Bool
data IsJustSym0 :: (~>) (Maybe a_a1Gyr) Bool
  where
    IsJustSym0KindInference :: SameKind (Apply IsJustSym0 arg_a1GBt) (IsJustSym1 arg_a1GBt) =>
                                IsJustSym0 a6989586621679411892
type instance Apply @(Maybe a_a1Gyr) @Bool IsJustSym0 a6989586621679411892 = IsJust a6989586621679411892
instance SuppressUnusedWarnings IsJustSym0 where
  suppressUnusedWarnings = snd ((,) IsJustSym0KindInference ())
type IsJustSym1 :: Maybe a_a1Gyr -> Bool
type family IsJustSym1 @a_a1Gyr (a6989586621679411892 :: Maybe a_a1Gyr) :: Bool where
  IsJustSym1 a6989586621679411892 = IsJust a6989586621679411892
type MapMaybe :: (~>) a_a1Gyj (Maybe b_a1Gyk)
                  -> [a_a1Gyj] -> [b_a1Gyk]
type family MapMaybe @a_a1Gyj @b_a1Gyk (a_a1GAE :: (~>) a_a1Gyj (Maybe b_a1Gyk)) (a_a1GAF :: [a_a1Gyj]) :: [b_a1Gyk] where
  MapMaybe _ '[] = NilSym0
  MapMaybe f_a1GAJ ('(:) x_a1GAK xs_a1GAL) = Apply (LamCases_6989586621679411850Sym0 f_a1GAJ x_a1GAK xs_a1GAL) (Apply f_a1GAJ x_a1GAK)
type CatMaybes :: [Maybe a_a1Gyl] -> [a_a1Gyl]
type family CatMaybes @a_a1Gyl (a_a1GAU :: [Maybe a_a1Gyl]) :: [a_a1Gyl] where
  CatMaybes '[] = NilSym0
  CatMaybes ('(:) ('Just x_a1GAX) xs_a1GAY) = Apply (Apply (:@#@$) x_a1GAX) (Apply CatMaybesSym0 xs_a1GAY)
  CatMaybes ('(:) 'Nothing xs_a1GAZ) = Apply CatMaybesSym0 xs_a1GAZ
type ListToMaybe :: [a_a1Gym] -> Maybe a_a1Gym
type family ListToMaybe @a_a1Gym (a_a1GB0 :: [a_a1Gym]) :: Maybe a_a1Gym where
  ListToMaybe '[] = NothingSym0
  ListToMaybe ('(:) a_a1GB3 _) = Apply JustSym0 a_a1GB3
type MaybeToList :: Maybe a_a1Gyn -> [a_a1Gyn]
type family MaybeToList @a_a1Gyn (a_a1GB4 :: Maybe a_a1Gyn) :: [a_a1Gyn] where
  MaybeToList 'Nothing = NilSym0
  MaybeToList ('Just x_a1GB7) = Apply (Apply (:@#@$) x_a1GB7) NilSym0
type FromMaybe :: a_a1Gyo -> Maybe a_a1Gyo -> a_a1Gyo
type family FromMaybe @a_a1Gyo (a_a1GB8 :: a_a1Gyo) (a_a1GB9 :: Maybe a_a1Gyo) :: a_a1Gyo where
  FromMaybe d_a1GBd x_a1GBe = Apply (LamCases_6989586621679411877Sym0 d_a1GBd x_a1GBe) x_a1GBe
type FromJust :: Maybe a_a1Gyp -> a_a1Gyp
type family FromJust @a_a1Gyp (a_a1GBl :: Maybe a_a1Gyp) :: a_a1Gyp where
  FromJust 'Nothing = Apply ErrorSym0 "Maybe.fromJust: Nothing"
  FromJust ('Just x_a1GBo) = x_a1GBo
type IsNothing :: Maybe a_a1Gyq -> Bool
type family IsNothing @a_a1Gyq (a_a1GBp :: Maybe a_a1Gyq) :: Bool where
  IsNothing 'Nothing = TrueSym0
  IsNothing ('Just _) = FalseSym0
type IsJust :: Maybe a_a1Gyr -> Bool
type family IsJust @a_a1Gyr (a_a1GBs :: Maybe a_a1Gyr) :: Bool where
  IsJust 'Nothing = FalseSym0
  IsJust ('Just _) = TrueSym0
sMapMaybe ::
  (forall (t_a1GBv :: (~>) a_a1Gyj (Maybe b_a1Gyk))
          (t_a1GBw :: [a_a1Gyj]).
    Sing t_a1GBv
    -> Sing t_a1GBw
      -> Sing (MapMaybe t_a1GBv t_a1GBw :: [b_a1Gyk]) :: Type)
sCatMaybes ::
  (forall (t_a1GBA :: [Maybe a_a1Gyl]).
    Sing t_a1GBA -> Sing (CatMaybes t_a1GBA :: [a_a1Gyl]) :: Type)
sListToMaybe ::
  (forall (t_a1GBC :: [a_a1Gym]).
    Sing t_a1GBC
    -> Sing (ListToMaybe t_a1GBC :: Maybe a_a1Gym) :: Type)
sMaybeToList ::
  (forall (t_a1GBE :: Maybe a_a1Gyn).
    Sing t_a1GBE -> Sing (MaybeToList t_a1GBE :: [a_a1Gyn]) :: Type)
sFromMaybe ::
  (forall (t_a1GBG :: a_a1Gyo) (t_a1GBH :: Maybe a_a1Gyo).
    Sing t_a1GBG
    -> Sing t_a1GBH
      -> Sing (FromMaybe t_a1GBG t_a1GBH :: a_a1Gyo) :: Type)
sFromJust ::
  (forall (t_a1GBL :: Maybe a_a1Gyp).
    Sing t_a1GBL -> Sing (FromJust t_a1GBL :: a_a1Gyp) :: Type)
sIsNothing ::
  (forall (t_a1GBN :: Maybe a_a1Gyq).
    Sing t_a1GBN -> Sing (IsNothing t_a1GBN :: Bool) :: Type)
sIsJust ::
  (forall (t_a1GBP :: Maybe a_a1Gyr).
    Sing t_a1GBP -> Sing (IsJust t_a1GBP :: Bool) :: Type)
sMapMaybe _ SNil = SNil
sMapMaybe
  (sF :: Sing f_a1GAJ)
  (SCons (sX :: Sing x_a1GAK) (sXs :: Sing xs_a1GAL))
  = let
      sRs :: Sing @_ (Let6989586621679411848Rs f_a1GAJ x_a1GAK xs_a1GAL)
      sRs
        = applySing (applySing (singFun2 @MapMaybeSym0 sMapMaybe) sF) sXs
    in
      applySing
        (singFun1
            @(LamCases_6989586621679411850Sym0 f_a1GAJ x_a1GAK xs_a1GAL)
            (\cases
              SNothing -> sRs
              (SJust (sR :: Sing r_a1GAQ))
                -> applySing (applySing (singFun2 @(:@#@$) SCons) sR) sRs))
        (applySing sF sX)
sCatMaybes SNil = SNil
sCatMaybes
  (SCons (SJust (sX :: Sing x_a1GAX)) (sXs :: Sing xs_a1GAY))
  = applySing
      (applySing (singFun2 @(:@#@$) SCons) sX)
      (applySing (singFun1 @CatMaybesSym0 sCatMaybes) sXs)
sCatMaybes (SCons SNothing (sXs :: Sing xs_a1GAZ))
  = applySing (singFun1 @CatMaybesSym0 sCatMaybes) sXs
sListToMaybe SNil = SNothing
sListToMaybe (SCons (sA :: Sing a_a1GB3) _)
  = applySing (singFun1 @JustSym0 SJust) sA
sMaybeToList SNothing = SNil
sMaybeToList (SJust (sX :: Sing x_a1GB7))
  = applySing (applySing (singFun2 @(:@#@$) SCons) sX) SNil
sFromMaybe (sD :: Sing d_a1GBd) (sX :: Sing x_a1GBe)
  = applySing
      (singFun1
          @(LamCases_6989586621679411877Sym0 d_a1GBd x_a1GBe)
          (\cases
            SNothing -> sD
            (SJust (sV :: Sing v_a1GBh)) -> sV))
      sX
sFromJust SNothing
  = applySing
      (singFun1 @ErrorSym0 sError)
      (sing :: Sing "Maybe.fromJust: Nothing")
sFromJust (SJust (sX :: Sing x_a1GBo)) = sX
sIsNothing SNothing = STrue
sIsNothing (SJust _) = SFalse
sIsJust SNothing = SFalse
sIsJust (SJust _) = STrue
instance SingI (MapMaybeSym0 :: (~>) ((~>) a_a1Gyj (Maybe b_a1Gyk)) ((~>) [a_a1Gyj] [b_a1Gyk])) where
  sing = singFun2 @MapMaybeSym0 sMapMaybe
instance SingI d_a1GBx =>
          SingI (MapMaybeSym1 (d_a1GBx :: (~>) a_a1Gyj (Maybe b_a1Gyk)) :: (~>) [a_a1Gyj] [b_a1Gyk]) where
  sing
    = singFun1
        @(MapMaybeSym1 (d_a1GBx :: (~>) a_a1Gyj (Maybe b_a1Gyk)))
        (sMapMaybe (sing @d_a1GBx))
instance SingI1 (MapMaybeSym1 :: (~>) a_a1Gyj (Maybe b_a1Gyk)
                                  -> (~>) [a_a1Gyj] [b_a1Gyk]) where
  liftSing
    (s_a1GBz :: Sing (d_a1GBx :: (~>) a_a1Gyj (Maybe b_a1Gyk)))
    = singFun1
        @(MapMaybeSym1 (d_a1GBx :: (~>) a_a1Gyj (Maybe b_a1Gyk)))
        (sMapMaybe s_a1GBz)
instance SingI (CatMaybesSym0 :: (~>) [Maybe a_a1Gyl] [a_a1Gyl]) where
  sing = singFun1 @CatMaybesSym0 sCatMaybes
instance SingI (ListToMaybeSym0 :: (~>) [a_a1Gym] (Maybe a_a1Gym)) where
  sing = singFun1 @ListToMaybeSym0 sListToMaybe
instance SingI (MaybeToListSym0 :: (~>) (Maybe a_a1Gyn) [a_a1Gyn]) where
  sing = singFun1 @MaybeToListSym0 sMaybeToList
instance SingI (FromMaybeSym0 :: (~>) a_a1Gyo ((~>) (Maybe a_a1Gyo) a_a1Gyo)) where
  sing = singFun2 @FromMaybeSym0 sFromMaybe
instance SingI d_a1GBI =>
          SingI (FromMaybeSym1 (d_a1GBI :: a_a1Gyo) :: (~>) (Maybe a_a1Gyo) a_a1Gyo) where
  sing
    = singFun1
        @(FromMaybeSym1 (d_a1GBI :: a_a1Gyo)) (sFromMaybe (sing @d_a1GBI))
instance SingI1 (FromMaybeSym1 :: a_a1Gyo
                                  -> (~>) (Maybe a_a1Gyo) a_a1Gyo) where
  liftSing (s_a1GBK :: Sing (d_a1GBI :: a_a1Gyo))
    = singFun1
        @(FromMaybeSym1 (d_a1GBI :: a_a1Gyo)) (sFromMaybe s_a1GBK)
instance SingI (FromJustSym0 :: (~>) (Maybe a_a1Gyp) a_a1Gyp) where
  sing = singFun1 @FromJustSym0 sFromJust
instance SingI (IsNothingSym0 :: (~>) (Maybe a_a1Gyq) Bool) where
  sing = singFun1 @IsNothingSym0 sIsNothing
instance SingI (IsJustSym0 :: (~>) (Maybe a_a1Gyr) Bool) where
  sing = singFun1 @IsJustSym0 sIsJust
