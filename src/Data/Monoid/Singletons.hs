{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NoNamedWildCards #-}

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
{-# LANGUAGE StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Monoid.Singletons
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted version of 'Monoid', 'PMonoid', and the
-- singleton version, 'SMonoid'.
--
----------------------------------------------------------------------------

module Data.Monoid.Singletons (
  PMonoid(..), SMonoid(..),

  Sing, SDual(..), SAll(..), SAny(..),
  SSum(..), SProduct(..), SFirst(..), SLast(..),
  GetDual, GetAll, GetAny, GetSum, GetProduct, GetFirst, GetLast,
  sGetDual, sGetAll, sGetAny, sGetSum, sGetProduct, sGetFirst, sGetLast,

  -- ** Defunctionalization symbols
  MemptySym0,
  MappendSym0, MappendSym1, MappendSym2,
  MconcatSym0, MconcatSym1,
  DualSym0, DualSym1, GetDualSym0, GetDualSym1,
  AllSym0, AllSym1, GetAllSym0, GetAllSym1,
  AnySym0, AnySym1, GetAnySym0, GetAnySym1,
  SumSym0, SumSym1, GetSumSym0, GetSumSym1,
  ProductSym0, ProductSym1, GetProductSym0, GetProductSym1,
  FirstSym0, FirstSym1, GetFirstSym0, GetFirstSym1,
  LastSym0, LastSym1, GetLastSym0, GetLastSym1
  ) where

import Control.Monad.Singletons.Internal
import Data.Eq.Singletons
import Data.Monoid (First(..), Last(..))
import Data.Ord (Down(..))
import Data.Ord.Singletons
import Data.Semigroup hiding (First(..), Last(..))
import Data.Semigroup.Singletons.Internal.Classes
import Data.Semigroup.Singletons.Internal.Wrappers hiding
       (SFirst, SLast,
        FirstSym0, FirstSym1, FirstSym0KindInference,
        LastSym0,  LastSym1,  LastSym0KindInference,
        GetFirst, sGetFirst, GetFirstSym0, GetFirstSym1, GetFirstSym0KindInference,
        GetLast,  sGetLast,  GetLastSym0,  GetLastSym1, GetLastSym0KindInference)
import Data.Singletons.Base.Instances

import Data.Singletons.TH
import GHC.Base.Singletons
import GHC.Num.Singletons
import GHC.TypeLits (Symbol)
import Text.Show.Singletons
import Data.Kind (Type)
import qualified Data.Singletons.ShowSing
import qualified Data.Type.Equality
import qualified Data.Singletons.Decide
import qualified Data.Type.Coercion
import qualified GHC.Num.Natural

type MemptySym0 :: forall a_a3wyl. a_a3wyl
type family MemptySym0 @a_a3wyl :: a_a3wyl where
  MemptySym0 = Mempty
type MappendSym0 :: forall a_a3wyl. (~>) a_a3wyl ((~>) a_a3wyl a_a3wyl)
data MappendSym0 :: (~>) a_a3wyl ((~>) a_a3wyl a_a3wyl)
  where
    MappendSym0KindInference :: SameKind (Apply MappendSym0 arg_a3wAl) (MappendSym1 arg_a3wAl) =>
                                MappendSym0 a6989586621679850038
type instance Apply @a_a3wyl @((~>) a_a3wyl a_a3wyl) MappendSym0 a6989586621679850038 = MappendSym1 a6989586621679850038
instance SuppressUnusedWarnings MappendSym0 where
  suppressUnusedWarnings = snd ((,) MappendSym0KindInference ())
type MappendSym1 :: forall a_a3wyl. a_a3wyl -> (~>) a_a3wyl a_a3wyl
data MappendSym1 (a6989586621679850038 :: a_a3wyl) :: (~>) a_a3wyl a_a3wyl
  where
    MappendSym1KindInference :: SameKind (Apply (MappendSym1 a6989586621679850038) arg_a3wAl) (MappendSym2 a6989586621679850038 arg_a3wAl) =>
                                MappendSym1 a6989586621679850038 a6989586621679850039
type instance Apply @a_a3wyl @a_a3wyl (MappendSym1 a6989586621679850038) a6989586621679850039 = Mappend a6989586621679850038 a6989586621679850039
instance SuppressUnusedWarnings (MappendSym1 a6989586621679850038) where
  suppressUnusedWarnings = snd ((,) MappendSym1KindInference ())
type MappendSym2 :: forall a_a3wyl. a_a3wyl -> a_a3wyl -> a_a3wyl
type family MappendSym2 @a_a3wyl (a6989586621679850038 :: a_a3wyl) (a6989586621679850039 :: a_a3wyl) :: a_a3wyl where
  MappendSym2 a6989586621679850038 a6989586621679850039 = Mappend a6989586621679850038 a6989586621679850039
type MconcatSym0 :: forall a_a3wyl. (~>) [a_a3wyl] a_a3wyl
data MconcatSym0 :: (~>) [a_a3wyl] a_a3wyl
  where
    MconcatSym0KindInference :: SameKind (Apply MconcatSym0 arg_a3wAp) (MconcatSym1 arg_a3wAp) =>
                                MconcatSym0 a6989586621679850042
type instance Apply @[a_a3wyl] @a_a3wyl MconcatSym0 a6989586621679850042 = Mconcat a6989586621679850042
instance SuppressUnusedWarnings MconcatSym0 where
  suppressUnusedWarnings = snd ((,) MconcatSym0KindInference ())
type MconcatSym1 :: forall a_a3wyl. [a_a3wyl] -> a_a3wyl
type family MconcatSym1 @a_a3wyl (a6989586621679850042 :: [a_a3wyl]) :: a_a3wyl where
  MconcatSym1 a6989586621679850042 = Mconcat a6989586621679850042
type Mappend_6989586621679850045 :: forall a_a3wyl. a_a3wyl
                                                    -> a_a3wyl -> a_a3wyl
type family Mappend_6989586621679850045 @a_a3wyl (a_a3wAz :: a_a3wyl) (a_a3wAA :: a_a3wyl) :: a_a3wyl where
  Mappend_6989586621679850045 @a_a3wyl (a_6989586621679850047_a3wAE :: a_a3wyl) (a_6989586621679850049_a3wAF :: a_a3wyl) = Apply (Apply (<>@#@$) a_6989586621679850047_a3wAE) a_6989586621679850049_a3wAF
type Mconcat_6989586621679850059 :: forall a_a3wyl. [a_a3wyl]
                                                    -> a_a3wyl
type family Mconcat_6989586621679850059 @a_a3wyl (a_a3wAL :: [a_a3wyl]) :: a_a3wyl where
  Mconcat_6989586621679850059 @a_a3wyl (a_6989586621679850061_a3wAO :: [a_a3wyl]) = Apply (Apply (Apply FoldrSym0 MappendSym0) MemptySym0) a_6989586621679850061_a3wAO
class PMonoid a_a3wyl where
  type family Mempty :: a_a3wyl
  type family Mappend (arg_a3wAj :: a_a3wyl) (arg_a3wAk :: a_a3wyl) :: a_a3wyl
  type family Mconcat (arg_a3wAo :: [a_a3wyl]) :: a_a3wyl
  type Mappend a_a3wAr a_a3wAs = Mappend_6989586621679850045 a_a3wAr a_a3wAs
  type Mconcat a_a3wAG = Mconcat_6989586621679850059 a_a3wAG
type Mempty_6989586621679850067 :: forall a_a3wym. [a_a3wym]
type family Mempty_6989586621679850067 @a_a3wym :: [a_a3wym] where
  Mempty_6989586621679850067 @a_a3wym = NilSym0
instance PMonoid [a_a3wym] where
  type Mempty = Mempty_6989586621679850067
type family LamCases_6989586621679850073_a3wAW a6989586621679849916 b6989586621679849915 a_6989586621679850075_a3wAY where
  LamCases_6989586621679850073_a3wAW a_a3wyo b_a3wyn _ = MemptySym0
data LamCases_6989586621679850073Sym0 a6989586621679849916 b6989586621679849915 a_69895866216798500756989586621679850076
  where
    LamCases_6989586621679850073Sym0KindInference :: SameKind (Apply (LamCases_6989586621679850073Sym0 a6989586621679849916 b6989586621679849915) arg_a3wAZ) (LamCases_6989586621679850073Sym1 a6989586621679849916 b6989586621679849915 arg_a3wAZ) =>
                                                      LamCases_6989586621679850073Sym0 a6989586621679849916 b6989586621679849915 a_69895866216798500756989586621679850076
type instance Apply @_ @_ (LamCases_6989586621679850073Sym0 a6989586621679849916 b6989586621679849915) a_69895866216798500756989586621679850076 = LamCases_6989586621679850073_a3wAW a6989586621679849916 b6989586621679849915 a_69895866216798500756989586621679850076
instance SuppressUnusedWarnings (LamCases_6989586621679850073Sym0 a6989586621679849916 b6989586621679849915) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679850073Sym0KindInference ())
type family LamCases_6989586621679850073Sym1 a6989586621679849916 b6989586621679849915 a_69895866216798500756989586621679850076 where
  LamCases_6989586621679850073Sym1 a6989586621679849916 b6989586621679849915 a_69895866216798500756989586621679850076 = LamCases_6989586621679850073_a3wAW a6989586621679849916 b6989586621679849915 a_69895866216798500756989586621679850076
type Mempty_6989586621679850070 :: forall a_a3wyo
                                          b_a3wyn. (~>) a_a3wyo b_a3wyn
type family Mempty_6989586621679850070 @a_a3wyo @b_a3wyn :: (~>) a_a3wyo b_a3wyn where
  Mempty_6989586621679850070 @a_a3wyo @b_a3wyn = LamCases_6989586621679850073Sym0 a_a3wyo b_a3wyn
instance PMonoid ((~>) a_a3wyo b_a3wyn) where
  type Mempty = Mempty_6989586621679850070
type Mempty_6989586621679850078 :: ()
type family Mempty_6989586621679850078 :: () where
  Mempty_6989586621679850078 = Tuple0Sym0
type Mconcat_6989586621679850082 :: [()] -> ()
type family Mconcat_6989586621679850082 (a_a3wB6 :: [()]) :: () where
  Mconcat_6989586621679850082 _ = Tuple0Sym0
instance PMonoid () where
  type Mempty = Mempty_6989586621679850078
  type Mconcat a_a3wB3 = Mconcat_6989586621679850082 a_a3wB3
type Mempty_6989586621679850087 :: forall a_a3wyp
                                          b_a3wyq. (a_a3wyp, b_a3wyq)
type family Mempty_6989586621679850087 @a_a3wyp @b_a3wyq :: (a_a3wyp,
                                                              b_a3wyq) where
  Mempty_6989586621679850087 @a_a3wyp @b_a3wyq = Apply (Apply Tuple2Sym0 MemptySym0) MemptySym0
instance PMonoid (a_a3wyp, b_a3wyq) where
  type Mempty = Mempty_6989586621679850087
type Mempty_6989586621679850090 :: forall a_a3wyr
                                          b_a3wys
                                          c_a3wyt. (a_a3wyr, b_a3wys, c_a3wyt)
type family Mempty_6989586621679850090 @a_a3wyr @b_a3wys @c_a3wyt :: (a_a3wyr,
                                                                      b_a3wys, c_a3wyt) where
  Mempty_6989586621679850090 @a_a3wyr @b_a3wys @c_a3wyt = Apply (Apply (Apply Tuple3Sym0 MemptySym0) MemptySym0) MemptySym0
instance PMonoid (a_a3wyr, b_a3wys, c_a3wyt) where
  type Mempty = Mempty_6989586621679850090
type Mempty_6989586621679850093 :: forall a_a3wyu
                                          b_a3wyv
                                          c_a3wyw
                                          d_a3wyx. (a_a3wyu, b_a3wyv, c_a3wyw, d_a3wyx)
type family Mempty_6989586621679850093 @a_a3wyu @b_a3wyv @c_a3wyw @d_a3wyx :: (a_a3wyu,
                                                                                b_a3wyv, c_a3wyw,
                                                                                d_a3wyx) where
  Mempty_6989586621679850093 @a_a3wyu @b_a3wyv @c_a3wyw @d_a3wyx = Apply (Apply (Apply (Apply Tuple4Sym0 MemptySym0) MemptySym0) MemptySym0) MemptySym0
instance PMonoid (a_a3wyu, b_a3wyv, c_a3wyw, d_a3wyx) where
  type Mempty = Mempty_6989586621679850093
type Mempty_6989586621679850096 :: forall a_a3wyy
                                          b_a3wyz
                                          c_a3wyA
                                          d_a3wyB
                                          e_a3wyC. (a_a3wyy, b_a3wyz, c_a3wyA, d_a3wyB, e_a3wyC)
type family Mempty_6989586621679850096 @a_a3wyy @b_a3wyz @c_a3wyA @d_a3wyB @e_a3wyC :: (a_a3wyy,
                                                                                        b_a3wyz,
                                                                                        c_a3wyA,
                                                                                        d_a3wyB,
                                                                                        e_a3wyC) where
  Mempty_6989586621679850096 @a_a3wyy @b_a3wyz @c_a3wyA @d_a3wyB @e_a3wyC = Apply (Apply (Apply (Apply (Apply Tuple5Sym0 MemptySym0) MemptySym0) MemptySym0) MemptySym0) MemptySym0
instance PMonoid (a_a3wyy, b_a3wyz, c_a3wyA, d_a3wyB,
                  e_a3wyC) where
  type Mempty = Mempty_6989586621679850096
type Mempty_6989586621679850099 :: Ordering
type family Mempty_6989586621679850099 :: Ordering where
  Mempty_6989586621679850099 = EQSym0
instance PMonoid Ordering where
  type Mempty = Mempty_6989586621679850099
type Mempty_6989586621679850102 :: forall a_a3wyD. Maybe a_a3wyD
type family Mempty_6989586621679850102 @a_a3wyD :: Maybe a_a3wyD where
  Mempty_6989586621679850102 @a_a3wyD = NothingSym0
instance PMonoid (Maybe a_a3wyD) where
  type Mempty = Mempty_6989586621679850102
type Mempty_6989586621679850105 :: Symbol
type family Mempty_6989586621679850105 :: Symbol where
  Mempty_6989586621679850105 = ""
instance PMonoid Symbol where
  type Mempty = Mempty_6989586621679850105
class SSemigroup a_a3wyl => SMonoid a_a3wyl where
  sMempty :: (Sing (Mempty :: a_a3wyl) :: Type)
  sMappend ::
    (forall (t_a3wBu :: a_a3wyl) (t_a3wBv :: a_a3wyl).
      Sing t_a3wBu
      -> Sing t_a3wBv
        -> Sing (Mappend t_a3wBu t_a3wBv :: a_a3wyl) :: Type)
  sMconcat ::
    (forall (t_a3wBz :: [a_a3wyl]).
      Sing t_a3wBz -> Sing (Mconcat t_a3wBz :: a_a3wyl) :: Type)
  default sMappend ::
            (forall (t_a3wBu :: a_a3wyl) (t_a3wBv :: a_a3wyl).
              ((Mappend t_a3wBu t_a3wBv :: a_a3wyl)
              ~ Mappend_6989586621679850045 t_a3wBu t_a3wBv) =>
              Sing t_a3wBu
              -> Sing t_a3wBv
                -> Sing (Mappend t_a3wBu t_a3wBv :: a_a3wyl) :: Type)
  default sMconcat ::
            (forall (t_a3wBz :: [a_a3wyl]).
              ((Mconcat t_a3wBz :: a_a3wyl)
              ~ Mconcat_6989586621679850059 t_a3wBz) =>
              Sing t_a3wBz -> Sing (Mconcat t_a3wBz :: a_a3wyl) :: Type)
  sMappend
    (sA_6989586621679850047 :: Sing a_6989586621679850047_a3wAE)
    (sA_6989586621679850049 :: Sing a_6989586621679850049_a3wAF)
    = applySing
        (applySing (singFun2 @(<>@#@$) (%<>)) sA_6989586621679850047)
        sA_6989586621679850049
  sMconcat
    (sA_6989586621679850061 :: Sing a_6989586621679850061_a3wAO)
    = applySing
        (applySing
            (applySing
              (singFun3 @FoldrSym0 sFoldr) (singFun2 @MappendSym0 sMappend))
            sMempty)
        sA_6989586621679850061
instance SMonoid [a_a3wym] where
  sMempty = SNil
instance SMonoid b_a3wyn => SMonoid ((~>) a_a3wyo b_a3wyn) where
  sMempty
    = singFun1
        @(LamCases_6989586621679850073Sym0 a_a3wyo b_a3wyn)
        (\cases _ -> sMempty)
instance SMonoid () where
  sMempty = STuple0
  sMconcat _ = STuple0
instance (SMonoid a_a3wyp, SMonoid b_a3wyq) =>
          SMonoid (a_a3wyp, b_a3wyq) where
  sMempty
    = applySing
        (applySing (singFun2 @Tuple2Sym0 STuple2) sMempty) sMempty
instance (SMonoid a_a3wyr, SMonoid b_a3wys, SMonoid c_a3wyt) =>
          SMonoid (a_a3wyr, b_a3wys, c_a3wyt) where
  sMempty
    = applySing
        (applySing
            (applySing (singFun3 @Tuple3Sym0 STuple3) sMempty) sMempty)
        sMempty
instance (SMonoid a_a3wyu,
          SMonoid b_a3wyv,
          SMonoid c_a3wyw,
          SMonoid d_a3wyx) =>
          SMonoid (a_a3wyu, b_a3wyv, c_a3wyw, d_a3wyx) where
  sMempty
    = applySing
        (applySing
            (applySing
              (applySing (singFun4 @Tuple4Sym0 STuple4) sMempty) sMempty)
            sMempty)
        sMempty
instance (SMonoid a_a3wyy,
          SMonoid b_a3wyz,
          SMonoid c_a3wyA,
          SMonoid d_a3wyB,
          SMonoid e_a3wyC) =>
          SMonoid (a_a3wyy, b_a3wyz, c_a3wyA, d_a3wyB, e_a3wyC) where
  sMempty
    = applySing
        (applySing
            (applySing
              (applySing
                  (applySing (singFun5 @Tuple5Sym0 STuple5) sMempty) sMempty)
              sMempty)
            sMempty)
        sMempty
instance SMonoid Ordering where
  sMempty = SEQ
instance SSemigroup a_a3wyD => SMonoid (Maybe a_a3wyD) where
  sMempty = SNothing
instance SMonoid Symbol where
  sMempty = sing :: Sing ""
instance SMonoid a_a3wyl =>
          SingI (MappendSym0 :: (~>) a_a3wyl ((~>) a_a3wyl a_a3wyl)) where
  sing = singFun2 @MappendSym0 sMappend
instance (SMonoid a_a3wyl, SingI d_a3wBw) =>
          SingI (MappendSym1 (d_a3wBw :: a_a3wyl) :: (~>) a_a3wyl a_a3wyl) where
  sing
    = singFun1
        @(MappendSym1 (d_a3wBw :: a_a3wyl)) (sMappend (sing @d_a3wBw))
instance SMonoid a_a3wyl =>
          SingI1 (MappendSym1 :: a_a3wyl -> (~>) a_a3wyl a_a3wyl) where
  liftSing (s_a3wBy :: Sing (d_a3wBw :: a_a3wyl))
    = singFun1 @(MappendSym1 (d_a3wBw :: a_a3wyl)) (sMappend s_a3wBy)
instance SMonoid a_a3wyl =>
          SingI (MconcatSym0 :: (~>) [a_a3wyl] a_a3wyl) where
  sing = singFun1 @MconcatSym0 sMconcat

type FirstSym0 :: forall (a_aNZz :: Type). (~>) (Maybe a_aNZz) (First a_aNZz)
data FirstSym0 :: (~>) (Maybe a_aNZz) (First a_aNZz)
  where
    FirstSym0KindInference :: SameKind (Apply FirstSym0 arg_a3xw5) (FirstSym1 arg_a3xw5) =>
                              FirstSym0 a6989586621679853618
type instance Apply @(Maybe a_aNZz) @(First a_aNZz) FirstSym0 a6989586621679853618 = 'First a6989586621679853618
instance SuppressUnusedWarnings FirstSym0 where
  suppressUnusedWarnings = snd ((,) FirstSym0KindInference ())
type FirstSym1 :: forall (a_aNZz :: Type). Maybe a_aNZz
                                            -> First a_aNZz
type family FirstSym1 @(a_aNZz :: Type) (a6989586621679853618 :: Maybe a_aNZz) :: First a_aNZz where
  FirstSym1 a6989586621679853618 = 'First a6989586621679853618
type GetFirstSym0 :: forall (a_aNZz :: Type). (~>) (First a_aNZz) (Maybe a_aNZz)
data GetFirstSym0 :: (~>) (First a_aNZz) (Maybe a_aNZz)
  where
    GetFirstSym0KindInference :: SameKind (Apply GetFirstSym0 arg_a3xw8) (GetFirstSym1 arg_a3xw8) =>
                                  GetFirstSym0 a6989586621679853621
type instance Apply @(First a_aNZz) @(Maybe a_aNZz) GetFirstSym0 a6989586621679853621 = GetFirst a6989586621679853621
instance SuppressUnusedWarnings GetFirstSym0 where
  suppressUnusedWarnings = snd ((,) GetFirstSym0KindInference ())
type GetFirstSym1 :: forall (a_aNZz :: Type). First a_aNZz
                                              -> Maybe a_aNZz
type family GetFirstSym1 @(a_aNZz :: Type) (a6989586621679853621 :: First a_aNZz) :: Maybe a_aNZz where
  GetFirstSym1 a6989586621679853621 = GetFirst a6989586621679853621
type GetFirst :: forall (a_aNZz :: Type). First a_aNZz
                                          -> Maybe a_aNZz
type family GetFirst @(a_aNZz :: Type) (a_a3xw7 :: First a_aNZz) :: Maybe a_aNZz where
  GetFirst @a_aNZz ('First field_a3xwa :: First a_aNZz) = field_a3xwa
sGetFirst ::
  forall (a_aNZz :: Type) (t_a3xwb :: First a_aNZz). Sing t_a3xwb
                                                      -> Sing (GetFirst t_a3xwb :: Maybe a_aNZz)
sGetFirst (SFirst (sField :: Sing field_a3xwa)) = sField
instance SingI (GetFirstSym0 :: (~>) (First a_aNZz) (Maybe a_aNZz)) where
  sing = singFun1 @GetFirstSym0 sGetFirst
type SFirst :: forall (a_aNZz :: Type). First a_aNZz -> Type
data SFirst :: forall (a_aNZz :: Type). First a_aNZz -> Type
  where
    SFirst :: forall (a_aNZz :: Type) (n_a3xwd :: Maybe a_aNZz).
              (Sing n_a3xwd) -> SFirst ('First n_a3xwd :: First a_aNZz)
type instance Sing @(First a_aNZz) = SFirst
instance SingKind a_aNZz => SingKind (First a_aNZz) where
  type Demote (First a_aNZz) = First (Demote a_aNZz)
  fromSing (SFirst b_a3xwf) = First (fromSing b_a3xwf)
  toSing (First (b_a3xwh :: Demote (Maybe a_aNZz)))
    = (\cases (SomeSing c_a3xwi) -> SomeSing (SFirst c_a3xwi))
        (toSing b_a3xwh :: SomeSing (Maybe a_aNZz))
instance SingI n_a3xwd =>
          SingI ('First (n_a3xwd :: Maybe a_aNZz)) where
  sing = SFirst sing
instance SingI1 'First where
  liftSing = SFirst
instance SingI (FirstSym0 :: (~>) (Maybe a_aNZz) (First a_aNZz)) where
  sing = singFun1 @FirstSym0 SFirst
type LastSym0 :: forall (a_aNZE :: Type). (~>) (Maybe a_aNZE) (Last a_aNZE)
data LastSym0 :: (~>) (Maybe a_aNZE) (Last a_aNZE)
  where
    LastSym0KindInference :: SameKind (Apply LastSym0 arg_a3xws) (LastSym1 arg_a3xws) =>
                              LastSym0 a6989586621679853641
type instance Apply @(Maybe a_aNZE) @(Last a_aNZE) LastSym0 a6989586621679853641 = 'Last a6989586621679853641
instance SuppressUnusedWarnings LastSym0 where
  suppressUnusedWarnings = snd ((,) LastSym0KindInference ())
type LastSym1 :: forall (a_aNZE :: Type). Maybe a_aNZE
                                          -> Last a_aNZE
type family LastSym1 @(a_aNZE :: Type) (a6989586621679853641 :: Maybe a_aNZE) :: Last a_aNZE where
  LastSym1 a6989586621679853641 = 'Last a6989586621679853641
type GetLastSym0 :: forall (a_aNZE :: Type). (~>) (Last a_aNZE) (Maybe a_aNZE)
data GetLastSym0 :: (~>) (Last a_aNZE) (Maybe a_aNZE)
  where
    GetLastSym0KindInference :: SameKind (Apply GetLastSym0 arg_a3xwv) (GetLastSym1 arg_a3xwv) =>
                                GetLastSym0 a6989586621679853644
type instance Apply @(Last a_aNZE) @(Maybe a_aNZE) GetLastSym0 a6989586621679853644 = GetLast a6989586621679853644
instance SuppressUnusedWarnings GetLastSym0 where
  suppressUnusedWarnings = snd ((,) GetLastSym0KindInference ())
type GetLastSym1 :: forall (a_aNZE :: Type). Last a_aNZE
                                              -> Maybe a_aNZE
type family GetLastSym1 @(a_aNZE :: Type) (a6989586621679853644 :: Last a_aNZE) :: Maybe a_aNZE where
  GetLastSym1 a6989586621679853644 = GetLast a6989586621679853644
type GetLast :: forall (a_aNZE :: Type). Last a_aNZE
                                          -> Maybe a_aNZE
type family GetLast @(a_aNZE :: Type) (a_a3xwu :: Last a_aNZE) :: Maybe a_aNZE where
  GetLast @a_aNZE ('Last field_a3xwx :: Last a_aNZE) = field_a3xwx
sGetLast ::
  forall (a_aNZE :: Type) (t_a3xwy :: Last a_aNZE). Sing t_a3xwy
                                                    -> Sing (GetLast t_a3xwy :: Maybe a_aNZE)
sGetLast (SLast (sField :: Sing field_a3xwx)) = sField
instance SingI (GetLastSym0 :: (~>) (Last a_aNZE) (Maybe a_aNZE)) where
  sing = singFun1 @GetLastSym0 sGetLast
type SLast :: forall (a_aNZE :: Type). Last a_aNZE -> Type
data SLast :: forall (a_aNZE :: Type). Last a_aNZE -> Type
  where
    SLast :: forall (a_aNZE :: Type) (n_a3xwA :: Maybe a_aNZE).
              (Sing n_a3xwA) -> SLast ('Last n_a3xwA :: Last a_aNZE)
type instance Sing @(Last a_aNZE) = SLast
instance SingKind a_aNZE => SingKind (Last a_aNZE) where
  type Demote (Last a_aNZE) = Last (Demote a_aNZE)
  fromSing (SLast b_a3xwC) = Last (fromSing b_a3xwC)
  toSing (Last (b_a3xwE :: Demote (Maybe a_aNZE)))
    = (\cases (SomeSing c_a3xwF) -> SomeSing (SLast c_a3xwF))
        (toSing b_a3xwE :: SomeSing (Maybe a_aNZE))
instance SingI n_a3xwA =>
          SingI ('Last (n_a3xwA :: Maybe a_aNZE)) where
  sing = SLast sing
instance SingI1 'Last where
  liftSing = SLast
instance SingI (LastSym0 :: (~>) (Maybe a_aNZE) (Last a_aNZE)) where
  sing = singFun1 @LastSym0 SLast
deriving instance Data.Singletons.ShowSing.ShowSing (Maybe a_aNZz) =>
                      Show (SFirst (z_a3xTC :: First a_aNZz))
deriving instance Data.Singletons.ShowSing.ShowSing (Maybe a_aNZE) =>
                  Show (SLast (z_a3xTG :: Last a_aNZE))

type TFHelper_6989586621679855358 :: forall a_aNZz. First a_aNZz
                                                        -> First a_aNZz -> Bool
type family TFHelper_6989586621679855358 @a_aNZz (a_a3xYc :: First a_aNZz) (a_a3xYd :: First a_aNZz) :: Bool where
  TFHelper_6989586621679855358 @a_aNZz ('First a_6989586621679855252_a3xYh :: First a_aNZz) ('First b_6989586621679855254_a3xYi :: First a_aNZz) = Apply (Apply (==@#@$) a_6989586621679855252_a3xYh) b_6989586621679855254_a3xYi
instance PEq (First a_aNZz) where
  type (==) a_a3xY8 a_a3xY9 = TFHelper_6989586621679855358 a_a3xY8 a_a3xY9
instance SEq (Maybe a_aNZz) => SEq (First a_aNZz) where
  (%==)
    (SFirst (sA_6989586621679855252 :: Sing a_6989586621679855252_a3xYh))
    (SFirst (sB_6989586621679855254 :: Sing b_6989586621679855254_a3xYi))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679855252)
        sB_6989586621679855254
type TFHelper_6989586621679855376 :: forall a_aNZE. Last a_aNZE
                                                    -> Last a_aNZE -> Bool
type family TFHelper_6989586621679855376 @a_aNZE (a_a3xYu :: Last a_aNZE) (a_a3xYv :: Last a_aNZE) :: Bool where
  TFHelper_6989586621679855376 @a_aNZE ('Last a_6989586621679855370_a3xYz :: Last a_aNZE) ('Last b_6989586621679855372_a3xYA :: Last a_aNZE) = Apply (Apply (==@#@$) a_6989586621679855370_a3xYz) b_6989586621679855372_a3xYA
instance PEq (Last a_aNZE) where
  type (==) a_a3xYq a_a3xYr = TFHelper_6989586621679855376 a_a3xYq a_a3xYr
instance SEq (Maybe a_aNZE) => SEq (Last a_aNZE) where
  (%==)
    (SLast (sA_6989586621679855370 :: Sing a_6989586621679855370_a3xYz))
    (SLast (sB_6989586621679855372 :: Sing b_6989586621679855372_a3xYA))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679855370)
        sB_6989586621679855372
instance SDecide (Maybe a_aNZz) => SDecide (First a_aNZz) where
      (%~) (SFirst a_a3y5T) (SFirst b_a3y5U)
        = (\cases
             (Proved Refl) -> Proved Refl
             (Disproved contra_a3y5V)
               -> Disproved (\cases Refl -> contra_a3y5V Refl))
            ((%~) a_a3y5T b_a3y5U)
instance Eq (SFirst (z_a3y5Y :: First a_aNZz)) where
  (==) _ _ = True
instance SDecide (Maybe a_aNZz) =>
          Data.Type.Equality.TestEquality (SFirst :: First a_aNZz
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide (Maybe a_aNZz) =>
          Data.Type.Coercion.TestCoercion (SFirst :: First a_aNZz
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide (Maybe a_aNZE) => SDecide (Last a_aNZE) where
  (%~) (SLast a_a3y66) (SLast b_a3y67)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a3y68)
            -> Disproved (\cases Refl -> contra_a3y68 Refl))
        ((%~) a_a3y66 b_a3y67)
instance Eq (SLast (z_a3y6b :: Last a_aNZE)) where
  (==) _ _ = True
instance SDecide (Maybe a_aNZE) =>
          Data.Type.Equality.TestEquality (SLast :: Last a_aNZE
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide (Maybe a_aNZE) =>
          Data.Type.Coercion.TestCoercion (SLast :: Last a_aNZE
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
type Compare_6989586621679856586 :: forall a_aNZz. First a_aNZz
                                                       -> First a_aNZz -> Ordering
type family Compare_6989586621679856586 @a_aNZz (a_a3yi0 :: First a_aNZz) (a_a3yi1 :: First a_aNZz) :: Ordering where
  Compare_6989586621679856586 @a_aNZz ('First a_6989586621679856340_a3yi5 :: First a_aNZz) ('First b_6989586621679856342_a3yi6 :: First a_aNZz) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679856340_a3yi5) b_6989586621679856342_a3yi6)) NilSym0)
instance POrd (First a_aNZz) where
  type Compare a_a3yhW a_a3yhX = Compare_6989586621679856586 a_a3yhW a_a3yhX
instance SOrd (Maybe a_aNZz) => SOrd (First a_aNZz) where
  sCompare
    (SFirst (sA_6989586621679856340 :: Sing a_6989586621679856340_a3yi5))
    (SFirst (sB_6989586621679856342 :: Sing b_6989586621679856342_a3yi6))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679856340)
                  sB_6989586621679856342))
            SNil)
type Compare_6989586621679856604 :: forall a_aNZE. Last a_aNZE
                                                    -> Last a_aNZE -> Ordering
type family Compare_6989586621679856604 @a_aNZE (a_a3yii :: Last a_aNZE) (a_a3yij :: Last a_aNZE) :: Ordering where
  Compare_6989586621679856604 @a_aNZE ('Last a_6989586621679856598_a3yin :: Last a_aNZE) ('Last b_6989586621679856600_a3yio :: Last a_aNZE) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679856598_a3yin) b_6989586621679856600_a3yio)) NilSym0)
instance POrd (Last a_aNZE) where
  type Compare a_a3yie a_a3yif = Compare_6989586621679856604 a_a3yie a_a3yif
instance SOrd (Maybe a_aNZE) => SOrd (Last a_aNZE) where
  sCompare
    (SLast (sA_6989586621679856598 :: Sing a_6989586621679856598_a3yin))
    (SLast (sB_6989586621679856600 :: Sing b_6989586621679856600_a3yio))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679856598)
                  sB_6989586621679856600))
            SNil)
type ShowsPrec_6989586621679857989 :: forall a_aNZz. GHC.Num.Natural.Natural
                                                         -> First a_aNZz -> Symbol -> Symbol
type family ShowsPrec_6989586621679857989 @a_aNZz (a_a3yEF :: GHC.Num.Natural.Natural) (a_a3yEG :: First a_aNZz) (a_a3yEH :: Symbol) :: Symbol where
  ShowsPrec_6989586621679857989 @a_aNZz (p_6989586621679857619_a3yEM :: GHC.Num.Natural.Natural) ('First arg_6989586621679857621_a3yEN :: First a_aNZz) (a_6989586621679857991_a3yEO :: Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679857619_a3yEM) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "First ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getFirst = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679857621_a3yEN)) (Apply ShowCharSym0 '}')))))) a_6989586621679857991_a3yEO
instance PShow (First a_aNZz) where
  type ShowsPrec a_a3yEy a_a3yEz a_a3yEA = ShowsPrec_6989586621679857989 a_a3yEy a_a3yEz a_a3yEA
instance SShow (Maybe a_aNZz) => SShow (First a_aNZz) where
  sShowsPrec
    (sP_6989586621679857619 :: Sing p_6989586621679857619_a3yEM)
    (SFirst (sArg_6989586621679857621 :: Sing arg_6989586621679857621_a3yEN))
    (sA_6989586621679857991 :: Sing a_6989586621679857991_a3yEO)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679857619)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "First ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString)
                          (sing :: Sing "getFirst = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679857621))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679857991
type ShowsPrec_6989586621679858030 :: forall a_aNZE. GHC.Num.Natural.Natural
                                                      -> Last a_aNZE -> Symbol -> Symbol
type family ShowsPrec_6989586621679858030 @a_aNZE (a_a3yFk :: GHC.Num.Natural.Natural) (a_a3yFl :: Last a_aNZE) (a_a3yFm :: Symbol) :: Symbol where
  ShowsPrec_6989586621679858030 @a_aNZE (p_6989586621679858021_a3yFr :: GHC.Num.Natural.Natural) ('Last arg_6989586621679858023_a3yFs :: Last a_aNZE) (a_6989586621679858032_a3yFt :: Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679858021_a3yFr) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Last ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getLast = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679858023_a3yFs)) (Apply ShowCharSym0 '}')))))) a_6989586621679858032_a3yFt
instance PShow (Last a_aNZE) where
  type ShowsPrec a_a3yFd a_a3yFe a_a3yFf = ShowsPrec_6989586621679858030 a_a3yFd a_a3yFe a_a3yFf
instance SShow (Maybe a_aNZE) => SShow (Last a_aNZE) where
  sShowsPrec
    (sP_6989586621679858021 :: Sing p_6989586621679858021_a3yFr)
    (SLast (sArg_6989586621679858023 :: Sing arg_6989586621679858023_a3yFs))
    (sA_6989586621679858032 :: Sing a_6989586621679858032_a3yFt)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679858021)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Last ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString)
                          (sing :: Sing "getLast = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679858023))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679858032


type Mempty_6989586621679861228 :: forall a_a3zp8. Dual a_a3zp8
type family Mempty_6989586621679861228 @a_a3zp8 :: Dual a_a3zp8 where
  Mempty_6989586621679861228 @a_a3zp8 = Apply DualSym0 MemptySym0
instance PMonoid (Dual a_a3zp8) where
  type Mempty = Mempty_6989586621679861228
type Mempty_6989586621679861231 :: All
type family Mempty_6989586621679861231 :: All where
  Mempty_6989586621679861231 = Apply AllSym0 TrueSym0
instance PMonoid All where
  type Mempty = Mempty_6989586621679861231
type Mempty_6989586621679861234 :: Any
type family Mempty_6989586621679861234 :: Any where
  Mempty_6989586621679861234 = Apply AnySym0 FalseSym0
instance PMonoid Any where
  type Mempty = Mempty_6989586621679861234
type Mempty_6989586621679861237 :: forall a_a3zp9. Sum a_a3zp9
type family Mempty_6989586621679861237 @a_a3zp9 :: Sum a_a3zp9 where
  Mempty_6989586621679861237 @a_a3zp9 = Apply SumSym0 (FromInteger 0)
instance PMonoid (Sum a_a3zp9) where
  type Mempty = Mempty_6989586621679861237
type Mempty_6989586621679861240 :: forall a_a3zpa. Product a_a3zpa
type family Mempty_6989586621679861240 @a_a3zpa :: Product a_a3zpa where
  Mempty_6989586621679861240 @a_a3zpa = Apply ProductSym0 (FromInteger 1)
instance PMonoid (Product a_a3zpa) where
  type Mempty = Mempty_6989586621679861240
type Mempty_6989586621679861243 :: forall a_a3zpb. Down a_a3zpb
type family Mempty_6989586621679861243 @a_a3zpb :: Down a_a3zpb where
  Mempty_6989586621679861243 @a_a3zpb = Apply DownSym0 MemptySym0
instance PMonoid (Down a_a3zpb) where
  type Mempty = Mempty_6989586621679861243
type Pure_6989586621679861325 :: forall a_i1v3p. a_i1v3p
                                                  -> First a_i1v3p
type family Pure_6989586621679861325 @a_i1v3p (a_a3zwt :: a_i1v3p) :: First a_i1v3p where
  Pure_6989586621679861325 @a_i1v3p a_6989586621679861327_a3zww = Apply (Apply (Apply (.@#@$) FirstSym0) PureSym0) a_6989586621679861327_a3zww
type TFHelper_6989586621679861335 :: forall a_i1v3r
                                            b_i1v3s. First ((~>) a_i1v3r b_i1v3s)
                                                      -> First a_i1v3r -> First b_i1v3s
type family TFHelper_6989586621679861335 @a_i1v3r @b_i1v3s (a_a3zwB :: First ((~>) a_i1v3r b_i1v3s)) (a_a3zwC :: First a_i1v3r) :: First b_i1v3s where
  TFHelper_6989586621679861335 @a_i1v3r @b_i1v3s ('First f_a3zwG) ('First x_a3zwH) = Apply FirstSym0 (Apply (Apply (<*>@#@$) f_a3zwG) x_a3zwH)
instance PApplicative First where
  type Pure a_a3zwo = Pure_6989586621679861325 a_a3zwo
  type (<*>) a_a3zwx a_a3zwy = TFHelper_6989586621679861335 a_a3zwx a_a3zwy
type Fmap_6989586621679861394 :: forall a_i1v3K
                                        b_i1v3L. (~>) a_i1v3K b_i1v3L
                                                  -> First a_i1v3K -> First b_i1v3L
type family Fmap_6989586621679861394 @a_i1v3K @b_i1v3L (a_a3zxy :: (~>) a_i1v3K b_i1v3L) (a_a3zxz :: First a_i1v3K) :: First b_i1v3L where
  Fmap_6989586621679861394 @a_i1v3K @b_i1v3L _f_6989586621679861181_a3zxD ('First a_6989586621679861191_a3zxE) = Apply FirstSym0 (Apply (Apply FmapSym0 _f_6989586621679861181_a3zxD) a_6989586621679861191_a3zxE)
type TFHelper_6989586621679861405 :: forall a_i1v3O
                                            b_i1v3P. a_i1v3O -> First b_i1v3P -> First a_i1v3O
type family TFHelper_6989586621679861405 @a_i1v3O @b_i1v3P (a_a3zxJ :: a_i1v3O) (a_a3zxK :: First b_i1v3P) :: First a_i1v3O where
  TFHelper_6989586621679861405 @a_i1v3O @b_i1v3P _z_6989586621679861183_a3zxO ('First a_6989586621679861199_a3zxP) = Apply FirstSym0 (Apply (Apply (<$@#@$) _z_6989586621679861183_a3zxO) a_6989586621679861199_a3zxP)
instance PFunctor First where
  type Fmap a_a3zxu a_a3zxv = Fmap_6989586621679861394 a_a3zxu a_a3zxv
  type (<$) a_a3zxF a_a3zxG = TFHelper_6989586621679861405 a_a3zxF a_a3zxG
type family LamCases_6989586621679861470_a3zyL x6989586621679861469 a6989586621679861465 (k6989586621679861466 :: (~>) a7566047373982791018 (First b7566047373982791019)) a_6989586621679861473_a3zyO where
  LamCases_6989586621679861470_a3zyL x_a3zyJ a_a3zyF k_a3zyG ('First y_a3zyM) = y_a3zyM
data LamCases_6989586621679861470Sym0 x6989586621679861469 a6989586621679861465 (k6989586621679861466 :: (~>) a7566047373982791018 (First b7566047373982791019)) a_69895866216798614736989586621679861474
  where
    LamCases_6989586621679861470Sym0KindInference :: SameKind (Apply (LamCases_6989586621679861470Sym0 x6989586621679861469 a6989586621679861465 k6989586621679861466) arg_a3zyP) (LamCases_6989586621679861470Sym1 x6989586621679861469 a6989586621679861465 k6989586621679861466 arg_a3zyP) =>
                                                      LamCases_6989586621679861470Sym0 x6989586621679861469 a6989586621679861465 k6989586621679861466 a_69895866216798614736989586621679861474
type instance Apply @_ @_ (LamCases_6989586621679861470Sym0 x6989586621679861469 a6989586621679861465 k6989586621679861466) a_69895866216798614736989586621679861474 = LamCases_6989586621679861470_a3zyL x6989586621679861469 a6989586621679861465 k6989586621679861466 a_69895866216798614736989586621679861474
instance SuppressUnusedWarnings (LamCases_6989586621679861470Sym0 x6989586621679861469 a6989586621679861465 k6989586621679861466) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679861470Sym0KindInference ())
type family LamCases_6989586621679861470Sym1 x6989586621679861469 a6989586621679861465 (k6989586621679861466 :: (~>) a7566047373982791018 (First b7566047373982791019)) a_69895866216798614736989586621679861474 where
  LamCases_6989586621679861470Sym1 x6989586621679861469 a6989586621679861465 k6989586621679861466 a_69895866216798614736989586621679861474 = LamCases_6989586621679861470_a3zyL x6989586621679861469 a6989586621679861465 k6989586621679861466 a_69895866216798614736989586621679861474
type family LamCases_6989586621679861467_a3zyI a6989586621679861465 (k6989586621679861466 :: (~>) a7566047373982791018 (First b7566047373982791019)) a_6989586621679861476_a3zyR where
  LamCases_6989586621679861467_a3zyI a_a3zyF k_a3zyG x_a3zyJ = Apply (LamCases_6989586621679861470Sym0 x_a3zyJ a_a3zyF k_a3zyG) (Apply k_a3zyG x_a3zyJ)
data LamCases_6989586621679861467Sym0 a6989586621679861465 (k6989586621679861466 :: (~>) a7566047373982791018 (First b7566047373982791019)) a_69895866216798614766989586621679861477
  where
    LamCases_6989586621679861467Sym0KindInference :: SameKind (Apply (LamCases_6989586621679861467Sym0 a6989586621679861465 k6989586621679861466) arg_a3zyS) (LamCases_6989586621679861467Sym1 a6989586621679861465 k6989586621679861466 arg_a3zyS) =>
                                                      LamCases_6989586621679861467Sym0 a6989586621679861465 k6989586621679861466 a_69895866216798614766989586621679861477
type instance Apply @_ @_ (LamCases_6989586621679861467Sym0 a6989586621679861465 k6989586621679861466) a_69895866216798614766989586621679861477 = LamCases_6989586621679861467_a3zyI a6989586621679861465 k6989586621679861466 a_69895866216798614766989586621679861477
instance SuppressUnusedWarnings (LamCases_6989586621679861467Sym0 a6989586621679861465 k6989586621679861466) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679861467Sym0KindInference ())
type family LamCases_6989586621679861467Sym1 a6989586621679861465 (k6989586621679861466 :: (~>) a7566047373982791018 (First b7566047373982791019)) a_69895866216798614766989586621679861477 where
  LamCases_6989586621679861467Sym1 a6989586621679861465 k6989586621679861466 a_69895866216798614766989586621679861477 = LamCases_6989586621679861467_a3zyI a6989586621679861465 k6989586621679861466 a_69895866216798614766989586621679861477
type TFHelper_6989586621679861458 :: forall a_i1v3Y
                                            b_i1v3Z. First a_i1v3Y
                                                      -> (~>) a_i1v3Y (First b_i1v3Z)
                                                        -> First b_i1v3Z
type family TFHelper_6989586621679861458 @a_i1v3Y @b_i1v3Z (a_a3zyA :: First a_i1v3Y) (a_a3zyB :: (~>) a_i1v3Y (First b_i1v3Z)) :: First b_i1v3Z where
  TFHelper_6989586621679861458 @a_i1v3Y @b_i1v3Z ('First a_a3zyF) k_a3zyG = Apply FirstSym0 (Apply (Apply (>>=@#@$) a_a3zyF) (LamCases_6989586621679861467Sym0 a_a3zyF k_a3zyG))
instance PMonad First where
  type (>>=) a_a3zyw a_a3zyx = TFHelper_6989586621679861458 a_a3zyw a_a3zyx
type family Let6989586621679861530ASym0 a6989586621679860884 wild_69895866216798609006989586621679861529 where
  Let6989586621679861530ASym0 a6989586621679860884 wild_69895866216798609006989586621679861529 = Let6989586621679861530A a6989586621679860884 wild_69895866216798609006989586621679861529
type family Let6989586621679861530A a6989586621679860884 wild_69895866216798609006989586621679861529 where
  Let6989586621679861530A a_a3zpi wild_6989586621679860900_a3zzH = Apply FirstSym0 (Apply JustSym0 wild_6989586621679860900_a3zzH)
type TFHelper_6989586621679861521 :: forall a_a3zpi. First a_a3zpi
                                                      -> First a_a3zpi -> First a_a3zpi
type family TFHelper_6989586621679861521 @a_a3zpi (a_a3zzB :: First a_a3zpi) (a_a3zzC :: First a_a3zpi) :: First a_a3zpi where
  TFHelper_6989586621679861521 @a_a3zpi ('First 'Nothing :: First a_a3zpi) (b_a3zzG :: First a_a3zpi) = b_a3zzG
  TFHelper_6989586621679861521 @a_a3zpi ('First ('Just wild_6989586621679860900_a3zzH) :: First a_a3zpi) (_ :: First a_a3zpi) = Let6989586621679861530ASym0 a_a3zpi wild_6989586621679860900_a3zzH
instance PSemigroup (First a_a3zpi) where
  type (<>) a_a3zzx a_a3zzy = TFHelper_6989586621679861521 a_a3zzx a_a3zzy
type Mempty_6989586621679861532 :: forall a_a3zpl. First a_a3zpl
type family Mempty_6989586621679861532 @a_a3zpl :: First a_a3zpl where
  Mempty_6989586621679861532 @a_a3zpl = Apply FirstSym0 NothingSym0
instance PMonoid (First a_a3zpl) where
  type Mempty = Mempty_6989586621679861532
type Pure_6989586621679861536 :: forall a_i1v3p. a_i1v3p
                                                  -> Last a_i1v3p
type family Pure_6989586621679861536 @a_i1v3p (a_a3zzS :: a_i1v3p) :: Last a_i1v3p where
  Pure_6989586621679861536 @a_i1v3p a_6989586621679861538_a3zzV = Apply (Apply (Apply (.@#@$) LastSym0) PureSym0) a_6989586621679861538_a3zzV
type TFHelper_6989586621679861546 :: forall a_i1v3r
                                            b_i1v3s. Last ((~>) a_i1v3r b_i1v3s)
                                                      -> Last a_i1v3r -> Last b_i1v3s
type family TFHelper_6989586621679861546 @a_i1v3r @b_i1v3s (a_a3zA0 :: Last ((~>) a_i1v3r b_i1v3s)) (a_a3zA1 :: Last a_i1v3r) :: Last b_i1v3s where
  TFHelper_6989586621679861546 @a_i1v3r @b_i1v3s ('Last f_a3zA5) ('Last x_a3zA6) = Apply LastSym0 (Apply (Apply (<*>@#@$) f_a3zA5) x_a3zA6)
instance PApplicative Last where
  type Pure a_a3zzN = Pure_6989586621679861536 a_a3zzN
  type (<*>) a_a3zzW a_a3zzX = TFHelper_6989586621679861546 a_a3zzW a_a3zzX
type Fmap_6989586621679861557 :: forall a_i1v3K
                                        b_i1v3L. (~>) a_i1v3K b_i1v3L
                                                  -> Last a_i1v3K -> Last b_i1v3L
type family Fmap_6989586621679861557 @a_i1v3K @b_i1v3L (a_a3zAb :: (~>) a_i1v3K b_i1v3L) (a_a3zAc :: Last a_i1v3K) :: Last b_i1v3L where
  Fmap_6989586621679861557 @a_i1v3K @b_i1v3L _f_6989586621679861208_a3zAg ('Last a_6989586621679861218_a3zAh) = Apply LastSym0 (Apply (Apply FmapSym0 _f_6989586621679861208_a3zAg) a_6989586621679861218_a3zAh)
type TFHelper_6989586621679861568 :: forall a_i1v3O
                                            b_i1v3P. a_i1v3O -> Last b_i1v3P -> Last a_i1v3O
type family TFHelper_6989586621679861568 @a_i1v3O @b_i1v3P (a_a3zAm :: a_i1v3O) (a_a3zAn :: Last b_i1v3P) :: Last a_i1v3O where
  TFHelper_6989586621679861568 @a_i1v3O @b_i1v3P _z_6989586621679861210_a3zAr ('Last a_6989586621679861226_a3zAs) = Apply LastSym0 (Apply (Apply (<$@#@$) _z_6989586621679861210_a3zAr) a_6989586621679861226_a3zAs)
instance PFunctor Last where
  type Fmap a_a3zA7 a_a3zA8 = Fmap_6989586621679861557 a_a3zA7 a_a3zA8
  type (<$) a_a3zAi a_a3zAj = TFHelper_6989586621679861568 a_a3zAi a_a3zAj
type family LamCases_6989586621679861591_a3zAI x6989586621679861590 a6989586621679861586 (k6989586621679861587 :: (~>) a7566047373982791018 (Last b7566047373982791019)) a_6989586621679861594_a3zAL where
  LamCases_6989586621679861591_a3zAI x_a3zAG a_a3zAC k_a3zAD ('Last y_a3zAJ) = y_a3zAJ
data LamCases_6989586621679861591Sym0 x6989586621679861590 a6989586621679861586 (k6989586621679861587 :: (~>) a7566047373982791018 (Last b7566047373982791019)) a_69895866216798615946989586621679861595
  where
    LamCases_6989586621679861591Sym0KindInference :: SameKind (Apply (LamCases_6989586621679861591Sym0 x6989586621679861590 a6989586621679861586 k6989586621679861587) arg_a3zAM) (LamCases_6989586621679861591Sym1 x6989586621679861590 a6989586621679861586 k6989586621679861587 arg_a3zAM) =>
                                                      LamCases_6989586621679861591Sym0 x6989586621679861590 a6989586621679861586 k6989586621679861587 a_69895866216798615946989586621679861595
type instance Apply @_ @_ (LamCases_6989586621679861591Sym0 x6989586621679861590 a6989586621679861586 k6989586621679861587) a_69895866216798615946989586621679861595 = LamCases_6989586621679861591_a3zAI x6989586621679861590 a6989586621679861586 k6989586621679861587 a_69895866216798615946989586621679861595
instance SuppressUnusedWarnings (LamCases_6989586621679861591Sym0 x6989586621679861590 a6989586621679861586 k6989586621679861587) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679861591Sym0KindInference ())
type family LamCases_6989586621679861591Sym1 x6989586621679861590 a6989586621679861586 (k6989586621679861587 :: (~>) a7566047373982791018 (Last b7566047373982791019)) a_69895866216798615946989586621679861595 where
  LamCases_6989586621679861591Sym1 x6989586621679861590 a6989586621679861586 k6989586621679861587 a_69895866216798615946989586621679861595 = LamCases_6989586621679861591_a3zAI x6989586621679861590 a6989586621679861586 k6989586621679861587 a_69895866216798615946989586621679861595
type family LamCases_6989586621679861588_a3zAF a6989586621679861586 (k6989586621679861587 :: (~>) a7566047373982791018 (Last b7566047373982791019)) a_6989586621679861597_a3zAO where
  LamCases_6989586621679861588_a3zAF a_a3zAC k_a3zAD x_a3zAG = Apply (LamCases_6989586621679861591Sym0 x_a3zAG a_a3zAC k_a3zAD) (Apply k_a3zAD x_a3zAG)
data LamCases_6989586621679861588Sym0 a6989586621679861586 (k6989586621679861587 :: (~>) a7566047373982791018 (Last b7566047373982791019)) a_69895866216798615976989586621679861598
  where
    LamCases_6989586621679861588Sym0KindInference :: SameKind (Apply (LamCases_6989586621679861588Sym0 a6989586621679861586 k6989586621679861587) arg_a3zAP) (LamCases_6989586621679861588Sym1 a6989586621679861586 k6989586621679861587 arg_a3zAP) =>
                                                      LamCases_6989586621679861588Sym0 a6989586621679861586 k6989586621679861587 a_69895866216798615976989586621679861598
type instance Apply @_ @_ (LamCases_6989586621679861588Sym0 a6989586621679861586 k6989586621679861587) a_69895866216798615976989586621679861598 = LamCases_6989586621679861588_a3zAF a6989586621679861586 k6989586621679861587 a_69895866216798615976989586621679861598
instance SuppressUnusedWarnings (LamCases_6989586621679861588Sym0 a6989586621679861586 k6989586621679861587) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679861588Sym0KindInference ())
type family LamCases_6989586621679861588Sym1 a6989586621679861586 (k6989586621679861587 :: (~>) a7566047373982791018 (Last b7566047373982791019)) a_69895866216798615976989586621679861598 where
  LamCases_6989586621679861588Sym1 a6989586621679861586 k6989586621679861587 a_69895866216798615976989586621679861598 = LamCases_6989586621679861588_a3zAF a6989586621679861586 k6989586621679861587 a_69895866216798615976989586621679861598
type TFHelper_6989586621679861579 :: forall a_i1v3Y
                                            b_i1v3Z. Last a_i1v3Y
                                                      -> (~>) a_i1v3Y (Last b_i1v3Z)
                                                        -> Last b_i1v3Z
type family TFHelper_6989586621679861579 @a_i1v3Y @b_i1v3Z (a_a3zAx :: Last a_i1v3Y) (a_a3zAy :: (~>) a_i1v3Y (Last b_i1v3Z)) :: Last b_i1v3Z where
  TFHelper_6989586621679861579 @a_i1v3Y @b_i1v3Z ('Last a_a3zAC) k_a3zAD = Apply LastSym0 (Apply (Apply (>>=@#@$) a_a3zAC) (LamCases_6989586621679861588Sym0 a_a3zAC k_a3zAD))
instance PMonad Last where
  type (>>=) a_a3zAt a_a3zAu = TFHelper_6989586621679861579 a_a3zAt a_a3zAu
type family Let6989586621679861611BSym0 a6989586621679860894 wild_69895866216798609046989586621679861610 where
  Let6989586621679861611BSym0 a6989586621679860894 wild_69895866216798609046989586621679861610 = Let6989586621679861611B a6989586621679860894 wild_69895866216798609046989586621679861610
type family Let6989586621679861611B a6989586621679860894 wild_69895866216798609046989586621679861610 where
  Let6989586621679861611B a_a3zps wild_6989586621679860904_a3zB0 = Apply LastSym0 (Apply JustSym0 wild_6989586621679860904_a3zB0)
type TFHelper_6989586621679861602 :: forall a_a3zps. Last a_a3zps
                                                      -> Last a_a3zps -> Last a_a3zps
type family TFHelper_6989586621679861602 @a_a3zps (a_a3zAU :: Last a_a3zps) (a_a3zAV :: Last a_a3zps) :: Last a_a3zps where
  TFHelper_6989586621679861602 @a_a3zps (a_a3zAZ :: Last a_a3zps) ('Last 'Nothing :: Last a_a3zps) = a_a3zAZ
  TFHelper_6989586621679861602 @a_a3zps (_ :: Last a_a3zps) ('Last ('Just wild_6989586621679860904_a3zB0) :: Last a_a3zps) = Let6989586621679861611BSym0 a_a3zps wild_6989586621679860904_a3zB0
instance PSemigroup (Last a_a3zps) where
  type (<>) a_a3zAQ a_a3zAR = TFHelper_6989586621679861602 a_a3zAQ a_a3zAR
type Mempty_6989586621679861613 :: forall a_a3zpv. Last a_a3zpv
type family Mempty_6989586621679861613 @a_a3zpv :: Last a_a3zpv where
  Mempty_6989586621679861613 @a_a3zpv = Apply LastSym0 NothingSym0
instance PMonoid (Last a_a3zpv) where
  type Mempty = Mempty_6989586621679861613
instance SMonoid a_a3zp8 => SMonoid (Dual a_a3zp8) where
  sMempty = applySing (singFun1 @DualSym0 SDual) sMempty
instance SMonoid All where
  sMempty = applySing (singFun1 @AllSym0 SAll) STrue
instance SMonoid Any where
  sMempty = applySing (singFun1 @AnySym0 SAny) SFalse
instance SNum a_a3zp9 => SMonoid (Sum a_a3zp9) where
  sMempty
    = applySing
        (singFun1 @SumSym0 SSum) (sFromInteger (sing :: Sing 0))
instance SNum a_a3zpa => SMonoid (Product a_a3zpa) where
  sMempty
    = applySing
        (singFun1 @ProductSym0 SProduct) (sFromInteger (sing :: Sing 1))
instance SMonoid a_a3zpb => SMonoid (Down a_a3zpb) where
  sMempty = applySing (singFun1 @DownSym0 SDown) sMempty
instance SApplicative First where
  sPure (sA_6989586621679861327 :: Sing a_6989586621679861327_a3zww)
    = applySing
        (applySing
            (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @FirstSym0 SFirst))
            (singFun1 @PureSym0 sPure))
        sA_6989586621679861327
  (%<*>) (SFirst (sF :: Sing f_a3zwG)) (SFirst (sX :: Sing x_a3zwH))
    = applySing
        (singFun1 @FirstSym0 SFirst)
        (applySing (applySing (singFun2 @(<*>@#@$) (%<*>)) sF) sX)
instance SFunctor First where
  sFmap
    (_sf_6989586621679861181 :: Sing _f_6989586621679861181_a3zxD)
    (SFirst (sA_6989586621679861191 :: Sing a_6989586621679861191_a3zxE))
    = applySing
        (singFun1 @FirstSym0 SFirst)
        (applySing
            (applySing (singFun2 @FmapSym0 sFmap) _sf_6989586621679861181)
            sA_6989586621679861191)
  (%<$)
    (_sz_6989586621679861183 :: Sing _z_6989586621679861183_a3zxO)
    (SFirst (sA_6989586621679861199 :: Sing a_6989586621679861199_a3zxP))
    = applySing
        (singFun1 @FirstSym0 SFirst)
        (applySing
            (applySing (singFun2 @(<$@#@$) (%<$)) _sz_6989586621679861183)
            sA_6989586621679861199)
instance SMonad First where
  (%>>=) (SFirst (sA :: Sing a_a3zyF)) (sK :: Sing k_a3zyG)
    = applySing
        (singFun1 @FirstSym0 SFirst)
        (applySing
            (applySing (singFun2 @(>>=@#@$) (%>>=)) sA)
            (singFun1
              @(LamCases_6989586621679861467Sym0 a_a3zyF k_a3zyG)
              (\cases
                  (sX :: Sing x_a3zyJ)
                    -> applySing
                        (singFun1
                            @(LamCases_6989586621679861470Sym0 x_a3zyJ a_a3zyF k_a3zyG)
                            (\cases (SFirst (sY :: Sing y_a3zyM)) -> sY))
                        (applySing sK sX))))
instance SSemigroup (First a_a3zpi) where
  (%<>) (SFirst SNothing) (sB :: Sing b_a3zzG) = sB
  (%<>)
    (SFirst (SJust (sWild_6989586621679860900 :: Sing wild_6989586621679860900_a3zzH)))
    _
    = let
        sA ::
          Sing @_ (Let6989586621679861530A a_a3zpi wild_6989586621679860900_a3zzH)
        sA
          = applySing
              (singFun1 @FirstSym0 SFirst)
              (applySing (singFun1 @JustSym0 SJust) sWild_6989586621679860900)
      in sA
instance SMonoid (First a_a3zpl) where
  sMempty = applySing (singFun1 @FirstSym0 SFirst) SNothing
instance SApplicative Last where
  sPure (sA_6989586621679861538 :: Sing a_6989586621679861538_a3zzV)
    = applySing
        (applySing
            (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @LastSym0 SLast))
            (singFun1 @PureSym0 sPure))
        sA_6989586621679861538
  (%<*>) (SLast (sF :: Sing f_a3zA5)) (SLast (sX :: Sing x_a3zA6))
    = applySing
        (singFun1 @LastSym0 SLast)
        (applySing (applySing (singFun2 @(<*>@#@$) (%<*>)) sF) sX)
instance SFunctor Last where
  sFmap
    (_sf_6989586621679861208 :: Sing _f_6989586621679861208_a3zAg)
    (SLast (sA_6989586621679861218 :: Sing a_6989586621679861218_a3zAh))
    = applySing
        (singFun1 @LastSym0 SLast)
        (applySing
            (applySing (singFun2 @FmapSym0 sFmap) _sf_6989586621679861208)
            sA_6989586621679861218)
  (%<$)
    (_sz_6989586621679861210 :: Sing _z_6989586621679861210_a3zAr)
    (SLast (sA_6989586621679861226 :: Sing a_6989586621679861226_a3zAs))
    = applySing
        (singFun1 @LastSym0 SLast)
        (applySing
            (applySing (singFun2 @(<$@#@$) (%<$)) _sz_6989586621679861210)
            sA_6989586621679861226)
instance SMonad Last where
  (%>>=) (SLast (sA :: Sing a_a3zAC)) (sK :: Sing k_a3zAD)
    = applySing
        (singFun1 @LastSym0 SLast)
        (applySing
            (applySing (singFun2 @(>>=@#@$) (%>>=)) sA)
            (singFun1
              @(LamCases_6989586621679861588Sym0 a_a3zAC k_a3zAD)
              (\cases
                  (sX :: Sing x_a3zAG)
                    -> applySing
                        (singFun1
                            @(LamCases_6989586621679861591Sym0 x_a3zAG a_a3zAC k_a3zAD)
                            (\cases (SLast (sY :: Sing y_a3zAJ)) -> sY))
                        (applySing sK sX))))
instance SSemigroup (Last a_a3zps) where
  (%<>) (sA :: Sing a_a3zAZ) (SLast SNothing) = sA
  (%<>)
    _
    (SLast (SJust (sWild_6989586621679860904 :: Sing wild_6989586621679860904_a3zB0)))
    = let
        sB ::
          Sing @_ (Let6989586621679861611B a_a3zps wild_6989586621679860904_a3zB0)
        sB
          = applySing
              (singFun1 @LastSym0 SLast)
              (applySing (singFun1 @JustSym0 SJust) sWild_6989586621679860904)
      in sB
instance SMonoid (Last a_a3zpv) where
  sMempty = applySing (singFun1 @LastSym0 SLast) SNothing
