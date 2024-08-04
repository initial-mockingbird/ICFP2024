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
{-# LANGUAGE InstanceSigs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Foldable.Singletons
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted and singled versions of the 'Foldable' type class.
--
----------------------------------------------------------------------------

module Data.Foldable.Singletons (
  PFoldable(..), SFoldable(..),

  FoldrM, sFoldrM,
  FoldlM, sFoldlM,

  Traverse_, sTraverse_,
  For_, sFor_,
  SequenceA_, sSequenceA_,
  Asum, sAsum,

  MapM_, sMapM_,
  ForM_, sForM_,
  Sequence_, sSequence_,
  Msum, sMsum,

  Concat, sConcat,
  ConcatMap, sConcatMap,
  And, sAnd,
  Or, sOr,
  Any, sAny,
  All, sAll,
  MaximumBy, sMaximumBy,
  MinimumBy, sMinimumBy,

  NotElem, sNotElem,
  Find, sFind,

  -- * Defunctionalization symbols
  FoldSym0, FoldSym1,
  FoldMapSym0, FoldMapSym1, FoldMapSym2,
  FoldrSym0, FoldrSym1, FoldrSym2, FoldrSym3,
  Foldr'Sym0, Foldr'Sym1, Foldr'Sym2, Foldr'Sym3,
  FoldlSym0, FoldlSym1, FoldlSym2, FoldlSym3,
  Foldl'Sym0, Foldl'Sym1, Foldl'Sym2, Foldl'Sym3,
  Foldr1Sym0, Foldr1Sym1, Foldr1Sym2,
  Foldl1Sym0, Foldl1Sym1, Foldl1Sym2,
  ToListSym0, ToListSym1,
  NullSym0, NullSym1,
  LengthSym0, LengthSym1,
  ElemSym0, ElemSym1, ElemSym2,
  MaximumSym0, MaximumSym1,
  MinimumSym0, MinimumSym1,
  SumSym0, SumSym1,
  ProductSym0, ProductSym1,

  FoldrMSym0, FoldrMSym1, FoldrMSym2, FoldrMSym3,
  FoldlMSym0, FoldlMSym1, FoldlMSym2, FoldlMSym3,

  Traverse_Sym0, Traverse_Sym1, Traverse_Sym2,
  For_Sym0, For_Sym1, For_Sym2,
  SequenceA_Sym0, SequenceA_Sym1,
  AsumSym0, AsumSym1,

  MapM_Sym0, MapM_Sym1, MapM_Sym2,
  ForM_Sym0, ForM_Sym1, ForM_Sym2,
  Sequence_Sym0, Sequence_Sym1,
  MsumSym0, MsumSym1,

  ConcatSym0, ConcatSym1,
  ConcatMapSym0, ConcatMapSym1, ConcatMapSym2,
  AndSym0, AndSym1,
  OrSym0, OrSym1,
  AnySym0, AnySym1, AnySym2,
  AllSym0, AllSym1, AllSym2,
  MaximumBySym0, MaximumBySym1, MaximumBySym2,
  MinimumBySym0, MinimumBySym1, MinimumBySym2,

  NotElemSym0, NotElemSym1, NotElemSym2,
  FindSym0, FindSym1, FindSym2
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Singletons.Internal
import Data.Bool.Singletons
import Data.Either.Singletons
import Data.Eq.Singletons
import Data.Kind
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.Singletons.Internal.Disambiguation
import Data.Maybe.Singletons
import Data.Monoid hiding (All(..), Any(..), Endo(..), Product(..), Sum(..))
import Data.Monoid.Singletons
  hiding ( AllSym0,     AllSym1
         , AnySym0,     AnySym1
         , ProductSym0, ProductSym1
         , SumSym0,     SumSym1 )
import qualified Data.Monoid as Monoid (Product(..), Sum(..))
import Data.Ord.Singletons
  hiding ( Max, MaxSym0, MaxSym1, MaxSym2, sMax
         , Min, MinSym0, MinSym1, MinSym2, sMin )
import Data.Semigroup.Singletons.Internal.Classes
import Data.Semigroup.Singletons.Internal.Disambiguation
import Data.Singletons
import Data.Singletons.Base.Instances
  hiding (Foldl, FoldlSym0(..), FoldlSym1(..), FoldlSym2(..), FoldlSym3, sFoldl)
import Data.Singletons.TH
import GHC.Base.Singletons
  hiding (Foldr, FoldrSym0, FoldrSym1, FoldrSym2, FoldrSym3, sFoldr)
import GHC.Num.Singletons
import GHC.TypeLits.Singletons.Internal

type Endo :: Type -> Type
newtype Endo a = Endo (a ~> a)
type SEndo :: Endo a -> Type
data SEndo e where
  SEndo :: Sing x -> SEndo ('Endo x)
type instance Sing @(Endo a) = SEndo
type EndoSym0 :: (a ~> a) ~> Endo a
data EndoSym0 tf
type instance Apply EndoSym0 x = 'Endo x

type AppEndoSym0 :: (~>) (Endo a_aqZp) ((~>) a_aqZp a_aqZp)
data AppEndoSym0 :: (~>) (Endo a_aqZp) ((~>) a_aqZp a_aqZp)
  where
    AppEndoSym0KindInference :: SameKind (Apply AppEndoSym0 arg_arb6) (AppEndoSym1 arg_arb6) =>
                                AppEndoSym0 a6989586621679114269
type instance Apply @(Endo a_aqZp) @((~>) a_aqZp a_aqZp) AppEndoSym0 a6989586621679114269 = AppEndoSym1 a6989586621679114269
instance SuppressUnusedWarnings AppEndoSym0 where
  suppressUnusedWarnings = snd ((,) AppEndoSym0KindInference ())
type AppEndoSym1 :: Endo a_aqZp -> (~>) a_aqZp a_aqZp
data AppEndoSym1 (a6989586621679114269 :: Endo a_aqZp) :: (~>) a_aqZp a_aqZp
  where
    AppEndoSym1KindInference :: SameKind (Apply (AppEndoSym1 a6989586621679114269) arg_arb6) (AppEndoSym2 a6989586621679114269 arg_arb6) =>
                                AppEndoSym1 a6989586621679114269 a6989586621679114270
type instance Apply @a_aqZp @a_aqZp (AppEndoSym1 a6989586621679114269) a6989586621679114270 = AppEndo a6989586621679114269 a6989586621679114270
instance SuppressUnusedWarnings (AppEndoSym1 a6989586621679114269) where
  suppressUnusedWarnings = snd ((,) AppEndoSym1KindInference ())
type AppEndoSym2 :: Endo a_aqZp -> a_aqZp -> a_aqZp
type family AppEndoSym2 @a_aqZp (a6989586621679114269 :: Endo a_aqZp) (a6989586621679114270 :: a_aqZp) :: a_aqZp where
  AppEndoSym2 a6989586621679114269 a6989586621679114270 = AppEndo a6989586621679114269 a6989586621679114270
type AppEndo :: Endo a_aqZp -> a_aqZp -> a_aqZp
type family AppEndo @a_aqZp (a_arb4 :: Endo a_aqZp) (a_arb5 :: a_aqZp) :: a_aqZp where
  AppEndo ('Endo x_arb9) a_6989586621679114264_arba = Apply x_arb9 a_6989586621679114264_arba
type TFHelper_6989586621679114521 :: forall a_aqZs. Endo a_aqZs
                                                    -> Endo a_aqZs -> Endo a_aqZs
type family TFHelper_6989586621679114521 @a_aqZs (a_arfd :: Endo a_aqZs) (a_arfe :: Endo a_aqZs) :: Endo a_aqZs where
  TFHelper_6989586621679114521 @a_aqZs ('Endo x_arfi :: Endo a_aqZs) ('Endo y_arfj :: Endo a_aqZs) = Apply EndoSym0 (Apply (Apply (.@#@$) x_arfi) y_arfj)
instance PSemigroup (Endo a_aqZs) where
  type (<>) a_arf9 a_arfa = TFHelper_6989586621679114521 a_arf9 a_arfa
type Mempty_6989586621679114739 :: forall a_aqZv. Endo a_aqZv
type family Mempty_6989586621679114739 @a_aqZv :: Endo a_aqZv where
  Mempty_6989586621679114739 @a_aqZv = Apply EndoSym0 IdSym0
instance PMonoid (Endo a_aqZv) where
  type Mempty = Mempty_6989586621679114739
sAppEndo ::
  (forall (t_ariK :: Endo a_aqZp) (t_ariL :: a_aqZp).
    Sing t_ariK
    -> Sing t_ariL -> Sing (AppEndo t_ariK t_ariL :: a_aqZp) :: Type)
sAppEndo
  (SEndo (sX :: Sing x_arb9))
  (sA_6989586621679114264 :: Sing a_6989586621679114264_arba)
  = applySing sX sA_6989586621679114264
instance SingI (AppEndoSym0 :: (~>) (Endo a_aqZp) ((~>) a_aqZp a_aqZp)) where
  sing = singFun2 @AppEndoSym0 sAppEndo
instance SingI d_ariM =>
          SingI (AppEndoSym1 (d_ariM :: Endo a_aqZp) :: (~>) a_aqZp a_aqZp) where
  sing
    = singFun1
        @(AppEndoSym1 (d_ariM :: Endo a_aqZp)) (sAppEndo (sing @d_ariM))
instance SingI1 (AppEndoSym1 :: Endo a_aqZp
                                -> (~>) a_aqZp a_aqZp) where
  liftSing (s_ariO :: Sing (d_ariM :: Endo a_aqZp))
    = singFun1 @(AppEndoSym1 (d_ariM :: Endo a_aqZp)) (sAppEndo s_ariO)
instance SSemigroup (Endo a_aqZs) where
  (%<>) (SEndo (sX :: Sing x_arfi)) (SEndo (sY :: Sing y_arfj))
    = applySing
        (singFun1 @EndoSym0 SEndo)
        (applySing (applySing (singFun3 @(.@#@$) (%.)) sX) sY)
instance SMonoid (Endo a_aqZv) where
  sMempty
    = applySing (singFun1 @EndoSym0 SEndo) (singFun1 @IdSym0 sId)

newtype MaxInternal a_arBY
      = MaxInternal {getMaxInternal_arBW :: (Maybe a_arBY)}
newtype MinInternal a_arBZ
  = MinInternal {getMinInternal_arBX :: (Maybe a_arBZ)}
type MaxInternalSym0 :: forall a_arBY. (~>) (Maybe a_arBY) (MaxInternal a_arBY)
data MaxInternalSym0 :: (~>) (Maybe a_arBY) (MaxInternal a_arBY)
  where
    MaxInternalSym0KindInference :: SameKind (Apply MaxInternalSym0 arg_arC9) (MaxInternalSym1 arg_arC9) =>
                                    MaxInternalSym0 a6989586621679115946
type instance Apply @(Maybe a_arBY) @(MaxInternal a_arBY) MaxInternalSym0 a6989586621679115946 = 'MaxInternal a6989586621679115946
instance SuppressUnusedWarnings MaxInternalSym0 where
  suppressUnusedWarnings = snd ((,) MaxInternalSym0KindInference ())
type MaxInternalSym1 :: forall a_arBY. Maybe a_arBY
                                        -> MaxInternal a_arBY
type family MaxInternalSym1 @a_arBY (a6989586621679115946 :: Maybe a_arBY) :: MaxInternal a_arBY where
  MaxInternalSym1 a6989586621679115946 = 'MaxInternal a6989586621679115946
type MinInternalSym0 :: forall a_arBZ. (~>) (Maybe a_arBZ) (MinInternal a_arBZ)
data MinInternalSym0 :: (~>) (Maybe a_arBZ) (MinInternal a_arBZ)
  where
    MinInternalSym0KindInference :: SameKind (Apply MinInternalSym0 arg_arCc) (MinInternalSym1 arg_arCc) =>
                                    MinInternalSym0 a6989586621679115949
type instance Apply @(Maybe a_arBZ) @(MinInternal a_arBZ) MinInternalSym0 a6989586621679115949 = 'MinInternal a6989586621679115949
instance SuppressUnusedWarnings MinInternalSym0 where
  suppressUnusedWarnings = snd ((,) MinInternalSym0KindInference ())
type MinInternalSym1 :: forall a_arBZ. Maybe a_arBZ
                                        -> MinInternal a_arBZ
type family MinInternalSym1 @a_arBZ (a6989586621679115949 :: Maybe a_arBZ) :: MinInternal a_arBZ where
  MinInternalSym1 a6989586621679115949 = 'MinInternal a6989586621679115949
type GetMinInternalSym0 :: forall a_arBZ. (~>) (MinInternal a_arBZ) (Maybe a_arBZ)
data GetMinInternalSym0 :: (~>) (MinInternal a_arBZ) (Maybe a_arBZ)
  where
    GetMinInternalSym0KindInference :: SameKind (Apply GetMinInternalSym0 arg_arCf) (GetMinInternalSym1 arg_arCf) =>
                                        GetMinInternalSym0 a6989586621679115952
type instance Apply @(MinInternal a_arBZ) @(Maybe a_arBZ) GetMinInternalSym0 a6989586621679115952 = GetMinInternal a6989586621679115952
instance SuppressUnusedWarnings GetMinInternalSym0 where
  suppressUnusedWarnings
    = snd ((,) GetMinInternalSym0KindInference ())
type GetMinInternalSym1 :: forall a_arBZ. MinInternal a_arBZ
                                          -> Maybe a_arBZ
type family GetMinInternalSym1 @a_arBZ (a6989586621679115952 :: MinInternal a_arBZ) :: Maybe a_arBZ where
  GetMinInternalSym1 a6989586621679115952 = GetMinInternal a6989586621679115952
type GetMaxInternalSym0 :: forall a_arBY. (~>) (MaxInternal a_arBY) (Maybe a_arBY)
data GetMaxInternalSym0 :: (~>) (MaxInternal a_arBY) (Maybe a_arBY)
  where
    GetMaxInternalSym0KindInference :: SameKind (Apply GetMaxInternalSym0 arg_arCj) (GetMaxInternalSym1 arg_arCj) =>
                                        GetMaxInternalSym0 a6989586621679115956
type instance Apply @(MaxInternal a_arBY) @(Maybe a_arBY) GetMaxInternalSym0 a6989586621679115956 = GetMaxInternal a6989586621679115956
instance SuppressUnusedWarnings GetMaxInternalSym0 where
  suppressUnusedWarnings
    = snd ((,) GetMaxInternalSym0KindInference ())
type GetMaxInternalSym1 :: forall a_arBY. MaxInternal a_arBY
                                          -> Maybe a_arBY
type family GetMaxInternalSym1 @a_arBY (a6989586621679115956 :: MaxInternal a_arBY) :: Maybe a_arBY where
  GetMaxInternalSym1 a6989586621679115956 = GetMaxInternal a6989586621679115956
type GetMinInternal :: forall a_arBZ. MinInternal a_arBZ
                                      -> Maybe a_arBZ
type family GetMinInternal @a_arBZ (a_arCe :: MinInternal a_arBZ) :: Maybe a_arBZ where
  GetMinInternal @a_arBZ ('MinInternal field_arCh :: MinInternal a_arBZ) = field_arCh
type GetMaxInternal :: forall a_arBY. MaxInternal a_arBY
                                      -> Maybe a_arBY
type family GetMaxInternal @a_arBY (a_arCi :: MaxInternal a_arBY) :: Maybe a_arBY where
  GetMaxInternal @a_arBY ('MaxInternal field_arCl :: MaxInternal a_arBY) = field_arCl
sGetMinInternal ::
  forall a_arBZ (t_arCm :: MinInternal a_arBZ). Sing t_arCm
                                                      -> Sing (GetMinInternal t_arCm :: Maybe a_arBZ)
sGetMaxInternal ::
  forall a_arBY (t_arCo :: MaxInternal a_arBY). Sing t_arCo
                                                      -> Sing (GetMaxInternal t_arCo :: Maybe a_arBY)
sGetMinInternal (SMinInternal (sField :: Sing field_arCh)) = sField
sGetMaxInternal (SMaxInternal (sField :: Sing field_arCl)) = sField
instance SingI (GetMinInternalSym0 :: (~>) (MinInternal a_arBZ) (Maybe a_arBZ)) where
  sing = singFun1 @GetMinInternalSym0 sGetMinInternal
instance SingI (GetMaxInternalSym0 :: (~>) (MaxInternal a_arBY) (Maybe a_arBY)) where
  sing = singFun1 @GetMaxInternalSym0 sGetMaxInternal
data SMaxInternal :: forall a_arBY. MaxInternal a_arBY -> Type
  where
    SMaxInternal :: forall a_arBY (n_arCq :: Maybe a_arBY).
                    (Sing n_arCq) ->
                    SMaxInternal ('MaxInternal n_arCq :: MaxInternal a_arBY)
type instance Sing @(MaxInternal a_arBY) = SMaxInternal
instance SingKind a_arBY =>
          SingKind (MaxInternal a_arBY) where
  type Demote (MaxInternal a_arBY) = MaxInternal (Demote a_arBY)
  fromSing (SMaxInternal b_arCs) = MaxInternal (fromSing b_arCs)
  toSing (MaxInternal (b_arCu :: Demote (Maybe a_arBY)))
    = (\cases (SomeSing c_arCv) -> SomeSing (SMaxInternal c_arCv))
        (toSing b_arCu :: SomeSing (Maybe a_arBY))
data SMinInternal :: forall a_arBZ. MinInternal a_arBZ -> Type
  where
    SMinInternal :: forall a_arBZ (n_arCx :: Maybe a_arBZ).
                    (Sing n_arCx) ->
                    SMinInternal ('MinInternal n_arCx :: MinInternal a_arBZ)
type instance Sing @(MinInternal a_arBZ) = SMinInternal
instance SingKind a_arBZ =>
          SingKind (MinInternal a_arBZ) where
  type Demote (MinInternal a_arBZ) = MinInternal (Demote a_arBZ)
  fromSing (SMinInternal b_arCz) = MinInternal (fromSing b_arCz)
  toSing (MinInternal (b_arCB :: Demote (Maybe a_arBZ)))
    = (\cases (SomeSing c_arCC) -> SomeSing (SMinInternal c_arCC))
        (toSing b_arCB :: SomeSing (Maybe a_arBZ))
instance SingI n_arCq =>
          SingI ('MaxInternal (n_arCq :: Maybe a_arBY)) where
  sing = SMaxInternal sing
instance SingI1 'MaxInternal where
  liftSing = SMaxInternal
instance SingI (MaxInternalSym0 :: (~>) (Maybe a_arBY) (MaxInternal a_arBY)) where
  sing = singFun1 @MaxInternalSym0 SMaxInternal
instance SingI n_arCx =>
          SingI ('MinInternal (n_arCx :: Maybe a_arBZ)) where
  sing = SMinInternal sing
instance SingI1 'MinInternal where
  liftSing = SMinInternal
instance SingI (MinInternalSym0 :: (~>) (Maybe a_arBZ) (MinInternal a_arBZ)) where
  sing = singFun1 @MinInternalSym0 SMinInternal

type family Let6989586621679118884NSym0 a6989586621679117884 x6989586621679118882 y6989586621679118883 where
      Let6989586621679118884NSym0 a6989586621679117884 x6989586621679118882 y6989586621679118883 = Let6989586621679118884N a6989586621679117884 x6989586621679118882 y6989586621679118883
type family Let6989586621679118884MSym0 a6989586621679117884 x6989586621679118882 y6989586621679118883 where
  Let6989586621679118884MSym0 a6989586621679117884 x6989586621679118882 y6989586621679118883 = Let6989586621679118884M a6989586621679117884 x6989586621679118882 y6989586621679118883
type family Let6989586621679118884N a6989586621679117884 x6989586621679118882 y6989586621679118883 where
  Let6989586621679118884N a_as7q x_asnw y_asnx = Apply JustSym0 y_asnx
type family Let6989586621679118884M a6989586621679117884 x6989586621679118882 y6989586621679118883 where
  Let6989586621679118884M a_as7q x_asnw y_asnx = Apply JustSym0 x_asnw
type family LamCases_6989586621679118887_asnC a6989586621679117884 x6989586621679118882 y6989586621679118883 a_6989586621679118889_asnE where
  LamCases_6989586621679118887_asnC a_as7q x_asnw y_asnx 'True = Apply MaxInternalSym0 (Let6989586621679118884MSym0 a_as7q x_asnw y_asnx)
  LamCases_6989586621679118887_asnC a_as7q x_asnw y_asnx 'False = Apply MaxInternalSym0 (Let6989586621679118884NSym0 a_as7q x_asnw y_asnx)
data LamCases_6989586621679118887Sym0 a6989586621679117884 x6989586621679118882 y6989586621679118883 a_69895866216791188896989586621679118890
  where
    LamCases_6989586621679118887Sym0KindInference :: SameKind (Apply (LamCases_6989586621679118887Sym0 a6989586621679117884 x6989586621679118882 y6989586621679118883) arg_asnF) (LamCases_6989586621679118887Sym1 a6989586621679117884 x6989586621679118882 y6989586621679118883 arg_asnF) =>
                                                      LamCases_6989586621679118887Sym0 a6989586621679117884 x6989586621679118882 y6989586621679118883 a_69895866216791188896989586621679118890
type instance Apply @_ @_ (LamCases_6989586621679118887Sym0 a6989586621679117884 x6989586621679118882 y6989586621679118883) a_69895866216791188896989586621679118890 = LamCases_6989586621679118887_asnC a6989586621679117884 x6989586621679118882 y6989586621679118883 a_69895866216791188896989586621679118890
instance SuppressUnusedWarnings (LamCases_6989586621679118887Sym0 a6989586621679117884 x6989586621679118882 y6989586621679118883) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679118887Sym0KindInference ())
type family LamCases_6989586621679118887Sym1 a6989586621679117884 x6989586621679118882 y6989586621679118883 a_69895866216791188896989586621679118890 where
  LamCases_6989586621679118887Sym1 a6989586621679117884 x6989586621679118882 y6989586621679118883 a_69895866216791188896989586621679118890 = LamCases_6989586621679118887_asnC a6989586621679117884 x6989586621679118882 y6989586621679118883 a_69895866216791188896989586621679118890
type TFHelper_6989586621679118873 :: forall a_as7q. MaxInternal a_as7q
                                                    -> MaxInternal a_as7q -> MaxInternal a_as7q
type family TFHelper_6989586621679118873 @a_as7q (a_asnp :: MaxInternal a_as7q) (a_asnq :: MaxInternal a_as7q) :: MaxInternal a_as7q where
  TFHelper_6989586621679118873 @a_as7q (m_asnu :: MaxInternal a_as7q) ('MaxInternal 'Nothing :: MaxInternal a_as7q) = m_asnu
  TFHelper_6989586621679118873 @a_as7q ('MaxInternal 'Nothing :: MaxInternal a_as7q) (n_asnv :: MaxInternal a_as7q) = n_asnv
  TFHelper_6989586621679118873 @a_as7q ('MaxInternal ('Just x_asnw) :: MaxInternal a_as7q) ('MaxInternal ('Just y_asnx) :: MaxInternal a_as7q) = Apply (LamCases_6989586621679118887Sym0 a_as7q x_asnw y_asnx) (Apply (Apply (>=@#@$) x_asnw) y_asnx)
instance PSemigroup (MaxInternal a_as7q) where
  type (<>) a_asnl a_asnm = TFHelper_6989586621679118873 a_asnl a_asnm
type Mempty_6989586621679118892 :: forall a_as7x. MaxInternal a_as7x
type family Mempty_6989586621679118892 @a_as7x :: MaxInternal a_as7x where
  Mempty_6989586621679118892 @a_as7x = Apply MaxInternalSym0 NothingSym0
instance PMonoid (MaxInternal a_as7x) where
  type Mempty = Mempty_6989586621679118892
type family Let6989586621679118908NSym0 a6989586621679117892 x6989586621679118906 y6989586621679118907 where
  Let6989586621679118908NSym0 a6989586621679117892 x6989586621679118906 y6989586621679118907 = Let6989586621679118908N a6989586621679117892 x6989586621679118906 y6989586621679118907
type family Let6989586621679118908MSym0 a6989586621679117892 x6989586621679118906 y6989586621679118907 where
  Let6989586621679118908MSym0 a6989586621679117892 x6989586621679118906 y6989586621679118907 = Let6989586621679118908M a6989586621679117892 x6989586621679118906 y6989586621679118907
type family Let6989586621679118908N a6989586621679117892 x6989586621679118906 y6989586621679118907 where
  Let6989586621679118908N a_as7y x_asnU y_asnV = Apply JustSym0 y_asnV
type family Let6989586621679118908M a6989586621679117892 x6989586621679118906 y6989586621679118907 where
  Let6989586621679118908M a_as7y x_asnU y_asnV = Apply JustSym0 x_asnU
type family LamCases_6989586621679118911_aso0 a6989586621679117892 x6989586621679118906 y6989586621679118907 a_6989586621679118913_aso2 where
  LamCases_6989586621679118911_aso0 a_as7y x_asnU y_asnV 'True = Apply MinInternalSym0 (Let6989586621679118908MSym0 a_as7y x_asnU y_asnV)
  LamCases_6989586621679118911_aso0 a_as7y x_asnU y_asnV 'False = Apply MinInternalSym0 (Let6989586621679118908NSym0 a_as7y x_asnU y_asnV)
data LamCases_6989586621679118911Sym0 a6989586621679117892 x6989586621679118906 y6989586621679118907 a_69895866216791189136989586621679118914
  where
    LamCases_6989586621679118911Sym0KindInference :: SameKind (Apply (LamCases_6989586621679118911Sym0 a6989586621679117892 x6989586621679118906 y6989586621679118907) arg_aso3) (LamCases_6989586621679118911Sym1 a6989586621679117892 x6989586621679118906 y6989586621679118907 arg_aso3) =>
                                                      LamCases_6989586621679118911Sym0 a6989586621679117892 x6989586621679118906 y6989586621679118907 a_69895866216791189136989586621679118914
type instance Apply @_ @_ (LamCases_6989586621679118911Sym0 a6989586621679117892 x6989586621679118906 y6989586621679118907) a_69895866216791189136989586621679118914 = LamCases_6989586621679118911_aso0 a6989586621679117892 x6989586621679118906 y6989586621679118907 a_69895866216791189136989586621679118914
instance SuppressUnusedWarnings (LamCases_6989586621679118911Sym0 a6989586621679117892 x6989586621679118906 y6989586621679118907) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679118911Sym0KindInference ())
type family LamCases_6989586621679118911Sym1 a6989586621679117892 x6989586621679118906 y6989586621679118907 a_69895866216791189136989586621679118914 where
  LamCases_6989586621679118911Sym1 a6989586621679117892 x6989586621679118906 y6989586621679118907 a_69895866216791189136989586621679118914 = LamCases_6989586621679118911_aso0 a6989586621679117892 x6989586621679118906 y6989586621679118907 a_69895866216791189136989586621679118914
type TFHelper_6989586621679118897 :: forall a_as7y. MinInternal a_as7y
                                                    -> MinInternal a_as7y -> MinInternal a_as7y
type family TFHelper_6989586621679118897 @a_as7y (a_asnN :: MinInternal a_as7y) (a_asnO :: MinInternal a_as7y) :: MinInternal a_as7y where
  TFHelper_6989586621679118897 @a_as7y (m_asnS :: MinInternal a_as7y) ('MinInternal 'Nothing :: MinInternal a_as7y) = m_asnS
  TFHelper_6989586621679118897 @a_as7y ('MinInternal 'Nothing :: MinInternal a_as7y) (n_asnT :: MinInternal a_as7y) = n_asnT
  TFHelper_6989586621679118897 @a_as7y ('MinInternal ('Just x_asnU) :: MinInternal a_as7y) ('MinInternal ('Just y_asnV) :: MinInternal a_as7y) = Apply (LamCases_6989586621679118911Sym0 a_as7y x_asnU y_asnV) (Apply (Apply (<=@#@$) x_asnU) y_asnV)
instance PSemigroup (MinInternal a_as7y) where
  type (<>) a_asnJ a_asnK = TFHelper_6989586621679118897 a_asnJ a_asnK
type Mempty_6989586621679118916 :: forall a_as7F. MinInternal a_as7F
type family Mempty_6989586621679118916 @a_as7F :: MinInternal a_as7F where
  Mempty_6989586621679118916 @a_as7F = Apply MinInternalSym0 NothingSym0
instance PMonoid (MinInternal a_as7F) where
  type Mempty = Mempty_6989586621679118916
instance SOrd a_as7q => SSemigroup (MaxInternal a_as7q) where
  (%<>) (sM :: Sing m_asnu) (SMaxInternal SNothing) = sM
  (%<>) (SMaxInternal SNothing) (sN :: Sing n_asnv) = sN
  (%<>)
    (SMaxInternal (SJust (sX :: Sing x_asnw)))
    (SMaxInternal (SJust (sY :: Sing y_asnx)))
    = let
        sN :: Sing @_ (Let6989586621679118884N a_as7q x_asnw y_asnx)
        sM :: Sing @_ (Let6989586621679118884M a_as7q x_asnw y_asnx)
        sN = applySing (singFun1 @JustSym0 SJust) sY
        sM = applySing (singFun1 @JustSym0 SJust) sX
      in
        applySing
          (singFun1
              @(LamCases_6989586621679118887Sym0 a_as7q x_asnw y_asnx)
              (\cases
                STrue -> applySing (singFun1 @MaxInternalSym0 SMaxInternal) sM
                SFalse -> applySing (singFun1 @MaxInternalSym0 SMaxInternal) sN))
          (applySing (applySing (singFun2 @(>=@#@$) (%>=)) sX) sY)
instance SOrd a_as7x => SMonoid (MaxInternal a_as7x) where
  sMempty
    = applySing (singFun1 @MaxInternalSym0 SMaxInternal) SNothing
instance SOrd a_as7y => SSemigroup (MinInternal a_as7y) where
  (%<>) (sM :: Sing m_asnS) (SMinInternal SNothing) = sM
  (%<>) (SMinInternal SNothing) (sN :: Sing n_asnT) = sN
  (%<>)
    (SMinInternal (SJust (sX :: Sing x_asnU)))
    (SMinInternal (SJust (sY :: Sing y_asnV)))
    = let
        sN :: Sing @_ (Let6989586621679118908N a_as7y x_asnU y_asnV)
        sM :: Sing @_ (Let6989586621679118908M a_as7y x_asnU y_asnV)
        sN = applySing (singFun1 @JustSym0 SJust) sY
        sM = applySing (singFun1 @JustSym0 SJust) sX
      in
        applySing
          (singFun1
              @(LamCases_6989586621679118911Sym0 a_as7y x_asnU y_asnV)
              (\cases
                STrue -> applySing (singFun1 @MinInternalSym0 SMinInternal) sM
                SFalse -> applySing (singFun1 @MinInternalSym0 SMinInternal) sN))
          (applySing (applySing (singFun2 @(<=@#@$) (%<=)) sX) sY)
instance SOrd a_as7F => SMonoid (MinInternal a_as7F) where
  sMempty
    = applySing (singFun1 @MinInternalSym0 SMinInternal) SNothing

type family LamCases_6989586621679127878_auID x6989586621679127877 (p6989586621679127873 :: (~>) a6989586621679126149 Bool) (a_69895866216791278666989586621679127874 :: t6989586621679126148 a6989586621679126149) a_6989586621679127880_auIF where
      LamCases_6989586621679127878_auID x_auIB p_auIx a_6989586621679127866_auIy 'True = Apply JustSym0 x_auIB
      LamCases_6989586621679127878_auID x_auIB p_auIx a_6989586621679127866_auIy 'False = NothingSym0
data LamCases_6989586621679127878Sym0 x6989586621679127877 (p6989586621679127873 :: (~>) a6989586621679126149 Bool) (a_69895866216791278666989586621679127874 :: t6989586621679126148 a6989586621679126149) a_69895866216791278806989586621679127881
  where
    LamCases_6989586621679127878Sym0KindInference :: SameKind (Apply (LamCases_6989586621679127878Sym0 x6989586621679127877 p6989586621679127873 a_69895866216791278666989586621679127874) arg_auIG) (LamCases_6989586621679127878Sym1 x6989586621679127877 p6989586621679127873 a_69895866216791278666989586621679127874 arg_auIG) =>
                                                      LamCases_6989586621679127878Sym0 x6989586621679127877 p6989586621679127873 a_69895866216791278666989586621679127874 a_69895866216791278806989586621679127881
type instance Apply @_ @_ (LamCases_6989586621679127878Sym0 x6989586621679127877 p6989586621679127873 a_69895866216791278666989586621679127874) a_69895866216791278806989586621679127881 = LamCases_6989586621679127878_auID x6989586621679127877 p6989586621679127873 a_69895866216791278666989586621679127874 a_69895866216791278806989586621679127881
instance SuppressUnusedWarnings (LamCases_6989586621679127878Sym0 x6989586621679127877 p6989586621679127873 a_69895866216791278666989586621679127874) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679127878Sym0KindInference ())
type family LamCases_6989586621679127878Sym1 x6989586621679127877 (p6989586621679127873 :: (~>) a6989586621679126149 Bool) (a_69895866216791278666989586621679127874 :: t6989586621679126148 a6989586621679126149) a_69895866216791278806989586621679127881 where
  LamCases_6989586621679127878Sym1 x6989586621679127877 p6989586621679127873 a_69895866216791278666989586621679127874 a_69895866216791278806989586621679127881 = LamCases_6989586621679127878_auID x6989586621679127877 p6989586621679127873 a_69895866216791278666989586621679127874 a_69895866216791278806989586621679127881
type family LamCases_6989586621679127875_auIA (p6989586621679127873 :: (~>) a6989586621679126149 Bool) (a_69895866216791278666989586621679127874 :: t6989586621679126148 a6989586621679126149) a_6989586621679127883_auII where
  LamCases_6989586621679127875_auIA p_auIx a_6989586621679127866_auIy x_auIB = Apply FirstSym0 (Apply (LamCases_6989586621679127878Sym0 x_auIB p_auIx a_6989586621679127866_auIy) (Apply p_auIx x_auIB))
data LamCases_6989586621679127875Sym0 (p6989586621679127873 :: (~>) a6989586621679126149 Bool) (a_69895866216791278666989586621679127874 :: t6989586621679126148 a6989586621679126149) a_69895866216791278836989586621679127884
  where
    LamCases_6989586621679127875Sym0KindInference :: SameKind (Apply (LamCases_6989586621679127875Sym0 p6989586621679127873 a_69895866216791278666989586621679127874) arg_auIJ) (LamCases_6989586621679127875Sym1 p6989586621679127873 a_69895866216791278666989586621679127874 arg_auIJ) =>
                                                      LamCases_6989586621679127875Sym0 p6989586621679127873 a_69895866216791278666989586621679127874 a_69895866216791278836989586621679127884
type instance Apply @_ @_ (LamCases_6989586621679127875Sym0 p6989586621679127873 a_69895866216791278666989586621679127874) a_69895866216791278836989586621679127884 = LamCases_6989586621679127875_auIA p6989586621679127873 a_69895866216791278666989586621679127874 a_69895866216791278836989586621679127884
instance SuppressUnusedWarnings (LamCases_6989586621679127875Sym0 p6989586621679127873 a_69895866216791278666989586621679127874) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679127875Sym0KindInference ())
type family LamCases_6989586621679127875Sym1 (p6989586621679127873 :: (~>) a6989586621679126149 Bool) (a_69895866216791278666989586621679127874 :: t6989586621679126148 a6989586621679126149) a_69895866216791278836989586621679127884 where
  LamCases_6989586621679127875Sym1 p6989586621679127873 a_69895866216791278666989586621679127874 a_69895866216791278836989586621679127884 = LamCases_6989586621679127875_auIA p6989586621679127873 a_69895866216791278666989586621679127874 a_69895866216791278836989586621679127884
type family LamCases_6989586621679127910_auJ9 x6989586621679127908 y6989586621679127909 (cmp6989586621679127902 :: (~>) a6989586621679126153 ((~>) a6989586621679126153 Ordering)) (a_69895866216791278956989586621679127903 :: t6989586621679126152 a6989586621679126153) a_6989586621679127912_auJb where
  LamCases_6989586621679127910_auJ9 x_auJ6 y_auJ7 cmp_auJ0 a_6989586621679127895_auJ1 'GT = y_auJ7
  LamCases_6989586621679127910_auJ9 x_auJ6 y_auJ7 cmp_auJ0 a_6989586621679127895_auJ1 'LT = x_auJ6
  LamCases_6989586621679127910_auJ9 x_auJ6 y_auJ7 cmp_auJ0 a_6989586621679127895_auJ1 'EQ = x_auJ6
data LamCases_6989586621679127910Sym0 x6989586621679127908 y6989586621679127909 (cmp6989586621679127902 :: (~>) a6989586621679126153 ((~>) a6989586621679126153 Ordering)) (a_69895866216791278956989586621679127903 :: t6989586621679126152 a6989586621679126153) a_69895866216791279126989586621679127913
  where
    LamCases_6989586621679127910Sym0KindInference :: SameKind (Apply (LamCases_6989586621679127910Sym0 x6989586621679127908 y6989586621679127909 cmp6989586621679127902 a_69895866216791278956989586621679127903) arg_auJc) (LamCases_6989586621679127910Sym1 x6989586621679127908 y6989586621679127909 cmp6989586621679127902 a_69895866216791278956989586621679127903 arg_auJc) =>
                                                      LamCases_6989586621679127910Sym0 x6989586621679127908 y6989586621679127909 cmp6989586621679127902 a_69895866216791278956989586621679127903 a_69895866216791279126989586621679127913
type instance Apply @_ @_ (LamCases_6989586621679127910Sym0 x6989586621679127908 y6989586621679127909 cmp6989586621679127902 a_69895866216791278956989586621679127903) a_69895866216791279126989586621679127913 = LamCases_6989586621679127910_auJ9 x6989586621679127908 y6989586621679127909 cmp6989586621679127902 a_69895866216791278956989586621679127903 a_69895866216791279126989586621679127913
instance SuppressUnusedWarnings (LamCases_6989586621679127910Sym0 x6989586621679127908 y6989586621679127909 cmp6989586621679127902 a_69895866216791278956989586621679127903) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679127910Sym0KindInference ())
type family LamCases_6989586621679127910Sym1 x6989586621679127908 y6989586621679127909 (cmp6989586621679127902 :: (~>) a6989586621679126153 ((~>) a6989586621679126153 Ordering)) (a_69895866216791278956989586621679127903 :: t6989586621679126152 a6989586621679126153) a_69895866216791279126989586621679127913 where
  LamCases_6989586621679127910Sym1 x6989586621679127908 y6989586621679127909 cmp6989586621679127902 a_69895866216791278956989586621679127903 a_69895866216791279126989586621679127913 = LamCases_6989586621679127910_auJ9 x6989586621679127908 y6989586621679127909 cmp6989586621679127902 a_69895866216791278956989586621679127903 a_69895866216791279126989586621679127913
data Let6989586621679127904Min'Sym0 (cmp6989586621679127902 :: (~>) a6989586621679126153 ((~>) a6989586621679126153 Ordering)) (a_69895866216791278956989586621679127903 :: t6989586621679126152 a6989586621679126153) a6989586621679127905
  where
    Let6989586621679127904Min'Sym0KindInference :: SameKind (Apply (Let6989586621679127904Min'Sym0 cmp6989586621679127902 a_69895866216791278956989586621679127903) arg_auJ5) (Let6989586621679127904Min'Sym1 cmp6989586621679127902 a_69895866216791278956989586621679127903 arg_auJ5) =>
                                                    Let6989586621679127904Min'Sym0 cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905
type instance Apply @_ @_ (Let6989586621679127904Min'Sym0 cmp6989586621679127902 a_69895866216791278956989586621679127903) a6989586621679127905 = Let6989586621679127904Min'Sym1 cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905
instance SuppressUnusedWarnings (Let6989586621679127904Min'Sym0 cmp6989586621679127902 a_69895866216791278956989586621679127903) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679127904Min'Sym0KindInference ())
data Let6989586621679127904Min'Sym1 (cmp6989586621679127902 :: (~>) a6989586621679126153 ((~>) a6989586621679126153 Ordering)) (a_69895866216791278956989586621679127903 :: t6989586621679126152 a6989586621679126153) a6989586621679127905 a6989586621679127906
  where
    Let6989586621679127904Min'Sym1KindInference :: SameKind (Apply (Let6989586621679127904Min'Sym1 cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905) arg_auJ5) (Let6989586621679127904Min'Sym2 cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905 arg_auJ5) =>
                                                    Let6989586621679127904Min'Sym1 cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905 a6989586621679127906
type instance Apply @_ @_ (Let6989586621679127904Min'Sym1 cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905) a6989586621679127906 = Let6989586621679127904Min' cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905 a6989586621679127906
instance SuppressUnusedWarnings (Let6989586621679127904Min'Sym1 cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679127904Min'Sym1KindInference ())
type family Let6989586621679127904Min'Sym2 (cmp6989586621679127902 :: (~>) a6989586621679126153 ((~>) a6989586621679126153 Ordering)) (a_69895866216791278956989586621679127903 :: t6989586621679126152 a6989586621679126153) a6989586621679127905 a6989586621679127906 where
  Let6989586621679127904Min'Sym2 cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905 a6989586621679127906 = Let6989586621679127904Min' cmp6989586621679127902 a_69895866216791278956989586621679127903 a6989586621679127905 a6989586621679127906
type family Let6989586621679127904Min' (cmp6989586621679127902 :: (~>) a6989586621679126153 ((~>) a6989586621679126153 Ordering)) (a_69895866216791278956989586621679127903 :: t6989586621679126152 a6989586621679126153) a_auJ3 a_auJ4 where
  Let6989586621679127904Min' cmp_auJ0 a_6989586621679127895_auJ1 x_auJ6 y_auJ7 = Apply (LamCases_6989586621679127910Sym0 x_auJ6 y_auJ7 cmp_auJ0 a_6989586621679127895_auJ1) (Apply (Apply cmp_auJ0 x_auJ6) y_auJ7)
type family LamCases_6989586621679127930_auJt x6989586621679127928 y6989586621679127929 (cmp6989586621679127922 :: (~>) a6989586621679126155 ((~>) a6989586621679126155 Ordering)) (a_69895866216791279156989586621679127923 :: t6989586621679126154 a6989586621679126155) a_6989586621679127932_auJv where
  LamCases_6989586621679127930_auJt x_auJq y_auJr cmp_auJk a_6989586621679127915_auJl 'GT = x_auJq
  LamCases_6989586621679127930_auJt x_auJq y_auJr cmp_auJk a_6989586621679127915_auJl 'LT = y_auJr
  LamCases_6989586621679127930_auJt x_auJq y_auJr cmp_auJk a_6989586621679127915_auJl 'EQ = y_auJr
data LamCases_6989586621679127930Sym0 x6989586621679127928 y6989586621679127929 (cmp6989586621679127922 :: (~>) a6989586621679126155 ((~>) a6989586621679126155 Ordering)) (a_69895866216791279156989586621679127923 :: t6989586621679126154 a6989586621679126155) a_69895866216791279326989586621679127933
  where
    LamCases_6989586621679127930Sym0KindInference :: SameKind (Apply (LamCases_6989586621679127930Sym0 x6989586621679127928 y6989586621679127929 cmp6989586621679127922 a_69895866216791279156989586621679127923) arg_auJw) (LamCases_6989586621679127930Sym1 x6989586621679127928 y6989586621679127929 cmp6989586621679127922 a_69895866216791279156989586621679127923 arg_auJw) =>
                                                      LamCases_6989586621679127930Sym0 x6989586621679127928 y6989586621679127929 cmp6989586621679127922 a_69895866216791279156989586621679127923 a_69895866216791279326989586621679127933
type instance Apply @_ @_ (LamCases_6989586621679127930Sym0 x6989586621679127928 y6989586621679127929 cmp6989586621679127922 a_69895866216791279156989586621679127923) a_69895866216791279326989586621679127933 = LamCases_6989586621679127930_auJt x6989586621679127928 y6989586621679127929 cmp6989586621679127922 a_69895866216791279156989586621679127923 a_69895866216791279326989586621679127933
instance SuppressUnusedWarnings (LamCases_6989586621679127930Sym0 x6989586621679127928 y6989586621679127929 cmp6989586621679127922 a_69895866216791279156989586621679127923) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679127930Sym0KindInference ())
type family LamCases_6989586621679127930Sym1 x6989586621679127928 y6989586621679127929 (cmp6989586621679127922 :: (~>) a6989586621679126155 ((~>) a6989586621679126155 Ordering)) (a_69895866216791279156989586621679127923 :: t6989586621679126154 a6989586621679126155) a_69895866216791279326989586621679127933 where
  LamCases_6989586621679127930Sym1 x6989586621679127928 y6989586621679127929 cmp6989586621679127922 a_69895866216791279156989586621679127923 a_69895866216791279326989586621679127933 = LamCases_6989586621679127930_auJt x6989586621679127928 y6989586621679127929 cmp6989586621679127922 a_69895866216791279156989586621679127923 a_69895866216791279326989586621679127933
data Let6989586621679127924Max'Sym0 (cmp6989586621679127922 :: (~>) a6989586621679126155 ((~>) a6989586621679126155 Ordering)) (a_69895866216791279156989586621679127923 :: t6989586621679126154 a6989586621679126155) a6989586621679127925
  where
    Let6989586621679127924Max'Sym0KindInference :: SameKind (Apply (Let6989586621679127924Max'Sym0 cmp6989586621679127922 a_69895866216791279156989586621679127923) arg_auJp) (Let6989586621679127924Max'Sym1 cmp6989586621679127922 a_69895866216791279156989586621679127923 arg_auJp) =>
                                                    Let6989586621679127924Max'Sym0 cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925
type instance Apply @_ @_ (Let6989586621679127924Max'Sym0 cmp6989586621679127922 a_69895866216791279156989586621679127923) a6989586621679127925 = Let6989586621679127924Max'Sym1 cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925
instance SuppressUnusedWarnings (Let6989586621679127924Max'Sym0 cmp6989586621679127922 a_69895866216791279156989586621679127923) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679127924Max'Sym0KindInference ())
data Let6989586621679127924Max'Sym1 (cmp6989586621679127922 :: (~>) a6989586621679126155 ((~>) a6989586621679126155 Ordering)) (a_69895866216791279156989586621679127923 :: t6989586621679126154 a6989586621679126155) a6989586621679127925 a6989586621679127926
  where
    Let6989586621679127924Max'Sym1KindInference :: SameKind (Apply (Let6989586621679127924Max'Sym1 cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925) arg_auJp) (Let6989586621679127924Max'Sym2 cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925 arg_auJp) =>
                                                    Let6989586621679127924Max'Sym1 cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925 a6989586621679127926
type instance Apply @_ @_ (Let6989586621679127924Max'Sym1 cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925) a6989586621679127926 = Let6989586621679127924Max' cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925 a6989586621679127926
instance SuppressUnusedWarnings (Let6989586621679127924Max'Sym1 cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679127924Max'Sym1KindInference ())
type family Let6989586621679127924Max'Sym2 (cmp6989586621679127922 :: (~>) a6989586621679126155 ((~>) a6989586621679126155 Ordering)) (a_69895866216791279156989586621679127923 :: t6989586621679126154 a6989586621679126155) a6989586621679127925 a6989586621679127926 where
  Let6989586621679127924Max'Sym2 cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925 a6989586621679127926 = Let6989586621679127924Max' cmp6989586621679127922 a_69895866216791279156989586621679127923 a6989586621679127925 a6989586621679127926
type family Let6989586621679127924Max' (cmp6989586621679127922 :: (~>) a6989586621679126155 ((~>) a6989586621679126155 Ordering)) (a_69895866216791279156989586621679127923 :: t6989586621679126154 a6989586621679126155) a_auJn a_auJo where
  Let6989586621679127924Max' cmp_auJk a_6989586621679127915_auJl x_auJq y_auJr = Apply (LamCases_6989586621679127930Sym0 x_auJq y_auJr cmp_auJk a_6989586621679127915_auJl) (Apply (Apply cmp_auJk x_auJq) y_auJr)
type family LamCases_6989586621679127972_auK9 (f6989586621679127970 :: (~>) a6989586621679126163 [b6989586621679126164]) (xs6989586621679127971 :: t6989586621679126162 a6989586621679126163) a_6989586621679127976_auKd a_6989586621679127978_auKf where
  LamCases_6989586621679127972_auK9 f_auK6 xs_auK7 x_auKa b_auKb = Apply (Apply (Apply FoldrSym0 (:@#@$)) b_auKb) (Apply f_auK6 x_auKa)
data LamCases_6989586621679127972Sym0 (f6989586621679127970 :: (~>) a6989586621679126163 [b6989586621679126164]) (xs6989586621679127971 :: t6989586621679126162 a6989586621679126163) a_69895866216791279766989586621679127977
  where
    LamCases_6989586621679127972Sym0KindInference :: SameKind (Apply (LamCases_6989586621679127972Sym0 f6989586621679127970 xs6989586621679127971) arg_auKg) (LamCases_6989586621679127972Sym1 f6989586621679127970 xs6989586621679127971 arg_auKg) =>
                                                      LamCases_6989586621679127972Sym0 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977
type instance Apply @_ @_ (LamCases_6989586621679127972Sym0 f6989586621679127970 xs6989586621679127971) a_69895866216791279766989586621679127977 = LamCases_6989586621679127972Sym1 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977
instance SuppressUnusedWarnings (LamCases_6989586621679127972Sym0 f6989586621679127970 xs6989586621679127971) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679127972Sym0KindInference ())
data LamCases_6989586621679127972Sym1 (f6989586621679127970 :: (~>) a6989586621679126163 [b6989586621679126164]) (xs6989586621679127971 :: t6989586621679126162 a6989586621679126163) a_69895866216791279766989586621679127977 a_69895866216791279786989586621679127979
  where
    LamCases_6989586621679127972Sym1KindInference :: SameKind (Apply (LamCases_6989586621679127972Sym1 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977) arg_auKg) (LamCases_6989586621679127972Sym2 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977 arg_auKg) =>
                                                      LamCases_6989586621679127972Sym1 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977 a_69895866216791279786989586621679127979
type instance Apply @_ @_ (LamCases_6989586621679127972Sym1 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977) a_69895866216791279786989586621679127979 = LamCases_6989586621679127972_auK9 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977 a_69895866216791279786989586621679127979
instance SuppressUnusedWarnings (LamCases_6989586621679127972Sym1 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679127972Sym1KindInference ())
type family LamCases_6989586621679127972Sym2 (f6989586621679127970 :: (~>) a6989586621679126163 [b6989586621679126164]) (xs6989586621679127971 :: t6989586621679126162 a6989586621679126163) a_69895866216791279766989586621679127977 a_69895866216791279786989586621679127979 where
  LamCases_6989586621679127972Sym2 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977 a_69895866216791279786989586621679127979 = LamCases_6989586621679127972_auK9 f6989586621679127970 xs6989586621679127971 a_69895866216791279766989586621679127977 a_69895866216791279786989586621679127979
type family LamCases_6989586621679127985_auKm (xs6989586621679127984 :: t6989586621679126165 [a6989586621679126166]) a_6989586621679127989_auKq a_6989586621679127991_auKs where
  LamCases_6989586621679127985_auKm xs_auKk x_auKn y_auKo = Apply (Apply (Apply FoldrSym0 (:@#@$)) y_auKo) x_auKn
data LamCases_6989586621679127985Sym0 (xs6989586621679127984 :: t6989586621679126165 [a6989586621679126166]) a_69895866216791279896989586621679127990
  where
    LamCases_6989586621679127985Sym0KindInference :: SameKind (Apply (LamCases_6989586621679127985Sym0 xs6989586621679127984) arg_auKt) (LamCases_6989586621679127985Sym1 xs6989586621679127984 arg_auKt) =>
                                                      LamCases_6989586621679127985Sym0 xs6989586621679127984 a_69895866216791279896989586621679127990
type instance Apply @_ @_ (LamCases_6989586621679127985Sym0 xs6989586621679127984) a_69895866216791279896989586621679127990 = LamCases_6989586621679127985Sym1 xs6989586621679127984 a_69895866216791279896989586621679127990
instance SuppressUnusedWarnings (LamCases_6989586621679127985Sym0 xs6989586621679127984) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679127985Sym0KindInference ())
data LamCases_6989586621679127985Sym1 (xs6989586621679127984 :: t6989586621679126165 [a6989586621679126166]) a_69895866216791279896989586621679127990 a_69895866216791279916989586621679127992
  where
    LamCases_6989586621679127985Sym1KindInference :: SameKind (Apply (LamCases_6989586621679127985Sym1 xs6989586621679127984 a_69895866216791279896989586621679127990) arg_auKt) (LamCases_6989586621679127985Sym2 xs6989586621679127984 a_69895866216791279896989586621679127990 arg_auKt) =>
                                                      LamCases_6989586621679127985Sym1 xs6989586621679127984 a_69895866216791279896989586621679127990 a_69895866216791279916989586621679127992
type instance Apply @_ @_ (LamCases_6989586621679127985Sym1 xs6989586621679127984 a_69895866216791279896989586621679127990) a_69895866216791279916989586621679127992 = LamCases_6989586621679127985_auKm xs6989586621679127984 a_69895866216791279896989586621679127990 a_69895866216791279916989586621679127992
instance SuppressUnusedWarnings (LamCases_6989586621679127985Sym1 xs6989586621679127984 a_69895866216791279896989586621679127990) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679127985Sym1KindInference ())
type family LamCases_6989586621679127985Sym2 (xs6989586621679127984 :: t6989586621679126165 [a6989586621679126166]) a_69895866216791279896989586621679127990 a_69895866216791279916989586621679127992 where
  LamCases_6989586621679127985Sym2 xs6989586621679127984 a_69895866216791279896989586621679127990 a_69895866216791279916989586621679127992 = LamCases_6989586621679127985_auKm xs6989586621679127984 a_69895866216791279896989586621679127990 a_69895866216791279916989586621679127992
data Let6989586621679128068F'Sym0 (f6989586621679128065 :: (~>) b6989586621679126197 ((~>) a6989586621679126198 (m6989586621679126196 b6989586621679126197))) (z06989586621679128066 :: b6989586621679126197) (xs6989586621679128067 :: t6989586621679126195 a6989586621679126198) a6989586621679128069
  where
    Let6989586621679128068F'Sym0KindInference :: SameKind (Apply (Let6989586621679128068F'Sym0 f6989586621679128065 z06989586621679128066 xs6989586621679128067) arg_auLK) (Let6989586621679128068F'Sym1 f6989586621679128065 z06989586621679128066 xs6989586621679128067 arg_auLK) =>
                                                  Let6989586621679128068F'Sym0 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069
type instance Apply @_ @_ (Let6989586621679128068F'Sym0 f6989586621679128065 z06989586621679128066 xs6989586621679128067) a6989586621679128069 = Let6989586621679128068F'Sym1 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069
instance SuppressUnusedWarnings (Let6989586621679128068F'Sym0 f6989586621679128065 z06989586621679128066 xs6989586621679128067) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128068F'Sym0KindInference ())
data Let6989586621679128068F'Sym1 (f6989586621679128065 :: (~>) b6989586621679126197 ((~>) a6989586621679126198 (m6989586621679126196 b6989586621679126197))) (z06989586621679128066 :: b6989586621679126197) (xs6989586621679128067 :: t6989586621679126195 a6989586621679126198) a6989586621679128069 a6989586621679128070
  where
    Let6989586621679128068F'Sym1KindInference :: SameKind (Apply (Let6989586621679128068F'Sym1 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069) arg_auLK) (Let6989586621679128068F'Sym2 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 arg_auLK) =>
                                                  Let6989586621679128068F'Sym1 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070
type instance Apply @_ @_ (Let6989586621679128068F'Sym1 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069) a6989586621679128070 = Let6989586621679128068F'Sym2 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070
instance SuppressUnusedWarnings (Let6989586621679128068F'Sym1 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128068F'Sym1KindInference ())
data Let6989586621679128068F'Sym2 (f6989586621679128065 :: (~>) b6989586621679126197 ((~>) a6989586621679126198 (m6989586621679126196 b6989586621679126197))) (z06989586621679128066 :: b6989586621679126197) (xs6989586621679128067 :: t6989586621679126195 a6989586621679126198) a6989586621679128069 a6989586621679128070 a6989586621679128071
  where
    Let6989586621679128068F'Sym2KindInference :: SameKind (Apply (Let6989586621679128068F'Sym2 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070) arg_auLK) (Let6989586621679128068F'Sym3 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070 arg_auLK) =>
                                                  Let6989586621679128068F'Sym2 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070 a6989586621679128071
type instance Apply @_ @_ (Let6989586621679128068F'Sym2 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070) a6989586621679128071 = Let6989586621679128068F' f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070 a6989586621679128071
instance SuppressUnusedWarnings (Let6989586621679128068F'Sym2 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128068F'Sym2KindInference ())
type family Let6989586621679128068F'Sym3 (f6989586621679128065 :: (~>) b6989586621679126197 ((~>) a6989586621679126198 (m6989586621679126196 b6989586621679126197))) (z06989586621679128066 :: b6989586621679126197) (xs6989586621679128067 :: t6989586621679126195 a6989586621679126198) a6989586621679128069 a6989586621679128070 a6989586621679128071 where
  Let6989586621679128068F'Sym3 f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070 a6989586621679128071 = Let6989586621679128068F' f6989586621679128065 z06989586621679128066 xs6989586621679128067 a6989586621679128069 a6989586621679128070 a6989586621679128071
type family Let6989586621679128068F' (f6989586621679128065 :: (~>) b6989586621679126197 ((~>) a6989586621679126198 (m6989586621679126196 b6989586621679126197))) (z06989586621679128066 :: b6989586621679126197) (xs6989586621679128067 :: t6989586621679126195 a6989586621679126198) a_auLH a_auLI a_auLJ where
  Let6989586621679128068F' f_auLD z0_auLE xs_auLF x_auLL k_auLM z_auLN = Apply (Apply (>>=@#@$) (Apply (Apply f_auLD z_auLN) x_auLL)) k_auLM
data Let6989586621679128086F'Sym0 (f6989586621679128083 :: (~>) a6989586621679126201 ((~>) b6989586621679126202 (m6989586621679126200 b6989586621679126202))) (z06989586621679128084 :: b6989586621679126202) (xs6989586621679128085 :: t6989586621679126199 a6989586621679126201) a6989586621679128087
  where
    Let6989586621679128086F'Sym0KindInference :: SameKind (Apply (Let6989586621679128086F'Sym0 f6989586621679128083 z06989586621679128084 xs6989586621679128085) arg_auM2) (Let6989586621679128086F'Sym1 f6989586621679128083 z06989586621679128084 xs6989586621679128085 arg_auM2) =>
                                                  Let6989586621679128086F'Sym0 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087
type instance Apply @_ @_ (Let6989586621679128086F'Sym0 f6989586621679128083 z06989586621679128084 xs6989586621679128085) a6989586621679128087 = Let6989586621679128086F'Sym1 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087
instance SuppressUnusedWarnings (Let6989586621679128086F'Sym0 f6989586621679128083 z06989586621679128084 xs6989586621679128085) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128086F'Sym0KindInference ())
data Let6989586621679128086F'Sym1 (f6989586621679128083 :: (~>) a6989586621679126201 ((~>) b6989586621679126202 (m6989586621679126200 b6989586621679126202))) (z06989586621679128084 :: b6989586621679126202) (xs6989586621679128085 :: t6989586621679126199 a6989586621679126201) a6989586621679128087 a6989586621679128088
  where
    Let6989586621679128086F'Sym1KindInference :: SameKind (Apply (Let6989586621679128086F'Sym1 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087) arg_auM2) (Let6989586621679128086F'Sym2 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 arg_auM2) =>
                                                  Let6989586621679128086F'Sym1 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088
type instance Apply @_ @_ (Let6989586621679128086F'Sym1 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087) a6989586621679128088 = Let6989586621679128086F'Sym2 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088
instance SuppressUnusedWarnings (Let6989586621679128086F'Sym1 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128086F'Sym1KindInference ())
data Let6989586621679128086F'Sym2 (f6989586621679128083 :: (~>) a6989586621679126201 ((~>) b6989586621679126202 (m6989586621679126200 b6989586621679126202))) (z06989586621679128084 :: b6989586621679126202) (xs6989586621679128085 :: t6989586621679126199 a6989586621679126201) a6989586621679128087 a6989586621679128088 a6989586621679128089
  where
    Let6989586621679128086F'Sym2KindInference :: SameKind (Apply (Let6989586621679128086F'Sym2 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088) arg_auM2) (Let6989586621679128086F'Sym3 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088 arg_auM2) =>
                                                  Let6989586621679128086F'Sym2 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088 a6989586621679128089
type instance Apply @_ @_ (Let6989586621679128086F'Sym2 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088) a6989586621679128089 = Let6989586621679128086F' f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088 a6989586621679128089
instance SuppressUnusedWarnings (Let6989586621679128086F'Sym2 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128086F'Sym2KindInference ())
type family Let6989586621679128086F'Sym3 (f6989586621679128083 :: (~>) a6989586621679126201 ((~>) b6989586621679126202 (m6989586621679126200 b6989586621679126202))) (z06989586621679128084 :: b6989586621679126202) (xs6989586621679128085 :: t6989586621679126199 a6989586621679126201) a6989586621679128087 a6989586621679128088 a6989586621679128089 where
  Let6989586621679128086F'Sym3 f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088 a6989586621679128089 = Let6989586621679128086F' f6989586621679128083 z06989586621679128084 xs6989586621679128085 a6989586621679128087 a6989586621679128088 a6989586621679128089
type family Let6989586621679128086F' (f6989586621679128083 :: (~>) a6989586621679126201 ((~>) b6989586621679126202 (m6989586621679126200 b6989586621679126202))) (z06989586621679128084 :: b6989586621679126202) (xs6989586621679128085 :: t6989586621679126199 a6989586621679126201) a_auLZ a_auM0 a_auM1 where
  Let6989586621679128086F' f_auLV z0_auLW xs_auLX k_auM3 x_auM4 z_auM5 = Apply (Apply (>>=@#@$) (Apply (Apply f_auLV x_auM4) z_auM5)) k_auM3
type FindSym0 :: (~>) ((~>) a_augJ Bool) ((~>) (t_augI a_augJ) (Maybe a_augJ))
data FindSym0 :: (~>) ((~>) a_augJ Bool) ((~>) (t_augI a_augJ) (Maybe a_augJ))
  where
    FindSym0KindInference :: SameKind (Apply FindSym0 arg_auIu) (FindSym1 arg_auIu) =>
                              FindSym0 a6989586621679127871
type instance Apply @((~>) a_augJ Bool) @((~>) (t_augI a_augJ) (Maybe a_augJ)) FindSym0 a6989586621679127871 = FindSym1 a6989586621679127871
instance SuppressUnusedWarnings FindSym0 where
  suppressUnusedWarnings = snd ((,) FindSym0KindInference ())
type FindSym1 :: (~>) a_augJ Bool
                  -> (~>) (t_augI a_augJ) (Maybe a_augJ)
data FindSym1 (a6989586621679127871 :: (~>) a_augJ Bool) :: (~>) (t_augI a_augJ) (Maybe a_augJ)
  where
    FindSym1KindInference :: SameKind (Apply (FindSym1 a6989586621679127871) arg_auIu) (FindSym2 a6989586621679127871 arg_auIu) =>
                              FindSym1 a6989586621679127871 a6989586621679127872
type instance Apply @(t_augI a_augJ) @(Maybe a_augJ) (FindSym1 a6989586621679127871) a6989586621679127872 = Find a6989586621679127871 a6989586621679127872
instance SuppressUnusedWarnings (FindSym1 a6989586621679127871) where
  suppressUnusedWarnings = snd ((,) FindSym1KindInference ())
type FindSym2 :: (~>) a_augJ Bool -> t_augI a_augJ -> Maybe a_augJ
type family FindSym2 @a_augJ @t_augI (a6989586621679127871 :: (~>) a_augJ Bool) (a6989586621679127872 :: t_augI a_augJ) :: Maybe a_augJ where
  FindSym2 a6989586621679127871 a6989586621679127872 = Find a6989586621679127871 a6989586621679127872
type NotElemSym0 :: (~>) a_augL ((~>) (t_augK a_augL) Bool)
data NotElemSym0 :: (~>) a_augL ((~>) (t_augK a_augL) Bool)
  where
    NotElemSym0KindInference :: SameKind (Apply NotElemSym0 arg_auIO) (NotElemSym1 arg_auIO) =>
                                NotElemSym0 a6989586621679127891
type instance Apply @a_augL @((~>) (t_augK a_augL) Bool) NotElemSym0 a6989586621679127891 = NotElemSym1 a6989586621679127891
instance SuppressUnusedWarnings NotElemSym0 where
  suppressUnusedWarnings = snd ((,) NotElemSym0KindInference ())
type NotElemSym1 :: a_augL -> (~>) (t_augK a_augL) Bool
data NotElemSym1 (a6989586621679127891 :: a_augL) :: (~>) (t_augK a_augL) Bool
  where
    NotElemSym1KindInference :: SameKind (Apply (NotElemSym1 a6989586621679127891) arg_auIO) (NotElemSym2 a6989586621679127891 arg_auIO) =>
                                NotElemSym1 a6989586621679127891 a6989586621679127892
type instance Apply @(t_augK a_augL) @Bool (NotElemSym1 a6989586621679127891) a6989586621679127892 = NotElem a6989586621679127891 a6989586621679127892
instance SuppressUnusedWarnings (NotElemSym1 a6989586621679127891) where
  suppressUnusedWarnings = snd ((,) NotElemSym1KindInference ())
type NotElemSym2 :: a_augL -> t_augK a_augL -> Bool
type family NotElemSym2 @a_augL @t_augK (a6989586621679127891 :: a_augL) (a6989586621679127892 :: t_augK a_augL) :: Bool where
  NotElemSym2 a6989586621679127891 a6989586621679127892 = NotElem a6989586621679127891 a6989586621679127892
type MinimumBySym0 :: (~>) ((~>) a_augN ((~>) a_augN Ordering)) ((~>) (t_augM a_augN) a_augN)
data MinimumBySym0 :: (~>) ((~>) a_augN ((~>) a_augN Ordering)) ((~>) (t_augM a_augN) a_augN)
  where
    MinimumBySym0KindInference :: SameKind (Apply MinimumBySym0 arg_auIX) (MinimumBySym1 arg_auIX) =>
                                  MinimumBySym0 a6989586621679127900
type instance Apply @((~>) a_augN ((~>) a_augN Ordering)) @((~>) (t_augM a_augN) a_augN) MinimumBySym0 a6989586621679127900 = MinimumBySym1 a6989586621679127900
instance SuppressUnusedWarnings MinimumBySym0 where
  suppressUnusedWarnings = snd ((,) MinimumBySym0KindInference ())
type MinimumBySym1 :: (~>) a_augN ((~>) a_augN Ordering)
                      -> (~>) (t_augM a_augN) a_augN
data MinimumBySym1 (a6989586621679127900 :: (~>) a_augN ((~>) a_augN Ordering)) :: (~>) (t_augM a_augN) a_augN
  where
    MinimumBySym1KindInference :: SameKind (Apply (MinimumBySym1 a6989586621679127900) arg_auIX) (MinimumBySym2 a6989586621679127900 arg_auIX) =>
                                  MinimumBySym1 a6989586621679127900 a6989586621679127901
type instance Apply @(t_augM a_augN) @a_augN (MinimumBySym1 a6989586621679127900) a6989586621679127901 = MinimumBy a6989586621679127900 a6989586621679127901
instance SuppressUnusedWarnings (MinimumBySym1 a6989586621679127900) where
  suppressUnusedWarnings = snd ((,) MinimumBySym1KindInference ())
type MinimumBySym2 :: (~>) a_augN ((~>) a_augN Ordering)
                      -> t_augM a_augN -> a_augN
type family MinimumBySym2 @a_augN @t_augM (a6989586621679127900 :: (~>) a_augN ((~>) a_augN Ordering)) (a6989586621679127901 :: t_augM a_augN) :: a_augN where
  MinimumBySym2 a6989586621679127900 a6989586621679127901 = MinimumBy a6989586621679127900 a6989586621679127901
type MaximumBySym0 :: (~>) ((~>) a_augP ((~>) a_augP Ordering)) ((~>) (t_augO a_augP) a_augP)
data MaximumBySym0 :: (~>) ((~>) a_augP ((~>) a_augP Ordering)) ((~>) (t_augO a_augP) a_augP)
  where
    MaximumBySym0KindInference :: SameKind (Apply MaximumBySym0 arg_auJh) (MaximumBySym1 arg_auJh) =>
                                  MaximumBySym0 a6989586621679127920
type instance Apply @((~>) a_augP ((~>) a_augP Ordering)) @((~>) (t_augO a_augP) a_augP) MaximumBySym0 a6989586621679127920 = MaximumBySym1 a6989586621679127920
instance SuppressUnusedWarnings MaximumBySym0 where
  suppressUnusedWarnings = snd ((,) MaximumBySym0KindInference ())
type MaximumBySym1 :: (~>) a_augP ((~>) a_augP Ordering)
                      -> (~>) (t_augO a_augP) a_augP
data MaximumBySym1 (a6989586621679127920 :: (~>) a_augP ((~>) a_augP Ordering)) :: (~>) (t_augO a_augP) a_augP
  where
    MaximumBySym1KindInference :: SameKind (Apply (MaximumBySym1 a6989586621679127920) arg_auJh) (MaximumBySym2 a6989586621679127920 arg_auJh) =>
                                  MaximumBySym1 a6989586621679127920 a6989586621679127921
type instance Apply @(t_augO a_augP) @a_augP (MaximumBySym1 a6989586621679127920) a6989586621679127921 = MaximumBy a6989586621679127920 a6989586621679127921
instance SuppressUnusedWarnings (MaximumBySym1 a6989586621679127920) where
  suppressUnusedWarnings = snd ((,) MaximumBySym1KindInference ())
type MaximumBySym2 :: (~>) a_augP ((~>) a_augP Ordering)
                      -> t_augO a_augP -> a_augP
type family MaximumBySym2 @a_augP @t_augO (a6989586621679127920 :: (~>) a_augP ((~>) a_augP Ordering)) (a6989586621679127921 :: t_augO a_augP) :: a_augP where
  MaximumBySym2 a6989586621679127920 a6989586621679127921 = MaximumBy a6989586621679127920 a6989586621679127921
type AllSym0 :: (~>) ((~>) a_augR Bool) ((~>) (t_augQ a_augR) Bool)
data AllSym0 :: (~>) ((~>) a_augR Bool) ((~>) (t_augQ a_augR) Bool)
  where
    AllSym0KindInference :: SameKind (Apply AllSym0 arg_auJB) (AllSym1 arg_auJB) =>
                            AllSym0 a6989586621679127940
type instance Apply @((~>) a_augR Bool) @((~>) (t_augQ a_augR) Bool) AllSym0 a6989586621679127940 = AllSym1 a6989586621679127940
instance SuppressUnusedWarnings AllSym0 where
  suppressUnusedWarnings = snd ((,) AllSym0KindInference ())
type AllSym1 :: (~>) a_augR Bool -> (~>) (t_augQ a_augR) Bool
data AllSym1 (a6989586621679127940 :: (~>) a_augR Bool) :: (~>) (t_augQ a_augR) Bool
  where
    AllSym1KindInference :: SameKind (Apply (AllSym1 a6989586621679127940) arg_auJB) (AllSym2 a6989586621679127940 arg_auJB) =>
                            AllSym1 a6989586621679127940 a6989586621679127941
type instance Apply @(t_augQ a_augR) @Bool (AllSym1 a6989586621679127940) a6989586621679127941 = All a6989586621679127940 a6989586621679127941
instance SuppressUnusedWarnings (AllSym1 a6989586621679127940) where
  suppressUnusedWarnings = snd ((,) AllSym1KindInference ())
type AllSym2 :: (~>) a_augR Bool -> t_augQ a_augR -> Bool
type family AllSym2 @a_augR @t_augQ (a6989586621679127940 :: (~>) a_augR Bool) (a6989586621679127941 :: t_augQ a_augR) :: Bool where
  AllSym2 a6989586621679127940 a6989586621679127941 = All a6989586621679127940 a6989586621679127941
type AnySym0 :: (~>) ((~>) a_augT Bool) ((~>) (t_augS a_augT) Bool)
data AnySym0 :: (~>) ((~>) a_augT Bool) ((~>) (t_augS a_augT) Bool)
  where
    AnySym0KindInference :: SameKind (Apply AnySym0 arg_auJK) (AnySym1 arg_auJK) =>
                            AnySym0 a6989586621679127949
type instance Apply @((~>) a_augT Bool) @((~>) (t_augS a_augT) Bool) AnySym0 a6989586621679127949 = AnySym1 a6989586621679127949
instance SuppressUnusedWarnings AnySym0 where
  suppressUnusedWarnings = snd ((,) AnySym0KindInference ())
type AnySym1 :: (~>) a_augT Bool -> (~>) (t_augS a_augT) Bool
data AnySym1 (a6989586621679127949 :: (~>) a_augT Bool) :: (~>) (t_augS a_augT) Bool
  where
    AnySym1KindInference :: SameKind (Apply (AnySym1 a6989586621679127949) arg_auJK) (AnySym2 a6989586621679127949 arg_auJK) =>
                            AnySym1 a6989586621679127949 a6989586621679127950
type instance Apply @(t_augS a_augT) @Bool (AnySym1 a6989586621679127949) a6989586621679127950 = Any a6989586621679127949 a6989586621679127950
instance SuppressUnusedWarnings (AnySym1 a6989586621679127949) where
  suppressUnusedWarnings = snd ((,) AnySym1KindInference ())
type AnySym2 :: (~>) a_augT Bool -> t_augS a_augT -> Bool
type family AnySym2 @a_augT @t_augS (a6989586621679127949 :: (~>) a_augT Bool) (a6989586621679127950 :: t_augS a_augT) :: Bool where
  AnySym2 a6989586621679127949 a6989586621679127950 = Any a6989586621679127949 a6989586621679127950
type OrSym0 :: (~>) (t_augU Bool) Bool
data OrSym0 :: (~>) (t_augU Bool) Bool
  where
    OrSym0KindInference :: SameKind (Apply OrSym0 arg_auJS) (OrSym1 arg_auJS) =>
                            OrSym0 a6989586621679127957
type instance Apply @(t_augU Bool) @Bool OrSym0 a6989586621679127957 = Or a6989586621679127957
instance SuppressUnusedWarnings OrSym0 where
  suppressUnusedWarnings = snd ((,) OrSym0KindInference ())
type OrSym1 :: t_augU Bool -> Bool
type family OrSym1 @t_augU (a6989586621679127957 :: t_augU Bool) :: Bool where
  OrSym1 a6989586621679127957 = Or a6989586621679127957
type AndSym0 :: (~>) (t_augV Bool) Bool
data AndSym0 :: (~>) (t_augV Bool) Bool
  where
    AndSym0KindInference :: SameKind (Apply AndSym0 arg_auJY) (AndSym1 arg_auJY) =>
                            AndSym0 a6989586621679127963
type instance Apply @(t_augV Bool) @Bool AndSym0 a6989586621679127963 = And a6989586621679127963
instance SuppressUnusedWarnings AndSym0 where
  suppressUnusedWarnings = snd ((,) AndSym0KindInference ())
type AndSym1 :: t_augV Bool -> Bool
type family AndSym1 @t_augV (a6989586621679127963 :: t_augV Bool) :: Bool where
  AndSym1 a6989586621679127963 = And a6989586621679127963
type ConcatMapSym0 :: (~>) ((~>) a_augX [b_augY]) ((~>) (t_augW a_augX) [b_augY])
data ConcatMapSym0 :: (~>) ((~>) a_augX [b_augY]) ((~>) (t_augW a_augX) [b_augY])
  where
    ConcatMapSym0KindInference :: SameKind (Apply ConcatMapSym0 arg_auK3) (ConcatMapSym1 arg_auK3) =>
                                  ConcatMapSym0 a6989586621679127968
type instance Apply @((~>) a_augX [b_augY]) @((~>) (t_augW a_augX) [b_augY]) ConcatMapSym0 a6989586621679127968 = ConcatMapSym1 a6989586621679127968
instance SuppressUnusedWarnings ConcatMapSym0 where
  suppressUnusedWarnings = snd ((,) ConcatMapSym0KindInference ())
type ConcatMapSym1 :: (~>) a_augX [b_augY]
                      -> (~>) (t_augW a_augX) [b_augY]
data ConcatMapSym1 (a6989586621679127968 :: (~>) a_augX [b_augY]) :: (~>) (t_augW a_augX) [b_augY]
  where
    ConcatMapSym1KindInference :: SameKind (Apply (ConcatMapSym1 a6989586621679127968) arg_auK3) (ConcatMapSym2 a6989586621679127968 arg_auK3) =>
                                  ConcatMapSym1 a6989586621679127968 a6989586621679127969
type instance Apply @(t_augW a_augX) @[b_augY] (ConcatMapSym1 a6989586621679127968) a6989586621679127969 = ConcatMap a6989586621679127968 a6989586621679127969
instance SuppressUnusedWarnings (ConcatMapSym1 a6989586621679127968) where
  suppressUnusedWarnings = snd ((,) ConcatMapSym1KindInference ())
type ConcatMapSym2 :: (~>) a_augX [b_augY]
                      -> t_augW a_augX -> [b_augY]
type family ConcatMapSym2 @a_augX @b_augY @t_augW (a6989586621679127968 :: (~>) a_augX [b_augY]) (a6989586621679127969 :: t_augW a_augX) :: [b_augY] where
  ConcatMapSym2 a6989586621679127968 a6989586621679127969 = ConcatMap a6989586621679127968 a6989586621679127969
type ConcatSym0 :: (~>) (t_augZ [a_auh0]) [a_auh0]
data ConcatSym0 :: (~>) (t_augZ [a_auh0]) [a_auh0]
  where
    ConcatSym0KindInference :: SameKind (Apply ConcatSym0 arg_auKi) (ConcatSym1 arg_auKi) =>
                                ConcatSym0 a6989586621679127983
type instance Apply @(t_augZ [a_auh0]) @[a_auh0] ConcatSym0 a6989586621679127983 = Concat a6989586621679127983
instance SuppressUnusedWarnings ConcatSym0 where
  suppressUnusedWarnings = snd ((,) ConcatSym0KindInference ())
type ConcatSym1 :: t_augZ [a_auh0] -> [a_auh0]
type family ConcatSym1 @t_augZ @a_auh0 (a6989586621679127983 :: t_augZ [a_auh0]) :: [a_auh0] where
  ConcatSym1 a6989586621679127983 = Concat a6989586621679127983
type MsumSym0 :: forall t_auh1
                        (m_auh2 :: Type -> Type)
                        a_auh3. (~>) (t_auh1 (m_auh2 a_auh3)) (m_auh2 a_auh3)
data MsumSym0 :: (~>) (t_auh1 (m_auh2 a_auh3)) (m_auh2 a_auh3)
  where
    MsumSym0KindInference :: SameKind (Apply MsumSym0 arg_auKx) (MsumSym1 arg_auKx) =>
                              MsumSym0 a6989586621679127998
type instance Apply @(t_auh1 (m_auh2 a_auh3)) @(m_auh2 a_auh3) MsumSym0 a6989586621679127998 = Msum a6989586621679127998
instance SuppressUnusedWarnings MsumSym0 where
  suppressUnusedWarnings = snd ((,) MsumSym0KindInference ())
type MsumSym1 :: forall t_auh1
                        (m_auh2 :: Type -> Type)
                        a_auh3. t_auh1 (m_auh2 a_auh3) -> m_auh2 a_auh3
type family MsumSym1 @t_auh1 @(m_auh2 :: Type
                                          -> Type) @a_auh3 (a6989586621679127998 :: t_auh1 (m_auh2 a_auh3)) :: m_auh2 a_auh3 where
  MsumSym1 a6989586621679127998 = Msum a6989586621679127998
type AsumSym0 :: forall t_auh4
                        (f_auh5 :: Type -> Type)
                        a_auh6. (~>) (t_auh4 (f_auh5 a_auh6)) (f_auh5 a_auh6)
data AsumSym0 :: (~>) (t_auh4 (f_auh5 a_auh6)) (f_auh5 a_auh6)
  where
    AsumSym0KindInference :: SameKind (Apply AsumSym0 arg_auKD) (AsumSym1 arg_auKD) =>
                              AsumSym0 a6989586621679128004
type instance Apply @(t_auh4 (f_auh5 a_auh6)) @(f_auh5 a_auh6) AsumSym0 a6989586621679128004 = Asum a6989586621679128004
instance SuppressUnusedWarnings AsumSym0 where
  suppressUnusedWarnings = snd ((,) AsumSym0KindInference ())
type AsumSym1 :: forall t_auh4
                        (f_auh5 :: Type -> Type)
                        a_auh6. t_auh4 (f_auh5 a_auh6) -> f_auh5 a_auh6
type family AsumSym1 @t_auh4 @(f_auh5 :: Type
                                          -> Type) @a_auh6 (a6989586621679128004 :: t_auh4 (f_auh5 a_auh6)) :: f_auh5 a_auh6 where
  AsumSym1 a6989586621679128004 = Asum a6989586621679128004
type Sequence_Sym0 :: (~>) (t_auh7 (m_auh8 a_auh9)) (m_auh8 ())
data Sequence_Sym0 :: (~>) (t_auh7 (m_auh8 a_auh9)) (m_auh8 ())
  where
    Sequence_Sym0KindInference :: SameKind (Apply Sequence_Sym0 arg_auKJ) (Sequence_Sym1 arg_auKJ) =>
                                  Sequence_Sym0 a6989586621679128010
type instance Apply @(t_auh7 (m_auh8 a_auh9)) @(m_auh8 ()) Sequence_Sym0 a6989586621679128010 = Sequence_ a6989586621679128010
instance SuppressUnusedWarnings Sequence_Sym0 where
  suppressUnusedWarnings = snd ((,) Sequence_Sym0KindInference ())
type Sequence_Sym1 :: t_auh7 (m_auh8 a_auh9) -> m_auh8 ()
type family Sequence_Sym1 @t_auh7 @m_auh8 @a_auh9 (a6989586621679128010 :: t_auh7 (m_auh8 a_auh9)) :: m_auh8 () where
  Sequence_Sym1 a6989586621679128010 = Sequence_ a6989586621679128010
type SequenceA_Sym0 :: (~>) (t_auha (f_auhb a_auhc)) (f_auhb ())
data SequenceA_Sym0 :: (~>) (t_auha (f_auhb a_auhc)) (f_auhb ())
  where
    SequenceA_Sym0KindInference :: SameKind (Apply SequenceA_Sym0 arg_auKP) (SequenceA_Sym1 arg_auKP) =>
                                    SequenceA_Sym0 a6989586621679128016
type instance Apply @(t_auha (f_auhb a_auhc)) @(f_auhb ()) SequenceA_Sym0 a6989586621679128016 = SequenceA_ a6989586621679128016
instance SuppressUnusedWarnings SequenceA_Sym0 where
  suppressUnusedWarnings = snd ((,) SequenceA_Sym0KindInference ())
type SequenceA_Sym1 :: t_auha (f_auhb a_auhc) -> f_auhb ()
type family SequenceA_Sym1 @t_auha @f_auhb @a_auhc (a6989586621679128016 :: t_auha (f_auhb a_auhc)) :: f_auhb () where
  SequenceA_Sym1 a6989586621679128016 = SequenceA_ a6989586621679128016
type ForM_Sym0 :: (~>) (t_auhd a_auhf) ((~>) ((~>) a_auhf (m_auhe b_auhg)) (m_auhe ()))
data ForM_Sym0 :: (~>) (t_auhd a_auhf) ((~>) ((~>) a_auhf (m_auhe b_auhg)) (m_auhe ()))
  where
    ForM_Sym0KindInference :: SameKind (Apply ForM_Sym0 arg_auKY) (ForM_Sym1 arg_auKY) =>
                              ForM_Sym0 a6989586621679128025
type instance Apply @(t_auhd a_auhf) @((~>) ((~>) a_auhf (m_auhe b_auhg)) (m_auhe ())) ForM_Sym0 a6989586621679128025 = ForM_Sym1 a6989586621679128025
instance SuppressUnusedWarnings ForM_Sym0 where
  suppressUnusedWarnings = snd ((,) ForM_Sym0KindInference ())
type ForM_Sym1 :: t_auhd a_auhf
                  -> (~>) ((~>) a_auhf (m_auhe b_auhg)) (m_auhe ())
data ForM_Sym1 (a6989586621679128025 :: t_auhd a_auhf) :: (~>) ((~>) a_auhf (m_auhe b_auhg)) (m_auhe ())
  where
    ForM_Sym1KindInference :: SameKind (Apply (ForM_Sym1 a6989586621679128025) arg_auKY) (ForM_Sym2 a6989586621679128025 arg_auKY) =>
                              ForM_Sym1 a6989586621679128025 a6989586621679128026
type instance Apply @((~>) a_auhf (m_auhe b_auhg)) @(m_auhe ()) (ForM_Sym1 a6989586621679128025) a6989586621679128026 = ForM_ a6989586621679128025 a6989586621679128026
instance SuppressUnusedWarnings (ForM_Sym1 a6989586621679128025) where
  suppressUnusedWarnings = snd ((,) ForM_Sym1KindInference ())
type ForM_Sym2 :: t_auhd a_auhf
                  -> (~>) a_auhf (m_auhe b_auhg) -> m_auhe ()
type family ForM_Sym2 @t_auhd @a_auhf @m_auhe @b_auhg (a6989586621679128025 :: t_auhd a_auhf) (a6989586621679128026 :: (~>) a_auhf (m_auhe b_auhg)) :: m_auhe () where
  ForM_Sym2 a6989586621679128025 a6989586621679128026 = ForM_ a6989586621679128025 a6989586621679128026
type MapM_Sym0 :: (~>) ((~>) a_auhj (m_auhi b_auhk)) ((~>) (t_auhh a_auhj) (m_auhi ()))
data MapM_Sym0 :: (~>) ((~>) a_auhj (m_auhi b_auhk)) ((~>) (t_auhh a_auhj) (m_auhi ()))
  where
    MapM_Sym0KindInference :: SameKind (Apply MapM_Sym0 arg_auL7) (MapM_Sym1 arg_auL7) =>
                              MapM_Sym0 a6989586621679128034
type instance Apply @((~>) a_auhj (m_auhi b_auhk)) @((~>) (t_auhh a_auhj) (m_auhi ())) MapM_Sym0 a6989586621679128034 = MapM_Sym1 a6989586621679128034
instance SuppressUnusedWarnings MapM_Sym0 where
  suppressUnusedWarnings = snd ((,) MapM_Sym0KindInference ())
type MapM_Sym1 :: (~>) a_auhj (m_auhi b_auhk)
                  -> (~>) (t_auhh a_auhj) (m_auhi ())
data MapM_Sym1 (a6989586621679128034 :: (~>) a_auhj (m_auhi b_auhk)) :: (~>) (t_auhh a_auhj) (m_auhi ())
  where
    MapM_Sym1KindInference :: SameKind (Apply (MapM_Sym1 a6989586621679128034) arg_auL7) (MapM_Sym2 a6989586621679128034 arg_auL7) =>
                              MapM_Sym1 a6989586621679128034 a6989586621679128035
type instance Apply @(t_auhh a_auhj) @(m_auhi ()) (MapM_Sym1 a6989586621679128034) a6989586621679128035 = MapM_ a6989586621679128034 a6989586621679128035
instance SuppressUnusedWarnings (MapM_Sym1 a6989586621679128034) where
  suppressUnusedWarnings = snd ((,) MapM_Sym1KindInference ())
type MapM_Sym2 :: (~>) a_auhj (m_auhi b_auhk)
                  -> t_auhh a_auhj -> m_auhi ()
type family MapM_Sym2 @a_auhj @m_auhi @b_auhk @t_auhh (a6989586621679128034 :: (~>) a_auhj (m_auhi b_auhk)) (a6989586621679128035 :: t_auhh a_auhj) :: m_auhi () where
  MapM_Sym2 a6989586621679128034 a6989586621679128035 = MapM_ a6989586621679128034 a6989586621679128035
type For_Sym0 :: (~>) (t_auhl a_auhn) ((~>) ((~>) a_auhn (f_auhm b_auho)) (f_auhm ()))
data For_Sym0 :: (~>) (t_auhl a_auhn) ((~>) ((~>) a_auhn (f_auhm b_auho)) (f_auhm ()))
  where
    For_Sym0KindInference :: SameKind (Apply For_Sym0 arg_auLi) (For_Sym1 arg_auLi) =>
                              For_Sym0 a6989586621679128045
type instance Apply @(t_auhl a_auhn) @((~>) ((~>) a_auhn (f_auhm b_auho)) (f_auhm ())) For_Sym0 a6989586621679128045 = For_Sym1 a6989586621679128045
instance SuppressUnusedWarnings For_Sym0 where
  suppressUnusedWarnings = snd ((,) For_Sym0KindInference ())
type For_Sym1 :: t_auhl a_auhn
                  -> (~>) ((~>) a_auhn (f_auhm b_auho)) (f_auhm ())
data For_Sym1 (a6989586621679128045 :: t_auhl a_auhn) :: (~>) ((~>) a_auhn (f_auhm b_auho)) (f_auhm ())
  where
    For_Sym1KindInference :: SameKind (Apply (For_Sym1 a6989586621679128045) arg_auLi) (For_Sym2 a6989586621679128045 arg_auLi) =>
                              For_Sym1 a6989586621679128045 a6989586621679128046
type instance Apply @((~>) a_auhn (f_auhm b_auho)) @(f_auhm ()) (For_Sym1 a6989586621679128045) a6989586621679128046 = For_ a6989586621679128045 a6989586621679128046
instance SuppressUnusedWarnings (For_Sym1 a6989586621679128045) where
  suppressUnusedWarnings = snd ((,) For_Sym1KindInference ())
type For_Sym2 :: t_auhl a_auhn
                  -> (~>) a_auhn (f_auhm b_auho) -> f_auhm ()
type family For_Sym2 @t_auhl @a_auhn @f_auhm @b_auho (a6989586621679128045 :: t_auhl a_auhn) (a6989586621679128046 :: (~>) a_auhn (f_auhm b_auho)) :: f_auhm () where
  For_Sym2 a6989586621679128045 a6989586621679128046 = For_ a6989586621679128045 a6989586621679128046
type Traverse_Sym0 :: (~>) ((~>) a_auhr (f_auhq b_auhs)) ((~>) (t_auhp a_auhr) (f_auhq ()))
data Traverse_Sym0 :: (~>) ((~>) a_auhr (f_auhq b_auhs)) ((~>) (t_auhp a_auhr) (f_auhq ()))
  where
    Traverse_Sym0KindInference :: SameKind (Apply Traverse_Sym0 arg_auLr) (Traverse_Sym1 arg_auLr) =>
                                  Traverse_Sym0 a6989586621679128054
type instance Apply @((~>) a_auhr (f_auhq b_auhs)) @((~>) (t_auhp a_auhr) (f_auhq ())) Traverse_Sym0 a6989586621679128054 = Traverse_Sym1 a6989586621679128054
instance SuppressUnusedWarnings Traverse_Sym0 where
  suppressUnusedWarnings = snd ((,) Traverse_Sym0KindInference ())
type Traverse_Sym1 :: (~>) a_auhr (f_auhq b_auhs)
                      -> (~>) (t_auhp a_auhr) (f_auhq ())
data Traverse_Sym1 (a6989586621679128054 :: (~>) a_auhr (f_auhq b_auhs)) :: (~>) (t_auhp a_auhr) (f_auhq ())
  where
    Traverse_Sym1KindInference :: SameKind (Apply (Traverse_Sym1 a6989586621679128054) arg_auLr) (Traverse_Sym2 a6989586621679128054 arg_auLr) =>
                                  Traverse_Sym1 a6989586621679128054 a6989586621679128055
type instance Apply @(t_auhp a_auhr) @(f_auhq ()) (Traverse_Sym1 a6989586621679128054) a6989586621679128055 = Traverse_ a6989586621679128054 a6989586621679128055
instance SuppressUnusedWarnings (Traverse_Sym1 a6989586621679128054) where
  suppressUnusedWarnings = snd ((,) Traverse_Sym1KindInference ())
type Traverse_Sym2 :: (~>) a_auhr (f_auhq b_auhs)
                      -> t_auhp a_auhr -> f_auhq ()
type family Traverse_Sym2 @a_auhr @f_auhq @b_auhs @t_auhp (a6989586621679128054 :: (~>) a_auhr (f_auhq b_auhs)) (a6989586621679128055 :: t_auhp a_auhr) :: f_auhq () where
  Traverse_Sym2 a6989586621679128054 a6989586621679128055 = Traverse_ a6989586621679128054 a6989586621679128055
type FoldlMSym0 :: (~>) ((~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) ((~>) b_auhv ((~>) (t_auht a_auhw) (m_auhu b_auhv)))
data FoldlMSym0 :: (~>) ((~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) ((~>) b_auhv ((~>) (t_auht a_auhw) (m_auhu b_auhv)))
  where
    FoldlMSym0KindInference :: SameKind (Apply FoldlMSym0 arg_auLz) (FoldlMSym1 arg_auLz) =>
                                FoldlMSym0 a6989586621679128062
type instance Apply @((~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) @((~>) b_auhv ((~>) (t_auht a_auhw) (m_auhu b_auhv))) FoldlMSym0 a6989586621679128062 = FoldlMSym1 a6989586621679128062
instance SuppressUnusedWarnings FoldlMSym0 where
  suppressUnusedWarnings = snd ((,) FoldlMSym0KindInference ())
type FoldlMSym1 :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))
                    -> (~>) b_auhv ((~>) (t_auht a_auhw) (m_auhu b_auhv))
data FoldlMSym1 (a6989586621679128062 :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) :: (~>) b_auhv ((~>) (t_auht a_auhw) (m_auhu b_auhv))
  where
    FoldlMSym1KindInference :: SameKind (Apply (FoldlMSym1 a6989586621679128062) arg_auLz) (FoldlMSym2 a6989586621679128062 arg_auLz) =>
                                FoldlMSym1 a6989586621679128062 a6989586621679128063
type instance Apply @b_auhv @((~>) (t_auht a_auhw) (m_auhu b_auhv)) (FoldlMSym1 a6989586621679128062) a6989586621679128063 = FoldlMSym2 a6989586621679128062 a6989586621679128063
instance SuppressUnusedWarnings (FoldlMSym1 a6989586621679128062) where
  suppressUnusedWarnings = snd ((,) FoldlMSym1KindInference ())
type FoldlMSym2 :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))
                    -> b_auhv -> (~>) (t_auht a_auhw) (m_auhu b_auhv)
data FoldlMSym2 (a6989586621679128062 :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) (a6989586621679128063 :: b_auhv) :: (~>) (t_auht a_auhw) (m_auhu b_auhv)
  where
    FoldlMSym2KindInference :: SameKind (Apply (FoldlMSym2 a6989586621679128062 a6989586621679128063) arg_auLz) (FoldlMSym3 a6989586621679128062 a6989586621679128063 arg_auLz) =>
                                FoldlMSym2 a6989586621679128062 a6989586621679128063 a6989586621679128064
type instance Apply @(t_auht a_auhw) @(m_auhu b_auhv) (FoldlMSym2 a6989586621679128062 a6989586621679128063) a6989586621679128064 = FoldlM a6989586621679128062 a6989586621679128063 a6989586621679128064
instance SuppressUnusedWarnings (FoldlMSym2 a6989586621679128062 a6989586621679128063) where
  suppressUnusedWarnings = snd ((,) FoldlMSym2KindInference ())
type FoldlMSym3 :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))
                    -> b_auhv -> t_auht a_auhw -> m_auhu b_auhv
type family FoldlMSym3 @b_auhv @a_auhw @m_auhu @t_auht (a6989586621679128062 :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) (a6989586621679128063 :: b_auhv) (a6989586621679128064 :: t_auht a_auhw) :: m_auhu b_auhv where
  FoldlMSym3 a6989586621679128062 a6989586621679128063 a6989586621679128064 = FoldlM a6989586621679128062 a6989586621679128063 a6989586621679128064
type FoldrMSym0 :: (~>) ((~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) ((~>) b_auhA ((~>) (t_auhx a_auhz) (m_auhy b_auhA)))
data FoldrMSym0 :: (~>) ((~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) ((~>) b_auhA ((~>) (t_auhx a_auhz) (m_auhy b_auhA)))
  where
    FoldrMSym0KindInference :: SameKind (Apply FoldrMSym0 arg_auLR) (FoldrMSym1 arg_auLR) =>
                                FoldrMSym0 a6989586621679128080
type instance Apply @((~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) @((~>) b_auhA ((~>) (t_auhx a_auhz) (m_auhy b_auhA))) FoldrMSym0 a6989586621679128080 = FoldrMSym1 a6989586621679128080
instance SuppressUnusedWarnings FoldrMSym0 where
  suppressUnusedWarnings = snd ((,) FoldrMSym0KindInference ())
type FoldrMSym1 :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))
                    -> (~>) b_auhA ((~>) (t_auhx a_auhz) (m_auhy b_auhA))
data FoldrMSym1 (a6989586621679128080 :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) :: (~>) b_auhA ((~>) (t_auhx a_auhz) (m_auhy b_auhA))
  where
    FoldrMSym1KindInference :: SameKind (Apply (FoldrMSym1 a6989586621679128080) arg_auLR) (FoldrMSym2 a6989586621679128080 arg_auLR) =>
                                FoldrMSym1 a6989586621679128080 a6989586621679128081
type instance Apply @b_auhA @((~>) (t_auhx a_auhz) (m_auhy b_auhA)) (FoldrMSym1 a6989586621679128080) a6989586621679128081 = FoldrMSym2 a6989586621679128080 a6989586621679128081
instance SuppressUnusedWarnings (FoldrMSym1 a6989586621679128080) where
  suppressUnusedWarnings = snd ((,) FoldrMSym1KindInference ())
type FoldrMSym2 :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))
                    -> b_auhA -> (~>) (t_auhx a_auhz) (m_auhy b_auhA)
data FoldrMSym2 (a6989586621679128080 :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) (a6989586621679128081 :: b_auhA) :: (~>) (t_auhx a_auhz) (m_auhy b_auhA)
  where
    FoldrMSym2KindInference :: SameKind (Apply (FoldrMSym2 a6989586621679128080 a6989586621679128081) arg_auLR) (FoldrMSym3 a6989586621679128080 a6989586621679128081 arg_auLR) =>
                                FoldrMSym2 a6989586621679128080 a6989586621679128081 a6989586621679128082
type instance Apply @(t_auhx a_auhz) @(m_auhy b_auhA) (FoldrMSym2 a6989586621679128080 a6989586621679128081) a6989586621679128082 = FoldrM a6989586621679128080 a6989586621679128081 a6989586621679128082
instance SuppressUnusedWarnings (FoldrMSym2 a6989586621679128080 a6989586621679128081) where
  suppressUnusedWarnings = snd ((,) FoldrMSym2KindInference ())
type FoldrMSym3 :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))
                    -> b_auhA -> t_auhx a_auhz -> m_auhy b_auhA
type family FoldrMSym3 @a_auhz @b_auhA @m_auhy @t_auhx (a6989586621679128080 :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) (a6989586621679128081 :: b_auhA) (a6989586621679128082 :: t_auhx a_auhz) :: m_auhy b_auhA where
  FoldrMSym3 a6989586621679128080 a6989586621679128081 a6989586621679128082 = FoldrM a6989586621679128080 a6989586621679128081 a6989586621679128082
type Find :: (~>) a_augJ Bool -> t_augI a_augJ -> Maybe a_augJ
type family Find @a_augJ @t_augI (a_auIs :: (~>) a_augJ Bool) (a_auIt :: t_augI a_augJ) :: Maybe a_augJ where
  Find p_auIx a_6989586621679127866_auIy = Apply (Apply (Apply (.@#@$) GetFirstSym0) (Apply FoldMapSym0 (LamCases_6989586621679127875Sym0 p_auIx a_6989586621679127866_auIy))) a_6989586621679127866_auIy
type NotElem :: a_augL -> t_augK a_augL -> Bool
type family NotElem @a_augL @t_augK (a_auIM :: a_augL) (a_auIN :: t_augK a_augL) :: Bool where
  NotElem x_auIR a_6989586621679127886_auIS = Apply (Apply (Apply (.@#@$) NotSym0) (Apply ElemSym0 x_auIR)) a_6989586621679127886_auIS
type MinimumBy :: (~>) a_augN ((~>) a_augN Ordering)
                  -> t_augM a_augN -> a_augN
type family MinimumBy @a_augN @t_augM (a_auIV :: (~>) a_augN ((~>) a_augN Ordering)) (a_auIW :: t_augM a_augN) :: a_augN where
  MinimumBy cmp_auJ0 a_6989586621679127895_auJ1 = Apply (Apply Foldl1Sym0 (Let6989586621679127904Min'Sym0 cmp_auJ0 a_6989586621679127895_auJ1)) a_6989586621679127895_auJ1
type MaximumBy :: (~>) a_augP ((~>) a_augP Ordering)
                  -> t_augO a_augP -> a_augP
type family MaximumBy @a_augP @t_augO (a_auJf :: (~>) a_augP ((~>) a_augP Ordering)) (a_auJg :: t_augO a_augP) :: a_augP where
  MaximumBy cmp_auJk a_6989586621679127915_auJl = Apply (Apply Foldl1Sym0 (Let6989586621679127924Max'Sym0 cmp_auJk a_6989586621679127915_auJl)) a_6989586621679127915_auJl
type All :: (~>) a_augR Bool -> t_augQ a_augR -> Bool
type family All @a_augR @t_augQ (a_auJz :: (~>) a_augR Bool) (a_auJA :: t_augQ a_augR) :: Bool where
  All p_auJE a_6989586621679127935_auJF = Apply (Apply (Apply (.@#@$) GetAllSym0) (Apply FoldMapSym0 (Apply (Apply (.@#@$) All_Sym0) p_auJE))) a_6989586621679127935_auJF
type Any :: (~>) a_augT Bool -> t_augS a_augT -> Bool
type family Any @a_augT @t_augS (a_auJI :: (~>) a_augT Bool) (a_auJJ :: t_augS a_augT) :: Bool where
  Any p_auJN a_6989586621679127944_auJO = Apply (Apply (Apply (.@#@$) GetAnySym0) (Apply FoldMapSym0 (Apply (Apply (.@#@$) Any_Sym0) p_auJN))) a_6989586621679127944_auJO
type Or :: t_augU Bool -> Bool
type family Or @t_augU (a_auJR :: t_augU Bool) :: Bool where
  Or a_6989586621679127953_auJU = Apply (Apply (Apply (.@#@$) GetAnySym0) (Apply FoldMapSym0 Any_Sym0)) a_6989586621679127953_auJU
type And :: t_augV Bool -> Bool
type family And @t_augV (a_auJX :: t_augV Bool) :: Bool where
  And a_6989586621679127959_auK0 = Apply (Apply (Apply (.@#@$) GetAllSym0) (Apply FoldMapSym0 All_Sym0)) a_6989586621679127959_auK0
type ConcatMap :: (~>) a_augX [b_augY] -> t_augW a_augX -> [b_augY]
type family ConcatMap @a_augX @b_augY @t_augW (a_auK1 :: (~>) a_augX [b_augY]) (a_auK2 :: t_augW a_augX) :: [b_augY] where
  ConcatMap f_auK6 xs_auK7 = Apply (Apply (Apply FoldrSym0 (LamCases_6989586621679127972Sym0 f_auK6 xs_auK7)) NilSym0) xs_auK7
type Concat :: t_augZ [a_auh0] -> [a_auh0]
type family Concat @t_augZ @a_auh0 (a_auKh :: t_augZ [a_auh0]) :: [a_auh0] where
  Concat xs_auKk = Apply (Apply (Apply FoldrSym0 (LamCases_6989586621679127985Sym0 xs_auKk)) NilSym0) xs_auKk
type Msum :: forall t_auh1
                    (m_auh2 :: Type -> Type)
                    a_auh3. t_auh1 (m_auh2 a_auh3) -> m_auh2 a_auh3
type family Msum @t_auh1 @(m_auh2 :: Type
                                      -> Type) @a_auh3 (a_auKw :: t_auh1 (m_auh2 a_auh3)) :: m_auh2 a_auh3 where
  Msum @t_auh1 @m_auh2 @a_auh3 (a_6989586621679127994_auKz :: t_auh1 (m_auh2 a_auh3)) = Apply AsumSym0 a_6989586621679127994_auKz
type Asum :: forall t_auh4
                    (f_auh5 :: Type -> Type)
                    a_auh6. t_auh4 (f_auh5 a_auh6) -> f_auh5 a_auh6
type family Asum @t_auh4 @(f_auh5 :: Type
                                      -> Type) @a_auh6 (a_auKC :: t_auh4 (f_auh5 a_auh6)) :: f_auh5 a_auh6 where
  Asum @t_auh4 @f_auh5 @a_auh6 (a_6989586621679128000_auKF :: t_auh4 (f_auh5 a_auh6)) = Apply (Apply (Apply FoldrSym0 (<|>@#@$)) EmptySym0) a_6989586621679128000_auKF
type Sequence_ :: t_auh7 (m_auh8 a_auh9) -> m_auh8 ()
type family Sequence_ @t_auh7 @m_auh8 @a_auh9 (a_auKI :: t_auh7 (m_auh8 a_auh9)) :: m_auh8 () where
  Sequence_ a_6989586621679128006_auKL = Apply (Apply (Apply FoldrSym0 (>>@#@$)) (Apply ReturnSym0 Tuple0Sym0)) a_6989586621679128006_auKL
type SequenceA_ :: t_auha (f_auhb a_auhc) -> f_auhb ()
type family SequenceA_ @t_auha @f_auhb @a_auhc (a_auKO :: t_auha (f_auhb a_auhc)) :: f_auhb () where
  SequenceA_ a_6989586621679128012_auKR = Apply (Apply (Apply FoldrSym0 (*>@#@$)) (Apply PureSym0 Tuple0Sym0)) a_6989586621679128012_auKR
type ForM_ :: t_auhd a_auhf
              -> (~>) a_auhf (m_auhe b_auhg) -> m_auhe ()
type family ForM_ @t_auhd @a_auhf @m_auhe @b_auhg (a_auKW :: t_auhd a_auhf) (a_auKX :: (~>) a_auhf (m_auhe b_auhg)) :: m_auhe () where
  ForM_ a_6989586621679128018_auL1 a_6989586621679128020_auL2 = Apply (Apply (Apply FlipSym0 MapM_Sym0) a_6989586621679128018_auL1) a_6989586621679128020_auL2
type MapM_ :: (~>) a_auhj (m_auhi b_auhk)
              -> t_auhh a_auhj -> m_auhi ()
type family MapM_ @a_auhj @m_auhi @b_auhk @t_auhh (a_auL5 :: (~>) a_auhj (m_auhi b_auhk)) (a_auL6 :: t_auhh a_auhj) :: m_auhi () where
  MapM_ f_auLa a_6989586621679128029_auLb = Apply (Apply (Apply FoldrSym0 (Apply (Apply (.@#@$) (>>@#@$)) f_auLa)) (Apply ReturnSym0 Tuple0Sym0)) a_6989586621679128029_auLb
type For_ :: t_auhl a_auhn
              -> (~>) a_auhn (f_auhm b_auho) -> f_auhm ()
type family For_ @t_auhl @a_auhn @f_auhm @b_auho (a_auLg :: t_auhl a_auhn) (a_auLh :: (~>) a_auhn (f_auhm b_auho)) :: f_auhm () where
  For_ a_6989586621679128038_auLl a_6989586621679128040_auLm = Apply (Apply (Apply FlipSym0 Traverse_Sym0) a_6989586621679128038_auLl) a_6989586621679128040_auLm
type Traverse_ :: (~>) a_auhr (f_auhq b_auhs)
                  -> t_auhp a_auhr -> f_auhq ()
type family Traverse_ @a_auhr @f_auhq @b_auhs @t_auhp (a_auLp :: (~>) a_auhr (f_auhq b_auhs)) (a_auLq :: t_auhp a_auhr) :: f_auhq () where
  Traverse_ f_auLu a_6989586621679128049_auLv = Apply (Apply (Apply FoldrSym0 (Apply (Apply (.@#@$) (*>@#@$)) f_auLu)) (Apply PureSym0 Tuple0Sym0)) a_6989586621679128049_auLv
type FoldlM :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))
                -> b_auhv -> t_auht a_auhw -> m_auhu b_auhv
type family FoldlM @b_auhv @a_auhw @m_auhu @t_auht (a_auLw :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) (a_auLx :: b_auhv) (a_auLy :: t_auht a_auhw) :: m_auhu b_auhv where
  FoldlM f_auLD z0_auLE xs_auLF = Apply (Apply (Apply (Apply FoldrSym0 (Let6989586621679128068F'Sym0 f_auLD z0_auLE xs_auLF)) ReturnSym0) xs_auLF) z0_auLE
type FoldrM :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))
                -> b_auhA -> t_auhx a_auhz -> m_auhy b_auhA
type family FoldrM @a_auhz @b_auhA @m_auhy @t_auhx (a_auLO :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) (a_auLP :: b_auhA) (a_auLQ :: t_auhx a_auhz) :: m_auhy b_auhA where
  FoldrM f_auLV z0_auLW xs_auLX = Apply (Apply (Apply (Apply FoldlSym0 (Let6989586621679128086F'Sym0 f_auLV z0_auLW xs_auLX)) ReturnSym0) xs_auLX) z0_auLW
type FoldSym0 :: forall (t_auic :: Type -> Type)
                        m_auid. (~>) (t_auic m_auid) m_auid
data FoldSym0 :: (~>) (t_auic m_auid) m_auid
  where
    FoldSym0KindInference :: SameKind (Apply FoldSym0 arg_auM7) (FoldSym1 arg_auM7) =>
                              FoldSym0 a6989586621679128096
type instance Apply @(t_auic m_auid) @m_auid FoldSym0 a6989586621679128096 = Fold a6989586621679128096
instance SuppressUnusedWarnings FoldSym0 where
  suppressUnusedWarnings = snd ((,) FoldSym0KindInference ())
type FoldSym1 :: forall (t_auic :: Type -> Type)
                        m_auid. t_auic m_auid -> m_auid
type family FoldSym1 @(t_auic :: Type
                                  -> Type) @m_auid (a6989586621679128096 :: t_auic m_auid) :: m_auid where
  FoldSym1 a6989586621679128096 = Fold a6989586621679128096
type FoldMapSym0 :: forall (t_auic :: Type -> Type)
                            a_auif
                            m_auie. (~>) ((~>) a_auif m_auie) ((~>) (t_auic a_auif) m_auie)
data FoldMapSym0 :: (~>) ((~>) a_auif m_auie) ((~>) (t_auic a_auif) m_auie)
  where
    FoldMapSym0KindInference :: SameKind (Apply FoldMapSym0 arg_auMb) (FoldMapSym1 arg_auMb) =>
                                FoldMapSym0 a6989586621679128100
type instance Apply @((~>) a_auif m_auie) @((~>) (t_auic a_auif) m_auie) FoldMapSym0 a6989586621679128100 = FoldMapSym1 a6989586621679128100
instance SuppressUnusedWarnings FoldMapSym0 where
  suppressUnusedWarnings = snd ((,) FoldMapSym0KindInference ())
type FoldMapSym1 :: forall (t_auic :: Type -> Type)
                            a_auif
                            m_auie. (~>) a_auif m_auie -> (~>) (t_auic a_auif) m_auie
data FoldMapSym1 (a6989586621679128100 :: (~>) a_auif m_auie) :: (~>) (t_auic a_auif) m_auie
  where
    FoldMapSym1KindInference :: SameKind (Apply (FoldMapSym1 a6989586621679128100) arg_auMb) (FoldMapSym2 a6989586621679128100 arg_auMb) =>
                                FoldMapSym1 a6989586621679128100 a6989586621679128101
type instance Apply @(t_auic a_auif) @m_auie (FoldMapSym1 a6989586621679128100) a6989586621679128101 = FoldMap a6989586621679128100 a6989586621679128101
instance SuppressUnusedWarnings (FoldMapSym1 a6989586621679128100) where
  suppressUnusedWarnings = snd ((,) FoldMapSym1KindInference ())
type FoldMapSym2 :: forall (t_auic :: Type -> Type)
                            a_auif
                            m_auie. (~>) a_auif m_auie -> t_auic a_auif -> m_auie
type family FoldMapSym2 @(t_auic :: Type
                                    -> Type) @a_auif @m_auie (a6989586621679128100 :: (~>) a_auif m_auie) (a6989586621679128101 :: t_auic a_auif) :: m_auie where
  FoldMapSym2 a6989586621679128100 a6989586621679128101 = FoldMap a6989586621679128100 a6989586621679128101
type FoldrSym0 :: forall (t_auic :: Type -> Type)
                          a_auig
                          b_auih. (~>) ((~>) a_auig ((~>) b_auih b_auih)) ((~>) b_auih ((~>) (t_auic a_auig) b_auih))
data FoldrSym0 :: (~>) ((~>) a_auig ((~>) b_auih b_auih)) ((~>) b_auih ((~>) (t_auic a_auig) b_auih))
  where
    FoldrSym0KindInference :: SameKind (Apply FoldrSym0 arg_auMh) (FoldrSym1 arg_auMh) =>
                              FoldrSym0 a6989586621679128106
type instance Apply @((~>) a_auig ((~>) b_auih b_auih)) @((~>) b_auih ((~>) (t_auic a_auig) b_auih)) FoldrSym0 a6989586621679128106 = FoldrSym1 a6989586621679128106
instance SuppressUnusedWarnings FoldrSym0 where
  suppressUnusedWarnings = snd ((,) FoldrSym0KindInference ())
type FoldrSym1 :: forall (t_auic :: Type -> Type)
                          a_auig
                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                  -> (~>) b_auih ((~>) (t_auic a_auig) b_auih)
data FoldrSym1 (a6989586621679128106 :: (~>) a_auig ((~>) b_auih b_auih)) :: (~>) b_auih ((~>) (t_auic a_auig) b_auih)
  where
    FoldrSym1KindInference :: SameKind (Apply (FoldrSym1 a6989586621679128106) arg_auMh) (FoldrSym2 a6989586621679128106 arg_auMh) =>
                              FoldrSym1 a6989586621679128106 a6989586621679128107
type instance Apply @b_auih @((~>) (t_auic a_auig) b_auih) (FoldrSym1 a6989586621679128106) a6989586621679128107 = FoldrSym2 a6989586621679128106 a6989586621679128107
instance SuppressUnusedWarnings (FoldrSym1 a6989586621679128106) where
  suppressUnusedWarnings = snd ((,) FoldrSym1KindInference ())
type FoldrSym2 :: forall (t_auic :: Type -> Type)
                          a_auig
                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                  -> b_auih -> (~>) (t_auic a_auig) b_auih
data FoldrSym2 (a6989586621679128106 :: (~>) a_auig ((~>) b_auih b_auih)) (a6989586621679128107 :: b_auih) :: (~>) (t_auic a_auig) b_auih
  where
    FoldrSym2KindInference :: SameKind (Apply (FoldrSym2 a6989586621679128106 a6989586621679128107) arg_auMh) (FoldrSym3 a6989586621679128106 a6989586621679128107 arg_auMh) =>
                              FoldrSym2 a6989586621679128106 a6989586621679128107 a6989586621679128108
type instance Apply @(t_auic a_auig) @b_auih (FoldrSym2 a6989586621679128106 a6989586621679128107) a6989586621679128108 = Foldr a6989586621679128106 a6989586621679128107 a6989586621679128108
instance SuppressUnusedWarnings (FoldrSym2 a6989586621679128106 a6989586621679128107) where
  suppressUnusedWarnings = snd ((,) FoldrSym2KindInference ())
type FoldrSym3 :: forall (t_auic :: Type -> Type)
                          a_auig
                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                  -> b_auih -> t_auic a_auig -> b_auih
type family FoldrSym3 @(t_auic :: Type
                                  -> Type) @a_auig @b_auih (a6989586621679128106 :: (~>) a_auig ((~>) b_auih b_auih)) (a6989586621679128107 :: b_auih) (a6989586621679128108 :: t_auic a_auig) :: b_auih where
  FoldrSym3 a6989586621679128106 a6989586621679128107 a6989586621679128108 = Foldr a6989586621679128106 a6989586621679128107 a6989586621679128108
type Foldr'Sym0 :: forall (t_auic :: Type -> Type)
                          a_auii
                          b_auij. (~>) ((~>) a_auii ((~>) b_auij b_auij)) ((~>) b_auij ((~>) (t_auic a_auii) b_auij))
data Foldr'Sym0 :: (~>) ((~>) a_auii ((~>) b_auij b_auij)) ((~>) b_auij ((~>) (t_auic a_auii) b_auij))
  where
    Foldr'Sym0KindInference :: SameKind (Apply Foldr'Sym0 arg_auMo) (Foldr'Sym1 arg_auMo) =>
                                Foldr'Sym0 a6989586621679128113
type instance Apply @((~>) a_auii ((~>) b_auij b_auij)) @((~>) b_auij ((~>) (t_auic a_auii) b_auij)) Foldr'Sym0 a6989586621679128113 = Foldr'Sym1 a6989586621679128113
instance SuppressUnusedWarnings Foldr'Sym0 where
  suppressUnusedWarnings = snd ((,) Foldr'Sym0KindInference ())
type Foldr'Sym1 :: forall (t_auic :: Type -> Type)
                          a_auii
                          b_auij. (~>) a_auii ((~>) b_auij b_auij)
                                  -> (~>) b_auij ((~>) (t_auic a_auii) b_auij)
data Foldr'Sym1 (a6989586621679128113 :: (~>) a_auii ((~>) b_auij b_auij)) :: (~>) b_auij ((~>) (t_auic a_auii) b_auij)
  where
    Foldr'Sym1KindInference :: SameKind (Apply (Foldr'Sym1 a6989586621679128113) arg_auMo) (Foldr'Sym2 a6989586621679128113 arg_auMo) =>
                                Foldr'Sym1 a6989586621679128113 a6989586621679128114
type instance Apply @b_auij @((~>) (t_auic a_auii) b_auij) (Foldr'Sym1 a6989586621679128113) a6989586621679128114 = Foldr'Sym2 a6989586621679128113 a6989586621679128114
instance SuppressUnusedWarnings (Foldr'Sym1 a6989586621679128113) where
  suppressUnusedWarnings = snd ((,) Foldr'Sym1KindInference ())
type Foldr'Sym2 :: forall (t_auic :: Type -> Type)
                          a_auii
                          b_auij. (~>) a_auii ((~>) b_auij b_auij)
                                  -> b_auij -> (~>) (t_auic a_auii) b_auij
data Foldr'Sym2 (a6989586621679128113 :: (~>) a_auii ((~>) b_auij b_auij)) (a6989586621679128114 :: b_auij) :: (~>) (t_auic a_auii) b_auij
  where
    Foldr'Sym2KindInference :: SameKind (Apply (Foldr'Sym2 a6989586621679128113 a6989586621679128114) arg_auMo) (Foldr'Sym3 a6989586621679128113 a6989586621679128114 arg_auMo) =>
                                Foldr'Sym2 a6989586621679128113 a6989586621679128114 a6989586621679128115
type instance Apply @(t_auic a_auii) @b_auij (Foldr'Sym2 a6989586621679128113 a6989586621679128114) a6989586621679128115 = Foldr' a6989586621679128113 a6989586621679128114 a6989586621679128115
instance SuppressUnusedWarnings (Foldr'Sym2 a6989586621679128113 a6989586621679128114) where
  suppressUnusedWarnings = snd ((,) Foldr'Sym2KindInference ())
type Foldr'Sym3 :: forall (t_auic :: Type -> Type)
                          a_auii
                          b_auij. (~>) a_auii ((~>) b_auij b_auij)
                                  -> b_auij -> t_auic a_auii -> b_auij
type family Foldr'Sym3 @(t_auic :: Type
                                    -> Type) @a_auii @b_auij (a6989586621679128113 :: (~>) a_auii ((~>) b_auij b_auij)) (a6989586621679128114 :: b_auij) (a6989586621679128115 :: t_auic a_auii) :: b_auij where
  Foldr'Sym3 a6989586621679128113 a6989586621679128114 a6989586621679128115 = Foldr' a6989586621679128113 a6989586621679128114 a6989586621679128115
type FoldlSym0 :: forall (t_auic :: Type -> Type)
                          b_auik
                          a_auil. (~>) ((~>) b_auik ((~>) a_auil b_auik)) ((~>) b_auik ((~>) (t_auic a_auil) b_auik))
data FoldlSym0 :: (~>) ((~>) b_auik ((~>) a_auil b_auik)) ((~>) b_auik ((~>) (t_auic a_auil) b_auik))
  where
    FoldlSym0KindInference :: SameKind (Apply FoldlSym0 arg_auMv) (FoldlSym1 arg_auMv) =>
                              FoldlSym0 a6989586621679128120
type instance Apply @((~>) b_auik ((~>) a_auil b_auik)) @((~>) b_auik ((~>) (t_auic a_auil) b_auik)) FoldlSym0 a6989586621679128120 = FoldlSym1 a6989586621679128120
instance SuppressUnusedWarnings FoldlSym0 where
  suppressUnusedWarnings = snd ((,) FoldlSym0KindInference ())
type FoldlSym1 :: forall (t_auic :: Type -> Type)
                          b_auik
                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                  -> (~>) b_auik ((~>) (t_auic a_auil) b_auik)
data FoldlSym1 (a6989586621679128120 :: (~>) b_auik ((~>) a_auil b_auik)) :: (~>) b_auik ((~>) (t_auic a_auil) b_auik)
  where
    FoldlSym1KindInference :: SameKind (Apply (FoldlSym1 a6989586621679128120) arg_auMv) (FoldlSym2 a6989586621679128120 arg_auMv) =>
                              FoldlSym1 a6989586621679128120 a6989586621679128121
type instance Apply @b_auik @((~>) (t_auic a_auil) b_auik) (FoldlSym1 a6989586621679128120) a6989586621679128121 = FoldlSym2 a6989586621679128120 a6989586621679128121
instance SuppressUnusedWarnings (FoldlSym1 a6989586621679128120) where
  suppressUnusedWarnings = snd ((,) FoldlSym1KindInference ())
type FoldlSym2 :: forall (t_auic :: Type -> Type)
                          b_auik
                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                  -> b_auik -> (~>) (t_auic a_auil) b_auik
data FoldlSym2 (a6989586621679128120 :: (~>) b_auik ((~>) a_auil b_auik)) (a6989586621679128121 :: b_auik) :: (~>) (t_auic a_auil) b_auik
  where
    FoldlSym2KindInference :: SameKind (Apply (FoldlSym2 a6989586621679128120 a6989586621679128121) arg_auMv) (FoldlSym3 a6989586621679128120 a6989586621679128121 arg_auMv) =>
                              FoldlSym2 a6989586621679128120 a6989586621679128121 a6989586621679128122
type instance Apply @(t_auic a_auil) @b_auik (FoldlSym2 a6989586621679128120 a6989586621679128121) a6989586621679128122 = Foldl a6989586621679128120 a6989586621679128121 a6989586621679128122
instance SuppressUnusedWarnings (FoldlSym2 a6989586621679128120 a6989586621679128121) where
  suppressUnusedWarnings = snd ((,) FoldlSym2KindInference ())
type FoldlSym3 :: forall (t_auic :: Type -> Type)
                          b_auik
                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                  -> b_auik -> t_auic a_auil -> b_auik
type family FoldlSym3 @(t_auic :: Type
                                  -> Type) @b_auik @a_auil (a6989586621679128120 :: (~>) b_auik ((~>) a_auil b_auik)) (a6989586621679128121 :: b_auik) (a6989586621679128122 :: t_auic a_auil) :: b_auik where
  FoldlSym3 a6989586621679128120 a6989586621679128121 a6989586621679128122 = Foldl a6989586621679128120 a6989586621679128121 a6989586621679128122
type Foldl'Sym0 :: forall (t_auic :: Type -> Type)
                          b_auim
                          a_auin. (~>) ((~>) b_auim ((~>) a_auin b_auim)) ((~>) b_auim ((~>) (t_auic a_auin) b_auim))
data Foldl'Sym0 :: (~>) ((~>) b_auim ((~>) a_auin b_auim)) ((~>) b_auim ((~>) (t_auic a_auin) b_auim))
  where
    Foldl'Sym0KindInference :: SameKind (Apply Foldl'Sym0 arg_auMC) (Foldl'Sym1 arg_auMC) =>
                                Foldl'Sym0 a6989586621679128127
type instance Apply @((~>) b_auim ((~>) a_auin b_auim)) @((~>) b_auim ((~>) (t_auic a_auin) b_auim)) Foldl'Sym0 a6989586621679128127 = Foldl'Sym1 a6989586621679128127
instance SuppressUnusedWarnings Foldl'Sym0 where
  suppressUnusedWarnings = snd ((,) Foldl'Sym0KindInference ())
type Foldl'Sym1 :: forall (t_auic :: Type -> Type)
                          b_auim
                          a_auin. (~>) b_auim ((~>) a_auin b_auim)
                                  -> (~>) b_auim ((~>) (t_auic a_auin) b_auim)
data Foldl'Sym1 (a6989586621679128127 :: (~>) b_auim ((~>) a_auin b_auim)) :: (~>) b_auim ((~>) (t_auic a_auin) b_auim)
  where
    Foldl'Sym1KindInference :: SameKind (Apply (Foldl'Sym1 a6989586621679128127) arg_auMC) (Foldl'Sym2 a6989586621679128127 arg_auMC) =>
                                Foldl'Sym1 a6989586621679128127 a6989586621679128128
type instance Apply @b_auim @((~>) (t_auic a_auin) b_auim) (Foldl'Sym1 a6989586621679128127) a6989586621679128128 = Foldl'Sym2 a6989586621679128127 a6989586621679128128
instance SuppressUnusedWarnings (Foldl'Sym1 a6989586621679128127) where
  suppressUnusedWarnings = snd ((,) Foldl'Sym1KindInference ())
type Foldl'Sym2 :: forall (t_auic :: Type -> Type)
                          b_auim
                          a_auin. (~>) b_auim ((~>) a_auin b_auim)
                                  -> b_auim -> (~>) (t_auic a_auin) b_auim
data Foldl'Sym2 (a6989586621679128127 :: (~>) b_auim ((~>) a_auin b_auim)) (a6989586621679128128 :: b_auim) :: (~>) (t_auic a_auin) b_auim
  where
    Foldl'Sym2KindInference :: SameKind (Apply (Foldl'Sym2 a6989586621679128127 a6989586621679128128) arg_auMC) (Foldl'Sym3 a6989586621679128127 a6989586621679128128 arg_auMC) =>
                                Foldl'Sym2 a6989586621679128127 a6989586621679128128 a6989586621679128129
type instance Apply @(t_auic a_auin) @b_auim (Foldl'Sym2 a6989586621679128127 a6989586621679128128) a6989586621679128129 = Foldl' a6989586621679128127 a6989586621679128128 a6989586621679128129
instance SuppressUnusedWarnings (Foldl'Sym2 a6989586621679128127 a6989586621679128128) where
  suppressUnusedWarnings = snd ((,) Foldl'Sym2KindInference ())
type Foldl'Sym3 :: forall (t_auic :: Type -> Type)
                          b_auim
                          a_auin. (~>) b_auim ((~>) a_auin b_auim)
                                  -> b_auim -> t_auic a_auin -> b_auim
type family Foldl'Sym3 @(t_auic :: Type
                                    -> Type) @b_auim @a_auin (a6989586621679128127 :: (~>) b_auim ((~>) a_auin b_auim)) (a6989586621679128128 :: b_auim) (a6989586621679128129 :: t_auic a_auin) :: b_auim where
  Foldl'Sym3 a6989586621679128127 a6989586621679128128 a6989586621679128129 = Foldl' a6989586621679128127 a6989586621679128128 a6989586621679128129
type Foldr1Sym0 :: forall (t_auic :: Type -> Type)
                          a_auio. (~>) ((~>) a_auio ((~>) a_auio a_auio)) ((~>) (t_auic a_auio) a_auio)
data Foldr1Sym0 :: (~>) ((~>) a_auio ((~>) a_auio a_auio)) ((~>) (t_auic a_auio) a_auio)
  where
    Foldr1Sym0KindInference :: SameKind (Apply Foldr1Sym0 arg_auMI) (Foldr1Sym1 arg_auMI) =>
                                Foldr1Sym0 a6989586621679128133
type instance Apply @((~>) a_auio ((~>) a_auio a_auio)) @((~>) (t_auic a_auio) a_auio) Foldr1Sym0 a6989586621679128133 = Foldr1Sym1 a6989586621679128133
instance SuppressUnusedWarnings Foldr1Sym0 where
  suppressUnusedWarnings = snd ((,) Foldr1Sym0KindInference ())
type Foldr1Sym1 :: forall (t_auic :: Type -> Type)
                          a_auio. (~>) a_auio ((~>) a_auio a_auio)
                                  -> (~>) (t_auic a_auio) a_auio
data Foldr1Sym1 (a6989586621679128133 :: (~>) a_auio ((~>) a_auio a_auio)) :: (~>) (t_auic a_auio) a_auio
  where
    Foldr1Sym1KindInference :: SameKind (Apply (Foldr1Sym1 a6989586621679128133) arg_auMI) (Foldr1Sym2 a6989586621679128133 arg_auMI) =>
                                Foldr1Sym1 a6989586621679128133 a6989586621679128134
type instance Apply @(t_auic a_auio) @a_auio (Foldr1Sym1 a6989586621679128133) a6989586621679128134 = Foldr1 a6989586621679128133 a6989586621679128134
instance SuppressUnusedWarnings (Foldr1Sym1 a6989586621679128133) where
  suppressUnusedWarnings = snd ((,) Foldr1Sym1KindInference ())
type Foldr1Sym2 :: forall (t_auic :: Type -> Type)
                          a_auio. (~>) a_auio ((~>) a_auio a_auio) -> t_auic a_auio -> a_auio
type family Foldr1Sym2 @(t_auic :: Type
                                    -> Type) @a_auio (a6989586621679128133 :: (~>) a_auio ((~>) a_auio a_auio)) (a6989586621679128134 :: t_auic a_auio) :: a_auio where
  Foldr1Sym2 a6989586621679128133 a6989586621679128134 = Foldr1 a6989586621679128133 a6989586621679128134
type Foldl1Sym0 :: forall (t_auic :: Type -> Type)
                          a_auip. (~>) ((~>) a_auip ((~>) a_auip a_auip)) ((~>) (t_auic a_auip) a_auip)
data Foldl1Sym0 :: (~>) ((~>) a_auip ((~>) a_auip a_auip)) ((~>) (t_auic a_auip) a_auip)
  where
    Foldl1Sym0KindInference :: SameKind (Apply Foldl1Sym0 arg_auMN) (Foldl1Sym1 arg_auMN) =>
                                Foldl1Sym0 a6989586621679128138
type instance Apply @((~>) a_auip ((~>) a_auip a_auip)) @((~>) (t_auic a_auip) a_auip) Foldl1Sym0 a6989586621679128138 = Foldl1Sym1 a6989586621679128138
instance SuppressUnusedWarnings Foldl1Sym0 where
  suppressUnusedWarnings = snd ((,) Foldl1Sym0KindInference ())
type Foldl1Sym1 :: forall (t_auic :: Type -> Type)
                          a_auip. (~>) a_auip ((~>) a_auip a_auip)
                                  -> (~>) (t_auic a_auip) a_auip
data Foldl1Sym1 (a6989586621679128138 :: (~>) a_auip ((~>) a_auip a_auip)) :: (~>) (t_auic a_auip) a_auip
  where
    Foldl1Sym1KindInference :: SameKind (Apply (Foldl1Sym1 a6989586621679128138) arg_auMN) (Foldl1Sym2 a6989586621679128138 arg_auMN) =>
                                Foldl1Sym1 a6989586621679128138 a6989586621679128139
type instance Apply @(t_auic a_auip) @a_auip (Foldl1Sym1 a6989586621679128138) a6989586621679128139 = Foldl1 a6989586621679128138 a6989586621679128139
instance SuppressUnusedWarnings (Foldl1Sym1 a6989586621679128138) where
  suppressUnusedWarnings = snd ((,) Foldl1Sym1KindInference ())
type Foldl1Sym2 :: forall (t_auic :: Type -> Type)
                          a_auip. (~>) a_auip ((~>) a_auip a_auip) -> t_auic a_auip -> a_auip
type family Foldl1Sym2 @(t_auic :: Type
                                    -> Type) @a_auip (a6989586621679128138 :: (~>) a_auip ((~>) a_auip a_auip)) (a6989586621679128139 :: t_auic a_auip) :: a_auip where
  Foldl1Sym2 a6989586621679128138 a6989586621679128139 = Foldl1 a6989586621679128138 a6989586621679128139
type ToListSym0 :: forall (t_auic :: Type -> Type)
                          a_auiq. (~>) (t_auic a_auiq) [a_auiq]
data ToListSym0 :: (~>) (t_auic a_auiq) [a_auiq]
  where
    ToListSym0KindInference :: SameKind (Apply ToListSym0 arg_auMR) (ToListSym1 arg_auMR) =>
                                ToListSym0 a6989586621679128142
type instance Apply @(t_auic a_auiq) @[a_auiq] ToListSym0 a6989586621679128142 = ToList a6989586621679128142
instance SuppressUnusedWarnings ToListSym0 where
  suppressUnusedWarnings = snd ((,) ToListSym0KindInference ())
type ToListSym1 :: forall (t_auic :: Type -> Type)
                          a_auiq. t_auic a_auiq -> [a_auiq]
type family ToListSym1 @(t_auic :: Type
                                    -> Type) @a_auiq (a6989586621679128142 :: t_auic a_auiq) :: [a_auiq] where
  ToListSym1 a6989586621679128142 = ToList a6989586621679128142
type NullSym0 :: forall (t_auic :: Type -> Type)
                        a_auir. (~>) (t_auic a_auir) Bool
data NullSym0 :: (~>) (t_auic a_auir) Bool
  where
    NullSym0KindInference :: SameKind (Apply NullSym0 arg_auMU) (NullSym1 arg_auMU) =>
                              NullSym0 a6989586621679128145
type instance Apply @(t_auic a_auir) @Bool NullSym0 a6989586621679128145 = Null a6989586621679128145
instance SuppressUnusedWarnings NullSym0 where
  suppressUnusedWarnings = snd ((,) NullSym0KindInference ())
type NullSym1 :: forall (t_auic :: Type -> Type)
                        a_auir. t_auic a_auir -> Bool
type family NullSym1 @(t_auic :: Type
                                  -> Type) @a_auir (a6989586621679128145 :: t_auic a_auir) :: Bool where
  NullSym1 a6989586621679128145 = Null a6989586621679128145
type LengthSym0 :: forall (t_auic :: Type -> Type)
                          a_auis. (~>) (t_auic a_auis) Natural
data LengthSym0 :: (~>) (t_auic a_auis) Natural
  where
    LengthSym0KindInference :: SameKind (Apply LengthSym0 arg_auMX) (LengthSym1 arg_auMX) =>
                                LengthSym0 a6989586621679128148
type instance Apply @(t_auic a_auis) @Natural LengthSym0 a6989586621679128148 = Length a6989586621679128148
instance SuppressUnusedWarnings LengthSym0 where
  suppressUnusedWarnings = snd ((,) LengthSym0KindInference ())
type LengthSym1 :: forall (t_auic :: Type -> Type)
                          a_auis. t_auic a_auis -> Natural
type family LengthSym1 @(t_auic :: Type
                                    -> Type) @a_auis (a6989586621679128148 :: t_auic a_auis) :: Natural where
  LengthSym1 a6989586621679128148 = Length a6989586621679128148
type ElemSym0 :: forall (t_auic :: Type -> Type)
                        a_auit. (~>) a_auit ((~>) (t_auic a_auit) Bool)
data ElemSym0 :: (~>) a_auit ((~>) (t_auic a_auit) Bool)
  where
    ElemSym0KindInference :: SameKind (Apply ElemSym0 arg_auN1) (ElemSym1 arg_auN1) =>
                              ElemSym0 a6989586621679128152
type instance Apply @a_auit @((~>) (t_auic a_auit) Bool) ElemSym0 a6989586621679128152 = ElemSym1 a6989586621679128152
instance SuppressUnusedWarnings ElemSym0 where
  suppressUnusedWarnings = snd ((,) ElemSym0KindInference ())
type ElemSym1 :: forall (t_auic :: Type -> Type) a_auit. a_auit
                                                          -> (~>) (t_auic a_auit) Bool
data ElemSym1 (a6989586621679128152 :: a_auit) :: (~>) (t_auic a_auit) Bool
  where
    ElemSym1KindInference :: SameKind (Apply (ElemSym1 a6989586621679128152) arg_auN1) (ElemSym2 a6989586621679128152 arg_auN1) =>
                              ElemSym1 a6989586621679128152 a6989586621679128153
type instance Apply @(t_auic a_auit) @Bool (ElemSym1 a6989586621679128152) a6989586621679128153 = Elem a6989586621679128152 a6989586621679128153
instance SuppressUnusedWarnings (ElemSym1 a6989586621679128152) where
  suppressUnusedWarnings = snd ((,) ElemSym1KindInference ())
type ElemSym2 :: forall (t_auic :: Type -> Type) a_auit. a_auit
                                                          -> t_auic a_auit -> Bool
type family ElemSym2 @(t_auic :: Type
                                  -> Type) @a_auit (a6989586621679128152 :: a_auit) (a6989586621679128153 :: t_auic a_auit) :: Bool where
  ElemSym2 a6989586621679128152 a6989586621679128153 = Elem a6989586621679128152 a6989586621679128153
type MaximumSym0 :: forall (t_auic :: Type -> Type)
                            a_auiu. (~>) (t_auic a_auiu) a_auiu
data MaximumSym0 :: (~>) (t_auic a_auiu) a_auiu
  where
    MaximumSym0KindInference :: SameKind (Apply MaximumSym0 arg_auN5) (MaximumSym1 arg_auN5) =>
                                MaximumSym0 a6989586621679128156
type instance Apply @(t_auic a_auiu) @a_auiu MaximumSym0 a6989586621679128156 = Maximum a6989586621679128156
instance SuppressUnusedWarnings MaximumSym0 where
  suppressUnusedWarnings = snd ((,) MaximumSym0KindInference ())
type MaximumSym1 :: forall (t_auic :: Type -> Type)
                            a_auiu. t_auic a_auiu -> a_auiu
type family MaximumSym1 @(t_auic :: Type
                                    -> Type) @a_auiu (a6989586621679128156 :: t_auic a_auiu) :: a_auiu where
  MaximumSym1 a6989586621679128156 = Maximum a6989586621679128156
type MinimumSym0 :: forall (t_auic :: Type -> Type)
                            a_auiv. (~>) (t_auic a_auiv) a_auiv
data MinimumSym0 :: (~>) (t_auic a_auiv) a_auiv
  where
    MinimumSym0KindInference :: SameKind (Apply MinimumSym0 arg_auN8) (MinimumSym1 arg_auN8) =>
                                MinimumSym0 a6989586621679128159
type instance Apply @(t_auic a_auiv) @a_auiv MinimumSym0 a6989586621679128159 = Minimum a6989586621679128159
instance SuppressUnusedWarnings MinimumSym0 where
  suppressUnusedWarnings = snd ((,) MinimumSym0KindInference ())
type MinimumSym1 :: forall (t_auic :: Type -> Type)
                            a_auiv. t_auic a_auiv -> a_auiv
type family MinimumSym1 @(t_auic :: Type
                                    -> Type) @a_auiv (a6989586621679128159 :: t_auic a_auiv) :: a_auiv where
  MinimumSym1 a6989586621679128159 = Minimum a6989586621679128159
type SumSym0 :: forall (t_auic :: Type -> Type)
                        a_auiw. (~>) (t_auic a_auiw) a_auiw
data SumSym0 :: (~>) (t_auic a_auiw) a_auiw
  where
    SumSym0KindInference :: SameKind (Apply SumSym0 arg_auNb) (SumSym1 arg_auNb) =>
                            SumSym0 a6989586621679128162
type instance Apply @(t_auic a_auiw) @a_auiw SumSym0 a6989586621679128162 = Sum a6989586621679128162
instance SuppressUnusedWarnings SumSym0 where
  suppressUnusedWarnings = snd ((,) SumSym0KindInference ())
type SumSym1 :: forall (t_auic :: Type -> Type)
                        a_auiw. t_auic a_auiw -> a_auiw
type family SumSym1 @(t_auic :: Type
                                -> Type) @a_auiw (a6989586621679128162 :: t_auic a_auiw) :: a_auiw where
  SumSym1 a6989586621679128162 = Sum a6989586621679128162
type ProductSym0 :: forall (t_auic :: Type -> Type)
                            a_auix. (~>) (t_auic a_auix) a_auix
data ProductSym0 :: (~>) (t_auic a_auix) a_auix
  where
    ProductSym0KindInference :: SameKind (Apply ProductSym0 arg_auNe) (ProductSym1 arg_auNe) =>
                                ProductSym0 a6989586621679128165
type instance Apply @(t_auic a_auix) @a_auix ProductSym0 a6989586621679128165 = Product a6989586621679128165
instance SuppressUnusedWarnings ProductSym0 where
  suppressUnusedWarnings = snd ((,) ProductSym0KindInference ())
type ProductSym1 :: forall (t_auic :: Type -> Type)
                            a_auix. t_auic a_auix -> a_auix
type family ProductSym1 @(t_auic :: Type
                                    -> Type) @a_auix (a6989586621679128165 :: t_auic a_auix) :: a_auix where
  ProductSym1 a6989586621679128165 = Product a6989586621679128165
type Fold_6989586621679128167 :: forall (t_auic :: Type -> Type)
                                        m_auid. t_auic m_auid -> m_auid
type family Fold_6989586621679128167 @(t_auic :: Type
                                                  -> Type) @m_auid (a_auNl :: t_auic m_auid) :: m_auid where
  Fold_6989586621679128167 @t_auic @m_auid (a_6989586621679128169_auNo :: t_auic m_auid) = Apply (Apply FoldMapSym0 IdSym0) a_6989586621679128169_auNo
type FoldMap_6989586621679128177 :: forall (t_auic :: Type -> Type)
                                            a_auif
                                            m_auie. (~>) a_auif m_auie -> t_auic a_auif -> m_auie
type family FoldMap_6989586621679128177 @(t_auic :: Type
                                                    -> Type) @a_auif @m_auie (a_auNv :: (~>) a_auif m_auie) (a_auNw :: t_auic a_auif) :: m_auie where
  FoldMap_6989586621679128177 @t_auic @a_auif @m_auie (f_auNA :: (~>) a_auif m_auie) (a_6989586621679128179_auNB :: t_auic a_auif) = Apply (Apply (Apply FoldrSym0 (Apply (Apply (.@#@$) MappendSym0) f_auNA)) MemptySym0) a_6989586621679128179_auNB
type Foldr_6989586621679128191 :: forall (t_auic :: Type -> Type)
                                          a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> t_auic a_auig -> b_auih
type family Foldr_6989586621679128191 @(t_auic :: Type
                                                  -> Type) @a_auig @b_auih (a_auNH :: (~>) a_auig ((~>) b_auih b_auih)) (a_auNI :: b_auih) (a_auNJ :: t_auic a_auig) :: b_auih where
  Foldr_6989586621679128191 @t_auic @a_auig @b_auih (f_auNO :: (~>) a_auig ((~>) b_auih b_auih)) (z_auNP :: b_auih) (t_auNQ :: t_auic a_auig) = Apply (Apply AppEndoSym0 (Apply (Apply FoldMapSym0 (Apply (Apply (.@#@$) EndoSym0) f_auNO)) t_auNQ)) z_auNP
data Let6989586621679128218F'Sym0 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128215 :: (~>) a6989586621679126246 ((~>) b6989586621679126247 b6989586621679126247)) (z06989586621679128216 :: b6989586621679126247) (xs6989586621679128217 :: t6989586621679126240 a6989586621679126246) a6989586621679128219
  where
    Let6989586621679128218F'Sym0KindInference :: SameKind (Apply (Let6989586621679128218F'Sym0 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217) arg_auOa) (Let6989586621679128218F'Sym1 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 arg_auOa) =>
                                                  Let6989586621679128218F'Sym0 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219
type instance Apply @_ @_ (Let6989586621679128218F'Sym0 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217) a6989586621679128219 = Let6989586621679128218F'Sym1 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219
instance SuppressUnusedWarnings (Let6989586621679128218F'Sym0 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128218F'Sym0KindInference ())
data Let6989586621679128218F'Sym1 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128215 :: (~>) a6989586621679126246 ((~>) b6989586621679126247 b6989586621679126247)) (z06989586621679128216 :: b6989586621679126247) (xs6989586621679128217 :: t6989586621679126240 a6989586621679126246) a6989586621679128219 a6989586621679128220
  where
    Let6989586621679128218F'Sym1KindInference :: SameKind (Apply (Let6989586621679128218F'Sym1 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219) arg_auOa) (Let6989586621679128218F'Sym2 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 arg_auOa) =>
                                                  Let6989586621679128218F'Sym1 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220
type instance Apply @_ @_ (Let6989586621679128218F'Sym1 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219) a6989586621679128220 = Let6989586621679128218F'Sym2 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220
instance SuppressUnusedWarnings (Let6989586621679128218F'Sym1 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128218F'Sym1KindInference ())
data Let6989586621679128218F'Sym2 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128215 :: (~>) a6989586621679126246 ((~>) b6989586621679126247 b6989586621679126247)) (z06989586621679128216 :: b6989586621679126247) (xs6989586621679128217 :: t6989586621679126240 a6989586621679126246) a6989586621679128219 a6989586621679128220 a6989586621679128221
  where
    Let6989586621679128218F'Sym2KindInference :: SameKind (Apply (Let6989586621679128218F'Sym2 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220) arg_auOa) (Let6989586621679128218F'Sym3 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220 arg_auOa) =>
                                                  Let6989586621679128218F'Sym2 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220 a6989586621679128221
type instance Apply @_ @_ (Let6989586621679128218F'Sym2 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220) a6989586621679128221 = Let6989586621679128218F' t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220 a6989586621679128221
instance SuppressUnusedWarnings (Let6989586621679128218F'Sym2 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128218F'Sym2KindInference ())
type family Let6989586621679128218F'Sym3 (t6989586621679126240 :: Type
                                                                  -> Type) (f6989586621679128215 :: (~>) a6989586621679126246 ((~>) b6989586621679126247 b6989586621679126247)) (z06989586621679128216 :: b6989586621679126247) (xs6989586621679128217 :: t6989586621679126240 a6989586621679126246) a6989586621679128219 a6989586621679128220 a6989586621679128221 where
  Let6989586621679128218F'Sym3 t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220 a6989586621679128221 = Let6989586621679128218F' t6989586621679126240 f6989586621679128215 z06989586621679128216 xs6989586621679128217 a6989586621679128219 a6989586621679128220 a6989586621679128221
type family Let6989586621679128218F' (t6989586621679126240 :: Type
                                                              -> Type) (f6989586621679128215 :: (~>) a6989586621679126246 ((~>) b6989586621679126247 b6989586621679126247)) (z06989586621679128216 :: b6989586621679126247) (xs6989586621679128217 :: t6989586621679126240 a6989586621679126246) a_auO7 a_auO8 a_auO9 where
  Let6989586621679128218F' t_auic f_auO3 z0_auO4 xs_auO5 k_auOb x_auOc z_auOd = Apply (Apply ($!@#@$) k_auOb) (Apply (Apply f_auO3 x_auOc) z_auOd)
type Foldr'_6989586621679128206 :: forall (t_auic :: Type -> Type)
                                          a_auii
                                          b_auij. (~>) a_auii ((~>) b_auij b_auij)
                                                  -> b_auij -> t_auic a_auii -> b_auij
type family Foldr'_6989586621679128206 @(t_auic :: Type
                                                    -> Type) @a_auii @b_auij (a_auNW :: (~>) a_auii ((~>) b_auij b_auij)) (a_auNX :: b_auij) (a_auNY :: t_auic a_auii) :: b_auij where
  Foldr'_6989586621679128206 @t_auic @a_auii @b_auij (f_auO3 :: (~>) a_auii ((~>) b_auij b_auij)) (z0_auO4 :: b_auij) (xs_auO5 :: t_auic a_auii) = Apply (Apply (Apply (Apply FoldlSym0 (Let6989586621679128218F'Sym0 t_auic f_auO3 z0_auO4 xs_auO5)) IdSym0) xs_auO5) z0_auO4
type Foldl_6989586621679128229 :: forall (t_auic :: Type -> Type)
                                          b_auik
                                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                                  -> b_auik -> t_auic a_auil -> b_auik
type family Foldl_6989586621679128229 @(t_auic :: Type
                                                  -> Type) @b_auik @a_auil (a_auOj :: (~>) b_auik ((~>) a_auil b_auik)) (a_auOk :: b_auik) (a_auOl :: t_auic a_auil) :: b_auik where
  Foldl_6989586621679128229 @t_auic @b_auik @a_auil (f_auOq :: (~>) b_auik ((~>) a_auil b_auik)) (z_auOr :: b_auik) (t_auOs :: t_auic a_auil) = Apply (Apply AppEndoSym0 (Apply GetDualSym0 (Apply (Apply FoldMapSym0 (Apply (Apply (.@#@$) DualSym0) (Apply (Apply (.@#@$) EndoSym0) (Apply FlipSym0 f_auOq)))) t_auOs))) z_auOr
data Let6989586621679128256F'Sym0 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128253 :: (~>) b6989586621679126250 ((~>) a6989586621679126251 b6989586621679126250)) (z06989586621679128254 :: b6989586621679126250) (xs6989586621679128255 :: t6989586621679126240 a6989586621679126251) a6989586621679128257
  where
    Let6989586621679128256F'Sym0KindInference :: SameKind (Apply (Let6989586621679128256F'Sym0 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255) arg_auOM) (Let6989586621679128256F'Sym1 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 arg_auOM) =>
                                                  Let6989586621679128256F'Sym0 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257
type instance Apply @_ @_ (Let6989586621679128256F'Sym0 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255) a6989586621679128257 = Let6989586621679128256F'Sym1 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257
instance SuppressUnusedWarnings (Let6989586621679128256F'Sym0 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128256F'Sym0KindInference ())
data Let6989586621679128256F'Sym1 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128253 :: (~>) b6989586621679126250 ((~>) a6989586621679126251 b6989586621679126250)) (z06989586621679128254 :: b6989586621679126250) (xs6989586621679128255 :: t6989586621679126240 a6989586621679126251) a6989586621679128257 a6989586621679128258
  where
    Let6989586621679128256F'Sym1KindInference :: SameKind (Apply (Let6989586621679128256F'Sym1 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257) arg_auOM) (Let6989586621679128256F'Sym2 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 arg_auOM) =>
                                                  Let6989586621679128256F'Sym1 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258
type instance Apply @_ @_ (Let6989586621679128256F'Sym1 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257) a6989586621679128258 = Let6989586621679128256F'Sym2 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258
instance SuppressUnusedWarnings (Let6989586621679128256F'Sym1 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128256F'Sym1KindInference ())
data Let6989586621679128256F'Sym2 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128253 :: (~>) b6989586621679126250 ((~>) a6989586621679126251 b6989586621679126250)) (z06989586621679128254 :: b6989586621679126250) (xs6989586621679128255 :: t6989586621679126240 a6989586621679126251) a6989586621679128257 a6989586621679128258 a6989586621679128259
  where
    Let6989586621679128256F'Sym2KindInference :: SameKind (Apply (Let6989586621679128256F'Sym2 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258) arg_auOM) (Let6989586621679128256F'Sym3 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258 arg_auOM) =>
                                                  Let6989586621679128256F'Sym2 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258 a6989586621679128259
type instance Apply @_ @_ (Let6989586621679128256F'Sym2 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258) a6989586621679128259 = Let6989586621679128256F' t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258 a6989586621679128259
instance SuppressUnusedWarnings (Let6989586621679128256F'Sym2 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128256F'Sym2KindInference ())
type family Let6989586621679128256F'Sym3 (t6989586621679126240 :: Type
                                                                  -> Type) (f6989586621679128253 :: (~>) b6989586621679126250 ((~>) a6989586621679126251 b6989586621679126250)) (z06989586621679128254 :: b6989586621679126250) (xs6989586621679128255 :: t6989586621679126240 a6989586621679126251) a6989586621679128257 a6989586621679128258 a6989586621679128259 where
  Let6989586621679128256F'Sym3 t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258 a6989586621679128259 = Let6989586621679128256F' t6989586621679126240 f6989586621679128253 z06989586621679128254 xs6989586621679128255 a6989586621679128257 a6989586621679128258 a6989586621679128259
type family Let6989586621679128256F' (t6989586621679126240 :: Type
                                                              -> Type) (f6989586621679128253 :: (~>) b6989586621679126250 ((~>) a6989586621679126251 b6989586621679126250)) (z06989586621679128254 :: b6989586621679126250) (xs6989586621679128255 :: t6989586621679126240 a6989586621679126251) a_auOJ a_auOK a_auOL where
  Let6989586621679128256F' t_auic f_auOF z0_auOG xs_auOH x_auON k_auOO z_auOP = Apply (Apply ($!@#@$) k_auOO) (Apply (Apply f_auOF z_auOP) x_auON)
type Foldl'_6989586621679128244 :: forall (t_auic :: Type -> Type)
                                          b_auim
                                          a_auin. (~>) b_auim ((~>) a_auin b_auim)
                                                  -> b_auim -> t_auic a_auin -> b_auim
type family Foldl'_6989586621679128244 @(t_auic :: Type
                                                    -> Type) @b_auim @a_auin (a_auOy :: (~>) b_auim ((~>) a_auin b_auim)) (a_auOz :: b_auim) (a_auOA :: t_auic a_auin) :: b_auim where
  Foldl'_6989586621679128244 @t_auic @b_auim @a_auin (f_auOF :: (~>) b_auim ((~>) a_auin b_auim)) (z0_auOG :: b_auim) (xs_auOH :: t_auic a_auin) = Apply (Apply (Apply (Apply FoldrSym0 (Let6989586621679128256F'Sym0 t_auic f_auOF z0_auOG xs_auOH)) IdSym0) xs_auOH) z0_auOG
type family LamCases_6989586621679128281_auP8 (t6989586621679126240 :: Type
                                                                        -> Type) x6989586621679128279 m6989586621679128280 (f6989586621679128273 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) (xs6989586621679128274 :: t6989586621679126240 a6989586621679126252) a_6989586621679128284_auPb where
  LamCases_6989586621679128281_auP8 t_auic x_auP5 m_auP6 f_auOZ xs_auP0 'Nothing = x_auP5
  LamCases_6989586621679128281_auP8 t_auic x_auP5 m_auP6 f_auOZ xs_auP0 ('Just y_auP9) = Apply (Apply f_auOZ x_auP5) y_auP9
data LamCases_6989586621679128281Sym0 (t6989586621679126240 :: Type
                                                                -> Type) x6989586621679128279 m6989586621679128280 (f6989586621679128273 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) (xs6989586621679128274 :: t6989586621679126240 a6989586621679126252) a_69895866216791282846989586621679128285
  where
    LamCases_6989586621679128281Sym0KindInference :: SameKind (Apply (LamCases_6989586621679128281Sym0 t6989586621679126240 x6989586621679128279 m6989586621679128280 f6989586621679128273 xs6989586621679128274) arg_auPc) (LamCases_6989586621679128281Sym1 t6989586621679126240 x6989586621679128279 m6989586621679128280 f6989586621679128273 xs6989586621679128274 arg_auPc) =>
                                                      LamCases_6989586621679128281Sym0 t6989586621679126240 x6989586621679128279 m6989586621679128280 f6989586621679128273 xs6989586621679128274 a_69895866216791282846989586621679128285
type instance Apply @_ @_ (LamCases_6989586621679128281Sym0 t6989586621679126240 x6989586621679128279 m6989586621679128280 f6989586621679128273 xs6989586621679128274) a_69895866216791282846989586621679128285 = LamCases_6989586621679128281_auP8 t6989586621679126240 x6989586621679128279 m6989586621679128280 f6989586621679128273 xs6989586621679128274 a_69895866216791282846989586621679128285
instance SuppressUnusedWarnings (LamCases_6989586621679128281Sym0 t6989586621679126240 x6989586621679128279 m6989586621679128280 f6989586621679128273 xs6989586621679128274) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679128281Sym0KindInference ())
type family LamCases_6989586621679128281Sym1 (t6989586621679126240 :: Type
                                                                      -> Type) x6989586621679128279 m6989586621679128280 (f6989586621679128273 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) (xs6989586621679128274 :: t6989586621679126240 a6989586621679126252) a_69895866216791282846989586621679128285 where
  LamCases_6989586621679128281Sym1 t6989586621679126240 x6989586621679128279 m6989586621679128280 f6989586621679128273 xs6989586621679128274 a_69895866216791282846989586621679128285 = LamCases_6989586621679128281_auP8 t6989586621679126240 x6989586621679128279 m6989586621679128280 f6989586621679128273 xs6989586621679128274 a_69895866216791282846989586621679128285
data Let6989586621679128275MfSym0 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128273 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) (xs6989586621679128274 :: t6989586621679126240 a6989586621679126252) a6989586621679128276
  where
    Let6989586621679128275MfSym0KindInference :: SameKind (Apply (Let6989586621679128275MfSym0 t6989586621679126240 f6989586621679128273 xs6989586621679128274) arg_auP4) (Let6989586621679128275MfSym1 t6989586621679126240 f6989586621679128273 xs6989586621679128274 arg_auP4) =>
                                                  Let6989586621679128275MfSym0 t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276
type instance Apply @_ @_ (Let6989586621679128275MfSym0 t6989586621679126240 f6989586621679128273 xs6989586621679128274) a6989586621679128276 = Let6989586621679128275MfSym1 t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276
instance SuppressUnusedWarnings (Let6989586621679128275MfSym0 t6989586621679126240 f6989586621679128273 xs6989586621679128274) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128275MfSym0KindInference ())
data Let6989586621679128275MfSym1 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128273 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) (xs6989586621679128274 :: t6989586621679126240 a6989586621679126252) a6989586621679128276 a6989586621679128277
  where
    Let6989586621679128275MfSym1KindInference :: SameKind (Apply (Let6989586621679128275MfSym1 t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276) arg_auP4) (Let6989586621679128275MfSym2 t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276 arg_auP4) =>
                                                  Let6989586621679128275MfSym1 t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276 a6989586621679128277
type instance Apply @_ @_ (Let6989586621679128275MfSym1 t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276) a6989586621679128277 = Let6989586621679128275Mf t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276 a6989586621679128277
instance SuppressUnusedWarnings (Let6989586621679128275MfSym1 t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128275MfSym1KindInference ())
type family Let6989586621679128275MfSym2 (t6989586621679126240 :: Type
                                                                  -> Type) (f6989586621679128273 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) (xs6989586621679128274 :: t6989586621679126240 a6989586621679126252) a6989586621679128276 a6989586621679128277 where
  Let6989586621679128275MfSym2 t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276 a6989586621679128277 = Let6989586621679128275Mf t6989586621679126240 f6989586621679128273 xs6989586621679128274 a6989586621679128276 a6989586621679128277
type family Let6989586621679128275Mf (t6989586621679126240 :: Type
                                                              -> Type) (f6989586621679128273 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) (xs6989586621679128274 :: t6989586621679126240 a6989586621679126252) a_auP2 a_auP3 where
  Let6989586621679128275Mf t_auic f_auOZ xs_auP0 x_auP5 m_auP6 = Apply JustSym0 (Apply (LamCases_6989586621679128281Sym0 t_auic x_auP5 m_auP6 f_auOZ xs_auP0) m_auP6)
type Foldr1_6989586621679128266 :: forall (t_auic :: Type -> Type)
                                          a_auio. (~>) a_auio ((~>) a_auio a_auio)
                                                  -> t_auic a_auio -> a_auio
type family Foldr1_6989586621679128266 @(t_auic :: Type
                                                    -> Type) @a_auio (a_auOU :: (~>) a_auio ((~>) a_auio a_auio)) (a_auOV :: t_auic a_auio) :: a_auio where
  Foldr1_6989586621679128266 @t_auic @a_auio (f_auOZ :: (~>) a_auio ((~>) a_auio a_auio)) (xs_auP0 :: t_auic a_auio) = Apply (Apply FromMaybeSym0 (Apply ErrorWithoutStackTraceSym0 "foldr1: empty structure")) (Apply (Apply (Apply FoldrSym0 (Let6989586621679128275MfSym0 t_auic f_auOZ xs_auP0)) NothingSym0) xs_auP0)
type family LamCases_6989586621679128304_auPv (t6989586621679126240 :: Type
                                                                        -> Type) m6989586621679128302 y6989586621679128303 (f6989586621679128296 :: (~>) a6989586621679126253 ((~>) a6989586621679126253 a6989586621679126253)) (xs6989586621679128297 :: t6989586621679126240 a6989586621679126253) a_6989586621679128307_auPy where
  LamCases_6989586621679128304_auPv t_auic m_auPs y_auPt f_auPm xs_auPn 'Nothing = y_auPt
  LamCases_6989586621679128304_auPv t_auic m_auPs y_auPt f_auPm xs_auPn ('Just x_auPw) = Apply (Apply f_auPm x_auPw) y_auPt
data LamCases_6989586621679128304Sym0 (t6989586621679126240 :: Type
                                                                -> Type) m6989586621679128302 y6989586621679128303 (f6989586621679128296 :: (~>) a6989586621679126253 ((~>) a6989586621679126253 a6989586621679126253)) (xs6989586621679128297 :: t6989586621679126240 a6989586621679126253) a_69895866216791283076989586621679128308
  where
    LamCases_6989586621679128304Sym0KindInference :: SameKind (Apply (LamCases_6989586621679128304Sym0 t6989586621679126240 m6989586621679128302 y6989586621679128303 f6989586621679128296 xs6989586621679128297) arg_auPz) (LamCases_6989586621679128304Sym1 t6989586621679126240 m6989586621679128302 y6989586621679128303 f6989586621679128296 xs6989586621679128297 arg_auPz) =>
                                                      LamCases_6989586621679128304Sym0 t6989586621679126240 m6989586621679128302 y6989586621679128303 f6989586621679128296 xs6989586621679128297 a_69895866216791283076989586621679128308
type instance Apply @_ @_ (LamCases_6989586621679128304Sym0 t6989586621679126240 m6989586621679128302 y6989586621679128303 f6989586621679128296 xs6989586621679128297) a_69895866216791283076989586621679128308 = LamCases_6989586621679128304_auPv t6989586621679126240 m6989586621679128302 y6989586621679128303 f6989586621679128296 xs6989586621679128297 a_69895866216791283076989586621679128308
instance SuppressUnusedWarnings (LamCases_6989586621679128304Sym0 t6989586621679126240 m6989586621679128302 y6989586621679128303 f6989586621679128296 xs6989586621679128297) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679128304Sym0KindInference ())
type family LamCases_6989586621679128304Sym1 (t6989586621679126240 :: Type
                                                                      -> Type) m6989586621679128302 y6989586621679128303 (f6989586621679128296 :: (~>) a6989586621679126253 ((~>) a6989586621679126253 a6989586621679126253)) (xs6989586621679128297 :: t6989586621679126240 a6989586621679126253) a_69895866216791283076989586621679128308 where
  LamCases_6989586621679128304Sym1 t6989586621679126240 m6989586621679128302 y6989586621679128303 f6989586621679128296 xs6989586621679128297 a_69895866216791283076989586621679128308 = LamCases_6989586621679128304_auPv t6989586621679126240 m6989586621679128302 y6989586621679128303 f6989586621679128296 xs6989586621679128297 a_69895866216791283076989586621679128308
data Let6989586621679128298MfSym0 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128296 :: (~>) a6989586621679126253 ((~>) a6989586621679126253 a6989586621679126253)) (xs6989586621679128297 :: t6989586621679126240 a6989586621679126253) a6989586621679128299
  where
    Let6989586621679128298MfSym0KindInference :: SameKind (Apply (Let6989586621679128298MfSym0 t6989586621679126240 f6989586621679128296 xs6989586621679128297) arg_auPr) (Let6989586621679128298MfSym1 t6989586621679126240 f6989586621679128296 xs6989586621679128297 arg_auPr) =>
                                                  Let6989586621679128298MfSym0 t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299
type instance Apply @_ @_ (Let6989586621679128298MfSym0 t6989586621679126240 f6989586621679128296 xs6989586621679128297) a6989586621679128299 = Let6989586621679128298MfSym1 t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299
instance SuppressUnusedWarnings (Let6989586621679128298MfSym0 t6989586621679126240 f6989586621679128296 xs6989586621679128297) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128298MfSym0KindInference ())
data Let6989586621679128298MfSym1 (t6989586621679126240 :: Type
                                                            -> Type) (f6989586621679128296 :: (~>) a6989586621679126253 ((~>) a6989586621679126253 a6989586621679126253)) (xs6989586621679128297 :: t6989586621679126240 a6989586621679126253) a6989586621679128299 a6989586621679128300
  where
    Let6989586621679128298MfSym1KindInference :: SameKind (Apply (Let6989586621679128298MfSym1 t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299) arg_auPr) (Let6989586621679128298MfSym2 t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299 arg_auPr) =>
                                                  Let6989586621679128298MfSym1 t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299 a6989586621679128300
type instance Apply @_ @_ (Let6989586621679128298MfSym1 t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299) a6989586621679128300 = Let6989586621679128298Mf t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299 a6989586621679128300
instance SuppressUnusedWarnings (Let6989586621679128298MfSym1 t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128298MfSym1KindInference ())
type family Let6989586621679128298MfSym2 (t6989586621679126240 :: Type
                                                                  -> Type) (f6989586621679128296 :: (~>) a6989586621679126253 ((~>) a6989586621679126253 a6989586621679126253)) (xs6989586621679128297 :: t6989586621679126240 a6989586621679126253) a6989586621679128299 a6989586621679128300 where
  Let6989586621679128298MfSym2 t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299 a6989586621679128300 = Let6989586621679128298Mf t6989586621679126240 f6989586621679128296 xs6989586621679128297 a6989586621679128299 a6989586621679128300
type family Let6989586621679128298Mf (t6989586621679126240 :: Type
                                                              -> Type) (f6989586621679128296 :: (~>) a6989586621679126253 ((~>) a6989586621679126253 a6989586621679126253)) (xs6989586621679128297 :: t6989586621679126240 a6989586621679126253) a_auPp a_auPq where
  Let6989586621679128298Mf t_auic f_auPm xs_auPn m_auPs y_auPt = Apply JustSym0 (Apply (LamCases_6989586621679128304Sym0 t_auic m_auPs y_auPt f_auPm xs_auPn) m_auPs)
type Foldl1_6989586621679128289 :: forall (t_auic :: Type -> Type)
                                          a_auip. (~>) a_auip ((~>) a_auip a_auip)
                                                  -> t_auic a_auip -> a_auip
type family Foldl1_6989586621679128289 @(t_auic :: Type
                                                    -> Type) @a_auip (a_auPh :: (~>) a_auip ((~>) a_auip a_auip)) (a_auPi :: t_auic a_auip) :: a_auip where
  Foldl1_6989586621679128289 @t_auic @a_auip (f_auPm :: (~>) a_auip ((~>) a_auip a_auip)) (xs_auPn :: t_auic a_auip) = Apply (Apply FromMaybeSym0 (Apply ErrorWithoutStackTraceSym0 "foldl1: empty structure")) (Apply (Apply (Apply FoldlSym0 (Let6989586621679128298MfSym0 t_auic f_auPm xs_auPn)) NothingSym0) xs_auPn)
type ToList_6989586621679128311 :: forall (t_auic :: Type -> Type)
                                          a_auiq. t_auic a_auiq -> [a_auiq]
type family ToList_6989586621679128311 @(t_auic :: Type
                                                    -> Type) @a_auiq (a_auPF :: t_auic a_auiq) :: [a_auiq] where
  ToList_6989586621679128311 @t_auic @a_auiq (a_6989586621679128313_auPI :: t_auic a_auiq) = Apply (Apply (Apply FoldrSym0 (:@#@$)) NilSym0) a_6989586621679128313_auPI
type family LamCases_6989586621679128328_auPT (t6989586621679126240 :: Type
                                                                        -> Type) (a_69895866216791283226989586621679128327 :: t6989586621679126240 a6989586621679126255) a_6989586621679128330_auPV a_6989586621679128332_auPX where
  LamCases_6989586621679128328_auPT t_auic a_6989586621679128322_auPR _ _ = FalseSym0
data LamCases_6989586621679128328Sym0 (t6989586621679126240 :: Type
                                                                -> Type) (a_69895866216791283226989586621679128327 :: t6989586621679126240 a6989586621679126255) a_69895866216791283306989586621679128331
  where
    LamCases_6989586621679128328Sym0KindInference :: SameKind (Apply (LamCases_6989586621679128328Sym0 t6989586621679126240 a_69895866216791283226989586621679128327) arg_auPY) (LamCases_6989586621679128328Sym1 t6989586621679126240 a_69895866216791283226989586621679128327 arg_auPY) =>
                                                      LamCases_6989586621679128328Sym0 t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331
type instance Apply @_ @_ (LamCases_6989586621679128328Sym0 t6989586621679126240 a_69895866216791283226989586621679128327) a_69895866216791283306989586621679128331 = LamCases_6989586621679128328Sym1 t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331
instance SuppressUnusedWarnings (LamCases_6989586621679128328Sym0 t6989586621679126240 a_69895866216791283226989586621679128327) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679128328Sym0KindInference ())
data LamCases_6989586621679128328Sym1 (t6989586621679126240 :: Type
                                                                -> Type) (a_69895866216791283226989586621679128327 :: t6989586621679126240 a6989586621679126255) a_69895866216791283306989586621679128331 a_69895866216791283326989586621679128333
  where
    LamCases_6989586621679128328Sym1KindInference :: SameKind (Apply (LamCases_6989586621679128328Sym1 t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331) arg_auPY) (LamCases_6989586621679128328Sym2 t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331 arg_auPY) =>
                                                      LamCases_6989586621679128328Sym1 t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331 a_69895866216791283326989586621679128333
type instance Apply @_ @_ (LamCases_6989586621679128328Sym1 t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331) a_69895866216791283326989586621679128333 = LamCases_6989586621679128328_auPT t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331 a_69895866216791283326989586621679128333
instance SuppressUnusedWarnings (LamCases_6989586621679128328Sym1 t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679128328Sym1KindInference ())
type family LamCases_6989586621679128328Sym2 (t6989586621679126240 :: Type
                                                                      -> Type) (a_69895866216791283226989586621679128327 :: t6989586621679126240 a6989586621679126255) a_69895866216791283306989586621679128331 a_69895866216791283326989586621679128333 where
  LamCases_6989586621679128328Sym2 t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331 a_69895866216791283326989586621679128333 = LamCases_6989586621679128328_auPT t6989586621679126240 a_69895866216791283226989586621679128327 a_69895866216791283306989586621679128331 a_69895866216791283326989586621679128333
type Null_6989586621679128320 :: forall (t_auic :: Type -> Type)
                                        a_auir. t_auic a_auir -> Bool
type family Null_6989586621679128320 @(t_auic :: Type
                                                  -> Type) @a_auir (a_auPO :: t_auic a_auir) :: Bool where
  Null_6989586621679128320 @t_auic @a_auir (a_6989586621679128322_auPR :: t_auic a_auir) = Apply (Apply (Apply FoldrSym0 (LamCases_6989586621679128328Sym0 t_auic a_6989586621679128322_auPR)) TrueSym0) a_6989586621679128322_auPR
type family LamCases_6989586621679128344_auQ9 (t6989586621679126240 :: Type
                                                                        -> Type) (a_69895866216791283386989586621679128343 :: t6989586621679126240 a6989586621679126256) a_6989586621679128347_auQc a_6989586621679128349_auQe where
  LamCases_6989586621679128344_auQ9 t_auic a_6989586621679128338_auQ7 c_auQa _ = Apply (Apply (+@#@$) c_auQa) (FromInteger 1)
data LamCases_6989586621679128344Sym0 (t6989586621679126240 :: Type
                                                                -> Type) (a_69895866216791283386989586621679128343 :: t6989586621679126240 a6989586621679126256) a_69895866216791283476989586621679128348
  where
    LamCases_6989586621679128344Sym0KindInference :: SameKind (Apply (LamCases_6989586621679128344Sym0 t6989586621679126240 a_69895866216791283386989586621679128343) arg_auQf) (LamCases_6989586621679128344Sym1 t6989586621679126240 a_69895866216791283386989586621679128343 arg_auQf) =>
                                                      LamCases_6989586621679128344Sym0 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348
type instance Apply @_ @_ (LamCases_6989586621679128344Sym0 t6989586621679126240 a_69895866216791283386989586621679128343) a_69895866216791283476989586621679128348 = LamCases_6989586621679128344Sym1 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348
instance SuppressUnusedWarnings (LamCases_6989586621679128344Sym0 t6989586621679126240 a_69895866216791283386989586621679128343) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679128344Sym0KindInference ())
data LamCases_6989586621679128344Sym1 (t6989586621679126240 :: Type
                                                                -> Type) (a_69895866216791283386989586621679128343 :: t6989586621679126240 a6989586621679126256) a_69895866216791283476989586621679128348 a_69895866216791283496989586621679128350
  where
    LamCases_6989586621679128344Sym1KindInference :: SameKind (Apply (LamCases_6989586621679128344Sym1 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348) arg_auQf) (LamCases_6989586621679128344Sym2 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348 arg_auQf) =>
                                                      LamCases_6989586621679128344Sym1 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348 a_69895866216791283496989586621679128350
type instance Apply @_ @_ (LamCases_6989586621679128344Sym1 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348) a_69895866216791283496989586621679128350 = LamCases_6989586621679128344_auQ9 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348 a_69895866216791283496989586621679128350
instance SuppressUnusedWarnings (LamCases_6989586621679128344Sym1 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679128344Sym1KindInference ())
type family LamCases_6989586621679128344Sym2 (t6989586621679126240 :: Type
                                                                      -> Type) (a_69895866216791283386989586621679128343 :: t6989586621679126240 a6989586621679126256) a_69895866216791283476989586621679128348 a_69895866216791283496989586621679128350 where
  LamCases_6989586621679128344Sym2 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348 a_69895866216791283496989586621679128350 = LamCases_6989586621679128344_auQ9 t6989586621679126240 a_69895866216791283386989586621679128343 a_69895866216791283476989586621679128348 a_69895866216791283496989586621679128350
type Length_6989586621679128336 :: forall (t_auic :: Type -> Type)
                                          a_auis. t_auic a_auis -> Natural
type family Length_6989586621679128336 @(t_auic :: Type
                                                    -> Type) @a_auis (a_auQ4 :: t_auic a_auis) :: Natural where
  Length_6989586621679128336 @t_auic @a_auis (a_6989586621679128338_auQ7 :: t_auic a_auis) = Apply (Apply (Apply Foldl'Sym0 (LamCases_6989586621679128344Sym0 t_auic a_6989586621679128338_auQ7)) (FromInteger 0)) a_6989586621679128338_auQ7
type Elem_6989586621679128354 :: forall (t_auic :: Type -> Type)
                                        a_auit. a_auit -> t_auic a_auit -> Bool
type family Elem_6989586621679128354 @(t_auic :: Type
                                                  -> Type) @a_auit (a_auQo :: a_auit) (a_auQp :: t_auic a_auit) :: Bool where
  Elem_6989586621679128354 @t_auic @a_auit (a_6989586621679128356_auQt :: a_auit) (a_6989586621679128358_auQu :: t_auic a_auit) = Apply (Apply (Apply (Apply (.@#@$) AnySym0) (==@#@$)) a_6989586621679128356_auQt) a_6989586621679128358_auQu
data Let6989586621679128376MkJustSym0 (t6989586621679126240 :: Type
                                                                -> Type) a6989586621679126258 (a_69895866216791283706989586621679128375 :: t6989586621679126240 a6989586621679126258) :: (~>) a6989586621679126258 (Maybe a6989586621679126258)
  where
    Let6989586621679128376MkJustSym0KindInference :: SameKind (Apply (Let6989586621679128376MkJustSym0 t6989586621679126240 a6989586621679126258 a_69895866216791283706989586621679128375) arg_auQI) (Let6989586621679128376MkJustSym1 t6989586621679126240 a6989586621679126258 a_69895866216791283706989586621679128375 arg_auQI) =>
                                                      Let6989586621679128376MkJustSym0 t6989586621679126240 a6989586621679126258 a_69895866216791283706989586621679128375 a6989586621679128379
type instance Apply @a6989586621679126258 @(Maybe a6989586621679126258) (Let6989586621679128376MkJustSym0 t6989586621679126240 a6989586621679126258 a_69895866216791283706989586621679128375) a6989586621679128379 = Let6989586621679128376MkJust t6989586621679126240 a6989586621679126258 a_69895866216791283706989586621679128375 a6989586621679128379
instance SuppressUnusedWarnings (Let6989586621679128376MkJustSym0 t6989586621679126240 a6989586621679126258 a_69895866216791283706989586621679128375) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128376MkJustSym0KindInference ())
type family Let6989586621679128376MkJustSym1 (t6989586621679126240 :: Type
                                                                      -> Type) a6989586621679126258 (a_69895866216791283706989586621679128375 :: t6989586621679126240 a6989586621679126258) (a6989586621679128379 :: a6989586621679126258) :: Maybe a6989586621679126258 where
  Let6989586621679128376MkJustSym1 t6989586621679126240 a6989586621679126258 a_69895866216791283706989586621679128375 a6989586621679128379 = Let6989586621679128376MkJust t6989586621679126240 a6989586621679126258 a_69895866216791283706989586621679128375 a6989586621679128379
type family Let6989586621679128376MkJust (t6989586621679126240 :: Type
                                                                  -> Type) a6989586621679126258 (a_69895866216791283706989586621679128375 :: t6989586621679126240 a6989586621679126258) (a_auQH :: a6989586621679126258) :: Maybe a6989586621679126258 where
  Let6989586621679128376MkJust t_auic a_auiu a_6989586621679128370_auQD a_6989586621679128377_auQJ = Apply JustSym0 a_6989586621679128377_auQJ
type Maximum_6989586621679128368 :: forall (t_auic :: Type -> Type)
                                            a_auiu. t_auic a_auiu -> a_auiu
type family Maximum_6989586621679128368 @(t_auic :: Type
                                                    -> Type) @a_auiu (a_auQA :: t_auic a_auiu) :: a_auiu where
  Maximum_6989586621679128368 @t_auic @a_auiu (a_6989586621679128370_auQD :: t_auic a_auiu) = Apply (Apply (Apply (.@#@$) (Apply FromMaybeSym0 (Apply ErrorWithoutStackTraceSym0 "maximum: empty structure"))) (Apply (Apply (.@#@$) GetMaxInternalSym0) (Apply FoldMapSym0 (Apply (Apply (.@#@$) MaxInternalSym0) (Let6989586621679128376MkJustSym0 t_auic a_auiu a_6989586621679128370_auQD))))) a_6989586621679128370_auQD
data Let6989586621679128391MkJustSym0 (t6989586621679126240 :: Type
                                                                -> Type) a6989586621679126259 (a_69895866216791283856989586621679128390 :: t6989586621679126240 a6989586621679126259) :: (~>) a6989586621679126259 (Maybe a6989586621679126259)
  where
    Let6989586621679128391MkJustSym0KindInference :: SameKind (Apply (Let6989586621679128391MkJustSym0 t6989586621679126240 a6989586621679126259 a_69895866216791283856989586621679128390) arg_auQX) (Let6989586621679128391MkJustSym1 t6989586621679126240 a6989586621679126259 a_69895866216791283856989586621679128390 arg_auQX) =>
                                                      Let6989586621679128391MkJustSym0 t6989586621679126240 a6989586621679126259 a_69895866216791283856989586621679128390 a6989586621679128394
type instance Apply @a6989586621679126259 @(Maybe a6989586621679126259) (Let6989586621679128391MkJustSym0 t6989586621679126240 a6989586621679126259 a_69895866216791283856989586621679128390) a6989586621679128394 = Let6989586621679128391MkJust t6989586621679126240 a6989586621679126259 a_69895866216791283856989586621679128390 a6989586621679128394
instance SuppressUnusedWarnings (Let6989586621679128391MkJustSym0 t6989586621679126240 a6989586621679126259 a_69895866216791283856989586621679128390) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128391MkJustSym0KindInference ())
type family Let6989586621679128391MkJustSym1 (t6989586621679126240 :: Type
                                                                      -> Type) a6989586621679126259 (a_69895866216791283856989586621679128390 :: t6989586621679126240 a6989586621679126259) (a6989586621679128394 :: a6989586621679126259) :: Maybe a6989586621679126259 where
  Let6989586621679128391MkJustSym1 t6989586621679126240 a6989586621679126259 a_69895866216791283856989586621679128390 a6989586621679128394 = Let6989586621679128391MkJust t6989586621679126240 a6989586621679126259 a_69895866216791283856989586621679128390 a6989586621679128394
type family Let6989586621679128391MkJust (t6989586621679126240 :: Type
                                                                  -> Type) a6989586621679126259 (a_69895866216791283856989586621679128390 :: t6989586621679126240 a6989586621679126259) (a_auQW :: a6989586621679126259) :: Maybe a6989586621679126259 where
  Let6989586621679128391MkJust t_auic a_auiv a_6989586621679128385_auQS a_6989586621679128392_auQY = Apply JustSym0 a_6989586621679128392_auQY
type Minimum_6989586621679128383 :: forall (t_auic :: Type -> Type)
                                            a_auiv. t_auic a_auiv -> a_auiv
type family Minimum_6989586621679128383 @(t_auic :: Type
                                                    -> Type) @a_auiv (a_auQP :: t_auic a_auiv) :: a_auiv where
  Minimum_6989586621679128383 @t_auic @a_auiv (a_6989586621679128385_auQS :: t_auic a_auiv) = Apply (Apply (Apply (.@#@$) (Apply FromMaybeSym0 (Apply ErrorWithoutStackTraceSym0 "minimum: empty structure"))) (Apply (Apply (.@#@$) GetMinInternalSym0) (Apply FoldMapSym0 (Apply (Apply (.@#@$) MinInternalSym0) (Let6989586621679128391MkJustSym0 t_auic a_auiv a_6989586621679128385_auQS))))) a_6989586621679128385_auQS
type Sum_6989586621679128398 :: forall (t_auic :: Type -> Type)
                                        a_auiw. t_auic a_auiw -> a_auiw
type family Sum_6989586621679128398 @(t_auic :: Type
                                                -> Type) @a_auiw (a_auR4 :: t_auic a_auiw) :: a_auiw where
  Sum_6989586621679128398 @t_auic @a_auiw (a_6989586621679128400_auR7 :: t_auic a_auiw) = Apply (Apply (Apply (.@#@$) GetSumSym0) (Apply FoldMapSym0 Sum_Sym0)) a_6989586621679128400_auR7
type Product_6989586621679128407 :: forall (t_auic :: Type -> Type)
                                            a_auix. t_auic a_auix -> a_auix
type family Product_6989586621679128407 @(t_auic :: Type
                                                    -> Type) @a_auix (a_auRd :: t_auic a_auix) :: a_auix where
  Product_6989586621679128407 @t_auic @a_auix (a_6989586621679128409_auRg :: t_auic a_auix) = Apply (Apply (Apply (.@#@$) GetProductSym0) (Apply FoldMapSym0 Product_Sym0)) a_6989586621679128409_auRg
type PFoldable :: (Type -> Type) -> Constraint
class PFoldable t_auic where
  type family Fold (arg_auM6 :: t_auic m_auid) :: m_auid
  type family FoldMap (arg_auM9 :: (~>) a_auif m_auie) (arg_auMa :: t_auic a_auif) :: m_auie
  type family Foldr (arg_auMe :: (~>) a_auig ((~>) b_auih b_auih)) (arg_auMf :: b_auih) (arg_auMg :: t_auic a_auig) :: b_auih
  type family Foldr' (arg_auMl :: (~>) a_auii ((~>) b_auij b_auij)) (arg_auMm :: b_auij) (arg_auMn :: t_auic a_auii) :: b_auij
  type family Foldl (arg_auMs :: (~>) b_auik ((~>) a_auil b_auik)) (arg_auMt :: b_auik) (arg_auMu :: t_auic a_auil) :: b_auik
  type family Foldl' (arg_auMz :: (~>) b_auim ((~>) a_auin b_auim)) (arg_auMA :: b_auim) (arg_auMB :: t_auic a_auin) :: b_auim
  type family Foldr1 (arg_auMG :: (~>) a_auio ((~>) a_auio a_auio)) (arg_auMH :: t_auic a_auio) :: a_auio
  type family Foldl1 (arg_auML :: (~>) a_auip ((~>) a_auip a_auip)) (arg_auMM :: t_auic a_auip) :: a_auip
  type family ToList (arg_auMQ :: t_auic a_auiq) :: [a_auiq]
  type family Null (arg_auMT :: t_auic a_auir) :: Bool
  type family Length (arg_auMW :: t_auic a_auis) :: Natural
  type family Elem (arg_auMZ :: a_auit) (arg_auN0 :: t_auic a_auit) :: Bool
  type family Maximum (arg_auN4 :: t_auic a_auiu) :: a_auiu
  type family Minimum (arg_auN7 :: t_auic a_auiv) :: a_auiv
  type family Sum (arg_auNa :: t_auic a_auiw) :: a_auiw
  type family Product (arg_auNd :: t_auic a_auix) :: a_auix
  type Fold a_auNg = Fold_6989586621679128167 a_auNg
  type FoldMap a_auNp a_auNq = FoldMap_6989586621679128177 a_auNp a_auNq
  type Foldr a_auNC a_auND a_auNE = Foldr_6989586621679128191 a_auNC a_auND a_auNE
  type Foldr' a_auNR a_auNS a_auNT = Foldr'_6989586621679128206 a_auNR a_auNS a_auNT
  type Foldl a_auOe a_auOf a_auOg = Foldl_6989586621679128229 a_auOe a_auOf a_auOg
  type Foldl' a_auOt a_auOu a_auOv = Foldl'_6989586621679128244 a_auOt a_auOu a_auOv
  type Foldr1 a_auOQ a_auOR = Foldr1_6989586621679128266 a_auOQ a_auOR
  type Foldl1 a_auPd a_auPe = Foldl1_6989586621679128289 a_auPd a_auPe
  type ToList a_auPA = ToList_6989586621679128311 a_auPA
  type Null a_auPJ = Null_6989586621679128320 a_auPJ
  type Length a_auPZ = Length_6989586621679128336 a_auPZ
  type Elem a_auQg a_auQh = Elem_6989586621679128354 a_auQg a_auQh
  type Maximum a_auQv = Maximum_6989586621679128368 a_auQv
  type Minimum a_auQK = Minimum_6989586621679128383 a_auQK
  type Sum a_auQZ = Sum_6989586621679128398 a_auQZ
  type Product a_auR8 = Product_6989586621679128407 a_auR8
type FoldMap_6989586621679128417 :: forall a_auif
                                            m_auie. (~>) a_auif m_auie -> Maybe a_auif -> m_auie
type family FoldMap_6989586621679128417 @a_auif @m_auie (a_auRp :: (~>) a_auif m_auie) (a_auRq :: Maybe a_auif) :: m_auie where
  FoldMap_6989586621679128417 @a_auif @m_auie a_6989586621679128419_auRu a_6989586621679128421_auRv = Apply (Apply (Apply Maybe_Sym0 MemptySym0) a_6989586621679128419_auRu) a_6989586621679128421_auRv
type Foldr_6989586621679128433 :: forall a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> Maybe a_auig -> b_auih
type family Foldr_6989586621679128433 @a_auig @b_auih (a_auRB :: (~>) a_auig ((~>) b_auih b_auih)) (a_auRC :: b_auih) (a_auRD :: Maybe a_auig) :: b_auih where
  Foldr_6989586621679128433 @a_auig @b_auih _ z_auRI 'Nothing = z_auRI
  Foldr_6989586621679128433 @a_auig @b_auih f_auRJ z_auRK ('Just x_auRL) = Apply (Apply f_auRJ x_auRL) z_auRK
type Foldl_6989586621679128449 :: forall b_auik
                                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                                  -> b_auik -> Maybe a_auil -> b_auik
type family Foldl_6989586621679128449 @b_auik @a_auil (a_auRR :: (~>) b_auik ((~>) a_auil b_auik)) (a_auRS :: b_auik) (a_auRT :: Maybe a_auil) :: b_auik where
  Foldl_6989586621679128449 @b_auik @a_auil _ z_auRY 'Nothing = z_auRY
  Foldl_6989586621679128449 @b_auik @a_auil f_auRZ z_auS0 ('Just x_auS1) = Apply (Apply f_auRZ z_auS0) x_auS1
instance PFoldable Maybe where
  type FoldMap a_auRh a_auRi = FoldMap_6989586621679128417 a_auRh a_auRi
  type Foldr a_auRw a_auRx a_auRy = Foldr_6989586621679128433 a_auRw a_auRx a_auRy
  type Foldl a_auRM a_auRN a_auRO = Foldl_6989586621679128449 a_auRM a_auRN a_auRO
type Elem_6989586621679128464 :: forall a_auit. a_auit
                                                -> [a_auit] -> Bool
type family Elem_6989586621679128464 @a_auit (a_auSa :: a_auit) (a_auSb :: [a_auit]) :: Bool where
  Elem_6989586621679128464 @a_auit a_6989586621679128466_auSf a_6989586621679128468_auSg = Apply (Apply ListelemSym0 a_6989586621679128466_auSf) a_6989586621679128468_auSg
type Foldl_6989586621679128480 :: forall b_auik
                                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                                  -> b_auik -> [a_auil] -> b_auik
type family Foldl_6989586621679128480 @b_auik @a_auil (a_auSs :: (~>) b_auik ((~>) a_auil b_auik)) (a_auSt :: b_auik) (a_auSu :: [a_auil]) :: b_auik where
  Foldl_6989586621679128480 @b_auik @a_auil a_6989586621679128482_auSz a_6989586621679128484_auSA a_6989586621679128486_auSB = Apply (Apply (Apply ListfoldlSym0 a_6989586621679128482_auSz) a_6989586621679128484_auSA) a_6989586621679128486_auSB
type Foldl'_6989586621679128501 :: forall b_auim
                                          a_auin. (~>) b_auim ((~>) a_auin b_auim)
                                                  -> b_auim -> [a_auin] -> b_auim
type family Foldl'_6989586621679128501 @b_auim @a_auin (a_auSN :: (~>) b_auim ((~>) a_auin b_auim)) (a_auSO :: b_auim) (a_auSP :: [a_auin]) :: b_auim where
  Foldl'_6989586621679128501 @b_auim @a_auin a_6989586621679128503_auSU a_6989586621679128505_auSV a_6989586621679128507_auSW = Apply (Apply (Apply Listfoldl'Sym0 a_6989586621679128503_auSU) a_6989586621679128505_auSV) a_6989586621679128507_auSW
type Foldl1_6989586621679128521 :: forall a_auip. (~>) a_auip ((~>) a_auip a_auip)
                                                  -> [a_auip] -> a_auip
type family Foldl1_6989586621679128521 @a_auip (a_auT5 :: (~>) a_auip ((~>) a_auip a_auip)) (a_auT6 :: [a_auip]) :: a_auip where
  Foldl1_6989586621679128521 @a_auip a_6989586621679128523_auTa a_6989586621679128525_auTb = Apply (Apply Listfoldl1Sym0 a_6989586621679128523_auTa) a_6989586621679128525_auTb
type Foldr_6989586621679128537 :: forall a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> [a_auig] -> b_auih
type family Foldr_6989586621679128537 @a_auig @b_auih (a_auTn :: (~>) a_auig ((~>) b_auih b_auih)) (a_auTo :: b_auih) (a_auTp :: [a_auig]) :: b_auih where
  Foldr_6989586621679128537 @a_auig @b_auih a_6989586621679128539_auTu a_6989586621679128541_auTv a_6989586621679128543_auTw = Apply (Apply (Apply ListfoldrSym0 a_6989586621679128539_auTu) a_6989586621679128541_auTv) a_6989586621679128543_auTw
type Foldr1_6989586621679128557 :: forall a_auio. (~>) a_auio ((~>) a_auio a_auio)
                                                  -> [a_auio] -> a_auio
type family Foldr1_6989586621679128557 @a_auio (a_auTF :: (~>) a_auio ((~>) a_auio a_auio)) (a_auTG :: [a_auio]) :: a_auio where
  Foldr1_6989586621679128557 @a_auio a_6989586621679128559_auTK a_6989586621679128561_auTL = Apply (Apply Listfoldr1Sym0 a_6989586621679128559_auTK) a_6989586621679128561_auTL
type Length_6989586621679128571 :: forall a_auis. [a_auis]
                                                  -> Natural
type family Length_6989586621679128571 @a_auis (a_auTR :: [a_auis]) :: Natural where
  Length_6989586621679128571 @a_auis a_6989586621679128573_auTU = Apply ListlengthSym0 a_6989586621679128573_auTU
type Maximum_6989586621679128580 :: forall a_auiu. [a_auiu]
                                                    -> a_auiu
type family Maximum_6989586621679128580 @a_auiu (a_auU0 :: [a_auiu]) :: a_auiu where
  Maximum_6989586621679128580 @a_auiu a_6989586621679128582_auU3 = Apply ListmaximumSym0 a_6989586621679128582_auU3
type Minimum_6989586621679128589 :: forall a_auiv. [a_auiv]
                                                    -> a_auiv
type family Minimum_6989586621679128589 @a_auiv (a_auU9 :: [a_auiv]) :: a_auiv where
  Minimum_6989586621679128589 @a_auiv a_6989586621679128591_auUc = Apply ListminimumSym0 a_6989586621679128591_auUc
type Null_6989586621679128598 :: forall a_auir. [a_auir] -> Bool
type family Null_6989586621679128598 @a_auir (a_auUi :: [a_auir]) :: Bool where
  Null_6989586621679128598 @a_auir a_6989586621679128600_auUl = Apply ListnullSym0 a_6989586621679128600_auUl
type Product_6989586621679128607 :: forall a_auix. [a_auix]
                                                    -> a_auix
type family Product_6989586621679128607 @a_auix (a_auUr :: [a_auix]) :: a_auix where
  Product_6989586621679128607 @a_auix a_6989586621679128609_auUu = Apply ListproductSym0 a_6989586621679128609_auUu
type Sum_6989586621679128616 :: forall a_auiw. [a_auiw] -> a_auiw
type family Sum_6989586621679128616 @a_auiw (a_auUA :: [a_auiw]) :: a_auiw where
  Sum_6989586621679128616 @a_auiw a_6989586621679128618_auUD = Apply ListsumSym0 a_6989586621679128618_auUD
type ToList_6989586621679128625 :: forall a_auiq. [a_auiq]
                                                  -> [a_auiq]
type family ToList_6989586621679128625 @a_auiq (a_auUJ :: [a_auiq]) :: [a_auiq] where
  ToList_6989586621679128625 @a_auiq a_6989586621679128627_auUM = Apply IdSym0 a_6989586621679128627_auUM
instance PFoldable [] where
  type Elem a_auS2 a_auS3 = Elem_6989586621679128464 a_auS2 a_auS3
  type Foldl a_auSh a_auSi a_auSj = Foldl_6989586621679128480 a_auSh a_auSi a_auSj
  type Foldl' a_auSC a_auSD a_auSE = Foldl'_6989586621679128501 a_auSC a_auSD a_auSE
  type Foldl1 a_auSX a_auSY = Foldl1_6989586621679128521 a_auSX a_auSY
  type Foldr a_auTc a_auTd a_auTe = Foldr_6989586621679128537 a_auTc a_auTd a_auTe
  type Foldr1 a_auTx a_auTy = Foldr1_6989586621679128557 a_auTx a_auTy
  type Length a_auTM = Length_6989586621679128571 a_auTM
  type Maximum a_auTV = Maximum_6989586621679128580 a_auTV
  type Minimum a_auU4 = Minimum_6989586621679128589 a_auU4
  type Null a_auUd = Null_6989586621679128598 a_auUd
  type Product a_auUm = Product_6989586621679128607 a_auUm
  type Sum a_auUv = Sum_6989586621679128616 a_auUv
  type ToList a_auUE = ToList_6989586621679128625 a_auUE
type Foldr_6989586621679128636 :: forall a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> NonEmpty a_auig -> b_auih
type family Foldr_6989586621679128636 @a_auig @b_auih (a_auUS :: (~>) a_auig ((~>) b_auih b_auih)) (a_auUT :: b_auih) (a_auUU :: NonEmpty a_auig) :: b_auih where
  Foldr_6989586621679128636 @a_auig @b_auih f_auUZ z_auV0 ('(:|) a_auV1 as_auV2) = Apply (Apply f_auUZ a_auV1) (Apply (Apply (Apply ListfoldrSym0 f_auUZ) z_auV0) as_auV2)
type Foldl_6989586621679128652 :: forall b_auik
                                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                                  -> b_auik -> NonEmpty a_auil -> b_auik
type family Foldl_6989586621679128652 @b_auik @a_auil (a_auV8 :: (~>) b_auik ((~>) a_auil b_auik)) (a_auV9 :: b_auik) (a_auVa :: NonEmpty a_auil) :: b_auik where
  Foldl_6989586621679128652 @b_auik @a_auil f_auVf z_auVg ('(:|) a_auVh as_auVi) = Apply (Apply (Apply ListfoldlSym0 f_auVf) (Apply (Apply f_auVf z_auVg) a_auVh)) as_auVi
type Foldl1_6989586621679128667 :: forall a_auip. (~>) a_auip ((~>) a_auip a_auip)
                                                  -> NonEmpty a_auip -> a_auip
type family Foldl1_6989586621679128667 @a_auip (a_auVn :: (~>) a_auip ((~>) a_auip a_auip)) (a_auVo :: NonEmpty a_auip) :: a_auip where
  Foldl1_6989586621679128667 @a_auip f_auVs ('(:|) a_auVt as_auVu) = Apply (Apply (Apply ListfoldlSym0 f_auVs) a_auVt) as_auVu
data Let6989586621679128689GoSym0 (f6989586621679128686 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) p6989586621679128687 ps6989586621679128688 a6989586621679128690
  where
    Let6989586621679128689GoSym0KindInference :: SameKind (Apply (Let6989586621679128689GoSym0 f6989586621679128686 p6989586621679128687 ps6989586621679128688) arg_auVL) (Let6989586621679128689GoSym1 f6989586621679128686 p6989586621679128687 ps6989586621679128688 arg_auVL) =>
                                                  Let6989586621679128689GoSym0 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690
type instance Apply @_ @_ (Let6989586621679128689GoSym0 f6989586621679128686 p6989586621679128687 ps6989586621679128688) a6989586621679128690 = Let6989586621679128689GoSym1 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690
instance SuppressUnusedWarnings (Let6989586621679128689GoSym0 f6989586621679128686 p6989586621679128687 ps6989586621679128688) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128689GoSym0KindInference ())
data Let6989586621679128689GoSym1 (f6989586621679128686 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691
  where
    Let6989586621679128689GoSym1KindInference :: SameKind (Apply (Let6989586621679128689GoSym1 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690) arg_auVL) (Let6989586621679128689GoSym2 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 arg_auVL) =>
                                                  Let6989586621679128689GoSym1 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691
type instance Apply @_ @_ (Let6989586621679128689GoSym1 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690) a6989586621679128691 = Let6989586621679128689GoSym2 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691
instance SuppressUnusedWarnings (Let6989586621679128689GoSym1 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128689GoSym1KindInference ())
data Let6989586621679128689GoSym2 (f6989586621679128686 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691 a6989586621679128692
  where
    Let6989586621679128689GoSym2KindInference :: SameKind (Apply (Let6989586621679128689GoSym2 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691) arg_auVL) (Let6989586621679128689GoSym3 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691 arg_auVL) =>
                                                  Let6989586621679128689GoSym2 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691 a6989586621679128692
type instance Apply @_ @_ (Let6989586621679128689GoSym2 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691) a6989586621679128692 = Let6989586621679128689Go f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691 a6989586621679128692
instance SuppressUnusedWarnings (Let6989586621679128689GoSym2 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679128689GoSym2KindInference ())
type family Let6989586621679128689GoSym3 (f6989586621679128686 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691 a6989586621679128692 where
  Let6989586621679128689GoSym3 f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691 a6989586621679128692 = Let6989586621679128689Go f6989586621679128686 p6989586621679128687 ps6989586621679128688 a6989586621679128690 a6989586621679128691 a6989586621679128692
type family Let6989586621679128689Go (f6989586621679128686 :: (~>) a6989586621679126252 ((~>) a6989586621679126252 a6989586621679126252)) p6989586621679128687 ps6989586621679128688 a_auVI a_auVJ a_auVK where
  Let6989586621679128689Go f_auVE p_auVF ps_auVG x_auVM r_auVN prev_auVO = Apply (Apply f_auVE prev_auVO) (Apply r_auVN x_auVM)
type Foldr1_6989586621679128679 :: forall a_auio. (~>) a_auio ((~>) a_auio a_auio)
                                                  -> NonEmpty a_auio -> a_auio
type family Foldr1_6989586621679128679 @a_auio (a_auVz :: (~>) a_auio ((~>) a_auio a_auio)) (a_auVA :: NonEmpty a_auio) :: a_auio where
  Foldr1_6989586621679128679 @a_auio f_auVE ('(:|) p_auVF ps_auVG) = Apply (Apply (Apply (Apply FoldrSym0 (Let6989586621679128689GoSym0 f_auVE p_auVF ps_auVG)) IdSym0) ps_auVG) p_auVF
type FoldMap_6989586621679128699 :: forall a_auif
                                            m_auie. (~>) a_auif m_auie
                                                    -> NonEmpty a_auif -> m_auie
type family FoldMap_6989586621679128699 @a_auif @m_auie (a_auVT :: (~>) a_auif m_auie) (a_auVU :: NonEmpty a_auif) :: m_auie where
  FoldMap_6989586621679128699 @a_auif @m_auie f_auVY ('(:|) a_auVZ as_auW0) = Apply (Apply MappendSym0 (Apply f_auVY a_auVZ)) (Apply (Apply FoldMapSym0 f_auVY) as_auW0)
type Fold_6989586621679128710 :: forall m_auid. NonEmpty m_auid
                                                -> m_auid
type family Fold_6989586621679128710 @m_auid (a_auW4 :: NonEmpty m_auid) :: m_auid where
  Fold_6989586621679128710 @m_auid ('(:|) m_auW7 ms_auW8) = Apply (Apply MappendSym0 m_auW7) (Apply FoldSym0 ms_auW8)
type ToList_6989586621679128718 :: forall a_auiq. NonEmpty a_auiq
                                                  -> [a_auiq]
type family ToList_6989586621679128718 @a_auiq (a_auWc :: NonEmpty a_auiq) :: [a_auiq] where
  ToList_6989586621679128718 @a_auiq ('(:|) a_auWf as_auWg) = Apply (Apply (:@#@$) a_auWf) as_auWg
instance PFoldable NonEmpty where
  type Foldr a_auUN a_auUO a_auUP = Foldr_6989586621679128636 a_auUN a_auUO a_auUP
  type Foldl a_auV3 a_auV4 a_auV5 = Foldl_6989586621679128652 a_auV3 a_auV4 a_auV5
  type Foldl1 a_auVj a_auVk = Foldl1_6989586621679128667 a_auVj a_auVk
  type Foldr1 a_auVv a_auVw = Foldr1_6989586621679128679 a_auVv a_auVw
  type FoldMap a_auVP a_auVQ = FoldMap_6989586621679128699 a_auVP a_auVQ
  type Fold a_auW1 = Fold_6989586621679128710 a_auW1
  type ToList a_auW9 = ToList_6989586621679128718 a_auW9
type FoldMap_6989586621679128727 :: forall a_aujF
                                            a_auif
                                            m_auie. (~>) a_auif m_auie
                                                    -> Either a_aujF a_auif -> m_auie
type family FoldMap_6989586621679128727 @a_aujF @a_auif @m_auie (a_auWl :: (~>) a_auif m_auie) (a_auWm :: Either a_aujF a_auif) :: m_auie where
  FoldMap_6989586621679128727 @a_aujF @a_auif @m_auie (_ :: (~>) a_auif m_auie) ('Left _ :: Either a_aujF a_auif) = MemptySym0
  FoldMap_6989586621679128727 @a_aujF @a_auif @m_auie (f_auWq :: (~>) a_auif m_auie) ('Right y_auWr :: Either a_aujF a_auif) = Apply f_auWq y_auWr
type Foldr_6989586621679128739 :: forall a_aujF
                                          a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> Either a_aujF a_auig -> b_auih
type family Foldr_6989586621679128739 @a_aujF @a_auig @b_auih (a_auWx :: (~>) a_auig ((~>) b_auih b_auih)) (a_auWy :: b_auih) (a_auWz :: Either a_aujF a_auig) :: b_auih where
  Foldr_6989586621679128739 @a_aujF @a_auig @b_auih (_ :: (~>) a_auig ((~>) b_auih b_auih)) (z_auWE :: b_auih) ('Left _ :: Either a_aujF a_auig) = z_auWE
  Foldr_6989586621679128739 @a_aujF @a_auig @b_auih (f_auWF :: (~>) a_auig ((~>) b_auih b_auih)) (z_auWG :: b_auih) ('Right y_auWH :: Either a_aujF a_auig) = Apply (Apply f_auWF y_auWH) z_auWG
type Length_6989586621679128753 :: forall a_aujF
                                          a_auis. Either a_aujF a_auis -> Natural
type family Length_6989586621679128753 @a_aujF @a_auis (a_auWL :: Either a_aujF a_auis) :: Natural where
  Length_6989586621679128753 @a_aujF @a_auis ('Left _ :: Either a_aujF a_auis) = FromInteger 0
  Length_6989586621679128753 @a_aujF @a_auis ('Right _ :: Either a_aujF a_auis) = FromInteger 1
type Null_6989586621679128759 :: forall a_aujF
                                        a_auir. Either a_aujF a_auir -> Bool
type family Null_6989586621679128759 @a_aujF @a_auir (a_auWT :: Either a_aujF a_auir) :: Bool where
  Null_6989586621679128759 @a_aujF @a_auir (a_6989586621679128761_auWW :: Either a_aujF a_auir) = Apply IsLeftSym0 a_6989586621679128761_auWW
instance PFoldable (Either a_aujF) where
  type FoldMap a_auWh a_auWi = FoldMap_6989586621679128727 a_auWh a_auWi
  type Foldr a_auWs a_auWt a_auWu = Foldr_6989586621679128739 a_auWs a_auWt a_auWu
  type Length a_auWI = Length_6989586621679128753 a_auWI
  type Null a_auWO = Null_6989586621679128759 a_auWO
type FoldMap_6989586621679128769 :: forall a_auif
                                            m_auie. (~>) a_auif m_auie -> Proxy a_auif -> m_auie
type family FoldMap_6989586621679128769 @a_auif @m_auie (a_auX1 :: (~>) a_auif m_auie) (a_auX2 :: Proxy a_auif) :: m_auie where
  FoldMap_6989586621679128769 @a_auif @m_auie _ _ = MemptySym0
type Fold_6989586621679128777 :: forall m_auid. Proxy m_auid
                                                -> m_auid
type family Fold_6989586621679128777 @m_auid (a_auX9 :: Proxy m_auid) :: m_auid where
  Fold_6989586621679128777 @m_auid _ = MemptySym0
type Foldr_6989586621679128785 :: forall a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> Proxy a_auig -> b_auih
type family Foldr_6989586621679128785 @a_auig @b_auih (a_auXh :: (~>) a_auig ((~>) b_auih b_auih)) (a_auXi :: b_auih) (a_auXj :: Proxy a_auig) :: b_auih where
  Foldr_6989586621679128785 @a_auig @b_auih _ z_auXo _ = z_auXo
type Foldl_6989586621679128798 :: forall b_auik
                                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                                  -> b_auik -> Proxy a_auil -> b_auik
type family Foldl_6989586621679128798 @b_auik @a_auil (a_auXu :: (~>) b_auik ((~>) a_auil b_auik)) (a_auXv :: b_auik) (a_auXw :: Proxy a_auil) :: b_auik where
  Foldl_6989586621679128798 @b_auik @a_auil _ z_auXB _ = z_auXB
type Foldl1_6989586621679128810 :: forall a_auip. (~>) a_auip ((~>) a_auip a_auip)
                                                  -> Proxy a_auip -> a_auip
type family Foldl1_6989586621679128810 @a_auip (a_auXG :: (~>) a_auip ((~>) a_auip a_auip)) (a_auXH :: Proxy a_auip) :: a_auip where
  Foldl1_6989586621679128810 @a_auip _ _ = Apply ErrorWithoutStackTraceSym0 "foldl1: Proxy"
type Foldr1_6989586621679128819 :: forall a_auio. (~>) a_auio ((~>) a_auio a_auio)
                                                  -> Proxy a_auio -> a_auio
type family Foldr1_6989586621679128819 @a_auio (a_auXP :: (~>) a_auio ((~>) a_auio a_auio)) (a_auXQ :: Proxy a_auio) :: a_auio where
  Foldr1_6989586621679128819 @a_auio _ _ = Apply ErrorWithoutStackTraceSym0 "foldr1: Proxy"
type Length_6989586621679128827 :: forall (a_aujM :: Type). Proxy a_aujM
                                                            -> Natural
type family Length_6989586621679128827 @(a_aujM :: Type) (a_auXX :: Proxy a_aujM) :: Natural where
  Length_6989586621679128827 @a_aujM (_ :: Proxy a_aujM) = FromInteger 0
type Null_6989586621679128833 :: forall (a_aujN :: Type). Proxy a_aujN
                                                          -> Bool
type family Null_6989586621679128833 @(a_aujN :: Type) (a_auY3 :: Proxy a_aujN) :: Bool where
  Null_6989586621679128833 @a_aujN (_ :: Proxy a_aujN) = TrueSym0
type Elem_6989586621679128840 :: forall a_auit. a_auit
                                                -> Proxy a_auit -> Bool
type family Elem_6989586621679128840 @a_auit (a_auYa :: a_auit) (a_auYb :: Proxy a_auit) :: Bool where
  Elem_6989586621679128840 @a_auit _ _ = FalseSym0
type Sum_6989586621679128848 :: forall a_auiw. Proxy a_auiw
                                                -> a_auiw
type family Sum_6989586621679128848 @a_auiw (a_auYi :: Proxy a_auiw) :: a_auiw where
  Sum_6989586621679128848 @a_auiw _ = FromInteger 0
type Product_6989586621679128854 :: forall a_auix. Proxy a_auix
                                                    -> a_auix
type family Product_6989586621679128854 @a_auix (a_auYo :: Proxy a_auix) :: a_auix where
  Product_6989586621679128854 @a_auix _ = FromInteger 1
instance PFoldable Proxy where
  type FoldMap a_auWX a_auWY = FoldMap_6989586621679128769 a_auWX a_auWY
  type Fold a_auX6 = Fold_6989586621679128777 a_auX6
  type Foldr a_auXc a_auXd a_auXe = Foldr_6989586621679128785 a_auXc a_auXd a_auXe
  type Foldl a_auXp a_auXq a_auXr = Foldl_6989586621679128798 a_auXp a_auXq a_auXr
  type Foldl1 a_auXC a_auXD = Foldl1_6989586621679128810 a_auXC a_auXD
  type Foldr1 a_auXL a_auXM = Foldr1_6989586621679128819 a_auXL a_auXM
  type Length a_auXU = Length_6989586621679128827 a_auXU
  type Null a_auY0 = Null_6989586621679128833 a_auY0
  type Elem a_auY6 a_auY7 = Elem_6989586621679128840 a_auY6 a_auY7
  type Sum a_auYf = Sum_6989586621679128848 a_auYf
  type Product a_auYl = Product_6989586621679128854 a_auYl
type FoldMap_6989586621679128861 :: forall a_auif
                                            m_auie. (~>) a_auif m_auie -> Dual a_auif -> m_auie
type family FoldMap_6989586621679128861 @a_auif @m_auie (a_auYv :: (~>) a_auif m_auie) (a_auYw :: Dual a_auif) :: m_auie where
  FoldMap_6989586621679128861 @a_auif @m_auie f_auYA ('Dual x_auYB) = Apply f_auYA x_auYB
type family LamCases_6989586621679128885_auYS (a_69895866216791288746989586621679128883 :: a6989586621679126257) (a_69895866216791288766989586621679128884 :: Dual a6989586621679126257) a_6989586621679128888_auYV where
  LamCases_6989586621679128885_auYS a_6989586621679128874_auYP a_6989586621679128876_auYQ lhs_6989586621679126414_auYT = Apply (Apply (.@#@$) lhs_6989586621679126414_auYT) GetDualSym0
data LamCases_6989586621679128885Sym0 (a_69895866216791288746989586621679128883 :: a6989586621679126257) (a_69895866216791288766989586621679128884 :: Dual a6989586621679126257) a_69895866216791288886989586621679128889
  where
    LamCases_6989586621679128885Sym0KindInference :: SameKind (Apply (LamCases_6989586621679128885Sym0 a_69895866216791288746989586621679128883 a_69895866216791288766989586621679128884) arg_auYW) (LamCases_6989586621679128885Sym1 a_69895866216791288746989586621679128883 a_69895866216791288766989586621679128884 arg_auYW) =>
                                                      LamCases_6989586621679128885Sym0 a_69895866216791288746989586621679128883 a_69895866216791288766989586621679128884 a_69895866216791288886989586621679128889
type instance Apply @_ @_ (LamCases_6989586621679128885Sym0 a_69895866216791288746989586621679128883 a_69895866216791288766989586621679128884) a_69895866216791288886989586621679128889 = LamCases_6989586621679128885_auYS a_69895866216791288746989586621679128883 a_69895866216791288766989586621679128884 a_69895866216791288886989586621679128889
instance SuppressUnusedWarnings (LamCases_6989586621679128885Sym0 a_69895866216791288746989586621679128883 a_69895866216791288766989586621679128884) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679128885Sym0KindInference ())
type family LamCases_6989586621679128885Sym1 (a_69895866216791288746989586621679128883 :: a6989586621679126257) (a_69895866216791288766989586621679128884 :: Dual a6989586621679126257) a_69895866216791288886989586621679128889 where
  LamCases_6989586621679128885Sym1 a_69895866216791288746989586621679128883 a_69895866216791288766989586621679128884 a_69895866216791288886989586621679128889 = LamCases_6989586621679128885_auYS a_69895866216791288746989586621679128883 a_69895866216791288766989586621679128884 a_69895866216791288886989586621679128889
type Elem_6989586621679128872 :: forall a_auit. a_auit
                                                -> Dual a_auit -> Bool
type family Elem_6989586621679128872 @a_auit (a_auYK :: a_auit) (a_auYL :: Dual a_auit) :: Bool where
  Elem_6989586621679128872 @a_auit a_6989586621679128874_auYP a_6989586621679128876_auYQ = Apply (Apply (Apply (Apply (.@#@$) (LamCases_6989586621679128885Sym0 a_6989586621679128874_auYP a_6989586621679128876_auYQ)) (==@#@$)) a_6989586621679128874_auYP) a_6989586621679128876_auYQ
type Foldl_6989586621679128894 :: forall b_auik
                                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                                  -> b_auik -> Dual a_auil -> b_auik
type family Foldl_6989586621679128894 @b_auik @a_auil (a_auZ2 :: (~>) b_auik ((~>) a_auil b_auik)) (a_auZ3 :: b_auik) (a_auZ4 :: Dual a_auil) :: b_auik where
  Foldl_6989586621679128894 @b_auik @a_auil f_auZ9 z_auZa ('Dual x_auZb) = Apply (Apply f_auZ9 z_auZa) x_auZb
type Foldl'_6989586621679128909 :: forall b_auim
                                          a_auin. (~>) b_auim ((~>) a_auin b_auim)
                                                  -> b_auim -> Dual a_auin -> b_auim
type family Foldl'_6989586621679128909 @b_auim @a_auin (a_auZh :: (~>) b_auim ((~>) a_auin b_auim)) (a_auZi :: b_auim) (a_auZj :: Dual a_auin) :: b_auim where
  Foldl'_6989586621679128909 @b_auim @a_auin f_auZo z_auZp ('Dual x_auZq) = Apply (Apply f_auZo z_auZp) x_auZq
type Foldl1_6989586621679128923 :: forall a_auip. (~>) a_auip ((~>) a_auip a_auip)
                                                  -> Dual a_auip -> a_auip
type family Foldl1_6989586621679128923 @a_auip (a_auZx :: (~>) a_auip ((~>) a_auip a_auip)) (a_auZy :: Dual a_auip) :: a_auip where
  Foldl1_6989586621679128923 @a_auip _ a_6989586621679128925_auZC = Apply GetDualSym0 a_6989586621679128925_auZC
type Foldr_6989586621679128936 :: forall a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> Dual a_auig -> b_auih
type family Foldr_6989586621679128936 @a_auig @b_auih (a_auZI :: (~>) a_auig ((~>) b_auih b_auih)) (a_auZJ :: b_auih) (a_auZK :: Dual a_auig) :: b_auih where
  Foldr_6989586621679128936 @a_auig @b_auih f_auZP z_auZQ ('Dual x_auZR) = Apply (Apply f_auZP x_auZR) z_auZQ
type Foldr'_6989586621679128951 :: forall a_auii
                                          b_auij. (~>) a_auii ((~>) b_auij b_auij)
                                                  -> b_auij -> Dual a_auii -> b_auij
type family Foldr'_6989586621679128951 @a_auii @b_auij (a_av03 :: (~>) a_auii ((~>) b_auij b_auij)) (a_av04 :: b_auij) (a_av05 :: Dual a_auii) :: b_auij where
  Foldr'_6989586621679128951 @a_auii @b_auij a_6989586621679128953_av0a a_6989586621679128955_av0b a_6989586621679128957_av0c = Apply (Apply (Apply FoldrSym0 a_6989586621679128953_av0a) a_6989586621679128955_av0b) a_6989586621679128957_av0c
type Foldr1_6989586621679128971 :: forall a_auio. (~>) a_auio ((~>) a_auio a_auio)
                                                  -> Dual a_auio -> a_auio
type family Foldr1_6989586621679128971 @a_auio (a_av0j :: (~>) a_auio ((~>) a_auio a_auio)) (a_av0k :: Dual a_auio) :: a_auio where
  Foldr1_6989586621679128971 @a_auio _ a_6989586621679128973_av0o = Apply GetDualSym0 a_6989586621679128973_av0o
type Length_6989586621679128982 :: forall a_auis. Dual a_auis
                                                  -> Natural
type family Length_6989586621679128982 @a_auis (a_av0s :: Dual a_auis) :: Natural where
  Length_6989586621679128982 @a_auis _ = FromInteger 1
type Maximum_6989586621679128988 :: forall a_auiu. Dual a_auiu
                                                    -> a_auiu
type family Maximum_6989586621679128988 @a_auiu (a_av0A :: Dual a_auiu) :: a_auiu where
  Maximum_6989586621679128988 @a_auiu a_6989586621679128990_av0D = Apply GetDualSym0 a_6989586621679128990_av0D
type Minimum_6989586621679128997 :: forall a_auiv. Dual a_auiv
                                                    -> a_auiv
type family Minimum_6989586621679128997 @a_auiv (a_av0J :: Dual a_auiv) :: a_auiv where
  Minimum_6989586621679128997 @a_auiv a_6989586621679128999_av0M = Apply GetDualSym0 a_6989586621679128999_av0M
type Null_6989586621679129006 :: forall a_auir. Dual a_auir -> Bool
type family Null_6989586621679129006 @a_auir (a_av0Q :: Dual a_auir) :: Bool where
  Null_6989586621679129006 @a_auir _ = FalseSym0
type Product_6989586621679129012 :: forall a_auix. Dual a_auix
                                                    -> a_auix
type family Product_6989586621679129012 @a_auix (a_av0Y :: Dual a_auix) :: a_auix where
  Product_6989586621679129012 @a_auix a_6989586621679129014_av11 = Apply GetDualSym0 a_6989586621679129014_av11
type Sum_6989586621679129021 :: forall a_auiw. Dual a_auiw
                                                -> a_auiw
type family Sum_6989586621679129021 @a_auiw (a_av17 :: Dual a_auiw) :: a_auiw where
  Sum_6989586621679129021 @a_auiw a_6989586621679129023_av1a = Apply GetDualSym0 a_6989586621679129023_av1a
type ToList_6989586621679129030 :: forall a_auiq. Dual a_auiq
                                                  -> [a_auiq]
type family ToList_6989586621679129030 @a_auiq (a_av1e :: Dual a_auiq) :: [a_auiq] where
  ToList_6989586621679129030 @a_auiq ('Dual x_av1h) = Apply (Apply (:@#@$) x_av1h) NilSym0
instance PFoldable Dual where
  type FoldMap a_auYr a_auYs = FoldMap_6989586621679128861 a_auYr a_auYs
  type Elem a_auYC a_auYD = Elem_6989586621679128872 a_auYC a_auYD
  type Foldl a_auYX a_auYY a_auYZ = Foldl_6989586621679128894 a_auYX a_auYY a_auYZ
  type Foldl' a_auZc a_auZd a_auZe = Foldl'_6989586621679128909 a_auZc a_auZd a_auZe
  type Foldl1 a_auZr a_auZs = Foldl1_6989586621679128923 a_auZr a_auZs
  type Foldr a_auZD a_auZE a_auZF = Foldr_6989586621679128936 a_auZD a_auZE a_auZF
  type Foldr' a_auZS a_auZT a_auZU = Foldr'_6989586621679128951 a_auZS a_auZT a_auZU
  type Foldr1 a_av0d a_av0e = Foldr1_6989586621679128971 a_av0d a_av0e
  type Length a_av0p = Length_6989586621679128982 a_av0p
  type Maximum a_av0v = Maximum_6989586621679128988 a_av0v
  type Minimum a_av0E = Minimum_6989586621679128997 a_av0E
  type Null a_av0N = Null_6989586621679129006 a_av0N
  type Product a_av0T = Product_6989586621679129012 a_av0T
  type Sum a_av12 = Sum_6989586621679129021 a_av12
  type ToList a_av1b = ToList_6989586621679129030 a_av1b
type FoldMap_6989586621679129038 :: forall a_auif
                                            m_auie. (~>) a_auif m_auie
                                                    -> Monoid.Sum a_auif -> m_auie
type family FoldMap_6989586621679129038 @a_auif @m_auie (a_av1m :: (~>) a_auif m_auie) (a_av1n :: Monoid.Sum a_auif) :: m_auie where
  FoldMap_6989586621679129038 @a_auif @m_auie f_av1r ('Monoid.Sum x_av1s) = Apply f_av1r x_av1s
type family LamCases_6989586621679129062_av1J (a_69895866216791290516989586621679129060 :: a6989586621679126257) (a_69895866216791290536989586621679129061 :: Monoid.Sum a6989586621679126257) a_6989586621679129065_av1M where
  LamCases_6989586621679129062_av1J a_6989586621679129051_av1G a_6989586621679129053_av1H lhs_6989586621679126416_av1K = Apply (Apply (.@#@$) lhs_6989586621679126416_av1K) GetSumSym0
data LamCases_6989586621679129062Sym0 (a_69895866216791290516989586621679129060 :: a6989586621679126257) (a_69895866216791290536989586621679129061 :: Monoid.Sum a6989586621679126257) a_69895866216791290656989586621679129066
  where
    LamCases_6989586621679129062Sym0KindInference :: SameKind (Apply (LamCases_6989586621679129062Sym0 a_69895866216791290516989586621679129060 a_69895866216791290536989586621679129061) arg_av1N) (LamCases_6989586621679129062Sym1 a_69895866216791290516989586621679129060 a_69895866216791290536989586621679129061 arg_av1N) =>
                                                      LamCases_6989586621679129062Sym0 a_69895866216791290516989586621679129060 a_69895866216791290536989586621679129061 a_69895866216791290656989586621679129066
type instance Apply @_ @_ (LamCases_6989586621679129062Sym0 a_69895866216791290516989586621679129060 a_69895866216791290536989586621679129061) a_69895866216791290656989586621679129066 = LamCases_6989586621679129062_av1J a_69895866216791290516989586621679129060 a_69895866216791290536989586621679129061 a_69895866216791290656989586621679129066
instance SuppressUnusedWarnings (LamCases_6989586621679129062Sym0 a_69895866216791290516989586621679129060 a_69895866216791290536989586621679129061) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679129062Sym0KindInference ())
type family LamCases_6989586621679129062Sym1 (a_69895866216791290516989586621679129060 :: a6989586621679126257) (a_69895866216791290536989586621679129061 :: Monoid.Sum a6989586621679126257) a_69895866216791290656989586621679129066 where
  LamCases_6989586621679129062Sym1 a_69895866216791290516989586621679129060 a_69895866216791290536989586621679129061 a_69895866216791290656989586621679129066 = LamCases_6989586621679129062_av1J a_69895866216791290516989586621679129060 a_69895866216791290536989586621679129061 a_69895866216791290656989586621679129066
type Elem_6989586621679129049 :: forall a_auit. a_auit
                                                -> Monoid.Sum a_auit -> Bool
type family Elem_6989586621679129049 @a_auit (a_av1B :: a_auit) (a_av1C :: Monoid.Sum a_auit) :: Bool where
  Elem_6989586621679129049 @a_auit a_6989586621679129051_av1G a_6989586621679129053_av1H = Apply (Apply (Apply (Apply (.@#@$) (LamCases_6989586621679129062Sym0 a_6989586621679129051_av1G a_6989586621679129053_av1H)) (==@#@$)) a_6989586621679129051_av1G) a_6989586621679129053_av1H
type Foldl_6989586621679129071 :: forall b_auik
                                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                                  -> b_auik -> Monoid.Sum a_auil -> b_auik
type family Foldl_6989586621679129071 @b_auik @a_auil (a_av1T :: (~>) b_auik ((~>) a_auil b_auik)) (a_av1U :: b_auik) (a_av1V :: Monoid.Sum a_auil) :: b_auik where
  Foldl_6989586621679129071 @b_auik @a_auil f_av20 z_av21 ('Monoid.Sum x_av22) = Apply (Apply f_av20 z_av21) x_av22
type Foldl'_6989586621679129086 :: forall b_auim
                                          a_auin. (~>) b_auim ((~>) a_auin b_auim)
                                                  -> b_auim -> Monoid.Sum a_auin -> b_auim
type family Foldl'_6989586621679129086 @b_auim @a_auin (a_av28 :: (~>) b_auim ((~>) a_auin b_auim)) (a_av29 :: b_auim) (a_av2a :: Monoid.Sum a_auin) :: b_auim where
  Foldl'_6989586621679129086 @b_auim @a_auin f_av2f z_av2g ('Monoid.Sum x_av2h) = Apply (Apply f_av2f z_av2g) x_av2h
type Foldl1_6989586621679129100 :: forall a_auip. (~>) a_auip ((~>) a_auip a_auip)
                                                  -> Monoid.Sum a_auip -> a_auip
type family Foldl1_6989586621679129100 @a_auip (a_av2o :: (~>) a_auip ((~>) a_auip a_auip)) (a_av2p :: Monoid.Sum a_auip) :: a_auip where
  Foldl1_6989586621679129100 @a_auip _ a_6989586621679129102_av2t = Apply GetSumSym0 a_6989586621679129102_av2t
type Foldr_6989586621679129113 :: forall a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> Monoid.Sum a_auig -> b_auih
type family Foldr_6989586621679129113 @a_auig @b_auih (a_av2z :: (~>) a_auig ((~>) b_auih b_auih)) (a_av2A :: b_auih) (a_av2B :: Monoid.Sum a_auig) :: b_auih where
  Foldr_6989586621679129113 @a_auig @b_auih f_av2G z_av2H ('Monoid.Sum x_av2I) = Apply (Apply f_av2G x_av2I) z_av2H
type Foldr'_6989586621679129128 :: forall a_auii
                                          b_auij. (~>) a_auii ((~>) b_auij b_auij)
                                                  -> b_auij -> Monoid.Sum a_auii -> b_auij
type family Foldr'_6989586621679129128 @a_auii @b_auij (a_av2U :: (~>) a_auii ((~>) b_auij b_auij)) (a_av2V :: b_auij) (a_av2W :: Monoid.Sum a_auii) :: b_auij where
  Foldr'_6989586621679129128 @a_auii @b_auij a_6989586621679129130_av31 a_6989586621679129132_av32 a_6989586621679129134_av33 = Apply (Apply (Apply FoldrSym0 a_6989586621679129130_av31) a_6989586621679129132_av32) a_6989586621679129134_av33
type Foldr1_6989586621679129148 :: forall a_auio. (~>) a_auio ((~>) a_auio a_auio)
                                                  -> Monoid.Sum a_auio -> a_auio
type family Foldr1_6989586621679129148 @a_auio (a_av3a :: (~>) a_auio ((~>) a_auio a_auio)) (a_av3b :: Monoid.Sum a_auio) :: a_auio where
  Foldr1_6989586621679129148 @a_auio _ a_6989586621679129150_av3f = Apply GetSumSym0 a_6989586621679129150_av3f
type Length_6989586621679129159 :: forall a_auis. Monoid.Sum a_auis
                                                  -> Natural
type family Length_6989586621679129159 @a_auis (a_av3j :: Monoid.Sum a_auis) :: Natural where
  Length_6989586621679129159 @a_auis _ = FromInteger 1
type Maximum_6989586621679129165 :: forall a_auiu. Monoid.Sum a_auiu
                                                    -> a_auiu
type family Maximum_6989586621679129165 @a_auiu (a_av3r :: Monoid.Sum a_auiu) :: a_auiu where
  Maximum_6989586621679129165 @a_auiu a_6989586621679129167_av3u = Apply GetSumSym0 a_6989586621679129167_av3u
type Minimum_6989586621679129174 :: forall a_auiv. Monoid.Sum a_auiv
                                                    -> a_auiv
type family Minimum_6989586621679129174 @a_auiv (a_av3A :: Monoid.Sum a_auiv) :: a_auiv where
  Minimum_6989586621679129174 @a_auiv a_6989586621679129176_av3D = Apply GetSumSym0 a_6989586621679129176_av3D
type Null_6989586621679129183 :: forall a_auir. Monoid.Sum a_auir
                                                -> Bool
type family Null_6989586621679129183 @a_auir (a_av3H :: Monoid.Sum a_auir) :: Bool where
  Null_6989586621679129183 @a_auir _ = FalseSym0
type Product_6989586621679129189 :: forall a_auix. Monoid.Sum a_auix
                                                    -> a_auix
type family Product_6989586621679129189 @a_auix (a_av3P :: Monoid.Sum a_auix) :: a_auix where
  Product_6989586621679129189 @a_auix a_6989586621679129191_av3S = Apply GetSumSym0 a_6989586621679129191_av3S
type Sum_6989586621679129198 :: forall a_auiw. Monoid.Sum a_auiw
                                                -> a_auiw
type family Sum_6989586621679129198 @a_auiw (a_av3Y :: Monoid.Sum a_auiw) :: a_auiw where
  Sum_6989586621679129198 @a_auiw a_6989586621679129200_av41 = Apply GetSumSym0 a_6989586621679129200_av41
type ToList_6989586621679129207 :: forall a_auiq. Monoid.Sum a_auiq
                                                  -> [a_auiq]
type family ToList_6989586621679129207 @a_auiq (a_av45 :: Monoid.Sum a_auiq) :: [a_auiq] where
  ToList_6989586621679129207 @a_auiq ('Monoid.Sum x_av48) = Apply (Apply (:@#@$) x_av48) NilSym0
instance PFoldable Monoid.Sum where
  type FoldMap a_av1i a_av1j = FoldMap_6989586621679129038 a_av1i a_av1j
  type Elem a_av1t a_av1u = Elem_6989586621679129049 a_av1t a_av1u
  type Foldl a_av1O a_av1P a_av1Q = Foldl_6989586621679129071 a_av1O a_av1P a_av1Q
  type Foldl' a_av23 a_av24 a_av25 = Foldl'_6989586621679129086 a_av23 a_av24 a_av25
  type Foldl1 a_av2i a_av2j = Foldl1_6989586621679129100 a_av2i a_av2j
  type Foldr a_av2u a_av2v a_av2w = Foldr_6989586621679129113 a_av2u a_av2v a_av2w
  type Foldr' a_av2J a_av2K a_av2L = Foldr'_6989586621679129128 a_av2J a_av2K a_av2L
  type Foldr1 a_av34 a_av35 = Foldr1_6989586621679129148 a_av34 a_av35
  type Length a_av3g = Length_6989586621679129159 a_av3g
  type Maximum a_av3m = Maximum_6989586621679129165 a_av3m
  type Minimum a_av3v = Minimum_6989586621679129174 a_av3v
  type Null a_av3E = Null_6989586621679129183 a_av3E
  type Product a_av3K = Product_6989586621679129189 a_av3K
  type Sum a_av3T = Sum_6989586621679129198 a_av3T
  type ToList a_av42 = ToList_6989586621679129207 a_av42
type FoldMap_6989586621679129215 :: forall a_auif
                                            m_auie. (~>) a_auif m_auie
                                                    -> Monoid.Product a_auif -> m_auie
type family FoldMap_6989586621679129215 @a_auif @m_auie (a_av4d :: (~>) a_auif m_auie) (a_av4e :: Monoid.Product a_auif) :: m_auie where
  FoldMap_6989586621679129215 @a_auif @m_auie f_av4i ('Monoid.Product x_av4j) = Apply f_av4i x_av4j
type family LamCases_6989586621679129239_av4A (a_69895866216791292286989586621679129237 :: a6989586621679126257) (a_69895866216791292306989586621679129238 :: Monoid.Product a6989586621679126257) a_6989586621679129242_av4D where
  LamCases_6989586621679129239_av4A a_6989586621679129228_av4x a_6989586621679129230_av4y lhs_6989586621679126418_av4B = Apply (Apply (.@#@$) lhs_6989586621679126418_av4B) GetProductSym0
data LamCases_6989586621679129239Sym0 (a_69895866216791292286989586621679129237 :: a6989586621679126257) (a_69895866216791292306989586621679129238 :: Monoid.Product a6989586621679126257) a_69895866216791292426989586621679129243
  where
    LamCases_6989586621679129239Sym0KindInference :: SameKind (Apply (LamCases_6989586621679129239Sym0 a_69895866216791292286989586621679129237 a_69895866216791292306989586621679129238) arg_av4E) (LamCases_6989586621679129239Sym1 a_69895866216791292286989586621679129237 a_69895866216791292306989586621679129238 arg_av4E) =>
                                                      LamCases_6989586621679129239Sym0 a_69895866216791292286989586621679129237 a_69895866216791292306989586621679129238 a_69895866216791292426989586621679129243
type instance Apply @_ @_ (LamCases_6989586621679129239Sym0 a_69895866216791292286989586621679129237 a_69895866216791292306989586621679129238) a_69895866216791292426989586621679129243 = LamCases_6989586621679129239_av4A a_69895866216791292286989586621679129237 a_69895866216791292306989586621679129238 a_69895866216791292426989586621679129243
instance SuppressUnusedWarnings (LamCases_6989586621679129239Sym0 a_69895866216791292286989586621679129237 a_69895866216791292306989586621679129238) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679129239Sym0KindInference ())
type family LamCases_6989586621679129239Sym1 (a_69895866216791292286989586621679129237 :: a6989586621679126257) (a_69895866216791292306989586621679129238 :: Monoid.Product a6989586621679126257) a_69895866216791292426989586621679129243 where
  LamCases_6989586621679129239Sym1 a_69895866216791292286989586621679129237 a_69895866216791292306989586621679129238 a_69895866216791292426989586621679129243 = LamCases_6989586621679129239_av4A a_69895866216791292286989586621679129237 a_69895866216791292306989586621679129238 a_69895866216791292426989586621679129243
type Elem_6989586621679129226 :: forall a_auit. a_auit
                                                -> Monoid.Product a_auit -> Bool
type family Elem_6989586621679129226 @a_auit (a_av4s :: a_auit) (a_av4t :: Monoid.Product a_auit) :: Bool where
  Elem_6989586621679129226 @a_auit a_6989586621679129228_av4x a_6989586621679129230_av4y = Apply (Apply (Apply (Apply (.@#@$) (LamCases_6989586621679129239Sym0 a_6989586621679129228_av4x a_6989586621679129230_av4y)) (==@#@$)) a_6989586621679129228_av4x) a_6989586621679129230_av4y
type Foldl_6989586621679129248 :: forall b_auik
                                          a_auil. (~>) b_auik ((~>) a_auil b_auik)
                                                  -> b_auik -> Monoid.Product a_auil -> b_auik
type family Foldl_6989586621679129248 @b_auik @a_auil (a_av4K :: (~>) b_auik ((~>) a_auil b_auik)) (a_av4L :: b_auik) (a_av4M :: Monoid.Product a_auil) :: b_auik where
  Foldl_6989586621679129248 @b_auik @a_auil f_av4R z_av4S ('Monoid.Product x_av4T) = Apply (Apply f_av4R z_av4S) x_av4T
type Foldl'_6989586621679129263 :: forall b_auim
                                          a_auin. (~>) b_auim ((~>) a_auin b_auim)
                                                  -> b_auim -> Monoid.Product a_auin -> b_auim
type family Foldl'_6989586621679129263 @b_auim @a_auin (a_av4Z :: (~>) b_auim ((~>) a_auin b_auim)) (a_av50 :: b_auim) (a_av51 :: Monoid.Product a_auin) :: b_auim where
  Foldl'_6989586621679129263 @b_auim @a_auin f_av56 z_av57 ('Monoid.Product x_av58) = Apply (Apply f_av56 z_av57) x_av58
type Foldl1_6989586621679129277 :: forall a_auip. (~>) a_auip ((~>) a_auip a_auip)
                                                  -> Monoid.Product a_auip -> a_auip
type family Foldl1_6989586621679129277 @a_auip (a_av5f :: (~>) a_auip ((~>) a_auip a_auip)) (a_av5g :: Monoid.Product a_auip) :: a_auip where
  Foldl1_6989586621679129277 @a_auip _ a_6989586621679129279_av5k = Apply GetProductSym0 a_6989586621679129279_av5k
type Foldr_6989586621679129290 :: forall a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> Monoid.Product a_auig -> b_auih
type family Foldr_6989586621679129290 @a_auig @b_auih (a_av5q :: (~>) a_auig ((~>) b_auih b_auih)) (a_av5r :: b_auih) (a_av5s :: Monoid.Product a_auig) :: b_auih where
  Foldr_6989586621679129290 @a_auig @b_auih f_av5x z_av5y ('Monoid.Product x_av5z) = Apply (Apply f_av5x x_av5z) z_av5y
type Foldr'_6989586621679129305 :: forall a_auii
                                          b_auij. (~>) a_auii ((~>) b_auij b_auij)
                                                  -> b_auij -> Monoid.Product a_auii -> b_auij
type family Foldr'_6989586621679129305 @a_auii @b_auij (a_av5L :: (~>) a_auii ((~>) b_auij b_auij)) (a_av5M :: b_auij) (a_av5N :: Monoid.Product a_auii) :: b_auij where
  Foldr'_6989586621679129305 @a_auii @b_auij a_6989586621679129307_av5S a_6989586621679129309_av5T a_6989586621679129311_av5U = Apply (Apply (Apply FoldrSym0 a_6989586621679129307_av5S) a_6989586621679129309_av5T) a_6989586621679129311_av5U
type Foldr1_6989586621679129325 :: forall a_auio. (~>) a_auio ((~>) a_auio a_auio)
                                                  -> Monoid.Product a_auio -> a_auio
type family Foldr1_6989586621679129325 @a_auio (a_av61 :: (~>) a_auio ((~>) a_auio a_auio)) (a_av62 :: Monoid.Product a_auio) :: a_auio where
  Foldr1_6989586621679129325 @a_auio _ a_6989586621679129327_av66 = Apply GetProductSym0 a_6989586621679129327_av66
type Length_6989586621679129336 :: forall a_auis. Monoid.Product a_auis
                                                  -> Natural
type family Length_6989586621679129336 @a_auis (a_av6a :: Monoid.Product a_auis) :: Natural where
  Length_6989586621679129336 @a_auis _ = FromInteger 1
type Maximum_6989586621679129342 :: forall a_auiu. Monoid.Product a_auiu
                                                    -> a_auiu
type family Maximum_6989586621679129342 @a_auiu (a_av6i :: Monoid.Product a_auiu) :: a_auiu where
  Maximum_6989586621679129342 @a_auiu a_6989586621679129344_av6l = Apply GetProductSym0 a_6989586621679129344_av6l
type Minimum_6989586621679129351 :: forall a_auiv. Monoid.Product a_auiv
                                                    -> a_auiv
type family Minimum_6989586621679129351 @a_auiv (a_av6r :: Monoid.Product a_auiv) :: a_auiv where
  Minimum_6989586621679129351 @a_auiv a_6989586621679129353_av6u = Apply GetProductSym0 a_6989586621679129353_av6u
type Null_6989586621679129360 :: forall a_auir. Monoid.Product a_auir
                                                -> Bool
type family Null_6989586621679129360 @a_auir (a_av6y :: Monoid.Product a_auir) :: Bool where
  Null_6989586621679129360 @a_auir _ = FalseSym0
type Product_6989586621679129366 :: forall a_auix. Monoid.Product a_auix
                                                    -> a_auix
type family Product_6989586621679129366 @a_auix (a_av6G :: Monoid.Product a_auix) :: a_auix where
  Product_6989586621679129366 @a_auix a_6989586621679129368_av6J = Apply GetProductSym0 a_6989586621679129368_av6J
type Sum_6989586621679129375 :: forall a_auiw. Monoid.Product a_auiw
                                                -> a_auiw
type family Sum_6989586621679129375 @a_auiw (a_av6P :: Monoid.Product a_auiw) :: a_auiw where
  Sum_6989586621679129375 @a_auiw a_6989586621679129377_av6S = Apply GetProductSym0 a_6989586621679129377_av6S
type ToList_6989586621679129384 :: forall a_auiq. Monoid.Product a_auiq
                                                  -> [a_auiq]
type family ToList_6989586621679129384 @a_auiq (a_av6W :: Monoid.Product a_auiq) :: [a_auiq] where
  ToList_6989586621679129384 @a_auiq ('Monoid.Product x_av6Z) = Apply (Apply (:@#@$) x_av6Z) NilSym0
instance PFoldable Monoid.Product where
  type FoldMap a_av49 a_av4a = FoldMap_6989586621679129215 a_av49 a_av4a
  type Elem a_av4k a_av4l = Elem_6989586621679129226 a_av4k a_av4l
  type Foldl a_av4F a_av4G a_av4H = Foldl_6989586621679129248 a_av4F a_av4G a_av4H
  type Foldl' a_av4U a_av4V a_av4W = Foldl'_6989586621679129263 a_av4U a_av4V a_av4W
  type Foldl1 a_av59 a_av5a = Foldl1_6989586621679129277 a_av59 a_av5a
  type Foldr a_av5l a_av5m a_av5n = Foldr_6989586621679129290 a_av5l a_av5m a_av5n
  type Foldr' a_av5A a_av5B a_av5C = Foldr'_6989586621679129305 a_av5A a_av5B a_av5C
  type Foldr1 a_av5V a_av5W = Foldr1_6989586621679129325 a_av5V a_av5W
  type Length a_av67 = Length_6989586621679129336 a_av67
  type Maximum a_av6d = Maximum_6989586621679129342 a_av6d
  type Minimum a_av6m = Minimum_6989586621679129351 a_av6m
  type Null a_av6v = Null_6989586621679129360 a_av6v
  type Product a_av6B = Product_6989586621679129366 a_av6B
  type Sum a_av6K = Sum_6989586621679129375 a_av6K
  type ToList a_av6T = ToList_6989586621679129384 a_av6T
sFind ::
  (forall (t_av70 :: (~>) a_augJ Bool) (t_av71 :: t_augI a_augJ).
    SFoldable t_augI =>
    Sing t_av70
    -> Sing t_av71
      -> Sing (Find t_av70 t_av71 :: Maybe a_augJ) :: Type)
sNotElem ::
  (forall (t_av75 :: a_augL) (t_av76 :: t_augK a_augL).
    (SFoldable t_augK, SEq a_augL) =>
    Sing t_av75
    -> Sing t_av76 -> Sing (NotElem t_av75 t_av76 :: Bool) :: Type)
sMinimumBy ::
  (forall (t_av7a :: (~>) a_augN ((~>) a_augN Ordering))
          (t_av7b :: t_augM a_augN).
    SFoldable t_augM =>
    Sing t_av7a
    -> Sing t_av7b -> Sing (MinimumBy t_av7a t_av7b :: a_augN) :: Type)
sMaximumBy ::
  (forall (t_av7f :: (~>) a_augP ((~>) a_augP Ordering))
          (t_av7g :: t_augO a_augP).
    SFoldable t_augO =>
    Sing t_av7f
    -> Sing t_av7g -> Sing (MaximumBy t_av7f t_av7g :: a_augP) :: Type)
sAll ::
  (forall (t_av7k :: (~>) a_augR Bool) (t_av7l :: t_augQ a_augR).
    SFoldable t_augQ =>
    Sing t_av7k
    -> Sing t_av7l -> Sing (All t_av7k t_av7l :: Bool) :: Type)
sAny ::
  (forall (t_av7p :: (~>) a_augT Bool) (t_av7q :: t_augS a_augT).
    SFoldable t_augS =>
    Sing t_av7p
    -> Sing t_av7q -> Sing (Any t_av7p t_av7q :: Bool) :: Type)
sOr ::
  (forall (t_av7u :: t_augU Bool).
    SFoldable t_augU =>
    Sing t_av7u -> Sing (Or t_av7u :: Bool) :: Type)
sAnd ::
  (forall (t_av7w :: t_augV Bool).
    SFoldable t_augV =>
    Sing t_av7w -> Sing (And t_av7w :: Bool) :: Type)
sConcatMap ::
  (forall (t_av7y :: (~>) a_augX [b_augY]) (t_av7z :: t_augW a_augX).
    SFoldable t_augW =>
    Sing t_av7y
    -> Sing t_av7z
      -> Sing (ConcatMap t_av7y t_av7z :: [b_augY]) :: Type)
sConcat ::
  (forall (t_av7D :: t_augZ [a_auh0]).
    SFoldable t_augZ =>
    Sing t_av7D -> Sing (Concat t_av7D :: [a_auh0]) :: Type)
sMsum ::
  forall t_auh1
          (m_auh2 :: Type -> Type)
          a_auh3
          (t_av7F :: t_auh1 (m_auh2 a_auh3)). (SFoldable t_auh1,
                                              SMonadPlus m_auh2) =>
                                              Sing t_av7F -> Sing (Msum t_av7F :: m_auh2 a_auh3)
sAsum ::
  forall t_auh4
          (f_auh5 :: Type -> Type)
          a_auh6
          (t_av7H :: t_auh4 (f_auh5 a_auh6)). (SFoldable t_auh4,
                                              SAlternative f_auh5) =>
                                              Sing t_av7H -> Sing (Asum t_av7H :: f_auh5 a_auh6)
sSequence_ ::
  (forall (t_av7J :: t_auh7 (m_auh8 a_auh9)).
    (SFoldable t_auh7, SMonad m_auh8) =>
    Sing t_av7J -> Sing (Sequence_ t_av7J :: m_auh8 ()) :: Type)
sSequenceA_ ::
  (forall (t_av7L :: t_auha (f_auhb a_auhc)).
    (SFoldable t_auha, SApplicative f_auhb) =>
    Sing t_av7L -> Sing (SequenceA_ t_av7L :: f_auhb ()) :: Type)
sForM_ ::
  (forall (t_av7N :: t_auhd a_auhf)
          (t_av7O :: (~>) a_auhf (m_auhe b_auhg)).
    (SFoldable t_auhd, SMonad m_auhe) =>
    Sing t_av7N
    -> Sing t_av7O -> Sing (ForM_ t_av7N t_av7O :: m_auhe ()) :: Type)
sMapM_ ::
  (forall (t_av7S :: (~>) a_auhj (m_auhi b_auhk))
          (t_av7T :: t_auhh a_auhj).
    (SFoldable t_auhh, SMonad m_auhi) =>
    Sing t_av7S
    -> Sing t_av7T -> Sing (MapM_ t_av7S t_av7T :: m_auhi ()) :: Type)
sFor_ ::
  (forall (t_av7X :: t_auhl a_auhn)
          (t_av7Y :: (~>) a_auhn (f_auhm b_auho)).
    (SFoldable t_auhl, SApplicative f_auhm) =>
    Sing t_av7X
    -> Sing t_av7Y -> Sing (For_ t_av7X t_av7Y :: f_auhm ()) :: Type)
sTraverse_ ::
  (forall (t_av82 :: (~>) a_auhr (f_auhq b_auhs))
          (t_av83 :: t_auhp a_auhr).
    (SFoldable t_auhp, SApplicative f_auhq) =>
    Sing t_av82
    -> Sing t_av83
      -> Sing (Traverse_ t_av82 t_av83 :: f_auhq ()) :: Type)
sFoldlM ::
  (forall (t_av87 :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv)))
          (t_av88 :: b_auhv)
          (t_av89 :: t_auht a_auhw).
    (SFoldable t_auht, SMonad m_auhu) =>
    Sing t_av87
    -> Sing t_av88
      -> Sing t_av89
          -> Sing (FoldlM t_av87 t_av88 t_av89 :: m_auhu b_auhv) :: Type)
sFoldrM ::
  (forall (t_av8h :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA)))
          (t_av8i :: b_auhA)
          (t_av8j :: t_auhx a_auhz).
    (SFoldable t_auhx, SMonad m_auhy) =>
    Sing t_av8h
    -> Sing t_av8i
      -> Sing t_av8j
          -> Sing (FoldrM t_av8h t_av8i t_av8j :: m_auhy b_auhA) :: Type)
sFind
  (sP :: Sing p_auIx)
  (sA_6989586621679127866 :: Sing a_6989586621679127866_auIy)
  = applySing
      (applySing
          (applySing
            (singFun3 @(.@#@$) (%.)) (singFun1 @GetFirstSym0 sGetFirst))
          (applySing
            (singFun2 @FoldMapSym0 sFoldMap)
            (singFun1
                @(LamCases_6989586621679127875Sym0 p_auIx a_6989586621679127866_auIy)
                (\cases
                  (sX :: Sing x_auIB)
                    -> applySing
                          (singFun1 @FirstSym0 SFirst)
                          (applySing
                            (singFun1
                                @(LamCases_6989586621679127878Sym0 x_auIB p_auIx a_6989586621679127866_auIy)
                                (\cases
                                  STrue -> applySing (singFun1 @JustSym0 SJust) sX
                                  SFalse -> SNothing))
                            (applySing sP sX))))))
      sA_6989586621679127866
sNotElem
  (sX :: Sing x_auIR)
  (sA_6989586621679127886 :: Sing a_6989586621679127886_auIS)
  = applySing
      (applySing
          (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @NotSym0 sNot))
          (applySing (singFun2 @ElemSym0 sElem) sX))
      sA_6989586621679127886
sMinimumBy
  (sCmp :: Sing cmp_auJ0)
  (sA_6989586621679127895 :: Sing a_6989586621679127895_auJ1)
  = applySing
      (let
          sMin' ::
            forall arg_av8z arg_av8A. Sing arg_av8z
                                      -> Sing arg_av8A
                                        -> Sing (Let6989586621679127904Min' cmp_auJ0 a_6989586621679127895_auJ1 arg_av8z arg_av8A)
          sMin' (sX :: Sing x_auJ6) (sY :: Sing y_auJ7)
            = applySing
                (singFun1
                  @(LamCases_6989586621679127910Sym0 x_auJ6 y_auJ7 cmp_auJ0 a_6989586621679127895_auJ1)
                  (\cases
                      SGT -> sY
                      SLT -> sX
                      SEQ -> sX))
                (applySing (applySing sCmp sX) sY)
        in
          applySing
            (singFun2 @Foldl1Sym0 sFoldl1)
            (singFun2
              @(Let6989586621679127904Min'Sym0 cmp_auJ0 a_6989586621679127895_auJ1)
              sMin'))
      sA_6989586621679127895
sMaximumBy
  (sCmp :: Sing cmp_auJk)
  (sA_6989586621679127915 :: Sing a_6989586621679127915_auJl)
  = applySing
      (let
          sMax' ::
            forall arg_av8E arg_av8F. Sing arg_av8E
                                      -> Sing arg_av8F
                                        -> Sing (Let6989586621679127924Max' cmp_auJk a_6989586621679127915_auJl arg_av8E arg_av8F)
          sMax' (sX :: Sing x_auJq) (sY :: Sing y_auJr)
            = applySing
                (singFun1
                  @(LamCases_6989586621679127930Sym0 x_auJq y_auJr cmp_auJk a_6989586621679127915_auJl)
                  (\cases
                      SGT -> sX
                      SLT -> sY
                      SEQ -> sY))
                (applySing (applySing sCmp sX) sY)
        in
          applySing
            (singFun2 @Foldl1Sym0 sFoldl1)
            (singFun2
              @(Let6989586621679127924Max'Sym0 cmp_auJk a_6989586621679127915_auJl)
              sMax'))
      sA_6989586621679127915
sAll
  (sP :: Sing p_auJE)
  (sA_6989586621679127935 :: Sing a_6989586621679127935_auJF)
  = applySing
      (applySing
          (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @GetAllSym0 sGetAll))
          (applySing
            (singFun2 @FoldMapSym0 sFoldMap)
            (applySing
                (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @All_Sym0 sAll_))
                sP)))
      sA_6989586621679127935
sAny
  (sP :: Sing p_auJN)
  (sA_6989586621679127944 :: Sing a_6989586621679127944_auJO)
  = applySing
      (applySing
          (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @GetAnySym0 sGetAny))
          (applySing
            (singFun2 @FoldMapSym0 sFoldMap)
            (applySing
                (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @Any_Sym0 sAny_))
                sP)))
      sA_6989586621679127944
sOr (sA_6989586621679127953 :: Sing a_6989586621679127953_auJU)
  = applySing
      (applySing
          (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @GetAnySym0 sGetAny))
          (applySing
            (singFun2 @FoldMapSym0 sFoldMap) (singFun1 @Any_Sym0 sAny_)))
      sA_6989586621679127953
sAnd (sA_6989586621679127959 :: Sing a_6989586621679127959_auK0)
  = applySing
      (applySing
          (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @GetAllSym0 sGetAll))
          (applySing
            (singFun2 @FoldMapSym0 sFoldMap) (singFun1 @All_Sym0 sAll_)))
      sA_6989586621679127959
sConcatMap (sF :: Sing f_auK6) (sXs :: Sing xs_auK7)
  = applySing
      (applySing
          (applySing
            (singFun3 @FoldrSym0 sFoldr)
            (singFun2
                @(LamCases_6989586621679127972Sym0 f_auK6 xs_auK7)
                (\cases
                  (sX :: Sing x_auKa) (sB :: Sing b_auKb)
                    -> applySing
                          (applySing
                            (applySing (singFun3 @FoldrSym0 sFoldr) (singFun2 @(:@#@$) SCons))
                            sB)
                          (applySing sF sX))))
          SNil)
      sXs
sConcat (sXs :: Sing xs_auKk)
  = applySing
      (applySing
          (applySing
            (singFun3 @FoldrSym0 sFoldr)
            (singFun2
                @(LamCases_6989586621679127985Sym0 xs_auKk)
                (\cases
                  (sX :: Sing x_auKn) (sY :: Sing y_auKo)
                    -> applySing
                          (applySing
                            (applySing (singFun3 @FoldrSym0 sFoldr) (singFun2 @(:@#@$) SCons))
                            sY)
                          sX)))
          SNil)
      sXs
sMsum (sA_6989586621679127994 :: Sing a_6989586621679127994_auKz)
  = applySing (singFun1 @AsumSym0 sAsum) sA_6989586621679127994
sAsum (sA_6989586621679128000 :: Sing a_6989586621679128000_auKF)
  = applySing
      (applySing
          (applySing
            (singFun3 @FoldrSym0 sFoldr) (singFun2 @(<|>@#@$) (%<|>)))
          sEmpty)
      sA_6989586621679128000
sSequence_
  (sA_6989586621679128006 :: Sing a_6989586621679128006_auKL)
  = applySing
      (applySing
          (applySing (singFun3 @FoldrSym0 sFoldr) (singFun2 @(>>@#@$) (%>>)))
          (applySing (singFun1 @ReturnSym0 sReturn) STuple0))
      sA_6989586621679128006
sSequenceA_
  (sA_6989586621679128012 :: Sing a_6989586621679128012_auKR)
  = applySing
      (applySing
          (applySing (singFun3 @FoldrSym0 sFoldr) (singFun2 @(*>@#@$) (%*>)))
          (applySing (singFun1 @PureSym0 sPure) STuple0))
      sA_6989586621679128012
sForM_
  (sA_6989586621679128018 :: Sing a_6989586621679128018_auL1)
  (sA_6989586621679128020 :: Sing a_6989586621679128020_auL2)
  = applySing
      (applySing
          (applySing (singFun3 @FlipSym0 sFlip) (singFun2 @MapM_Sym0 sMapM_))
          sA_6989586621679128018)
      sA_6989586621679128020
sMapM_
  (sF :: Sing f_auLa)
  (sA_6989586621679128029 :: Sing a_6989586621679128029_auLb)
  = applySing
      (applySing
          (applySing
            (singFun3 @FoldrSym0 sFoldr)
            (applySing
                (applySing (singFun3 @(.@#@$) (%.)) (singFun2 @(>>@#@$) (%>>)))
                sF))
          (applySing (singFun1 @ReturnSym0 sReturn) STuple0))
      sA_6989586621679128029
sFor_
  (sA_6989586621679128038 :: Sing a_6989586621679128038_auLl)
  (sA_6989586621679128040 :: Sing a_6989586621679128040_auLm)
  = applySing
      (applySing
          (applySing
            (singFun3 @FlipSym0 sFlip) (singFun2 @Traverse_Sym0 sTraverse_))
          sA_6989586621679128038)
      sA_6989586621679128040
sTraverse_
  (sF :: Sing f_auLu)
  (sA_6989586621679128049 :: Sing a_6989586621679128049_auLv)
  = applySing
      (applySing
          (applySing
            (singFun3 @FoldrSym0 sFoldr)
            (applySing
                (applySing (singFun3 @(.@#@$) (%.)) (singFun2 @(*>@#@$) (%*>)))
                sF))
          (applySing (singFun1 @PureSym0 sPure) STuple0))
      sA_6989586621679128049
sFoldlM
  (sF :: Sing f_auLD)
  (sZ0 :: Sing z0_auLE)
  (sXs :: Sing xs_auLF)
  = let
      sF' ::
        forall arg_av9P arg_av9Q arg_av9R. Sing arg_av9P
                                            -> Sing arg_av9Q
                                              -> Sing arg_av9R
                                                  -> Sing (Let6989586621679128068F' f_auLD z0_auLE xs_auLF arg_av9P arg_av9Q arg_av9R)
      sF' (sX :: Sing x_auLL) (sK :: Sing k_auLM) (sZ :: Sing z_auLN)
        = applySing
            (applySing
                (singFun2 @(>>=@#@$) (%>>=)) (applySing (applySing sF sZ) sX))
            sK
    in
      applySing
        (applySing
            (applySing
              (applySing
                  (singFun3 @FoldrSym0 sFoldr)
                  (singFun3
                    @(Let6989586621679128068F'Sym0 f_auLD z0_auLE xs_auLF) sF'))
              (singFun1 @ReturnSym0 sReturn))
            sXs)
        sZ0
sFoldrM
  (sF :: Sing f_auLV)
  (sZ0 :: Sing z0_auLW)
  (sXs :: Sing xs_auLX)
  = let
      sF' ::
        forall arg_ava3 arg_ava4 arg_ava5. Sing arg_ava3
                                            -> Sing arg_ava4
                                              -> Sing arg_ava5
                                                  -> Sing (Let6989586621679128086F' f_auLV z0_auLW xs_auLX arg_ava3 arg_ava4 arg_ava5)
      sF' (sK :: Sing k_auM3) (sX :: Sing x_auM4) (sZ :: Sing z_auM5)
        = applySing
            (applySing
                (singFun2 @(>>=@#@$) (%>>=)) (applySing (applySing sF sX) sZ))
            sK
    in
      applySing
        (applySing
            (applySing
              (applySing
                  (singFun3 @FoldlSym0 sFoldl)
                  (singFun3
                    @(Let6989586621679128086F'Sym0 f_auLV z0_auLW xs_auLX) sF'))
              (singFun1 @ReturnSym0 sReturn))
            sXs)
        sZ0
instance SFoldable t_augI =>
          SingI (FindSym0 :: (~>) ((~>) a_augJ Bool) ((~>) (t_augI a_augJ) (Maybe a_augJ))) where
  sing = singFun2 @FindSym0 sFind
instance (SFoldable t_augI, SingI d_av72) =>
          SingI (FindSym1 (d_av72 :: (~>) a_augJ Bool) :: (~>) (t_augI a_augJ) (Maybe a_augJ)) where
  sing
    = singFun1
        @(FindSym1 (d_av72 :: (~>) a_augJ Bool)) (sFind (sing @d_av72))
instance SFoldable t_augI =>
          SingI1 (FindSym1 :: (~>) a_augJ Bool
                              -> (~>) (t_augI a_augJ) (Maybe a_augJ)) where
  liftSing (s_av74 :: Sing (d_av72 :: (~>) a_augJ Bool))
    = singFun1 @(FindSym1 (d_av72 :: (~>) a_augJ Bool)) (sFind s_av74)
instance (SFoldable t_augK, SEq a_augL) =>
          SingI (NotElemSym0 :: (~>) a_augL ((~>) (t_augK a_augL) Bool)) where
  sing = singFun2 @NotElemSym0 sNotElem
instance (SFoldable t_augK, SEq a_augL, SingI d_av77) =>
          SingI (NotElemSym1 (d_av77 :: a_augL) :: (~>) (t_augK a_augL) Bool) where
  sing
    = singFun1
        @(NotElemSym1 (d_av77 :: a_augL)) (sNotElem (sing @d_av77))
instance (SFoldable t_augK, SEq a_augL) =>
          SingI1 (NotElemSym1 :: a_augL -> (~>) (t_augK a_augL) Bool) where
  liftSing (s_av79 :: Sing (d_av77 :: a_augL))
    = singFun1 @(NotElemSym1 (d_av77 :: a_augL)) (sNotElem s_av79)
instance SFoldable t_augM =>
          SingI (MinimumBySym0 :: (~>) ((~>) a_augN ((~>) a_augN Ordering)) ((~>) (t_augM a_augN) a_augN)) where
  sing = singFun2 @MinimumBySym0 sMinimumBy
instance (SFoldable t_augM, SingI d_av7c) =>
          SingI (MinimumBySym1 (d_av7c :: (~>) a_augN ((~>) a_augN Ordering)) :: (~>) (t_augM a_augN) a_augN) where
  sing
    = singFun1
        @(MinimumBySym1 (d_av7c :: (~>) a_augN ((~>) a_augN Ordering)))
        (sMinimumBy (sing @d_av7c))
instance SFoldable t_augM =>
          SingI1 (MinimumBySym1 :: (~>) a_augN ((~>) a_augN Ordering)
                                  -> (~>) (t_augM a_augN) a_augN) where
  liftSing
    (s_av7e :: Sing (d_av7c :: (~>) a_augN ((~>) a_augN Ordering)))
    = singFun1
        @(MinimumBySym1 (d_av7c :: (~>) a_augN ((~>) a_augN Ordering)))
        (sMinimumBy s_av7e)
instance SFoldable t_augO =>
          SingI (MaximumBySym0 :: (~>) ((~>) a_augP ((~>) a_augP Ordering)) ((~>) (t_augO a_augP) a_augP)) where
  sing = singFun2 @MaximumBySym0 sMaximumBy
instance (SFoldable t_augO, SingI d_av7h) =>
          SingI (MaximumBySym1 (d_av7h :: (~>) a_augP ((~>) a_augP Ordering)) :: (~>) (t_augO a_augP) a_augP) where
  sing
    = singFun1
        @(MaximumBySym1 (d_av7h :: (~>) a_augP ((~>) a_augP Ordering)))
        (sMaximumBy (sing @d_av7h))
instance SFoldable t_augO =>
          SingI1 (MaximumBySym1 :: (~>) a_augP ((~>) a_augP Ordering)
                                  -> (~>) (t_augO a_augP) a_augP) where
  liftSing
    (s_av7j :: Sing (d_av7h :: (~>) a_augP ((~>) a_augP Ordering)))
    = singFun1
        @(MaximumBySym1 (d_av7h :: (~>) a_augP ((~>) a_augP Ordering)))
        (sMaximumBy s_av7j)
instance SFoldable t_augQ =>
          SingI (AllSym0 :: (~>) ((~>) a_augR Bool) ((~>) (t_augQ a_augR) Bool)) where
  sing = singFun2 @AllSym0 sAll
instance (SFoldable t_augQ, SingI d_av7m) =>
          SingI (AllSym1 (d_av7m :: (~>) a_augR Bool) :: (~>) (t_augQ a_augR) Bool) where
  sing
    = singFun1
        @(AllSym1 (d_av7m :: (~>) a_augR Bool)) (sAll (sing @d_av7m))
instance SFoldable t_augQ =>
          SingI1 (AllSym1 :: (~>) a_augR Bool
                            -> (~>) (t_augQ a_augR) Bool) where
  liftSing (s_av7o :: Sing (d_av7m :: (~>) a_augR Bool))
    = singFun1 @(AllSym1 (d_av7m :: (~>) a_augR Bool)) (sAll s_av7o)
instance SFoldable t_augS =>
          SingI (AnySym0 :: (~>) ((~>) a_augT Bool) ((~>) (t_augS a_augT) Bool)) where
  sing = singFun2 @AnySym0 sAny
instance (SFoldable t_augS, SingI d_av7r) =>
          SingI (AnySym1 (d_av7r :: (~>) a_augT Bool) :: (~>) (t_augS a_augT) Bool) where
  sing
    = singFun1
        @(AnySym1 (d_av7r :: (~>) a_augT Bool)) (sAny (sing @d_av7r))
instance SFoldable t_augS =>
          SingI1 (AnySym1 :: (~>) a_augT Bool
                            -> (~>) (t_augS a_augT) Bool) where
  liftSing (s_av7t :: Sing (d_av7r :: (~>) a_augT Bool))
    = singFun1 @(AnySym1 (d_av7r :: (~>) a_augT Bool)) (sAny s_av7t)
instance SFoldable t_augU =>
          SingI (OrSym0 :: (~>) (t_augU Bool) Bool) where
  sing = singFun1 @OrSym0 sOr
instance SFoldable t_augV =>
          SingI (AndSym0 :: (~>) (t_augV Bool) Bool) where
  sing = singFun1 @AndSym0 sAnd
instance SFoldable t_augW =>
          SingI (ConcatMapSym0 :: (~>) ((~>) a_augX [b_augY]) ((~>) (t_augW a_augX) [b_augY])) where
  sing = singFun2 @ConcatMapSym0 sConcatMap
instance (SFoldable t_augW, SingI d_av7A) =>
          SingI (ConcatMapSym1 (d_av7A :: (~>) a_augX [b_augY]) :: (~>) (t_augW a_augX) [b_augY]) where
  sing
    = singFun1
        @(ConcatMapSym1 (d_av7A :: (~>) a_augX [b_augY]))
        (sConcatMap (sing @d_av7A))
instance SFoldable t_augW =>
          SingI1 (ConcatMapSym1 :: (~>) a_augX [b_augY]
                                  -> (~>) (t_augW a_augX) [b_augY]) where
  liftSing (s_av7C :: Sing (d_av7A :: (~>) a_augX [b_augY]))
    = singFun1
        @(ConcatMapSym1 (d_av7A :: (~>) a_augX [b_augY]))
        (sConcatMap s_av7C)
instance SFoldable t_augZ =>
          SingI (ConcatSym0 :: (~>) (t_augZ [a_auh0]) [a_auh0]) where
  sing = singFun1 @ConcatSym0 sConcat
instance (SFoldable t_auh1, SMonadPlus m_auh2) =>
          SingI (MsumSym0 :: (~>) (t_auh1 (m_auh2 a_auh3)) (m_auh2 a_auh3)) where
  sing = singFun1 @MsumSym0 sMsum
instance (SFoldable t_auh4, SAlternative f_auh5) =>
          SingI (AsumSym0 :: (~>) (t_auh4 (f_auh5 a_auh6)) (f_auh5 a_auh6)) where
  sing = singFun1 @AsumSym0 sAsum
instance (SFoldable t_auh7, SMonad m_auh8) =>
          SingI (Sequence_Sym0 :: (~>) (t_auh7 (m_auh8 a_auh9)) (m_auh8 ())) where
  sing = singFun1 @Sequence_Sym0 sSequence_
instance (SFoldable t_auha, SApplicative f_auhb) =>
          SingI (SequenceA_Sym0 :: (~>) (t_auha (f_auhb a_auhc)) (f_auhb ())) where
  sing = singFun1 @SequenceA_Sym0 sSequenceA_
instance (SFoldable t_auhd, SMonad m_auhe) =>
          SingI (ForM_Sym0 :: (~>) (t_auhd a_auhf) ((~>) ((~>) a_auhf (m_auhe b_auhg)) (m_auhe ()))) where
  sing = singFun2 @ForM_Sym0 sForM_
instance (SFoldable t_auhd, SMonad m_auhe, SingI d_av7P) =>
          SingI (ForM_Sym1 (d_av7P :: t_auhd a_auhf) :: (~>) ((~>) a_auhf (m_auhe b_auhg)) (m_auhe ())) where
  sing
    = singFun1
        @(ForM_Sym1 (d_av7P :: t_auhd a_auhf)) (sForM_ (sing @d_av7P))
instance (SFoldable t_auhd, SMonad m_auhe) =>
          SingI1 (ForM_Sym1 :: t_auhd a_auhf
                              -> (~>) ((~>) a_auhf (m_auhe b_auhg)) (m_auhe ())) where
  liftSing (s_av7R :: Sing (d_av7P :: t_auhd a_auhf))
    = singFun1 @(ForM_Sym1 (d_av7P :: t_auhd a_auhf)) (sForM_ s_av7R)
instance (SFoldable t_auhh, SMonad m_auhi) =>
          SingI (MapM_Sym0 :: (~>) ((~>) a_auhj (m_auhi b_auhk)) ((~>) (t_auhh a_auhj) (m_auhi ()))) where
  sing = singFun2 @MapM_Sym0 sMapM_
instance (SFoldable t_auhh, SMonad m_auhi, SingI d_av7U) =>
          SingI (MapM_Sym1 (d_av7U :: (~>) a_auhj (m_auhi b_auhk)) :: (~>) (t_auhh a_auhj) (m_auhi ())) where
  sing
    = singFun1
        @(MapM_Sym1 (d_av7U :: (~>) a_auhj (m_auhi b_auhk)))
        (sMapM_ (sing @d_av7U))
instance (SFoldable t_auhh, SMonad m_auhi) =>
          SingI1 (MapM_Sym1 :: (~>) a_auhj (m_auhi b_auhk)
                              -> (~>) (t_auhh a_auhj) (m_auhi ())) where
  liftSing (s_av7W :: Sing (d_av7U :: (~>) a_auhj (m_auhi b_auhk)))
    = singFun1
        @(MapM_Sym1 (d_av7U :: (~>) a_auhj (m_auhi b_auhk)))
        (sMapM_ s_av7W)
instance (SFoldable t_auhl, SApplicative f_auhm) =>
          SingI (For_Sym0 :: (~>) (t_auhl a_auhn) ((~>) ((~>) a_auhn (f_auhm b_auho)) (f_auhm ()))) where
  sing = singFun2 @For_Sym0 sFor_
instance (SFoldable t_auhl, SApplicative f_auhm, SingI d_av7Z) =>
          SingI (For_Sym1 (d_av7Z :: t_auhl a_auhn) :: (~>) ((~>) a_auhn (f_auhm b_auho)) (f_auhm ())) where
  sing
    = singFun1
        @(For_Sym1 (d_av7Z :: t_auhl a_auhn)) (sFor_ (sing @d_av7Z))
instance (SFoldable t_auhl, SApplicative f_auhm) =>
          SingI1 (For_Sym1 :: t_auhl a_auhn
                              -> (~>) ((~>) a_auhn (f_auhm b_auho)) (f_auhm ())) where
  liftSing (s_av81 :: Sing (d_av7Z :: t_auhl a_auhn))
    = singFun1 @(For_Sym1 (d_av7Z :: t_auhl a_auhn)) (sFor_ s_av81)
instance (SFoldable t_auhp, SApplicative f_auhq) =>
          SingI (Traverse_Sym0 :: (~>) ((~>) a_auhr (f_auhq b_auhs)) ((~>) (t_auhp a_auhr) (f_auhq ()))) where
  sing = singFun2 @Traverse_Sym0 sTraverse_
instance (SFoldable t_auhp, SApplicative f_auhq, SingI d_av84) =>
          SingI (Traverse_Sym1 (d_av84 :: (~>) a_auhr (f_auhq b_auhs)) :: (~>) (t_auhp a_auhr) (f_auhq ())) where
  sing
    = singFun1
        @(Traverse_Sym1 (d_av84 :: (~>) a_auhr (f_auhq b_auhs)))
        (sTraverse_ (sing @d_av84))
instance (SFoldable t_auhp, SApplicative f_auhq) =>
          SingI1 (Traverse_Sym1 :: (~>) a_auhr (f_auhq b_auhs)
                                  -> (~>) (t_auhp a_auhr) (f_auhq ())) where
  liftSing (s_av86 :: Sing (d_av84 :: (~>) a_auhr (f_auhq b_auhs)))
    = singFun1
        @(Traverse_Sym1 (d_av84 :: (~>) a_auhr (f_auhq b_auhs)))
        (sTraverse_ s_av86)
instance (SFoldable t_auht, SMonad m_auhu) =>
          SingI (FoldlMSym0 :: (~>) ((~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) ((~>) b_auhv ((~>) (t_auht a_auhw) (m_auhu b_auhv)))) where
  sing = singFun3 @FoldlMSym0 sFoldlM
instance (SFoldable t_auht, SMonad m_auhu, SingI d_av8a) =>
          SingI (FoldlMSym1 (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) :: (~>) b_auhv ((~>) (t_auht a_auhw) (m_auhu b_auhv))) where
  sing
    = singFun2
        @(FoldlMSym1 (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))))
        (sFoldlM (sing @d_av8a))
instance (SFoldable t_auht, SMonad m_auhu) =>
          SingI1 (FoldlMSym1 :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))
                                -> (~>) b_auhv ((~>) (t_auht a_auhw) (m_auhu b_auhv))) where
  liftSing
    (s_av8g :: Sing (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))))
    = singFun2
        @(FoldlMSym1 (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))))
        (sFoldlM s_av8g)
instance (SFoldable t_auht,
          SMonad m_auhu,
          SingI d_av8a,
          SingI d_av8b) =>
          SingI (FoldlMSym2 (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) (d_av8b :: b_auhv) :: (~>) (t_auht a_auhw) (m_auhu b_auhv)) where
  sing
    = singFun1
        @(FoldlMSym2 (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) (d_av8b :: b_auhv))
        (sFoldlM (sing @d_av8a) (sing @d_av8b))
instance (SFoldable t_auht, SMonad m_auhu, SingI d_av8a) =>
          SingI1 (FoldlMSym2 (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) :: b_auhv
                                                                                      -> (~>) (t_auht a_auhw) (m_auhu b_auhv)) where
  liftSing (s_av8d :: Sing (d_av8b :: b_auhv))
    = singFun1
        @(FoldlMSym2 (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) (d_av8b :: b_auhv))
        (sFoldlM (sing @d_av8a) s_av8d)
instance (SFoldable t_auht, SMonad m_auhu) =>
          SingI2 (FoldlMSym2 :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))
                                -> b_auhv -> (~>) (t_auht a_auhw) (m_auhu b_auhv)) where
  liftSing2
    (s_av8e :: Sing (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))))
    (s_av8f :: Sing (d_av8b :: b_auhv))
    = singFun1
        @(FoldlMSym2 (d_av8a :: (~>) b_auhv ((~>) a_auhw (m_auhu b_auhv))) (d_av8b :: b_auhv))
        (sFoldlM s_av8e s_av8f)
instance (SFoldable t_auhx, SMonad m_auhy) =>
          SingI (FoldrMSym0 :: (~>) ((~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) ((~>) b_auhA ((~>) (t_auhx a_auhz) (m_auhy b_auhA)))) where
  sing = singFun3 @FoldrMSym0 sFoldrM
instance (SFoldable t_auhx, SMonad m_auhy, SingI d_av8k) =>
          SingI (FoldrMSym1 (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) :: (~>) b_auhA ((~>) (t_auhx a_auhz) (m_auhy b_auhA))) where
  sing
    = singFun2
        @(FoldrMSym1 (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))))
        (sFoldrM (sing @d_av8k))
instance (SFoldable t_auhx, SMonad m_auhy) =>
          SingI1 (FoldrMSym1 :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))
                                -> (~>) b_auhA ((~>) (t_auhx a_auhz) (m_auhy b_auhA))) where
  liftSing
    (s_av8q :: Sing (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))))
    = singFun2
        @(FoldrMSym1 (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))))
        (sFoldrM s_av8q)
instance (SFoldable t_auhx,
          SMonad m_auhy,
          SingI d_av8k,
          SingI d_av8l) =>
          SingI (FoldrMSym2 (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) (d_av8l :: b_auhA) :: (~>) (t_auhx a_auhz) (m_auhy b_auhA)) where
  sing
    = singFun1
        @(FoldrMSym2 (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) (d_av8l :: b_auhA))
        (sFoldrM (sing @d_av8k) (sing @d_av8l))
instance (SFoldable t_auhx, SMonad m_auhy, SingI d_av8k) =>
          SingI1 (FoldrMSym2 (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) :: b_auhA
                                                                                      -> (~>) (t_auhx a_auhz) (m_auhy b_auhA)) where
  liftSing (s_av8n :: Sing (d_av8l :: b_auhA))
    = singFun1
        @(FoldrMSym2 (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) (d_av8l :: b_auhA))
        (sFoldrM (sing @d_av8k) s_av8n)
instance (SFoldable t_auhx, SMonad m_auhy) =>
          SingI2 (FoldrMSym2 :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))
                                -> b_auhA -> (~>) (t_auhx a_auhz) (m_auhy b_auhA)) where
  liftSing2
    (s_av8o :: Sing (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))))
    (s_av8p :: Sing (d_av8l :: b_auhA))
    = singFun1
        @(FoldrMSym2 (d_av8k :: (~>) a_auhz ((~>) b_auhA (m_auhy b_auhA))) (d_av8l :: b_auhA))
        (sFoldrM s_av8o s_av8p)
class SFoldable t_auic where
  sFold ::
    (forall (t_avad :: t_auic m_auid).
      SMonoid m_auid =>
      Sing t_avad -> Sing (Fold t_avad :: m_auid) :: Type)
  sFoldMap ::
    (forall (t_avaf :: (~>) a_auif m_auie) (t_avag :: t_auic a_auif).
      SMonoid m_auie =>
      Sing t_avaf
      -> Sing t_avag -> Sing (FoldMap t_avaf t_avag :: m_auie) :: Type)
  sFoldr ::
    (forall (t_avak :: (~>) a_auig ((~>) b_auih b_auih))
            (t_aval :: b_auih)
            (t_avam :: t_auic a_auig).
      Sing t_avak
      -> Sing t_aval
        -> Sing t_avam
            -> Sing (Foldr t_avak t_aval t_avam :: b_auih) :: Type)
  sFoldr' ::
    (forall (t_avau :: (~>) a_auii ((~>) b_auij b_auij))
            (t_avav :: b_auij)
            (t_avaw :: t_auic a_auii).
      Sing t_avau
      -> Sing t_avav
        -> Sing t_avaw
            -> Sing (Foldr' t_avau t_avav t_avaw :: b_auij) :: Type)
  sFoldl ::
    (forall (t_avaE :: (~>) b_auik ((~>) a_auil b_auik))
            (t_avaF :: b_auik)
            (t_avaG :: t_auic a_auil).
      Sing t_avaE
      -> Sing t_avaF
        -> Sing t_avaG
            -> Sing (Foldl t_avaE t_avaF t_avaG :: b_auik) :: Type)
  sFoldl' ::
    (forall (t_avaO :: (~>) b_auim ((~>) a_auin b_auim))
            (t_avaP :: b_auim)
            (t_avaQ :: t_auic a_auin).
      Sing t_avaO
      -> Sing t_avaP
        -> Sing t_avaQ
            -> Sing (Foldl' t_avaO t_avaP t_avaQ :: b_auim) :: Type)
  sFoldr1 ::
    (forall (t_avaY :: (~>) a_auio ((~>) a_auio a_auio))
            (t_avaZ :: t_auic a_auio).
      Sing t_avaY
      -> Sing t_avaZ -> Sing (Foldr1 t_avaY t_avaZ :: a_auio) :: Type)
  sFoldl1 ::
    (forall (t_avb3 :: (~>) a_auip ((~>) a_auip a_auip))
            (t_avb4 :: t_auic a_auip).
      Sing t_avb3
      -> Sing t_avb4 -> Sing (Foldl1 t_avb3 t_avb4 :: a_auip) :: Type)
  sToList ::
    (forall (t_avb8 :: t_auic a_auiq).
      Sing t_avb8 -> Sing (ToList t_avb8 :: [a_auiq]) :: Type)
  sNull ::
    (forall (t_avba :: t_auic a_auir).
      Sing t_avba -> Sing (Null t_avba :: Bool) :: Type)
  sLength ::
    (forall (t_avbc :: t_auic a_auis).
      Sing t_avbc -> Sing (Length t_avbc :: Natural) :: Type)
  sElem ::
    (forall (t_avbe :: a_auit) (t_avbf :: t_auic a_auit).
      SEq a_auit =>
      Sing t_avbe
      -> Sing t_avbf -> Sing (Elem t_avbe t_avbf :: Bool) :: Type)
  sMaximum ::
    forall a_auiu (t_avbj :: t_auic a_auiu). SOrd a_auiu =>
                                              Sing t_avbj -> Sing (Maximum t_avbj :: a_auiu)
  sMinimum ::
    forall a_auiv (t_avbl :: t_auic a_auiv). SOrd a_auiv =>
                                              Sing t_avbl -> Sing (Minimum t_avbl :: a_auiv)
  sSum ::
    (forall (t_avbn :: t_auic a_auiw).
      SNum a_auiw => Sing t_avbn -> Sing (Sum t_avbn :: a_auiw) :: Type)
  sProduct ::
    (forall (t_avbp :: t_auic a_auix).
      SNum a_auix =>
      Sing t_avbp -> Sing (Product t_avbp :: a_auix) :: Type)
  default sFold ::
            (forall (t_avad :: t_auic m_auid).
              ((Fold t_avad :: m_auid) ~ Fold_6989586621679128167 t_avad,
              SMonoid m_auid) =>
              Sing t_avad -> Sing (Fold t_avad :: m_auid) :: Type)
  default sFoldMap ::
            (forall (t_avaf :: (~>) a_auif m_auie) (t_avag :: t_auic a_auif).
              ((FoldMap t_avaf t_avag :: m_auie)
              ~ FoldMap_6989586621679128177 t_avaf t_avag,
              SMonoid m_auie) =>
              Sing t_avaf
              -> Sing t_avag -> Sing (FoldMap t_avaf t_avag :: m_auie) :: Type)
  default sFoldr ::
            (forall (t_avak :: (~>) a_auig ((~>) b_auih b_auih))
                    (t_aval :: b_auih)
                    (t_avam :: t_auic a_auig).
              ((Foldr t_avak t_aval t_avam :: b_auih)
              ~ Foldr_6989586621679128191 t_avak t_aval t_avam) =>
              Sing t_avak
              -> Sing t_aval
                -> Sing t_avam
                    -> Sing (Foldr t_avak t_aval t_avam :: b_auih) :: Type)
  default sFoldr' ::
            (forall (t_avau :: (~>) a_auii ((~>) b_auij b_auij))
                    (t_avav :: b_auij)
                    (t_avaw :: t_auic a_auii).
              ((Foldr' t_avau t_avav t_avaw :: b_auij)
              ~ Foldr'_6989586621679128206 t_avau t_avav t_avaw) =>
              Sing t_avau
              -> Sing t_avav
                -> Sing t_avaw
                    -> Sing (Foldr' t_avau t_avav t_avaw :: b_auij) :: Type)
  default sFoldl ::
            (forall (t_avaE :: (~>) b_auik ((~>) a_auil b_auik))
                    (t_avaF :: b_auik)
                    (t_avaG :: t_auic a_auil).
              ((Foldl t_avaE t_avaF t_avaG :: b_auik)
              ~ Foldl_6989586621679128229 t_avaE t_avaF t_avaG) =>
              Sing t_avaE
              -> Sing t_avaF
                -> Sing t_avaG
                    -> Sing (Foldl t_avaE t_avaF t_avaG :: b_auik) :: Type)
  default sFoldl' ::
            (forall (t_avaO :: (~>) b_auim ((~>) a_auin b_auim))
                    (t_avaP :: b_auim)
                    (t_avaQ :: t_auic a_auin).
              ((Foldl' t_avaO t_avaP t_avaQ :: b_auim)
              ~ Foldl'_6989586621679128244 t_avaO t_avaP t_avaQ) =>
              Sing t_avaO
              -> Sing t_avaP
                -> Sing t_avaQ
                    -> Sing (Foldl' t_avaO t_avaP t_avaQ :: b_auim) :: Type)
  default sFoldr1 ::
            (forall (t_avaY :: (~>) a_auio ((~>) a_auio a_auio))
                    (t_avaZ :: t_auic a_auio).
              ((Foldr1 t_avaY t_avaZ :: a_auio)
              ~ Foldr1_6989586621679128266 t_avaY t_avaZ) =>
              Sing t_avaY
              -> Sing t_avaZ -> Sing (Foldr1 t_avaY t_avaZ :: a_auio) :: Type)
  default sFoldl1 ::
            (forall (t_avb3 :: (~>) a_auip ((~>) a_auip a_auip))
                    (t_avb4 :: t_auic a_auip).
              ((Foldl1 t_avb3 t_avb4 :: a_auip)
              ~ Foldl1_6989586621679128289 t_avb3 t_avb4) =>
              Sing t_avb3
              -> Sing t_avb4 -> Sing (Foldl1 t_avb3 t_avb4 :: a_auip) :: Type)
  default sToList ::
            (forall (t_avb8 :: t_auic a_auiq).
              ((ToList t_avb8 :: [a_auiq])
              ~ ToList_6989586621679128311 t_avb8) =>
              Sing t_avb8 -> Sing (ToList t_avb8 :: [a_auiq]) :: Type)
  default sNull ::
            (forall (t_avba :: t_auic a_auir).
              ((Null t_avba :: Bool) ~ Null_6989586621679128320 t_avba) =>
              Sing t_avba -> Sing (Null t_avba :: Bool) :: Type)
  default sLength ::
            (forall (t_avbc :: t_auic a_auis).
              ((Length t_avbc :: Natural) ~ Length_6989586621679128336 t_avbc) =>
              Sing t_avbc -> Sing (Length t_avbc :: Natural) :: Type)
  default sElem ::
            (forall (t_avbe :: a_auit) (t_avbf :: t_auic a_auit).
              ((Elem t_avbe t_avbf :: Bool)
              ~ Elem_6989586621679128354 t_avbe t_avbf,
              SEq a_auit) =>
              Sing t_avbe
              -> Sing t_avbf -> Sing (Elem t_avbe t_avbf :: Bool) :: Type)
  default sMaximum ::
            forall a_auiu
                    (t_avbj :: t_auic a_auiu). ((Maximum t_avbj :: a_auiu)
                                                ~ Maximum_6989586621679128368 t_avbj,
                                                SOrd a_auiu) =>
                                              Sing t_avbj -> Sing (Maximum t_avbj :: a_auiu)
  default sMinimum ::
            forall a_auiv
                    (t_avbl :: t_auic a_auiv). ((Minimum t_avbl :: a_auiv)
                                                ~ Minimum_6989586621679128383 t_avbl,
                                                SOrd a_auiv) =>
                                              Sing t_avbl -> Sing (Minimum t_avbl :: a_auiv)
  default sSum ::
            (forall (t_avbn :: t_auic a_auiw).
              ((Sum t_avbn :: a_auiw) ~ Sum_6989586621679128398 t_avbn,
              SNum a_auiw) =>
              Sing t_avbn -> Sing (Sum t_avbn :: a_auiw) :: Type)
  default sProduct ::
            (forall (t_avbp :: t_auic a_auix).
              ((Product t_avbp :: a_auix) ~ Product_6989586621679128407 t_avbp,
              SNum a_auix) =>
              Sing t_avbp -> Sing (Product t_avbp :: a_auix) :: Type)
  sFold (sA_6989586621679128169 :: Sing a_6989586621679128169_auNo)
    = applySing
        (applySing (singFun2 @FoldMapSym0 sFoldMap) (singFun1 @IdSym0 sId))
        sA_6989586621679128169
  sFoldMap
    (sF :: Sing f_auNA)
    (sA_6989586621679128179 :: Sing a_6989586621679128179_auNB)
    = applySing
        (applySing
            (applySing
              (singFun3 @FoldrSym0 sFoldr)
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.)) (singFun2 @MappendSym0 sMappend))
                  sF))
            sMempty)
        sA_6989586621679128179
  sFoldr (sF :: Sing f_auNO) (sZ :: Sing z_auNP) (sT :: Sing t_auNQ)
    = applySing
        (applySing
            (singFun2 @AppEndoSym0 sAppEndo)
            (applySing
              (applySing
                  (singFun2 @FoldMapSym0 sFoldMap)
                  (applySing
                    (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @EndoSym0 SEndo))
                    sF))
              sT))
        sZ
  sFoldr'
    (sF :: Sing f_auO3)
    (sZ0 :: Sing z0_auO4)
    (sXs :: Sing xs_auO5)
    = let
        sF' ::
          forall arg_avbr arg_avbs arg_avbt. Sing arg_avbr
                                              -> Sing arg_avbs
                                                -> Sing arg_avbt
                                                    -> Sing (Let6989586621679128218F' t_auic f_auO3 z0_auO4 xs_auO5 arg_avbr arg_avbs arg_avbt)
        sF' (sK :: Sing k_auOb) (sX :: Sing x_auOc) (sZ :: Sing z_auOd)
          = applySing
              (applySing (singFun2 @($!@#@$) (%$!)) sK)
              (applySing (applySing sF sX) sZ)
      in
        applySing
          (applySing
              (applySing
                (applySing
                    (singFun3 @FoldlSym0 sFoldl)
                    (singFun3
                      @(Let6989586621679128218F'Sym0 t_auic f_auO3 z0_auO4 xs_auO5) sF'))
                (singFun1 @IdSym0 sId))
              sXs)
          sZ0
  sFoldl (sF :: Sing f_auOq) (sZ :: Sing z_auOr) (sT :: Sing t_auOs)
    = applySing
        (applySing
            (singFun2 @AppEndoSym0 sAppEndo)
            (applySing
              (singFun1 @GetDualSym0 sGetDual)
              (applySing
                  (applySing
                    (singFun2 @FoldMapSym0 sFoldMap)
                    (applySing
                        (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @DualSym0 SDual))
                        (applySing
                          (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @EndoSym0 SEndo))
                          (applySing (singFun3 @FlipSym0 sFlip) sF))))
                  sT)))
        sZ
  sFoldl'
    (sF :: Sing f_auOF)
    (sZ0 :: Sing z0_auOG)
    (sXs :: Sing xs_auOH)
    = let
        sF' ::
          forall arg_avbK arg_avbL arg_avbM. Sing arg_avbK
                                              -> Sing arg_avbL
                                                -> Sing arg_avbM
                                                    -> Sing (Let6989586621679128256F' t_auic f_auOF z0_auOG xs_auOH arg_avbK arg_avbL arg_avbM)
        sF' (sX :: Sing x_auON) (sK :: Sing k_auOO) (sZ :: Sing z_auOP)
          = applySing
              (applySing (singFun2 @($!@#@$) (%$!)) sK)
              (applySing (applySing sF sZ) sX)
      in
        applySing
          (applySing
              (applySing
                (applySing
                    (singFun3 @FoldrSym0 sFoldr)
                    (singFun3
                      @(Let6989586621679128256F'Sym0 t_auic f_auOF z0_auOG xs_auOH) sF'))
                (singFun1 @IdSym0 sId))
              sXs)
          sZ0
  sFoldr1 (sF :: Sing f_auOZ) (sXs :: Sing xs_auP0)
    = let
        sMf ::
          forall arg_avbU arg_avbV. Sing arg_avbU
                                    -> Sing arg_avbV
                                        -> Sing (Let6989586621679128275Mf t_auic f_auOZ xs_auP0 arg_avbU arg_avbV)
        sMf (sX :: Sing x_auP5) (sM :: Sing m_auP6)
          = applySing
              (singFun1 @JustSym0 SJust)
              (applySing
                  (singFun1
                    @(LamCases_6989586621679128281Sym0 t_auic x_auP5 m_auP6 f_auOZ xs_auP0)
                    (\cases
                        SNothing -> sX
                        (SJust (sY :: Sing y_auP9)) -> applySing (applySing sF sX) sY))
                  sM)
      in
        applySing
          (applySing
              (singFun2 @FromMaybeSym0 sFromMaybe)
              (applySing
                (singFun1 @ErrorWithoutStackTraceSym0 sErrorWithoutStackTrace)
                (sing :: Sing "foldr1: empty structure")))
          (applySing
              (applySing
                (applySing
                    (singFun3 @FoldrSym0 sFoldr)
                    (singFun2
                      @(Let6989586621679128275MfSym0 t_auic f_auOZ xs_auP0) sMf))
                SNothing)
              sXs)
  sFoldl1 (sF :: Sing f_auPm) (sXs :: Sing xs_auPn)
    = let
        sMf ::
          forall arg_avc9 arg_avca. Sing arg_avc9
                                    -> Sing arg_avca
                                        -> Sing (Let6989586621679128298Mf t_auic f_auPm xs_auPn arg_avc9 arg_avca)
        sMf (sM :: Sing m_auPs) (sY :: Sing y_auPt)
          = applySing
              (singFun1 @JustSym0 SJust)
              (applySing
                  (singFun1
                    @(LamCases_6989586621679128304Sym0 t_auic m_auPs y_auPt f_auPm xs_auPn)
                    (\cases
                        SNothing -> sY
                        (SJust (sX :: Sing x_auPw)) -> applySing (applySing sF sX) sY))
                  sM)
      in
        applySing
          (applySing
              (singFun2 @FromMaybeSym0 sFromMaybe)
              (applySing
                (singFun1 @ErrorWithoutStackTraceSym0 sErrorWithoutStackTrace)
                (sing :: Sing "foldl1: empty structure")))
          (applySing
              (applySing
                (applySing
                    (singFun3 @FoldlSym0 sFoldl)
                    (singFun2
                      @(Let6989586621679128298MfSym0 t_auic f_auPm xs_auPn) sMf))
                SNothing)
              sXs)
  sToList (sA_6989586621679128313 :: Sing a_6989586621679128313_auPI)
    = applySing
        (applySing
            (applySing (singFun3 @FoldrSym0 sFoldr) (singFun2 @(:@#@$) SCons))
            SNil)
        sA_6989586621679128313
  sNull (sA_6989586621679128322 :: Sing a_6989586621679128322_auPR)
    = applySing
        (applySing
            (applySing
              (singFun3 @FoldrSym0 sFoldr)
              (singFun2
                  @(LamCases_6989586621679128328Sym0 t_auic a_6989586621679128322_auPR)
                  (\cases _ _ -> SFalse)))
            STrue)
        sA_6989586621679128322
  sLength (sA_6989586621679128338 :: Sing a_6989586621679128338_auQ7)
    = applySing
        (applySing
            (applySing
              (singFun3 @Foldl'Sym0 sFoldl')
              (singFun2
                  @(LamCases_6989586621679128344Sym0 t_auic a_6989586621679128338_auQ7)
                  (\cases
                    (sC :: Sing c_auQa) _
                      -> applySing
                            (applySing (singFun2 @(+@#@$) (%+)) sC)
                            (sFromInteger (sing :: Sing 1)))))
            (sFromInteger (sing :: Sing 0)))
        sA_6989586621679128338
  sElem
    (sA_6989586621679128356 :: Sing a_6989586621679128356_auQt)
    (sA_6989586621679128358 :: Sing a_6989586621679128358_auQu)
    = applySing
        (applySing
            (applySing
              (applySing (singFun3 @(.@#@$) (%.)) (singFun2 @AnySym0 sAny))
              (singFun2 @(==@#@$) (%==)))
            sA_6989586621679128356)
        sA_6989586621679128358
  sMaximum
    (sA_6989586621679128370 :: Sing a_6989586621679128370_auQD)
    = applySing
        (let
            sMkJust ::
              (forall (t_avci :: a_auiu).
              Sing t_avci
              -> Sing (Let6989586621679128376MkJust t_auic a_auiu a_6989586621679128370_auQD t_avci :: Maybe a_auiu) :: Type)
            sMkJust (sA_6989586621679128377 :: Sing a_6989586621679128377_auQJ)
              = applySing (singFun1 @JustSym0 SJust) sA_6989586621679128377
          in
            applySing
              (applySing
                (singFun3 @(.@#@$) (%.))
                (applySing
                    (singFun2 @FromMaybeSym0 sFromMaybe)
                    (applySing
                      (singFun1 @ErrorWithoutStackTraceSym0 sErrorWithoutStackTrace)
                      (sing :: Sing "maximum: empty structure"))))
              (applySing
                (applySing
                    (singFun3 @(.@#@$) (%.))
                    (singFun1 @GetMaxInternalSym0 sGetMaxInternal))
                (applySing
                    (singFun2 @FoldMapSym0 sFoldMap)
                    (applySing
                      (applySing
                          (singFun3 @(.@#@$) (%.)) (singFun1 @MaxInternalSym0 SMaxInternal))
                      (singFun1
                          @(Let6989586621679128376MkJustSym0 t_auic a_auiu a_6989586621679128370_auQD)
                          sMkJust)))))
        sA_6989586621679128370
  sMinimum
    (sA_6989586621679128385 :: Sing a_6989586621679128385_auQS)
    = applySing
        (let
            sMkJust ::
              (forall (t_avck :: a_auiv).
              Sing t_avck
              -> Sing (Let6989586621679128391MkJust t_auic a_auiv a_6989586621679128385_auQS t_avck :: Maybe a_auiv) :: Type)
            sMkJust (sA_6989586621679128392 :: Sing a_6989586621679128392_auQY)
              = applySing (singFun1 @JustSym0 SJust) sA_6989586621679128392
          in
            applySing
              (applySing
                (singFun3 @(.@#@$) (%.))
                (applySing
                    (singFun2 @FromMaybeSym0 sFromMaybe)
                    (applySing
                      (singFun1 @ErrorWithoutStackTraceSym0 sErrorWithoutStackTrace)
                      (sing :: Sing "minimum: empty structure"))))
              (applySing
                (applySing
                    (singFun3 @(.@#@$) (%.))
                    (singFun1 @GetMinInternalSym0 sGetMinInternal))
                (applySing
                    (singFun2 @FoldMapSym0 sFoldMap)
                    (applySing
                      (applySing
                          (singFun3 @(.@#@$) (%.)) (singFun1 @MinInternalSym0 SMinInternal))
                      (singFun1
                          @(Let6989586621679128391MkJustSym0 t_auic a_auiv a_6989586621679128385_auQS)
                          sMkJust)))))
        sA_6989586621679128385
  sSum (sA_6989586621679128400 :: Sing a_6989586621679128400_auR7)
    = applySing
        (applySing
            (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @GetSumSym0 sGetSum))
            (applySing
              (singFun2 @FoldMapSym0 sFoldMap) (singFun1 @Sum_Sym0 sSum_)))
        sA_6989586621679128400
  sProduct
    (sA_6989586621679128409 :: Sing a_6989586621679128409_auRg)
    = applySing
        (applySing
            (applySing
              (singFun3 @(.@#@$) (%.)) (singFun1 @GetProductSym0 sGetProduct))
            (applySing
              (singFun2 @FoldMapSym0 sFoldMap)
              (singFun1 @Product_Sym0 sProduct_)))
        sA_6989586621679128409
instance SFoldable Maybe where
  sFoldMap
    (sA_6989586621679128419 :: Sing a_6989586621679128419_auRu)
    (sA_6989586621679128421 :: Sing a_6989586621679128421_auRv)
    = applySing
        (applySing
            (applySing (singFun3 @Maybe_Sym0 sMaybe_) sMempty)
            sA_6989586621679128419)
        sA_6989586621679128421
  sFoldr _ (sZ :: Sing z_auRI) SNothing = sZ
  sFoldr
    (sF :: Sing f_auRJ)
    (sZ :: Sing z_auRK)
    (SJust (sX :: Sing x_auRL))
    = applySing (applySing sF sX) sZ
  sFoldl _ (sZ :: Sing z_auRY) SNothing = sZ
  sFoldl
    (sF :: Sing f_auRZ)
    (sZ :: Sing z_auS0)
    (SJust (sX :: Sing x_auS1))
    = applySing (applySing sF sZ) sX
instance SFoldable [] where
  sElem
    (sA_6989586621679128466 :: Sing a_6989586621679128466_auSf)
    (sA_6989586621679128468 :: Sing a_6989586621679128468_auSg)
    = applySing
        (applySing
            (singFun2 @ListelemSym0 sListelem) sA_6989586621679128466)
        sA_6989586621679128468
  sFoldl
    (sA_6989586621679128482 :: Sing a_6989586621679128482_auSz)
    (sA_6989586621679128484 :: Sing a_6989586621679128484_auSA)
    (sA_6989586621679128486 :: Sing a_6989586621679128486_auSB)
    = applySing
        (applySing
            (applySing
              (singFun3 @ListfoldlSym0 sListfoldl) sA_6989586621679128482)
            sA_6989586621679128484)
        sA_6989586621679128486
  sFoldl'
    (sA_6989586621679128503 :: Sing a_6989586621679128503_auSU)
    (sA_6989586621679128505 :: Sing a_6989586621679128505_auSV)
    (sA_6989586621679128507 :: Sing a_6989586621679128507_auSW)
    = applySing
        (applySing
            (applySing
              (singFun3 @Listfoldl'Sym0 sListfoldl') sA_6989586621679128503)
            sA_6989586621679128505)
        sA_6989586621679128507
  sFoldl1
    (sA_6989586621679128523 :: Sing a_6989586621679128523_auTa)
    (sA_6989586621679128525 :: Sing a_6989586621679128525_auTb)
    = applySing
        (applySing
            (singFun2 @Listfoldl1Sym0 sListfoldl1) sA_6989586621679128523)
        sA_6989586621679128525
  sFoldr
    (sA_6989586621679128539 :: Sing a_6989586621679128539_auTu)
    (sA_6989586621679128541 :: Sing a_6989586621679128541_auTv)
    (sA_6989586621679128543 :: Sing a_6989586621679128543_auTw)
    = applySing
        (applySing
            (applySing
              (singFun3 @ListfoldrSym0 sListfoldr) sA_6989586621679128539)
            sA_6989586621679128541)
        sA_6989586621679128543
  sFoldr1
    (sA_6989586621679128559 :: Sing a_6989586621679128559_auTK)
    (sA_6989586621679128561 :: Sing a_6989586621679128561_auTL)
    = applySing
        (applySing
            (singFun2 @Listfoldr1Sym0 sListfoldr1) sA_6989586621679128559)
        sA_6989586621679128561
  sLength (sA_6989586621679128573 :: Sing a_6989586621679128573_auTU)
    = applySing
        (singFun1 @ListlengthSym0 sListlength) sA_6989586621679128573
  sMaximum
    (sA_6989586621679128582 :: Sing a_6989586621679128582_auU3)
    = applySing
        (singFun1 @ListmaximumSym0 sListmaximum) sA_6989586621679128582
  sMinimum
    (sA_6989586621679128591 :: Sing a_6989586621679128591_auUc)
    = applySing
        (singFun1 @ListminimumSym0 sListminimum) sA_6989586621679128591
  sNull (sA_6989586621679128600 :: Sing a_6989586621679128600_auUl)
    = applySing
        (singFun1 @ListnullSym0 sListnull) sA_6989586621679128600
  sProduct
    (sA_6989586621679128609 :: Sing a_6989586621679128609_auUu)
    = applySing
        (singFun1 @ListproductSym0 sListproduct) sA_6989586621679128609
  sSum (sA_6989586621679128618 :: Sing a_6989586621679128618_auUD)
    = applySing (singFun1 @ListsumSym0 sListsum) sA_6989586621679128618
  sToList (sA_6989586621679128627 :: Sing a_6989586621679128627_auUM)
    = applySing (singFun1 @IdSym0 sId) sA_6989586621679128627
instance SFoldable NonEmpty where
  sFoldr
    (sF :: Sing f_auUZ)
    (sZ :: Sing z_auV0)
    ((:%|) (sA :: Sing a_auV1) (sAs :: Sing as_auV2))
    = applySing
        (applySing sF sA)
        (applySing
            (applySing (applySing (singFun3 @ListfoldrSym0 sListfoldr) sF) sZ)
            sAs)
  sFoldl
    (sF :: Sing f_auVf)
    (sZ :: Sing z_auVg)
    ((:%|) (sA :: Sing a_auVh) (sAs :: Sing as_auVi))
    = applySing
        (applySing
            (applySing (singFun3 @ListfoldlSym0 sListfoldl) sF)
            (applySing (applySing sF sZ) sA))
        sAs
  sFoldl1
    (sF :: Sing f_auVs)
    ((:%|) (sA :: Sing a_auVt) (sAs :: Sing as_auVu))
    = applySing
        (applySing (applySing (singFun3 @ListfoldlSym0 sListfoldl) sF) sA)
        sAs
  sFoldr1
    (sF :: Sing f_auVE)
    ((:%|) (sP :: Sing p_auVF) (sPs :: Sing ps_auVG))
    = let
        sGo ::
          forall arg_avdi arg_avdj arg_avdk. Sing arg_avdi
                                              -> Sing arg_avdj
                                                -> Sing arg_avdk
                                                    -> Sing (Let6989586621679128689Go f_auVE p_auVF ps_auVG arg_avdi arg_avdj arg_avdk)
        sGo
          (sX :: Sing x_auVM)
          (sR :: Sing r_auVN)
          (sPrev :: Sing prev_auVO)
          = applySing (applySing sF sPrev) (applySing sR sX)
      in
        applySing
          (applySing
              (applySing
                (applySing
                    (singFun3 @FoldrSym0 sFoldr)
                    (singFun3
                      @(Let6989586621679128689GoSym0 f_auVE p_auVF ps_auVG) sGo))
                (singFun1 @IdSym0 sId))
              sPs)
          sP
  sFoldMap
    (sF :: Sing f_auVY)
    ((:%|) (sA :: Sing a_auVZ) (sAs :: Sing as_auW0))
    = applySing
        (applySing (singFun2 @MappendSym0 sMappend) (applySing sF sA))
        (applySing (applySing (singFun2 @FoldMapSym0 sFoldMap) sF) sAs)
  sFold ((:%|) (sM :: Sing m_auW7) (sMs :: Sing ms_auW8))
    = applySing
        (applySing (singFun2 @MappendSym0 sMappend) sM)
        (applySing (singFun1 @FoldSym0 sFold) sMs)
  sToList ((:%|) (sA :: Sing a_auWf) (sAs :: Sing as_auWg))
    = applySing (applySing (singFun2 @(:@#@$) SCons) sA) sAs
instance SFoldable (Either a_aujF) where
  sFoldMap _ (SLeft _) = sMempty
  sFoldMap (sF :: Sing f_auWq) (SRight (sY :: Sing y_auWr))
    = applySing sF sY
  sFoldr _ (sZ :: Sing z_auWE) (SLeft _) = sZ
  sFoldr
    (sF :: Sing f_auWF)
    (sZ :: Sing z_auWG)
    (SRight (sY :: Sing y_auWH))
    = applySing (applySing sF sY) sZ
  sLength (SLeft _) = sFromInteger (sing :: Sing 0)
  sLength (SRight _) = sFromInteger (sing :: Sing 1)
  sNull (sA_6989586621679128761 :: Sing a_6989586621679128761_auWW)
    = applySing (singFun1 @IsLeftSym0 sIsLeft) sA_6989586621679128761
instance SFoldable Proxy where
  sLength ::
    forall (a_aujM :: Type) (t_avdF :: Proxy a_aujM). Sing t_avdF
                                                      -> Sing (Length t_avdF :: Natural)
  sNull ::
    forall (a_aujN :: Type) (t_avdQ :: Proxy a_aujN). Sing t_avdQ
                                                      -> Sing (Null t_avdQ :: Bool)
  sFoldMap _ _ = sMempty
  sFold _ = sMempty
  sFoldr _ (sZ :: Sing z_auXo) _ = sZ
  sFoldl _ (sZ :: Sing z_auXB) _ = sZ
  sFoldl1 _ _
    = applySing
        (singFun1 @ErrorWithoutStackTraceSym0 sErrorWithoutStackTrace)
        (sing :: Sing "foldl1: Proxy")
  sFoldr1 _ _
    = applySing
        (singFun1 @ErrorWithoutStackTraceSym0 sErrorWithoutStackTrace)
        (sing :: Sing "foldr1: Proxy")
  sLength _ = sFromInteger (sing :: Sing 0)
  sNull _ = STrue
  sElem _ _ = SFalse
  sSum _ = sFromInteger (sing :: Sing 0)
  sProduct _ = sFromInteger (sing :: Sing 1)
instance SFoldable Dual where
  sFoldMap (sF :: Sing f_auYA) (SDual (sX :: Sing x_auYB))
    = applySing sF sX
  sElem
    (sA_6989586621679128874 :: Sing a_6989586621679128874_auYP)
    (sA_6989586621679128876 :: Sing a_6989586621679128876_auYQ)
    = applySing
        (applySing
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (singFun1
                    @(LamCases_6989586621679128885Sym0 a_6989586621679128874_auYP a_6989586621679128876_auYQ)
                    (\cases
                        (sLhs_6989586621679126414 :: Sing lhs_6989586621679126414_auYT)
                          -> applySing
                              (applySing (singFun3 @(.@#@$) (%.)) sLhs_6989586621679126414)
                              (singFun1 @GetDualSym0 sGetDual))))
              (singFun2 @(==@#@$) (%==)))
            sA_6989586621679128874)
        sA_6989586621679128876
  sFoldl
    (sF :: Sing f_auZ9)
    (sZ :: Sing z_auZa)
    (SDual (sX :: Sing x_auZb))
    = applySing (applySing sF sZ) sX
  sFoldl'
    (sF :: Sing f_auZo)
    (sZ :: Sing z_auZp)
    (SDual (sX :: Sing x_auZq))
    = applySing (applySing sF sZ) sX
  sFoldl1
    _
    (sA_6989586621679128925 :: Sing a_6989586621679128925_auZC)
    = applySing (singFun1 @GetDualSym0 sGetDual) sA_6989586621679128925
  sFoldr
    (sF :: Sing f_auZP)
    (sZ :: Sing z_auZQ)
    (SDual (sX :: Sing x_auZR))
    = applySing (applySing sF sX) sZ
  sFoldr'
    (sA_6989586621679128953 :: Sing a_6989586621679128953_av0a)
    (sA_6989586621679128955 :: Sing a_6989586621679128955_av0b)
    (sA_6989586621679128957 :: Sing a_6989586621679128957_av0c)
    = applySing
        (applySing
            (applySing (singFun3 @FoldrSym0 sFoldr) sA_6989586621679128953)
            sA_6989586621679128955)
        sA_6989586621679128957
  sFoldr1
    _
    (sA_6989586621679128973 :: Sing a_6989586621679128973_av0o)
    = applySing (singFun1 @GetDualSym0 sGetDual) sA_6989586621679128973
  sLength _ = sFromInteger (sing :: Sing 1)
  sMaximum
    (sA_6989586621679128990 :: Sing a_6989586621679128990_av0D)
    = applySing (singFun1 @GetDualSym0 sGetDual) sA_6989586621679128990
  sMinimum
    (sA_6989586621679128999 :: Sing a_6989586621679128999_av0M)
    = applySing (singFun1 @GetDualSym0 sGetDual) sA_6989586621679128999
  sNull _ = SFalse
  sProduct
    (sA_6989586621679129014 :: Sing a_6989586621679129014_av11)
    = applySing (singFun1 @GetDualSym0 sGetDual) sA_6989586621679129014
  sSum (sA_6989586621679129023 :: Sing a_6989586621679129023_av1a)
    = applySing (singFun1 @GetDualSym0 sGetDual) sA_6989586621679129023
  sToList (SDual (sX :: Sing x_av1h))
    = applySing (applySing (singFun2 @(:@#@$) SCons) sX) SNil
instance SFoldable Monoid.Sum where
  sFoldMap (sF :: Sing f_av1r) (SSum (sX :: Sing x_av1s))
    = applySing sF sX
  sElem
    (sA_6989586621679129051 :: Sing a_6989586621679129051_av1G)
    (sA_6989586621679129053 :: Sing a_6989586621679129053_av1H)
    = applySing
        (applySing
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (singFun1
                    @(LamCases_6989586621679129062Sym0 a_6989586621679129051_av1G a_6989586621679129053_av1H)
                    (\cases
                        (sLhs_6989586621679126416 :: Sing lhs_6989586621679126416_av1K)
                          -> applySing
                              (applySing (singFun3 @(.@#@$) (%.)) sLhs_6989586621679126416)
                              (singFun1 @GetSumSym0 sGetSum))))
              (singFun2 @(==@#@$) (%==)))
            sA_6989586621679129051)
        sA_6989586621679129053
  sFoldl
    (sF :: Sing f_av20)
    (sZ :: Sing z_av21)
    (SSum (sX :: Sing x_av22))
    = applySing (applySing sF sZ) sX
  sFoldl'
    (sF :: Sing f_av2f)
    (sZ :: Sing z_av2g)
    (SSum (sX :: Sing x_av2h))
    = applySing (applySing sF sZ) sX
  sFoldl1
    _
    (sA_6989586621679129102 :: Sing a_6989586621679129102_av2t)
    = applySing (singFun1 @GetSumSym0 sGetSum) sA_6989586621679129102
  sFoldr
    (sF :: Sing f_av2G)
    (sZ :: Sing z_av2H)
    (SSum (sX :: Sing x_av2I))
    = applySing (applySing sF sX) sZ
  sFoldr'
    (sA_6989586621679129130 :: Sing a_6989586621679129130_av31)
    (sA_6989586621679129132 :: Sing a_6989586621679129132_av32)
    (sA_6989586621679129134 :: Sing a_6989586621679129134_av33)
    = applySing
        (applySing
            (applySing (singFun3 @FoldrSym0 sFoldr) sA_6989586621679129130)
            sA_6989586621679129132)
        sA_6989586621679129134
  sFoldr1
    _
    (sA_6989586621679129150 :: Sing a_6989586621679129150_av3f)
    = applySing (singFun1 @GetSumSym0 sGetSum) sA_6989586621679129150
  sLength _ = sFromInteger (sing :: Sing 1)
  sMaximum
    (sA_6989586621679129167 :: Sing a_6989586621679129167_av3u)
    = applySing (singFun1 @GetSumSym0 sGetSum) sA_6989586621679129167
  sMinimum
    (sA_6989586621679129176 :: Sing a_6989586621679129176_av3D)
    = applySing (singFun1 @GetSumSym0 sGetSum) sA_6989586621679129176
  sNull _ = SFalse
  sProduct
    (sA_6989586621679129191 :: Sing a_6989586621679129191_av3S)
    = applySing (singFun1 @GetSumSym0 sGetSum) sA_6989586621679129191
  sSum (sA_6989586621679129200 :: Sing a_6989586621679129200_av41)
    = applySing (singFun1 @GetSumSym0 sGetSum) sA_6989586621679129200
  sToList (SSum (sX :: Sing x_av48))
    = applySing (applySing (singFun2 @(:@#@$) SCons) sX) SNil
instance SFoldable Monoid.Product where
  sFoldMap (sF :: Sing f_av4i) (SProduct (sX :: Sing x_av4j))
    = applySing sF sX
  sElem
    (sA_6989586621679129228 :: Sing a_6989586621679129228_av4x)
    (sA_6989586621679129230 :: Sing a_6989586621679129230_av4y)
    = applySing
        (applySing
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (singFun1
                    @(LamCases_6989586621679129239Sym0 a_6989586621679129228_av4x a_6989586621679129230_av4y)
                    (\cases
                        (sLhs_6989586621679126418 :: Sing lhs_6989586621679126418_av4B)
                          -> applySing
                              (applySing (singFun3 @(.@#@$) (%.)) sLhs_6989586621679126418)
                              (singFun1 @GetProductSym0 sGetProduct))))
              (singFun2 @(==@#@$) (%==)))
            sA_6989586621679129228)
        sA_6989586621679129230
  sFoldl
    (sF :: Sing f_av4R)
    (sZ :: Sing z_av4S)
    (SProduct (sX :: Sing x_av4T))
    = applySing (applySing sF sZ) sX
  sFoldl'
    (sF :: Sing f_av56)
    (sZ :: Sing z_av57)
    (SProduct (sX :: Sing x_av58))
    = applySing (applySing sF sZ) sX
  sFoldl1
    _
    (sA_6989586621679129279 :: Sing a_6989586621679129279_av5k)
    = applySing
        (singFun1 @GetProductSym0 sGetProduct) sA_6989586621679129279
  sFoldr
    (sF :: Sing f_av5x)
    (sZ :: Sing z_av5y)
    (SProduct (sX :: Sing x_av5z))
    = applySing (applySing sF sX) sZ
  sFoldr'
    (sA_6989586621679129307 :: Sing a_6989586621679129307_av5S)
    (sA_6989586621679129309 :: Sing a_6989586621679129309_av5T)
    (sA_6989586621679129311 :: Sing a_6989586621679129311_av5U)
    = applySing
        (applySing
            (applySing (singFun3 @FoldrSym0 sFoldr) sA_6989586621679129307)
            sA_6989586621679129309)
        sA_6989586621679129311
  sFoldr1
    _
    (sA_6989586621679129327 :: Sing a_6989586621679129327_av66)
    = applySing
        (singFun1 @GetProductSym0 sGetProduct) sA_6989586621679129327
  sLength _ = sFromInteger (sing :: Sing 1)
  sMaximum
    (sA_6989586621679129344 :: Sing a_6989586621679129344_av6l)
    = applySing
        (singFun1 @GetProductSym0 sGetProduct) sA_6989586621679129344
  sMinimum
    (sA_6989586621679129353 :: Sing a_6989586621679129353_av6u)
    = applySing
        (singFun1 @GetProductSym0 sGetProduct) sA_6989586621679129353
  sNull _ = SFalse
  sProduct
    (sA_6989586621679129368 :: Sing a_6989586621679129368_av6J)
    = applySing
        (singFun1 @GetProductSym0 sGetProduct) sA_6989586621679129368
  sSum (sA_6989586621679129377 :: Sing a_6989586621679129377_av6S)
    = applySing
        (singFun1 @GetProductSym0 sGetProduct) sA_6989586621679129377
  sToList (SProduct (sX :: Sing x_av6Z))
    = applySing (applySing (singFun2 @(:@#@$) SCons) sX) SNil
type SFoldable :: (Type -> Type) -> Constraint
instance (SFoldable t_auic, SMonoid m_auid) =>
          SingI (FoldSym0 :: (~>) (t_auic m_auid) m_auid) where
  sing = singFun1 @FoldSym0 sFold
instance (SFoldable t_auic, SMonoid m_auie) =>
          SingI (FoldMapSym0 :: (~>) ((~>) a_auif m_auie) ((~>) (t_auic a_auif) m_auie)) where
  sing = singFun2 @FoldMapSym0 sFoldMap
instance (SFoldable t_auic, SMonoid m_auie, SingI d_avah) =>
          SingI (FoldMapSym1 (d_avah :: (~>) a_auif m_auie) :: (~>) (t_auic a_auif) m_auie) where
  sing
    = singFun1
        @(FoldMapSym1 (d_avah :: (~>) a_auif m_auie))
        (sFoldMap (sing @d_avah))
instance (SFoldable t_auic, SMonoid m_auie) =>
          SingI1 (FoldMapSym1 :: (~>) a_auif m_auie
                                -> (~>) (t_auic a_auif) m_auie) where
  liftSing (s_avaj :: Sing (d_avah :: (~>) a_auif m_auie))
    = singFun1
        @(FoldMapSym1 (d_avah :: (~>) a_auif m_auie)) (sFoldMap s_avaj)
instance SFoldable t_auic =>
          SingI (FoldrSym0 :: (~>) ((~>) a_auig ((~>) b_auih b_auih)) ((~>) b_auih ((~>) (t_auic a_auig) b_auih))) where
  sing = singFun3 @FoldrSym0 sFoldr
instance (SFoldable t_auic, SingI d_avan) =>
          SingI (FoldrSym1 (d_avan :: (~>) a_auig ((~>) b_auih b_auih)) :: (~>) b_auih ((~>) (t_auic a_auig) b_auih)) where
  sing
    = singFun2
        @(FoldrSym1 (d_avan :: (~>) a_auig ((~>) b_auih b_auih)))
        (sFoldr (sing @d_avan))
instance SFoldable t_auic =>
          SingI1 (FoldrSym1 :: (~>) a_auig ((~>) b_auih b_auih)
                              -> (~>) b_auih ((~>) (t_auic a_auig) b_auih)) where
  liftSing
    (s_avat :: Sing (d_avan :: (~>) a_auig ((~>) b_auih b_auih)))
    = singFun2
        @(FoldrSym1 (d_avan :: (~>) a_auig ((~>) b_auih b_auih)))
        (sFoldr s_avat)
instance (SFoldable t_auic, SingI d_avan, SingI d_avao) =>
          SingI (FoldrSym2 (d_avan :: (~>) a_auig ((~>) b_auih b_auih)) (d_avao :: b_auih) :: (~>) (t_auic a_auig) b_auih) where
  sing
    = singFun1
        @(FoldrSym2 (d_avan :: (~>) a_auig ((~>) b_auih b_auih)) (d_avao :: b_auih))
        (sFoldr (sing @d_avan) (sing @d_avao))
instance (SFoldable t_auic, SingI d_avan) =>
          SingI1 (FoldrSym2 (d_avan :: (~>) a_auig ((~>) b_auih b_auih)) :: b_auih
                                                                            -> (~>) (t_auic a_auig) b_auih) where
  liftSing (s_avaq :: Sing (d_avao :: b_auih))
    = singFun1
        @(FoldrSym2 (d_avan :: (~>) a_auig ((~>) b_auih b_auih)) (d_avao :: b_auih))
        (sFoldr (sing @d_avan) s_avaq)
instance SFoldable t_auic =>
          SingI2 (FoldrSym2 :: (~>) a_auig ((~>) b_auih b_auih)
                              -> b_auih -> (~>) (t_auic a_auig) b_auih) where
  liftSing2
    (s_avar :: Sing (d_avan :: (~>) a_auig ((~>) b_auih b_auih)))
    (s_avas :: Sing (d_avao :: b_auih))
    = singFun1
        @(FoldrSym2 (d_avan :: (~>) a_auig ((~>) b_auih b_auih)) (d_avao :: b_auih))
        (sFoldr s_avar s_avas)
instance SFoldable t_auic =>
          SingI (Foldr'Sym0 :: (~>) ((~>) a_auii ((~>) b_auij b_auij)) ((~>) b_auij ((~>) (t_auic a_auii) b_auij))) where
  sing = singFun3 @Foldr'Sym0 sFoldr'
instance (SFoldable t_auic, SingI d_avax) =>
          SingI (Foldr'Sym1 (d_avax :: (~>) a_auii ((~>) b_auij b_auij)) :: (~>) b_auij ((~>) (t_auic a_auii) b_auij)) where
  sing
    = singFun2
        @(Foldr'Sym1 (d_avax :: (~>) a_auii ((~>) b_auij b_auij)))
        (sFoldr' (sing @d_avax))
instance SFoldable t_auic =>
          SingI1 (Foldr'Sym1 :: (~>) a_auii ((~>) b_auij b_auij)
                                -> (~>) b_auij ((~>) (t_auic a_auii) b_auij)) where
  liftSing
    (s_avaD :: Sing (d_avax :: (~>) a_auii ((~>) b_auij b_auij)))
    = singFun2
        @(Foldr'Sym1 (d_avax :: (~>) a_auii ((~>) b_auij b_auij)))
        (sFoldr' s_avaD)
instance (SFoldable t_auic, SingI d_avax, SingI d_avay) =>
          SingI (Foldr'Sym2 (d_avax :: (~>) a_auii ((~>) b_auij b_auij)) (d_avay :: b_auij) :: (~>) (t_auic a_auii) b_auij) where
  sing
    = singFun1
        @(Foldr'Sym2 (d_avax :: (~>) a_auii ((~>) b_auij b_auij)) (d_avay :: b_auij))
        (sFoldr' (sing @d_avax) (sing @d_avay))
instance (SFoldable t_auic, SingI d_avax) =>
          SingI1 (Foldr'Sym2 (d_avax :: (~>) a_auii ((~>) b_auij b_auij)) :: b_auij
                                                                            -> (~>) (t_auic a_auii) b_auij) where
  liftSing (s_avaA :: Sing (d_avay :: b_auij))
    = singFun1
        @(Foldr'Sym2 (d_avax :: (~>) a_auii ((~>) b_auij b_auij)) (d_avay :: b_auij))
        (sFoldr' (sing @d_avax) s_avaA)
instance SFoldable t_auic =>
          SingI2 (Foldr'Sym2 :: (~>) a_auii ((~>) b_auij b_auij)
                                -> b_auij -> (~>) (t_auic a_auii) b_auij) where
  liftSing2
    (s_avaB :: Sing (d_avax :: (~>) a_auii ((~>) b_auij b_auij)))
    (s_avaC :: Sing (d_avay :: b_auij))
    = singFun1
        @(Foldr'Sym2 (d_avax :: (~>) a_auii ((~>) b_auij b_auij)) (d_avay :: b_auij))
        (sFoldr' s_avaB s_avaC)
instance SFoldable t_auic =>
          SingI (FoldlSym0 :: (~>) ((~>) b_auik ((~>) a_auil b_auik)) ((~>) b_auik ((~>) (t_auic a_auil) b_auik))) where
  sing = singFun3 @FoldlSym0 sFoldl
instance (SFoldable t_auic, SingI d_avaH) =>
          SingI (FoldlSym1 (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)) :: (~>) b_auik ((~>) (t_auic a_auil) b_auik)) where
  sing
    = singFun2
        @(FoldlSym1 (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)))
        (sFoldl (sing @d_avaH))
instance SFoldable t_auic =>
          SingI1 (FoldlSym1 :: (~>) b_auik ((~>) a_auil b_auik)
                              -> (~>) b_auik ((~>) (t_auic a_auil) b_auik)) where
  liftSing
    (s_avaN :: Sing (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)))
    = singFun2
        @(FoldlSym1 (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)))
        (sFoldl s_avaN)
instance (SFoldable t_auic, SingI d_avaH, SingI d_avaI) =>
          SingI (FoldlSym2 (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)) (d_avaI :: b_auik) :: (~>) (t_auic a_auil) b_auik) where
  sing
    = singFun1
        @(FoldlSym2 (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)) (d_avaI :: b_auik))
        (sFoldl (sing @d_avaH) (sing @d_avaI))
instance (SFoldable t_auic, SingI d_avaH) =>
          SingI1 (FoldlSym2 (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)) :: b_auik
                                                                            -> (~>) (t_auic a_auil) b_auik) where
  liftSing (s_avaK :: Sing (d_avaI :: b_auik))
    = singFun1
        @(FoldlSym2 (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)) (d_avaI :: b_auik))
        (sFoldl (sing @d_avaH) s_avaK)
instance SFoldable t_auic =>
          SingI2 (FoldlSym2 :: (~>) b_auik ((~>) a_auil b_auik)
                              -> b_auik -> (~>) (t_auic a_auil) b_auik) where
  liftSing2
    (s_avaL :: Sing (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)))
    (s_avaM :: Sing (d_avaI :: b_auik))
    = singFun1
        @(FoldlSym2 (d_avaH :: (~>) b_auik ((~>) a_auil b_auik)) (d_avaI :: b_auik))
        (sFoldl s_avaL s_avaM)
instance SFoldable t_auic =>
          SingI (Foldl'Sym0 :: (~>) ((~>) b_auim ((~>) a_auin b_auim)) ((~>) b_auim ((~>) (t_auic a_auin) b_auim))) where
  sing = singFun3 @Foldl'Sym0 sFoldl'
instance (SFoldable t_auic, SingI d_avaR) =>
          SingI (Foldl'Sym1 (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)) :: (~>) b_auim ((~>) (t_auic a_auin) b_auim)) where
  sing
    = singFun2
        @(Foldl'Sym1 (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)))
        (sFoldl' (sing @d_avaR))
instance SFoldable t_auic =>
          SingI1 (Foldl'Sym1 :: (~>) b_auim ((~>) a_auin b_auim)
                                -> (~>) b_auim ((~>) (t_auic a_auin) b_auim)) where
  liftSing
    (s_avaX :: Sing (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)))
    = singFun2
        @(Foldl'Sym1 (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)))
        (sFoldl' s_avaX)
instance (SFoldable t_auic, SingI d_avaR, SingI d_avaS) =>
          SingI (Foldl'Sym2 (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)) (d_avaS :: b_auim) :: (~>) (t_auic a_auin) b_auim) where
  sing
    = singFun1
        @(Foldl'Sym2 (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)) (d_avaS :: b_auim))
        (sFoldl' (sing @d_avaR) (sing @d_avaS))
instance (SFoldable t_auic, SingI d_avaR) =>
          SingI1 (Foldl'Sym2 (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)) :: b_auim
                                                                            -> (~>) (t_auic a_auin) b_auim) where
  liftSing (s_avaU :: Sing (d_avaS :: b_auim))
    = singFun1
        @(Foldl'Sym2 (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)) (d_avaS :: b_auim))
        (sFoldl' (sing @d_avaR) s_avaU)
instance SFoldable t_auic =>
          SingI2 (Foldl'Sym2 :: (~>) b_auim ((~>) a_auin b_auim)
                                -> b_auim -> (~>) (t_auic a_auin) b_auim) where
  liftSing2
    (s_avaV :: Sing (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)))
    (s_avaW :: Sing (d_avaS :: b_auim))
    = singFun1
        @(Foldl'Sym2 (d_avaR :: (~>) b_auim ((~>) a_auin b_auim)) (d_avaS :: b_auim))
        (sFoldl' s_avaV s_avaW)
instance SFoldable t_auic =>
          SingI (Foldr1Sym0 :: (~>) ((~>) a_auio ((~>) a_auio a_auio)) ((~>) (t_auic a_auio) a_auio)) where
  sing = singFun2 @Foldr1Sym0 sFoldr1
instance (SFoldable t_auic, SingI d_avb0) =>
          SingI (Foldr1Sym1 (d_avb0 :: (~>) a_auio ((~>) a_auio a_auio)) :: (~>) (t_auic a_auio) a_auio) where
  sing
    = singFun1
        @(Foldr1Sym1 (d_avb0 :: (~>) a_auio ((~>) a_auio a_auio)))
        (sFoldr1 (sing @d_avb0))
instance SFoldable t_auic =>
          SingI1 (Foldr1Sym1 :: (~>) a_auio ((~>) a_auio a_auio)
                                -> (~>) (t_auic a_auio) a_auio) where
  liftSing
    (s_avb2 :: Sing (d_avb0 :: (~>) a_auio ((~>) a_auio a_auio)))
    = singFun1
        @(Foldr1Sym1 (d_avb0 :: (~>) a_auio ((~>) a_auio a_auio)))
        (sFoldr1 s_avb2)
instance SFoldable t_auic =>
          SingI (Foldl1Sym0 :: (~>) ((~>) a_auip ((~>) a_auip a_auip)) ((~>) (t_auic a_auip) a_auip)) where
  sing = singFun2 @Foldl1Sym0 sFoldl1
instance (SFoldable t_auic, SingI d_avb5) =>
          SingI (Foldl1Sym1 (d_avb5 :: (~>) a_auip ((~>) a_auip a_auip)) :: (~>) (t_auic a_auip) a_auip) where
  sing
    = singFun1
        @(Foldl1Sym1 (d_avb5 :: (~>) a_auip ((~>) a_auip a_auip)))
        (sFoldl1 (sing @d_avb5))
instance SFoldable t_auic =>
          SingI1 (Foldl1Sym1 :: (~>) a_auip ((~>) a_auip a_auip)
                                -> (~>) (t_auic a_auip) a_auip) where
  liftSing
    (s_avb7 :: Sing (d_avb5 :: (~>) a_auip ((~>) a_auip a_auip)))
    = singFun1
        @(Foldl1Sym1 (d_avb5 :: (~>) a_auip ((~>) a_auip a_auip)))
        (sFoldl1 s_avb7)
instance SFoldable t_auic =>
          SingI (ToListSym0 :: (~>) (t_auic a_auiq) [a_auiq]) where
  sing = singFun1 @ToListSym0 sToList
instance SFoldable t_auic =>
          SingI (NullSym0 :: (~>) (t_auic a_auir) Bool) where
  sing = singFun1 @NullSym0 sNull
instance SFoldable t_auic =>
          SingI (LengthSym0 :: (~>) (t_auic a_auis) Natural) where
  sing = singFun1 @LengthSym0 sLength
instance (SFoldable t_auic, SEq a_auit) =>
          SingI (ElemSym0 :: (~>) a_auit ((~>) (t_auic a_auit) Bool)) where
  sing = singFun2 @ElemSym0 sElem
instance (SFoldable t_auic, SEq a_auit, SingI d_avbg) =>
          SingI (ElemSym1 (d_avbg :: a_auit) :: (~>) (t_auic a_auit) Bool) where
  sing
    = singFun1 @(ElemSym1 (d_avbg :: a_auit)) (sElem (sing @d_avbg))
instance (SFoldable t_auic, SEq a_auit) =>
          SingI1 (ElemSym1 :: a_auit -> (~>) (t_auic a_auit) Bool) where
  liftSing (s_avbi :: Sing (d_avbg :: a_auit))
    = singFun1 @(ElemSym1 (d_avbg :: a_auit)) (sElem s_avbi)
instance (SFoldable t_auic, SOrd a_auiu) =>
          SingI (MaximumSym0 :: (~>) (t_auic a_auiu) a_auiu) where
  sing = singFun1 @MaximumSym0 sMaximum
instance (SFoldable t_auic, SOrd a_auiv) =>
          SingI (MinimumSym0 :: (~>) (t_auic a_auiv) a_auiv) where
  sing = singFun1 @MinimumSym0 sMinimum
instance (SFoldable t_auic, SNum a_auiw) =>
          SingI (SumSym0 :: (~>) (t_auic a_auiw) a_auiw) where
  sing = singFun1 @SumSym0 sSum
instance (SFoldable t_auic, SNum a_auix) =>
          SingI (ProductSym0 :: (~>) (t_auic a_auix) a_auix) where
  sing = singFun1 @ProductSym0 sProduct

type family LamCases_6989586621679185468_aJHv a6989586621679185135 (_f_69895866216791853806989586621679185465 :: (~>) a6989586621679126243 m6989586621679126242) a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467 a_6989586621679185470_aJHx where
      LamCases_6989586621679185468_aJHv a_aJC7 _f_6989586621679185380_aJHr a_6989586621679185384_aJHs a_6989586621679185386_aJHt _ = MemptySym0
data LamCases_6989586621679185468Sym0 a6989586621679185135 (_f_69895866216791853806989586621679185465 :: (~>) a6989586621679126243 m6989586621679126242) a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467 a_69895866216791854706989586621679185471
  where
    LamCases_6989586621679185468Sym0KindInference :: SameKind (Apply (LamCases_6989586621679185468Sym0 a6989586621679185135 _f_69895866216791853806989586621679185465 a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467) arg_aJHy) (LamCases_6989586621679185468Sym1 a6989586621679185135 _f_69895866216791853806989586621679185465 a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467 arg_aJHy) =>
                                                      LamCases_6989586621679185468Sym0 a6989586621679185135 _f_69895866216791853806989586621679185465 a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467 a_69895866216791854706989586621679185471
type instance Apply @_ @_ (LamCases_6989586621679185468Sym0 a6989586621679185135 _f_69895866216791853806989586621679185465 a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467) a_69895866216791854706989586621679185471 = LamCases_6989586621679185468_aJHv a6989586621679185135 _f_69895866216791853806989586621679185465 a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467 a_69895866216791854706989586621679185471
instance SuppressUnusedWarnings (LamCases_6989586621679185468Sym0 a6989586621679185135 _f_69895866216791853806989586621679185465 a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679185468Sym0KindInference ())
type family LamCases_6989586621679185468Sym1 a6989586621679185135 (_f_69895866216791853806989586621679185465 :: (~>) a6989586621679126243 m6989586621679126242) a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467 a_69895866216791854706989586621679185471 where
  LamCases_6989586621679185468Sym1 a6989586621679185135 _f_69895866216791853806989586621679185465 a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467 a_69895866216791854706989586621679185471 = LamCases_6989586621679185468_aJHv a6989586621679185135 _f_69895866216791853806989586621679185465 a_69895866216791853846989586621679185466 a_69895866216791853866989586621679185467 a_69895866216791854706989586621679185471
type FoldMap_6989586621679185458 :: forall a_aJC7
                                            a_auif
                                            m_auie. (~>) a_auif m_auie
                                                    -> (a_aJC7, a_auif) -> m_auie
type family FoldMap_6989586621679185458 @a_aJC7 @a_auif @m_auie (a_aJHm :: (~>) a_auif m_auie) (a_aJHn :: (a_aJC7,
                                                                                                            a_auif)) :: m_auie where
  FoldMap_6989586621679185458 @a_aJC7 @a_auif @m_auie (_f_6989586621679185380_aJHr :: (~>) a_auif m_auie) ('(a_6989586621679185384_aJHs,
                                                                                                              a_6989586621679185386_aJHt) :: (a_aJC7,
                                                                                                                                              a_auif)) = Apply (Apply MappendSym0 (Apply (LamCases_6989586621679185468Sym0 a_aJC7 _f_6989586621679185380_aJHr a_6989586621679185384_aJHs a_6989586621679185386_aJHt) a_6989586621679185384_aJHs)) (Apply _f_6989586621679185380_aJHr a_6989586621679185386_aJHt)
type family LamCases_6989586621679185489_aJHQ a6989586621679185135 (_f_69895866216791853806989586621679185485 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791853826989586621679185486 :: b6989586621679126245) a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_6989586621679185492_aJHT a_6989586621679185494_aJHV where
  LamCases_6989586621679185489_aJHQ a_aJC7 _f_6989586621679185380_aJHL _z_6989586621679185382_aJHM a_6989586621679185390_aJHN a_6989586621679185392_aJHO _ n_6989586621679185388_aJHR = n_6989586621679185388_aJHR
data LamCases_6989586621679185489Sym0 a6989586621679185135 (_f_69895866216791853806989586621679185485 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791853826989586621679185486 :: b6989586621679126245) a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493
  where
    LamCases_6989586621679185489Sym0KindInference :: SameKind (Apply (LamCases_6989586621679185489Sym0 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488) arg_aJHW) (LamCases_6989586621679185489Sym1 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 arg_aJHW) =>
                                                      LamCases_6989586621679185489Sym0 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493
type instance Apply @_ @_ (LamCases_6989586621679185489Sym0 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488) a_69895866216791854926989586621679185493 = LamCases_6989586621679185489Sym1 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493
instance SuppressUnusedWarnings (LamCases_6989586621679185489Sym0 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679185489Sym0KindInference ())
data LamCases_6989586621679185489Sym1 a6989586621679185135 (_f_69895866216791853806989586621679185485 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791853826989586621679185486 :: b6989586621679126245) a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493 a_69895866216791854946989586621679185495
  where
    LamCases_6989586621679185489Sym1KindInference :: SameKind (Apply (LamCases_6989586621679185489Sym1 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493) arg_aJHW) (LamCases_6989586621679185489Sym2 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493 arg_aJHW) =>
                                                      LamCases_6989586621679185489Sym1 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493 a_69895866216791854946989586621679185495
type instance Apply @_ @_ (LamCases_6989586621679185489Sym1 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493) a_69895866216791854946989586621679185495 = LamCases_6989586621679185489_aJHQ a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493 a_69895866216791854946989586621679185495
instance SuppressUnusedWarnings (LamCases_6989586621679185489Sym1 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679185489Sym1KindInference ())
type family LamCases_6989586621679185489Sym2 a6989586621679185135 (_f_69895866216791853806989586621679185485 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791853826989586621679185486 :: b6989586621679126245) a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493 a_69895866216791854946989586621679185495 where
  LamCases_6989586621679185489Sym2 a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493 a_69895866216791854946989586621679185495 = LamCases_6989586621679185489_aJHQ a6989586621679185135 _f_69895866216791853806989586621679185485 _z_69895866216791853826989586621679185486 a_69895866216791853906989586621679185487 a_69895866216791853926989586621679185488 a_69895866216791854926989586621679185493 a_69895866216791854946989586621679185495
type Foldr_6989586621679185476 :: forall a_aJC7
                                          a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> (a_aJC7, a_auig) -> b_auih
type family Foldr_6989586621679185476 @a_aJC7 @a_auig @b_auih (a_aJHE :: (~>) a_auig ((~>) b_auih b_auih)) (a_aJHF :: b_auih) (a_aJHG :: (a_aJC7,
                                                                                                                                          a_auig)) :: b_auih where
  Foldr_6989586621679185476 @a_aJC7 @a_auig @b_auih (_f_6989586621679185380_aJHL :: (~>) a_auig ((~>) b_auih b_auih)) (_z_6989586621679185382_aJHM :: b_auih) ('(a_6989586621679185390_aJHN,
                                                                                                                                                                  a_6989586621679185392_aJHO) :: (a_aJC7,
                                                                                                                                                                                                  a_auig)) = Apply (Apply (LamCases_6989586621679185489Sym0 a_aJC7 _f_6989586621679185380_aJHL _z_6989586621679185382_aJHM a_6989586621679185390_aJHN a_6989586621679185392_aJHO) a_6989586621679185390_aJHN) (Apply (Apply _f_6989586621679185380_aJHL a_6989586621679185392_aJHO) _z_6989586621679185382_aJHM)
instance PFoldable ((,) a_aJC7) where
  type FoldMap a_aJHi a_aJHj = FoldMap_6989586621679185458 a_aJHi a_aJHj
  type Foldr a_aJHz a_aJHA a_aJHB = Foldr_6989586621679185476 a_aJHz a_aJHA a_aJHB
type FoldMap_6989586621679185499 :: forall a_auif
                                            m_auie. (~>) a_auif m_auie -> First a_auif -> m_auie
type family FoldMap_6989586621679185499 @a_auif @m_auie (a_aJI1 :: (~>) a_auif m_auie) (a_aJI2 :: First a_auif) :: m_auie where
  FoldMap_6989586621679185499 @a_auif @m_auie _f_6989586621679185401_aJI6 ('First a_6989586621679185411_aJI7) = Apply (Apply FoldMapSym0 _f_6989586621679185401_aJI6) a_6989586621679185411_aJI7
type family LamCases_6989586621679185523_aJIo (_f_69895866216791854016989586621679185520 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791854036989586621679185521 :: b6989586621679126245) a_69895866216791854236989586621679185522 a_6989586621679185527_aJIs a_6989586621679185529_aJIu where
  LamCases_6989586621679185523_aJIo _f_6989586621679185401_aJIk _z_6989586621679185403_aJIl a_6989586621679185423_aJIm n1_6989586621679185419_aJIp n2_6989586621679185421_aJIq = Apply (Apply (Apply FoldrSym0 _f_6989586621679185401_aJIk) n2_6989586621679185421_aJIq) n1_6989586621679185419_aJIp
data LamCases_6989586621679185523Sym0 (_f_69895866216791854016989586621679185520 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791854036989586621679185521 :: b6989586621679126245) a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528
  where
    LamCases_6989586621679185523Sym0KindInference :: SameKind (Apply (LamCases_6989586621679185523Sym0 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522) arg_aJIv) (LamCases_6989586621679185523Sym1 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 arg_aJIv) =>
                                                      LamCases_6989586621679185523Sym0 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528
type instance Apply @_ @_ (LamCases_6989586621679185523Sym0 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522) a_69895866216791855276989586621679185528 = LamCases_6989586621679185523Sym1 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528
instance SuppressUnusedWarnings (LamCases_6989586621679185523Sym0 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679185523Sym0KindInference ())
data LamCases_6989586621679185523Sym1 (_f_69895866216791854016989586621679185520 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791854036989586621679185521 :: b6989586621679126245) a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528 a_69895866216791855296989586621679185530
  where
    LamCases_6989586621679185523Sym1KindInference :: SameKind (Apply (LamCases_6989586621679185523Sym1 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528) arg_aJIv) (LamCases_6989586621679185523Sym2 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528 arg_aJIv) =>
                                                      LamCases_6989586621679185523Sym1 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528 a_69895866216791855296989586621679185530
type instance Apply @_ @_ (LamCases_6989586621679185523Sym1 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528) a_69895866216791855296989586621679185530 = LamCases_6989586621679185523_aJIo _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528 a_69895866216791855296989586621679185530
instance SuppressUnusedWarnings (LamCases_6989586621679185523Sym1 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679185523Sym1KindInference ())
type family LamCases_6989586621679185523Sym2 (_f_69895866216791854016989586621679185520 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791854036989586621679185521 :: b6989586621679126245) a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528 a_69895866216791855296989586621679185530 where
  LamCases_6989586621679185523Sym2 _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528 a_69895866216791855296989586621679185530 = LamCases_6989586621679185523_aJIo _f_69895866216791854016989586621679185520 _z_69895866216791854036989586621679185521 a_69895866216791854236989586621679185522 a_69895866216791855276989586621679185528 a_69895866216791855296989586621679185530
type Foldr_6989586621679185511 :: forall a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> First a_auig -> b_auih
type family Foldr_6989586621679185511 @a_auig @b_auih (a_aJId :: (~>) a_auig ((~>) b_auih b_auih)) (a_aJIe :: b_auih) (a_aJIf :: First a_auig) :: b_auih where
  Foldr_6989586621679185511 @a_auig @b_auih _f_6989586621679185401_aJIk _z_6989586621679185403_aJIl ('First a_6989586621679185423_aJIm) = Apply (Apply (LamCases_6989586621679185523Sym0 _f_6989586621679185401_aJIk _z_6989586621679185403_aJIl a_6989586621679185423_aJIm) a_6989586621679185423_aJIm) _z_6989586621679185403_aJIl
instance PFoldable First where
  type FoldMap a_aJHX a_aJHY = FoldMap_6989586621679185499 a_aJHX a_aJHY
  type Foldr a_aJI8 a_aJI9 a_aJIa = Foldr_6989586621679185511 a_aJI8 a_aJI9 a_aJIa
type FoldMap_6989586621679185534 :: forall a_auif
                                            m_auie. (~>) a_auif m_auie -> Last a_auif -> m_auie
type family FoldMap_6989586621679185534 @a_auif @m_auie (a_aJIA :: (~>) a_auif m_auie) (a_aJIB :: Last a_auif) :: m_auie where
  FoldMap_6989586621679185534 @a_auif @m_auie _f_6989586621679185432_aJIF ('Last a_6989586621679185442_aJIG) = Apply (Apply FoldMapSym0 _f_6989586621679185432_aJIF) a_6989586621679185442_aJIG
type family LamCases_6989586621679185558_aJIX (_f_69895866216791854326989586621679185555 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791854346989586621679185556 :: b6989586621679126245) a_69895866216791854546989586621679185557 a_6989586621679185562_aJJ1 a_6989586621679185564_aJJ3 where
  LamCases_6989586621679185558_aJIX _f_6989586621679185432_aJIT _z_6989586621679185434_aJIU a_6989586621679185454_aJIV n1_6989586621679185450_aJIY n2_6989586621679185452_aJIZ = Apply (Apply (Apply FoldrSym0 _f_6989586621679185432_aJIT) n2_6989586621679185452_aJIZ) n1_6989586621679185450_aJIY
data LamCases_6989586621679185558Sym0 (_f_69895866216791854326989586621679185555 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791854346989586621679185556 :: b6989586621679126245) a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563
  where
    LamCases_6989586621679185558Sym0KindInference :: SameKind (Apply (LamCases_6989586621679185558Sym0 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557) arg_aJJ4) (LamCases_6989586621679185558Sym1 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 arg_aJJ4) =>
                                                      LamCases_6989586621679185558Sym0 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563
type instance Apply @_ @_ (LamCases_6989586621679185558Sym0 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557) a_69895866216791855626989586621679185563 = LamCases_6989586621679185558Sym1 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563
instance SuppressUnusedWarnings (LamCases_6989586621679185558Sym0 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679185558Sym0KindInference ())
data LamCases_6989586621679185558Sym1 (_f_69895866216791854326989586621679185555 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791854346989586621679185556 :: b6989586621679126245) a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563 a_69895866216791855646989586621679185565
  where
    LamCases_6989586621679185558Sym1KindInference :: SameKind (Apply (LamCases_6989586621679185558Sym1 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563) arg_aJJ4) (LamCases_6989586621679185558Sym2 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563 arg_aJJ4) =>
                                                      LamCases_6989586621679185558Sym1 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563 a_69895866216791855646989586621679185565
type instance Apply @_ @_ (LamCases_6989586621679185558Sym1 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563) a_69895866216791855646989586621679185565 = LamCases_6989586621679185558_aJIX _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563 a_69895866216791855646989586621679185565
instance SuppressUnusedWarnings (LamCases_6989586621679185558Sym1 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679185558Sym1KindInference ())
type family LamCases_6989586621679185558Sym2 (_f_69895866216791854326989586621679185555 :: (~>) a6989586621679126244 ((~>) b6989586621679126245 b6989586621679126245)) (_z_69895866216791854346989586621679185556 :: b6989586621679126245) a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563 a_69895866216791855646989586621679185565 where
  LamCases_6989586621679185558Sym2 _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563 a_69895866216791855646989586621679185565 = LamCases_6989586621679185558_aJIX _f_69895866216791854326989586621679185555 _z_69895866216791854346989586621679185556 a_69895866216791854546989586621679185557 a_69895866216791855626989586621679185563 a_69895866216791855646989586621679185565
type Foldr_6989586621679185546 :: forall a_auig
                                          b_auih. (~>) a_auig ((~>) b_auih b_auih)
                                                  -> b_auih -> Last a_auig -> b_auih
type family Foldr_6989586621679185546 @a_auig @b_auih (a_aJIM :: (~>) a_auig ((~>) b_auih b_auih)) (a_aJIN :: b_auih) (a_aJIO :: Last a_auig) :: b_auih where
  Foldr_6989586621679185546 @a_auig @b_auih _f_6989586621679185432_aJIT _z_6989586621679185434_aJIU ('Last a_6989586621679185454_aJIV) = Apply (Apply (LamCases_6989586621679185558Sym0 _f_6989586621679185432_aJIT _z_6989586621679185434_aJIU a_6989586621679185454_aJIV) a_6989586621679185454_aJIV) _z_6989586621679185434_aJIU
instance PFoldable Last where
  type FoldMap a_aJIw a_aJIx = FoldMap_6989586621679185534 a_aJIw a_aJIx
  type Foldr a_aJIH a_aJII a_aJIJ = Foldr_6989586621679185546 a_aJIH a_aJII a_aJIJ
instance SFoldable ((,) a_aJC7) where
  sFoldMap
    (_sf_6989586621679185380 :: Sing _f_6989586621679185380_aJHr)
    (STuple2 (sA_6989586621679185384 :: Sing a_6989586621679185384_aJHs)
              (sA_6989586621679185386 :: Sing a_6989586621679185386_aJHt))
    = applySing
        (applySing
            (singFun2 @MappendSym0 sMappend)
            (applySing
              (singFun1
                  @(LamCases_6989586621679185468Sym0 a_aJC7 _f_6989586621679185380_aJHr a_6989586621679185384_aJHs a_6989586621679185386_aJHt)
                  (\cases _ -> sMempty))
              sA_6989586621679185384))
        (applySing _sf_6989586621679185380 sA_6989586621679185386)
  sFoldr
    (_sf_6989586621679185380 :: Sing _f_6989586621679185380_aJHL)
    (_sz_6989586621679185382 :: Sing _z_6989586621679185382_aJHM)
    (STuple2 (sA_6989586621679185390 :: Sing a_6989586621679185390_aJHN)
              (sA_6989586621679185392 :: Sing a_6989586621679185392_aJHO))
    = applySing
        (applySing
            (singFun2
              @(LamCases_6989586621679185489Sym0 a_aJC7 _f_6989586621679185380_aJHL _z_6989586621679185382_aJHM a_6989586621679185390_aJHN a_6989586621679185392_aJHO)
              (\cases
                  _ (sN_6989586621679185388 :: Sing n_6989586621679185388_aJHR)
                    -> sN_6989586621679185388))
            sA_6989586621679185390)
        (applySing
            (applySing _sf_6989586621679185380 sA_6989586621679185392)
            _sz_6989586621679185382)
instance SFoldable First where
  sFoldMap
    (_sf_6989586621679185401 :: Sing _f_6989586621679185401_aJI6)
    (SFirst (sA_6989586621679185411 :: Sing a_6989586621679185411_aJI7))
    = applySing
        (applySing
            (singFun2 @FoldMapSym0 sFoldMap) _sf_6989586621679185401)
        sA_6989586621679185411
  sFoldr
    (_sf_6989586621679185401 :: Sing _f_6989586621679185401_aJIk)
    (_sz_6989586621679185403 :: Sing _z_6989586621679185403_aJIl)
    (SFirst (sA_6989586621679185423 :: Sing a_6989586621679185423_aJIm))
    = applySing
        (applySing
            (singFun2
              @(LamCases_6989586621679185523Sym0 _f_6989586621679185401_aJIk _z_6989586621679185403_aJIl a_6989586621679185423_aJIm)
              (\cases
                  (sN1_6989586621679185419 :: Sing n1_6989586621679185419_aJIp)
                    (sN2_6989586621679185421 :: Sing n2_6989586621679185421_aJIq)
                    -> applySing
                        (applySing
                            (applySing (singFun3 @FoldrSym0 sFoldr) _sf_6989586621679185401)
                            sN2_6989586621679185421)
                        sN1_6989586621679185419))
            sA_6989586621679185423)
        _sz_6989586621679185403
instance SFoldable Last where
  sFoldMap
    (_sf_6989586621679185432 :: Sing _f_6989586621679185432_aJIF)
    (SLast (sA_6989586621679185442 :: Sing a_6989586621679185442_aJIG))
    = applySing
        (applySing
            (singFun2 @FoldMapSym0 sFoldMap) _sf_6989586621679185432)
        sA_6989586621679185442
  sFoldr
    (_sf_6989586621679185432 :: Sing _f_6989586621679185432_aJIT)
    (_sz_6989586621679185434 :: Sing _z_6989586621679185434_aJIU)
    (SLast (sA_6989586621679185454 :: Sing a_6989586621679185454_aJIV))
    = applySing
        (applySing
            (singFun2
              @(LamCases_6989586621679185558Sym0 _f_6989586621679185432_aJIT _z_6989586621679185434_aJIU a_6989586621679185454_aJIV)
              (\cases
                  (sN1_6989586621679185450 :: Sing n1_6989586621679185450_aJIY)
                    (sN2_6989586621679185452 :: Sing n2_6989586621679185452_aJIZ)
                    -> applySing
                        (applySing
                            (applySing (singFun3 @FoldrSym0 sFoldr) _sf_6989586621679185432)
                            sN2_6989586621679185452)
                        sN1_6989586621679185450))
            sA_6989586621679185454)
        _sz_6989586621679185434

