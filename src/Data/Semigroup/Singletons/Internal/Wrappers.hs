{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoNamedWildCards #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStarIsType #-}
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
-- Module      :  Data.Semigroup.Singletons.Internal.Wrappers
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted and singled versions of the @newtype@ wrappers from
-- "Data.Semigroup", all of which are reexported from the "Data.Semigroup"
-- module or imported directly by some other modules.
--
-- This module exists to avoid import cycles with
-- "Data.Monoid.Singletons".
--
----------------------------------------------------------------------------

module Data.Semigroup.Singletons.Internal.Wrappers where

import Control.Monad.Singletons.Internal
import Data.Bool.Singletons
import Data.Eq.Singletons
import Data.Ord.Singletons hiding (MinSym0, MinSym1, MaxSym0, MaxSym1)
import Data.Semigroup (Dual(..), All(..), Any(..), Sum(..), Product(..))
import Data.Semigroup.Singletons.Internal.Classes
import Data.Singletons.Base.Enum
import Data.Singletons.Base.Instances

import Data.Singletons.TH
import GHC.Num.Singletons
import Data.Kind (Type)
import qualified Data.Semigroup
import qualified Data.Singletons.ShowSing
import qualified Data.Type.Equality
import qualified Data.Singletons.Decide
import qualified Data.Type.Coercion
import qualified GHC.Num.Natural

type DualSym0 :: forall (a_aO0t :: Type). (~>) a_aO0t (Dual a_aO0t)
data DualSym0 :: (~>) a_aO0t (Dual a_aO0t)
  where
    DualSym0KindInference :: SameKind (Apply DualSym0 arg_a1WRB) (DualSym1 arg_a1WRB) =>
                              DualSym0 a6989586621679474396
type instance Apply @a_aO0t @(Dual a_aO0t) DualSym0 a6989586621679474396 = 'Dual a6989586621679474396
instance SuppressUnusedWarnings DualSym0 where
  suppressUnusedWarnings = snd ((,) DualSym0KindInference ())
type DualSym1 :: forall (a_aO0t :: Type). a_aO0t -> Dual a_aO0t
type family DualSym1 @(a_aO0t :: Type) (a6989586621679474396 :: a_aO0t) :: Dual a_aO0t where
  DualSym1 a6989586621679474396 = 'Dual a6989586621679474396
type GetDualSym0 :: forall (a_aO0t :: Type). (~>) (Dual a_aO0t) a_aO0t
data GetDualSym0 :: (~>) (Dual a_aO0t) a_aO0t
  where
    GetDualSym0KindInference :: SameKind (Apply GetDualSym0 arg_a1WRE) (GetDualSym1 arg_a1WRE) =>
                                GetDualSym0 a6989586621679474399
type instance Apply @(Dual a_aO0t) @a_aO0t GetDualSym0 a6989586621679474399 = GetDual a6989586621679474399
instance SuppressUnusedWarnings GetDualSym0 where
  suppressUnusedWarnings = snd ((,) GetDualSym0KindInference ())
type GetDualSym1 :: forall (a_aO0t :: Type). Dual a_aO0t -> a_aO0t
type family GetDualSym1 @(a_aO0t :: Type) (a6989586621679474399 :: Dual a_aO0t) :: a_aO0t where
  GetDualSym1 a6989586621679474399 = GetDual a6989586621679474399
type GetDual :: forall (a_aO0t :: Type). Dual a_aO0t -> a_aO0t
type family GetDual @(a_aO0t :: Type) (a_a1WRD :: Dual a_aO0t) :: a_aO0t where
  GetDual @a_aO0t ('Dual field_a1WRG :: Dual a_aO0t) = field_a1WRG
sGetDual ::
  forall (a_aO0t :: Type) (t_a1WRH :: Dual a_aO0t). Sing t_a1WRH
                                                    -> Sing (GetDual t_a1WRH :: a_aO0t)
sGetDual (SDual (sField :: Sing field_a1WRG)) = sField
instance SingI (GetDualSym0 :: (~>) (Dual a_aO0t) a_aO0t) where
  sing = singFun1 @GetDualSym0 sGetDual
type SDual :: forall (a_aO0t :: Type). Dual a_aO0t -> Type
data SDual :: forall (a_aO0t :: Type). Dual a_aO0t -> Type
  where
    SDual :: forall (a_aO0t :: Type) (n_a1WRJ :: a_aO0t).
              (Sing n_a1WRJ) -> SDual ('Dual n_a1WRJ :: Dual a_aO0t)
type instance Sing @(Dual a_aO0t) = SDual
instance SingKind a_aO0t => SingKind (Dual a_aO0t) where
  type Demote (Dual a_aO0t) = Dual (Demote a_aO0t)
  fromSing (SDual b_a1WRL) = Dual (fromSing b_a1WRL)
  toSing (Dual (b_a1WRN :: Demote a_aO0t))
    = (\cases (SomeSing c_a1WRO) -> SomeSing (SDual c_a1WRO))
        (toSing b_a1WRN :: SomeSing a_aO0t)
instance SingI n_a1WRJ => SingI ('Dual (n_a1WRJ :: a_aO0t)) where
  sing = SDual sing
instance SingI1 'Dual where
  liftSing = SDual
instance SingI (DualSym0 :: (~>) a_aO0t (Dual a_aO0t)) where
  sing = singFun1 @DualSym0 SDual
type AllSym0 :: (~>) Bool All
data AllSym0 :: (~>) Bool All
  where
    AllSym0KindInference :: SameKind (Apply AllSym0 arg_a1WRR) (AllSym1 arg_a1WRR) =>
                            AllSym0 a6989586621679474412
type instance Apply @Bool @All AllSym0 a6989586621679474412 = 'All a6989586621679474412
instance SuppressUnusedWarnings AllSym0 where
  suppressUnusedWarnings = snd ((,) AllSym0KindInference ())
type AllSym1 :: Bool -> All
type family AllSym1 (a6989586621679474412 :: Bool) :: All where
  AllSym1 a6989586621679474412 = 'All a6989586621679474412
type GetAllSym0 :: (~>) All Bool
data GetAllSym0 :: (~>) All Bool
  where
    GetAllSym0KindInference :: SameKind (Apply GetAllSym0 arg_a1WRU) (GetAllSym1 arg_a1WRU) =>
                                GetAllSym0 a6989586621679474415
type instance Apply @All @Bool GetAllSym0 a6989586621679474415 = GetAll a6989586621679474415
instance SuppressUnusedWarnings GetAllSym0 where
  suppressUnusedWarnings = snd ((,) GetAllSym0KindInference ())
type GetAllSym1 :: All -> Bool
type family GetAllSym1 (a6989586621679474415 :: All) :: Bool where
  GetAllSym1 a6989586621679474415 = GetAll a6989586621679474415
type GetAll :: All -> Bool
type family GetAll (a_a1WRT :: All) :: Bool where
  GetAll ('All field_a1WRW) = field_a1WRW
sGetAll ::
  (forall (t_a1WRX :: All).
    Sing t_a1WRX -> Sing (GetAll t_a1WRX :: Bool) :: Type)
sGetAll (SAll (sField :: Sing field_a1WRW)) = sField
instance SingI (GetAllSym0 :: (~>) All Bool) where
  sing = singFun1 @GetAllSym0 sGetAll
type SAll :: All -> Type
data SAll :: All -> Type
  where
    SAll :: forall (n_a1WRZ :: Bool).
            (Sing n_a1WRZ) -> SAll ('All n_a1WRZ :: All)
type instance Sing @All = SAll
instance SingKind All where
  type Demote All = All
  fromSing (SAll b_a1WS1) = All (fromSing b_a1WS1)
  toSing (All (b_a1WS3 :: Demote Bool))
    = (\cases (SomeSing c_a1WS4) -> SomeSing (SAll c_a1WS4))
        (toSing b_a1WS3 :: SomeSing Bool)
instance SingI n_a1WRZ => SingI ('All (n_a1WRZ :: Bool)) where
  sing = SAll sing
instance SingI1 'All where
  liftSing = SAll
instance SingI (AllSym0 :: (~>) Bool All) where
  sing = singFun1 @AllSym0 SAll
type AnySym0 :: (~>) Bool Any
data AnySym0 :: (~>) Bool Any
  where
    AnySym0KindInference :: SameKind (Apply AnySym0 arg_a1WS7) (AnySym1 arg_a1WS7) =>
                            AnySym0 a6989586621679474428
type instance Apply @Bool @Any AnySym0 a6989586621679474428 = 'Any a6989586621679474428
instance SuppressUnusedWarnings AnySym0 where
  suppressUnusedWarnings = snd ((,) AnySym0KindInference ())
type AnySym1 :: Bool -> Any
type family AnySym1 (a6989586621679474428 :: Bool) :: Any where
  AnySym1 a6989586621679474428 = 'Any a6989586621679474428
type GetAnySym0 :: (~>) Any Bool
data GetAnySym0 :: (~>) Any Bool
  where
    GetAnySym0KindInference :: SameKind (Apply GetAnySym0 arg_a1WSa) (GetAnySym1 arg_a1WSa) =>
                                GetAnySym0 a6989586621679474431
type instance Apply @Any @Bool GetAnySym0 a6989586621679474431 = GetAny a6989586621679474431
instance SuppressUnusedWarnings GetAnySym0 where
  suppressUnusedWarnings = snd ((,) GetAnySym0KindInference ())
type GetAnySym1 :: Any -> Bool
type family GetAnySym1 (a6989586621679474431 :: Any) :: Bool where
  GetAnySym1 a6989586621679474431 = GetAny a6989586621679474431
type GetAny :: Any -> Bool
type family GetAny (a_a1WS9 :: Any) :: Bool where
  GetAny ('Any field_a1WSc) = field_a1WSc
sGetAny ::
  (forall (t_a1WSd :: Any).
    Sing t_a1WSd -> Sing (GetAny t_a1WSd :: Bool) :: Type)
sGetAny (SAny (sField :: Sing field_a1WSc)) = sField
instance SingI (GetAnySym0 :: (~>) Any Bool) where
  sing = singFun1 @GetAnySym0 sGetAny
type SAny :: Any -> Type
data SAny :: Any -> Type
  where
    SAny :: forall (n_a1WSf :: Bool).
            (Sing n_a1WSf) -> SAny ('Any n_a1WSf :: Any)
type instance Sing @Any = SAny
instance SingKind Any where
  type Demote Any = Any
  fromSing (SAny b_a1WSh) = Any (fromSing b_a1WSh)
  toSing (Any (b_a1WSj :: Demote Bool))
    = (\cases (SomeSing c_a1WSk) -> SomeSing (SAny c_a1WSk))
        (toSing b_a1WSj :: SomeSing Bool)
instance SingI n_a1WSf => SingI ('Any (n_a1WSf :: Bool)) where
  sing = SAny sing
instance SingI1 'Any where
  liftSing = SAny
instance SingI (AnySym0 :: (~>) Bool Any) where
  sing = singFun1 @AnySym0 SAny
type SumSym0 :: forall (a_aO0D :: Type). (~>) a_aO0D (Sum a_aO0D)
data SumSym0 :: (~>) a_aO0D (Sum a_aO0D)
  where
    SumSym0KindInference :: SameKind (Apply SumSym0 arg_a1WSq) (SumSym1 arg_a1WSq) =>
                            SumSym0 a6989586621679474447
type instance Apply @a_aO0D @(Sum a_aO0D) SumSym0 a6989586621679474447 = 'Sum a6989586621679474447
instance SuppressUnusedWarnings SumSym0 where
  suppressUnusedWarnings = snd ((,) SumSym0KindInference ())
type SumSym1 :: forall (a_aO0D :: Type). a_aO0D -> Sum a_aO0D
type family SumSym1 @(a_aO0D :: Type) (a6989586621679474447 :: a_aO0D) :: Sum a_aO0D where
  SumSym1 a6989586621679474447 = 'Sum a6989586621679474447
type GetSumSym0 :: forall (a_aO0D :: Type). (~>) (Sum a_aO0D) a_aO0D
data GetSumSym0 :: (~>) (Sum a_aO0D) a_aO0D
  where
    GetSumSym0KindInference :: SameKind (Apply GetSumSym0 arg_a1WSt) (GetSumSym1 arg_a1WSt) =>
                                GetSumSym0 a6989586621679474450
type instance Apply @(Sum a_aO0D) @a_aO0D GetSumSym0 a6989586621679474450 = GetSum a6989586621679474450
instance SuppressUnusedWarnings GetSumSym0 where
  suppressUnusedWarnings = snd ((,) GetSumSym0KindInference ())
type GetSumSym1 :: forall (a_aO0D :: Type). Sum a_aO0D -> a_aO0D
type family GetSumSym1 @(a_aO0D :: Type) (a6989586621679474450 :: Sum a_aO0D) :: a_aO0D where
  GetSumSym1 a6989586621679474450 = GetSum a6989586621679474450
type GetSum :: forall (a_aO0D :: Type). Sum a_aO0D -> a_aO0D
type family GetSum @(a_aO0D :: Type) (a_a1WSs :: Sum a_aO0D) :: a_aO0D where
  GetSum @a_aO0D ('Sum field_a1WSv :: Sum a_aO0D) = field_a1WSv
sGetSum ::
  forall (a_aO0D :: Type) (t_a1WSw :: Sum a_aO0D). Sing t_a1WSw
                                                    -> Sing (GetSum t_a1WSw :: a_aO0D)
sGetSum (SSum (sField :: Sing field_a1WSv)) = sField
instance SingI (GetSumSym0 :: (~>) (Sum a_aO0D) a_aO0D) where
  sing = singFun1 @GetSumSym0 sGetSum
type SSum :: forall (a_aO0D :: Type). Sum a_aO0D -> Type
data SSum :: forall (a_aO0D :: Type). Sum a_aO0D -> Type
  where
    SSum :: forall (a_aO0D :: Type) (n_a1WSy :: a_aO0D).
            (Sing n_a1WSy) -> SSum ('Sum n_a1WSy :: Sum a_aO0D)
type instance Sing @(Sum a_aO0D) = SSum
instance SingKind a_aO0D => SingKind (Sum a_aO0D) where
  type Demote (Sum a_aO0D) = Sum (Demote a_aO0D)
  fromSing (SSum b_a1WSA) = Sum (fromSing b_a1WSA)
  toSing (Sum (b_a1WSC :: Demote a_aO0D))
    = (\cases (SomeSing c_a1WSD) -> SomeSing (SSum c_a1WSD))
        (toSing b_a1WSC :: SomeSing a_aO0D)
instance SingI n_a1WSy => SingI ('Sum (n_a1WSy :: a_aO0D)) where
  sing = SSum sing
instance SingI1 'Sum where
  liftSing = SSum
instance SingI (SumSym0 :: (~>) a_aO0D (Sum a_aO0D)) where
  sing = singFun1 @SumSym0 SSum
type ProductSym0 :: forall (a_aO0y :: Type). (~>) a_aO0y (Product a_aO0y)
data ProductSym0 :: (~>) a_aO0y (Product a_aO0y)
  where
    ProductSym0KindInference :: SameKind (Apply ProductSym0 arg_a1WSJ) (ProductSym1 arg_a1WSJ) =>
                                ProductSym0 a6989586621679474466
type instance Apply @a_aO0y @(Product a_aO0y) ProductSym0 a6989586621679474466 = 'Product a6989586621679474466
instance SuppressUnusedWarnings ProductSym0 where
  suppressUnusedWarnings = snd ((,) ProductSym0KindInference ())
type ProductSym1 :: forall (a_aO0y :: Type). a_aO0y
                                              -> Product a_aO0y
type family ProductSym1 @(a_aO0y :: Type) (a6989586621679474466 :: a_aO0y) :: Product a_aO0y where
  ProductSym1 a6989586621679474466 = 'Product a6989586621679474466
type GetProductSym0 :: forall (a_aO0y :: Type). (~>) (Product a_aO0y) a_aO0y
data GetProductSym0 :: (~>) (Product a_aO0y) a_aO0y
  where
    GetProductSym0KindInference :: SameKind (Apply GetProductSym0 arg_a1WSM) (GetProductSym1 arg_a1WSM) =>
                                    GetProductSym0 a6989586621679474469
type instance Apply @(Product a_aO0y) @a_aO0y GetProductSym0 a6989586621679474469 = GetProduct a6989586621679474469
instance SuppressUnusedWarnings GetProductSym0 where
  suppressUnusedWarnings = snd ((,) GetProductSym0KindInference ())
type GetProductSym1 :: forall (a_aO0y :: Type). Product a_aO0y
                                                -> a_aO0y
type family GetProductSym1 @(a_aO0y :: Type) (a6989586621679474469 :: Product a_aO0y) :: a_aO0y where
  GetProductSym1 a6989586621679474469 = GetProduct a6989586621679474469
type GetProduct :: forall (a_aO0y :: Type). Product a_aO0y
                                            -> a_aO0y
type family GetProduct @(a_aO0y :: Type) (a_a1WSL :: Product a_aO0y) :: a_aO0y where
  GetProduct @a_aO0y ('Product field_a1WSO :: Product a_aO0y) = field_a1WSO
sGetProduct ::
  forall (a_aO0y :: Type) (t_a1WSP :: Product a_aO0y). Sing t_a1WSP
                                                        -> Sing (GetProduct t_a1WSP :: a_aO0y)
sGetProduct (SProduct (sField :: Sing field_a1WSO)) = sField
instance SingI (GetProductSym0 :: (~>) (Product a_aO0y) a_aO0y) where
  sing = singFun1 @GetProductSym0 sGetProduct
type SProduct :: forall (a_aO0y :: Type). Product a_aO0y -> Type
data SProduct :: forall (a_aO0y :: Type). Product a_aO0y -> Type
  where
    SProduct :: forall (a_aO0y :: Type) (n_a1WSR :: a_aO0y).
                (Sing n_a1WSR) -> SProduct ('Product n_a1WSR :: Product a_aO0y)
type instance Sing @(Product a_aO0y) = SProduct
instance SingKind a_aO0y => SingKind (Product a_aO0y) where
  type Demote (Product a_aO0y) = Product (Demote a_aO0y)
  fromSing (SProduct b_a1WST) = Product (fromSing b_a1WST)
  toSing (Product (b_a1WSV :: Demote a_aO0y))
    = (\cases (SomeSing c_a1WSW) -> SomeSing (SProduct c_a1WSW))
        (toSing b_a1WSV :: SomeSing a_aO0y)
instance SingI n_a1WSR =>
          SingI ('Product (n_a1WSR :: a_aO0y)) where
  sing = SProduct sing
instance SingI1 'Product where
  liftSing = SProduct
instance SingI (ProductSym0 :: (~>) a_aO0y (Product a_aO0y)) where
  sing = singFun1 @ProductSym0 SProduct
type MinSym0 :: forall (a_aO06 :: Type). (~>) a_aO06 (Data.Semigroup.Min a_aO06)
data MinSym0 :: (~>) a_aO06 (Data.Semigroup.Min a_aO06)
  where
    MinSym0KindInference :: SameKind (Apply MinSym0 arg_a1WT2) (MinSym1 arg_a1WT2) =>
                            MinSym0 a6989586621679474485
type instance Apply @a_aO06 @(Data.Semigroup.Min a_aO06) MinSym0 a6989586621679474485 = 'Data.Semigroup.Min a6989586621679474485
instance SuppressUnusedWarnings MinSym0 where
  suppressUnusedWarnings = snd ((,) MinSym0KindInference ())
type MinSym1 :: forall (a_aO06 :: Type). a_aO06
                                          -> Data.Semigroup.Min a_aO06
type family MinSym1 @(a_aO06 :: Type) (a6989586621679474485 :: a_aO06) :: Data.Semigroup.Min a_aO06 where
  MinSym1 a6989586621679474485 = 'Data.Semigroup.Min a6989586621679474485
type GetMinSym0 :: forall (a_aO06 :: Type). (~>) (Data.Semigroup.Min a_aO06) a_aO06
data GetMinSym0 :: (~>) (Data.Semigroup.Min a_aO06) a_aO06
  where
    GetMinSym0KindInference :: SameKind (Apply GetMinSym0 arg_a1WT5) (GetMinSym1 arg_a1WT5) =>
                                GetMinSym0 a6989586621679474488
type instance Apply @(Data.Semigroup.Min a_aO06) @a_aO06 GetMinSym0 a6989586621679474488 = GetMin a6989586621679474488
instance SuppressUnusedWarnings GetMinSym0 where
  suppressUnusedWarnings = snd ((,) GetMinSym0KindInference ())
type GetMinSym1 :: forall (a_aO06 :: Type). Data.Semigroup.Min a_aO06
                                            -> a_aO06
type family GetMinSym1 @(a_aO06 :: Type) (a6989586621679474488 :: Data.Semigroup.Min a_aO06) :: a_aO06 where
  GetMinSym1 a6989586621679474488 = GetMin a6989586621679474488
type GetMin :: forall (a_aO06 :: Type). Data.Semigroup.Min a_aO06
                                        -> a_aO06
type family GetMin @(a_aO06 :: Type) (a_a1WT4 :: Data.Semigroup.Min a_aO06) :: a_aO06 where
  GetMin @a_aO06 ('Data.Semigroup.Min field_a1WT7 :: Data.Semigroup.Min a_aO06) = field_a1WT7
sGetMin ::
  forall (a_aO06 :: Type)
          (t_a1WT8 :: Data.Semigroup.Min a_aO06). Sing t_a1WT8
                                                  -> Sing (GetMin t_a1WT8 :: a_aO06)
sGetMin (SMin (sField :: Sing field_a1WT7)) = sField
instance SingI (GetMinSym0 :: (~>) (Data.Semigroup.Min a_aO06) a_aO06) where
  sing = singFun1 @GetMinSym0 sGetMin
type SMin :: forall (a_aO06 :: Type). Data.Semigroup.Min a_aO06
                                      -> Type
data SMin :: forall (a_aO06 :: Type).
              Data.Semigroup.Min a_aO06 -> Type
  where
    SMin :: forall (a_aO06 :: Type) (n_a1WTa :: a_aO06).
            (Sing n_a1WTa) ->
            SMin ('Data.Semigroup.Min n_a1WTa :: Data.Semigroup.Min a_aO06)
type instance Sing @(Data.Semigroup.Min a_aO06) = SMin
instance SingKind a_aO06 =>
          SingKind (Data.Semigroup.Min a_aO06) where
  type Demote (Data.Semigroup.Min a_aO06) = Data.Semigroup.Min (Demote a_aO06)
  fromSing (SMin b_a1WTc) = Data.Semigroup.Min (fromSing b_a1WTc)
  toSing (Data.Semigroup.Min (b_a1WTe :: Demote a_aO06))
    = (\cases (SomeSing c_a1WTf) -> SomeSing (SMin c_a1WTf))
        (toSing b_a1WTe :: SomeSing a_aO06)
instance SingI n_a1WTa =>
          SingI ('Data.Semigroup.Min (n_a1WTa :: a_aO06)) where
  sing = SMin sing
instance SingI1 'Data.Semigroup.Min where
  liftSing = SMin
instance SingI (MinSym0 :: (~>) a_aO06 (Data.Semigroup.Min a_aO06)) where
  sing = singFun1 @MinSym0 SMin
type MaxSym0 :: forall (a_aO01 :: Type). (~>) a_aO01 (Data.Semigroup.Max a_aO01)
data MaxSym0 :: (~>) a_aO01 (Data.Semigroup.Max a_aO01)
  where
    MaxSym0KindInference :: SameKind (Apply MaxSym0 arg_a1WTl) (MaxSym1 arg_a1WTl) =>
                            MaxSym0 a6989586621679474504
type instance Apply @a_aO01 @(Data.Semigroup.Max a_aO01) MaxSym0 a6989586621679474504 = 'Data.Semigroup.Max a6989586621679474504
instance SuppressUnusedWarnings MaxSym0 where
  suppressUnusedWarnings = snd ((,) MaxSym0KindInference ())
type MaxSym1 :: forall (a_aO01 :: Type). a_aO01
                                          -> Data.Semigroup.Max a_aO01
type family MaxSym1 @(a_aO01 :: Type) (a6989586621679474504 :: a_aO01) :: Data.Semigroup.Max a_aO01 where
  MaxSym1 a6989586621679474504 = 'Data.Semigroup.Max a6989586621679474504
type GetMaxSym0 :: forall (a_aO01 :: Type). (~>) (Data.Semigroup.Max a_aO01) a_aO01
data GetMaxSym0 :: (~>) (Data.Semigroup.Max a_aO01) a_aO01
  where
    GetMaxSym0KindInference :: SameKind (Apply GetMaxSym0 arg_a1WTo) (GetMaxSym1 arg_a1WTo) =>
                                GetMaxSym0 a6989586621679474507
type instance Apply @(Data.Semigroup.Max a_aO01) @a_aO01 GetMaxSym0 a6989586621679474507 = GetMax a6989586621679474507
instance SuppressUnusedWarnings GetMaxSym0 where
  suppressUnusedWarnings = snd ((,) GetMaxSym0KindInference ())
type GetMaxSym1 :: forall (a_aO01 :: Type). Data.Semigroup.Max a_aO01
                                            -> a_aO01
type family GetMaxSym1 @(a_aO01 :: Type) (a6989586621679474507 :: Data.Semigroup.Max a_aO01) :: a_aO01 where
  GetMaxSym1 a6989586621679474507 = GetMax a6989586621679474507
type GetMax :: forall (a_aO01 :: Type). Data.Semigroup.Max a_aO01
                                        -> a_aO01
type family GetMax @(a_aO01 :: Type) (a_a1WTn :: Data.Semigroup.Max a_aO01) :: a_aO01 where
  GetMax @a_aO01 ('Data.Semigroup.Max field_a1WTq :: Data.Semigroup.Max a_aO01) = field_a1WTq
sGetMax ::
  forall (a_aO01 :: Type)
          (t_a1WTr :: Data.Semigroup.Max a_aO01). Sing t_a1WTr
                                                  -> Sing (GetMax t_a1WTr :: a_aO01)
sGetMax (SMax (sField :: Sing field_a1WTq)) = sField
instance SingI (GetMaxSym0 :: (~>) (Data.Semigroup.Max a_aO01) a_aO01) where
  sing = singFun1 @GetMaxSym0 sGetMax
type SMax :: forall (a_aO01 :: Type). Data.Semigroup.Max a_aO01
                                      -> Type
data SMax :: forall (a_aO01 :: Type).
              Data.Semigroup.Max a_aO01 -> Type
  where
    SMax :: forall (a_aO01 :: Type) (n_a1WTt :: a_aO01).
            (Sing n_a1WTt) ->
            SMax ('Data.Semigroup.Max n_a1WTt :: Data.Semigroup.Max a_aO01)
type instance Sing @(Data.Semigroup.Max a_aO01) = SMax
instance SingKind a_aO01 =>
          SingKind (Data.Semigroup.Max a_aO01) where
  type Demote (Data.Semigroup.Max a_aO01) = Data.Semigroup.Max (Demote a_aO01)
  fromSing (SMax b_a1WTv) = Data.Semigroup.Max (fromSing b_a1WTv)
  toSing (Data.Semigroup.Max (b_a1WTx :: Demote a_aO01))
    = (\cases (SomeSing c_a1WTy) -> SomeSing (SMax c_a1WTy))
        (toSing b_a1WTx :: SomeSing a_aO01)
instance SingI n_a1WTt =>
          SingI ('Data.Semigroup.Max (n_a1WTt :: a_aO01)) where
  sing = SMax sing
instance SingI1 'Data.Semigroup.Max where
  liftSing = SMax
instance SingI (MaxSym0 :: (~>) a_aO01 (Data.Semigroup.Max a_aO01)) where
  sing = singFun1 @MaxSym0 SMax
type FirstSym0 :: forall (a_aNZR :: Type). (~>) a_aNZR (Data.Semigroup.First a_aNZR)
data FirstSym0 :: (~>) a_aNZR (Data.Semigroup.First a_aNZR)
  where
    FirstSym0KindInference :: SameKind (Apply FirstSym0 arg_a1WTE) (FirstSym1 arg_a1WTE) =>
                              FirstSym0 a6989586621679474523
type instance Apply @a_aNZR @(Data.Semigroup.First a_aNZR) FirstSym0 a6989586621679474523 = 'Data.Semigroup.First a6989586621679474523
instance SuppressUnusedWarnings FirstSym0 where
  suppressUnusedWarnings = snd ((,) FirstSym0KindInference ())
type FirstSym1 :: forall (a_aNZR :: Type). a_aNZR
                                            -> Data.Semigroup.First a_aNZR
type family FirstSym1 @(a_aNZR :: Type) (a6989586621679474523 :: a_aNZR) :: Data.Semigroup.First a_aNZR where
  FirstSym1 a6989586621679474523 = 'Data.Semigroup.First a6989586621679474523
type GetFirstSym0 :: forall (a_aNZR :: Type). (~>) (Data.Semigroup.First a_aNZR) a_aNZR
data GetFirstSym0 :: (~>) (Data.Semigroup.First a_aNZR) a_aNZR
  where
    GetFirstSym0KindInference :: SameKind (Apply GetFirstSym0 arg_a1WTH) (GetFirstSym1 arg_a1WTH) =>
                                  GetFirstSym0 a6989586621679474526
type instance Apply @(Data.Semigroup.First a_aNZR) @a_aNZR GetFirstSym0 a6989586621679474526 = GetFirst a6989586621679474526
instance SuppressUnusedWarnings GetFirstSym0 where
  suppressUnusedWarnings = snd ((,) GetFirstSym0KindInference ())
type GetFirstSym1 :: forall (a_aNZR :: Type). Data.Semigroup.First a_aNZR
                                              -> a_aNZR
type family GetFirstSym1 @(a_aNZR :: Type) (a6989586621679474526 :: Data.Semigroup.First a_aNZR) :: a_aNZR where
  GetFirstSym1 a6989586621679474526 = GetFirst a6989586621679474526
type GetFirst :: forall (a_aNZR :: Type). Data.Semigroup.First a_aNZR
                                          -> a_aNZR
type family GetFirst @(a_aNZR :: Type) (a_a1WTG :: Data.Semigroup.First a_aNZR) :: a_aNZR where
  GetFirst @a_aNZR ('Data.Semigroup.First field_a1WTJ :: Data.Semigroup.First a_aNZR) = field_a1WTJ
sGetFirst ::
  forall (a_aNZR :: Type)
          (t_a1WTK :: Data.Semigroup.First a_aNZR). Sing t_a1WTK
                                                    -> Sing (GetFirst t_a1WTK :: a_aNZR)
sGetFirst (SFirst (sField :: Sing field_a1WTJ)) = sField
instance SingI (GetFirstSym0 :: (~>) (Data.Semigroup.First a_aNZR) a_aNZR) where
  sing = singFun1 @GetFirstSym0 sGetFirst
type SFirst :: forall (a_aNZR :: Type). Data.Semigroup.First a_aNZR
                                        -> Type
data SFirst :: forall (a_aNZR :: Type).
                Data.Semigroup.First a_aNZR -> Type
  where
    SFirst :: forall (a_aNZR :: Type) (n_a1WTM :: a_aNZR).
              (Sing n_a1WTM) ->
              SFirst ('Data.Semigroup.First n_a1WTM :: Data.Semigroup.First a_aNZR)
type instance Sing @(Data.Semigroup.First a_aNZR) = SFirst
instance SingKind a_aNZR =>
          SingKind (Data.Semigroup.First a_aNZR) where
  type Demote (Data.Semigroup.First a_aNZR) = Data.Semigroup.First (Demote a_aNZR)
  fromSing (SFirst b_a1WTO) = Data.Semigroup.First (fromSing b_a1WTO)
  toSing (Data.Semigroup.First (b_a1WTQ :: Demote a_aNZR))
    = (\cases (SomeSing c_a1WTR) -> SomeSing (SFirst c_a1WTR))
        (toSing b_a1WTQ :: SomeSing a_aNZR)
instance SingI n_a1WTM =>
          SingI ('Data.Semigroup.First (n_a1WTM :: a_aNZR)) where
  sing = SFirst sing
instance SingI1 'Data.Semigroup.First where
  liftSing = SFirst
instance SingI (FirstSym0 :: (~>) a_aNZR (Data.Semigroup.First a_aNZR)) where
  sing = singFun1 @FirstSym0 SFirst
type LastSym0 :: forall (a_aNZW :: Type). (~>) a_aNZW (Data.Semigroup.Last a_aNZW)
data LastSym0 :: (~>) a_aNZW (Data.Semigroup.Last a_aNZW)
  where
    LastSym0KindInference :: SameKind (Apply LastSym0 arg_a1WTX) (LastSym1 arg_a1WTX) =>
                              LastSym0 a6989586621679474542
type instance Apply @a_aNZW @(Data.Semigroup.Last a_aNZW) LastSym0 a6989586621679474542 = 'Data.Semigroup.Last a6989586621679474542
instance SuppressUnusedWarnings LastSym0 where
  suppressUnusedWarnings = snd ((,) LastSym0KindInference ())
type LastSym1 :: forall (a_aNZW :: Type). a_aNZW
                                          -> Data.Semigroup.Last a_aNZW
type family LastSym1 @(a_aNZW :: Type) (a6989586621679474542 :: a_aNZW) :: Data.Semigroup.Last a_aNZW where
  LastSym1 a6989586621679474542 = 'Data.Semigroup.Last a6989586621679474542
type GetLastSym0 :: forall (a_aNZW :: Type). (~>) (Data.Semigroup.Last a_aNZW) a_aNZW
data GetLastSym0 :: (~>) (Data.Semigroup.Last a_aNZW) a_aNZW
  where
    GetLastSym0KindInference :: SameKind (Apply GetLastSym0 arg_a1WU0) (GetLastSym1 arg_a1WU0) =>
                                GetLastSym0 a6989586621679474545
type instance Apply @(Data.Semigroup.Last a_aNZW) @a_aNZW GetLastSym0 a6989586621679474545 = GetLast a6989586621679474545
instance SuppressUnusedWarnings GetLastSym0 where
  suppressUnusedWarnings = snd ((,) GetLastSym0KindInference ())
type GetLastSym1 :: forall (a_aNZW :: Type). Data.Semigroup.Last a_aNZW
                                              -> a_aNZW
type family GetLastSym1 @(a_aNZW :: Type) (a6989586621679474545 :: Data.Semigroup.Last a_aNZW) :: a_aNZW where
  GetLastSym1 a6989586621679474545 = GetLast a6989586621679474545
type GetLast :: forall (a_aNZW :: Type). Data.Semigroup.Last a_aNZW
                                          -> a_aNZW
type family GetLast @(a_aNZW :: Type) (a_a1WTZ :: Data.Semigroup.Last a_aNZW) :: a_aNZW where
  GetLast @a_aNZW ('Data.Semigroup.Last field_a1WU2 :: Data.Semigroup.Last a_aNZW) = field_a1WU2
sGetLast ::
  forall (a_aNZW :: Type)
          (t_a1WU3 :: Data.Semigroup.Last a_aNZW). Sing t_a1WU3
                                                  -> Sing (GetLast t_a1WU3 :: a_aNZW)
sGetLast (SLast (sField :: Sing field_a1WU2)) = sField
instance SingI (GetLastSym0 :: (~>) (Data.Semigroup.Last a_aNZW) a_aNZW) where
  sing = singFun1 @GetLastSym0 sGetLast
type SLast :: forall (a_aNZW :: Type). Data.Semigroup.Last a_aNZW
                                        -> Type
data SLast :: forall (a_aNZW :: Type).
              Data.Semigroup.Last a_aNZW -> Type
  where
    SLast :: forall (a_aNZW :: Type) (n_a1WU5 :: a_aNZW).
              (Sing n_a1WU5) ->
              SLast ('Data.Semigroup.Last n_a1WU5 :: Data.Semigroup.Last a_aNZW)
type instance Sing @(Data.Semigroup.Last a_aNZW) = SLast
instance SingKind a_aNZW =>
          SingKind (Data.Semigroup.Last a_aNZW) where
  type Demote (Data.Semigroup.Last a_aNZW) = Data.Semigroup.Last (Demote a_aNZW)
  fromSing (SLast b_a1WU7) = Data.Semigroup.Last (fromSing b_a1WU7)
  toSing (Data.Semigroup.Last (b_a1WU9 :: Demote a_aNZW))
    = (\cases (SomeSing c_a1WUa) -> SomeSing (SLast c_a1WUa))
        (toSing b_a1WU9 :: SomeSing a_aNZW)
instance SingI n_a1WU5 =>
          SingI ('Data.Semigroup.Last (n_a1WU5 :: a_aNZW)) where
  sing = SLast sing
instance SingI1 'Data.Semigroup.Last where
  liftSing = SLast
instance SingI (LastSym0 :: (~>) a_aNZW (Data.Semigroup.Last a_aNZW)) where
  sing = singFun1 @LastSym0 SLast
type WrapMonoidSym0 :: forall (m_aO0b :: Type). (~>) m_aO0b (Data.Semigroup.WrappedMonoid m_aO0b)
data WrapMonoidSym0 :: (~>) m_aO0b (Data.Semigroup.WrappedMonoid m_aO0b)
  where
    WrapMonoidSym0KindInference :: SameKind (Apply WrapMonoidSym0 arg_a1WUg) (WrapMonoidSym1 arg_a1WUg) =>
                                    WrapMonoidSym0 a6989586621679474561
type instance Apply @m_aO0b @(Data.Semigroup.WrappedMonoid m_aO0b) WrapMonoidSym0 a6989586621679474561 = 'Data.Semigroup.WrapMonoid a6989586621679474561
instance SuppressUnusedWarnings WrapMonoidSym0 where
  suppressUnusedWarnings = snd ((,) WrapMonoidSym0KindInference ())
type WrapMonoidSym1 :: forall (m_aO0b :: Type). m_aO0b
                                                -> Data.Semigroup.WrappedMonoid m_aO0b
type family WrapMonoidSym1 @(m_aO0b :: Type) (a6989586621679474561 :: m_aO0b) :: Data.Semigroup.WrappedMonoid m_aO0b where
  WrapMonoidSym1 a6989586621679474561 = 'Data.Semigroup.WrapMonoid a6989586621679474561
type UnwrapMonoidSym0 :: forall (m_aO0b :: Type). (~>) (Data.Semigroup.WrappedMonoid m_aO0b) m_aO0b
data UnwrapMonoidSym0 :: (~>) (Data.Semigroup.WrappedMonoid m_aO0b) m_aO0b
  where
    UnwrapMonoidSym0KindInference :: SameKind (Apply UnwrapMonoidSym0 arg_a1WUj) (UnwrapMonoidSym1 arg_a1WUj) =>
                                      UnwrapMonoidSym0 a6989586621679474564
type instance Apply @(Data.Semigroup.WrappedMonoid m_aO0b) @m_aO0b UnwrapMonoidSym0 a6989586621679474564 = UnwrapMonoid a6989586621679474564
instance SuppressUnusedWarnings UnwrapMonoidSym0 where
  suppressUnusedWarnings = snd ((,) UnwrapMonoidSym0KindInference ())
type UnwrapMonoidSym1 :: forall (m_aO0b :: Type). Data.Semigroup.WrappedMonoid m_aO0b
                                                  -> m_aO0b
type family UnwrapMonoidSym1 @(m_aO0b :: Type) (a6989586621679474564 :: Data.Semigroup.WrappedMonoid m_aO0b) :: m_aO0b where
  UnwrapMonoidSym1 a6989586621679474564 = UnwrapMonoid a6989586621679474564
type UnwrapMonoid :: forall (m_aO0b :: Type). Data.Semigroup.WrappedMonoid m_aO0b
                                              -> m_aO0b
type family UnwrapMonoid @(m_aO0b :: Type) (a_a1WUi :: Data.Semigroup.WrappedMonoid m_aO0b) :: m_aO0b where
  UnwrapMonoid @m_aO0b ('Data.Semigroup.WrapMonoid field_a1WUl :: Data.Semigroup.WrappedMonoid m_aO0b) = field_a1WUl
sUnwrapMonoid ::
  forall (m_aO0b :: Type)
          (t_a1WUm :: Data.Semigroup.WrappedMonoid m_aO0b). Sing t_a1WUm
                                                            -> Sing (UnwrapMonoid t_a1WUm :: m_aO0b)
sUnwrapMonoid (SWrapMonoid (sField :: Sing field_a1WUl)) = sField
instance SingI (UnwrapMonoidSym0 :: (~>) (Data.Semigroup.WrappedMonoid m_aO0b) m_aO0b) where
  sing = singFun1 @UnwrapMonoidSym0 sUnwrapMonoid
type SWrappedMonoid :: forall (m_aO0b :: Type). Data.Semigroup.WrappedMonoid m_aO0b
                                                -> Type
data SWrappedMonoid :: forall (m_aO0b :: Type).
                        Data.Semigroup.WrappedMonoid m_aO0b -> Type
  where
    SWrapMonoid :: forall (m_aO0b :: Type) (n_a1WUo :: m_aO0b).
                    (Sing n_a1WUo) ->
                    SWrappedMonoid ('Data.Semigroup.WrapMonoid n_a1WUo :: Data.Semigroup.WrappedMonoid m_aO0b)
type instance Sing @(Data.Semigroup.WrappedMonoid m_aO0b) = SWrappedMonoid
instance SingKind m_aO0b =>
          SingKind (Data.Semigroup.WrappedMonoid m_aO0b) where
  type Demote (Data.Semigroup.WrappedMonoid m_aO0b) = Data.Semigroup.WrappedMonoid (Demote m_aO0b)
  fromSing (SWrapMonoid b_a1WUq)
    = Data.Semigroup.WrapMonoid (fromSing b_a1WUq)
  toSing (Data.Semigroup.WrapMonoid (b_a1WUs :: Demote m_aO0b))
    = (\cases (SomeSing c_a1WUt) -> SomeSing (SWrapMonoid c_a1WUt))
        (toSing b_a1WUs :: SomeSing m_aO0b)
instance SingI n_a1WUo =>
          SingI ('Data.Semigroup.WrapMonoid (n_a1WUo :: m_aO0b)) where
  sing = SWrapMonoid sing
instance SingI1 'Data.Semigroup.WrapMonoid where
  liftSing = SWrapMonoid
instance SingI (WrapMonoidSym0 :: (~>) m_aO0b (Data.Semigroup.WrappedMonoid m_aO0b)) where
  sing = singFun1 @WrapMonoidSym0 SWrapMonoid
type MinBound_6989586621679481385 :: forall a_aO0t. Dual a_aO0t
type family MinBound_6989586621679481385 @a_aO0t :: Dual a_aO0t where
  MinBound_6989586621679481385 @a_aO0t = Apply DualSym0 MinBoundSym0
type MaxBound_6989586621679481388 :: forall a_aO0t. Dual a_aO0t
type family MaxBound_6989586621679481388 @a_aO0t :: Dual a_aO0t where
  MaxBound_6989586621679481388 @a_aO0t = Apply DualSym0 MaxBoundSym0
instance PBounded (Dual a_aO0t) where
  type MinBound = MinBound_6989586621679481385
  type MaxBound = MaxBound_6989586621679481388
instance SBounded a_aO0t => SBounded (Dual a_aO0t) where
  sMinBound = applySing (singFun1 @DualSym0 SDual) sMinBound
  sMaxBound = applySing (singFun1 @DualSym0 SDual) sMaxBound
type MinBound_6989586621679481392 :: All
type family MinBound_6989586621679481392 :: All where
  MinBound_6989586621679481392 = Apply AllSym0 MinBoundSym0
type MaxBound_6989586621679481395 :: All
type family MaxBound_6989586621679481395 :: All where
  MaxBound_6989586621679481395 = Apply AllSym0 MaxBoundSym0
instance PBounded All where
  type MinBound = MinBound_6989586621679481392
  type MaxBound = MaxBound_6989586621679481395
instance SBounded Bool => SBounded All where
  sMinBound = applySing (singFun1 @AllSym0 SAll) sMinBound
  sMaxBound = applySing (singFun1 @AllSym0 SAll) sMaxBound
type MinBound_6989586621679481398 :: Any
type family MinBound_6989586621679481398 :: Any where
  MinBound_6989586621679481398 = Apply AnySym0 MinBoundSym0
type MaxBound_6989586621679481401 :: Any
type family MaxBound_6989586621679481401 :: Any where
  MaxBound_6989586621679481401 = Apply AnySym0 MaxBoundSym0
instance PBounded Any where
  type MinBound = MinBound_6989586621679481398
  type MaxBound = MaxBound_6989586621679481401
instance SBounded Bool => SBounded Any where
  sMinBound = applySing (singFun1 @AnySym0 SAny) sMinBound
  sMaxBound = applySing (singFun1 @AnySym0 SAny) sMaxBound
type MinBound_6989586621679481407 :: forall a_aO0D. Sum a_aO0D
type family MinBound_6989586621679481407 @a_aO0D :: Sum a_aO0D where
  MinBound_6989586621679481407 @a_aO0D = Apply SumSym0 MinBoundSym0
type MaxBound_6989586621679481410 :: forall a_aO0D. Sum a_aO0D
type family MaxBound_6989586621679481410 @a_aO0D :: Sum a_aO0D where
  MaxBound_6989586621679481410 @a_aO0D = Apply SumSym0 MaxBoundSym0
instance PBounded (Sum a_aO0D) where
  type MinBound = MinBound_6989586621679481407
  type MaxBound = MaxBound_6989586621679481410
instance SBounded a_aO0D => SBounded (Sum a_aO0D) where
  sMinBound = applySing (singFun1 @SumSym0 SSum) sMinBound
  sMaxBound = applySing (singFun1 @SumSym0 SSum) sMaxBound
type MinBound_6989586621679481416 :: forall a_aO0y. Product a_aO0y
type family MinBound_6989586621679481416 @a_aO0y :: Product a_aO0y where
  MinBound_6989586621679481416 @a_aO0y = Apply ProductSym0 MinBoundSym0
type MaxBound_6989586621679481419 :: forall a_aO0y. Product a_aO0y
type family MaxBound_6989586621679481419 @a_aO0y :: Product a_aO0y where
  MaxBound_6989586621679481419 @a_aO0y = Apply ProductSym0 MaxBoundSym0
instance PBounded (Product a_aO0y) where
  type MinBound = MinBound_6989586621679481416
  type MaxBound = MaxBound_6989586621679481419
instance SBounded a_aO0y => SBounded (Product a_aO0y) where
  sMinBound = applySing (singFun1 @ProductSym0 SProduct) sMinBound
  sMaxBound = applySing (singFun1 @ProductSym0 SProduct) sMaxBound
type MinBound_6989586621679481425 :: forall a_aO06. Data.Semigroup.Min a_aO06
type family MinBound_6989586621679481425 @a_aO06 :: Data.Semigroup.Min a_aO06 where
  MinBound_6989586621679481425 @a_aO06 = Apply MinSym0 MinBoundSym0
type MaxBound_6989586621679481428 :: forall a_aO06. Data.Semigroup.Min a_aO06
type family MaxBound_6989586621679481428 @a_aO06 :: Data.Semigroup.Min a_aO06 where
  MaxBound_6989586621679481428 @a_aO06 = Apply MinSym0 MaxBoundSym0
instance PBounded (Data.Semigroup.Min a_aO06) where
  type MinBound = MinBound_6989586621679481425
  type MaxBound = MaxBound_6989586621679481428
instance SBounded a_aO06 =>
          SBounded (Data.Semigroup.Min a_aO06) where
  sMinBound = applySing (singFun1 @MinSym0 SMin) sMinBound
  sMaxBound = applySing (singFun1 @MinSym0 SMin) sMaxBound
type MinBound_6989586621679481434 :: forall a_aO01. Data.Semigroup.Max a_aO01
type family MinBound_6989586621679481434 @a_aO01 :: Data.Semigroup.Max a_aO01 where
  MinBound_6989586621679481434 @a_aO01 = Apply MaxSym0 MinBoundSym0
type MaxBound_6989586621679481437 :: forall a_aO01. Data.Semigroup.Max a_aO01
type family MaxBound_6989586621679481437 @a_aO01 :: Data.Semigroup.Max a_aO01 where
  MaxBound_6989586621679481437 @a_aO01 = Apply MaxSym0 MaxBoundSym0
instance PBounded (Data.Semigroup.Max a_aO01) where
  type MinBound = MinBound_6989586621679481434
  type MaxBound = MaxBound_6989586621679481437
instance SBounded a_aO01 =>
          SBounded (Data.Semigroup.Max a_aO01) where
  sMinBound = applySing (singFun1 @MaxSym0 SMax) sMinBound
  sMaxBound = applySing (singFun1 @MaxSym0 SMax) sMaxBound
type MinBound_6989586621679481443 :: forall a_aNZR. Data.Semigroup.First a_aNZR
type family MinBound_6989586621679481443 @a_aNZR :: Data.Semigroup.First a_aNZR where
  MinBound_6989586621679481443 @a_aNZR = Apply FirstSym0 MinBoundSym0
type MaxBound_6989586621679481446 :: forall a_aNZR. Data.Semigroup.First a_aNZR
type family MaxBound_6989586621679481446 @a_aNZR :: Data.Semigroup.First a_aNZR where
  MaxBound_6989586621679481446 @a_aNZR = Apply FirstSym0 MaxBoundSym0
instance PBounded (Data.Semigroup.First a_aNZR) where
  type MinBound = MinBound_6989586621679481443
  type MaxBound = MaxBound_6989586621679481446
instance SBounded a_aNZR =>
          SBounded (Data.Semigroup.First a_aNZR) where
  sMinBound = applySing (singFun1 @FirstSym0 SFirst) sMinBound
  sMaxBound = applySing (singFun1 @FirstSym0 SFirst) sMaxBound
type MinBound_6989586621679481452 :: forall a_aNZW. Data.Semigroup.Last a_aNZW
type family MinBound_6989586621679481452 @a_aNZW :: Data.Semigroup.Last a_aNZW where
  MinBound_6989586621679481452 @a_aNZW = Apply LastSym0 MinBoundSym0
type MaxBound_6989586621679481455 :: forall a_aNZW. Data.Semigroup.Last a_aNZW
type family MaxBound_6989586621679481455 @a_aNZW :: Data.Semigroup.Last a_aNZW where
  MaxBound_6989586621679481455 @a_aNZW = Apply LastSym0 MaxBoundSym0
instance PBounded (Data.Semigroup.Last a_aNZW) where
  type MinBound = MinBound_6989586621679481452
  type MaxBound = MaxBound_6989586621679481455
instance SBounded a_aNZW =>
          SBounded (Data.Semigroup.Last a_aNZW) where
  sMinBound = applySing (singFun1 @LastSym0 SLast) sMinBound
  sMaxBound = applySing (singFun1 @LastSym0 SLast) sMaxBound
type MinBound_6989586621679481461 :: forall m_aO0b. Data.Semigroup.WrappedMonoid m_aO0b
type family MinBound_6989586621679481461 @m_aO0b :: Data.Semigroup.WrappedMonoid m_aO0b where
  MinBound_6989586621679481461 @m_aO0b = Apply WrapMonoidSym0 MinBoundSym0
type MaxBound_6989586621679481464 :: forall m_aO0b. Data.Semigroup.WrappedMonoid m_aO0b
type family MaxBound_6989586621679481464 @m_aO0b :: Data.Semigroup.WrappedMonoid m_aO0b where
  MaxBound_6989586621679481464 @m_aO0b = Apply WrapMonoidSym0 MaxBoundSym0
instance PBounded (Data.Semigroup.WrappedMonoid m_aO0b) where
  type MinBound = MinBound_6989586621679481461
  type MaxBound = MaxBound_6989586621679481464
instance SBounded m_aO0b =>
          SBounded (Data.Semigroup.WrappedMonoid m_aO0b) where
  sMinBound
    = applySing (singFun1 @WrapMonoidSym0 SWrapMonoid) sMinBound
  sMaxBound
    = applySing (singFun1 @WrapMonoidSym0 SWrapMonoid) sMaxBound
type TFHelper_6989586621679483282 :: forall a_aO0t. Dual a_aO0t
                                                        -> Dual a_aO0t -> Bool
type family TFHelper_6989586621679483282 @a_aO0t (a_a1ZaY :: Dual a_aO0t) (a_a1ZaZ :: Dual a_aO0t) :: Bool where
  TFHelper_6989586621679483282 @a_aO0t ('Dual a_6989586621679483255_a1Zb3 :: Dual a_aO0t) ('Dual b_6989586621679483257_a1Zb4 :: Dual a_aO0t) = Apply (Apply (==@#@$) a_6989586621679483255_a1Zb3) b_6989586621679483257_a1Zb4
instance PEq (Dual a_aO0t) where
  type (==) a_a1ZaU a_a1ZaV = TFHelper_6989586621679483282 a_a1ZaU a_a1ZaV
instance SEq a_aO0t => SEq (Dual a_aO0t) where
  (%==)
    (SDual (sA_6989586621679483255 :: Sing a_6989586621679483255_a1Zb3))
    (SDual (sB_6989586621679483257 :: Sing b_6989586621679483257_a1Zb4))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483255)
        sB_6989586621679483257
type TFHelper_6989586621679483297 :: All -> All -> Bool
type family TFHelper_6989586621679483297 (a_a1Zbd :: All) (a_a1Zbe :: All) :: Bool where
  TFHelper_6989586621679483297 ('All a_6989586621679483291_a1Zbi) ('All b_6989586621679483293_a1Zbj) = Apply (Apply (==@#@$) a_6989586621679483291_a1Zbi) b_6989586621679483293_a1Zbj
instance PEq All where
  type (==) a_a1Zb9 a_a1Zba = TFHelper_6989586621679483297 a_a1Zb9 a_a1Zba
instance SEq Bool => SEq All where
  (%==)
    (SAll (sA_6989586621679483291 :: Sing a_6989586621679483291_a1Zbi))
    (SAll (sB_6989586621679483293 :: Sing b_6989586621679483293_a1Zbj))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483291)
        sB_6989586621679483293
type TFHelper_6989586621679483312 :: Any -> Any -> Bool
type family TFHelper_6989586621679483312 (a_a1Zbs :: Any) (a_a1Zbt :: Any) :: Bool where
  TFHelper_6989586621679483312 ('Any a_6989586621679483306_a1Zbx) ('Any b_6989586621679483308_a1Zby) = Apply (Apply (==@#@$) a_6989586621679483306_a1Zbx) b_6989586621679483308_a1Zby
instance PEq Any where
  type (==) a_a1Zbo a_a1Zbp = TFHelper_6989586621679483312 a_a1Zbo a_a1Zbp
instance SEq Bool => SEq Any where
  (%==)
    (SAny (sA_6989586621679483306 :: Sing a_6989586621679483306_a1Zbx))
    (SAny (sB_6989586621679483308 :: Sing b_6989586621679483308_a1Zby))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483306)
        sB_6989586621679483308
type TFHelper_6989586621679483330 :: forall a_aO0D. Sum a_aO0D
                                                    -> Sum a_aO0D -> Bool
type family TFHelper_6989586621679483330 @a_aO0D (a_a1ZbK :: Sum a_aO0D) (a_a1ZbL :: Sum a_aO0D) :: Bool where
  TFHelper_6989586621679483330 @a_aO0D ('Sum a_6989586621679483324_a1ZbP :: Sum a_aO0D) ('Sum b_6989586621679483326_a1ZbQ :: Sum a_aO0D) = Apply (Apply (==@#@$) a_6989586621679483324_a1ZbP) b_6989586621679483326_a1ZbQ
instance PEq (Sum a_aO0D) where
  type (==) a_a1ZbG a_a1ZbH = TFHelper_6989586621679483330 a_a1ZbG a_a1ZbH
instance SEq a_aO0D => SEq (Sum a_aO0D) where
  (%==)
    (SSum (sA_6989586621679483324 :: Sing a_6989586621679483324_a1ZbP))
    (SSum (sB_6989586621679483326 :: Sing b_6989586621679483326_a1ZbQ))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483324)
        sB_6989586621679483326
type TFHelper_6989586621679483348 :: forall a_aO0y. Product a_aO0y
                                                    -> Product a_aO0y -> Bool
type family TFHelper_6989586621679483348 @a_aO0y (a_a1Zc2 :: Product a_aO0y) (a_a1Zc3 :: Product a_aO0y) :: Bool where
  TFHelper_6989586621679483348 @a_aO0y ('Product a_6989586621679483342_a1Zc7 :: Product a_aO0y) ('Product b_6989586621679483344_a1Zc8 :: Product a_aO0y) = Apply (Apply (==@#@$) a_6989586621679483342_a1Zc7) b_6989586621679483344_a1Zc8
instance PEq (Product a_aO0y) where
  type (==) a_a1ZbY a_a1ZbZ = TFHelper_6989586621679483348 a_a1ZbY a_a1ZbZ
instance SEq a_aO0y => SEq (Product a_aO0y) where
  (%==)
    (SProduct (sA_6989586621679483342 :: Sing a_6989586621679483342_a1Zc7))
    (SProduct (sB_6989586621679483344 :: Sing b_6989586621679483344_a1Zc8))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483342)
        sB_6989586621679483344
type TFHelper_6989586621679483366 :: forall a_aO06. Data.Semigroup.Min a_aO06
                                                    -> Data.Semigroup.Min a_aO06 -> Bool
type family TFHelper_6989586621679483366 @a_aO06 (a_a1Zck :: Data.Semigroup.Min a_aO06) (a_a1Zcl :: Data.Semigroup.Min a_aO06) :: Bool where
  TFHelper_6989586621679483366 @a_aO06 ('Data.Semigroup.Min a_6989586621679483360_a1Zcp :: Data.Semigroup.Min a_aO06) ('Data.Semigroup.Min b_6989586621679483362_a1Zcq :: Data.Semigroup.Min a_aO06) = Apply (Apply (==@#@$) a_6989586621679483360_a1Zcp) b_6989586621679483362_a1Zcq
instance PEq (Data.Semigroup.Min a_aO06) where
  type (==) a_a1Zcg a_a1Zch = TFHelper_6989586621679483366 a_a1Zcg a_a1Zch
instance SEq a_aO06 => SEq (Data.Semigroup.Min a_aO06) where
  (%==)
    (SMin (sA_6989586621679483360 :: Sing a_6989586621679483360_a1Zcp))
    (SMin (sB_6989586621679483362 :: Sing b_6989586621679483362_a1Zcq))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483360)
        sB_6989586621679483362
type TFHelper_6989586621679483384 :: forall a_aO01. Data.Semigroup.Max a_aO01
                                                    -> Data.Semigroup.Max a_aO01 -> Bool
type family TFHelper_6989586621679483384 @a_aO01 (a_a1ZcC :: Data.Semigroup.Max a_aO01) (a_a1ZcD :: Data.Semigroup.Max a_aO01) :: Bool where
  TFHelper_6989586621679483384 @a_aO01 ('Data.Semigroup.Max a_6989586621679483378_a1ZcH :: Data.Semigroup.Max a_aO01) ('Data.Semigroup.Max b_6989586621679483380_a1ZcI :: Data.Semigroup.Max a_aO01) = Apply (Apply (==@#@$) a_6989586621679483378_a1ZcH) b_6989586621679483380_a1ZcI
instance PEq (Data.Semigroup.Max a_aO01) where
  type (==) a_a1Zcy a_a1Zcz = TFHelper_6989586621679483384 a_a1Zcy a_a1Zcz
instance SEq a_aO01 => SEq (Data.Semigroup.Max a_aO01) where
  (%==)
    (SMax (sA_6989586621679483378 :: Sing a_6989586621679483378_a1ZcH))
    (SMax (sB_6989586621679483380 :: Sing b_6989586621679483380_a1ZcI))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483378)
        sB_6989586621679483380
type TFHelper_6989586621679483402 :: forall a_aNZR. Data.Semigroup.First a_aNZR
                                                    -> Data.Semigroup.First a_aNZR -> Bool
type family TFHelper_6989586621679483402 @a_aNZR (a_a1ZcU :: Data.Semigroup.First a_aNZR) (a_a1ZcV :: Data.Semigroup.First a_aNZR) :: Bool where
  TFHelper_6989586621679483402 @a_aNZR ('Data.Semigroup.First a_6989586621679483396_a1ZcZ :: Data.Semigroup.First a_aNZR) ('Data.Semigroup.First b_6989586621679483398_a1Zd0 :: Data.Semigroup.First a_aNZR) = Apply (Apply (==@#@$) a_6989586621679483396_a1ZcZ) b_6989586621679483398_a1Zd0
instance PEq (Data.Semigroup.First a_aNZR) where
  type (==) a_a1ZcQ a_a1ZcR = TFHelper_6989586621679483402 a_a1ZcQ a_a1ZcR
instance SEq a_aNZR => SEq (Data.Semigroup.First a_aNZR) where
  (%==)
    (SFirst (sA_6989586621679483396 :: Sing a_6989586621679483396_a1ZcZ))
    (SFirst (sB_6989586621679483398 :: Sing b_6989586621679483398_a1Zd0))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483396)
        sB_6989586621679483398
type TFHelper_6989586621679483420 :: forall a_aNZW. Data.Semigroup.Last a_aNZW
                                                    -> Data.Semigroup.Last a_aNZW -> Bool
type family TFHelper_6989586621679483420 @a_aNZW (a_a1Zdc :: Data.Semigroup.Last a_aNZW) (a_a1Zdd :: Data.Semigroup.Last a_aNZW) :: Bool where
  TFHelper_6989586621679483420 @a_aNZW ('Data.Semigroup.Last a_6989586621679483414_a1Zdh :: Data.Semigroup.Last a_aNZW) ('Data.Semigroup.Last b_6989586621679483416_a1Zdi :: Data.Semigroup.Last a_aNZW) = Apply (Apply (==@#@$) a_6989586621679483414_a1Zdh) b_6989586621679483416_a1Zdi
instance PEq (Data.Semigroup.Last a_aNZW) where
  type (==) a_a1Zd8 a_a1Zd9 = TFHelper_6989586621679483420 a_a1Zd8 a_a1Zd9
instance SEq a_aNZW => SEq (Data.Semigroup.Last a_aNZW) where
  (%==)
    (SLast (sA_6989586621679483414 :: Sing a_6989586621679483414_a1Zdh))
    (SLast (sB_6989586621679483416 :: Sing b_6989586621679483416_a1Zdi))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483414)
        sB_6989586621679483416
type TFHelper_6989586621679483438 :: forall m_aO0b. Data.Semigroup.WrappedMonoid m_aO0b
                                                    -> Data.Semigroup.WrappedMonoid m_aO0b
                                                        -> Bool
type family TFHelper_6989586621679483438 @m_aO0b (a_a1Zdu :: Data.Semigroup.WrappedMonoid m_aO0b) (a_a1Zdv :: Data.Semigroup.WrappedMonoid m_aO0b) :: Bool where
  TFHelper_6989586621679483438 @m_aO0b ('Data.Semigroup.WrapMonoid a_6989586621679483432_a1Zdz :: Data.Semigroup.WrappedMonoid m_aO0b) ('Data.Semigroup.WrapMonoid b_6989586621679483434_a1ZdA :: Data.Semigroup.WrappedMonoid m_aO0b) = Apply (Apply (==@#@$) a_6989586621679483432_a1Zdz) b_6989586621679483434_a1ZdA
instance PEq (Data.Semigroup.WrappedMonoid m_aO0b) where
  type (==) a_a1Zdq a_a1Zdr = TFHelper_6989586621679483438 a_a1Zdq a_a1Zdr
instance SEq m_aO0b =>
          SEq (Data.Semigroup.WrappedMonoid m_aO0b) where
  (%==)
    (SWrapMonoid (sA_6989586621679483432 :: Sing a_6989586621679483432_a1Zdz))
    (SWrapMonoid (sB_6989586621679483434 :: Sing b_6989586621679483434_a1ZdA))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679483432)
        sB_6989586621679483434
instance SDecide a_aO0t => SDecide (Dual a_aO0t) where
      (%~) (SDual a_a1ZJQ) (SDual b_a1ZJR)
        = (\cases
             (Proved Refl) -> Proved Refl
             (Disproved contra_a1ZJS)
               -> Disproved (\cases Refl -> contra_a1ZJS Refl))
            ((%~) a_a1ZJQ b_a1ZJR)
instance Eq (SDual (z_a1ZJV :: Dual a_aO0t)) where
  (==) _ _ = True
instance SDecide a_aO0t =>
          Data.Type.Equality.TestEquality (SDual :: Dual a_aO0t
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_aO0t =>
          Data.Type.Coercion.TestCoercion (SDual :: Dual a_aO0t
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide Bool => SDecide All where
  (%~) (SAll a_a1ZK2) (SAll b_a1ZK3)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a1ZK4)
            -> Disproved (\cases Refl -> contra_a1ZK4 Refl))
        ((%~) a_a1ZK2 b_a1ZK3)
instance Eq (SAll (z_a1ZK5 :: All)) where
  (==) _ _ = True
instance SDecide Bool =>
          Data.Type.Equality.TestEquality (SAll :: All -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide Bool =>
          Data.Type.Coercion.TestCoercion (SAll :: All -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide Bool => SDecide Any where
  (%~) (SAny a_a1ZK8) (SAny b_a1ZK9)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a1ZKa)
            -> Disproved (\cases Refl -> contra_a1ZKa Refl))
        ((%~) a_a1ZK8 b_a1ZK9)
instance Eq (SAny (z_a1ZKb :: Any)) where
  (==) _ _ = True
instance SDecide Bool =>
          Data.Type.Equality.TestEquality (SAny :: Any -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide Bool =>
          Data.Type.Coercion.TestCoercion (SAny :: Any -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide a_aO0D => SDecide (Sum a_aO0D) where
  (%~) (SSum a_a1ZKf) (SSum b_a1ZKg)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a1ZKh)
            -> Disproved (\cases Refl -> contra_a1ZKh Refl))
        ((%~) a_a1ZKf b_a1ZKg)
instance Eq (SSum (z_a1ZKk :: Sum a_aO0D)) where
  (==) _ _ = True
instance SDecide a_aO0D =>
          Data.Type.Equality.TestEquality (SSum :: Sum a_aO0D -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_aO0D =>
          Data.Type.Coercion.TestCoercion (SSum :: Sum a_aO0D -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide a_aO0y => SDecide (Product a_aO0y) where
  (%~) (SProduct a_a1ZKs) (SProduct b_a1ZKt)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a1ZKu)
            -> Disproved (\cases Refl -> contra_a1ZKu Refl))
        ((%~) a_a1ZKs b_a1ZKt)
instance Eq (SProduct (z_a1ZKx :: Product a_aO0y)) where
  (==) _ _ = True
instance SDecide a_aO0y =>
          Data.Type.Equality.TestEquality (SProduct :: Product a_aO0y
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_aO0y =>
          Data.Type.Coercion.TestCoercion (SProduct :: Product a_aO0y
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide a_aO06 =>
          SDecide (Data.Semigroup.Min a_aO06) where
  (%~) (SMin a_a1ZKF) (SMin b_a1ZKG)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a1ZKH)
            -> Disproved (\cases Refl -> contra_a1ZKH Refl))
        ((%~) a_a1ZKF b_a1ZKG)
instance Eq (SMin (z_a1ZKK :: Data.Semigroup.Min a_aO06)) where
  (==) _ _ = True
instance SDecide a_aO06 =>
          Data.Type.Equality.TestEquality (SMin :: Data.Semigroup.Min a_aO06
                                                  -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_aO06 =>
          Data.Type.Coercion.TestCoercion (SMin :: Data.Semigroup.Min a_aO06
                                                  -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide a_aO01 =>
          SDecide (Data.Semigroup.Max a_aO01) where
  (%~) (SMax a_a1ZKS) (SMax b_a1ZKT)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a1ZKU)
            -> Disproved (\cases Refl -> contra_a1ZKU Refl))
        ((%~) a_a1ZKS b_a1ZKT)
instance Eq (SMax (z_a1ZKX :: Data.Semigroup.Max a_aO01)) where
  (==) _ _ = True
instance SDecide a_aO01 =>
          Data.Type.Equality.TestEquality (SMax :: Data.Semigroup.Max a_aO01
                                                  -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_aO01 =>
          Data.Type.Coercion.TestCoercion (SMax :: Data.Semigroup.Max a_aO01
                                                  -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide a_aNZR =>
          SDecide (Data.Semigroup.First a_aNZR) where
  (%~) (SFirst a_a1ZL5) (SFirst b_a1ZL6)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a1ZL7)
            -> Disproved (\cases Refl -> contra_a1ZL7 Refl))
        ((%~) a_a1ZL5 b_a1ZL6)
instance Eq (SFirst (z_a1ZLa :: Data.Semigroup.First a_aNZR)) where
  (==) _ _ = True
instance SDecide a_aNZR =>
          Data.Type.Equality.TestEquality (SFirst :: Data.Semigroup.First a_aNZR
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_aNZR =>
          Data.Type.Coercion.TestCoercion (SFirst :: Data.Semigroup.First a_aNZR
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide a_aNZW =>
          SDecide (Data.Semigroup.Last a_aNZW) where
  (%~) (SLast a_a1ZLi) (SLast b_a1ZLj)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a1ZLk)
            -> Disproved (\cases Refl -> contra_a1ZLk Refl))
        ((%~) a_a1ZLi b_a1ZLj)
instance Eq (SLast (z_a1ZLn :: Data.Semigroup.Last a_aNZW)) where
  (==) _ _ = True
instance SDecide a_aNZW =>
          Data.Type.Equality.TestEquality (SLast :: Data.Semigroup.Last a_aNZW
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_aNZW =>
          Data.Type.Coercion.TestCoercion (SLast :: Data.Semigroup.Last a_aNZW
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide m_aO0b =>
          SDecide (Data.Semigroup.WrappedMonoid m_aO0b) where
  (%~) (SWrapMonoid a_a1ZLv) (SWrapMonoid b_a1ZLw)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a1ZLx)
            -> Disproved (\cases Refl -> contra_a1ZLx Refl))
        ((%~) a_a1ZLv b_a1ZLw)
instance Eq (SWrappedMonoid (z_a1ZLA :: Data.Semigroup.WrappedMonoid m_aO0b)) where
  (==) _ _ = True
instance SDecide m_aO0b =>
          Data.Type.Equality.TestEquality (SWrappedMonoid :: Data.Semigroup.WrappedMonoid m_aO0b
                                                            -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide m_aO0b =>
          Data.Type.Coercion.TestCoercion (SWrappedMonoid :: Data.Semigroup.WrappedMonoid m_aO0b
                                                            -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
type Compare_6989586621679488381 :: forall a_aO0t. Dual a_aO0t
                                                       -> Dual a_aO0t -> Ordering
type family Compare_6989586621679488381 @a_aO0t (a_a20vd :: Dual a_aO0t) (a_a20ve :: Dual a_aO0t) :: Ordering where
  Compare_6989586621679488381 @a_aO0t ('Dual a_6989586621679487742_a20vi :: Dual a_aO0t) ('Dual b_6989586621679487744_a20vj :: Dual a_aO0t) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679487742_a20vi) b_6989586621679487744_a20vj)) NilSym0)
instance POrd (Dual a_aO0t) where
  type Compare a_a20v9 a_a20va = Compare_6989586621679488381 a_a20v9 a_a20va
instance SOrd a_aO0t => SOrd (Dual a_aO0t) where
  sCompare
    (SDual (sA_6989586621679487742 :: Sing a_6989586621679487742_a20vi))
    (SDual (sB_6989586621679487744 :: Sing b_6989586621679487744_a20vj))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679487742)
                  sB_6989586621679487744))
            SNil)
type Compare_6989586621679488396 :: All -> All -> Ordering
type family Compare_6989586621679488396 (a_a20vs :: All) (a_a20vt :: All) :: Ordering where
  Compare_6989586621679488396 ('All a_6989586621679488390_a20vx) ('All b_6989586621679488392_a20vy) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679488390_a20vx) b_6989586621679488392_a20vy)) NilSym0)
instance POrd All where
  type Compare a_a20vo a_a20vp = Compare_6989586621679488396 a_a20vo a_a20vp
instance SOrd Bool => SOrd All where
  sCompare
    (SAll (sA_6989586621679488390 :: Sing a_6989586621679488390_a20vx))
    (SAll (sB_6989586621679488392 :: Sing b_6989586621679488392_a20vy))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679488390)
                  sB_6989586621679488392))
            SNil)
type Compare_6989586621679488411 :: Any -> Any -> Ordering
type family Compare_6989586621679488411 (a_a20vH :: Any) (a_a20vI :: Any) :: Ordering where
  Compare_6989586621679488411 ('Any a_6989586621679488405_a20vM) ('Any b_6989586621679488407_a20vN) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679488405_a20vM) b_6989586621679488407_a20vN)) NilSym0)
instance POrd Any where
  type Compare a_a20vD a_a20vE = Compare_6989586621679488411 a_a20vD a_a20vE
instance SOrd Bool => SOrd Any where
  sCompare
    (SAny (sA_6989586621679488405 :: Sing a_6989586621679488405_a20vM))
    (SAny (sB_6989586621679488407 :: Sing b_6989586621679488407_a20vN))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679488405)
                  sB_6989586621679488407))
            SNil)
type Compare_6989586621679488429 :: forall a_aO0D. Sum a_aO0D
                                                    -> Sum a_aO0D -> Ordering
type family Compare_6989586621679488429 @a_aO0D (a_a20vZ :: Sum a_aO0D) (a_a20w0 :: Sum a_aO0D) :: Ordering where
  Compare_6989586621679488429 @a_aO0D ('Sum a_6989586621679488423_a20w4 :: Sum a_aO0D) ('Sum b_6989586621679488425_a20w5 :: Sum a_aO0D) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679488423_a20w4) b_6989586621679488425_a20w5)) NilSym0)
instance POrd (Sum a_aO0D) where
  type Compare a_a20vV a_a20vW = Compare_6989586621679488429 a_a20vV a_a20vW
instance SOrd a_aO0D => SOrd (Sum a_aO0D) where
  sCompare
    (SSum (sA_6989586621679488423 :: Sing a_6989586621679488423_a20w4))
    (SSum (sB_6989586621679488425 :: Sing b_6989586621679488425_a20w5))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679488423)
                  sB_6989586621679488425))
            SNil)
type Compare_6989586621679488447 :: forall a_aO0y. Product a_aO0y
                                                    -> Product a_aO0y -> Ordering
type family Compare_6989586621679488447 @a_aO0y (a_a20wh :: Product a_aO0y) (a_a20wi :: Product a_aO0y) :: Ordering where
  Compare_6989586621679488447 @a_aO0y ('Product a_6989586621679488441_a20wm :: Product a_aO0y) ('Product b_6989586621679488443_a20wn :: Product a_aO0y) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679488441_a20wm) b_6989586621679488443_a20wn)) NilSym0)
instance POrd (Product a_aO0y) where
  type Compare a_a20wd a_a20we = Compare_6989586621679488447 a_a20wd a_a20we
instance SOrd a_aO0y => SOrd (Product a_aO0y) where
  sCompare
    (SProduct (sA_6989586621679488441 :: Sing a_6989586621679488441_a20wm))
    (SProduct (sB_6989586621679488443 :: Sing b_6989586621679488443_a20wn))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679488441)
                  sB_6989586621679488443))
            SNil)
type Compare_6989586621679488465 :: forall a_aO06. Data.Semigroup.Min a_aO06
                                                    -> Data.Semigroup.Min a_aO06 -> Ordering
type family Compare_6989586621679488465 @a_aO06 (a_a20wz :: Data.Semigroup.Min a_aO06) (a_a20wA :: Data.Semigroup.Min a_aO06) :: Ordering where
  Compare_6989586621679488465 @a_aO06 ('Data.Semigroup.Min a_6989586621679488459_a20wE :: Data.Semigroup.Min a_aO06) ('Data.Semigroup.Min b_6989586621679488461_a20wF :: Data.Semigroup.Min a_aO06) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679488459_a20wE) b_6989586621679488461_a20wF)) NilSym0)
instance POrd (Data.Semigroup.Min a_aO06) where
  type Compare a_a20wv a_a20ww = Compare_6989586621679488465 a_a20wv a_a20ww
instance SOrd a_aO06 => SOrd (Data.Semigroup.Min a_aO06) where
  sCompare
    (SMin (sA_6989586621679488459 :: Sing a_6989586621679488459_a20wE))
    (SMin (sB_6989586621679488461 :: Sing b_6989586621679488461_a20wF))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679488459)
                  sB_6989586621679488461))
            SNil)
type Compare_6989586621679488483 :: forall a_aO01. Data.Semigroup.Max a_aO01
                                                    -> Data.Semigroup.Max a_aO01 -> Ordering
type family Compare_6989586621679488483 @a_aO01 (a_a20wR :: Data.Semigroup.Max a_aO01) (a_a20wS :: Data.Semigroup.Max a_aO01) :: Ordering where
  Compare_6989586621679488483 @a_aO01 ('Data.Semigroup.Max a_6989586621679488477_a20wW :: Data.Semigroup.Max a_aO01) ('Data.Semigroup.Max b_6989586621679488479_a20wX :: Data.Semigroup.Max a_aO01) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679488477_a20wW) b_6989586621679488479_a20wX)) NilSym0)
instance POrd (Data.Semigroup.Max a_aO01) where
  type Compare a_a20wN a_a20wO = Compare_6989586621679488483 a_a20wN a_a20wO
instance SOrd a_aO01 => SOrd (Data.Semigroup.Max a_aO01) where
  sCompare
    (SMax (sA_6989586621679488477 :: Sing a_6989586621679488477_a20wW))
    (SMax (sB_6989586621679488479 :: Sing b_6989586621679488479_a20wX))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679488477)
                  sB_6989586621679488479))
            SNil)
type Compare_6989586621679488501 :: forall a_aNZR. Data.Semigroup.First a_aNZR
                                                    -> Data.Semigroup.First a_aNZR -> Ordering
type family Compare_6989586621679488501 @a_aNZR (a_a20x9 :: Data.Semigroup.First a_aNZR) (a_a20xa :: Data.Semigroup.First a_aNZR) :: Ordering where
  Compare_6989586621679488501 @a_aNZR ('Data.Semigroup.First a_6989586621679488495_a20xe :: Data.Semigroup.First a_aNZR) ('Data.Semigroup.First b_6989586621679488497_a20xf :: Data.Semigroup.First a_aNZR) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679488495_a20xe) b_6989586621679488497_a20xf)) NilSym0)
instance POrd (Data.Semigroup.First a_aNZR) where
  type Compare a_a20x5 a_a20x6 = Compare_6989586621679488501 a_a20x5 a_a20x6
instance SOrd a_aNZR => SOrd (Data.Semigroup.First a_aNZR) where
  sCompare
    (SFirst (sA_6989586621679488495 :: Sing a_6989586621679488495_a20xe))
    (SFirst (sB_6989586621679488497 :: Sing b_6989586621679488497_a20xf))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679488495)
                  sB_6989586621679488497))
            SNil)
type Compare_6989586621679488519 :: forall a_aNZW. Data.Semigroup.Last a_aNZW
                                                    -> Data.Semigroup.Last a_aNZW -> Ordering
type family Compare_6989586621679488519 @a_aNZW (a_a20xr :: Data.Semigroup.Last a_aNZW) (a_a20xs :: Data.Semigroup.Last a_aNZW) :: Ordering where
  Compare_6989586621679488519 @a_aNZW ('Data.Semigroup.Last a_6989586621679488513_a20xw :: Data.Semigroup.Last a_aNZW) ('Data.Semigroup.Last b_6989586621679488515_a20xx :: Data.Semigroup.Last a_aNZW) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679488513_a20xw) b_6989586621679488515_a20xx)) NilSym0)
instance POrd (Data.Semigroup.Last a_aNZW) where
  type Compare a_a20xn a_a20xo = Compare_6989586621679488519 a_a20xn a_a20xo
instance SOrd a_aNZW => SOrd (Data.Semigroup.Last a_aNZW) where
  sCompare
    (SLast (sA_6989586621679488513 :: Sing a_6989586621679488513_a20xw))
    (SLast (sB_6989586621679488515 :: Sing b_6989586621679488515_a20xx))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679488513)
                  sB_6989586621679488515))
            SNil)
type Compare_6989586621679488537 :: forall m_aO0b. Data.Semigroup.WrappedMonoid m_aO0b
                                                    -> Data.Semigroup.WrappedMonoid m_aO0b
                                                      -> Ordering
type family Compare_6989586621679488537 @m_aO0b (a_a20xJ :: Data.Semigroup.WrappedMonoid m_aO0b) (a_a20xK :: Data.Semigroup.WrappedMonoid m_aO0b) :: Ordering where
  Compare_6989586621679488537 @m_aO0b ('Data.Semigroup.WrapMonoid a_6989586621679488531_a20xO :: Data.Semigroup.WrappedMonoid m_aO0b) ('Data.Semigroup.WrapMonoid b_6989586621679488533_a20xP :: Data.Semigroup.WrappedMonoid m_aO0b) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679488531_a20xO) b_6989586621679488533_a20xP)) NilSym0)
instance POrd (Data.Semigroup.WrappedMonoid m_aO0b) where
  type Compare a_a20xF a_a20xG = Compare_6989586621679488537 a_a20xF a_a20xG
instance SOrd m_aO0b =>
          SOrd (Data.Semigroup.WrappedMonoid m_aO0b) where
  sCompare
    (SWrapMonoid (sA_6989586621679488531 :: Sing a_6989586621679488531_a20xO))
    (SWrapMonoid (sB_6989586621679488533 :: Sing b_6989586621679488533_a20xP))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679488531)
                  sB_6989586621679488533))
            SNil)

type Pure_6989586621679495010 :: forall a_i1v3p. a_i1v3p
                                                     -> Dual a_i1v3p
type family Pure_6989586621679495010 @a_i1v3p (a_a22ea :: a_i1v3p) :: Dual a_i1v3p where
  Pure_6989586621679495010 @a_i1v3p a_6989586621679495012_a22ed = Apply DualSym0 a_6989586621679495012_a22ed
type TFHelper_6989586621679495020 :: forall a_i1v3r
                                            b_i1v3s. Dual ((~>) a_i1v3r b_i1v3s)
                                                      -> Dual a_i1v3r -> Dual b_i1v3s
type family TFHelper_6989586621679495020 @a_i1v3r @b_i1v3s (a_a22ei :: Dual ((~>) a_i1v3r b_i1v3s)) (a_a22ej :: Dual a_i1v3r) :: Dual b_i1v3s where
  TFHelper_6989586621679495020 @a_i1v3r @b_i1v3s ('Dual f_a22en) ('Dual x_a22eo) = Apply DualSym0 (Apply f_a22en x_a22eo)
instance PApplicative Dual where
  type Pure a_a22e5 = Pure_6989586621679495010 a_a22e5
  type (<*>) a_a22ee a_a22ef = TFHelper_6989586621679495020 a_a22ee a_a22ef
type Fmap_6989586621679495031 :: forall a_i1v3K
                                        b_i1v3L. (~>) a_i1v3K b_i1v3L
                                                  -> Dual a_i1v3K -> Dual b_i1v3L
type family Fmap_6989586621679495031 @a_i1v3K @b_i1v3L (a_a22et :: (~>) a_i1v3K b_i1v3L) (a_a22eu :: Dual a_i1v3K) :: Dual b_i1v3L where
  Fmap_6989586621679495031 @a_i1v3K @b_i1v3L _f_6989586621679494822_a22ey ('Dual a_6989586621679494826_a22ez) = Apply DualSym0 (Apply _f_6989586621679494822_a22ey a_6989586621679494826_a22ez)
type family LamCases_6989586621679495051_a22eM (_z_69895866216794948246989586621679495049 :: a7566047373982791008) a_69895866216794948286989586621679495050 a_6989586621679495053_a22eO where
  LamCases_6989586621679495051_a22eM _z_6989586621679494824_a22eJ a_6989586621679494828_a22eK _ = _z_6989586621679494824_a22eJ
data LamCases_6989586621679495051Sym0 (_z_69895866216794948246989586621679495049 :: a7566047373982791008) a_69895866216794948286989586621679495050 a_69895866216794950536989586621679495054
  where
    LamCases_6989586621679495051Sym0KindInference :: SameKind (Apply (LamCases_6989586621679495051Sym0 _z_69895866216794948246989586621679495049 a_69895866216794948286989586621679495050) arg_a22eP) (LamCases_6989586621679495051Sym1 _z_69895866216794948246989586621679495049 a_69895866216794948286989586621679495050 arg_a22eP) =>
                                                      LamCases_6989586621679495051Sym0 _z_69895866216794948246989586621679495049 a_69895866216794948286989586621679495050 a_69895866216794950536989586621679495054
type instance Apply @_ @_ (LamCases_6989586621679495051Sym0 _z_69895866216794948246989586621679495049 a_69895866216794948286989586621679495050) a_69895866216794950536989586621679495054 = LamCases_6989586621679495051_a22eM _z_69895866216794948246989586621679495049 a_69895866216794948286989586621679495050 a_69895866216794950536989586621679495054
instance SuppressUnusedWarnings (LamCases_6989586621679495051Sym0 _z_69895866216794948246989586621679495049 a_69895866216794948286989586621679495050) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679495051Sym0KindInference ())
type family LamCases_6989586621679495051Sym1 (_z_69895866216794948246989586621679495049 :: a7566047373982791008) a_69895866216794948286989586621679495050 a_69895866216794950536989586621679495054 where
  LamCases_6989586621679495051Sym1 _z_69895866216794948246989586621679495049 a_69895866216794948286989586621679495050 a_69895866216794950536989586621679495054 = LamCases_6989586621679495051_a22eM _z_69895866216794948246989586621679495049 a_69895866216794948286989586621679495050 a_69895866216794950536989586621679495054
type TFHelper_6989586621679495042 :: forall a_i1v3O
                                            b_i1v3P. a_i1v3O -> Dual b_i1v3P -> Dual a_i1v3O
type family TFHelper_6989586621679495042 @a_i1v3O @b_i1v3P (a_a22eE :: a_i1v3O) (a_a22eF :: Dual b_i1v3P) :: Dual a_i1v3O where
  TFHelper_6989586621679495042 @a_i1v3O @b_i1v3P _z_6989586621679494824_a22eJ ('Dual a_6989586621679494828_a22eK) = Apply DualSym0 (Apply (LamCases_6989586621679495051Sym0 _z_6989586621679494824_a22eJ a_6989586621679494828_a22eK) a_6989586621679494828_a22eK)
instance PFunctor Dual where
  type Fmap a_a22ep a_a22eq = Fmap_6989586621679495031 a_a22ep a_a22eq
  type (<$) a_a22eA a_a22eB = TFHelper_6989586621679495042 a_a22eA a_a22eB
type TFHelper_6989586621679495132 :: forall a_i1v3Y
                                            b_i1v3Z. Dual a_i1v3Y
                                                      -> (~>) a_i1v3Y (Dual b_i1v3Z)
                                                        -> Dual b_i1v3Z
type family TFHelper_6989586621679495132 @a_i1v3Y @b_i1v3Z (a_a22g6 :: Dual a_i1v3Y) (a_a22g7 :: (~>) a_i1v3Y (Dual b_i1v3Z)) :: Dual b_i1v3Z where
  TFHelper_6989586621679495132 @a_i1v3Y @b_i1v3Z ('Dual a_a22gb) k_a22gc = Apply k_a22gc a_a22gb
instance PMonad Dual where
  type (>>=) a_a22g2 a_a22g3 = TFHelper_6989586621679495132 a_a22g2 a_a22g3
type TFHelper_6989586621679495156 :: forall a_a228U. Dual a_a228U
                                                      -> Dual a_a228U -> Dual a_a228U
type family TFHelper_6989586621679495156 @a_a228U (a_a22gu :: Dual a_a228U) (a_a22gv :: Dual a_a228U) :: Dual a_a228U where
  TFHelper_6989586621679495156 @a_a228U ('Dual a_a22gz :: Dual a_a228U) ('Dual b_a22gA :: Dual a_a228U) = Apply DualSym0 (Apply (Apply (<>@#@$) b_a22gA) a_a22gz)
instance PSemigroup (Dual a_a228U) where
  type (<>) a_a22gq a_a22gr = TFHelper_6989586621679495156 a_a22gq a_a22gr
type TFHelper_6989586621679495167 :: All -> All -> All
type family TFHelper_6989586621679495167 (a_a22gF :: All) (a_a22gG :: All) :: All where
  TFHelper_6989586621679495167 ('All a_a22gK) ('All b_a22gL) = Apply AllSym0 (Apply (Apply (&&@#@$) a_a22gK) b_a22gL)
instance PSemigroup All where
  type (<>) a_a22gB a_a22gC = TFHelper_6989586621679495167 a_a22gB a_a22gC
type TFHelper_6989586621679495178 :: Any -> Any -> Any
type family TFHelper_6989586621679495178 (a_a22gQ :: Any) (a_a22gR :: Any) :: Any where
  TFHelper_6989586621679495178 ('Any a_a22gV) ('Any b_a22gW) = Apply AnySym0 (Apply (Apply (||@#@$) a_a22gV) b_a22gW)
instance PSemigroup Any where
  type (<>) a_a22gM a_a22gN = TFHelper_6989586621679495178 a_a22gM a_a22gN
type Pure_6989586621679495188 :: forall a_i1v3p. a_i1v3p
                                                  -> Sum a_i1v3p
type family Pure_6989586621679495188 @a_i1v3p (a_a22h2 :: a_i1v3p) :: Sum a_i1v3p where
  Pure_6989586621679495188 @a_i1v3p a_6989586621679495190_a22h5 = Apply SumSym0 a_6989586621679495190_a22h5
type TFHelper_6989586621679495198 :: forall a_i1v3r
                                            b_i1v3s. Sum ((~>) a_i1v3r b_i1v3s)
                                                      -> Sum a_i1v3r -> Sum b_i1v3s
type family TFHelper_6989586621679495198 @a_i1v3r @b_i1v3s (a_a22ha :: Sum ((~>) a_i1v3r b_i1v3s)) (a_a22hb :: Sum a_i1v3r) :: Sum b_i1v3s where
  TFHelper_6989586621679495198 @a_i1v3r @b_i1v3s ('Sum f_a22hf) ('Sum x_a22hg) = Apply SumSym0 (Apply f_a22hf x_a22hg)
instance PApplicative Sum where
  type Pure a_a22gX = Pure_6989586621679495188 a_a22gX
  type (<*>) a_a22h6 a_a22h7 = TFHelper_6989586621679495198 a_a22h6 a_a22h7
type Fmap_6989586621679495209 :: forall a_i1v3K
                                        b_i1v3L. (~>) a_i1v3K b_i1v3L
                                                  -> Sum a_i1v3K -> Sum b_i1v3L
type family Fmap_6989586621679495209 @a_i1v3K @b_i1v3L (a_a22hl :: (~>) a_i1v3K b_i1v3L) (a_a22hm :: Sum a_i1v3K) :: Sum b_i1v3L where
  Fmap_6989586621679495209 @a_i1v3K @b_i1v3L _f_6989586621679494831_a22hq ('Sum a_6989586621679494835_a22hr) = Apply SumSym0 (Apply _f_6989586621679494831_a22hq a_6989586621679494835_a22hr)
type family LamCases_6989586621679495229_a22hE (_z_69895866216794948336989586621679495227 :: a7566047373982791008) a_69895866216794948376989586621679495228 a_6989586621679495231_a22hG where
  LamCases_6989586621679495229_a22hE _z_6989586621679494833_a22hB a_6989586621679494837_a22hC _ = _z_6989586621679494833_a22hB
data LamCases_6989586621679495229Sym0 (_z_69895866216794948336989586621679495227 :: a7566047373982791008) a_69895866216794948376989586621679495228 a_69895866216794952316989586621679495232
  where
    LamCases_6989586621679495229Sym0KindInference :: SameKind (Apply (LamCases_6989586621679495229Sym0 _z_69895866216794948336989586621679495227 a_69895866216794948376989586621679495228) arg_a22hH) (LamCases_6989586621679495229Sym1 _z_69895866216794948336989586621679495227 a_69895866216794948376989586621679495228 arg_a22hH) =>
                                                      LamCases_6989586621679495229Sym0 _z_69895866216794948336989586621679495227 a_69895866216794948376989586621679495228 a_69895866216794952316989586621679495232
type instance Apply @_ @_ (LamCases_6989586621679495229Sym0 _z_69895866216794948336989586621679495227 a_69895866216794948376989586621679495228) a_69895866216794952316989586621679495232 = LamCases_6989586621679495229_a22hE _z_69895866216794948336989586621679495227 a_69895866216794948376989586621679495228 a_69895866216794952316989586621679495232
instance SuppressUnusedWarnings (LamCases_6989586621679495229Sym0 _z_69895866216794948336989586621679495227 a_69895866216794948376989586621679495228) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679495229Sym0KindInference ())
type family LamCases_6989586621679495229Sym1 (_z_69895866216794948336989586621679495227 :: a7566047373982791008) a_69895866216794948376989586621679495228 a_69895866216794952316989586621679495232 where
  LamCases_6989586621679495229Sym1 _z_69895866216794948336989586621679495227 a_69895866216794948376989586621679495228 a_69895866216794952316989586621679495232 = LamCases_6989586621679495229_a22hE _z_69895866216794948336989586621679495227 a_69895866216794948376989586621679495228 a_69895866216794952316989586621679495232
type TFHelper_6989586621679495220 :: forall a_i1v3O
                                            b_i1v3P. a_i1v3O -> Sum b_i1v3P -> Sum a_i1v3O
type family TFHelper_6989586621679495220 @a_i1v3O @b_i1v3P (a_a22hw :: a_i1v3O) (a_a22hx :: Sum b_i1v3P) :: Sum a_i1v3O where
  TFHelper_6989586621679495220 @a_i1v3O @b_i1v3P _z_6989586621679494833_a22hB ('Sum a_6989586621679494837_a22hC) = Apply SumSym0 (Apply (LamCases_6989586621679495229Sym0 _z_6989586621679494833_a22hB a_6989586621679494837_a22hC) a_6989586621679494837_a22hC)
instance PFunctor Sum where
  type Fmap a_a22hh a_a22hi = Fmap_6989586621679495209 a_a22hh a_a22hi
  type (<$) a_a22hs a_a22ht = TFHelper_6989586621679495220 a_a22hs a_a22ht
type TFHelper_6989586621679495236 :: forall a_i1v3Y
                                            b_i1v3Z. Sum a_i1v3Y
                                                      -> (~>) a_i1v3Y (Sum b_i1v3Z)
                                                        -> Sum b_i1v3Z
type family TFHelper_6989586621679495236 @a_i1v3Y @b_i1v3Z (a_a22hM :: Sum a_i1v3Y) (a_a22hN :: (~>) a_i1v3Y (Sum b_i1v3Z)) :: Sum b_i1v3Z where
  TFHelper_6989586621679495236 @a_i1v3Y @b_i1v3Z ('Sum a_a22hR) k_a22hS = Apply k_a22hS a_a22hR
instance PMonad Sum where
  type (>>=) a_a22hI a_a22hJ = TFHelper_6989586621679495236 a_a22hI a_a22hJ
type TFHelper_6989586621679495247 :: forall a_a2295. Sum a_a2295
                                                      -> Sum a_a2295 -> Sum a_a2295
type family TFHelper_6989586621679495247 @a_a2295 (a_a22hX :: Sum a_a2295) (a_a22hY :: Sum a_a2295) :: Sum a_a2295 where
  TFHelper_6989586621679495247 @a_a2295 ('Sum a_a22i2 :: Sum a_a2295) ('Sum b_a22i3 :: Sum a_a2295) = Apply SumSym0 (Apply (Apply (+@#@$) a_a22i2) b_a22i3)
instance PSemigroup (Sum a_a2295) where
  type (<>) a_a22hT a_a22hU = TFHelper_6989586621679495247 a_a22hT a_a22hU
type TFHelper_6989586621679495305 :: forall a_a2298. Sum a_a2298
                                                      -> Sum a_a2298 -> Sum a_a2298
type family TFHelper_6989586621679495305 @a_a2298 (a_a22iT :: Sum a_a2298) (a_a22iU :: Sum a_a2298) :: Sum a_a2298 where
  TFHelper_6989586621679495305 @a_a2298 ('Sum a_a22iY :: Sum a_a2298) ('Sum b_a22iZ :: Sum a_a2298) = Apply SumSym0 (Apply (Apply (+@#@$) a_a22iY) b_a22iZ)
type TFHelper_6989586621679495316 :: forall a_a2298. Sum a_a2298
                                                      -> Sum a_a2298 -> Sum a_a2298
type family TFHelper_6989586621679495316 @a_a2298 (a_a22j4 :: Sum a_a2298) (a_a22j5 :: Sum a_a2298) :: Sum a_a2298 where
  TFHelper_6989586621679495316 @a_a2298 ('Sum a_a22j9 :: Sum a_a2298) ('Sum b_a22ja :: Sum a_a2298) = Apply SumSym0 (Apply (Apply (-@#@$) a_a22j9) b_a22ja)
type TFHelper_6989586621679495327 :: forall a_a2298. Sum a_a2298
                                                      -> Sum a_a2298 -> Sum a_a2298
type family TFHelper_6989586621679495327 @a_a2298 (a_a22jf :: Sum a_a2298) (a_a22jg :: Sum a_a2298) :: Sum a_a2298 where
  TFHelper_6989586621679495327 @a_a2298 ('Sum a_a22jk :: Sum a_a2298) ('Sum b_a22jl :: Sum a_a2298) = Apply SumSym0 (Apply (Apply (*@#@$) a_a22jk) b_a22jl)
type Negate_6989586621679495337 :: forall a_a2298. Sum a_a2298
                                                    -> Sum a_a2298
type family Negate_6989586621679495337 @a_a2298 (a_a22jp :: Sum a_a2298) :: Sum a_a2298 where
  Negate_6989586621679495337 @a_a2298 ('Sum a_a22js :: Sum a_a2298) = Apply SumSym0 (Apply NegateSym0 a_a22js)
type Abs_6989586621679495344 :: forall a_a2298. Sum a_a2298
                                                -> Sum a_a2298
type family Abs_6989586621679495344 @a_a2298 (a_a22jw :: Sum a_a2298) :: Sum a_a2298 where
  Abs_6989586621679495344 @a_a2298 ('Sum a_a22jz :: Sum a_a2298) = Apply SumSym0 (Apply AbsSym0 a_a22jz)
type Signum_6989586621679495351 :: forall a_a2298. Sum a_a2298
                                                    -> Sum a_a2298
type family Signum_6989586621679495351 @a_a2298 (a_a22jD :: Sum a_a2298) :: Sum a_a2298 where
  Signum_6989586621679495351 @a_a2298 ('Sum a_a22jG :: Sum a_a2298) = Apply SumSym0 (Apply SignumSym0 a_a22jG)
type FromInteger_6989586621679495358 :: forall a_a2298. GHC.Num.Natural.Natural
                                                        -> Sum a_a2298
type family FromInteger_6989586621679495358 @a_a2298 (a_a22jK :: GHC.Num.Natural.Natural) :: Sum a_a2298 where
  FromInteger_6989586621679495358 @a_a2298 (n_a22jN :: GHC.Num.Natural.Natural) = Apply SumSym0 (Apply FromIntegerSym0 n_a22jN)
instance PNum (Sum a_a2298) where
  type (+) a_a22iP a_a22iQ = TFHelper_6989586621679495305 a_a22iP a_a22iQ
  type (-) a_a22j0 a_a22j1 = TFHelper_6989586621679495316 a_a22j0 a_a22j1
  type (*) a_a22jb a_a22jc = TFHelper_6989586621679495327 a_a22jb a_a22jc
  type Negate a_a22jm = Negate_6989586621679495337 a_a22jm
  type Abs a_a22jt = Abs_6989586621679495344 a_a22jt
  type Signum a_a22jA = Signum_6989586621679495351 a_a22jA
  type FromInteger a_a22jH = FromInteger_6989586621679495358 a_a22jH
type Pure_6989586621679495365 :: forall a_i1v3p. a_i1v3p
                                                  -> Product a_i1v3p
type family Pure_6989586621679495365 @a_i1v3p (a_a22jT :: a_i1v3p) :: Product a_i1v3p where
  Pure_6989586621679495365 @a_i1v3p a_6989586621679495367_a22jW = Apply ProductSym0 a_6989586621679495367_a22jW
type TFHelper_6989586621679495375 :: forall a_i1v3r
                                            b_i1v3s. Product ((~>) a_i1v3r b_i1v3s)
                                                      -> Product a_i1v3r -> Product b_i1v3s
type family TFHelper_6989586621679495375 @a_i1v3r @b_i1v3s (a_a22k1 :: Product ((~>) a_i1v3r b_i1v3s)) (a_a22k2 :: Product a_i1v3r) :: Product b_i1v3s where
  TFHelper_6989586621679495375 @a_i1v3r @b_i1v3s ('Product f_a22k6) ('Product x_a22k7) = Apply ProductSym0 (Apply f_a22k6 x_a22k7)
instance PApplicative Product where
  type Pure a_a22jO = Pure_6989586621679495365 a_a22jO
  type (<*>) a_a22jX a_a22jY = TFHelper_6989586621679495375 a_a22jX a_a22jY
type Fmap_6989586621679495386 :: forall a_i1v3K
                                        b_i1v3L. (~>) a_i1v3K b_i1v3L
                                                  -> Product a_i1v3K -> Product b_i1v3L
type family Fmap_6989586621679495386 @a_i1v3K @b_i1v3L (a_a22kc :: (~>) a_i1v3K b_i1v3L) (a_a22kd :: Product a_i1v3K) :: Product b_i1v3L where
  Fmap_6989586621679495386 @a_i1v3K @b_i1v3L _f_6989586621679494840_a22kh ('Product a_6989586621679494844_a22ki) = Apply ProductSym0 (Apply _f_6989586621679494840_a22kh a_6989586621679494844_a22ki)
type family LamCases_6989586621679495406_a22kv (_z_69895866216794948426989586621679495404 :: a7566047373982791008) a_69895866216794948466989586621679495405 a_6989586621679495408_a22kx where
  LamCases_6989586621679495406_a22kv _z_6989586621679494842_a22ks a_6989586621679494846_a22kt _ = _z_6989586621679494842_a22ks
data LamCases_6989586621679495406Sym0 (_z_69895866216794948426989586621679495404 :: a7566047373982791008) a_69895866216794948466989586621679495405 a_69895866216794954086989586621679495409
  where
    LamCases_6989586621679495406Sym0KindInference :: SameKind (Apply (LamCases_6989586621679495406Sym0 _z_69895866216794948426989586621679495404 a_69895866216794948466989586621679495405) arg_a22ky) (LamCases_6989586621679495406Sym1 _z_69895866216794948426989586621679495404 a_69895866216794948466989586621679495405 arg_a22ky) =>
                                                      LamCases_6989586621679495406Sym0 _z_69895866216794948426989586621679495404 a_69895866216794948466989586621679495405 a_69895866216794954086989586621679495409
type instance Apply @_ @_ (LamCases_6989586621679495406Sym0 _z_69895866216794948426989586621679495404 a_69895866216794948466989586621679495405) a_69895866216794954086989586621679495409 = LamCases_6989586621679495406_a22kv _z_69895866216794948426989586621679495404 a_69895866216794948466989586621679495405 a_69895866216794954086989586621679495409
instance SuppressUnusedWarnings (LamCases_6989586621679495406Sym0 _z_69895866216794948426989586621679495404 a_69895866216794948466989586621679495405) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679495406Sym0KindInference ())
type family LamCases_6989586621679495406Sym1 (_z_69895866216794948426989586621679495404 :: a7566047373982791008) a_69895866216794948466989586621679495405 a_69895866216794954086989586621679495409 where
  LamCases_6989586621679495406Sym1 _z_69895866216794948426989586621679495404 a_69895866216794948466989586621679495405 a_69895866216794954086989586621679495409 = LamCases_6989586621679495406_a22kv _z_69895866216794948426989586621679495404 a_69895866216794948466989586621679495405 a_69895866216794954086989586621679495409
type TFHelper_6989586621679495397 :: forall a_i1v3O
                                            b_i1v3P. a_i1v3O
                                                      -> Product b_i1v3P -> Product a_i1v3O
type family TFHelper_6989586621679495397 @a_i1v3O @b_i1v3P (a_a22kn :: a_i1v3O) (a_a22ko :: Product b_i1v3P) :: Product a_i1v3O where
  TFHelper_6989586621679495397 @a_i1v3O @b_i1v3P _z_6989586621679494842_a22ks ('Product a_6989586621679494846_a22kt) = Apply ProductSym0 (Apply (LamCases_6989586621679495406Sym0 _z_6989586621679494842_a22ks a_6989586621679494846_a22kt) a_6989586621679494846_a22kt)
instance PFunctor Product where
  type Fmap a_a22k8 a_a22k9 = Fmap_6989586621679495386 a_a22k8 a_a22k9
  type (<$) a_a22kj a_a22kk = TFHelper_6989586621679495397 a_a22kj a_a22kk
type TFHelper_6989586621679495413 :: forall a_i1v3Y
                                            b_i1v3Z. Product a_i1v3Y
                                                      -> (~>) a_i1v3Y (Product b_i1v3Z)
                                                        -> Product b_i1v3Z
type family TFHelper_6989586621679495413 @a_i1v3Y @b_i1v3Z (a_a22kD :: Product a_i1v3Y) (a_a22kE :: (~>) a_i1v3Y (Product b_i1v3Z)) :: Product b_i1v3Z where
  TFHelper_6989586621679495413 @a_i1v3Y @b_i1v3Z ('Product a_a22kI) k_a22kJ = Apply k_a22kJ a_a22kI
instance PMonad Product where
  type (>>=) a_a22kz a_a22kA = TFHelper_6989586621679495413 a_a22kz a_a22kA
type TFHelper_6989586621679495424 :: forall a_a229n. Product a_a229n
                                                      -> Product a_a229n -> Product a_a229n
type family TFHelper_6989586621679495424 @a_a229n (a_a22kO :: Product a_a229n) (a_a22kP :: Product a_a229n) :: Product a_a229n where
  TFHelper_6989586621679495424 @a_a229n ('Product a_a22kT :: Product a_a229n) ('Product b_a22kU :: Product a_a229n) = Apply ProductSym0 (Apply (Apply (*@#@$) a_a22kT) b_a22kU)
instance PSemigroup (Product a_a229n) where
  type (<>) a_a22kK a_a22kL = TFHelper_6989586621679495424 a_a22kK a_a22kL
type TFHelper_6989586621679495435 :: forall a_a229q. Product a_a229q
                                                      -> Product a_a229q -> Product a_a229q
type family TFHelper_6989586621679495435 @a_a229q (a_a22kZ :: Product a_a229q) (a_a22l0 :: Product a_a229q) :: Product a_a229q where
  TFHelper_6989586621679495435 @a_a229q ('Product a_a22l4 :: Product a_a229q) ('Product b_a22l5 :: Product a_a229q) = Apply ProductSym0 (Apply (Apply (+@#@$) a_a22l4) b_a22l5)
type TFHelper_6989586621679495446 :: forall a_a229q. Product a_a229q
                                                      -> Product a_a229q -> Product a_a229q
type family TFHelper_6989586621679495446 @a_a229q (a_a22la :: Product a_a229q) (a_a22lb :: Product a_a229q) :: Product a_a229q where
  TFHelper_6989586621679495446 @a_a229q ('Product a_a22lf :: Product a_a229q) ('Product b_a22lg :: Product a_a229q) = Apply ProductSym0 (Apply (Apply (-@#@$) a_a22lf) b_a22lg)
type TFHelper_6989586621679495457 :: forall a_a229q. Product a_a229q
                                                      -> Product a_a229q -> Product a_a229q
type family TFHelper_6989586621679495457 @a_a229q (a_a22ll :: Product a_a229q) (a_a22lm :: Product a_a229q) :: Product a_a229q where
  TFHelper_6989586621679495457 @a_a229q ('Product a_a22lq :: Product a_a229q) ('Product b_a22lr :: Product a_a229q) = Apply ProductSym0 (Apply (Apply (*@#@$) a_a22lq) b_a22lr)
type Negate_6989586621679495467 :: forall a_a229q. Product a_a229q
                                                    -> Product a_a229q
type family Negate_6989586621679495467 @a_a229q (a_a22lv :: Product a_a229q) :: Product a_a229q where
  Negate_6989586621679495467 @a_a229q ('Product a_a22ly :: Product a_a229q) = Apply ProductSym0 (Apply NegateSym0 a_a22ly)
type Abs_6989586621679495474 :: forall a_a229q. Product a_a229q
                                                -> Product a_a229q
type family Abs_6989586621679495474 @a_a229q (a_a22lC :: Product a_a229q) :: Product a_a229q where
  Abs_6989586621679495474 @a_a229q ('Product a_a22lF :: Product a_a229q) = Apply ProductSym0 (Apply AbsSym0 a_a22lF)
type Signum_6989586621679495481 :: forall a_a229q. Product a_a229q
                                                    -> Product a_a229q
type family Signum_6989586621679495481 @a_a229q (a_a22lJ :: Product a_a229q) :: Product a_a229q where
  Signum_6989586621679495481 @a_a229q ('Product a_a22lM :: Product a_a229q) = Apply ProductSym0 (Apply SignumSym0 a_a22lM)
type FromInteger_6989586621679495488 :: forall a_a229q. GHC.Num.Natural.Natural
                                                        -> Product a_a229q
type family FromInteger_6989586621679495488 @a_a229q (a_a22lQ :: GHC.Num.Natural.Natural) :: Product a_a229q where
  FromInteger_6989586621679495488 @a_a229q (n_a22lT :: GHC.Num.Natural.Natural) = Apply ProductSym0 (Apply FromIntegerSym0 n_a22lT)
instance PNum (Product a_a229q) where
  type (+) a_a22kV a_a22kW = TFHelper_6989586621679495435 a_a22kV a_a22kW
  type (-) a_a22l6 a_a22l7 = TFHelper_6989586621679495446 a_a22l6 a_a22l7
  type (*) a_a22lh a_a22li = TFHelper_6989586621679495457 a_a22lh a_a22li
  type Negate a_a22ls = Negate_6989586621679495467 a_a22ls
  type Abs a_a22lz = Abs_6989586621679495474 a_a22lz
  type Signum a_a22lG = Signum_6989586621679495481 a_a22lG
  type FromInteger a_a22lN = FromInteger_6989586621679495488 a_a22lN
instance SApplicative Dual where
  sPure (sA_6989586621679495012 :: Sing a_6989586621679495012_a22ed)
    = applySing (singFun1 @DualSym0 SDual) sA_6989586621679495012
  (%<*>) (SDual (sF :: Sing f_a22en)) (SDual (sX :: Sing x_a22eo))
    = applySing (singFun1 @DualSym0 SDual) (applySing sF sX)
instance SFunctor Dual where
  sFmap
    (_sf_6989586621679494822 :: Sing _f_6989586621679494822_a22ey)
    (SDual (sA_6989586621679494826 :: Sing a_6989586621679494826_a22ez))
    = applySing
        (singFun1 @DualSym0 SDual)
        (applySing _sf_6989586621679494822 sA_6989586621679494826)
  (%<$)
    (_sz_6989586621679494824 :: Sing _z_6989586621679494824_a22eJ)
    (SDual (sA_6989586621679494828 :: Sing a_6989586621679494828_a22eK))
    = applySing
        (singFun1 @DualSym0 SDual)
        (applySing
            (singFun1
              @(LamCases_6989586621679495051Sym0 _z_6989586621679494824_a22eJ a_6989586621679494828_a22eK)
              (\cases _ -> _sz_6989586621679494824))
            sA_6989586621679494828)
instance SMonad Dual where
  (%>>=) (SDual (sA :: Sing a_a22gb)) (sK :: Sing k_a22gc)
    = applySing sK sA
instance SSemigroup a_a228U => SSemigroup (Dual a_a228U) where
  (%<>) (SDual (sA :: Sing a_a22gz)) (SDual (sB :: Sing b_a22gA))
    = applySing
        (singFun1 @DualSym0 SDual)
        (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sB) sA)
instance SSemigroup All where
  (%<>) (SAll (sA :: Sing a_a22gK)) (SAll (sB :: Sing b_a22gL))
    = applySing
        (singFun1 @AllSym0 SAll)
        (applySing (applySing (singFun2 @(&&@#@$) (%&&)) sA) sB)
instance SSemigroup Any where
  (%<>) (SAny (sA :: Sing a_a22gV)) (SAny (sB :: Sing b_a22gW))
    = applySing
        (singFun1 @AnySym0 SAny)
        (applySing (applySing (singFun2 @(||@#@$) (%||)) sA) sB)
instance SApplicative Sum where
  sPure (sA_6989586621679495190 :: Sing a_6989586621679495190_a22h5)
    = applySing (singFun1 @SumSym0 SSum) sA_6989586621679495190
  (%<*>) (SSum (sF :: Sing f_a22hf)) (SSum (sX :: Sing x_a22hg))
    = applySing (singFun1 @SumSym0 SSum) (applySing sF sX)
instance SFunctor Sum where
  sFmap
    (_sf_6989586621679494831 :: Sing _f_6989586621679494831_a22hq)
    (SSum (sA_6989586621679494835 :: Sing a_6989586621679494835_a22hr))
    = applySing
        (singFun1 @SumSym0 SSum)
        (applySing _sf_6989586621679494831 sA_6989586621679494835)
  (%<$)
    (_sz_6989586621679494833 :: Sing _z_6989586621679494833_a22hB)
    (SSum (sA_6989586621679494837 :: Sing a_6989586621679494837_a22hC))
    = applySing
        (singFun1 @SumSym0 SSum)
        (applySing
            (singFun1
              @(LamCases_6989586621679495229Sym0 _z_6989586621679494833_a22hB a_6989586621679494837_a22hC)
              (\cases _ -> _sz_6989586621679494833))
            sA_6989586621679494837)
instance SMonad Sum where
  (%>>=) (SSum (sA :: Sing a_a22hR)) (sK :: Sing k_a22hS)
    = applySing sK sA
instance SNum a_a2295 => SSemigroup (Sum a_a2295) where
  (%<>) (SSum (sA :: Sing a_a22i2)) (SSum (sB :: Sing b_a22i3))
    = applySing
        (singFun1 @SumSym0 SSum)
        (applySing (applySing (singFun2 @(+@#@$) (%+)) sA) sB)
instance SNum a_a2298 => SNum (Sum a_a2298) where
  (%+) (SSum (sA :: Sing a_a22iY)) (SSum (sB :: Sing b_a22iZ))
    = applySing
        (singFun1 @SumSym0 SSum)
        (applySing (applySing (singFun2 @(+@#@$) (%+)) sA) sB)
  (%-) (SSum (sA :: Sing a_a22j9)) (SSum (sB :: Sing b_a22ja))
    = applySing
        (singFun1 @SumSym0 SSum)
        (applySing (applySing (singFun2 @(-@#@$) (%-)) sA) sB)
  (%*) (SSum (sA :: Sing a_a22jk)) (SSum (sB :: Sing b_a22jl))
    = applySing
        (singFun1 @SumSym0 SSum)
        (applySing (applySing (singFun2 @(*@#@$) (%*)) sA) sB)
  sNegate (SSum (sA :: Sing a_a22js))
    = applySing
        (singFun1 @SumSym0 SSum)
        (applySing (singFun1 @NegateSym0 sNegate) sA)
  sAbs (SSum (sA :: Sing a_a22jz))
    = applySing
        (singFun1 @SumSym0 SSum) (applySing (singFun1 @AbsSym0 sAbs) sA)
  sSignum (SSum (sA :: Sing a_a22jG))
    = applySing
        (singFun1 @SumSym0 SSum)
        (applySing (singFun1 @SignumSym0 sSignum) sA)
  sFromInteger (sN :: Sing n_a22jN)
    = applySing
        (singFun1 @SumSym0 SSum)
        (applySing (singFun1 @FromIntegerSym0 sFromInteger) sN)
instance SApplicative Product where
  sPure (sA_6989586621679495367 :: Sing a_6989586621679495367_a22jW)
    = applySing (singFun1 @ProductSym0 SProduct) sA_6989586621679495367
  (%<*>)
    (SProduct (sF :: Sing f_a22k6))
    (SProduct (sX :: Sing x_a22k7))
    = applySing (singFun1 @ProductSym0 SProduct) (applySing sF sX)
instance SFunctor Product where
  sFmap
    (_sf_6989586621679494840 :: Sing _f_6989586621679494840_a22kh)
    (SProduct (sA_6989586621679494844 :: Sing a_6989586621679494844_a22ki))
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing _sf_6989586621679494840 sA_6989586621679494844)
  (%<$)
    (_sz_6989586621679494842 :: Sing _z_6989586621679494842_a22ks)
    (SProduct (sA_6989586621679494846 :: Sing a_6989586621679494846_a22kt))
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing
            (singFun1
              @(LamCases_6989586621679495406Sym0 _z_6989586621679494842_a22ks a_6989586621679494846_a22kt)
              (\cases _ -> _sz_6989586621679494842))
            sA_6989586621679494846)
instance SMonad Product where
  (%>>=) (SProduct (sA :: Sing a_a22kI)) (sK :: Sing k_a22kJ)
    = applySing sK sA
instance SNum a_a229n => SSemigroup (Product a_a229n) where
  (%<>)
    (SProduct (sA :: Sing a_a22kT))
    (SProduct (sB :: Sing b_a22kU))
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing (applySing (singFun2 @(*@#@$) (%*)) sA) sB)
instance SNum a_a229q => SNum (Product a_a229q) where
  (%+)
    (SProduct (sA :: Sing a_a22l4))
    (SProduct (sB :: Sing b_a22l5))
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing (applySing (singFun2 @(+@#@$) (%+)) sA) sB)
  (%-)
    (SProduct (sA :: Sing a_a22lf))
    (SProduct (sB :: Sing b_a22lg))
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing (applySing (singFun2 @(-@#@$) (%-)) sA) sB)
  (%*)
    (SProduct (sA :: Sing a_a22lq))
    (SProduct (sB :: Sing b_a22lr))
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing (applySing (singFun2 @(*@#@$) (%*)) sA) sB)
  sNegate (SProduct (sA :: Sing a_a22ly))
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing (singFun1 @NegateSym0 sNegate) sA)
  sAbs (SProduct (sA :: Sing a_a22lF))
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing (singFun1 @AbsSym0 sAbs) sA)
  sSignum (SProduct (sA :: Sing a_a22lM))
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing (singFun1 @SignumSym0 sSignum) sA)
  sFromInteger (sN :: Sing n_a22lT)
    = applySing
        (singFun1 @ProductSym0 SProduct)
        (applySing (singFun1 @FromIntegerSym0 sFromInteger) sN)
