{-# LANGUAGE DataKinds #-}
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
-- Module      :  Data.Semigroup.Singletons
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted version of 'Semigroup', 'PSemigroup', and the
-- singleton version, 'SSemigroup'.
--
----------------------------------------------------------------------------

module Data.Semigroup.Singletons (
  PSemigroup(..), SSemigroup(..),

  Sing, SMin(..), SMax(..), SFirst(..), SLast(..),
  SWrappedMonoid(..), SDual(..), SAll(..), SAny(..),
  SSum(..), SProduct(..), SArg(..),
  GetMin, GetMax, GetFirst, GetLast, UnwrapMonoid, GetDual,
  GetAll, GetAny, GetSum, GetProduct,
  sGetMin, sGetMax, sGetFirst, sGetLast, sUnwrapMonoid, sGetDual,
  sGetAll, sGetAny, sGetSum, sGetProduct,

  -- ** Defunctionalization symbols
  type (<>@#@$), type (<>@#@$$), type (<>@#@$$$),
  SconcatSym0, SconcatSym1,
  MinSym0, MinSym1, GetMinSym0, GetMinSym1,
  MaxSym0, MaxSym1, GetMaxSym0, GetMaxSym1,
  FirstSym0, FirstSym1, GetFirstSym0, GetFirstSym1,
  LastSym0, LastSym1, GetLastSym0, GetLastSym1,
  WrapMonoidSym0, WrapMonoidSym1, UnwrapMonoidSym0, UnwrapMonoidSym1,
  DualSym0, DualSym1, GetDualSym0, GetDualSym1,
  AllSym0, AllSym1, GetAllSym0, GetAllSym1,
  AnySym0, AnySym1, GetAnySym0, GetAnySym1,
  SumSym0, SumSym1, GetSumSym0, GetSumSym1,
  ProductSym0, ProductSym1, GetProductSym0, GetProductSym1,
  ArgSym0, ArgSym1, ArgSym2
  ) where

import Control.Monad.Singletons.Internal
import Data.Eq.Singletons
import Data.Foldable.Singletons hiding
       ( All,     AllSym0,     AllSym1
       , Any,     AnySym0,     AnySym1
       , Product, ProductSym0, ProductSym1
       , Sum,     SumSym0,     SumSym1 )
import Data.Monoid.Singletons hiding
       (SFirst(..), SLast(..),
        FirstSym0, FirstSym1, LastSym0, LastSym1,
        GetFirst, sGetFirst, GetFirstSym0, GetFirstSym1,
        GetLast,  sGetLast,  GetLastSym0,  GetLastSym1)
import Data.Ord.Singletons hiding
       (MinSym0, MinSym1, MaxSym0, MaxSym1)
import Data.Ord.Singletons.Disambiguation
import qualified Data.Semigroup as Semi (Min(..), Max(..))
import Data.Semigroup (First(..), Last(..), WrappedMonoid(..), Arg(..))
import Data.Semigroup.Singletons.Internal.Classes
import Data.Semigroup.Singletons.Internal.Wrappers
import Data.Singletons.Base.Enum
import Data.Singletons.Base.Instances

import Data.Singletons.TH
import Data.Traversable.Singletons
import GHC.Base.Singletons hiding
       (Foldr, FoldrSym0, FoldrSym1, FoldrSym2, FoldrSym3, sFoldr)
import GHC.Num.Singletons
import Text.Show.Singletons
import Data.Kind (Type)
import qualified Data.Semigroup
import qualified Data.Singletons.ShowSing
import qualified Data.Type.Equality
import qualified Data.Singletons.Decide
import qualified Data.Type.Coercion
import qualified GHC.Num.Natural
import qualified Data.Semigroup
import qualified GHC.Exts

type ArgSym0 :: forall (a_i8wW :: Type)
                           (b_i8wX :: Type). (~>) a_i8wW ((~>) b_i8wX (Arg a_i8wW b_i8wX))
data ArgSym0 :: (~>) a_i8wW ((~>) b_i8wX (Arg a_i8wW b_i8wX))
  where
    ArgSym0KindInference :: SameKind (Apply ArgSym0 arg_a1pNU) (ArgSym1 arg_a1pNU) =>
                            ArgSym0 a6989586621679347315
type instance Apply @a_i8wW @((~>) b_i8wX (Arg a_i8wW b_i8wX)) ArgSym0 a6989586621679347315 = ArgSym1 a6989586621679347315
instance SuppressUnusedWarnings ArgSym0 where
  suppressUnusedWarnings = snd ((,) ArgSym0KindInference ())
type ArgSym1 :: forall (a_i8wW :: Type) (b_i8wX :: Type). a_i8wW
                                                          -> (~>) b_i8wX (Arg a_i8wW b_i8wX)
data ArgSym1 (a6989586621679347315 :: a_i8wW) :: (~>) b_i8wX (Arg a_i8wW b_i8wX)
  where
    ArgSym1KindInference :: SameKind (Apply (ArgSym1 a6989586621679347315) arg_a1pNU) (ArgSym2 a6989586621679347315 arg_a1pNU) =>
                            ArgSym1 a6989586621679347315 a6989586621679347316
type instance Apply @b_i8wX @(Arg a_i8wW b_i8wX) (ArgSym1 a6989586621679347315) a6989586621679347316 = 'Arg a6989586621679347315 a6989586621679347316
instance SuppressUnusedWarnings (ArgSym1 a6989586621679347315) where
  suppressUnusedWarnings = snd ((,) ArgSym1KindInference ())
type ArgSym2 :: forall (a_i8wW :: Type) (b_i8wX :: Type). a_i8wW
                                                          -> b_i8wX -> Arg a_i8wW b_i8wX
type family ArgSym2 @(a_i8wW :: Type) @(b_i8wX :: Type) (a6989586621679347315 :: a_i8wW) (a6989586621679347316 :: b_i8wX) :: Arg a_i8wW b_i8wX where
  ArgSym2 a6989586621679347315 a6989586621679347316 = 'Arg a6989586621679347315 a6989586621679347316
type SArg :: forall (a_i8wW :: Type)
                    (b_i8wX :: Type). Arg a_i8wW b_i8wX -> Type
data SArg :: forall (a_i8wW :: Type) (b_i8wX :: Type).
              Arg a_i8wW b_i8wX -> Type
  where
    SArg :: forall (a_i8wW :: Type)
                    (b_i8wX :: Type)
                    (n_a1pNX :: a_i8wW)
                    (n_a1pNY :: b_i8wX).
            (Sing n_a1pNX) ->
            (Sing n_a1pNY) ->
            SArg ('Arg n_a1pNX n_a1pNY :: Arg a_i8wW b_i8wX)
type instance Sing @(Arg a_i8wW b_i8wX) = SArg
instance (SingKind a_i8wW, SingKind b_i8wX) =>
          SingKind (Arg a_i8wW b_i8wX) where
  type Demote (Arg a_i8wW b_i8wX) = Arg (Demote a_i8wW) (Demote b_i8wX)
  fromSing (SArg b_a1pO2 b_a1pO3)
    = Arg (fromSing b_a1pO2) (fromSing b_a1pO3)
  toSing (Arg (b_a1pO5 :: Demote a_i8wW) (b_a1pO6 :: Demote b_i8wX))
    = (\cases
          (SomeSing c_a1pO7) (SomeSing c_a1pO8)
            -> SomeSing (SArg c_a1pO7 c_a1pO8))
        (toSing b_a1pO5 :: SomeSing a_i8wW)
        (toSing b_a1pO6 :: SomeSing b_i8wX)
instance (SingI n_a1pNX, SingI n_a1pNY) =>
          SingI ('Arg (n_a1pNX :: a_i8wW) (n_a1pNY :: b_i8wX)) where
  sing = SArg sing sing
instance SingI n_a1pNX => SingI1 ('Arg (n_a1pNX :: a_i8wW)) where
  liftSing = SArg sing
instance SingI2 'Arg where
  liftSing2 = SArg
instance SingI (ArgSym0 :: (~>) a_i8wW ((~>) b_i8wX (Arg a_i8wW b_i8wX))) where
  sing = singFun2 @ArgSym0 SArg
instance SingI d_a1pNZ =>
          SingI (ArgSym1 (d_a1pNZ :: a_i8wW) :: (~>) b_i8wX (Arg a_i8wW b_i8wX)) where
  sing
    = singFun1 @(ArgSym1 (d_a1pNZ :: a_i8wW)) (SArg (sing @d_a1pNZ))
instance SingI1 (ArgSym1 :: a_i8wW
                            -> (~>) b_i8wX (Arg a_i8wW b_i8wX)) where
  liftSing (s_a1pO1 :: Sing (d_a1pNZ :: a_i8wW))
    = singFun1 @(ArgSym1 (d_a1pNZ :: a_i8wW)) (SArg s_a1pO1)

deriving instance Data.Singletons.ShowSing.ShowSing a_i8xF =>
                      Show (SDual (z_a1q9z :: Data.Semigroup.Dual a_i8xF))
deriving instance Data.Singletons.ShowSing.ShowSing Bool =>
                  Show (SAll (z_a1q9C :: Data.Semigroup.All))
deriving instance Data.Singletons.ShowSing.ShowSing Bool =>
                  Show (SAny (z_a1q9D :: Data.Semigroup.Any))
deriving instance Data.Singletons.ShowSing.ShowSing a_i8xP =>
                  Show (SSum (z_a1q9F :: Data.Semigroup.Sum a_i8xP))
deriving instance Data.Singletons.ShowSing.ShowSing a_i8xK =>
                  Show (SProduct (z_a1q9J :: Data.Semigroup.Product a_i8xK))
deriving instance Data.Singletons.ShowSing.ShowSing a_i8xi =>
                  Show (SMin (z_a1q9N :: Semi.Min a_i8xi))
deriving instance Data.Singletons.ShowSing.ShowSing a_i8xd =>
                  Show (SMax (z_a1q9R :: Semi.Max a_i8xd))
deriving instance Data.Singletons.ShowSing.ShowSing a_i8x3 =>
                  Show (SFirst (z_a1q9V :: First a_i8x3))
deriving instance Data.Singletons.ShowSing.ShowSing a_i8x8 =>
                  Show (SLast (z_a1q9Z :: Last a_i8x8))
deriving instance Data.Singletons.ShowSing.ShowSing m_i8xn =>
                  Show (SWrappedMonoid (z_a1qa3 :: WrappedMonoid m_i8xn))

type ShowsPrec_6989586621679349594 :: forall a_i8xF. GHC.Num.Natural.Natural
                                                         -> Data.Semigroup.Dual a_i8xF
                                                            -> GHC.Exts.Symbol
                                                               -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349594 @a_i8xF (a_a1qoK :: GHC.Num.Natural.Natural) (a_a1qoL :: Data.Semigroup.Dual a_i8xF) (a_a1qoM :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349594 @a_i8xF (p_6989586621679349552_a1qoR :: GHC.Num.Natural.Natural) ('Data.Semigroup.Dual arg_6989586621679349554_a1qoS :: Data.Semigroup.Dual a_i8xF) (a_6989586621679349596_a1qoT :: GHC.Exts.Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349552_a1qoR) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Dual ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getDual = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349554_a1qoS)) (Apply ShowCharSym0 '}')))))) a_6989586621679349596_a1qoT
instance PShow (Data.Semigroup.Dual a_i8xF) where
  type ShowsPrec a_a1qoD a_a1qoE a_a1qoF = ShowsPrec_6989586621679349594 a_a1qoD a_a1qoE a_a1qoF
instance SShow a_i8xF =>
          SShow (Data.Semigroup.Dual a_i8xF) where
  sShowsPrec
    (sP_6989586621679349552 :: Sing p_6989586621679349552_a1qoR)
    (SDual (sArg_6989586621679349554 :: Sing arg_6989586621679349554_a1qoS))
    (sA_6989586621679349596 :: Sing a_6989586621679349596_a1qoT)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349552)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Dual ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString)
                          (sing :: Sing "getDual = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679349554))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349596
type ShowsPrec_6989586621679349617 :: GHC.Num.Natural.Natural
                                      -> Data.Semigroup.All
                                          -> GHC.Exts.Symbol
                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349617 (a_a1qp7 :: GHC.Num.Natural.Natural) (a_a1qp8 :: Data.Semigroup.All) (a_a1qp9 :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349617 p_6989586621679349610_a1qpe ('Data.Semigroup.All arg_6989586621679349612_a1qpf) a_6989586621679349619_a1qpg = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349610_a1qpe) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "All ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getAll = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349612_a1qpf)) (Apply ShowCharSym0 '}')))))) a_6989586621679349619_a1qpg
instance PShow Data.Semigroup.All where
  type ShowsPrec a_a1qp0 a_a1qp1 a_a1qp2 = ShowsPrec_6989586621679349617 a_a1qp0 a_a1qp1 a_a1qp2
instance SShow Bool => SShow Data.Semigroup.All where
  sShowsPrec
    (sP_6989586621679349610 :: Sing p_6989586621679349610_a1qpe)
    (SAll (sArg_6989586621679349612 :: Sing arg_6989586621679349612_a1qpf))
    (sA_6989586621679349619 :: Sing a_6989586621679349619_a1qpg)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349610)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "All ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "getAll = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679349612))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349619
type ShowsPrec_6989586621679349638 :: GHC.Num.Natural.Natural
                                      -> Data.Semigroup.Any
                                          -> GHC.Exts.Symbol
                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349638 (a_a1qps :: GHC.Num.Natural.Natural) (a_a1qpt :: Data.Semigroup.Any) (a_a1qpu :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349638 p_6989586621679349631_a1qpz ('Data.Semigroup.Any arg_6989586621679349633_a1qpA) a_6989586621679349640_a1qpB = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349631_a1qpz) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Any ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getAny = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349633_a1qpA)) (Apply ShowCharSym0 '}')))))) a_6989586621679349640_a1qpB
instance PShow Data.Semigroup.Any where
  type ShowsPrec a_a1qpl a_a1qpm a_a1qpn = ShowsPrec_6989586621679349638 a_a1qpl a_a1qpm a_a1qpn
instance SShow Bool => SShow Data.Semigroup.Any where
  sShowsPrec
    (sP_6989586621679349631 :: Sing p_6989586621679349631_a1qpz)
    (SAny (sArg_6989586621679349633 :: Sing arg_6989586621679349633_a1qpA))
    (sA_6989586621679349640 :: Sing a_6989586621679349640_a1qpB)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349631)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Any ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "getAny = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679349633))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349640
type ShowsPrec_6989586621679349662 :: forall a_i8xP. GHC.Num.Natural.Natural
                                                      -> Data.Semigroup.Sum a_i8xP
                                                        -> GHC.Exts.Symbol
                                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349662 @a_i8xP (a_a1qpQ :: GHC.Num.Natural.Natural) (a_a1qpR :: Data.Semigroup.Sum a_i8xP) (a_a1qpS :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349662 @a_i8xP (p_6989586621679349653_a1qpX :: GHC.Num.Natural.Natural) ('Data.Semigroup.Sum arg_6989586621679349655_a1qpY :: Data.Semigroup.Sum a_i8xP) (a_6989586621679349664_a1qpZ :: GHC.Exts.Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349653_a1qpX) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Sum ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getSum = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349655_a1qpY)) (Apply ShowCharSym0 '}')))))) a_6989586621679349664_a1qpZ
instance PShow (Data.Semigroup.Sum a_i8xP) where
  type ShowsPrec a_a1qpJ a_a1qpK a_a1qpL = ShowsPrec_6989586621679349662 a_a1qpJ a_a1qpK a_a1qpL
instance SShow a_i8xP =>
          SShow (Data.Semigroup.Sum a_i8xP) where
  sShowsPrec
    (sP_6989586621679349653 :: Sing p_6989586621679349653_a1qpX)
    (SSum (sArg_6989586621679349655 :: Sing arg_6989586621679349655_a1qpY))
    (sA_6989586621679349664 :: Sing a_6989586621679349664_a1qpZ)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349653)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Sum ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "getSum = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679349655))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349664
type ShowsPrec_6989586621679349686 :: forall a_i8xK. GHC.Num.Natural.Natural
                                                      -> Data.Semigroup.Product a_i8xK
                                                        -> GHC.Exts.Symbol
                                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349686 @a_i8xK (a_a1qqe :: GHC.Num.Natural.Natural) (a_a1qqf :: Data.Semigroup.Product a_i8xK) (a_a1qqg :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349686 @a_i8xK (p_6989586621679349677_a1qql :: GHC.Num.Natural.Natural) ('Data.Semigroup.Product arg_6989586621679349679_a1qqm :: Data.Semigroup.Product a_i8xK) (a_6989586621679349688_a1qqn :: GHC.Exts.Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349677_a1qql) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Product ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getProduct = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349679_a1qqm)) (Apply ShowCharSym0 '}')))))) a_6989586621679349688_a1qqn
instance PShow (Data.Semigroup.Product a_i8xK) where
  type ShowsPrec a_a1qq7 a_a1qq8 a_a1qq9 = ShowsPrec_6989586621679349686 a_a1qq7 a_a1qq8 a_a1qq9
instance SShow a_i8xK =>
          SShow (Data.Semigroup.Product a_i8xK) where
  sShowsPrec
    (sP_6989586621679349677 :: Sing p_6989586621679349677_a1qql)
    (SProduct (sArg_6989586621679349679 :: Sing arg_6989586621679349679_a1qqm))
    (sA_6989586621679349688 :: Sing a_6989586621679349688_a1qqn)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349677)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Product ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString)
                          (sing :: Sing "getProduct = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679349679))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349688
type ShowsPrec_6989586621679349710 :: forall a_i8xi. GHC.Num.Natural.Natural
                                                      -> Semi.Min a_i8xi
                                                        -> GHC.Exts.Symbol
                                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349710 @a_i8xi (a_a1qqC :: GHC.Num.Natural.Natural) (a_a1qqD :: Semi.Min a_i8xi) (a_a1qqE :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349710 @a_i8xi (p_6989586621679349701_a1qqJ :: GHC.Num.Natural.Natural) ('Semi.Min arg_6989586621679349703_a1qqK :: Semi.Min a_i8xi) (a_6989586621679349712_a1qqL :: GHC.Exts.Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349701_a1qqJ) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Min ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getMin = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349703_a1qqK)) (Apply ShowCharSym0 '}')))))) a_6989586621679349712_a1qqL
instance PShow (Semi.Min a_i8xi) where
  type ShowsPrec a_a1qqv a_a1qqw a_a1qqx = ShowsPrec_6989586621679349710 a_a1qqv a_a1qqw a_a1qqx
instance SShow a_i8xi => SShow (Semi.Min a_i8xi) where
  sShowsPrec
    (sP_6989586621679349701 :: Sing p_6989586621679349701_a1qqJ)
    (SMin (sArg_6989586621679349703 :: Sing arg_6989586621679349703_a1qqK))
    (sA_6989586621679349712 :: Sing a_6989586621679349712_a1qqL)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349701)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Min ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "getMin = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679349703))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349712
type ShowsPrec_6989586621679349734 :: forall a_i8xd. GHC.Num.Natural.Natural
                                                      -> Semi.Max a_i8xd
                                                        -> GHC.Exts.Symbol
                                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349734 @a_i8xd (a_a1qr0 :: GHC.Num.Natural.Natural) (a_a1qr1 :: Semi.Max a_i8xd) (a_a1qr2 :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349734 @a_i8xd (p_6989586621679349725_a1qr7 :: GHC.Num.Natural.Natural) ('Semi.Max arg_6989586621679349727_a1qr8 :: Semi.Max a_i8xd) (a_6989586621679349736_a1qr9 :: GHC.Exts.Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349725_a1qr7) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Max ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getMax = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349727_a1qr8)) (Apply ShowCharSym0 '}')))))) a_6989586621679349736_a1qr9
instance PShow (Semi.Max a_i8xd) where
  type ShowsPrec a_a1qqT a_a1qqU a_a1qqV = ShowsPrec_6989586621679349734 a_a1qqT a_a1qqU a_a1qqV
instance SShow a_i8xd => SShow (Semi.Max a_i8xd) where
  sShowsPrec
    (sP_6989586621679349725 :: Sing p_6989586621679349725_a1qr7)
    (SMax (sArg_6989586621679349727 :: Sing arg_6989586621679349727_a1qr8))
    (sA_6989586621679349736 :: Sing a_6989586621679349736_a1qr9)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349725)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Max ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "getMax = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679349727))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349736
type ShowsPrec_6989586621679349758 :: forall a_i8x3. GHC.Num.Natural.Natural
                                                      -> First a_i8x3
                                                        -> GHC.Exts.Symbol
                                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349758 @a_i8x3 (a_a1qro :: GHC.Num.Natural.Natural) (a_a1qrp :: First a_i8x3) (a_a1qrq :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349758 @a_i8x3 (p_6989586621679349749_a1qrv :: GHC.Num.Natural.Natural) ('First arg_6989586621679349751_a1qrw :: First a_i8x3) (a_6989586621679349760_a1qrx :: GHC.Exts.Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349749_a1qrv) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "First ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getFirst = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349751_a1qrw)) (Apply ShowCharSym0 '}')))))) a_6989586621679349760_a1qrx
instance PShow (First a_i8x3) where
  type ShowsPrec a_a1qrh a_a1qri a_a1qrj = ShowsPrec_6989586621679349758 a_a1qrh a_a1qri a_a1qrj
instance SShow a_i8x3 => SShow (First a_i8x3) where
  sShowsPrec
    (sP_6989586621679349749 :: Sing p_6989586621679349749_a1qrv)
    (SFirst (sArg_6989586621679349751 :: Sing arg_6989586621679349751_a1qrw))
    (sA_6989586621679349760 :: Sing a_6989586621679349760_a1qrx)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349749)
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
                              sArg_6989586621679349751))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349760
type ShowsPrec_6989586621679349782 :: forall a_i8x8. GHC.Num.Natural.Natural
                                                      -> Last a_i8x8
                                                        -> GHC.Exts.Symbol
                                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349782 @a_i8x8 (a_a1qrM :: GHC.Num.Natural.Natural) (a_a1qrN :: Last a_i8x8) (a_a1qrO :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349782 @a_i8x8 (p_6989586621679349773_a1qrT :: GHC.Num.Natural.Natural) ('Last arg_6989586621679349775_a1qrU :: Last a_i8x8) (a_6989586621679349784_a1qrV :: GHC.Exts.Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349773_a1qrT) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Last ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "getLast = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349775_a1qrU)) (Apply ShowCharSym0 '}')))))) a_6989586621679349784_a1qrV
instance PShow (Last a_i8x8) where
  type ShowsPrec a_a1qrF a_a1qrG a_a1qrH = ShowsPrec_6989586621679349782 a_a1qrF a_a1qrG a_a1qrH
instance SShow a_i8x8 => SShow (Last a_i8x8) where
  sShowsPrec
    (sP_6989586621679349773 :: Sing p_6989586621679349773_a1qrT)
    (SLast (sArg_6989586621679349775 :: Sing arg_6989586621679349775_a1qrU))
    (sA_6989586621679349784 :: Sing a_6989586621679349784_a1qrV)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349773)
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
                              sArg_6989586621679349775))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349784
type ShowsPrec_6989586621679349806 :: forall m_i8xn. GHC.Num.Natural.Natural
                                                      -> WrappedMonoid m_i8xn
                                                        -> GHC.Exts.Symbol
                                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679349806 @m_i8xn (a_a1qsa :: GHC.Num.Natural.Natural) (a_a1qsb :: WrappedMonoid m_i8xn) (a_a1qsc :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679349806 @m_i8xn (p_6989586621679349797_a1qsh :: GHC.Num.Natural.Natural) ('WrapMonoid arg_6989586621679349799_a1qsi :: WrappedMonoid m_i8xn) (a_6989586621679349808_a1qsj :: GHC.Exts.Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679349797_a1qsh) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "WrapMonoid ")) (Apply (Apply (.@#@$) (Apply ShowCharSym0 '{')) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "unwrapMonoid = ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 0)) arg_6989586621679349799_a1qsi)) (Apply ShowCharSym0 '}')))))) a_6989586621679349808_a1qsj
instance PShow (WrappedMonoid m_i8xn) where
  type ShowsPrec a_a1qs3 a_a1qs4 a_a1qs5 = ShowsPrec_6989586621679349806 a_a1qs3 a_a1qs4 a_a1qs5
instance SShow m_i8xn => SShow (WrappedMonoid m_i8xn) where
  sShowsPrec
    (sP_6989586621679349797 :: Sing p_6989586621679349797_a1qsh)
    (SWrapMonoid (sArg_6989586621679349799 :: Sing arg_6989586621679349799_a1qsi))
    (sA_6989586621679349808 :: Sing a_6989586621679349808_a1qsj)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679349797)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString)
                    (sing :: Sing "WrapMonoid ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '{')))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.))
                        (applySing
                          (singFun2 @ShowStringSym0 sShowString)
                          (sing :: Sing "unwrapMonoid = ")))
                    (applySing
                        (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing
                              (applySing
                                (singFun3 @ShowsPrecSym0 sShowsPrec)
                                (sFromInteger (sing :: Sing 0)))
                              sArg_6989586621679349799))
                        (applySing
                          (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '}')))))))
        sA_6989586621679349808

instance Eq (SArg z) where
  _ == _ = True

instance Ord (SArg z) where
  compare _ _ = EQ

type Pure_6989586621679363176 :: forall a_iv9m. a_iv9m
                                                    -> Semi.Min a_iv9m
type family Pure_6989586621679363176 @a_iv9m (a_a1tVO :: a_iv9m) :: Semi.Min a_iv9m where
  Pure_6989586621679363176 @a_iv9m a_6989586621679363178_a1tVR = Apply MinSym0 a_6989586621679363178_a1tVR
type TFHelper_6989586621679363186 :: forall a_iv9C
                                            b_iv9D. Semi.Min a_iv9C
                                                    -> Semi.Min b_iv9D -> Semi.Min a_iv9C
type family TFHelper_6989586621679363186 @a_iv9C @b_iv9D (a_a1tVW :: Semi.Min a_iv9C) (a_a1tVX :: Semi.Min b_iv9D) :: Semi.Min a_iv9C where
  TFHelper_6989586621679363186 @a_iv9C @b_iv9D a_a1tW1 _ = a_a1tW1
type TFHelper_6989586621679363196 :: forall a_iv9y
                                            b_iv9z. Semi.Min a_iv9y
                                                    -> Semi.Min b_iv9z -> Semi.Min b_iv9z
type family TFHelper_6989586621679363196 @a_iv9y @b_iv9z (a_a1tW6 :: Semi.Min a_iv9y) (a_a1tW7 :: Semi.Min b_iv9z) :: Semi.Min b_iv9z where
  TFHelper_6989586621679363196 @a_iv9y @b_iv9z _ a_a1tWb = a_a1tWb
type TFHelper_6989586621679363206 :: forall a_iv9o
                                            b_iv9p. Semi.Min ((~>) a_iv9o b_iv9p)
                                                    -> Semi.Min a_iv9o -> Semi.Min b_iv9p
type family TFHelper_6989586621679363206 @a_iv9o @b_iv9p (a_a1tWg :: Semi.Min ((~>) a_iv9o b_iv9p)) (a_a1tWh :: Semi.Min a_iv9o) :: Semi.Min b_iv9p where
  TFHelper_6989586621679363206 @a_iv9o @b_iv9p ('Semi.Min f_a1tWl) ('Semi.Min x_a1tWm) = Apply MinSym0 (Apply f_a1tWl x_a1tWm)
type LiftA2_6989586621679363218 :: forall a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> Semi.Min a_iv9s
                                                      -> Semi.Min b_iv9t -> Semi.Min c_iv9u
type family LiftA2_6989586621679363218 @a_iv9s @b_iv9t @c_iv9u (a_a1tWs :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a1tWt :: Semi.Min a_iv9s) (a_a1tWu :: Semi.Min b_iv9t) :: Semi.Min c_iv9u where
  LiftA2_6989586621679363218 @a_iv9s @b_iv9t @c_iv9u f_a1tWz ('Semi.Min a_a1tWA) ('Semi.Min b_a1tWB) = Apply MinSym0 (Apply (Apply f_a1tWz a_a1tWA) b_a1tWB)
instance PApplicative Semi.Min where
  type Pure a_a1tVJ = Pure_6989586621679363176 a_a1tVJ
  type (<*) a_a1tVS a_a1tVT = TFHelper_6989586621679363186 a_a1tVS a_a1tVT
  type (*>) a_a1tW2 a_a1tW3 = TFHelper_6989586621679363196 a_a1tW2 a_a1tW3
  type (<*>) a_a1tWc a_a1tWd = TFHelper_6989586621679363206 a_a1tWc a_a1tWd
  type LiftA2 a_a1tWn a_a1tWo a_a1tWp = LiftA2_6989586621679363218 a_a1tWn a_a1tWo a_a1tWp
type Succ_6989586621679363297 :: forall a_a1tMX. Semi.Min a_a1tMX
                                                  -> Semi.Min a_a1tMX
type family Succ_6989586621679363297 @a_a1tMX (a_a1tXJ :: Semi.Min a_a1tMX) :: Semi.Min a_a1tMX where
  Succ_6989586621679363297 @a_a1tMX ('Semi.Min a_a1tXM :: Semi.Min a_a1tMX) = Apply MinSym0 (Apply SuccSym0 a_a1tXM)
type Pred_6989586621679363304 :: forall a_a1tMX. Semi.Min a_a1tMX
                                                  -> Semi.Min a_a1tMX
type family Pred_6989586621679363304 @a_a1tMX (a_a1tXQ :: Semi.Min a_a1tMX) :: Semi.Min a_a1tMX where
  Pred_6989586621679363304 @a_a1tMX ('Semi.Min a_a1tXT :: Semi.Min a_a1tMX) = Apply MinSym0 (Apply PredSym0 a_a1tXT)
type ToEnum_6989586621679363311 :: forall a_a1tMX. GHC.Num.Natural.Natural
                                                    -> Semi.Min a_a1tMX
type family ToEnum_6989586621679363311 @a_a1tMX (a_a1tXZ :: GHC.Num.Natural.Natural) :: Semi.Min a_a1tMX where
  ToEnum_6989586621679363311 @a_a1tMX (a_6989586621679363313_a1tY2 :: GHC.Num.Natural.Natural) = Apply (Apply (Apply (.@#@$) MinSym0) ToEnumSym0) a_6989586621679363313_a1tY2
type FromEnum_6989586621679363320 :: forall a_a1tMX. Semi.Min a_a1tMX
                                                      -> GHC.Num.Natural.Natural
type family FromEnum_6989586621679363320 @a_a1tMX (a_a1tY6 :: Semi.Min a_a1tMX) :: GHC.Num.Natural.Natural where
  FromEnum_6989586621679363320 @a_a1tMX ('Semi.Min a_a1tY9 :: Semi.Min a_a1tMX) = Apply FromEnumSym0 a_a1tY9
type EnumFromTo_6989586621679363328 :: forall a_a1tMX. Semi.Min a_a1tMX
                                                        -> Semi.Min a_a1tMX -> [Semi.Min a_a1tMX]
type family EnumFromTo_6989586621679363328 @a_a1tMX (a_a1tYe :: Semi.Min a_a1tMX) (a_a1tYf :: Semi.Min a_a1tMX) :: [Semi.Min a_a1tMX] where
  EnumFromTo_6989586621679363328 @a_a1tMX ('Semi.Min a_a1tYj :: Semi.Min a_a1tMX) ('Semi.Min b_a1tYk :: Semi.Min a_a1tMX) = Apply (Apply MapSym0 MinSym0) (Apply (Apply EnumFromToSym0 a_a1tYj) b_a1tYk)
type EnumFromThenTo_6989586621679363340 :: forall a_a1tMX. Semi.Min a_a1tMX
                                                            -> Semi.Min a_a1tMX
                                                              -> Semi.Min a_a1tMX
                                                                  -> [Semi.Min a_a1tMX]
type family EnumFromThenTo_6989586621679363340 @a_a1tMX (a_a1tYq :: Semi.Min a_a1tMX) (a_a1tYr :: Semi.Min a_a1tMX) (a_a1tYs :: Semi.Min a_a1tMX) :: [Semi.Min a_a1tMX] where
  EnumFromThenTo_6989586621679363340 @a_a1tMX ('Semi.Min a_a1tYx :: Semi.Min a_a1tMX) ('Semi.Min b_a1tYy :: Semi.Min a_a1tMX) ('Semi.Min c_a1tYz :: Semi.Min a_a1tMX) = Apply (Apply MapSym0 MinSym0) (Apply (Apply (Apply EnumFromThenToSym0 a_a1tYx) b_a1tYy) c_a1tYz)
instance PEnum (Semi.Min a_a1tMX) where
  type Succ a_a1tXG = Succ_6989586621679363297 a_a1tXG
  type Pred a_a1tXN = Pred_6989586621679363304 a_a1tXN
  type ToEnum a_a1tXU = ToEnum_6989586621679363311 a_a1tXU
  type FromEnum a_a1tY3 = FromEnum_6989586621679363320 a_a1tY3
  type EnumFromTo a_a1tYa a_a1tYb = EnumFromTo_6989586621679363328 a_a1tYa a_a1tYb
  type EnumFromThenTo a_a1tYl a_a1tYm a_a1tYn = EnumFromThenTo_6989586621679363340 a_a1tYl a_a1tYm a_a1tYn
type Fmap_6989586621679363388 :: forall a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> Semi.Min a_iYSL -> Semi.Min b_iYSM
type family Fmap_6989586621679363388 @a_iYSL @b_iYSM (a_a1tZc :: (~>) a_iYSL b_iYSM) (a_a1tZd :: Semi.Min a_iYSL) :: Semi.Min b_iYSM where
  Fmap_6989586621679363388 @a_iYSL @b_iYSM _f_6989586621679362950_a1tZh ('Semi.Min a_6989586621679362954_a1tZi) = Apply MinSym0 (Apply _f_6989586621679362950_a1tZh a_6989586621679362954_a1tZi)
type family LamCases_6989586621679363408_a1tZv (_z_69895866216793629526989586621679363406 :: a7566047373982667319) a_69895866216793629566989586621679363407 a_6989586621679363410_a1tZx where
  LamCases_6989586621679363408_a1tZv _z_6989586621679362952_a1tZs a_6989586621679362956_a1tZt _ = _z_6989586621679362952_a1tZs
data LamCases_6989586621679363408Sym0 (_z_69895866216793629526989586621679363406 :: a7566047373982667319) a_69895866216793629566989586621679363407 a_69895866216793634106989586621679363411
  where
    LamCases_6989586621679363408Sym0KindInference :: SameKind (Apply (LamCases_6989586621679363408Sym0 _z_69895866216793629526989586621679363406 a_69895866216793629566989586621679363407) arg_a1tZy) (LamCases_6989586621679363408Sym1 _z_69895866216793629526989586621679363406 a_69895866216793629566989586621679363407 arg_a1tZy) =>
                                                      LamCases_6989586621679363408Sym0 _z_69895866216793629526989586621679363406 a_69895866216793629566989586621679363407 a_69895866216793634106989586621679363411
type instance Apply @_ @_ (LamCases_6989586621679363408Sym0 _z_69895866216793629526989586621679363406 a_69895866216793629566989586621679363407) a_69895866216793634106989586621679363411 = LamCases_6989586621679363408_a1tZv _z_69895866216793629526989586621679363406 a_69895866216793629566989586621679363407 a_69895866216793634106989586621679363411
instance SuppressUnusedWarnings (LamCases_6989586621679363408Sym0 _z_69895866216793629526989586621679363406 a_69895866216793629566989586621679363407) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679363408Sym0KindInference ())
type family LamCases_6989586621679363408Sym1 (_z_69895866216793629526989586621679363406 :: a7566047373982667319) a_69895866216793629566989586621679363407 a_69895866216793634106989586621679363411 where
  LamCases_6989586621679363408Sym1 _z_69895866216793629526989586621679363406 a_69895866216793629566989586621679363407 a_69895866216793634106989586621679363411 = LamCases_6989586621679363408_a1tZv _z_69895866216793629526989586621679363406 a_69895866216793629566989586621679363407 a_69895866216793634106989586621679363411
type TFHelper_6989586621679363399 :: forall a_iYSP b_iYSQ. a_iYSP
                                                            -> Semi.Min b_iYSQ -> Semi.Min a_iYSP
type family TFHelper_6989586621679363399 @a_iYSP @b_iYSQ (a_a1tZn :: a_iYSP) (a_a1tZo :: Semi.Min b_iYSQ) :: Semi.Min a_iYSP where
  TFHelper_6989586621679363399 @a_iYSP @b_iYSQ _z_6989586621679362952_a1tZs ('Semi.Min a_6989586621679362956_a1tZt) = Apply MinSym0 (Apply (LamCases_6989586621679363408Sym0 _z_6989586621679362952_a1tZs a_6989586621679362956_a1tZt) a_6989586621679362956_a1tZt)
instance PFunctor Semi.Min where
  type Fmap a_a1tZ8 a_a1tZ9 = Fmap_6989586621679363388 a_a1tZ8 a_a1tZ9
  type (<$) a_a1tZj a_a1tZk = TFHelper_6989586621679363399 a_a1tZj a_a1tZk
type TFHelper_6989586621679363429 :: forall a_iv98
                                            b_iv99. Semi.Min a_iv98
                                                    -> Semi.Min b_iv99 -> Semi.Min b_iv99
type family TFHelper_6989586621679363429 @a_iv98 @b_iv99 (a_a1tZV :: Semi.Min a_iv98) (a_a1tZW :: Semi.Min b_iv99) :: Semi.Min b_iv99 where
  TFHelper_6989586621679363429 @a_iv98 @b_iv99 a_6989586621679363431_a1u00 a_6989586621679363433_a1u01 = Apply (Apply (*>@#@$) a_6989586621679363431_a1u00) a_6989586621679363433_a1u01
type TFHelper_6989586621679363444 :: forall a_iv94
                                            b_iv95. Semi.Min a_iv94
                                                    -> (~>) a_iv94 (Semi.Min b_iv95)
                                                        -> Semi.Min b_iv95
type family TFHelper_6989586621679363444 @a_iv94 @b_iv95 (a_a1u06 :: Semi.Min a_iv94) (a_a1u07 :: (~>) a_iv94 (Semi.Min b_iv95)) :: Semi.Min b_iv95 where
  TFHelper_6989586621679363444 @a_iv94 @b_iv95 ('Semi.Min a_a1u0b) f_a1u0c = Apply f_a1u0c a_a1u0b
instance PMonad Semi.Min where
  type (>>) a_a1tZN a_a1tZO = TFHelper_6989586621679363429 a_a1tZN a_a1tZO
  type (>>=) a_a1u02 a_a1u03 = TFHelper_6989586621679363444 a_a1u02 a_a1u03
type TFHelper_6989586621679363481 :: forall a_a1tN8. Semi.Min a_a1tN8
                                                      -> Semi.Min a_a1tN8 -> Semi.Min a_a1tN8
type family TFHelper_6989586621679363481 @a_a1tN8 (a_a1u0H :: Semi.Min a_a1tN8) (a_a1u0I :: Semi.Min a_a1tN8) :: Semi.Min a_a1tN8 where
  TFHelper_6989586621679363481 @a_a1tN8 ('Semi.Min a_a1u0M :: Semi.Min a_a1tN8) ('Semi.Min b_a1u0N :: Semi.Min a_a1tN8) = Apply MinSym0 (Apply (Apply Min_Sym0 a_a1u0M) b_a1u0N)
instance PSemigroup (Semi.Min a_a1tN8) where
  type (<>) a_a1u0D a_a1u0E = TFHelper_6989586621679363481 a_a1u0D a_a1u0E
type Mempty_6989586621679363517 :: forall a_a1tNb. Semi.Min a_a1tNb
type family Mempty_6989586621679363517 @a_a1tNb :: Semi.Min a_a1tNb where
  Mempty_6989586621679363517 @a_a1tNb = MaxBoundSym0
instance PMonoid (Semi.Min a_a1tNb) where
  type Mempty = Mempty_6989586621679363517
type TFHelper_6989586621679363592 :: forall a_a1tNc. Semi.Min a_a1tNc
                                                      -> Semi.Min a_a1tNc -> Semi.Min a_a1tNc
type family TFHelper_6989586621679363592 @a_a1tNc (a_a1u2u :: Semi.Min a_a1tNc) (a_a1u2v :: Semi.Min a_a1tNc) :: Semi.Min a_a1tNc where
  TFHelper_6989586621679363592 @a_a1tNc ('Semi.Min a_a1u2z :: Semi.Min a_a1tNc) ('Semi.Min b_a1u2A :: Semi.Min a_a1tNc) = Apply MinSym0 (Apply (Apply (+@#@$) a_a1u2z) b_a1u2A)
type TFHelper_6989586621679363603 :: forall a_a1tNc. Semi.Min a_a1tNc
                                                      -> Semi.Min a_a1tNc -> Semi.Min a_a1tNc
type family TFHelper_6989586621679363603 @a_a1tNc (a_a1u2F :: Semi.Min a_a1tNc) (a_a1u2G :: Semi.Min a_a1tNc) :: Semi.Min a_a1tNc where
  TFHelper_6989586621679363603 @a_a1tNc ('Semi.Min a_a1u2K :: Semi.Min a_a1tNc) ('Semi.Min b_a1u2L :: Semi.Min a_a1tNc) = Apply MinSym0 (Apply (Apply (*@#@$) a_a1u2K) b_a1u2L)
type TFHelper_6989586621679363614 :: forall a_a1tNc. Semi.Min a_a1tNc
                                                      -> Semi.Min a_a1tNc -> Semi.Min a_a1tNc
type family TFHelper_6989586621679363614 @a_a1tNc (a_a1u2Q :: Semi.Min a_a1tNc) (a_a1u2R :: Semi.Min a_a1tNc) :: Semi.Min a_a1tNc where
  TFHelper_6989586621679363614 @a_a1tNc ('Semi.Min a_a1u2V :: Semi.Min a_a1tNc) ('Semi.Min b_a1u2W :: Semi.Min a_a1tNc) = Apply MinSym0 (Apply (Apply (-@#@$) a_a1u2V) b_a1u2W)
type Negate_6989586621679363624 :: forall a_a1tNc. Semi.Min a_a1tNc
                                                    -> Semi.Min a_a1tNc
type family Negate_6989586621679363624 @a_a1tNc (a_a1u30 :: Semi.Min a_a1tNc) :: Semi.Min a_a1tNc where
  Negate_6989586621679363624 @a_a1tNc ('Semi.Min a_a1u33 :: Semi.Min a_a1tNc) = Apply MinSym0 (Apply NegateSym0 a_a1u33)
type Abs_6989586621679363631 :: forall a_a1tNc. Semi.Min a_a1tNc
                                                -> Semi.Min a_a1tNc
type family Abs_6989586621679363631 @a_a1tNc (a_a1u37 :: Semi.Min a_a1tNc) :: Semi.Min a_a1tNc where
  Abs_6989586621679363631 @a_a1tNc ('Semi.Min a_a1u3a :: Semi.Min a_a1tNc) = Apply MinSym0 (Apply AbsSym0 a_a1u3a)
type Signum_6989586621679363638 :: forall a_a1tNc. Semi.Min a_a1tNc
                                                    -> Semi.Min a_a1tNc
type family Signum_6989586621679363638 @a_a1tNc (a_a1u3e :: Semi.Min a_a1tNc) :: Semi.Min a_a1tNc where
  Signum_6989586621679363638 @a_a1tNc ('Semi.Min a_a1u3h :: Semi.Min a_a1tNc) = Apply MinSym0 (Apply SignumSym0 a_a1u3h)
type FromInteger_6989586621679363645 :: forall a_a1tNc. GHC.Num.Natural.Natural
                                                        -> Semi.Min a_a1tNc
type family FromInteger_6989586621679363645 @a_a1tNc (a_a1u3n :: GHC.Num.Natural.Natural) :: Semi.Min a_a1tNc where
  FromInteger_6989586621679363645 @a_a1tNc (a_6989586621679363647_a1u3q :: GHC.Num.Natural.Natural) = Apply (Apply (Apply (.@#@$) MinSym0) FromIntegerSym0) a_6989586621679363647_a1u3q
instance PNum (Semi.Min a_a1tNc) where
  type (+) a_a1u2q a_a1u2r = TFHelper_6989586621679363592 a_a1u2q a_a1u2r
  type (*) a_a1u2B a_a1u2C = TFHelper_6989586621679363603 a_a1u2B a_a1u2C
  type (-) a_a1u2M a_a1u2N = TFHelper_6989586621679363614 a_a1u2M a_a1u2N
  type Negate a_a1u2X = Negate_6989586621679363624 a_a1u2X
  type Abs a_a1u34 = Abs_6989586621679363631 a_a1u34
  type Signum a_a1u3b = Signum_6989586621679363638 a_a1u3b
  type FromInteger a_a1u3i = FromInteger_6989586621679363645 a_a1u3i
type FoldMap_6989586621679363733 :: forall a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU
                                                    -> Semi.Min a_iYVT -> m_iYVU
type family FoldMap_6989586621679363733 @a_iYVT @m_iYVU (a_a1u4L :: (~>) a_iYVT m_iYVU) (a_a1u4M :: Semi.Min a_iYVT) :: m_iYVU where
  FoldMap_6989586621679363733 @a_iYVT @m_iYVU _f_6989586621679362959_a1u4Q ('Semi.Min a_6989586621679362963_a1u4R) = Apply _f_6989586621679362959_a1u4Q a_6989586621679362963_a1u4R
type Foldr_6989586621679363745 :: forall a_iYVX
                                          b_iYVY. (~>) a_iYVX ((~>) b_iYVY b_iYVY)
                                                  -> b_iYVY -> Semi.Min a_iYVX -> b_iYVY
type family Foldr_6989586621679363745 @a_iYVX @b_iYVY (a_a1u4X :: (~>) a_iYVX ((~>) b_iYVY b_iYVY)) (a_a1u4Y :: b_iYVY) (a_a1u4Z :: Semi.Min a_iYVX) :: b_iYVY where
  Foldr_6989586621679363745 @a_iYVX @b_iYVY _f_6989586621679362959_a1u54 _z_6989586621679362961_a1u55 ('Semi.Min a_6989586621679362965_a1u56) = Apply (Apply _f_6989586621679362959_a1u54 a_6989586621679362965_a1u56) _z_6989586621679362961_a1u55
instance PFoldable Semi.Min where
  type FoldMap a_a1u4H a_a1u4I = FoldMap_6989586621679363733 a_a1u4H a_a1u4I
  type Foldr a_a1u4S a_a1u4T a_a1u4U = Foldr_6989586621679363745 a_a1u4S a_a1u4T a_a1u4U
type Traverse_6989586621679364101 :: forall a_i1u58
                                            f_i1u59
                                            b_i1u5a. (~>) a_i1u58 (f_i1u59 b_i1u5a)
                                                      -> Semi.Min a_i1u58
                                                        -> f_i1u59 (Semi.Min b_i1u5a)
type family Traverse_6989586621679364101 @a_i1u58 @f_i1u59 @b_i1u5a (a_a1uaH :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) (a_a1uaI :: Semi.Min a_i1u58) :: f_i1u59 (Semi.Min b_i1u5a) where
  Traverse_6989586621679364101 @a_i1u58 @f_i1u59 @b_i1u5a _f_6989586621679362968_a1uaM ('Semi.Min a_6989586621679362970_a1uaN) = Apply (Apply FmapSym0 MinSym0) (Apply _f_6989586621679362968_a1uaM a_6989586621679362970_a1uaN)
instance PTraversable Semi.Min where
  type Traverse a_a1uaD a_a1uaE = Traverse_6989586621679364101 a_a1uaD a_a1uaE
type Pure_6989586621679364111 :: forall a_iv9m. a_iv9m
                                                -> Semi.Max a_iv9m
type family Pure_6989586621679364111 @a_iv9m (a_a1uaT :: a_iv9m) :: Semi.Max a_iv9m where
  Pure_6989586621679364111 @a_iv9m a_6989586621679364113_a1uaW = Apply MaxSym0 a_6989586621679364113_a1uaW
type TFHelper_6989586621679364121 :: forall a_iv9C
                                            b_iv9D. Semi.Max a_iv9C
                                                    -> Semi.Max b_iv9D -> Semi.Max a_iv9C
type family TFHelper_6989586621679364121 @a_iv9C @b_iv9D (a_a1ub1 :: Semi.Max a_iv9C) (a_a1ub2 :: Semi.Max b_iv9D) :: Semi.Max a_iv9C where
  TFHelper_6989586621679364121 @a_iv9C @b_iv9D a_a1ub6 _ = a_a1ub6
type TFHelper_6989586621679364131 :: forall a_iv9y
                                            b_iv9z. Semi.Max a_iv9y
                                                    -> Semi.Max b_iv9z -> Semi.Max b_iv9z
type family TFHelper_6989586621679364131 @a_iv9y @b_iv9z (a_a1ubb :: Semi.Max a_iv9y) (a_a1ubc :: Semi.Max b_iv9z) :: Semi.Max b_iv9z where
  TFHelper_6989586621679364131 @a_iv9y @b_iv9z _ a_a1ubg = a_a1ubg
type TFHelper_6989586621679364141 :: forall a_iv9o
                                            b_iv9p. Semi.Max ((~>) a_iv9o b_iv9p)
                                                    -> Semi.Max a_iv9o -> Semi.Max b_iv9p
type family TFHelper_6989586621679364141 @a_iv9o @b_iv9p (a_a1ubl :: Semi.Max ((~>) a_iv9o b_iv9p)) (a_a1ubm :: Semi.Max a_iv9o) :: Semi.Max b_iv9p where
  TFHelper_6989586621679364141 @a_iv9o @b_iv9p ('Semi.Max f_a1ubq) ('Semi.Max x_a1ubr) = Apply MaxSym0 (Apply f_a1ubq x_a1ubr)
type LiftA2_6989586621679364153 :: forall a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> Semi.Max a_iv9s
                                                      -> Semi.Max b_iv9t -> Semi.Max c_iv9u
type family LiftA2_6989586621679364153 @a_iv9s @b_iv9t @c_iv9u (a_a1ubx :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a1uby :: Semi.Max a_iv9s) (a_a1ubz :: Semi.Max b_iv9t) :: Semi.Max c_iv9u where
  LiftA2_6989586621679364153 @a_iv9s @b_iv9t @c_iv9u f_a1ubE ('Semi.Max a_a1ubF) ('Semi.Max b_a1ubG) = Apply MaxSym0 (Apply (Apply f_a1ubE a_a1ubF) b_a1ubG)
instance PApplicative Semi.Max where
  type Pure a_a1uaO = Pure_6989586621679364111 a_a1uaO
  type (<*) a_a1uaX a_a1uaY = TFHelper_6989586621679364121 a_a1uaX a_a1uaY
  type (*>) a_a1ub7 a_a1ub8 = TFHelper_6989586621679364131 a_a1ub7 a_a1ub8
  type (<*>) a_a1ubh a_a1ubi = TFHelper_6989586621679364141 a_a1ubh a_a1ubi
  type LiftA2 a_a1ubs a_a1ubt a_a1ubu = LiftA2_6989586621679364153 a_a1ubs a_a1ubt a_a1ubu
type Succ_6989586621679364166 :: forall a_a1tNt. Semi.Max a_a1tNt
                                                  -> Semi.Max a_a1tNt
type family Succ_6989586621679364166 @a_a1tNt (a_a1ubK :: Semi.Max a_a1tNt) :: Semi.Max a_a1tNt where
  Succ_6989586621679364166 @a_a1tNt ('Semi.Max a_a1ubN :: Semi.Max a_a1tNt) = Apply MaxSym0 (Apply SuccSym0 a_a1ubN)
type Pred_6989586621679364173 :: forall a_a1tNt. Semi.Max a_a1tNt
                                                  -> Semi.Max a_a1tNt
type family Pred_6989586621679364173 @a_a1tNt (a_a1ubR :: Semi.Max a_a1tNt) :: Semi.Max a_a1tNt where
  Pred_6989586621679364173 @a_a1tNt ('Semi.Max a_a1ubU :: Semi.Max a_a1tNt) = Apply MaxSym0 (Apply PredSym0 a_a1ubU)
type ToEnum_6989586621679364180 :: forall a_a1tNt. GHC.Num.Natural.Natural
                                                    -> Semi.Max a_a1tNt
type family ToEnum_6989586621679364180 @a_a1tNt (a_a1uc0 :: GHC.Num.Natural.Natural) :: Semi.Max a_a1tNt where
  ToEnum_6989586621679364180 @a_a1tNt (a_6989586621679364182_a1uc3 :: GHC.Num.Natural.Natural) = Apply (Apply (Apply (.@#@$) MaxSym0) ToEnumSym0) a_6989586621679364182_a1uc3
type FromEnum_6989586621679364189 :: forall a_a1tNt. Semi.Max a_a1tNt
                                                      -> GHC.Num.Natural.Natural
type family FromEnum_6989586621679364189 @a_a1tNt (a_a1uc7 :: Semi.Max a_a1tNt) :: GHC.Num.Natural.Natural where
  FromEnum_6989586621679364189 @a_a1tNt ('Semi.Max a_a1uca :: Semi.Max a_a1tNt) = Apply FromEnumSym0 a_a1uca
type EnumFromTo_6989586621679364197 :: forall a_a1tNt. Semi.Max a_a1tNt
                                                        -> Semi.Max a_a1tNt -> [Semi.Max a_a1tNt]
type family EnumFromTo_6989586621679364197 @a_a1tNt (a_a1ucf :: Semi.Max a_a1tNt) (a_a1ucg :: Semi.Max a_a1tNt) :: [Semi.Max a_a1tNt] where
  EnumFromTo_6989586621679364197 @a_a1tNt ('Semi.Max a_a1uck :: Semi.Max a_a1tNt) ('Semi.Max b_a1ucl :: Semi.Max a_a1tNt) = Apply (Apply MapSym0 MaxSym0) (Apply (Apply EnumFromToSym0 a_a1uck) b_a1ucl)
type EnumFromThenTo_6989586621679364209 :: forall a_a1tNt. Semi.Max a_a1tNt
                                                            -> Semi.Max a_a1tNt
                                                              -> Semi.Max a_a1tNt
                                                                  -> [Semi.Max a_a1tNt]
type family EnumFromThenTo_6989586621679364209 @a_a1tNt (a_a1ucr :: Semi.Max a_a1tNt) (a_a1ucs :: Semi.Max a_a1tNt) (a_a1uct :: Semi.Max a_a1tNt) :: [Semi.Max a_a1tNt] where
  EnumFromThenTo_6989586621679364209 @a_a1tNt ('Semi.Max a_a1ucy :: Semi.Max a_a1tNt) ('Semi.Max b_a1ucz :: Semi.Max a_a1tNt) ('Semi.Max c_a1ucA :: Semi.Max a_a1tNt) = Apply (Apply MapSym0 MaxSym0) (Apply (Apply (Apply EnumFromThenToSym0 a_a1ucy) b_a1ucz) c_a1ucA)
instance PEnum (Semi.Max a_a1tNt) where
  type Succ a_a1ubH = Succ_6989586621679364166 a_a1ubH
  type Pred a_a1ubO = Pred_6989586621679364173 a_a1ubO
  type ToEnum a_a1ubV = ToEnum_6989586621679364180 a_a1ubV
  type FromEnum a_a1uc4 = FromEnum_6989586621679364189 a_a1uc4
  type EnumFromTo a_a1ucb a_a1ucc = EnumFromTo_6989586621679364197 a_a1ucb a_a1ucc
  type EnumFromThenTo a_a1ucm a_a1ucn a_a1uco = EnumFromThenTo_6989586621679364209 a_a1ucm a_a1ucn a_a1uco
type Fmap_6989586621679364223 :: forall a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> Semi.Max a_iYSL -> Semi.Max b_iYSM
type family Fmap_6989586621679364223 @a_iYSL @b_iYSM (a_a1ucF :: (~>) a_iYSL b_iYSM) (a_a1ucG :: Semi.Max a_iYSL) :: Semi.Max b_iYSM where
  Fmap_6989586621679364223 @a_iYSL @b_iYSM _f_6989586621679362973_a1ucK ('Semi.Max a_6989586621679362977_a1ucL) = Apply MaxSym0 (Apply _f_6989586621679362973_a1ucK a_6989586621679362977_a1ucL)
type family LamCases_6989586621679364243_a1ucY (_z_69895866216793629756989586621679364241 :: a7566047373982667319) a_69895866216793629796989586621679364242 a_6989586621679364245_a1ud0 where
  LamCases_6989586621679364243_a1ucY _z_6989586621679362975_a1ucV a_6989586621679362979_a1ucW _ = _z_6989586621679362975_a1ucV
data LamCases_6989586621679364243Sym0 (_z_69895866216793629756989586621679364241 :: a7566047373982667319) a_69895866216793629796989586621679364242 a_69895866216793642456989586621679364246
  where
    LamCases_6989586621679364243Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364243Sym0 _z_69895866216793629756989586621679364241 a_69895866216793629796989586621679364242) arg_a1ud1) (LamCases_6989586621679364243Sym1 _z_69895866216793629756989586621679364241 a_69895866216793629796989586621679364242 arg_a1ud1) =>
                                                      LamCases_6989586621679364243Sym0 _z_69895866216793629756989586621679364241 a_69895866216793629796989586621679364242 a_69895866216793642456989586621679364246
type instance Apply @_ @_ (LamCases_6989586621679364243Sym0 _z_69895866216793629756989586621679364241 a_69895866216793629796989586621679364242) a_69895866216793642456989586621679364246 = LamCases_6989586621679364243_a1ucY _z_69895866216793629756989586621679364241 a_69895866216793629796989586621679364242 a_69895866216793642456989586621679364246
instance SuppressUnusedWarnings (LamCases_6989586621679364243Sym0 _z_69895866216793629756989586621679364241 a_69895866216793629796989586621679364242) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364243Sym0KindInference ())
type family LamCases_6989586621679364243Sym1 (_z_69895866216793629756989586621679364241 :: a7566047373982667319) a_69895866216793629796989586621679364242 a_69895866216793642456989586621679364246 where
  LamCases_6989586621679364243Sym1 _z_69895866216793629756989586621679364241 a_69895866216793629796989586621679364242 a_69895866216793642456989586621679364246 = LamCases_6989586621679364243_a1ucY _z_69895866216793629756989586621679364241 a_69895866216793629796989586621679364242 a_69895866216793642456989586621679364246
type TFHelper_6989586621679364234 :: forall a_iYSP b_iYSQ. a_iYSP
                                                            -> Semi.Max b_iYSQ -> Semi.Max a_iYSP
type family TFHelper_6989586621679364234 @a_iYSP @b_iYSQ (a_a1ucQ :: a_iYSP) (a_a1ucR :: Semi.Max b_iYSQ) :: Semi.Max a_iYSP where
  TFHelper_6989586621679364234 @a_iYSP @b_iYSQ _z_6989586621679362975_a1ucV ('Semi.Max a_6989586621679362979_a1ucW) = Apply MaxSym0 (Apply (LamCases_6989586621679364243Sym0 _z_6989586621679362975_a1ucV a_6989586621679362979_a1ucW) a_6989586621679362979_a1ucW)
instance PFunctor Semi.Max where
  type Fmap a_a1ucB a_a1ucC = Fmap_6989586621679364223 a_a1ucB a_a1ucC
  type (<$) a_a1ucM a_a1ucN = TFHelper_6989586621679364234 a_a1ucM a_a1ucN
type TFHelper_6989586621679364250 :: forall a_iv98
                                            b_iv99. Semi.Max a_iv98
                                                    -> Semi.Max b_iv99 -> Semi.Max b_iv99
type family TFHelper_6989586621679364250 @a_iv98 @b_iv99 (a_a1uda :: Semi.Max a_iv98) (a_a1udb :: Semi.Max b_iv99) :: Semi.Max b_iv99 where
  TFHelper_6989586621679364250 @a_iv98 @b_iv99 a_6989586621679364252_a1udf a_6989586621679364254_a1udg = Apply (Apply (*>@#@$) a_6989586621679364252_a1udf) a_6989586621679364254_a1udg
type TFHelper_6989586621679364265 :: forall a_iv94
                                            b_iv95. Semi.Max a_iv94
                                                    -> (~>) a_iv94 (Semi.Max b_iv95)
                                                        -> Semi.Max b_iv95
type family TFHelper_6989586621679364265 @a_iv94 @b_iv95 (a_a1udl :: Semi.Max a_iv94) (a_a1udm :: (~>) a_iv94 (Semi.Max b_iv95)) :: Semi.Max b_iv95 where
  TFHelper_6989586621679364265 @a_iv94 @b_iv95 ('Semi.Max a_a1udq) f_a1udr = Apply f_a1udr a_a1udq
instance PMonad Semi.Max where
  type (>>) a_a1ud2 a_a1ud3 = TFHelper_6989586621679364250 a_a1ud2 a_a1ud3
  type (>>=) a_a1udh a_a1udi = TFHelper_6989586621679364265 a_a1udh a_a1udi
type TFHelper_6989586621679364276 :: forall a_a1tNE. Semi.Max a_a1tNE
                                                      -> Semi.Max a_a1tNE -> Semi.Max a_a1tNE
type family TFHelper_6989586621679364276 @a_a1tNE (a_a1udw :: Semi.Max a_a1tNE) (a_a1udx :: Semi.Max a_a1tNE) :: Semi.Max a_a1tNE where
  TFHelper_6989586621679364276 @a_a1tNE ('Semi.Max a_a1udB :: Semi.Max a_a1tNE) ('Semi.Max b_a1udC :: Semi.Max a_a1tNE) = Apply MaxSym0 (Apply (Apply Max_Sym0 a_a1udB) b_a1udC)
instance PSemigroup (Semi.Max a_a1tNE) where
  type (<>) a_a1uds a_a1udt = TFHelper_6989586621679364276 a_a1uds a_a1udt
type Mempty_6989586621679364285 :: forall a_a1tNH. Semi.Max a_a1tNH
type family Mempty_6989586621679364285 @a_a1tNH :: Semi.Max a_a1tNH where
  Mempty_6989586621679364285 @a_a1tNH = MinBoundSym0
instance PMonoid (Semi.Max a_a1tNH) where
  type Mempty = Mempty_6989586621679364285
type TFHelper_6989586621679364290 :: forall a_a1tNI. Semi.Max a_a1tNI
                                                      -> Semi.Max a_a1tNI -> Semi.Max a_a1tNI
type family TFHelper_6989586621679364290 @a_a1tNI (a_a1udK :: Semi.Max a_a1tNI) (a_a1udL :: Semi.Max a_a1tNI) :: Semi.Max a_a1tNI where
  TFHelper_6989586621679364290 @a_a1tNI ('Semi.Max a_a1udP :: Semi.Max a_a1tNI) ('Semi.Max b_a1udQ :: Semi.Max a_a1tNI) = Apply MaxSym0 (Apply (Apply (+@#@$) a_a1udP) b_a1udQ)
type TFHelper_6989586621679364301 :: forall a_a1tNI. Semi.Max a_a1tNI
                                                      -> Semi.Max a_a1tNI -> Semi.Max a_a1tNI
type family TFHelper_6989586621679364301 @a_a1tNI (a_a1udV :: Semi.Max a_a1tNI) (a_a1udW :: Semi.Max a_a1tNI) :: Semi.Max a_a1tNI where
  TFHelper_6989586621679364301 @a_a1tNI ('Semi.Max a_a1ue0 :: Semi.Max a_a1tNI) ('Semi.Max b_a1ue1 :: Semi.Max a_a1tNI) = Apply MaxSym0 (Apply (Apply (*@#@$) a_a1ue0) b_a1ue1)
type TFHelper_6989586621679364312 :: forall a_a1tNI. Semi.Max a_a1tNI
                                                      -> Semi.Max a_a1tNI -> Semi.Max a_a1tNI
type family TFHelper_6989586621679364312 @a_a1tNI (a_a1ue6 :: Semi.Max a_a1tNI) (a_a1ue7 :: Semi.Max a_a1tNI) :: Semi.Max a_a1tNI where
  TFHelper_6989586621679364312 @a_a1tNI ('Semi.Max a_a1ueb :: Semi.Max a_a1tNI) ('Semi.Max b_a1uec :: Semi.Max a_a1tNI) = Apply MaxSym0 (Apply (Apply (-@#@$) a_a1ueb) b_a1uec)
type Negate_6989586621679364322 :: forall a_a1tNI. Semi.Max a_a1tNI
                                                    -> Semi.Max a_a1tNI
type family Negate_6989586621679364322 @a_a1tNI (a_a1ueg :: Semi.Max a_a1tNI) :: Semi.Max a_a1tNI where
  Negate_6989586621679364322 @a_a1tNI ('Semi.Max a_a1uej :: Semi.Max a_a1tNI) = Apply MaxSym0 (Apply NegateSym0 a_a1uej)
type Abs_6989586621679364329 :: forall a_a1tNI. Semi.Max a_a1tNI
                                                -> Semi.Max a_a1tNI
type family Abs_6989586621679364329 @a_a1tNI (a_a1uen :: Semi.Max a_a1tNI) :: Semi.Max a_a1tNI where
  Abs_6989586621679364329 @a_a1tNI ('Semi.Max a_a1ueq :: Semi.Max a_a1tNI) = Apply MaxSym0 (Apply AbsSym0 a_a1ueq)
type Signum_6989586621679364336 :: forall a_a1tNI. Semi.Max a_a1tNI
                                                    -> Semi.Max a_a1tNI
type family Signum_6989586621679364336 @a_a1tNI (a_a1ueu :: Semi.Max a_a1tNI) :: Semi.Max a_a1tNI where
  Signum_6989586621679364336 @a_a1tNI ('Semi.Max a_a1uex :: Semi.Max a_a1tNI) = Apply MaxSym0 (Apply SignumSym0 a_a1uex)
type FromInteger_6989586621679364343 :: forall a_a1tNI. GHC.Num.Natural.Natural
                                                        -> Semi.Max a_a1tNI
type family FromInteger_6989586621679364343 @a_a1tNI (a_a1ueD :: GHC.Num.Natural.Natural) :: Semi.Max a_a1tNI where
  FromInteger_6989586621679364343 @a_a1tNI (a_6989586621679364345_a1ueG :: GHC.Num.Natural.Natural) = Apply (Apply (Apply (.@#@$) MaxSym0) FromIntegerSym0) a_6989586621679364345_a1ueG
instance PNum (Semi.Max a_a1tNI) where
  type (+) a_a1udG a_a1udH = TFHelper_6989586621679364290 a_a1udG a_a1udH
  type (*) a_a1udR a_a1udS = TFHelper_6989586621679364301 a_a1udR a_a1udS
  type (-) a_a1ue2 a_a1ue3 = TFHelper_6989586621679364312 a_a1ue2 a_a1ue3
  type Negate a_a1ued = Negate_6989586621679364322 a_a1ued
  type Abs a_a1uek = Abs_6989586621679364329 a_a1uek
  type Signum a_a1uer = Signum_6989586621679364336 a_a1uer
  type FromInteger a_a1uey = FromInteger_6989586621679364343 a_a1uey
type FoldMap_6989586621679364353 :: forall a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU
                                                    -> Semi.Max a_iYVT -> m_iYVU
type family FoldMap_6989586621679364353 @a_iYVT @m_iYVU (a_a1ueL :: (~>) a_iYVT m_iYVU) (a_a1ueM :: Semi.Max a_iYVT) :: m_iYVU where
  FoldMap_6989586621679364353 @a_iYVT @m_iYVU _f_6989586621679362982_a1ueQ ('Semi.Max a_6989586621679362986_a1ueR) = Apply _f_6989586621679362982_a1ueQ a_6989586621679362986_a1ueR
type Foldr_6989586621679364365 :: forall a_iYVX
                                          b_iYVY. (~>) a_iYVX ((~>) b_iYVY b_iYVY)
                                                  -> b_iYVY -> Semi.Max a_iYVX -> b_iYVY
type family Foldr_6989586621679364365 @a_iYVX @b_iYVY (a_a1ueX :: (~>) a_iYVX ((~>) b_iYVY b_iYVY)) (a_a1ueY :: b_iYVY) (a_a1ueZ :: Semi.Max a_iYVX) :: b_iYVY where
  Foldr_6989586621679364365 @a_iYVX @b_iYVY _f_6989586621679362982_a1uf4 _z_6989586621679362984_a1uf5 ('Semi.Max a_6989586621679362988_a1uf6) = Apply (Apply _f_6989586621679362982_a1uf4 a_6989586621679362988_a1uf6) _z_6989586621679362984_a1uf5
instance PFoldable Semi.Max where
  type FoldMap a_a1ueH a_a1ueI = FoldMap_6989586621679364353 a_a1ueH a_a1ueI
  type Foldr a_a1ueS a_a1ueT a_a1ueU = Foldr_6989586621679364365 a_a1ueS a_a1ueT a_a1ueU
type Traverse_6989586621679364379 :: forall a_i1u58
                                            f_i1u59
                                            b_i1u5a. (~>) a_i1u58 (f_i1u59 b_i1u5a)
                                                      -> Semi.Max a_i1u58
                                                        -> f_i1u59 (Semi.Max b_i1u5a)
type family Traverse_6989586621679364379 @a_i1u58 @f_i1u59 @b_i1u5a (a_a1ufb :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) (a_a1ufc :: Semi.Max a_i1u58) :: f_i1u59 (Semi.Max b_i1u5a) where
  Traverse_6989586621679364379 @a_i1u58 @f_i1u59 @b_i1u5a _f_6989586621679362991_a1ufg ('Semi.Max a_6989586621679362993_a1ufh) = Apply (Apply FmapSym0 MaxSym0) (Apply _f_6989586621679362991_a1ufg a_6989586621679362993_a1ufh)
instance PTraversable Semi.Max where
  type Traverse a_a1uf7 a_a1uf8 = Traverse_6989586621679364379 a_a1uf7 a_a1uf8
type TFHelper_6989586621679364415 :: forall a_a1tNS
                                            b_a1tNT. Arg a_a1tNS b_a1tNT
                                                      -> Arg a_a1tNS b_a1tNT -> Bool
type family TFHelper_6989586621679364415 @a_a1tNS @b_a1tNT (a_a1ufL :: Arg a_a1tNS b_a1tNT) (a_a1ufM :: Arg a_a1tNS b_a1tNT) :: Bool where
  TFHelper_6989586621679364415 @a_a1tNS @b_a1tNT ('Arg a_a1ufQ _ :: Arg a_a1tNS b_a1tNT) ('Arg b_a1ufR _ :: Arg a_a1tNS b_a1tNT) = Apply (Apply (==@#@$) a_a1ufQ) b_a1ufR
instance PEq (Arg a_a1tNS b_a1tNT) where
  type (==) a_a1ufH a_a1ufI = TFHelper_6989586621679364415 a_a1ufH a_a1ufI
type family LamCases_6989586621679364436_a1ug5 a6989586621679362692 (_f_69895866216793629976989586621679364433 :: (~>) a7566047373982667315 b7566047373982667316) a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435 a_6989586621679364439_a1ug8 where
  LamCases_6989586621679364436_a1ug5 a_a1tNW _f_6989586621679362997_a1ug1 a_6989586621679363003_a1ug2 a_6989586621679363005_a1ug3 n_6989586621679363001_a1ug6 = n_6989586621679363001_a1ug6
data LamCases_6989586621679364436Sym0 a6989586621679362692 (_f_69895866216793629976989586621679364433 :: (~>) a7566047373982667315 b7566047373982667316) a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435 a_69895866216793644396989586621679364440
  where
    LamCases_6989586621679364436Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364436Sym0 a6989586621679362692 _f_69895866216793629976989586621679364433 a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435) arg_a1ug9) (LamCases_6989586621679364436Sym1 a6989586621679362692 _f_69895866216793629976989586621679364433 a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435 arg_a1ug9) =>
                                                      LamCases_6989586621679364436Sym0 a6989586621679362692 _f_69895866216793629976989586621679364433 a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435 a_69895866216793644396989586621679364440
type instance Apply @_ @_ (LamCases_6989586621679364436Sym0 a6989586621679362692 _f_69895866216793629976989586621679364433 a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435) a_69895866216793644396989586621679364440 = LamCases_6989586621679364436_a1ug5 a6989586621679362692 _f_69895866216793629976989586621679364433 a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435 a_69895866216793644396989586621679364440
instance SuppressUnusedWarnings (LamCases_6989586621679364436Sym0 a6989586621679362692 _f_69895866216793629976989586621679364433 a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364436Sym0KindInference ())
type family LamCases_6989586621679364436Sym1 a6989586621679362692 (_f_69895866216793629976989586621679364433 :: (~>) a7566047373982667315 b7566047373982667316) a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435 a_69895866216793644396989586621679364440 where
  LamCases_6989586621679364436Sym1 a6989586621679362692 _f_69895866216793629976989586621679364433 a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435 a_69895866216793644396989586621679364440 = LamCases_6989586621679364436_a1ug5 a6989586621679362692 _f_69895866216793629976989586621679364433 a_69895866216793630036989586621679364434 a_69895866216793630056989586621679364435 a_69895866216793644396989586621679364440
type Fmap_6989586621679364426 :: forall a_a1tNW
                                        a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> Arg a_a1tNW a_iYSL -> Arg a_a1tNW b_iYSM
type family Fmap_6989586621679364426 @a_a1tNW @a_iYSL @b_iYSM (a_a1ufW :: (~>) a_iYSL b_iYSM) (a_a1ufX :: Arg a_a1tNW a_iYSL) :: Arg a_a1tNW b_iYSM where
  Fmap_6989586621679364426 @a_a1tNW @a_iYSL @b_iYSM (_f_6989586621679362997_a1ug1 :: (~>) a_iYSL b_iYSM) ('Arg a_6989586621679363003_a1ug2 a_6989586621679363005_a1ug3 :: Arg a_a1tNW a_iYSL) = Apply (Apply ArgSym0 (Apply (LamCases_6989586621679364436Sym0 a_a1tNW _f_6989586621679362997_a1ug1 a_6989586621679363003_a1ug2 a_6989586621679363005_a1ug3) a_6989586621679363003_a1ug2)) (Apply _f_6989586621679362997_a1ug1 a_6989586621679363005_a1ug3)
type family LamCases_6989586621679364454_a1ugn a6989586621679362692 (_z_69895866216793629996989586621679364451 :: a7566047373982667319) a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_6989586621679364457_a1ugq where
  LamCases_6989586621679364454_a1ugn a_a1tNW _z_6989586621679362999_a1ugj a_6989586621679363009_a1ugk a_6989586621679363011_a1ugl n_6989586621679363007_a1ugo = n_6989586621679363007_a1ugo
data LamCases_6989586621679364454Sym0 a6989586621679362692 (_z_69895866216793629996989586621679364451 :: a7566047373982667319) a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644576989586621679364458
  where
    LamCases_6989586621679364454Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364454Sym0 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453) arg_a1ugr) (LamCases_6989586621679364454Sym1 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 arg_a1ugr) =>
                                                      LamCases_6989586621679364454Sym0 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644576989586621679364458
type instance Apply @_ @_ (LamCases_6989586621679364454Sym0 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453) a_69895866216793644576989586621679364458 = LamCases_6989586621679364454_a1ugn a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644576989586621679364458
instance SuppressUnusedWarnings (LamCases_6989586621679364454Sym0 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364454Sym0KindInference ())
type family LamCases_6989586621679364454Sym1 a6989586621679362692 (_z_69895866216793629996989586621679364451 :: a7566047373982667319) a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644576989586621679364458 where
  LamCases_6989586621679364454Sym1 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644576989586621679364458 = LamCases_6989586621679364454_a1ugn a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644576989586621679364458
type family LamCases_6989586621679364460_a1ugt a6989586621679362692 (_z_69895866216793629996989586621679364451 :: a7566047373982667319) a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_6989586621679364462_a1ugv where
  LamCases_6989586621679364460_a1ugt a_a1tNW _z_6989586621679362999_a1ugj a_6989586621679363009_a1ugk a_6989586621679363011_a1ugl _ = _z_6989586621679362999_a1ugj
data LamCases_6989586621679364460Sym0 a6989586621679362692 (_z_69895866216793629996989586621679364451 :: a7566047373982667319) a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644626989586621679364463
  where
    LamCases_6989586621679364460Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364460Sym0 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453) arg_a1ugw) (LamCases_6989586621679364460Sym1 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 arg_a1ugw) =>
                                                      LamCases_6989586621679364460Sym0 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644626989586621679364463
type instance Apply @_ @_ (LamCases_6989586621679364460Sym0 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453) a_69895866216793644626989586621679364463 = LamCases_6989586621679364460_a1ugt a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644626989586621679364463
instance SuppressUnusedWarnings (LamCases_6989586621679364460Sym0 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364460Sym0KindInference ())
type family LamCases_6989586621679364460Sym1 a6989586621679362692 (_z_69895866216793629996989586621679364451 :: a7566047373982667319) a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644626989586621679364463 where
  LamCases_6989586621679364460Sym1 a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644626989586621679364463 = LamCases_6989586621679364460_a1ugt a6989586621679362692 _z_69895866216793629996989586621679364451 a_69895866216793630096989586621679364452 a_69895866216793630116989586621679364453 a_69895866216793644626989586621679364463
type TFHelper_6989586621679364444 :: forall a_a1tNW
                                            a_iYSP
                                            b_iYSQ. a_iYSP
                                                    -> Arg a_a1tNW b_iYSQ -> Arg a_a1tNW a_iYSP
type family TFHelper_6989586621679364444 @a_a1tNW @a_iYSP @b_iYSQ (a_a1uge :: a_iYSP) (a_a1ugf :: Arg a_a1tNW b_iYSQ) :: Arg a_a1tNW a_iYSP where
  TFHelper_6989586621679364444 @a_a1tNW @a_iYSP @b_iYSQ (_z_6989586621679362999_a1ugj :: a_iYSP) ('Arg a_6989586621679363009_a1ugk a_6989586621679363011_a1ugl :: Arg a_a1tNW b_iYSQ) = Apply (Apply ArgSym0 (Apply (LamCases_6989586621679364454Sym0 a_a1tNW _z_6989586621679362999_a1ugj a_6989586621679363009_a1ugk a_6989586621679363011_a1ugl) a_6989586621679363009_a1ugk)) (Apply (LamCases_6989586621679364460Sym0 a_a1tNW _z_6989586621679362999_a1ugj a_6989586621679363009_a1ugk a_6989586621679363011_a1ugl) a_6989586621679363011_a1ugl)
instance PFunctor (Arg a_a1tNW) where
  type Fmap a_a1ufS a_a1ufT = Fmap_6989586621679364426 a_a1ufS a_a1ufT
  type (<$) a_a1uga a_a1ugb = TFHelper_6989586621679364444 a_a1uga a_a1ugb
type Compare_6989586621679364517 :: forall a_a1tNX
                                            b_a1tNY. Arg a_a1tNX b_a1tNY
                                                    -> Arg a_a1tNX b_a1tNY -> Ordering
type family Compare_6989586621679364517 @a_a1tNX @b_a1tNY (a_a1uhp :: Arg a_a1tNX b_a1tNY) (a_a1uhq :: Arg a_a1tNX b_a1tNY) :: Ordering where
  Compare_6989586621679364517 @a_a1tNX @b_a1tNY ('Arg a_a1uhu _ :: Arg a_a1tNX b_a1tNY) ('Arg b_a1uhv _ :: Arg a_a1tNX b_a1tNY) = Apply (Apply CompareSym0 a_a1uhu) b_a1uhv
type family Let6989586621679364543YSym0 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) where
  Let6989586621679364543YSym0 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 = Let6989586621679364543Y a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536
type family Let6989586621679364543XSym0 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) where
  Let6989586621679364543XSym0 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 = Let6989586621679364543X a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536
type family Let6989586621679364543Y a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) where
  Let6989586621679364543Y a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG = Apply (Apply ArgSym0 b_a1uhL) wild_6989586621679362770_a1uhM
type family Let6989586621679364543X a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) where
  Let6989586621679364543X a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG = Apply (Apply ArgSym0 a_a1uhJ) wild_6989586621679362768_a1uhK
type family LamCases_6989586621679364546_a1uhR a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) a_6989586621679364548_a1uhT where
  LamCases_6989586621679364546_a1uhR a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG 'True = Let6989586621679364543XSym0 a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG
  LamCases_6989586621679364546_a1uhR a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG 'False = Let6989586621679364543YSym0 a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG
data LamCases_6989586621679364546Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645486989586621679364549
  where
    LamCases_6989586621679364546Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364546Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536) arg_a1uhU) (LamCases_6989586621679364546Sym1 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 arg_a1uhU) =>
                                                      LamCases_6989586621679364546Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645486989586621679364549
type instance Apply @_ @_ (LamCases_6989586621679364546Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536) a_69895866216793645486989586621679364549 = LamCases_6989586621679364546_a1uhR a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645486989586621679364549
instance SuppressUnusedWarnings (LamCases_6989586621679364546Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364546Sym0KindInference ())
type family LamCases_6989586621679364546Sym1 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645486989586621679364549 where
  LamCases_6989586621679364546Sym1 a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645486989586621679364549 = LamCases_6989586621679364546_a1uhR a6989586621679362693 b6989586621679362694 a6989586621679364539 wild_69895866216793627686989586621679364540 b6989586621679364541 wild_69895866216793627706989586621679364542 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645486989586621679364549
type family LamCases_6989586621679364537_a1uhI a6989586621679362693 b6989586621679362694 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) a_6989586621679364551_a1uhW a_6989586621679364553_a1uhY where
  LamCases_6989586621679364537_a1uhI a_a1tNX b_a1tNY arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG ('Arg a_a1uhJ wild_6989586621679362768_a1uhK) ('Arg b_a1uhL wild_6989586621679362770_a1uhM) = Apply (LamCases_6989586621679364546Sym0 a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG) (Apply (Apply (<=@#@$) a_a1uhJ) b_a1uhL)
data LamCases_6989586621679364537Sym0 a6989586621679362693 b6989586621679362694 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645516989586621679364552
  where
    LamCases_6989586621679364537Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364537Sym0 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536) arg_a1uhZ) (LamCases_6989586621679364537Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 arg_a1uhZ) =>
                                                      LamCases_6989586621679364537Sym0 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552
type instance Apply @_ @_ (LamCases_6989586621679364537Sym0 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536) a_69895866216793645516989586621679364552 = LamCases_6989586621679364537Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552
instance SuppressUnusedWarnings (LamCases_6989586621679364537Sym0 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364537Sym0KindInference ())
data LamCases_6989586621679364537Sym1 a6989586621679362693 b6989586621679362694 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645516989586621679364552 a_69895866216793645536989586621679364554
  where
    LamCases_6989586621679364537Sym1KindInference :: SameKind (Apply (LamCases_6989586621679364537Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552) arg_a1uhZ) (LamCases_6989586621679364537Sym2 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552 arg_a1uhZ) =>
                                                      LamCases_6989586621679364537Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552 a_69895866216793645536989586621679364554
type instance Apply @_ @_ (LamCases_6989586621679364537Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552) a_69895866216793645536989586621679364554 = LamCases_6989586621679364537_a1uhI a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552 a_69895866216793645536989586621679364554
instance SuppressUnusedWarnings (LamCases_6989586621679364537Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364537Sym1KindInference ())
type family LamCases_6989586621679364537Sym2 a6989586621679362693 b6989586621679362694 (arg_69895866216793627646989586621679364535 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627666989586621679364536 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645516989586621679364552 a_69895866216793645536989586621679364554 where
  LamCases_6989586621679364537Sym2 a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552 a_69895866216793645536989586621679364554 = LamCases_6989586621679364537_a1uhI a6989586621679362693 b6989586621679362694 arg_69895866216793627646989586621679364535 arg_69895866216793627666989586621679364536 a_69895866216793645516989586621679364552 a_69895866216793645536989586621679364554
type Min_6989586621679364528 :: forall a_a1tNX
                                        b_a1tNY. Arg a_a1tNX b_a1tNY
                                                -> Arg a_a1tNX b_a1tNY -> Arg a_a1tNX b_a1tNY
type family Min_6989586621679364528 @a_a1tNX @b_a1tNY (a_a1uhA :: Arg a_a1tNX b_a1tNY) (a_a1uhB :: Arg a_a1tNX b_a1tNY) :: Arg a_a1tNX b_a1tNY where
  Min_6989586621679364528 @a_a1tNX @b_a1tNY (arg_6989586621679362764_a1uhF :: Arg a_a1tNX b_a1tNY) (arg_6989586621679362766_a1uhG :: Arg a_a1tNX b_a1tNY) = Apply (Apply (LamCases_6989586621679364537Sym0 a_a1tNX b_a1tNY arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG) arg_6989586621679362764_a1uhF) arg_6989586621679362766_a1uhG
type family Let6989586621679364573YSym0 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) where
  Let6989586621679364573YSym0 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 = Let6989586621679364573Y a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566
type family Let6989586621679364573XSym0 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) where
  Let6989586621679364573XSym0 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 = Let6989586621679364573X a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566
type family Let6989586621679364573Y a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) where
  Let6989586621679364573Y a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia = Apply (Apply ArgSym0 b_a1uif) wild_6989586621679362782_a1uig
type family Let6989586621679364573X a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) where
  Let6989586621679364573X a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia = Apply (Apply ArgSym0 a_a1uid) wild_6989586621679362780_a1uie
type family LamCases_6989586621679364576_a1uil a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) a_6989586621679364578_a1uin where
  LamCases_6989586621679364576_a1uil a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia 'True = Let6989586621679364573XSym0 a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia
  LamCases_6989586621679364576_a1uil a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia 'False = Let6989586621679364573YSym0 a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia
data LamCases_6989586621679364576Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645786989586621679364579
  where
    LamCases_6989586621679364576Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364576Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566) arg_a1uio) (LamCases_6989586621679364576Sym1 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 arg_a1uio) =>
                                                      LamCases_6989586621679364576Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645786989586621679364579
type instance Apply @_ @_ (LamCases_6989586621679364576Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566) a_69895866216793645786989586621679364579 = LamCases_6989586621679364576_a1uil a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645786989586621679364579
instance SuppressUnusedWarnings (LamCases_6989586621679364576Sym0 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364576Sym0KindInference ())
type family LamCases_6989586621679364576Sym1 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645786989586621679364579 where
  LamCases_6989586621679364576Sym1 a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645786989586621679364579 = LamCases_6989586621679364576_a1uil a6989586621679362693 b6989586621679362694 a6989586621679364569 wild_69895866216793627806989586621679364570 b6989586621679364571 wild_69895866216793627826989586621679364572 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645786989586621679364579
type family LamCases_6989586621679364567_a1uic a6989586621679362693 b6989586621679362694 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) a_6989586621679364581_a1uiq a_6989586621679364583_a1uis where
  LamCases_6989586621679364567_a1uic a_a1tNX b_a1tNY arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia ('Arg a_a1uid wild_6989586621679362780_a1uie) ('Arg b_a1uif wild_6989586621679362782_a1uig) = Apply (LamCases_6989586621679364576Sym0 a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia) (Apply (Apply (>=@#@$) a_a1uid) b_a1uif)
data LamCases_6989586621679364567Sym0 a6989586621679362693 b6989586621679362694 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645816989586621679364582
  where
    LamCases_6989586621679364567Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364567Sym0 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566) arg_a1uit) (LamCases_6989586621679364567Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 arg_a1uit) =>
                                                      LamCases_6989586621679364567Sym0 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582
type instance Apply @_ @_ (LamCases_6989586621679364567Sym0 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566) a_69895866216793645816989586621679364582 = LamCases_6989586621679364567Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582
instance SuppressUnusedWarnings (LamCases_6989586621679364567Sym0 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364567Sym0KindInference ())
data LamCases_6989586621679364567Sym1 a6989586621679362693 b6989586621679362694 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645816989586621679364582 a_69895866216793645836989586621679364584
  where
    LamCases_6989586621679364567Sym1KindInference :: SameKind (Apply (LamCases_6989586621679364567Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582) arg_a1uit) (LamCases_6989586621679364567Sym2 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582 arg_a1uit) =>
                                                      LamCases_6989586621679364567Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582 a_69895866216793645836989586621679364584
type instance Apply @_ @_ (LamCases_6989586621679364567Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582) a_69895866216793645836989586621679364584 = LamCases_6989586621679364567_a1uic a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582 a_69895866216793645836989586621679364584
instance SuppressUnusedWarnings (LamCases_6989586621679364567Sym1 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364567Sym1KindInference ())
type family LamCases_6989586621679364567Sym2 a6989586621679362693 b6989586621679362694 (arg_69895866216793627766989586621679364565 :: Arg a6989586621679362693 b6989586621679362694) (arg_69895866216793627786989586621679364566 :: Arg a6989586621679362693 b6989586621679362694) a_69895866216793645816989586621679364582 a_69895866216793645836989586621679364584 where
  LamCases_6989586621679364567Sym2 a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582 a_69895866216793645836989586621679364584 = LamCases_6989586621679364567_a1uic a6989586621679362693 b6989586621679362694 arg_69895866216793627766989586621679364565 arg_69895866216793627786989586621679364566 a_69895866216793645816989586621679364582 a_69895866216793645836989586621679364584
type Max_6989586621679364558 :: forall a_a1tNX
                                        b_a1tNY. Arg a_a1tNX b_a1tNY
                                                -> Arg a_a1tNX b_a1tNY -> Arg a_a1tNX b_a1tNY
type family Max_6989586621679364558 @a_a1tNX @b_a1tNY (a_a1ui4 :: Arg a_a1tNX b_a1tNY) (a_a1ui5 :: Arg a_a1tNX b_a1tNY) :: Arg a_a1tNX b_a1tNY where
  Max_6989586621679364558 @a_a1tNX @b_a1tNY (arg_6989586621679362776_a1ui9 :: Arg a_a1tNX b_a1tNY) (arg_6989586621679362778_a1uia :: Arg a_a1tNX b_a1tNY) = Apply (Apply (LamCases_6989586621679364567Sym0 a_a1tNX b_a1tNY arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia) arg_6989586621679362776_a1ui9) arg_6989586621679362778_a1uia
instance POrd (Arg a_a1tNX b_a1tNY) where
  type Compare a_a1uhl a_a1uhm = Compare_6989586621679364517 a_a1uhl a_a1uhm
  type Min a_a1uhw a_a1uhx = Min_6989586621679364528 a_a1uhw a_a1uhx
  type Max a_a1ui0 a_a1ui1 = Max_6989586621679364558 a_a1ui0 a_a1ui1
type ShowsPrec_6989586621679364589 :: forall a_a1tO9
                                              b_a1tOa. GHC.Num.Natural.Natural
                                                      -> Arg a_a1tO9 b_a1tOa
                                                          -> GHC.Exts.Symbol
                                                            -> GHC.Exts.Symbol
type family ShowsPrec_6989586621679364589 @a_a1tO9 @b_a1tOa (a_a1uiB :: GHC.Num.Natural.Natural) (a_a1uiC :: Arg a_a1tO9 b_a1tOa) (a_a1uiD :: GHC.Exts.Symbol) :: GHC.Exts.Symbol where
  ShowsPrec_6989586621679364589 @a_a1tO9 @b_a1tOa (p_6989586621679363015_a1uiI :: GHC.Num.Natural.Natural) ('Arg arg_6989586621679363017_a1uiJ arg_6989586621679363019_a1uiK :: Arg a_a1tO9 b_a1tOa) (a_6989586621679364591_a1uiL :: GHC.Exts.Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679363015_a1uiI) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Arg ")) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 11)) arg_6989586621679363017_a1uiJ)) (Apply (Apply (.@#@$) ShowSpaceSym0) (Apply (Apply ShowsPrecSym0 (FromInteger 11)) arg_6989586621679363019_a1uiK))))) a_6989586621679364591_a1uiL
instance PShow (Arg a_a1tO9 b_a1tOa) where
  type ShowsPrec a_a1uiu a_a1uiv a_a1uiw = ShowsPrec_6989586621679364589 a_a1uiu a_a1uiv a_a1uiw
type family LamCases_6989586621679364616_a1uiZ a6989586621679362707 (_f_69895866216793630236989586621679364613 :: (~>) a7566047373982667509 m7566047373982667510) a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615 a_6989586621679364618_a1uj1 where
  LamCases_6989586621679364616_a1uiZ a_a1tOb _f_6989586621679363023_a1uiV a_6989586621679363027_a1uiW a_6989586621679363029_a1uiX _ = MemptySym0
data LamCases_6989586621679364616Sym0 a6989586621679362707 (_f_69895866216793630236989586621679364613 :: (~>) a7566047373982667509 m7566047373982667510) a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615 a_69895866216793646186989586621679364619
  where
    LamCases_6989586621679364616Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364616Sym0 a6989586621679362707 _f_69895866216793630236989586621679364613 a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615) arg_a1uj2) (LamCases_6989586621679364616Sym1 a6989586621679362707 _f_69895866216793630236989586621679364613 a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615 arg_a1uj2) =>
                                                      LamCases_6989586621679364616Sym0 a6989586621679362707 _f_69895866216793630236989586621679364613 a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615 a_69895866216793646186989586621679364619
type instance Apply @_ @_ (LamCases_6989586621679364616Sym0 a6989586621679362707 _f_69895866216793630236989586621679364613 a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615) a_69895866216793646186989586621679364619 = LamCases_6989586621679364616_a1uiZ a6989586621679362707 _f_69895866216793630236989586621679364613 a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615 a_69895866216793646186989586621679364619
instance SuppressUnusedWarnings (LamCases_6989586621679364616Sym0 a6989586621679362707 _f_69895866216793630236989586621679364613 a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364616Sym0KindInference ())
type family LamCases_6989586621679364616Sym1 a6989586621679362707 (_f_69895866216793630236989586621679364613 :: (~>) a7566047373982667509 m7566047373982667510) a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615 a_69895866216793646186989586621679364619 where
  LamCases_6989586621679364616Sym1 a6989586621679362707 _f_69895866216793630236989586621679364613 a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615 a_69895866216793646186989586621679364619 = LamCases_6989586621679364616_a1uiZ a6989586621679362707 _f_69895866216793630236989586621679364613 a_69895866216793630276989586621679364614 a_69895866216793630296989586621679364615 a_69895866216793646186989586621679364619
type FoldMap_6989586621679364606 :: forall a_a1tOb
                                            a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU
                                                    -> Arg a_a1tOb a_iYVT -> m_iYVU
type family FoldMap_6989586621679364606 @a_a1tOb @a_iYVT @m_iYVU (a_a1uiQ :: (~>) a_iYVT m_iYVU) (a_a1uiR :: Arg a_a1tOb a_iYVT) :: m_iYVU where
  FoldMap_6989586621679364606 @a_a1tOb @a_iYVT @m_iYVU (_f_6989586621679363023_a1uiV :: (~>) a_iYVT m_iYVU) ('Arg a_6989586621679363027_a1uiW a_6989586621679363029_a1uiX :: Arg a_a1tOb a_iYVT) = Apply (Apply MappendSym0 (Apply (LamCases_6989586621679364616Sym0 a_a1tOb _f_6989586621679363023_a1uiV a_6989586621679363027_a1uiW a_6989586621679363029_a1uiX) a_6989586621679363027_a1uiW)) (Apply _f_6989586621679363023_a1uiV a_6989586621679363029_a1uiX)
type family LamCases_6989586621679364637_a1ujk a6989586621679362707 (_f_69895866216793630236989586621679364633 :: (~>) a7566047373982667513 ((~>) b7566047373982667514 b7566047373982667514)) (_z_69895866216793630256989586621679364634 :: b7566047373982667514) a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_6989586621679364640_a1ujn a_6989586621679364642_a1ujp where
  LamCases_6989586621679364637_a1ujk a_a1tOb _f_6989586621679363023_a1ujf _z_6989586621679363025_a1ujg a_6989586621679363033_a1ujh a_6989586621679363035_a1uji _ n_6989586621679363031_a1ujl = n_6989586621679363031_a1ujl
data LamCases_6989586621679364637Sym0 a6989586621679362707 (_f_69895866216793630236989586621679364633 :: (~>) a7566047373982667513 ((~>) b7566047373982667514 b7566047373982667514)) (_z_69895866216793630256989586621679364634 :: b7566047373982667514) a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641
  where
    LamCases_6989586621679364637Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364637Sym0 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636) arg_a1ujq) (LamCases_6989586621679364637Sym1 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 arg_a1ujq) =>
                                                      LamCases_6989586621679364637Sym0 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641
type instance Apply @_ @_ (LamCases_6989586621679364637Sym0 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636) a_69895866216793646406989586621679364641 = LamCases_6989586621679364637Sym1 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641
instance SuppressUnusedWarnings (LamCases_6989586621679364637Sym0 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364637Sym0KindInference ())
data LamCases_6989586621679364637Sym1 a6989586621679362707 (_f_69895866216793630236989586621679364633 :: (~>) a7566047373982667513 ((~>) b7566047373982667514 b7566047373982667514)) (_z_69895866216793630256989586621679364634 :: b7566047373982667514) a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641 a_69895866216793646426989586621679364643
  where
    LamCases_6989586621679364637Sym1KindInference :: SameKind (Apply (LamCases_6989586621679364637Sym1 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641) arg_a1ujq) (LamCases_6989586621679364637Sym2 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641 arg_a1ujq) =>
                                                      LamCases_6989586621679364637Sym1 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641 a_69895866216793646426989586621679364643
type instance Apply @_ @_ (LamCases_6989586621679364637Sym1 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641) a_69895866216793646426989586621679364643 = LamCases_6989586621679364637_a1ujk a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641 a_69895866216793646426989586621679364643
instance SuppressUnusedWarnings (LamCases_6989586621679364637Sym1 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364637Sym1KindInference ())
type family LamCases_6989586621679364637Sym2 a6989586621679362707 (_f_69895866216793630236989586621679364633 :: (~>) a7566047373982667513 ((~>) b7566047373982667514 b7566047373982667514)) (_z_69895866216793630256989586621679364634 :: b7566047373982667514) a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641 a_69895866216793646426989586621679364643 where
  LamCases_6989586621679364637Sym2 a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641 a_69895866216793646426989586621679364643 = LamCases_6989586621679364637_a1ujk a6989586621679362707 _f_69895866216793630236989586621679364633 _z_69895866216793630256989586621679364634 a_69895866216793630336989586621679364635 a_69895866216793630356989586621679364636 a_69895866216793646406989586621679364641 a_69895866216793646426989586621679364643
type Foldr_6989586621679364624 :: forall a_a1tOb
                                          a_iYVX
                                          b_iYVY. (~>) a_iYVX ((~>) b_iYVY b_iYVY)
                                                  -> b_iYVY -> Arg a_a1tOb a_iYVX -> b_iYVY
type family Foldr_6989586621679364624 @a_a1tOb @a_iYVX @b_iYVY (a_a1uj8 :: (~>) a_iYVX ((~>) b_iYVY b_iYVY)) (a_a1uj9 :: b_iYVY) (a_a1uja :: Arg a_a1tOb a_iYVX) :: b_iYVY where
  Foldr_6989586621679364624 @a_a1tOb @a_iYVX @b_iYVY (_f_6989586621679363023_a1ujf :: (~>) a_iYVX ((~>) b_iYVY b_iYVY)) (_z_6989586621679363025_a1ujg :: b_iYVY) ('Arg a_6989586621679363033_a1ujh a_6989586621679363035_a1uji :: Arg a_a1tOb a_iYVX) = Apply (Apply (LamCases_6989586621679364637Sym0 a_a1tOb _f_6989586621679363023_a1ujf _z_6989586621679363025_a1ujg a_6989586621679363033_a1ujh a_6989586621679363035_a1uji) a_6989586621679363033_a1ujh) (Apply (Apply _f_6989586621679363023_a1ujf a_6989586621679363035_a1uji) _z_6989586621679363025_a1ujg)
instance PFoldable (Arg a_a1tOb) where
  type FoldMap a_a1uiM a_a1uiN = FoldMap_6989586621679364606 a_a1uiM a_a1uiN
  type Foldr a_a1uj3 a_a1uj4 a_a1uj5 = Foldr_6989586621679364624 a_a1uj3 a_a1uj4 a_a1uj5
type Traverse_6989586621679364647 :: forall a_a1tOc
                                            a_i1u58
                                            f_i1u59
                                            b_i1u5a. (~>) a_i1u58 (f_i1u59 b_i1u5a)
                                                      -> Arg a_a1tOc a_i1u58
                                                        -> f_i1u59 (Arg a_a1tOc b_i1u5a)
type family Traverse_6989586621679364647 @a_a1tOc @a_i1u58 @f_i1u59 @b_i1u5a (a_a1ujv :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) (a_a1ujw :: Arg a_a1tOc a_i1u58) :: f_i1u59 (Arg a_a1tOc b_i1u5a) where
  Traverse_6989586621679364647 @a_a1tOc @a_i1u58 @f_i1u59 @b_i1u5a (_f_6989586621679363039_a1ujA :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) ('Arg a_6989586621679363041_a1ujB a_6989586621679363043_a1ujC :: Arg a_a1tOc a_i1u58) = Apply (Apply (Apply LiftA2Sym0 ArgSym0) (Apply PureSym0 a_6989586621679363041_a1ujB)) (Apply _f_6989586621679363039_a1ujA a_6989586621679363043_a1ujC)
instance PTraversable (Arg a_a1tOc) where
  type Traverse a_a1ujr a_a1ujs = Traverse_6989586621679364647 a_a1ujr a_a1ujs
type Pure_6989586621679364658 :: forall a_iv9m. a_iv9m
                                                -> First a_iv9m
type family Pure_6989586621679364658 @a_iv9m (a_a1ujG :: a_iv9m) :: First a_iv9m where
  Pure_6989586621679364658 @a_iv9m x_a1ujJ = Apply FirstSym0 x_a1ujJ
type TFHelper_6989586621679364666 :: forall a_iv9C
                                            b_iv9D. First a_iv9C -> First b_iv9D -> First a_iv9C
type family TFHelper_6989586621679364666 @a_iv9C @b_iv9D (a_a1ujO :: First a_iv9C) (a_a1ujP :: First b_iv9D) :: First a_iv9C where
  TFHelper_6989586621679364666 @a_iv9C @b_iv9D a_a1ujT _ = a_a1ujT
type TFHelper_6989586621679364676 :: forall a_iv9y
                                            b_iv9z. First a_iv9y -> First b_iv9z -> First b_iv9z
type family TFHelper_6989586621679364676 @a_iv9y @b_iv9z (a_a1ujY :: First a_iv9y) (a_a1ujZ :: First b_iv9z) :: First b_iv9z where
  TFHelper_6989586621679364676 @a_iv9y @b_iv9z _ a_a1uk3 = a_a1uk3
type TFHelper_6989586621679364686 :: forall a_iv9o
                                            b_iv9p. First ((~>) a_iv9o b_iv9p)
                                                    -> First a_iv9o -> First b_iv9p
type family TFHelper_6989586621679364686 @a_iv9o @b_iv9p (a_a1uk8 :: First ((~>) a_iv9o b_iv9p)) (a_a1uk9 :: First a_iv9o) :: First b_iv9p where
  TFHelper_6989586621679364686 @a_iv9o @b_iv9p ('First f_a1ukd) ('First x_a1uke) = Apply FirstSym0 (Apply f_a1ukd x_a1uke)
type LiftA2_6989586621679364698 :: forall a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> First a_iv9s
                                                      -> First b_iv9t -> First c_iv9u
type family LiftA2_6989586621679364698 @a_iv9s @b_iv9t @c_iv9u (a_a1ukk :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a1ukl :: First a_iv9s) (a_a1ukm :: First b_iv9t) :: First c_iv9u where
  LiftA2_6989586621679364698 @a_iv9s @b_iv9t @c_iv9u f_a1ukr ('First a_a1uks) ('First b_a1ukt) = Apply FirstSym0 (Apply (Apply f_a1ukr a_a1uks) b_a1ukt)
instance PApplicative First where
  type Pure a_a1ujD = Pure_6989586621679364658 a_a1ujD
  type (<*) a_a1ujK a_a1ujL = TFHelper_6989586621679364666 a_a1ujK a_a1ujL
  type (*>) a_a1ujU a_a1ujV = TFHelper_6989586621679364676 a_a1ujU a_a1ujV
  type (<*>) a_a1uk4 a_a1uk5 = TFHelper_6989586621679364686 a_a1uk4 a_a1uk5
  type LiftA2 a_a1ukf a_a1ukg a_a1ukh = LiftA2_6989586621679364698 a_a1ukf a_a1ukg a_a1ukh
type Succ_6989586621679364711 :: forall a_a1tOl. First a_a1tOl
                                                  -> First a_a1tOl
type family Succ_6989586621679364711 @a_a1tOl (a_a1ukx :: First a_a1tOl) :: First a_a1tOl where
  Succ_6989586621679364711 @a_a1tOl ('First a_a1ukA :: First a_a1tOl) = Apply FirstSym0 (Apply SuccSym0 a_a1ukA)
type Pred_6989586621679364718 :: forall a_a1tOl. First a_a1tOl
                                                  -> First a_a1tOl
type family Pred_6989586621679364718 @a_a1tOl (a_a1ukE :: First a_a1tOl) :: First a_a1tOl where
  Pred_6989586621679364718 @a_a1tOl ('First a_a1ukH :: First a_a1tOl) = Apply FirstSym0 (Apply PredSym0 a_a1ukH)
type ToEnum_6989586621679364725 :: forall a_a1tOl. GHC.Num.Natural.Natural
                                                    -> First a_a1tOl
type family ToEnum_6989586621679364725 @a_a1tOl (a_a1ukN :: GHC.Num.Natural.Natural) :: First a_a1tOl where
  ToEnum_6989586621679364725 @a_a1tOl (a_6989586621679364727_a1ukQ :: GHC.Num.Natural.Natural) = Apply (Apply (Apply (.@#@$) FirstSym0) ToEnumSym0) a_6989586621679364727_a1ukQ
type FromEnum_6989586621679364734 :: forall a_a1tOl. First a_a1tOl
                                                      -> GHC.Num.Natural.Natural
type family FromEnum_6989586621679364734 @a_a1tOl (a_a1ukU :: First a_a1tOl) :: GHC.Num.Natural.Natural where
  FromEnum_6989586621679364734 @a_a1tOl ('First a_a1ukX :: First a_a1tOl) = Apply FromEnumSym0 a_a1ukX
type EnumFromTo_6989586621679364742 :: forall a_a1tOl. First a_a1tOl
                                                        -> First a_a1tOl -> [First a_a1tOl]
type family EnumFromTo_6989586621679364742 @a_a1tOl (a_a1ul2 :: First a_a1tOl) (a_a1ul3 :: First a_a1tOl) :: [First a_a1tOl] where
  EnumFromTo_6989586621679364742 @a_a1tOl ('First a_a1ul7 :: First a_a1tOl) ('First b_a1ul8 :: First a_a1tOl) = Apply (Apply MapSym0 FirstSym0) (Apply (Apply EnumFromToSym0 a_a1ul7) b_a1ul8)
type EnumFromThenTo_6989586621679364754 :: forall a_a1tOl. First a_a1tOl
                                                            -> First a_a1tOl
                                                              -> First a_a1tOl
                                                                  -> [First a_a1tOl]
type family EnumFromThenTo_6989586621679364754 @a_a1tOl (a_a1ule :: First a_a1tOl) (a_a1ulf :: First a_a1tOl) (a_a1ulg :: First a_a1tOl) :: [First a_a1tOl] where
  EnumFromThenTo_6989586621679364754 @a_a1tOl ('First a_a1ull :: First a_a1tOl) ('First b_a1ulm :: First a_a1tOl) ('First c_a1uln :: First a_a1tOl) = Apply (Apply MapSym0 FirstSym0) (Apply (Apply (Apply EnumFromThenToSym0 a_a1ull) b_a1ulm) c_a1uln)
instance PEnum (First a_a1tOl) where
  type Succ a_a1uku = Succ_6989586621679364711 a_a1uku
  type Pred a_a1ukB = Pred_6989586621679364718 a_a1ukB
  type ToEnum a_a1ukI = ToEnum_6989586621679364725 a_a1ukI
  type FromEnum a_a1ukR = FromEnum_6989586621679364734 a_a1ukR
  type EnumFromTo a_a1ukY a_a1ukZ = EnumFromTo_6989586621679364742 a_a1ukY a_a1ukZ
  type EnumFromThenTo a_a1ul9 a_a1ula a_a1ulb = EnumFromThenTo_6989586621679364754 a_a1ul9 a_a1ula a_a1ulb
type Fmap_6989586621679364768 :: forall a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> First a_iYSL -> First b_iYSM
type family Fmap_6989586621679364768 @a_iYSL @b_iYSM (a_a1uls :: (~>) a_iYSL b_iYSM) (a_a1ult :: First a_iYSL) :: First b_iYSM where
  Fmap_6989586621679364768 @a_iYSL @b_iYSM _f_6989586621679363046_a1ulx ('First a_6989586621679363050_a1uly) = Apply FirstSym0 (Apply _f_6989586621679363046_a1ulx a_6989586621679363050_a1uly)
type family LamCases_6989586621679364788_a1ulL (_z_69895866216793630486989586621679364786 :: a7566047373982667319) a_69895866216793630526989586621679364787 a_6989586621679364790_a1ulN where
  LamCases_6989586621679364788_a1ulL _z_6989586621679363048_a1ulI a_6989586621679363052_a1ulJ _ = _z_6989586621679363048_a1ulI
data LamCases_6989586621679364788Sym0 (_z_69895866216793630486989586621679364786 :: a7566047373982667319) a_69895866216793630526989586621679364787 a_69895866216793647906989586621679364791
  where
    LamCases_6989586621679364788Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364788Sym0 _z_69895866216793630486989586621679364786 a_69895866216793630526989586621679364787) arg_a1ulO) (LamCases_6989586621679364788Sym1 _z_69895866216793630486989586621679364786 a_69895866216793630526989586621679364787 arg_a1ulO) =>
                                                      LamCases_6989586621679364788Sym0 _z_69895866216793630486989586621679364786 a_69895866216793630526989586621679364787 a_69895866216793647906989586621679364791
type instance Apply @_ @_ (LamCases_6989586621679364788Sym0 _z_69895866216793630486989586621679364786 a_69895866216793630526989586621679364787) a_69895866216793647906989586621679364791 = LamCases_6989586621679364788_a1ulL _z_69895866216793630486989586621679364786 a_69895866216793630526989586621679364787 a_69895866216793647906989586621679364791
instance SuppressUnusedWarnings (LamCases_6989586621679364788Sym0 _z_69895866216793630486989586621679364786 a_69895866216793630526989586621679364787) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364788Sym0KindInference ())
type family LamCases_6989586621679364788Sym1 (_z_69895866216793630486989586621679364786 :: a7566047373982667319) a_69895866216793630526989586621679364787 a_69895866216793647906989586621679364791 where
  LamCases_6989586621679364788Sym1 _z_69895866216793630486989586621679364786 a_69895866216793630526989586621679364787 a_69895866216793647906989586621679364791 = LamCases_6989586621679364788_a1ulL _z_69895866216793630486989586621679364786 a_69895866216793630526989586621679364787 a_69895866216793647906989586621679364791
type TFHelper_6989586621679364779 :: forall a_iYSP b_iYSQ. a_iYSP
                                                            -> First b_iYSQ -> First a_iYSP
type family TFHelper_6989586621679364779 @a_iYSP @b_iYSQ (a_a1ulD :: a_iYSP) (a_a1ulE :: First b_iYSQ) :: First a_iYSP where
  TFHelper_6989586621679364779 @a_iYSP @b_iYSQ _z_6989586621679363048_a1ulI ('First a_6989586621679363052_a1ulJ) = Apply FirstSym0 (Apply (LamCases_6989586621679364788Sym0 _z_6989586621679363048_a1ulI a_6989586621679363052_a1ulJ) a_6989586621679363052_a1ulJ)
instance PFunctor First where
  type Fmap a_a1ulo a_a1ulp = Fmap_6989586621679364768 a_a1ulo a_a1ulp
  type (<$) a_a1ulz a_a1ulA = TFHelper_6989586621679364779 a_a1ulz a_a1ulA
type TFHelper_6989586621679364795 :: forall a_iv98
                                            b_iv99. First a_iv98 -> First b_iv99 -> First b_iv99
type family TFHelper_6989586621679364795 @a_iv98 @b_iv99 (a_a1ulX :: First a_iv98) (a_a1ulY :: First b_iv99) :: First b_iv99 where
  TFHelper_6989586621679364795 @a_iv98 @b_iv99 a_6989586621679364797_a1um2 a_6989586621679364799_a1um3 = Apply (Apply (*>@#@$) a_6989586621679364797_a1um2) a_6989586621679364799_a1um3
type TFHelper_6989586621679364810 :: forall a_iv94
                                            b_iv95. First a_iv94
                                                    -> (~>) a_iv94 (First b_iv95)
                                                        -> First b_iv95
type family TFHelper_6989586621679364810 @a_iv94 @b_iv95 (a_a1um8 :: First a_iv94) (a_a1um9 :: (~>) a_iv94 (First b_iv95)) :: First b_iv95 where
  TFHelper_6989586621679364810 @a_iv94 @b_iv95 ('First a_a1umd) f_a1ume = Apply f_a1ume a_a1umd
instance PMonad First where
  type (>>) a_a1ulP a_a1ulQ = TFHelper_6989586621679364795 a_a1ulP a_a1ulQ
  type (>>=) a_a1um4 a_a1um5 = TFHelper_6989586621679364810 a_a1um4 a_a1um5
type TFHelper_6989586621679364821 :: forall a_a1tOw. First a_a1tOw
                                                      -> First a_a1tOw -> First a_a1tOw
type family TFHelper_6989586621679364821 @a_a1tOw (a_a1umj :: First a_a1tOw) (a_a1umk :: First a_a1tOw) :: First a_a1tOw where
  TFHelper_6989586621679364821 @a_a1tOw (a_a1umo :: First a_a1tOw) (_ :: First a_a1tOw) = a_a1umo
instance PSemigroup (First a_a1tOw) where
  type (<>) a_a1umf a_a1umg = TFHelper_6989586621679364821 a_a1umf a_a1umg
type FoldMap_6989586621679364831 :: forall a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU -> First a_iYVT -> m_iYVU
type family FoldMap_6989586621679364831 @a_iYVT @m_iYVU (a_a1umt :: (~>) a_iYVT m_iYVU) (a_a1umu :: First a_iYVT) :: m_iYVU where
  FoldMap_6989586621679364831 @a_iYVT @m_iYVU _f_6989586621679363055_a1umy ('First a_6989586621679363059_a1umz) = Apply _f_6989586621679363055_a1umy a_6989586621679363059_a1umz
type Foldr_6989586621679364843 :: forall a_iYVX
                                          b_iYVY. (~>) a_iYVX ((~>) b_iYVY b_iYVY)
                                                  -> b_iYVY -> First a_iYVX -> b_iYVY
type family Foldr_6989586621679364843 @a_iYVX @b_iYVY (a_a1umF :: (~>) a_iYVX ((~>) b_iYVY b_iYVY)) (a_a1umG :: b_iYVY) (a_a1umH :: First a_iYVX) :: b_iYVY where
  Foldr_6989586621679364843 @a_iYVX @b_iYVY _f_6989586621679363055_a1umM _z_6989586621679363057_a1umN ('First a_6989586621679363061_a1umO) = Apply (Apply _f_6989586621679363055_a1umM a_6989586621679363061_a1umO) _z_6989586621679363057_a1umN
instance PFoldable First where
  type FoldMap a_a1ump a_a1umq = FoldMap_6989586621679364831 a_a1ump a_a1umq
  type Foldr a_a1umA a_a1umB a_a1umC = Foldr_6989586621679364843 a_a1umA a_a1umB a_a1umC
type Traverse_6989586621679364857 :: forall a_i1u58
                                            f_i1u59
                                            b_i1u5a. (~>) a_i1u58 (f_i1u59 b_i1u5a)
                                                      -> First a_i1u58 -> f_i1u59 (First b_i1u5a)
type family Traverse_6989586621679364857 @a_i1u58 @f_i1u59 @b_i1u5a (a_a1umT :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) (a_a1umU :: First a_i1u58) :: f_i1u59 (First b_i1u5a) where
  Traverse_6989586621679364857 @a_i1u58 @f_i1u59 @b_i1u5a _f_6989586621679363064_a1umY ('First a_6989586621679363066_a1umZ) = Apply (Apply FmapSym0 FirstSym0) (Apply _f_6989586621679363064_a1umY a_6989586621679363066_a1umZ)
instance PTraversable First where
  type Traverse a_a1umP a_a1umQ = Traverse_6989586621679364857 a_a1umP a_a1umQ
type Pure_6989586621679364867 :: forall a_iv9m. a_iv9m
                                                -> Last a_iv9m
type family Pure_6989586621679364867 @a_iv9m (a_a1un3 :: a_iv9m) :: Last a_iv9m where
  Pure_6989586621679364867 @a_iv9m x_a1un6 = Apply LastSym0 x_a1un6
type TFHelper_6989586621679364875 :: forall a_iv9C
                                            b_iv9D. Last a_iv9C -> Last b_iv9D -> Last a_iv9C
type family TFHelper_6989586621679364875 @a_iv9C @b_iv9D (a_a1unb :: Last a_iv9C) (a_a1unc :: Last b_iv9D) :: Last a_iv9C where
  TFHelper_6989586621679364875 @a_iv9C @b_iv9D a_a1ung _ = a_a1ung
type TFHelper_6989586621679364885 :: forall a_iv9y
                                            b_iv9z. Last a_iv9y -> Last b_iv9z -> Last b_iv9z
type family TFHelper_6989586621679364885 @a_iv9y @b_iv9z (a_a1unl :: Last a_iv9y) (a_a1unm :: Last b_iv9z) :: Last b_iv9z where
  TFHelper_6989586621679364885 @a_iv9y @b_iv9z _ a_a1unq = a_a1unq
type TFHelper_6989586621679364895 :: forall a_iv9o
                                            b_iv9p. Last ((~>) a_iv9o b_iv9p)
                                                    -> Last a_iv9o -> Last b_iv9p
type family TFHelper_6989586621679364895 @a_iv9o @b_iv9p (a_a1unv :: Last ((~>) a_iv9o b_iv9p)) (a_a1unw :: Last a_iv9o) :: Last b_iv9p where
  TFHelper_6989586621679364895 @a_iv9o @b_iv9p ('Last f_a1unA) ('Last x_a1unB) = Apply LastSym0 (Apply f_a1unA x_a1unB)
type LiftA2_6989586621679364907 :: forall a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> Last a_iv9s -> Last b_iv9t -> Last c_iv9u
type family LiftA2_6989586621679364907 @a_iv9s @b_iv9t @c_iv9u (a_a1unH :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a1unI :: Last a_iv9s) (a_a1unJ :: Last b_iv9t) :: Last c_iv9u where
  LiftA2_6989586621679364907 @a_iv9s @b_iv9t @c_iv9u f_a1unO ('Last a_a1unP) ('Last b_a1unQ) = Apply LastSym0 (Apply (Apply f_a1unO a_a1unP) b_a1unQ)
instance PApplicative Last where
  type Pure a_a1un0 = Pure_6989586621679364867 a_a1un0
  type (<*) a_a1un7 a_a1un8 = TFHelper_6989586621679364875 a_a1un7 a_a1un8
  type (*>) a_a1unh a_a1uni = TFHelper_6989586621679364885 a_a1unh a_a1uni
  type (<*>) a_a1unr a_a1uns = TFHelper_6989586621679364895 a_a1unr a_a1uns
  type LiftA2 a_a1unC a_a1unD a_a1unE = LiftA2_6989586621679364907 a_a1unC a_a1unD a_a1unE
type Succ_6989586621679364920 :: forall a_a1tOG. Last a_a1tOG
                                                  -> Last a_a1tOG
type family Succ_6989586621679364920 @a_a1tOG (a_a1unU :: Last a_a1tOG) :: Last a_a1tOG where
  Succ_6989586621679364920 @a_a1tOG ('Last a_a1unX :: Last a_a1tOG) = Apply LastSym0 (Apply SuccSym0 a_a1unX)
type Pred_6989586621679364927 :: forall a_a1tOG. Last a_a1tOG
                                                  -> Last a_a1tOG
type family Pred_6989586621679364927 @a_a1tOG (a_a1uo1 :: Last a_a1tOG) :: Last a_a1tOG where
  Pred_6989586621679364927 @a_a1tOG ('Last a_a1uo4 :: Last a_a1tOG) = Apply LastSym0 (Apply PredSym0 a_a1uo4)
type ToEnum_6989586621679364934 :: forall a_a1tOG. GHC.Num.Natural.Natural
                                                    -> Last a_a1tOG
type family ToEnum_6989586621679364934 @a_a1tOG (a_a1uoa :: GHC.Num.Natural.Natural) :: Last a_a1tOG where
  ToEnum_6989586621679364934 @a_a1tOG (a_6989586621679364936_a1uod :: GHC.Num.Natural.Natural) = Apply (Apply (Apply (.@#@$) LastSym0) ToEnumSym0) a_6989586621679364936_a1uod
type FromEnum_6989586621679364943 :: forall a_a1tOG. Last a_a1tOG
                                                      -> GHC.Num.Natural.Natural
type family FromEnum_6989586621679364943 @a_a1tOG (a_a1uoh :: Last a_a1tOG) :: GHC.Num.Natural.Natural where
  FromEnum_6989586621679364943 @a_a1tOG ('Last a_a1uok :: Last a_a1tOG) = Apply FromEnumSym0 a_a1uok
type EnumFromTo_6989586621679364951 :: forall a_a1tOG. Last a_a1tOG
                                                        -> Last a_a1tOG -> [Last a_a1tOG]
type family EnumFromTo_6989586621679364951 @a_a1tOG (a_a1uop :: Last a_a1tOG) (a_a1uoq :: Last a_a1tOG) :: [Last a_a1tOG] where
  EnumFromTo_6989586621679364951 @a_a1tOG ('Last a_a1uou :: Last a_a1tOG) ('Last b_a1uov :: Last a_a1tOG) = Apply (Apply MapSym0 LastSym0) (Apply (Apply EnumFromToSym0 a_a1uou) b_a1uov)
type EnumFromThenTo_6989586621679364963 :: forall a_a1tOG. Last a_a1tOG
                                                            -> Last a_a1tOG
                                                              -> Last a_a1tOG -> [Last a_a1tOG]
type family EnumFromThenTo_6989586621679364963 @a_a1tOG (a_a1uoB :: Last a_a1tOG) (a_a1uoC :: Last a_a1tOG) (a_a1uoD :: Last a_a1tOG) :: [Last a_a1tOG] where
  EnumFromThenTo_6989586621679364963 @a_a1tOG ('Last a_a1uoI :: Last a_a1tOG) ('Last b_a1uoJ :: Last a_a1tOG) ('Last c_a1uoK :: Last a_a1tOG) = Apply (Apply MapSym0 LastSym0) (Apply (Apply (Apply EnumFromThenToSym0 a_a1uoI) b_a1uoJ) c_a1uoK)
instance PEnum (Last a_a1tOG) where
  type Succ a_a1unR = Succ_6989586621679364920 a_a1unR
  type Pred a_a1unY = Pred_6989586621679364927 a_a1unY
  type ToEnum a_a1uo5 = ToEnum_6989586621679364934 a_a1uo5
  type FromEnum a_a1uoe = FromEnum_6989586621679364943 a_a1uoe
  type EnumFromTo a_a1uol a_a1uom = EnumFromTo_6989586621679364951 a_a1uol a_a1uom
  type EnumFromThenTo a_a1uow a_a1uox a_a1uoy = EnumFromThenTo_6989586621679364963 a_a1uow a_a1uox a_a1uoy
type Fmap_6989586621679364977 :: forall a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM -> Last a_iYSL -> Last b_iYSM
type family Fmap_6989586621679364977 @a_iYSL @b_iYSM (a_a1uoP :: (~>) a_iYSL b_iYSM) (a_a1uoQ :: Last a_iYSL) :: Last b_iYSM where
  Fmap_6989586621679364977 @a_iYSL @b_iYSM _f_6989586621679363069_a1uoU ('Last a_6989586621679363073_a1uoV) = Apply LastSym0 (Apply _f_6989586621679363069_a1uoU a_6989586621679363073_a1uoV)
type family LamCases_6989586621679364997_a1up8 (_z_69895866216793630716989586621679364995 :: a7566047373982667319) a_69895866216793630756989586621679364996 a_6989586621679364999_a1upa where
  LamCases_6989586621679364997_a1up8 _z_6989586621679363071_a1up5 a_6989586621679363075_a1up6 _ = _z_6989586621679363071_a1up5
data LamCases_6989586621679364997Sym0 (_z_69895866216793630716989586621679364995 :: a7566047373982667319) a_69895866216793630756989586621679364996 a_69895866216793649996989586621679365000
  where
    LamCases_6989586621679364997Sym0KindInference :: SameKind (Apply (LamCases_6989586621679364997Sym0 _z_69895866216793630716989586621679364995 a_69895866216793630756989586621679364996) arg_a1upb) (LamCases_6989586621679364997Sym1 _z_69895866216793630716989586621679364995 a_69895866216793630756989586621679364996 arg_a1upb) =>
                                                      LamCases_6989586621679364997Sym0 _z_69895866216793630716989586621679364995 a_69895866216793630756989586621679364996 a_69895866216793649996989586621679365000
type instance Apply @_ @_ (LamCases_6989586621679364997Sym0 _z_69895866216793630716989586621679364995 a_69895866216793630756989586621679364996) a_69895866216793649996989586621679365000 = LamCases_6989586621679364997_a1up8 _z_69895866216793630716989586621679364995 a_69895866216793630756989586621679364996 a_69895866216793649996989586621679365000
instance SuppressUnusedWarnings (LamCases_6989586621679364997Sym0 _z_69895866216793630716989586621679364995 a_69895866216793630756989586621679364996) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679364997Sym0KindInference ())
type family LamCases_6989586621679364997Sym1 (_z_69895866216793630716989586621679364995 :: a7566047373982667319) a_69895866216793630756989586621679364996 a_69895866216793649996989586621679365000 where
  LamCases_6989586621679364997Sym1 _z_69895866216793630716989586621679364995 a_69895866216793630756989586621679364996 a_69895866216793649996989586621679365000 = LamCases_6989586621679364997_a1up8 _z_69895866216793630716989586621679364995 a_69895866216793630756989586621679364996 a_69895866216793649996989586621679365000
type TFHelper_6989586621679364988 :: forall a_iYSP b_iYSQ. a_iYSP
                                                            -> Last b_iYSQ -> Last a_iYSP
type family TFHelper_6989586621679364988 @a_iYSP @b_iYSQ (a_a1up0 :: a_iYSP) (a_a1up1 :: Last b_iYSQ) :: Last a_iYSP where
  TFHelper_6989586621679364988 @a_iYSP @b_iYSQ _z_6989586621679363071_a1up5 ('Last a_6989586621679363075_a1up6) = Apply LastSym0 (Apply (LamCases_6989586621679364997Sym0 _z_6989586621679363071_a1up5 a_6989586621679363075_a1up6) a_6989586621679363075_a1up6)
instance PFunctor Last where
  type Fmap a_a1uoL a_a1uoM = Fmap_6989586621679364977 a_a1uoL a_a1uoM
  type (<$) a_a1uoW a_a1uoX = TFHelper_6989586621679364988 a_a1uoW a_a1uoX
type TFHelper_6989586621679365004 :: forall a_iv98
                                            b_iv99. Last a_iv98 -> Last b_iv99 -> Last b_iv99
type family TFHelper_6989586621679365004 @a_iv98 @b_iv99 (a_a1upk :: Last a_iv98) (a_a1upl :: Last b_iv99) :: Last b_iv99 where
  TFHelper_6989586621679365004 @a_iv98 @b_iv99 a_6989586621679365006_a1upp a_6989586621679365008_a1upq = Apply (Apply (*>@#@$) a_6989586621679365006_a1upp) a_6989586621679365008_a1upq
type TFHelper_6989586621679365019 :: forall a_iv94
                                            b_iv95. Last a_iv94
                                                    -> (~>) a_iv94 (Last b_iv95) -> Last b_iv95
type family TFHelper_6989586621679365019 @a_iv94 @b_iv95 (a_a1upv :: Last a_iv94) (a_a1upw :: (~>) a_iv94 (Last b_iv95)) :: Last b_iv95 where
  TFHelper_6989586621679365019 @a_iv94 @b_iv95 ('Last a_a1upA) f_a1upB = Apply f_a1upB a_a1upA
instance PMonad Last where
  type (>>) a_a1upc a_a1upd = TFHelper_6989586621679365004 a_a1upc a_a1upd
  type (>>=) a_a1upr a_a1ups = TFHelper_6989586621679365019 a_a1upr a_a1ups
type TFHelper_6989586621679365030 :: forall a_a1tOR. Last a_a1tOR
                                                      -> Last a_a1tOR -> Last a_a1tOR
type family TFHelper_6989586621679365030 @a_a1tOR (a_a1upG :: Last a_a1tOR) (a_a1upH :: Last a_a1tOR) :: Last a_a1tOR where
  TFHelper_6989586621679365030 @a_a1tOR (_ :: Last a_a1tOR) (b_a1upL :: Last a_a1tOR) = b_a1upL
instance PSemigroup (Last a_a1tOR) where
  type (<>) a_a1upC a_a1upD = TFHelper_6989586621679365030 a_a1upC a_a1upD
type FoldMap_6989586621679365040 :: forall a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU -> Last a_iYVT -> m_iYVU
type family FoldMap_6989586621679365040 @a_iYVT @m_iYVU (a_a1upQ :: (~>) a_iYVT m_iYVU) (a_a1upR :: Last a_iYVT) :: m_iYVU where
  FoldMap_6989586621679365040 @a_iYVT @m_iYVU _f_6989586621679363078_a1upV ('Last a_6989586621679363082_a1upW) = Apply _f_6989586621679363078_a1upV a_6989586621679363082_a1upW
type Foldr_6989586621679365052 :: forall a_iYVX
                                          b_iYVY. (~>) a_iYVX ((~>) b_iYVY b_iYVY)
                                                  -> b_iYVY -> Last a_iYVX -> b_iYVY
type family Foldr_6989586621679365052 @a_iYVX @b_iYVY (a_a1uq2 :: (~>) a_iYVX ((~>) b_iYVY b_iYVY)) (a_a1uq3 :: b_iYVY) (a_a1uq4 :: Last a_iYVX) :: b_iYVY where
  Foldr_6989586621679365052 @a_iYVX @b_iYVY _f_6989586621679363078_a1uq9 _z_6989586621679363080_a1uqa ('Last a_6989586621679363084_a1uqb) = Apply (Apply _f_6989586621679363078_a1uq9 a_6989586621679363084_a1uqb) _z_6989586621679363080_a1uqa
instance PFoldable Last where
  type FoldMap a_a1upM a_a1upN = FoldMap_6989586621679365040 a_a1upM a_a1upN
  type Foldr a_a1upX a_a1upY a_a1upZ = Foldr_6989586621679365052 a_a1upX a_a1upY a_a1upZ
type Traverse_6989586621679365066 :: forall a_i1u58
                                            f_i1u59
                                            b_i1u5a. (~>) a_i1u58 (f_i1u59 b_i1u5a)
                                                      -> Last a_i1u58 -> f_i1u59 (Last b_i1u5a)
type family Traverse_6989586621679365066 @a_i1u58 @f_i1u59 @b_i1u5a (a_a1uqg :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) (a_a1uqh :: Last a_i1u58) :: f_i1u59 (Last b_i1u5a) where
  Traverse_6989586621679365066 @a_i1u58 @f_i1u59 @b_i1u5a _f_6989586621679363087_a1uql ('Last a_6989586621679363089_a1uqm) = Apply (Apply FmapSym0 LastSym0) (Apply _f_6989586621679363087_a1uql a_6989586621679363089_a1uqm)
instance PTraversable Last where
  type Traverse a_a1uqc a_a1uqd = Traverse_6989586621679365066 a_a1uqc a_a1uqd
type TFHelper_6989586621679365077 :: forall m_a1tOT. WrappedMonoid m_a1tOT
                                                      -> WrappedMonoid m_a1tOT
                                                        -> WrappedMonoid m_a1tOT
type family TFHelper_6989586621679365077 @m_a1tOT (a_a1uqr :: WrappedMonoid m_a1tOT) (a_a1uqs :: WrappedMonoid m_a1tOT) :: WrappedMonoid m_a1tOT where
  TFHelper_6989586621679365077 @m_a1tOT ('WrapMonoid a_a1uqw :: WrappedMonoid m_a1tOT) ('WrapMonoid b_a1uqx :: WrappedMonoid m_a1tOT) = Apply WrapMonoidSym0 (Apply (Apply MappendSym0 a_a1uqw) b_a1uqx)
instance PSemigroup (WrappedMonoid m_a1tOT) where
  type (<>) a_a1uqn a_a1uqo = TFHelper_6989586621679365077 a_a1uqn a_a1uqo
type Mempty_6989586621679365086 :: forall m_a1tOW. WrappedMonoid m_a1tOW
type family Mempty_6989586621679365086 @m_a1tOW :: WrappedMonoid m_a1tOW where
  Mempty_6989586621679365086 @m_a1tOW = Apply WrapMonoidSym0 MemptySym0
instance PMonoid (WrappedMonoid m_a1tOW) where
  type Mempty = Mempty_6989586621679365086
type Succ_6989586621679365090 :: forall a_a1tOX. WrappedMonoid a_a1tOX
                                                  -> WrappedMonoid a_a1tOX
type family Succ_6989586621679365090 @a_a1tOX (a_a1uqE :: WrappedMonoid a_a1tOX) :: WrappedMonoid a_a1tOX where
  Succ_6989586621679365090 @a_a1tOX ('WrapMonoid a_a1uqH :: WrappedMonoid a_a1tOX) = Apply WrapMonoidSym0 (Apply SuccSym0 a_a1uqH)
type Pred_6989586621679365097 :: forall a_a1tOX. WrappedMonoid a_a1tOX
                                                  -> WrappedMonoid a_a1tOX
type family Pred_6989586621679365097 @a_a1tOX (a_a1uqL :: WrappedMonoid a_a1tOX) :: WrappedMonoid a_a1tOX where
  Pred_6989586621679365097 @a_a1tOX ('WrapMonoid a_a1uqO :: WrappedMonoid a_a1tOX) = Apply WrapMonoidSym0 (Apply PredSym0 a_a1uqO)
type ToEnum_6989586621679365104 :: forall a_a1tOX. GHC.Num.Natural.Natural
                                                    -> WrappedMonoid a_a1tOX
type family ToEnum_6989586621679365104 @a_a1tOX (a_a1uqU :: GHC.Num.Natural.Natural) :: WrappedMonoid a_a1tOX where
  ToEnum_6989586621679365104 @a_a1tOX (a_6989586621679365106_a1uqX :: GHC.Num.Natural.Natural) = Apply (Apply (Apply (.@#@$) WrapMonoidSym0) ToEnumSym0) a_6989586621679365106_a1uqX
type FromEnum_6989586621679365113 :: forall a_a1tOX. WrappedMonoid a_a1tOX
                                                      -> GHC.Num.Natural.Natural
type family FromEnum_6989586621679365113 @a_a1tOX (a_a1ur1 :: WrappedMonoid a_a1tOX) :: GHC.Num.Natural.Natural where
  FromEnum_6989586621679365113 @a_a1tOX ('WrapMonoid a_a1ur4 :: WrappedMonoid a_a1tOX) = Apply FromEnumSym0 a_a1ur4
type EnumFromTo_6989586621679365121 :: forall a_a1tOX. WrappedMonoid a_a1tOX
                                                        -> WrappedMonoid a_a1tOX
                                                          -> [WrappedMonoid a_a1tOX]
type family EnumFromTo_6989586621679365121 @a_a1tOX (a_a1ur9 :: WrappedMonoid a_a1tOX) (a_a1ura :: WrappedMonoid a_a1tOX) :: [WrappedMonoid a_a1tOX] where
  EnumFromTo_6989586621679365121 @a_a1tOX ('WrapMonoid a_a1ure :: WrappedMonoid a_a1tOX) ('WrapMonoid b_a1urf :: WrappedMonoid a_a1tOX) = Apply (Apply MapSym0 WrapMonoidSym0) (Apply (Apply EnumFromToSym0 a_a1ure) b_a1urf)
type EnumFromThenTo_6989586621679365133 :: forall a_a1tOX. WrappedMonoid a_a1tOX
                                                            -> WrappedMonoid a_a1tOX
                                                              -> WrappedMonoid a_a1tOX
                                                                  -> [WrappedMonoid a_a1tOX]
type family EnumFromThenTo_6989586621679365133 @a_a1tOX (a_a1url :: WrappedMonoid a_a1tOX) (a_a1urm :: WrappedMonoid a_a1tOX) (a_a1urn :: WrappedMonoid a_a1tOX) :: [WrappedMonoid a_a1tOX] where
  EnumFromThenTo_6989586621679365133 @a_a1tOX ('WrapMonoid a_a1urs :: WrappedMonoid a_a1tOX) ('WrapMonoid b_a1urt :: WrappedMonoid a_a1tOX) ('WrapMonoid c_a1uru :: WrappedMonoid a_a1tOX) = Apply (Apply MapSym0 WrapMonoidSym0) (Apply (Apply (Apply EnumFromThenToSym0 a_a1urs) b_a1urt) c_a1uru)
instance PEnum (WrappedMonoid a_a1tOX) where
  type Succ a_a1uqB = Succ_6989586621679365090 a_a1uqB
  type Pred a_a1uqI = Pred_6989586621679365097 a_a1uqI
  type ToEnum a_a1uqP = ToEnum_6989586621679365104 a_a1uqP
  type FromEnum a_a1uqY = FromEnum_6989586621679365113 a_a1uqY
  type EnumFromTo a_a1ur5 a_a1ur6 = EnumFromTo_6989586621679365121 a_a1ur5 a_a1ur6
  type EnumFromThenTo a_a1urg a_a1urh a_a1uri = EnumFromThenTo_6989586621679365133 a_a1urg a_a1urh a_a1uri
instance SApplicative Semi.Min where
  sPure (sA_6989586621679363178 :: Sing a_6989586621679363178_a1tVR)
    = applySing (singFun1 @MinSym0 SMin) sA_6989586621679363178
  (%<*) (sA :: Sing a_a1tW1) _ = sA
  (%*>) _ (sA :: Sing a_a1tWb) = sA
  (%<*>) (SMin (sF :: Sing f_a1tWl)) (SMin (sX :: Sing x_a1tWm))
    = applySing (singFun1 @MinSym0 SMin) (applySing sF sX)
  sLiftA2
    (sF :: Sing f_a1tWz)
    (SMin (sA :: Sing a_a1tWA))
    (SMin (sB :: Sing b_a1tWB))
    = applySing
        (singFun1 @MinSym0 SMin) (applySing (applySing sF sA) sB)
instance SEnum a_a1tMX => SEnum (Semi.Min a_a1tMX) where
  sSucc (SMin (sA :: Sing a_a1tXM))
    = applySing
        (singFun1 @MinSym0 SMin) (applySing (singFun1 @SuccSym0 sSucc) sA)
  sPred (SMin (sA :: Sing a_a1tXT))
    = applySing
        (singFun1 @MinSym0 SMin) (applySing (singFun1 @PredSym0 sPred) sA)
  sToEnum
    (sA_6989586621679363313 :: Sing a_6989586621679363313_a1tY2)
    = applySing
        (applySing
            (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @MinSym0 SMin))
            (singFun1 @ToEnumSym0 sToEnum))
        sA_6989586621679363313
  sFromEnum (SMin (sA :: Sing a_a1tY9))
    = applySing (singFun1 @FromEnumSym0 sFromEnum) sA
  sEnumFromTo (SMin (sA :: Sing a_a1tYj)) (SMin (sB :: Sing b_a1tYk))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @MinSym0 SMin))
        (applySing
            (applySing (singFun2 @EnumFromToSym0 sEnumFromTo) sA) sB)
  sEnumFromThenTo
    (SMin (sA :: Sing a_a1tYx))
    (SMin (sB :: Sing b_a1tYy))
    (SMin (sC :: Sing c_a1tYz))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @MinSym0 SMin))
        (applySing
            (applySing
              (applySing (singFun3 @EnumFromThenToSym0 sEnumFromThenTo) sA) sB)
            sC)
instance SFunctor Semi.Min where
  sFmap
    (_sf_6989586621679362950 :: Sing _f_6989586621679362950_a1tZh)
    (SMin (sA_6989586621679362954 :: Sing a_6989586621679362954_a1tZi))
    = applySing
        (singFun1 @MinSym0 SMin)
        (applySing _sf_6989586621679362950 sA_6989586621679362954)
  (%<$)
    (_sz_6989586621679362952 :: Sing _z_6989586621679362952_a1tZs)
    (SMin (sA_6989586621679362956 :: Sing a_6989586621679362956_a1tZt))
    = applySing
        (singFun1 @MinSym0 SMin)
        (applySing
            (singFun1
              @(LamCases_6989586621679363408Sym0 _z_6989586621679362952_a1tZs a_6989586621679362956_a1tZt)
              (\cases _ -> _sz_6989586621679362952))
            sA_6989586621679362956)
instance SMonad Semi.Min where
  (%>>)
    (sA_6989586621679363431 :: Sing a_6989586621679363431_a1u00)
    (sA_6989586621679363433 :: Sing a_6989586621679363433_a1u01)
    = applySing
        (applySing (singFun2 @(*>@#@$) (%*>)) sA_6989586621679363431)
        sA_6989586621679363433
  (%>>=) (SMin (sA :: Sing a_a1u0b)) (sF :: Sing f_a1u0c)
    = applySing sF sA
instance SOrd a_a1tN8 => SSemigroup (Semi.Min a_a1tN8) where
  (%<>) (SMin (sA :: Sing a_a1u0M)) (SMin (sB :: Sing b_a1u0N))
    = applySing
        (singFun1 @MinSym0 SMin)
        (applySing (applySing (singFun2 @Min_Sym0 sMin_) sA) sB)
instance (SOrd a_a1tNb, SBounded a_a1tNb) =>
          SMonoid (Semi.Min a_a1tNb) where
  sMempty = sMaxBound
instance SNum a_a1tNc => SNum (Semi.Min a_a1tNc) where
  (%+) (SMin (sA :: Sing a_a1u2z)) (SMin (sB :: Sing b_a1u2A))
    = applySing
        (singFun1 @MinSym0 SMin)
        (applySing (applySing (singFun2 @(+@#@$) (%+)) sA) sB)
  (%*) (SMin (sA :: Sing a_a1u2K)) (SMin (sB :: Sing b_a1u2L))
    = applySing
        (singFun1 @MinSym0 SMin)
        (applySing (applySing (singFun2 @(*@#@$) (%*)) sA) sB)
  (%-) (SMin (sA :: Sing a_a1u2V)) (SMin (sB :: Sing b_a1u2W))
    = applySing
        (singFun1 @MinSym0 SMin)
        (applySing (applySing (singFun2 @(-@#@$) (%-)) sA) sB)
  sNegate (SMin (sA :: Sing a_a1u33))
    = applySing
        (singFun1 @MinSym0 SMin)
        (applySing (singFun1 @NegateSym0 sNegate) sA)
  sAbs (SMin (sA :: Sing a_a1u3a))
    = applySing
        (singFun1 @MinSym0 SMin) (applySing (singFun1 @AbsSym0 sAbs) sA)
  sSignum (SMin (sA :: Sing a_a1u3h))
    = applySing
        (singFun1 @MinSym0 SMin)
        (applySing (singFun1 @SignumSym0 sSignum) sA)
  sFromInteger
    (sA_6989586621679363647 :: Sing a_6989586621679363647_a1u3q)
    = applySing
        (applySing
            (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @MinSym0 SMin))
            (singFun1 @FromIntegerSym0 sFromInteger))
        sA_6989586621679363647
instance SFoldable Semi.Min where
  sFoldMap
    (_sf_6989586621679362959 :: Sing _f_6989586621679362959_a1u4Q)
    (SMin (sA_6989586621679362963 :: Sing a_6989586621679362963_a1u4R))
    = applySing _sf_6989586621679362959 sA_6989586621679362963
  sFoldr
    (_sf_6989586621679362959 :: Sing _f_6989586621679362959_a1u54)
    (_sz_6989586621679362961 :: Sing _z_6989586621679362961_a1u55)
    (SMin (sA_6989586621679362965 :: Sing a_6989586621679362965_a1u56))
    = applySing
        (applySing _sf_6989586621679362959 sA_6989586621679362965)
        _sz_6989586621679362961
instance STraversable Semi.Min where
  sTraverse
    (_sf_6989586621679362968 :: Sing _f_6989586621679362968_a1uaM)
    (SMin (sA_6989586621679362970 :: Sing a_6989586621679362970_a1uaN))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @MinSym0 SMin))
        (applySing _sf_6989586621679362968 sA_6989586621679362970)
instance SApplicative Semi.Max where
  sPure (sA_6989586621679364113 :: Sing a_6989586621679364113_a1uaW)
    = applySing (singFun1 @MaxSym0 SMax) sA_6989586621679364113
  (%<*) (sA :: Sing a_a1ub6) _ = sA
  (%*>) _ (sA :: Sing a_a1ubg) = sA
  (%<*>) (SMax (sF :: Sing f_a1ubq)) (SMax (sX :: Sing x_a1ubr))
    = applySing (singFun1 @MaxSym0 SMax) (applySing sF sX)
  sLiftA2
    (sF :: Sing f_a1ubE)
    (SMax (sA :: Sing a_a1ubF))
    (SMax (sB :: Sing b_a1ubG))
    = applySing
        (singFun1 @MaxSym0 SMax) (applySing (applySing sF sA) sB)
instance SEnum a_a1tNt => SEnum (Semi.Max a_a1tNt) where
  sSucc (SMax (sA :: Sing a_a1ubN))
    = applySing
        (singFun1 @MaxSym0 SMax) (applySing (singFun1 @SuccSym0 sSucc) sA)
  sPred (SMax (sA :: Sing a_a1ubU))
    = applySing
        (singFun1 @MaxSym0 SMax) (applySing (singFun1 @PredSym0 sPred) sA)
  sToEnum
    (sA_6989586621679364182 :: Sing a_6989586621679364182_a1uc3)
    = applySing
        (applySing
            (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @MaxSym0 SMax))
            (singFun1 @ToEnumSym0 sToEnum))
        sA_6989586621679364182
  sFromEnum (SMax (sA :: Sing a_a1uca))
    = applySing (singFun1 @FromEnumSym0 sFromEnum) sA
  sEnumFromTo (SMax (sA :: Sing a_a1uck)) (SMax (sB :: Sing b_a1ucl))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @MaxSym0 SMax))
        (applySing
            (applySing (singFun2 @EnumFromToSym0 sEnumFromTo) sA) sB)
  sEnumFromThenTo
    (SMax (sA :: Sing a_a1ucy))
    (SMax (sB :: Sing b_a1ucz))
    (SMax (sC :: Sing c_a1ucA))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @MaxSym0 SMax))
        (applySing
            (applySing
              (applySing (singFun3 @EnumFromThenToSym0 sEnumFromThenTo) sA) sB)
            sC)
instance SFunctor Semi.Max where
  sFmap
    (_sf_6989586621679362973 :: Sing _f_6989586621679362973_a1ucK)
    (SMax (sA_6989586621679362977 :: Sing a_6989586621679362977_a1ucL))
    = applySing
        (singFun1 @MaxSym0 SMax)
        (applySing _sf_6989586621679362973 sA_6989586621679362977)
  (%<$)
    (_sz_6989586621679362975 :: Sing _z_6989586621679362975_a1ucV)
    (SMax (sA_6989586621679362979 :: Sing a_6989586621679362979_a1ucW))
    = applySing
        (singFun1 @MaxSym0 SMax)
        (applySing
            (singFun1
              @(LamCases_6989586621679364243Sym0 _z_6989586621679362975_a1ucV a_6989586621679362979_a1ucW)
              (\cases _ -> _sz_6989586621679362975))
            sA_6989586621679362979)
instance SMonad Semi.Max where
  (%>>)
    (sA_6989586621679364252 :: Sing a_6989586621679364252_a1udf)
    (sA_6989586621679364254 :: Sing a_6989586621679364254_a1udg)
    = applySing
        (applySing (singFun2 @(*>@#@$) (%*>)) sA_6989586621679364252)
        sA_6989586621679364254
  (%>>=) (SMax (sA :: Sing a_a1udq)) (sF :: Sing f_a1udr)
    = applySing sF sA
instance SOrd a_a1tNE => SSemigroup (Semi.Max a_a1tNE) where
  (%<>) (SMax (sA :: Sing a_a1udB)) (SMax (sB :: Sing b_a1udC))
    = applySing
        (singFun1 @MaxSym0 SMax)
        (applySing (applySing (singFun2 @Max_Sym0 sMax_) sA) sB)
instance (SOrd a_a1tNH, SBounded a_a1tNH) =>
          SMonoid (Semi.Max a_a1tNH) where
  sMempty = sMinBound
instance SNum a_a1tNI => SNum (Semi.Max a_a1tNI) where
  (%+) (SMax (sA :: Sing a_a1udP)) (SMax (sB :: Sing b_a1udQ))
    = applySing
        (singFun1 @MaxSym0 SMax)
        (applySing (applySing (singFun2 @(+@#@$) (%+)) sA) sB)
  (%*) (SMax (sA :: Sing a_a1ue0)) (SMax (sB :: Sing b_a1ue1))
    = applySing
        (singFun1 @MaxSym0 SMax)
        (applySing (applySing (singFun2 @(*@#@$) (%*)) sA) sB)
  (%-) (SMax (sA :: Sing a_a1ueb)) (SMax (sB :: Sing b_a1uec))
    = applySing
        (singFun1 @MaxSym0 SMax)
        (applySing (applySing (singFun2 @(-@#@$) (%-)) sA) sB)
  sNegate (SMax (sA :: Sing a_a1uej))
    = applySing
        (singFun1 @MaxSym0 SMax)
        (applySing (singFun1 @NegateSym0 sNegate) sA)
  sAbs (SMax (sA :: Sing a_a1ueq))
    = applySing
        (singFun1 @MaxSym0 SMax) (applySing (singFun1 @AbsSym0 sAbs) sA)
  sSignum (SMax (sA :: Sing a_a1uex))
    = applySing
        (singFun1 @MaxSym0 SMax)
        (applySing (singFun1 @SignumSym0 sSignum) sA)
  sFromInteger
    (sA_6989586621679364345 :: Sing a_6989586621679364345_a1ueG)
    = applySing
        (applySing
            (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @MaxSym0 SMax))
            (singFun1 @FromIntegerSym0 sFromInteger))
        sA_6989586621679364345
instance SFoldable Semi.Max where
  sFoldMap
    (_sf_6989586621679362982 :: Sing _f_6989586621679362982_a1ueQ)
    (SMax (sA_6989586621679362986 :: Sing a_6989586621679362986_a1ueR))
    = applySing _sf_6989586621679362982 sA_6989586621679362986
  sFoldr
    (_sf_6989586621679362982 :: Sing _f_6989586621679362982_a1uf4)
    (_sz_6989586621679362984 :: Sing _z_6989586621679362984_a1uf5)
    (SMax (sA_6989586621679362988 :: Sing a_6989586621679362988_a1uf6))
    = applySing
        (applySing _sf_6989586621679362982 sA_6989586621679362988)
        _sz_6989586621679362984
instance STraversable Semi.Max where
  sTraverse
    (_sf_6989586621679362991 :: Sing _f_6989586621679362991_a1ufg)
    (SMax (sA_6989586621679362993 :: Sing a_6989586621679362993_a1ufh))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @MaxSym0 SMax))
        (applySing _sf_6989586621679362991 sA_6989586621679362993)
instance SEq a_a1tNS => SEq (Arg a_a1tNS b_a1tNT) where
  (%==) (SArg (sA :: Sing a_a1ufQ) _) (SArg (sB :: Sing b_a1ufR) _)
    = applySing (applySing (singFun2 @(==@#@$) (%==)) sA) sB
instance SFunctor (Arg a_a1tNW) where
  sFmap
    (_sf_6989586621679362997 :: Sing _f_6989586621679362997_a1ug1)
    (SArg (sA_6989586621679363003 :: Sing a_6989586621679363003_a1ug2)
          (sA_6989586621679363005 :: Sing a_6989586621679363005_a1ug3))
    = applySing
        (applySing
            (singFun2 @ArgSym0 SArg)
            (applySing
              (singFun1
                  @(LamCases_6989586621679364436Sym0 a_a1tNW _f_6989586621679362997_a1ug1 a_6989586621679363003_a1ug2 a_6989586621679363005_a1ug3)
                  (\cases
                    (sN_6989586621679363001 :: Sing n_6989586621679363001_a1ug6)
                      -> sN_6989586621679363001))
              sA_6989586621679363003))
        (applySing _sf_6989586621679362997 sA_6989586621679363005)
  (%<$)
    (_sz_6989586621679362999 :: Sing _z_6989586621679362999_a1ugj)
    (SArg (sA_6989586621679363009 :: Sing a_6989586621679363009_a1ugk)
          (sA_6989586621679363011 :: Sing a_6989586621679363011_a1ugl))
    = applySing
        (applySing
            (singFun2 @ArgSym0 SArg)
            (applySing
              (singFun1
                  @(LamCases_6989586621679364454Sym0 a_a1tNW _z_6989586621679362999_a1ugj a_6989586621679363009_a1ugk a_6989586621679363011_a1ugl)
                  (\cases
                    (sN_6989586621679363007 :: Sing n_6989586621679363007_a1ugo)
                      -> sN_6989586621679363007))
              sA_6989586621679363009))
        (applySing
            (singFun1
              @(LamCases_6989586621679364460Sym0 a_a1tNW _z_6989586621679362999_a1ugj a_6989586621679363009_a1ugk a_6989586621679363011_a1ugl)
              (\cases _ -> _sz_6989586621679362999))
            sA_6989586621679363011)
instance SOrd a_a1tNX => SOrd (Arg a_a1tNX b_a1tNY) where
  sCompare
    (SArg (sA :: Sing a_a1uhu) _)
    (SArg (sB :: Sing b_a1uhv) _)
    = applySing (applySing (singFun2 @CompareSym0 sCompare) sA) sB
  sMin
    (sArg_6989586621679362764 :: Sing arg_6989586621679362764_a1uhF)
    (sArg_6989586621679362766 :: Sing arg_6989586621679362766_a1uhG)
    = applySing
        (applySing
            (singFun2
              @(LamCases_6989586621679364537Sym0 a_a1tNX b_a1tNY arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG)
              (\cases
                  (SArg (sA :: Sing a_a1uhJ)
                        (sWild_6989586621679362768 :: Sing wild_6989586621679362768_a1uhK))
                    (SArg (sB :: Sing b_a1uhL)
                          (sWild_6989586621679362770 :: Sing wild_6989586621679362770_a1uhM))
                    -> let
                        sY ::
                          Sing @_ (Let6989586621679364543Y a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG)
                        sX ::
                          Sing @_ (Let6989586621679364543X a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG)
                        sY
                          = applySing
                              (applySing (singFun2 @ArgSym0 SArg) sB) sWild_6989586621679362770
                        sX
                          = applySing
                              (applySing (singFun2 @ArgSym0 SArg) sA) sWild_6989586621679362768
                      in
                        applySing
                          (singFun1
                              @(LamCases_6989586621679364546Sym0 a_a1tNX b_a1tNY a_a1uhJ wild_6989586621679362768_a1uhK b_a1uhL wild_6989586621679362770_a1uhM arg_6989586621679362764_a1uhF arg_6989586621679362766_a1uhG)
                              (\cases
                                STrue -> sX
                                SFalse -> sY))
                          (applySing (applySing (singFun2 @(<=@#@$) (%<=)) sA) sB)))
            sArg_6989586621679362764)
        sArg_6989586621679362766
  sMax
    (sArg_6989586621679362776 :: Sing arg_6989586621679362776_a1ui9)
    (sArg_6989586621679362778 :: Sing arg_6989586621679362778_a1uia)
    = applySing
        (applySing
            (singFun2
              @(LamCases_6989586621679364567Sym0 a_a1tNX b_a1tNY arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia)
              (\cases
                  (SArg (sA :: Sing a_a1uid)
                        (sWild_6989586621679362780 :: Sing wild_6989586621679362780_a1uie))
                    (SArg (sB :: Sing b_a1uif)
                          (sWild_6989586621679362782 :: Sing wild_6989586621679362782_a1uig))
                    -> let
                        sY ::
                          Sing @_ (Let6989586621679364573Y a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia)
                        sX ::
                          Sing @_ (Let6989586621679364573X a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia)
                        sY
                          = applySing
                              (applySing (singFun2 @ArgSym0 SArg) sB) sWild_6989586621679362782
                        sX
                          = applySing
                              (applySing (singFun2 @ArgSym0 SArg) sA) sWild_6989586621679362780
                      in
                        applySing
                          (singFun1
                              @(LamCases_6989586621679364576Sym0 a_a1tNX b_a1tNY a_a1uid wild_6989586621679362780_a1uie b_a1uif wild_6989586621679362782_a1uig arg_6989586621679362776_a1ui9 arg_6989586621679362778_a1uia)
                              (\cases
                                STrue -> sX
                                SFalse -> sY))
                          (applySing (applySing (singFun2 @(>=@#@$) (%>=)) sA) sB)))
            sArg_6989586621679362776)
        sArg_6989586621679362778
instance (SShow a_a1tO9, SShow b_a1tOa) =>
          SShow (Arg a_a1tO9 b_a1tOa) where
  sShowsPrec
    (sP_6989586621679363015 :: Sing p_6989586621679363015_a1uiI)
    (SArg (sArg_6989586621679363017 :: Sing arg_6989586621679363017_a1uiJ)
          (sArg_6989586621679363019 :: Sing arg_6989586621679363019_a1uiK))
    (sA_6989586621679364591 :: Sing a_6989586621679364591_a1uiL)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679363015)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Arg ")))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing
                        (applySing
                          (singFun3 @ShowsPrecSym0 sShowsPrec)
                          (sFromInteger (sing :: Sing 11)))
                        sArg_6989586621679363017))
                  (applySing
                    (applySing
                        (singFun3 @(.@#@$) (%.)) (singFun1 @ShowSpaceSym0 sShowSpace))
                    (applySing
                        (applySing
                          (singFun3 @ShowsPrecSym0 sShowsPrec)
                          (sFromInteger (sing :: Sing 11)))
                        sArg_6989586621679363019)))))
        sA_6989586621679364591
instance SFoldable (Arg a_a1tOb) where
  sFoldMap
    (_sf_6989586621679363023 :: Sing _f_6989586621679363023_a1uiV)
    (SArg (sA_6989586621679363027 :: Sing a_6989586621679363027_a1uiW)
          (sA_6989586621679363029 :: Sing a_6989586621679363029_a1uiX))
    = applySing
        (applySing
            (singFun2 @MappendSym0 sMappend)
            (applySing
              (singFun1
                  @(LamCases_6989586621679364616Sym0 a_a1tOb _f_6989586621679363023_a1uiV a_6989586621679363027_a1uiW a_6989586621679363029_a1uiX)
                  (\cases _ -> sMempty))
              sA_6989586621679363027))
        (applySing _sf_6989586621679363023 sA_6989586621679363029)
  sFoldr
    (_sf_6989586621679363023 :: Sing _f_6989586621679363023_a1ujf)
    (_sz_6989586621679363025 :: Sing _z_6989586621679363025_a1ujg)
    (SArg (sA_6989586621679363033 :: Sing a_6989586621679363033_a1ujh)
          (sA_6989586621679363035 :: Sing a_6989586621679363035_a1uji))
    = applySing
        (applySing
            (singFun2
              @(LamCases_6989586621679364637Sym0 a_a1tOb _f_6989586621679363023_a1ujf _z_6989586621679363025_a1ujg a_6989586621679363033_a1ujh a_6989586621679363035_a1uji)
              (\cases
                  _ (sN_6989586621679363031 :: Sing n_6989586621679363031_a1ujl)
                    -> sN_6989586621679363031))
            sA_6989586621679363033)
        (applySing
            (applySing _sf_6989586621679363023 sA_6989586621679363035)
            _sz_6989586621679363025)
instance STraversable (Arg a_a1tOc) where
  sTraverse
    (_sf_6989586621679363039 :: Sing _f_6989586621679363039_a1ujA)
    (SArg (sA_6989586621679363041 :: Sing a_6989586621679363041_a1ujB)
          (sA_6989586621679363043 :: Sing a_6989586621679363043_a1ujC))
    = applySing
        (applySing
            (applySing (singFun3 @LiftA2Sym0 sLiftA2) (singFun2 @ArgSym0 SArg))
            (applySing (singFun1 @PureSym0 sPure) sA_6989586621679363041))
        (applySing _sf_6989586621679363039 sA_6989586621679363043)
instance SApplicative First where
  sPure (sX :: Sing x_a1ujJ)
    = applySing (singFun1 @FirstSym0 SFirst) sX
  (%<*) (sA :: Sing a_a1ujT) _ = sA
  (%*>) _ (sA :: Sing a_a1uk3) = sA
  (%<*>) (SFirst (sF :: Sing f_a1ukd)) (SFirst (sX :: Sing x_a1uke))
    = applySing (singFun1 @FirstSym0 SFirst) (applySing sF sX)
  sLiftA2
    (sF :: Sing f_a1ukr)
    (SFirst (sA :: Sing a_a1uks))
    (SFirst (sB :: Sing b_a1ukt))
    = applySing
        (singFun1 @FirstSym0 SFirst) (applySing (applySing sF sA) sB)
instance SEnum a_a1tOl => SEnum (First a_a1tOl) where
  sSucc (SFirst (sA :: Sing a_a1ukA))
    = applySing
        (singFun1 @FirstSym0 SFirst)
        (applySing (singFun1 @SuccSym0 sSucc) sA)
  sPred (SFirst (sA :: Sing a_a1ukH))
    = applySing
        (singFun1 @FirstSym0 SFirst)
        (applySing (singFun1 @PredSym0 sPred) sA)
  sToEnum
    (sA_6989586621679364727 :: Sing a_6989586621679364727_a1ukQ)
    = applySing
        (applySing
            (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @FirstSym0 SFirst))
            (singFun1 @ToEnumSym0 sToEnum))
        sA_6989586621679364727
  sFromEnum (SFirst (sA :: Sing a_a1ukX))
    = applySing (singFun1 @FromEnumSym0 sFromEnum) sA
  sEnumFromTo
    (SFirst (sA :: Sing a_a1ul7))
    (SFirst (sB :: Sing b_a1ul8))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @FirstSym0 SFirst))
        (applySing
            (applySing (singFun2 @EnumFromToSym0 sEnumFromTo) sA) sB)
  sEnumFromThenTo
    (SFirst (sA :: Sing a_a1ull))
    (SFirst (sB :: Sing b_a1ulm))
    (SFirst (sC :: Sing c_a1uln))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @FirstSym0 SFirst))
        (applySing
            (applySing
              (applySing (singFun3 @EnumFromThenToSym0 sEnumFromThenTo) sA) sB)
            sC)
instance SFunctor First where
  sFmap
    (_sf_6989586621679363046 :: Sing _f_6989586621679363046_a1ulx)
    (SFirst (sA_6989586621679363050 :: Sing a_6989586621679363050_a1uly))
    = applySing
        (singFun1 @FirstSym0 SFirst)
        (applySing _sf_6989586621679363046 sA_6989586621679363050)
  (%<$)
    (_sz_6989586621679363048 :: Sing _z_6989586621679363048_a1ulI)
    (SFirst (sA_6989586621679363052 :: Sing a_6989586621679363052_a1ulJ))
    = applySing
        (singFun1 @FirstSym0 SFirst)
        (applySing
            (singFun1
              @(LamCases_6989586621679364788Sym0 _z_6989586621679363048_a1ulI a_6989586621679363052_a1ulJ)
              (\cases _ -> _sz_6989586621679363048))
            sA_6989586621679363052)
instance SMonad First where
  (%>>)
    (sA_6989586621679364797 :: Sing a_6989586621679364797_a1um2)
    (sA_6989586621679364799 :: Sing a_6989586621679364799_a1um3)
    = applySing
        (applySing (singFun2 @(*>@#@$) (%*>)) sA_6989586621679364797)
        sA_6989586621679364799
  (%>>=) (SFirst (sA :: Sing a_a1umd)) (sF :: Sing f_a1ume)
    = applySing sF sA
instance SSemigroup (First a_a1tOw) where
  (%<>) (sA :: Sing a_a1umo) _ = sA
instance SFoldable First where
  sFoldMap
    (_sf_6989586621679363055 :: Sing _f_6989586621679363055_a1umy)
    (SFirst (sA_6989586621679363059 :: Sing a_6989586621679363059_a1umz))
    = applySing _sf_6989586621679363055 sA_6989586621679363059
  sFoldr
    (_sf_6989586621679363055 :: Sing _f_6989586621679363055_a1umM)
    (_sz_6989586621679363057 :: Sing _z_6989586621679363057_a1umN)
    (SFirst (sA_6989586621679363061 :: Sing a_6989586621679363061_a1umO))
    = applySing
        (applySing _sf_6989586621679363055 sA_6989586621679363061)
        _sz_6989586621679363057
instance STraversable First where
  sTraverse
    (_sf_6989586621679363064 :: Sing _f_6989586621679363064_a1umY)
    (SFirst (sA_6989586621679363066 :: Sing a_6989586621679363066_a1umZ))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @FirstSym0 SFirst))
        (applySing _sf_6989586621679363064 sA_6989586621679363066)
instance SApplicative Last where
  sPure (sX :: Sing x_a1un6)
    = applySing (singFun1 @LastSym0 SLast) sX
  (%<*) (sA :: Sing a_a1ung) _ = sA
  (%*>) _ (sA :: Sing a_a1unq) = sA
  (%<*>) (SLast (sF :: Sing f_a1unA)) (SLast (sX :: Sing x_a1unB))
    = applySing (singFun1 @LastSym0 SLast) (applySing sF sX)
  sLiftA2
    (sF :: Sing f_a1unO)
    (SLast (sA :: Sing a_a1unP))
    (SLast (sB :: Sing b_a1unQ))
    = applySing
        (singFun1 @LastSym0 SLast) (applySing (applySing sF sA) sB)
instance SEnum a_a1tOG => SEnum (Last a_a1tOG) where
  sSucc (SLast (sA :: Sing a_a1unX))
    = applySing
        (singFun1 @LastSym0 SLast)
        (applySing (singFun1 @SuccSym0 sSucc) sA)
  sPred (SLast (sA :: Sing a_a1uo4))
    = applySing
        (singFun1 @LastSym0 SLast)
        (applySing (singFun1 @PredSym0 sPred) sA)
  sToEnum
    (sA_6989586621679364936 :: Sing a_6989586621679364936_a1uod)
    = applySing
        (applySing
            (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @LastSym0 SLast))
            (singFun1 @ToEnumSym0 sToEnum))
        sA_6989586621679364936
  sFromEnum (SLast (sA :: Sing a_a1uok))
    = applySing (singFun1 @FromEnumSym0 sFromEnum) sA
  sEnumFromTo
    (SLast (sA :: Sing a_a1uou))
    (SLast (sB :: Sing b_a1uov))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @LastSym0 SLast))
        (applySing
            (applySing (singFun2 @EnumFromToSym0 sEnumFromTo) sA) sB)
  sEnumFromThenTo
    (SLast (sA :: Sing a_a1uoI))
    (SLast (sB :: Sing b_a1uoJ))
    (SLast (sC :: Sing c_a1uoK))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @LastSym0 SLast))
        (applySing
            (applySing
              (applySing (singFun3 @EnumFromThenToSym0 sEnumFromThenTo) sA) sB)
            sC)
instance SFunctor Last where
  sFmap
    (_sf_6989586621679363069 :: Sing _f_6989586621679363069_a1uoU)
    (SLast (sA_6989586621679363073 :: Sing a_6989586621679363073_a1uoV))
    = applySing
        (singFun1 @LastSym0 SLast)
        (applySing _sf_6989586621679363069 sA_6989586621679363073)
  (%<$)
    (_sz_6989586621679363071 :: Sing _z_6989586621679363071_a1up5)
    (SLast (sA_6989586621679363075 :: Sing a_6989586621679363075_a1up6))
    = applySing
        (singFun1 @LastSym0 SLast)
        (applySing
            (singFun1
              @(LamCases_6989586621679364997Sym0 _z_6989586621679363071_a1up5 a_6989586621679363075_a1up6)
              (\cases _ -> _sz_6989586621679363071))
            sA_6989586621679363075)
instance SMonad Last where
  (%>>)
    (sA_6989586621679365006 :: Sing a_6989586621679365006_a1upp)
    (sA_6989586621679365008 :: Sing a_6989586621679365008_a1upq)
    = applySing
        (applySing (singFun2 @(*>@#@$) (%*>)) sA_6989586621679365006)
        sA_6989586621679365008
  (%>>=) (SLast (sA :: Sing a_a1upA)) (sF :: Sing f_a1upB)
    = applySing sF sA
instance SSemigroup (Last a_a1tOR) where
  (%<>) _ (sB :: Sing b_a1upL) = sB
instance SFoldable Last where
  sFoldMap
    (_sf_6989586621679363078 :: Sing _f_6989586621679363078_a1upV)
    (SLast (sA_6989586621679363082 :: Sing a_6989586621679363082_a1upW))
    = applySing _sf_6989586621679363078 sA_6989586621679363082
  sFoldr
    (_sf_6989586621679363078 :: Sing _f_6989586621679363078_a1uq9)
    (_sz_6989586621679363080 :: Sing _z_6989586621679363080_a1uqa)
    (SLast (sA_6989586621679363084 :: Sing a_6989586621679363084_a1uqb))
    = applySing
        (applySing _sf_6989586621679363078 sA_6989586621679363084)
        _sz_6989586621679363080
instance STraversable Last where
  sTraverse
    (_sf_6989586621679363087 :: Sing _f_6989586621679363087_a1uql)
    (SLast (sA_6989586621679363089 :: Sing a_6989586621679363089_a1uqm))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @LastSym0 SLast))
        (applySing _sf_6989586621679363087 sA_6989586621679363089)
instance SMonoid m_a1tOT =>
          SSemigroup (WrappedMonoid m_a1tOT) where
  (%<>)
    (SWrapMonoid (sA :: Sing a_a1uqw))
    (SWrapMonoid (sB :: Sing b_a1uqx))
    = applySing
        (singFun1 @WrapMonoidSym0 SWrapMonoid)
        (applySing (applySing (singFun2 @MappendSym0 sMappend) sA) sB)
instance SMonoid m_a1tOW => SMonoid (WrappedMonoid m_a1tOW) where
  sMempty = applySing (singFun1 @WrapMonoidSym0 SWrapMonoid) sMempty
instance SEnum a_a1tOX => SEnum (WrappedMonoid a_a1tOX) where
  sSucc (SWrapMonoid (sA :: Sing a_a1uqH))
    = applySing
        (singFun1 @WrapMonoidSym0 SWrapMonoid)
        (applySing (singFun1 @SuccSym0 sSucc) sA)
  sPred (SWrapMonoid (sA :: Sing a_a1uqO))
    = applySing
        (singFun1 @WrapMonoidSym0 SWrapMonoid)
        (applySing (singFun1 @PredSym0 sPred) sA)
  sToEnum
    (sA_6989586621679365106 :: Sing a_6989586621679365106_a1uqX)
    = applySing
        (applySing
            (applySing
              (singFun3 @(.@#@$) (%.)) (singFun1 @WrapMonoidSym0 SWrapMonoid))
            (singFun1 @ToEnumSym0 sToEnum))
        sA_6989586621679365106
  sFromEnum (SWrapMonoid (sA :: Sing a_a1ur4))
    = applySing (singFun1 @FromEnumSym0 sFromEnum) sA
  sEnumFromTo
    (SWrapMonoid (sA :: Sing a_a1ure))
    (SWrapMonoid (sB :: Sing b_a1urf))
    = applySing
        (applySing
            (singFun2 @MapSym0 sMap) (singFun1 @WrapMonoidSym0 SWrapMonoid))
        (applySing
            (applySing (singFun2 @EnumFromToSym0 sEnumFromTo) sA) sB)
  sEnumFromThenTo
    (SWrapMonoid (sA :: Sing a_a1urs))
    (SWrapMonoid (sB :: Sing b_a1urt))
    (SWrapMonoid (sC :: Sing c_a1uru))
    = applySing
        (applySing
            (singFun2 @MapSym0 sMap) (singFun1 @WrapMonoidSym0 SWrapMonoid))
        (applySing
            (applySing
              (applySing (singFun3 @EnumFromThenToSym0 sEnumFromThenTo) sA) sB)
            sC)
deriving instance (Data.Singletons.ShowSing.ShowSing a_a1tO9,
                    Data.Singletons.ShowSing.ShowSing b_a1tOa) =>
                  Show (SArg (z_a1urD :: Arg a_a1tO9 b_a1tOa))
