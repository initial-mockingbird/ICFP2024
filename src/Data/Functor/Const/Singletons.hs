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
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Const.Singletons
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Exports the promoted and singled versions of the 'Const' data type.
--
-----------------------------------------------------------------------------

module Data.Functor.Const.Singletons (
  -- * The 'Const' singleton
  Sing, SConst(..), GetConst, sGetConst,

  -- * Defunctionalization symbols
  ConstSym0, ConstSym1,
  GetConstSym0, GetConstSym1
  ) where

import Control.Applicative
import Control.Monad.Singletons.Internal
import Data.Eq.Singletons
import Data.Foldable.Singletons
import Data.Monoid.Singletons
import Data.Ord.Singletons
import Data.Semigroup.Singletons.Internal.Classes
import Data.Singletons.Base.Instances hiding (FoldlSym0, sFoldl)
import Data.Singletons.Base.Enum
import Data.Singletons.TH
import GHC.Base.Singletons
  hiding ( Const, ConstSym0, ConstSym1
         , Foldr, FoldrSym0, sFoldr )
import GHC.Num.Singletons
import Text.Show.Singletons
import Data.Kind (Type)
import qualified GHC.Num.Natural
import GHC.Exts
import qualified Data.Type.Equality
import qualified Data.Singletons.Decide
import qualified Data.Type.Coercion
type ConstSym0 :: forall {k_ar1T :: Type}
                             (a_ar1U :: Type)
                             (b_ar1V :: k_ar1T). (~>) a_ar1U (Const a_ar1U b_ar1V)
data ConstSym0 :: (~>) a_ar1U (Const a_ar1U b_ar1V)
  where
    ConstSym0KindInference :: SameKind (Apply ConstSym0 arg_a12Dz) (ConstSym1 arg_a12Dz) =>
                              ConstSym0 a6989586621679258262
type instance Apply @a_ar1U @(Const a_ar1U b_ar1V) ConstSym0 a6989586621679258262 = 'Const a6989586621679258262
instance SuppressUnusedWarnings ConstSym0 where
  suppressUnusedWarnings = snd ((,) ConstSym0KindInference ())
type ConstSym1 :: forall {k_ar1T :: Type}
                          (a_ar1U :: Type)
                          (b_ar1V :: k_ar1T). a_ar1U -> Const a_ar1U b_ar1V
type family ConstSym1 @(a_ar1U :: Type) @(b_ar1V :: k_ar1T) (a6989586621679258262 :: a_ar1U) :: Const a_ar1U b_ar1V where
  ConstSym1 a6989586621679258262 = 'Const a6989586621679258262
type GetConstSym0 :: forall {k_ar1T :: Type}
                            (a_ar1U :: Type)
                            (b_ar1V :: k_ar1T). (~>) (Const a_ar1U b_ar1V) a_ar1U
data GetConstSym0 :: (~>) (Const a_ar1U b_ar1V) a_ar1U
  where
    GetConstSym0KindInference :: SameKind (Apply GetConstSym0 arg_a12DC) (GetConstSym1 arg_a12DC) =>
                                  GetConstSym0 a6989586621679258265
type instance Apply @(Const a_ar1U b_ar1V) @a_ar1U GetConstSym0 a6989586621679258265 = GetConst a6989586621679258265
instance SuppressUnusedWarnings GetConstSym0 where
  suppressUnusedWarnings = snd ((,) GetConstSym0KindInference ())
type GetConstSym1 :: forall {k_ar1T :: Type}
                            (a_ar1U :: Type)
                            (b_ar1V :: k_ar1T). Const a_ar1U b_ar1V -> a_ar1U
type family GetConstSym1 @(a_ar1U :: Type) @(b_ar1V :: k_ar1T) (a6989586621679258265 :: Const a_ar1U b_ar1V) :: a_ar1U where
  GetConstSym1 a6989586621679258265 = GetConst a6989586621679258265
type GetConst :: forall {k_ar1T :: Type}
                        (a_ar1U :: Type)
                        (b_ar1V :: k_ar1T). Const a_ar1U b_ar1V -> a_ar1U
type family GetConst @(a_ar1U :: Type) @(b_ar1V :: k_ar1T) (a_a12DB :: Const a_ar1U b_ar1V) :: a_ar1U where
  GetConst @a_ar1U @b_ar1V ('Const field_a12DE :: Const a_ar1U b_ar1V) = field_a12DE
sGetConst ::
  forall {k_ar1T :: Type}
          (a_ar1U :: Type)
          (b_ar1V :: k_ar1T)
          (t_a12DF :: Const a_ar1U b_ar1V). Sing t_a12DF
                                            -> Sing (GetConst t_a12DF :: a_ar1U)
sGetConst (SConst (sField :: Sing field_a12DE)) = sField
instance SingI (GetConstSym0 :: (~>) (Const a_ar1U b_ar1V) a_ar1U) where
  sing = singFun1 @GetConstSym0 sGetConst
type SConst :: forall {k_ar1T :: Type}
                      (a_ar1U :: Type)
                      (b_ar1V :: k_ar1T). Const a_ar1U b_ar1V -> Type
data SConst :: forall {k_ar1T :: Type}
                      (a_ar1U :: Type)
                      (b_ar1V :: k_ar1T).
                Const a_ar1U b_ar1V -> Type
  where
    SConst :: forall {k_ar1T :: Type}
                      (a_ar1U :: Type)
                      (b_ar1V :: k_ar1T)
                      (n_a12DH :: a_ar1U).
              (Sing n_a12DH) -> SConst ('Const n_a12DH :: Const a_ar1U b_ar1V)
type instance Sing @(Const a_ar1U b_ar1V) = SConst
instance SingI n_a12DH => SingI ('Const (n_a12DH :: a_ar1U)) where
  sing = SConst sing
instance SingI1 'Const where
  liftSing = SConst
instance SingI (ConstSym0 :: (~>) a_ar1U (Const a_ar1U b_ar1V)) where
  sing = singFun1 @ConstSym0 SConst

instance SingKind a => SingKind (Const a b) where
  type Demote (Const a b) = Const (Demote a) b
  fromSing (SConst sa) = Const (fromSing sa)
  toSing (Const a) = withSomeSing a $ SomeSing . SConst

type MinBound_6989586621679262129 :: forall a_a13pp
                                                b_a13pq. Const a_a13pp b_a13pq
type family MinBound_6989586621679262129 @a_a13pp @b_a13pq :: Const a_a13pp b_a13pq where
  MinBound_6989586621679262129 @a_a13pp @b_a13pq = Apply ConstSym0 MinBoundSym0
type MaxBound_6989586621679262132 :: forall a_a13pp
                                            b_a13pq. Const a_a13pp b_a13pq
type family MaxBound_6989586621679262132 @a_a13pp @b_a13pq :: Const a_a13pp b_a13pq where
  MaxBound_6989586621679262132 @a_a13pp @b_a13pq = Apply ConstSym0 MaxBoundSym0
instance PBounded (Const a_a13pp b_a13pq) where
  type MinBound = MinBound_6989586621679262129
  type MaxBound = MaxBound_6989586621679262132
type TFHelper_6989586621679262543 :: forall a_a13pr
                                            b_a13ps. Const a_a13pr b_a13ps
                                                      -> Const a_a13pr b_a13ps -> Bool
type family TFHelper_6989586621679262543 @a_a13pr @b_a13ps (a_a13KF :: Const a_a13pr b_a13ps) (a_a13KG :: Const a_a13pr b_a13ps) :: Bool where
  TFHelper_6989586621679262543 @a_a13pr @b_a13ps ('Const a_6989586621679261872_a13KK :: Const a_a13pr b_a13ps) ('Const b_6989586621679261874_a13KL :: Const a_a13pr b_a13ps) = Apply (Apply (==@#@$) a_6989586621679261872_a13KK) b_6989586621679261874_a13KL
instance PEq (Const a_a13pr b_a13ps) where
  type (==) a_a13KB a_a13KC = TFHelper_6989586621679262543 a_a13KB a_a13KC
type Compare_6989586621679263503 :: forall a_a13pt
                                            b_a13pu. Const a_a13pt b_a13pu
                                                    -> Const a_a13pt b_a13pu -> Ordering
type family Compare_6989586621679263503 @a_a13pt @b_a13pu (a_a1409 :: Const a_a13pt b_a13pu) (a_a140a :: Const a_a13pt b_a13pu) :: Ordering where
  Compare_6989586621679263503 @a_a13pt @b_a13pu ('Const a_6989586621679261879_a140e :: Const a_a13pt b_a13pu) ('Const b_6989586621679261881_a140f :: Const a_a13pt b_a13pu) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679261879_a140e) b_6989586621679261881_a140f)) NilSym0)
instance POrd (Const a_a13pt b_a13pu) where
  type Compare a_a1405 a_a1406 = Compare_6989586621679263503 a_a1405 a_a1406
type Succ_6989586621679263513 :: forall a_a13pv
                                        b_a13pw. Const a_a13pv b_a13pw -> Const a_a13pv b_a13pw
type family Succ_6989586621679263513 @a_a13pv @b_a13pw (a_a140j :: Const a_a13pv b_a13pw) :: Const a_a13pv b_a13pw where
  Succ_6989586621679263513 @a_a13pv @b_a13pw ('Const x_a140m :: Const a_a13pv b_a13pw) = Apply ConstSym0 (Apply SuccSym0 x_a140m)
type Pred_6989586621679263520 :: forall a_a13pv
                                        b_a13pw. Const a_a13pv b_a13pw -> Const a_a13pv b_a13pw
type family Pred_6989586621679263520 @a_a13pv @b_a13pw (a_a140q :: Const a_a13pv b_a13pw) :: Const a_a13pv b_a13pw where
  Pred_6989586621679263520 @a_a13pv @b_a13pw ('Const x_a140t :: Const a_a13pv b_a13pw) = Apply ConstSym0 (Apply PredSym0 x_a140t)
type ToEnum_6989586621679263527 :: forall a_a13pv
                                          b_a13pw. GHC.Num.Natural.Natural
                                                    -> Const a_a13pv b_a13pw
type family ToEnum_6989586621679263527 @a_a13pv @b_a13pw (a_a140x :: GHC.Num.Natural.Natural) :: Const a_a13pv b_a13pw where
  ToEnum_6989586621679263527 @a_a13pv @b_a13pw (i_a140A :: GHC.Num.Natural.Natural) = Apply ConstSym0 (Apply ToEnumSym0 i_a140A)
type FromEnum_6989586621679263534 :: forall a_a13pv
                                            b_a13pw. Const a_a13pv b_a13pw
                                                      -> GHC.Num.Natural.Natural
type family FromEnum_6989586621679263534 @a_a13pv @b_a13pw (a_a140E :: Const a_a13pv b_a13pw) :: GHC.Num.Natural.Natural where
  FromEnum_6989586621679263534 @a_a13pv @b_a13pw ('Const x_a140H :: Const a_a13pv b_a13pw) = Apply FromEnumSym0 x_a140H
type EnumFromTo_6989586621679263542 :: forall a_a13pv
                                              b_a13pw. Const a_a13pv b_a13pw
                                                        -> Const a_a13pv b_a13pw
                                                          -> [Const a_a13pv b_a13pw]
type family EnumFromTo_6989586621679263542 @a_a13pv @b_a13pw (a_a140M :: Const a_a13pv b_a13pw) (a_a140N :: Const a_a13pv b_a13pw) :: [Const a_a13pv b_a13pw] where
  EnumFromTo_6989586621679263542 @a_a13pv @b_a13pw ('Const x_a140R :: Const a_a13pv b_a13pw) ('Const y_a140S :: Const a_a13pv b_a13pw) = Apply (Apply MapSym0 ConstSym0) (Apply (Apply EnumFromToSym0 x_a140R) y_a140S)
type EnumFromThenTo_6989586621679263554 :: forall a_a13pv
                                                  b_a13pw. Const a_a13pv b_a13pw
                                                            -> Const a_a13pv b_a13pw
                                                              -> Const a_a13pv b_a13pw
                                                                  -> [Const a_a13pv b_a13pw]
type family EnumFromThenTo_6989586621679263554 @a_a13pv @b_a13pw (a_a140Y :: Const a_a13pv b_a13pw) (a_a140Z :: Const a_a13pv b_a13pw) (a_a1410 :: Const a_a13pv b_a13pw) :: [Const a_a13pv b_a13pw] where
  EnumFromThenTo_6989586621679263554 @a_a13pv @b_a13pw ('Const x_a1415 :: Const a_a13pv b_a13pw) ('Const y_a1416 :: Const a_a13pv b_a13pw) ('Const z_a1417 :: Const a_a13pv b_a13pw) = Apply (Apply MapSym0 ConstSym0) (Apply (Apply (Apply EnumFromThenToSym0 x_a1415) y_a1416) z_a1417)
instance PEnum (Const a_a13pv b_a13pw) where
  type Succ a_a140g = Succ_6989586621679263513 a_a140g
  type Pred a_a140n = Pred_6989586621679263520 a_a140n
  type ToEnum a_a140u = ToEnum_6989586621679263527 a_a140u
  type FromEnum a_a140B = FromEnum_6989586621679263534 a_a140B
  type EnumFromTo a_a140I a_a140J = EnumFromTo_6989586621679263542 a_a140I a_a140J
  type EnumFromThenTo a_a140T a_a140U a_a140V = EnumFromThenTo_6989586621679263554 a_a140T a_a140U a_a140V
type Mempty_6989586621679263566 :: forall a_a13pG
                                          b_a13pH. Const a_a13pG b_a13pH
type family Mempty_6989586621679263566 @a_a13pG @b_a13pH :: Const a_a13pG b_a13pH where
  Mempty_6989586621679263566 @a_a13pG @b_a13pH = Apply ConstSym0 MemptySym0
instance PMonoid (Const a_a13pG b_a13pH) where
  type Mempty = Mempty_6989586621679263566
type TFHelper_6989586621679263571 :: forall a_a13pI
                                            b_a13pJ. Const a_a13pI b_a13pJ
                                                      -> Const a_a13pI b_a13pJ
                                                        -> Const a_a13pI b_a13pJ
type family TFHelper_6989586621679263571 @a_a13pI @b_a13pJ (a_a141f :: Const a_a13pI b_a13pJ) (a_a141g :: Const a_a13pI b_a13pJ) :: Const a_a13pI b_a13pJ where
  TFHelper_6989586621679263571 @a_a13pI @b_a13pJ ('Const x_a141k :: Const a_a13pI b_a13pJ) ('Const y_a141l :: Const a_a13pI b_a13pJ) = Apply ConstSym0 (Apply (Apply (+@#@$) x_a141k) y_a141l)
type TFHelper_6989586621679263582 :: forall a_a13pI
                                            b_a13pJ. Const a_a13pI b_a13pJ
                                                      -> Const a_a13pI b_a13pJ
                                                        -> Const a_a13pI b_a13pJ
type family TFHelper_6989586621679263582 @a_a13pI @b_a13pJ (a_a141q :: Const a_a13pI b_a13pJ) (a_a141r :: Const a_a13pI b_a13pJ) :: Const a_a13pI b_a13pJ where
  TFHelper_6989586621679263582 @a_a13pI @b_a13pJ ('Const x_a141v :: Const a_a13pI b_a13pJ) ('Const y_a141w :: Const a_a13pI b_a13pJ) = Apply ConstSym0 (Apply (Apply (-@#@$) x_a141v) y_a141w)
type TFHelper_6989586621679263593 :: forall a_a13pI
                                            b_a13pJ. Const a_a13pI b_a13pJ
                                                      -> Const a_a13pI b_a13pJ
                                                        -> Const a_a13pI b_a13pJ
type family TFHelper_6989586621679263593 @a_a13pI @b_a13pJ (a_a141B :: Const a_a13pI b_a13pJ) (a_a141C :: Const a_a13pI b_a13pJ) :: Const a_a13pI b_a13pJ where
  TFHelper_6989586621679263593 @a_a13pI @b_a13pJ ('Const x_a141G :: Const a_a13pI b_a13pJ) ('Const y_a141H :: Const a_a13pI b_a13pJ) = Apply ConstSym0 (Apply (Apply (*@#@$) x_a141G) y_a141H)
type Negate_6989586621679263603 :: forall a_a13pI
                                          b_a13pJ. Const a_a13pI b_a13pJ
                                                    -> Const a_a13pI b_a13pJ
type family Negate_6989586621679263603 @a_a13pI @b_a13pJ (a_a141L :: Const a_a13pI b_a13pJ) :: Const a_a13pI b_a13pJ where
  Negate_6989586621679263603 @a_a13pI @b_a13pJ ('Const x_a141O :: Const a_a13pI b_a13pJ) = Apply ConstSym0 (Apply NegateSym0 x_a141O)
type Abs_6989586621679263610 :: forall a_a13pI
                                        b_a13pJ. Const a_a13pI b_a13pJ -> Const a_a13pI b_a13pJ
type family Abs_6989586621679263610 @a_a13pI @b_a13pJ (a_a141S :: Const a_a13pI b_a13pJ) :: Const a_a13pI b_a13pJ where
  Abs_6989586621679263610 @a_a13pI @b_a13pJ ('Const x_a141V :: Const a_a13pI b_a13pJ) = Apply ConstSym0 (Apply AbsSym0 x_a141V)
type Signum_6989586621679263617 :: forall a_a13pI
                                          b_a13pJ. Const a_a13pI b_a13pJ
                                                    -> Const a_a13pI b_a13pJ
type family Signum_6989586621679263617 @a_a13pI @b_a13pJ (a_a141Z :: Const a_a13pI b_a13pJ) :: Const a_a13pI b_a13pJ where
  Signum_6989586621679263617 @a_a13pI @b_a13pJ ('Const x_a1422 :: Const a_a13pI b_a13pJ) = Apply ConstSym0 (Apply SignumSym0 x_a1422)
type FromInteger_6989586621679263624 :: forall a_a13pI
                                                b_a13pJ. GHC.Num.Natural.Natural
                                                        -> Const a_a13pI b_a13pJ
type family FromInteger_6989586621679263624 @a_a13pI @b_a13pJ (a_a1426 :: GHC.Num.Natural.Natural) :: Const a_a13pI b_a13pJ where
  FromInteger_6989586621679263624 @a_a13pI @b_a13pJ (n_a1429 :: GHC.Num.Natural.Natural) = Apply ConstSym0 (Apply FromIntegerSym0 n_a1429)
instance PNum (Const a_a13pI b_a13pJ) where
  type (+) a_a141b a_a141c = TFHelper_6989586621679263571 a_a141b a_a141c
  type (-) a_a141m a_a141n = TFHelper_6989586621679263582 a_a141m a_a141n
  type (*) a_a141x a_a141y = TFHelper_6989586621679263593 a_a141x a_a141y
  type Negate a_a141I = Negate_6989586621679263603 a_a141I
  type Abs a_a141P = Abs_6989586621679263610 a_a141P
  type Signum a_a141W = Signum_6989586621679263617 a_a141W
  type FromInteger a_a1423 = FromInteger_6989586621679263624 a_a1423
type TFHelper_6989586621679263632 :: forall a_a13pU
                                            b_a13pV. Const a_a13pU b_a13pV
                                                      -> Const a_a13pU b_a13pV
                                                        -> Const a_a13pU b_a13pV
type family TFHelper_6989586621679263632 @a_a13pU @b_a13pV (a_a142e :: Const a_a13pU b_a13pV) (a_a142f :: Const a_a13pU b_a13pV) :: Const a_a13pU b_a13pV where
  TFHelper_6989586621679263632 @a_a13pU @b_a13pV ('Const x_a142j :: Const a_a13pU b_a13pV) ('Const y_a142k :: Const a_a13pU b_a13pV) = Apply ConstSym0 (Apply (Apply (<>@#@$) x_a142j) y_a142k)
instance PSemigroup (Const a_a13pU b_a13pV) where
  type (<>) a_a142a a_a142b = TFHelper_6989586621679263632 a_a142a a_a142b
type ShowsPrec_6989586621679263644 :: forall a_a13pY
                                              b_a13pZ. GHC.Num.Natural.Natural
                                                      -> Const a_a13pY b_a13pZ
                                                          -> Symbol
                                                            -> Symbol
type family ShowsPrec_6989586621679263644 @a_a13pY @b_a13pZ (a_a142s :: GHC.Num.Natural.Natural) (a_a142t :: Const a_a13pY b_a13pZ) (a_a142u :: Symbol) :: Symbol where
  ShowsPrec_6989586621679263644 @a_a13pY @b_a13pZ (d_a142z :: GHC.Num.Natural.Natural) ('Const x_a142A :: Const a_a13pY b_a13pZ) (a_6989586621679263646_a142B :: Symbol) = Apply (Apply (Apply ($@#@$) (Apply ShowParenSym0 (Apply (Apply (>@#@$) d_a142z) (FromInteger 10)))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Const ")) (Apply (Apply ShowsPrecSym0 (FromInteger 11)) x_a142A))) a_6989586621679263646_a142B
instance PShow (Const a_a13pY b_a13pZ) where
  type ShowsPrec a_a142l a_a142m a_a142n = ShowsPrec_6989586621679263644 a_a142l a_a142m a_a142n
type family LamCases_6989586621679263669_a142O m6989586621679261266 (_f_69895866216792618866989586621679263667 :: (~>) a7566047373982667315 b7566047373982667316) a_69895866216792618926989586621679263668 a_6989586621679263672_a142R where
  LamCases_6989586621679263669_a142O m_a13q2 _f_6989586621679261886_a142L a_6989586621679261892_a142M n_6989586621679261890_a142P = n_6989586621679261890_a142P
data LamCases_6989586621679263669Sym0 m6989586621679261266 (_f_69895866216792618866989586621679263667 :: (~>) a7566047373982667315 b7566047373982667316) a_69895866216792618926989586621679263668 a_69895866216792636726989586621679263673
  where
    LamCases_6989586621679263669Sym0KindInference :: SameKind (Apply (LamCases_6989586621679263669Sym0 m6989586621679261266 _f_69895866216792618866989586621679263667 a_69895866216792618926989586621679263668) arg_a142S) (LamCases_6989586621679263669Sym1 m6989586621679261266 _f_69895866216792618866989586621679263667 a_69895866216792618926989586621679263668 arg_a142S) =>
                                                      LamCases_6989586621679263669Sym0 m6989586621679261266 _f_69895866216792618866989586621679263667 a_69895866216792618926989586621679263668 a_69895866216792636726989586621679263673
type instance Apply @_ @_ (LamCases_6989586621679263669Sym0 m6989586621679261266 _f_69895866216792618866989586621679263667 a_69895866216792618926989586621679263668) a_69895866216792636726989586621679263673 = LamCases_6989586621679263669_a142O m6989586621679261266 _f_69895866216792618866989586621679263667 a_69895866216792618926989586621679263668 a_69895866216792636726989586621679263673
instance SuppressUnusedWarnings (LamCases_6989586621679263669Sym0 m6989586621679261266 _f_69895866216792618866989586621679263667 a_69895866216792618926989586621679263668) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679263669Sym0KindInference ())
type family LamCases_6989586621679263669Sym1 m6989586621679261266 (_f_69895866216792618866989586621679263667 :: (~>) a7566047373982667315 b7566047373982667316) a_69895866216792618926989586621679263668 a_69895866216792636726989586621679263673 where
  LamCases_6989586621679263669Sym1 m6989586621679261266 _f_69895866216792618866989586621679263667 a_69895866216792618926989586621679263668 a_69895866216792636726989586621679263673 = LamCases_6989586621679263669_a142O m6989586621679261266 _f_69895866216792618866989586621679263667 a_69895866216792618926989586621679263668 a_69895866216792636726989586621679263673
type Fmap_6989586621679263660 :: forall m_a13q2
                                        a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> Const m_a13q2 a_iYSL -> Const m_a13q2 b_iYSM
type family Fmap_6989586621679263660 @m_a13q2 @a_iYSL @b_iYSM (a_a142G :: (~>) a_iYSL b_iYSM) (a_a142H :: Const m_a13q2 a_iYSL) :: Const m_a13q2 b_iYSM where
  Fmap_6989586621679263660 @m_a13q2 @a_iYSL @b_iYSM (_f_6989586621679261886_a142L :: (~>) a_iYSL b_iYSM) ('Const a_6989586621679261892_a142M :: Const m_a13q2 a_iYSL) = Apply ConstSym0 (Apply (LamCases_6989586621679263669Sym0 m_a13q2 _f_6989586621679261886_a142L a_6989586621679261892_a142M) a_6989586621679261892_a142M)
type family LamCases_6989586621679263686_a1435 m6989586621679261266 (_z_69895866216792618886989586621679263684 :: a7566047373982667319) a_69895866216792618966989586621679263685 a_6989586621679263689_a1438 where
  LamCases_6989586621679263686_a1435 m_a13q2 _z_6989586621679261888_a1432 a_6989586621679261896_a1433 n_6989586621679261894_a1436 = n_6989586621679261894_a1436
data LamCases_6989586621679263686Sym0 m6989586621679261266 (_z_69895866216792618886989586621679263684 :: a7566047373982667319) a_69895866216792618966989586621679263685 a_69895866216792636896989586621679263690
  where
    LamCases_6989586621679263686Sym0KindInference :: SameKind (Apply (LamCases_6989586621679263686Sym0 m6989586621679261266 _z_69895866216792618886989586621679263684 a_69895866216792618966989586621679263685) arg_a1439) (LamCases_6989586621679263686Sym1 m6989586621679261266 _z_69895866216792618886989586621679263684 a_69895866216792618966989586621679263685 arg_a1439) =>
                                                      LamCases_6989586621679263686Sym0 m6989586621679261266 _z_69895866216792618886989586621679263684 a_69895866216792618966989586621679263685 a_69895866216792636896989586621679263690
type instance Apply @_ @_ (LamCases_6989586621679263686Sym0 m6989586621679261266 _z_69895866216792618886989586621679263684 a_69895866216792618966989586621679263685) a_69895866216792636896989586621679263690 = LamCases_6989586621679263686_a1435 m6989586621679261266 _z_69895866216792618886989586621679263684 a_69895866216792618966989586621679263685 a_69895866216792636896989586621679263690
instance SuppressUnusedWarnings (LamCases_6989586621679263686Sym0 m6989586621679261266 _z_69895866216792618886989586621679263684 a_69895866216792618966989586621679263685) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679263686Sym0KindInference ())
type family LamCases_6989586621679263686Sym1 m6989586621679261266 (_z_69895866216792618886989586621679263684 :: a7566047373982667319) a_69895866216792618966989586621679263685 a_69895866216792636896989586621679263690 where
  LamCases_6989586621679263686Sym1 m6989586621679261266 _z_69895866216792618886989586621679263684 a_69895866216792618966989586621679263685 a_69895866216792636896989586621679263690 = LamCases_6989586621679263686_a1435 m6989586621679261266 _z_69895866216792618886989586621679263684 a_69895866216792618966989586621679263685 a_69895866216792636896989586621679263690
type TFHelper_6989586621679263677 :: forall m_a13q2
                                            a_iYSP
                                            b_iYSQ. a_iYSP
                                                    -> Const m_a13q2 b_iYSQ
                                                        -> Const m_a13q2 a_iYSP
type family TFHelper_6989586621679263677 @m_a13q2 @a_iYSP @b_iYSQ (a_a142X :: a_iYSP) (a_a142Y :: Const m_a13q2 b_iYSQ) :: Const m_a13q2 a_iYSP where
  TFHelper_6989586621679263677 @m_a13q2 @a_iYSP @b_iYSQ (_z_6989586621679261888_a1432 :: a_iYSP) ('Const a_6989586621679261896_a1433 :: Const m_a13q2 b_iYSQ) = Apply ConstSym0 (Apply (LamCases_6989586621679263686Sym0 m_a13q2 _z_6989586621679261888_a1432 a_6989586621679261896_a1433) a_6989586621679261896_a1433)
instance PFunctor (Const m_a13q2) where
  type Fmap a_a142C a_a142D = Fmap_6989586621679263660 a_a142C a_a142D
  type (<$) a_a142T a_a142U = TFHelper_6989586621679263677 a_a142T a_a142U
type family LamCases_6989586621679263703_a143m m6989586621679261267 (_f_69895866216792619016989586621679263701 :: (~>) a7566047373982667509 m7566047373982667510) a_69895866216792619056989586621679263702 a_6989586621679263705_a143o where
  LamCases_6989586621679263703_a143m m_a13q3 _f_6989586621679261901_a143j a_6989586621679261905_a143k _ = MemptySym0
data LamCases_6989586621679263703Sym0 m6989586621679261267 (_f_69895866216792619016989586621679263701 :: (~>) a7566047373982667509 m7566047373982667510) a_69895866216792619056989586621679263702 a_69895866216792637056989586621679263706
  where
    LamCases_6989586621679263703Sym0KindInference :: SameKind (Apply (LamCases_6989586621679263703Sym0 m6989586621679261267 _f_69895866216792619016989586621679263701 a_69895866216792619056989586621679263702) arg_a143p) (LamCases_6989586621679263703Sym1 m6989586621679261267 _f_69895866216792619016989586621679263701 a_69895866216792619056989586621679263702 arg_a143p) =>
                                                      LamCases_6989586621679263703Sym0 m6989586621679261267 _f_69895866216792619016989586621679263701 a_69895866216792619056989586621679263702 a_69895866216792637056989586621679263706
type instance Apply @_ @_ (LamCases_6989586621679263703Sym0 m6989586621679261267 _f_69895866216792619016989586621679263701 a_69895866216792619056989586621679263702) a_69895866216792637056989586621679263706 = LamCases_6989586621679263703_a143m m6989586621679261267 _f_69895866216792619016989586621679263701 a_69895866216792619056989586621679263702 a_69895866216792637056989586621679263706
instance SuppressUnusedWarnings (LamCases_6989586621679263703Sym0 m6989586621679261267 _f_69895866216792619016989586621679263701 a_69895866216792619056989586621679263702) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679263703Sym0KindInference ())
type family LamCases_6989586621679263703Sym1 m6989586621679261267 (_f_69895866216792619016989586621679263701 :: (~>) a7566047373982667509 m7566047373982667510) a_69895866216792619056989586621679263702 a_69895866216792637056989586621679263706 where
  LamCases_6989586621679263703Sym1 m6989586621679261267 _f_69895866216792619016989586621679263701 a_69895866216792619056989586621679263702 a_69895866216792637056989586621679263706 = LamCases_6989586621679263703_a143m m6989586621679261267 _f_69895866216792619016989586621679263701 a_69895866216792619056989586621679263702 a_69895866216792637056989586621679263706
type FoldMap_6989586621679263694 :: forall m_a13q3
                                            a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU
                                                    -> Const m_a13q3 a_iYVT -> m_iYVU
type family FoldMap_6989586621679263694 @m_a13q3 @a_iYVT @m_iYVU (a_a143e :: (~>) a_iYVT m_iYVU) (a_a143f :: Const m_a13q3 a_iYVT) :: m_iYVU where
  FoldMap_6989586621679263694 @m_a13q3 @a_iYVT @m_iYVU (_f_6989586621679261901_a143j :: (~>) a_iYVT m_iYVU) ('Const a_6989586621679261905_a143k :: Const m_a13q3 a_iYVT) = Apply (LamCases_6989586621679263703Sym0 m_a13q3 _f_6989586621679261901_a143j a_6989586621679261905_a143k) a_6989586621679261905_a143k
type family LamCases_6989586621679263723_a143G m6989586621679261267 (_f_69895866216792619016989586621679263720 :: (~>) a7566047373982667513 ((~>) b7566047373982667514 b7566047373982667514)) (_z_69895866216792619036989586621679263721 :: b7566047373982667514) a_69895866216792619096989586621679263722 a_6989586621679263726_a143J a_6989586621679263728_a143L where
  LamCases_6989586621679263723_a143G m_a13q3 _f_6989586621679261901_a143C _z_6989586621679261903_a143D a_6989586621679261909_a143E _ n_6989586621679261907_a143H = n_6989586621679261907_a143H
data LamCases_6989586621679263723Sym0 m6989586621679261267 (_f_69895866216792619016989586621679263720 :: (~>) a7566047373982667513 ((~>) b7566047373982667514 b7566047373982667514)) (_z_69895866216792619036989586621679263721 :: b7566047373982667514) a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727
  where
    LamCases_6989586621679263723Sym0KindInference :: SameKind (Apply (LamCases_6989586621679263723Sym0 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722) arg_a143M) (LamCases_6989586621679263723Sym1 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 arg_a143M) =>
                                                      LamCases_6989586621679263723Sym0 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727
type instance Apply @_ @_ (LamCases_6989586621679263723Sym0 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722) a_69895866216792637266989586621679263727 = LamCases_6989586621679263723Sym1 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727
instance SuppressUnusedWarnings (LamCases_6989586621679263723Sym0 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679263723Sym0KindInference ())
data LamCases_6989586621679263723Sym1 m6989586621679261267 (_f_69895866216792619016989586621679263720 :: (~>) a7566047373982667513 ((~>) b7566047373982667514 b7566047373982667514)) (_z_69895866216792619036989586621679263721 :: b7566047373982667514) a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727 a_69895866216792637286989586621679263729
  where
    LamCases_6989586621679263723Sym1KindInference :: SameKind (Apply (LamCases_6989586621679263723Sym1 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727) arg_a143M) (LamCases_6989586621679263723Sym2 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727 arg_a143M) =>
                                                      LamCases_6989586621679263723Sym1 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727 a_69895866216792637286989586621679263729
type instance Apply @_ @_ (LamCases_6989586621679263723Sym1 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727) a_69895866216792637286989586621679263729 = LamCases_6989586621679263723_a143G m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727 a_69895866216792637286989586621679263729
instance SuppressUnusedWarnings (LamCases_6989586621679263723Sym1 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679263723Sym1KindInference ())
type family LamCases_6989586621679263723Sym2 m6989586621679261267 (_f_69895866216792619016989586621679263720 :: (~>) a7566047373982667513 ((~>) b7566047373982667514 b7566047373982667514)) (_z_69895866216792619036989586621679263721 :: b7566047373982667514) a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727 a_69895866216792637286989586621679263729 where
  LamCases_6989586621679263723Sym2 m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727 a_69895866216792637286989586621679263729 = LamCases_6989586621679263723_a143G m6989586621679261267 _f_69895866216792619016989586621679263720 _z_69895866216792619036989586621679263721 a_69895866216792619096989586621679263722 a_69895866216792637266989586621679263727 a_69895866216792637286989586621679263729
type Foldr_6989586621679263711 :: forall m_a13q3
                                          a_iYVX
                                          b_iYVY. (~>) a_iYVX ((~>) b_iYVY b_iYVY)
                                                  -> b_iYVY -> Const m_a13q3 a_iYVX -> b_iYVY
type family Foldr_6989586621679263711 @m_a13q3 @a_iYVX @b_iYVY (a_a143v :: (~>) a_iYVX ((~>) b_iYVY b_iYVY)) (a_a143w :: b_iYVY) (a_a143x :: Const m_a13q3 a_iYVX) :: b_iYVY where
  Foldr_6989586621679263711 @m_a13q3 @a_iYVX @b_iYVY (_f_6989586621679261901_a143C :: (~>) a_iYVX ((~>) b_iYVY b_iYVY)) (_z_6989586621679261903_a143D :: b_iYVY) ('Const a_6989586621679261909_a143E :: Const m_a13q3 a_iYVX) = Apply (Apply (LamCases_6989586621679263723Sym0 m_a13q3 _f_6989586621679261901_a143C _z_6989586621679261903_a143D a_6989586621679261909_a143E) a_6989586621679261909_a143E) _z_6989586621679261903_a143D
instance PFoldable (Const m_a13q3) where
  type FoldMap a_a143a a_a143b = FoldMap_6989586621679263694 a_a143a a_a143b
  type Foldr a_a143q a_a143r a_a143s = Foldr_6989586621679263711 a_a143q a_a143r a_a143s
type Pure_6989586621679263732 :: forall m_a13q4 a_iv9m. a_iv9m
                                                        -> Const m_a13q4 a_iv9m
type family Pure_6989586621679263732 @m_a13q4 @a_iv9m (a_a143Q :: a_iv9m) :: Const m_a13q4 a_iv9m where
  Pure_6989586621679263732 @m_a13q4 @a_iv9m (_ :: a_iv9m) = Apply ConstSym0 MemptySym0
type LiftA2_6989586621679263740 :: forall m_a13q4
                                          a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> Const m_a13q4 a_iv9s
                                                      -> Const m_a13q4 b_iv9t
                                                        -> Const m_a13q4 c_iv9u
type family LiftA2_6989586621679263740 @m_a13q4 @a_iv9s @b_iv9t @c_iv9u (a_a143Y :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a143Z :: Const m_a13q4 a_iv9s) (a_a1440 :: Const m_a13q4 b_iv9t) :: Const m_a13q4 c_iv9u where
  LiftA2_6989586621679263740 @m_a13q4 @a_iv9s @b_iv9t @c_iv9u (_ :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) ('Const x_a1445 :: Const m_a13q4 a_iv9s) ('Const y_a1446 :: Const m_a13q4 b_iv9t) = Apply ConstSym0 (Apply (Apply MappendSym0 x_a1445) y_a1446)
type TFHelper_6989586621679263753 :: forall m_a13q4
                                            a_iv9o
                                            b_iv9p. Const m_a13q4 ((~>) a_iv9o b_iv9p)
                                                    -> Const m_a13q4 a_iv9o
                                                        -> Const m_a13q4 b_iv9p
type family TFHelper_6989586621679263753 @m_a13q4 @a_iv9o @b_iv9p (a_a144b :: Const m_a13q4 ((~>) a_iv9o b_iv9p)) (a_a144c :: Const m_a13q4 a_iv9o) :: Const m_a13q4 b_iv9p where
  TFHelper_6989586621679263753 @m_a13q4 @a_iv9o @b_iv9p ('Const x_a144g :: Const m_a13q4 ((~>) a_iv9o b_iv9p)) ('Const y_a144h :: Const m_a13q4 a_iv9o) = Apply ConstSym0 (Apply (Apply MappendSym0 x_a144g) y_a144h)
instance PApplicative (Const m_a13q4) where
  type Pure a_a143N = Pure_6989586621679263732 a_a143N
  type LiftA2 a_a143T a_a143U a_a143V = LiftA2_6989586621679263740 a_a143T a_a143U a_a143V
  type (<*>) a_a1447 a_a1448 = TFHelper_6989586621679263753 a_a1447 a_a1448
instance SBounded a_a13pp => SBounded (Const a_a13pp b_a13pq) where
  sMinBound = applySing (singFun1 @ConstSym0 SConst) sMinBound
  sMaxBound = applySing (singFun1 @ConstSym0 SConst) sMaxBound
instance SEq a_a13pr => SEq (Const a_a13pr b_a13ps) where
  (%==)
    (SConst (sA_6989586621679261872 :: Sing a_6989586621679261872_a13KK))
    (SConst (sB_6989586621679261874 :: Sing b_6989586621679261874_a13KL))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679261872)
        sB_6989586621679261874
instance SOrd a_a13pt => SOrd (Const a_a13pt b_a13pu) where
  sCompare
    (SConst (sA_6989586621679261879 :: Sing a_6989586621679261879_a140e))
    (SConst (sB_6989586621679261881 :: Sing b_6989586621679261881_a140f))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679261879)
                  sB_6989586621679261881))
            SNil)
instance SEnum a_a13pv => SEnum (Const a_a13pv b_a13pw) where
  sSucc (SConst (sX :: Sing x_a140m))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (singFun1 @SuccSym0 sSucc) sX)
  sPred (SConst (sX :: Sing x_a140t))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (singFun1 @PredSym0 sPred) sX)
  sToEnum (sI :: Sing i_a140A)
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (singFun1 @ToEnumSym0 sToEnum) sI)
  sFromEnum (SConst (sX :: Sing x_a140H))
    = applySing (singFun1 @FromEnumSym0 sFromEnum) sX
  sEnumFromTo
    (SConst (sX :: Sing x_a140R))
    (SConst (sY :: Sing y_a140S))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @ConstSym0 SConst))
        (applySing
            (applySing (singFun2 @EnumFromToSym0 sEnumFromTo) sX) sY)
  sEnumFromThenTo
    (SConst (sX :: Sing x_a1415))
    (SConst (sY :: Sing y_a1416))
    (SConst (sZ :: Sing z_a1417))
    = applySing
        (applySing (singFun2 @MapSym0 sMap) (singFun1 @ConstSym0 SConst))
        (applySing
            (applySing
              (applySing (singFun3 @EnumFromThenToSym0 sEnumFromThenTo) sX) sY)
            sZ)
instance SMonoid a_a13pG => SMonoid (Const a_a13pG b_a13pH) where
  sMempty = applySing (singFun1 @ConstSym0 SConst) sMempty
instance SNum a_a13pI => SNum (Const a_a13pI b_a13pJ) where
  (%+) (SConst (sX :: Sing x_a141k)) (SConst (sY :: Sing y_a141l))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (applySing (singFun2 @(+@#@$) (%+)) sX) sY)
  (%-) (SConst (sX :: Sing x_a141v)) (SConst (sY :: Sing y_a141w))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (applySing (singFun2 @(-@#@$) (%-)) sX) sY)
  (%*) (SConst (sX :: Sing x_a141G)) (SConst (sY :: Sing y_a141H))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (applySing (singFun2 @(*@#@$) (%*)) sX) sY)
  sNegate (SConst (sX :: Sing x_a141O))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (singFun1 @NegateSym0 sNegate) sX)
  sAbs (SConst (sX :: Sing x_a141V))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (singFun1 @AbsSym0 sAbs) sX)
  sSignum (SConst (sX :: Sing x_a1422))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (singFun1 @SignumSym0 sSignum) sX)
  sFromInteger (sN :: Sing n_a1429)
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (singFun1 @FromIntegerSym0 sFromInteger) sN)
instance SSemigroup a_a13pU =>
          SSemigroup (Const a_a13pU b_a13pV) where
  (%<>) (SConst (sX :: Sing x_a142j)) (SConst (sY :: Sing y_a142k))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sX) sY)
instance SShow a_a13pY => SShow (Const a_a13pY b_a13pZ) where
  sShowsPrec
    (sD :: Sing d_a142z)
    (SConst (sX :: Sing x_a142A))
    (sA_6989586621679263646 :: Sing a_6989586621679263646_a142B)
    = applySing
        (applySing
            (applySing
              (singFun2 @($@#@$) (%$))
              (applySing
                  (singFun3 @ShowParenSym0 sShowParen)
                  (applySing
                    (applySing (singFun2 @(>@#@$) (%>)) sD)
                    (sFromInteger (sing :: Sing 10)))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Const ")))
              (applySing
                  (applySing
                    (singFun3 @ShowsPrecSym0 sShowsPrec)
                    (sFromInteger (sing :: Sing 11)))
                  sX)))
        sA_6989586621679263646
instance SFunctor (Const m_a13q2) where
  sFmap
    (_sf_6989586621679261886 :: Sing _f_6989586621679261886_a142L)
    (SConst (sA_6989586621679261892 :: Sing a_6989586621679261892_a142M))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing
            (singFun1
              @(LamCases_6989586621679263669Sym0 m_a13q2 _f_6989586621679261886_a142L a_6989586621679261892_a142M)
              (\cases
                  (sN_6989586621679261890 :: Sing n_6989586621679261890_a142P)
                    -> sN_6989586621679261890))
            sA_6989586621679261892)
  (%<$)
    (_sz_6989586621679261888 :: Sing _z_6989586621679261888_a1432)
    (SConst (sA_6989586621679261896 :: Sing a_6989586621679261896_a1433))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing
            (singFun1
              @(LamCases_6989586621679263686Sym0 m_a13q2 _z_6989586621679261888_a1432 a_6989586621679261896_a1433)
              (\cases
                  (sN_6989586621679261894 :: Sing n_6989586621679261894_a1436)
                    -> sN_6989586621679261894))
            sA_6989586621679261896)
instance SFoldable (Const m_a13q3) where
  sFoldMap
    (_sf_6989586621679261901 :: Sing _f_6989586621679261901_a143j)
    (SConst (sA_6989586621679261905 :: Sing a_6989586621679261905_a143k))
    = applySing
        (singFun1
            @(LamCases_6989586621679263703Sym0 m_a13q3 _f_6989586621679261901_a143j a_6989586621679261905_a143k)
            (\cases _ -> sMempty))
        sA_6989586621679261905
  sFoldr
    (_sf_6989586621679261901 :: Sing _f_6989586621679261901_a143C)
    (_sz_6989586621679261903 :: Sing _z_6989586621679261903_a143D)
    (SConst (sA_6989586621679261909 :: Sing a_6989586621679261909_a143E))
    = applySing
        (applySing
            (singFun2
              @(LamCases_6989586621679263723Sym0 m_a13q3 _f_6989586621679261901_a143C _z_6989586621679261903_a143D a_6989586621679261909_a143E)
              (\cases
                  _ (sN_6989586621679261907 :: Sing n_6989586621679261907_a143H)
                    -> sN_6989586621679261907))
            sA_6989586621679261909)
        _sz_6989586621679261903
instance SMonoid m_a13q4 => SApplicative (Const m_a13q4) where
  sPure _ = applySing (singFun1 @ConstSym0 SConst) sMempty
  sLiftA2
    _
    (SConst (sX :: Sing x_a1445))
    (SConst (sY :: Sing y_a1446))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (applySing (singFun2 @MappendSym0 sMappend) sX) sY)
  (%<*>) (SConst (sX :: Sing x_a144g)) (SConst (sY :: Sing y_a144h))
    = applySing
        (singFun1 @ConstSym0 SConst)
        (applySing (applySing (singFun2 @MappendSym0 sMappend) sX) sY)
instance SDecide a_a13pr => SDecide (Const a_a13pr b_a13ps) where
  (%~) (SConst a_a144p) (SConst b_a144q)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a144r)
            -> Disproved (\cases Refl -> contra_a144r Refl))
        ((%~) a_a144p b_a144q)
instance Eq (SConst (z_a144s :: Const a_a13pr b_a13ps)) where
  (==) _ _ = True
instance SDecide a_a13pr =>
          Data.Type.Equality.TestEquality (SConst :: Const a_a13pr b_a13ps
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_a13pr =>
          Data.Type.Coercion.TestCoercion (SConst :: Const a_a13pr b_a13ps
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance Ord (SConst (z_a144t :: Const a_a13pt b_a13pu)) where
  compare _ _ = EQ

