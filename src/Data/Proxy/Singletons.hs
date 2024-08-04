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
-- Module      :  Data.Proxy.Singletons
-- Copyright   :  (C) 2020 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Exports promoted and singled versions of the definitions in "Data.Proxy".
--
-----------------------------------------------------------------------------

module Data.Proxy.Singletons (
    -- * The 'Proxy' singleton
    Sing, SProxy(..)
  , AsProxyTypeOf, sAsProxyTypeOf

    -- * Defunctionalization symbols
  , ProxySym0
  , AsProxyTypeOfSym0, AsProxyTypeOfSym1, AsProxyTypeOfSym2
  ) where


import Control.Monad.Singletons.Internal
import Data.Eq.Singletons
import Data.Monoid.Singletons
import Data.Ord.Singletons
import Data.Proxy
import Data.Semigroup.Singletons.Internal.Classes
import Data.Singletons.Decide
import Data.Singletons.Base.Enum
import Data.Singletons.Base.Instances
import Data.Singletons.TH
import Data.Type.Coercion
import Data.Type.Equality hiding (type (==))
import GHC.Base.Singletons
import GHC.Num.Singletons
import GHC.TypeLits.Singletons.Internal
import Text.Show.Singletons
import Data.Kind (Type)
import qualified GHC.Base

type ProxySym0 :: forall {k_a3H5U :: Type}
                             (t_a3H5V :: k_a3H5U). Proxy t_a3H5V
type family ProxySym0 @(t_a3H5V :: k_a3H5U) :: Proxy t_a3H5V where
  ProxySym0 = 'Proxy
type SProxy :: forall {k_a3H5U :: Type}
                      (t_a3H5V :: k_a3H5U). Proxy t_a3H5V -> Type
data SProxy :: forall {k_a3H5U :: Type} (t_a3H5V :: k_a3H5U).
                Proxy t_a3H5V -> Type
  where
    SProxy :: forall {k_a3H5U :: Type} (t_a3H5V :: k_a3H5U).
              SProxy ('Proxy :: Proxy t_a3H5V)
type instance Sing @(Proxy t_a3H5V) = SProxy
instance SingI 'Proxy where
  sing = SProxy

instance SingKind (Proxy t) where
  type Demote (Proxy t) = Proxy t
  fromSing SProxy = Proxy
  toSing Proxy = SomeSing SProxy

instance Eq (SProxy z) where
  _ == _ = True

instance SDecide (Proxy t) where
  SProxy %~ SProxy = Proved Refl

instance TestEquality SProxy where
  testEquality = decideEquality

instance TestCoercion SProxy where
  testCoercion = decideCoercion

instance Ord (SProxy z) where
  compare _ _ = EQ

instance Show (SProxy z) where
  showsPrec _ _ = showString "SProxy"

type AsProxyTypeOfSym0 :: (~>) a_a3HoG ((~>) (proxy_a3HoH a_a3HoG) a_a3HoG)
data AsProxyTypeOfSym0 :: (~>) a_a3HoG ((~>) (proxy_a3HoH a_a3HoG) a_a3HoG)
  where
    AsProxyTypeOfSym0KindInference :: SameKind (Apply AsProxyTypeOfSym0 arg_a3HQx) (AsProxyTypeOfSym1 arg_a3HQx) =>
                                      AsProxyTypeOfSym0 a6989586621679893326
type instance Apply @a_a3HoG @((~>) (proxy_a3HoH a_a3HoG) a_a3HoG) AsProxyTypeOfSym0 a6989586621679893326 = AsProxyTypeOfSym1 a6989586621679893326
instance SuppressUnusedWarnings AsProxyTypeOfSym0 where
  suppressUnusedWarnings
    = snd ((,) AsProxyTypeOfSym0KindInference ())
type AsProxyTypeOfSym1 :: a_a3HoG
                          -> (~>) (proxy_a3HoH a_a3HoG) a_a3HoG
data AsProxyTypeOfSym1 (a6989586621679893326 :: a_a3HoG) :: (~>) (proxy_a3HoH a_a3HoG) a_a3HoG
  where
    AsProxyTypeOfSym1KindInference :: SameKind (Apply (AsProxyTypeOfSym1 a6989586621679893326) arg_a3HQx) (AsProxyTypeOfSym2 a6989586621679893326 arg_a3HQx) =>
                                      AsProxyTypeOfSym1 a6989586621679893326 a6989586621679893327
type instance Apply @(proxy_a3HoH a_a3HoG) @a_a3HoG (AsProxyTypeOfSym1 a6989586621679893326) a6989586621679893327 = AsProxyTypeOf a6989586621679893326 a6989586621679893327
instance SuppressUnusedWarnings (AsProxyTypeOfSym1 a6989586621679893326) where
  suppressUnusedWarnings
    = snd ((,) AsProxyTypeOfSym1KindInference ())
type AsProxyTypeOfSym2 :: a_a3HoG -> proxy_a3HoH a_a3HoG -> a_a3HoG
type family AsProxyTypeOfSym2 @a_a3HoG @proxy_a3HoH (a6989586621679893326 :: a_a3HoG) (a6989586621679893327 :: proxy_a3HoH a_a3HoG) :: a_a3HoG where
  AsProxyTypeOfSym2 a6989586621679893326 a6989586621679893327 = AsProxyTypeOf a6989586621679893326 a6989586621679893327
type AsProxyTypeOf :: a_a3HoG -> proxy_a3HoH a_a3HoG -> a_a3HoG
type family AsProxyTypeOf @a_a3HoG @proxy_a3HoH (a_a3HQv :: a_a3HoG) (a_a3HQw :: proxy_a3HoH a_a3HoG) :: a_a3HoG where
  AsProxyTypeOf a_6989586621679893319_a3HQA a_6989586621679893321_a3HQB = Apply (Apply ConstSym0 a_6989586621679893319_a3HQA) a_6989586621679893321_a3HQB
type MinBound_6989586621679893378 :: forall s_a3HoJ. Proxy s_a3HoJ
type family MinBound_6989586621679893378 @s_a3HoJ :: Proxy s_a3HoJ where
  MinBound_6989586621679893378 @s_a3HoJ = ProxySym0
type MaxBound_6989586621679893381 :: forall s_a3HoJ. Proxy s_a3HoJ
type family MaxBound_6989586621679893381 @s_a3HoJ :: Proxy s_a3HoJ where
  MaxBound_6989586621679893381 @s_a3HoJ = ProxySym0
instance PBounded (Proxy s_a3HoJ) where
  type MinBound = MinBound_6989586621679893378
  type MaxBound = MaxBound_6989586621679893381
type TFHelper_6989586621679893408 :: forall s_a3HoK. Proxy s_a3HoK
                                                      -> Proxy s_a3HoK -> Bool
type family TFHelper_6989586621679893408 @s_a3HoK (a_a3HRU :: Proxy s_a3HoK) (a_a3HRV :: Proxy s_a3HoK) :: Bool where
  TFHelper_6989586621679893408 @s_a3HoK (_ :: Proxy s_a3HoK) (_ :: Proxy s_a3HoK) = TrueSym0
instance PEq (Proxy s_a3HoK) where
  type (==) a_a3HRQ a_a3HRR = TFHelper_6989586621679893408 a_a3HRQ a_a3HRR
type Compare_6989586621679893469 :: forall s_a3HoL. Proxy s_a3HoL
                                                    -> Proxy s_a3HoL -> Ordering
type family Compare_6989586621679893469 @s_a3HoL (a_a3HST :: Proxy s_a3HoL) (a_a3HSU :: Proxy s_a3HoL) :: Ordering where
  Compare_6989586621679893469 @s_a3HoL (_ :: Proxy s_a3HoL) (_ :: Proxy s_a3HoL) = EQSym0
instance POrd (Proxy s_a3HoL) where
  type Compare a_a3HSP a_a3HSQ = Compare_6989586621679893469 a_a3HSP a_a3HSQ
type ShowsPrec_6989586621679893509 :: forall s_a3HoM. Natural
                                                      -> Proxy s_a3HoM -> Symbol -> Symbol
type family ShowsPrec_6989586621679893509 @s_a3HoM (a_a3HTz :: Natural) (a_a3HTA :: Proxy s_a3HoM) (a_a3HTB :: Symbol) :: Symbol where
  ShowsPrec_6989586621679893509 @s_a3HoM (_ :: Natural) (_ :: Proxy s_a3HoM) (a_6989586621679893511_a3HTG :: Symbol) = Apply (Apply ShowStringSym0 "Proxy") a_6989586621679893511_a3HTG
instance PShow (Proxy s_a3HoM) where
  type ShowsPrec a_a3HTs a_a3HTt a_a3HTu = ShowsPrec_6989586621679893509 a_a3HTs a_a3HTt a_a3HTu
type Succ_6989586621679893595 :: forall s_a3HoN. Proxy s_a3HoN
                                                  -> Proxy s_a3HoN
type family Succ_6989586621679893595 @s_a3HoN (a_a3HUV :: Proxy s_a3HoN) :: Proxy s_a3HoN where
  Succ_6989586621679893595 @s_a3HoN (_ :: Proxy s_a3HoN) = Apply ErrorWithoutStackTraceSym0 "Proxy.succ"
type Pred_6989586621679893601 :: forall s_a3HoN. Proxy s_a3HoN
                                                  -> Proxy s_a3HoN
type family Pred_6989586621679893601 @s_a3HoN (a_a3HV1 :: Proxy s_a3HoN) :: Proxy s_a3HoN where
  Pred_6989586621679893601 @s_a3HoN (_ :: Proxy s_a3HoN) = Apply ErrorWithoutStackTraceSym0 "Proxy.pred"
type FromEnum_6989586621679893607 :: forall s_a3HoN. Proxy s_a3HoN
                                                      -> Natural
type family FromEnum_6989586621679893607 @s_a3HoN (a_a3HV7 :: Proxy s_a3HoN) :: Natural where
  FromEnum_6989586621679893607 @s_a3HoN (_ :: Proxy s_a3HoN) = FromInteger 0
type family LamCases_6989586621679893619_a3HVi s6989586621679891605 (n6989586621679893618 :: Natural) a_6989586621679893621_a3HVk where
  LamCases_6989586621679893619_a3HVi s_a3HoN n_a3HVg 'True = ProxySym0
  LamCases_6989586621679893619_a3HVi s_a3HoN n_a3HVg 'False = Apply ErrorWithoutStackTraceSym0 "Proxy.toEnum: 0 expected"
data LamCases_6989586621679893619Sym0 s6989586621679891605 (n6989586621679893618 :: Natural) a_69895866216798936216989586621679893622
  where
    LamCases_6989586621679893619Sym0KindInference :: SameKind (Apply (LamCases_6989586621679893619Sym0 s6989586621679891605 n6989586621679893618) arg_a3HVl) (LamCases_6989586621679893619Sym1 s6989586621679891605 n6989586621679893618 arg_a3HVl) =>
                                                      LamCases_6989586621679893619Sym0 s6989586621679891605 n6989586621679893618 a_69895866216798936216989586621679893622
type instance Apply @_ @_ (LamCases_6989586621679893619Sym0 s6989586621679891605 n6989586621679893618) a_69895866216798936216989586621679893622 = LamCases_6989586621679893619_a3HVi s6989586621679891605 n6989586621679893618 a_69895866216798936216989586621679893622
instance SuppressUnusedWarnings (LamCases_6989586621679893619Sym0 s6989586621679891605 n6989586621679893618) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679893619Sym0KindInference ())
type family LamCases_6989586621679893619Sym1 s6989586621679891605 (n6989586621679893618 :: Natural) a_69895866216798936216989586621679893622 where
  LamCases_6989586621679893619Sym1 s6989586621679891605 n6989586621679893618 a_69895866216798936216989586621679893622 = LamCases_6989586621679893619_a3HVi s6989586621679891605 n6989586621679893618 a_69895866216798936216989586621679893622
type ToEnum_6989586621679893613 :: forall s_a3HoN. Natural
                                                    -> Proxy s_a3HoN
type family ToEnum_6989586621679893613 @s_a3HoN (a_a3HVd :: Natural) :: Proxy s_a3HoN where
  ToEnum_6989586621679893613 @s_a3HoN (n_a3HVg :: Natural) = Apply (LamCases_6989586621679893619Sym0 s_a3HoN n_a3HVg) (Apply (Apply (==@#@$) n_a3HVg) (FromInteger 0))
type EnumFromThenTo_6989586621679893627 :: forall s_a3HoN. Proxy s_a3HoN
                                                            -> Proxy s_a3HoN
                                                              -> Proxy s_a3HoN
                                                                  -> [Proxy s_a3HoN]
type family EnumFromThenTo_6989586621679893627 @s_a3HoN (a_a3HVr :: Proxy s_a3HoN) (a_a3HVs :: Proxy s_a3HoN) (a_a3HVt :: Proxy s_a3HoN) :: [Proxy s_a3HoN] where
  EnumFromThenTo_6989586621679893627 @s_a3HoN (_ :: Proxy s_a3HoN) (_ :: Proxy s_a3HoN) (_ :: Proxy s_a3HoN) = Apply (Apply (:@#@$) ProxySym0) NilSym0
type EnumFromTo_6989586621679893638 :: forall s_a3HoN. Proxy s_a3HoN
                                                        -> Proxy s_a3HoN -> [Proxy s_a3HoN]
type family EnumFromTo_6989586621679893638 @s_a3HoN (a_a3HVC :: Proxy s_a3HoN) (a_a3HVD :: Proxy s_a3HoN) :: [Proxy s_a3HoN] where
  EnumFromTo_6989586621679893638 @s_a3HoN (_ :: Proxy s_a3HoN) (_ :: Proxy s_a3HoN) = Apply (Apply (:@#@$) ProxySym0) NilSym0
instance PEnum (Proxy s_a3HoN) where
  type Succ a_a3HUS = Succ_6989586621679893595 a_a3HUS
  type Pred a_a3HUY = Pred_6989586621679893601 a_a3HUY
  type FromEnum a_a3HV4 = FromEnum_6989586621679893607 a_a3HV4
  type ToEnum a_a3HVa = ToEnum_6989586621679893613 a_a3HVa
  type EnumFromThenTo a_a3HVm a_a3HVn a_a3HVo = EnumFromThenTo_6989586621679893627 a_a3HVm a_a3HVn a_a3HVo
  type EnumFromTo a_a3HVy a_a3HVz = EnumFromTo_6989586621679893638 a_a3HVy a_a3HVz
type TFHelper_6989586621679893667 :: forall s_a3HoP. Proxy s_a3HoP
                                                      -> Proxy s_a3HoP -> Proxy s_a3HoP
type family TFHelper_6989586621679893667 @s_a3HoP (a_a3HW5 :: Proxy s_a3HoP) (a_a3HW6 :: Proxy s_a3HoP) :: Proxy s_a3HoP where
  TFHelper_6989586621679893667 @s_a3HoP (_ :: Proxy s_a3HoP) (_ :: Proxy s_a3HoP) = ProxySym0
type Sconcat_6989586621679893675 :: forall s_a3HoP. GHC.Base.NonEmpty (Proxy s_a3HoP)
                                                    -> Proxy s_a3HoP
type family Sconcat_6989586621679893675 @s_a3HoP (a_a3HWd :: GHC.Base.NonEmpty (Proxy s_a3HoP)) :: Proxy s_a3HoP where
  Sconcat_6989586621679893675 @s_a3HoP (_ :: GHC.Base.NonEmpty (Proxy s_a3HoP)) = ProxySym0
instance PSemigroup (Proxy s_a3HoP) where
  type (<>) a_a3HW1 a_a3HW2 = TFHelper_6989586621679893667 a_a3HW1 a_a3HW2
  type Sconcat a_a3HWa = Sconcat_6989586621679893675 a_a3HWa
type Mempty_6989586621679893888 :: forall s_a3HoQ. Proxy s_a3HoQ
type family Mempty_6989586621679893888 @s_a3HoQ :: Proxy s_a3HoQ where
  Mempty_6989586621679893888 @s_a3HoQ = ProxySym0
type Mconcat_6989586621679893892 :: forall s_a3HoQ. [Proxy s_a3HoQ]
                                                    -> Proxy s_a3HoQ
type family Mconcat_6989586621679893892 @s_a3HoQ (a_a3HZI :: [Proxy s_a3HoQ]) :: Proxy s_a3HoQ where
  Mconcat_6989586621679893892 @s_a3HoQ (_ :: [Proxy s_a3HoQ]) = ProxySym0
instance PMonoid (Proxy s_a3HoQ) where
  type Mempty = Mempty_6989586621679893888
  type Mconcat a_a3HZF = Mconcat_6989586621679893892 a_a3HZF
type Fmap_6989586621679893931 :: forall a_i1v3K
                                        b_i1v3L. (~>) a_i1v3K b_i1v3L
                                                  -> Proxy a_i1v3K -> Proxy b_i1v3L
type family Fmap_6989586621679893931 @a_i1v3K @b_i1v3L (a_a3I0l :: (~>) a_i1v3K b_i1v3L) (a_a3I0m :: Proxy a_i1v3K) :: Proxy b_i1v3L where
  Fmap_6989586621679893931 @a_i1v3K @b_i1v3L _ _ = ProxySym0
instance PFunctor Proxy where
  type Fmap a_a3I0h a_a3I0i = Fmap_6989586621679893931 a_a3I0h a_a3I0i
type Pure_6989586621679893991 :: forall a_i1v3p. a_i1v3p
                                                  -> Proxy a_i1v3p
type family Pure_6989586621679893991 @a_i1v3p (a_a3I1j :: a_i1v3p) :: Proxy a_i1v3p where
  Pure_6989586621679893991 @a_i1v3p _ = ProxySym0
type TFHelper_6989586621679893998 :: forall a_i1v3r
                                            b_i1v3s. Proxy ((~>) a_i1v3r b_i1v3s)
                                                      -> Proxy a_i1v3r -> Proxy b_i1v3s
type family TFHelper_6989586621679893998 @a_i1v3r @b_i1v3s (a_a3I1q :: Proxy ((~>) a_i1v3r b_i1v3s)) (a_a3I1r :: Proxy a_i1v3r) :: Proxy b_i1v3s where
  TFHelper_6989586621679893998 @a_i1v3r @b_i1v3s _ _ = ProxySym0
instance PApplicative Proxy where
  type Pure a_a3I1g = Pure_6989586621679893991 a_a3I1g
  type (<*>) a_a3I1m a_a3I1n = TFHelper_6989586621679893998 a_a3I1m a_a3I1n
type Empty_6989586621679894019 :: forall a_i1v3T. Proxy a_i1v3T
type family Empty_6989586621679894019 @a_i1v3T :: Proxy a_i1v3T where
  Empty_6989586621679894019 @a_i1v3T = ProxySym0
type TFHelper_6989586621679894024 :: forall a_i1v3U. Proxy a_i1v3U
                                                      -> Proxy a_i1v3U -> Proxy a_i1v3U
type family TFHelper_6989586621679894024 @a_i1v3U (a_a3I1Q :: Proxy a_i1v3U) (a_a3I1R :: Proxy a_i1v3U) :: Proxy a_i1v3U where
  TFHelper_6989586621679894024 @a_i1v3U _ _ = ProxySym0
instance PAlternative Proxy where
  type Empty = Empty_6989586621679894019
  type (<|>) a_a3I1M a_a3I1N = TFHelper_6989586621679894024 a_a3I1M a_a3I1N
type TFHelper_6989586621679894061 :: forall a_i1v3Y
                                            b_i1v3Z. Proxy a_i1v3Y
                                                      -> (~>) a_i1v3Y (Proxy b_i1v3Z)
                                                        -> Proxy b_i1v3Z
type family TFHelper_6989586621679894061 @a_i1v3Y @b_i1v3Z (a_a3I2r :: Proxy a_i1v3Y) (a_a3I2s :: (~>) a_i1v3Y (Proxy b_i1v3Z)) :: Proxy b_i1v3Z where
  TFHelper_6989586621679894061 @a_i1v3Y @b_i1v3Z _ _ = ProxySym0
instance PMonad Proxy where
  type (>>=) a_a3I2n a_a3I2o = TFHelper_6989586621679894061 a_a3I2n a_a3I2o
instance PMonadPlus Proxy
sAsProxyTypeOf ::
  (forall (t_a3I2K :: a_a3HoG) (t_a3I2L :: proxy_a3HoH a_a3HoG).
    Sing t_a3I2K
    -> Sing t_a3I2L
      -> Sing (AsProxyTypeOf t_a3I2K t_a3I2L :: a_a3HoG) :: Type)
sAsProxyTypeOf
  (sA_6989586621679893319 :: Sing a_6989586621679893319_a3HQA)
  (sA_6989586621679893321 :: Sing a_6989586621679893321_a3HQB)
  = applySing
      (applySing (singFun2 @ConstSym0 sConst) sA_6989586621679893319)
      sA_6989586621679893321
instance SingI (AsProxyTypeOfSym0 :: (~>) a_a3HoG ((~>) (proxy_a3HoH a_a3HoG) a_a3HoG)) where
  sing = singFun2 @AsProxyTypeOfSym0 sAsProxyTypeOf
instance SingI d_a3I2M =>
          SingI (AsProxyTypeOfSym1 (d_a3I2M :: a_a3HoG) :: (~>) (proxy_a3HoH a_a3HoG) a_a3HoG) where
  sing
    = singFun1
        @(AsProxyTypeOfSym1 (d_a3I2M :: a_a3HoG))
        (sAsProxyTypeOf (sing @d_a3I2M))
instance SingI1 (AsProxyTypeOfSym1 :: a_a3HoG
                                      -> (~>) (proxy_a3HoH a_a3HoG) a_a3HoG) where
  liftSing (s_a3I2O :: Sing (d_a3I2M :: a_a3HoG))
    = singFun1
        @(AsProxyTypeOfSym1 (d_a3I2M :: a_a3HoG)) (sAsProxyTypeOf s_a3I2O)
instance SBounded (Proxy s_a3HoJ) where
  sMinBound = SProxy
  sMaxBound = SProxy
instance SEq (Proxy s_a3HoK) where
  (%==) _ _ = STrue
instance SOrd (Proxy s_a3HoL) where
  sCompare _ _ = SEQ
instance SShow (Proxy s_a3HoM) where
  sShowsPrec
    _
    _
    (sA_6989586621679893511 :: Sing a_6989586621679893511_a3HTG)
    = applySing
        (applySing
            (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Proxy"))
        sA_6989586621679893511
instance SEnum (Proxy s_a3HoN) where
  sSucc _
    = applySing
        (singFun1 @ErrorWithoutStackTraceSym0 sErrorWithoutStackTrace)
        (sing :: Sing "Proxy.succ")
  sPred _
    = applySing
        (singFun1 @ErrorWithoutStackTraceSym0 sErrorWithoutStackTrace)
        (sing :: Sing "Proxy.pred")
  sFromEnum _ = sFromInteger (sing :: Sing 0)
  sToEnum (sN :: Sing n_a3HVg)
    = applySing
        (singFun1
            @(LamCases_6989586621679893619Sym0 s_a3HoN n_a3HVg)
            (\cases
              STrue -> SProxy
              SFalse
                -> applySing
                      (singFun1 @ErrorWithoutStackTraceSym0 sErrorWithoutStackTrace)
                      (sing :: Sing "Proxy.toEnum: 0 expected")))
        (applySing
            (applySing (singFun2 @(==@#@$) (%==)) sN)
            (sFromInteger (sing :: Sing 0)))
  sEnumFromThenTo _ _ _
    = applySing (applySing (singFun2 @(:@#@$) SCons) SProxy) SNil
  sEnumFromTo _ _
    = applySing (applySing (singFun2 @(:@#@$) SCons) SProxy) SNil
instance SSemigroup (Proxy s_a3HoP) where
  (%<>) _ _ = SProxy
  sSconcat _ = SProxy
instance SMonoid (Proxy s_a3HoQ) where
  sMempty = SProxy
  sMconcat _ = SProxy
instance SFunctor Proxy where
  sFmap _ _ = SProxy
instance SApplicative Proxy where
  sPure _ = SProxy
  (%<*>) _ _ = SProxy
instance SAlternative Proxy where
  sEmpty = SProxy
  (%<|>) _ _ = SProxy
instance SMonad Proxy where
  (%>>=) _ _ = SProxy
instance SMonadPlus Proxy
