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
-- Module      :  Data.Functor.Sum.Singletons
-- Copyright   :  (C) 2021 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Exports the promoted and singled versions of the 'Sum' data type.
--
-----------------------------------------------------------------------------

module Data.Functor.Sum.Singletons (
  -- * The 'Product' singleton
  Sing, SSum(..),

  -- * Defunctionalization symbols
  InLSym0, InLSym1,
  InRSym0, InRSym1,
  ) where

import Data.Bool.Singletons
import Data.Eq.Singletons
import Data.Foldable.Singletons hiding (Sum)
import Data.Functor.Singletons
import Data.Functor.Sum
import Data.Ord.Singletons
import Data.Semigroup.Singletons hiding (SSum(..))
import Data.Singletons.Base.Instances (SList(..), (:@#@$), NilSym0)
import Data.Singletons.TH
import Data.Traversable.Singletons
import Data.Kind (Type)
import qualified Data.Type.Equality
import qualified Data.Type.Coercion
import qualified Data.Singletons.Decide
type InLSym0 :: forall {k_as8c :: Type}
                           (f_as8d :: k_as8c -> Type)
                           (g_as8e :: k_as8c -> Type)
                           (a_as8f :: k_as8c). (~>) (f_as8d a_as8f) (Sum f_as8d g_as8e a_as8f)
data InLSym0 :: (~>) (f_as8d a_as8f) (Sum f_as8d g_as8e a_as8f)
  where
    InLSym0KindInference :: SameKind (Apply InLSym0 arg_a29bH) (InLSym1 arg_a29bH) =>
                            InLSym0 a6989586621679521770
type instance Apply @(f_as8d a_as8f) @(Sum f_as8d g_as8e a_as8f) InLSym0 a6989586621679521770 = 'InL a6989586621679521770
instance SuppressUnusedWarnings InLSym0 where
  suppressUnusedWarnings = snd ((,) InLSym0KindInference ())
type InLSym1 :: forall {k_as8c :: Type}
                        (f_as8d :: k_as8c -> Type)
                        (g_as8e :: k_as8c -> Type)
                        (a_as8f :: k_as8c). f_as8d a_as8f -> Sum f_as8d g_as8e a_as8f
type family InLSym1 @(f_as8d :: k_as8c -> Type) @(g_as8e :: k_as8c
                                                            -> Type) @(a_as8f :: k_as8c) (a6989586621679521770 :: f_as8d a_as8f) :: Sum f_as8d g_as8e a_as8f where
  InLSym1 a6989586621679521770 = 'InL a6989586621679521770
type InRSym0 :: forall {k_as8c :: Type}
                        (f_as8d :: k_as8c -> Type)
                        (g_as8e :: k_as8c -> Type)
                        (a_as8f :: k_as8c). (~>) (g_as8e a_as8f) (Sum f_as8d g_as8e a_as8f)
data InRSym0 :: (~>) (g_as8e a_as8f) (Sum f_as8d g_as8e a_as8f)
  where
    InRSym0KindInference :: SameKind (Apply InRSym0 arg_a29bJ) (InRSym1 arg_a29bJ) =>
                            InRSym0 a6989586621679521772
type instance Apply @(g_as8e a_as8f) @(Sum f_as8d g_as8e a_as8f) InRSym0 a6989586621679521772 = 'InR a6989586621679521772
instance SuppressUnusedWarnings InRSym0 where
  suppressUnusedWarnings = snd ((,) InRSym0KindInference ())
type InRSym1 :: forall {k_as8c :: Type}
                        (f_as8d :: k_as8c -> Type)
                        (g_as8e :: k_as8c -> Type)
                        (a_as8f :: k_as8c). g_as8e a_as8f -> Sum f_as8d g_as8e a_as8f
type family InRSym1 @(f_as8d :: k_as8c -> Type) @(g_as8e :: k_as8c
                                                            -> Type) @(a_as8f :: k_as8c) (a6989586621679521772 :: g_as8e a_as8f) :: Sum f_as8d g_as8e a_as8f where
  InRSym1 a6989586621679521772 = 'InR a6989586621679521772
type SSum :: forall {k_as8c :: Type}
                    (f_as8d :: k_as8c -> Type)
                    (g_as8e :: k_as8c -> Type)
                    (a_as8f :: k_as8c). Sum f_as8d g_as8e a_as8f -> Type
data SSum :: forall {k_as8c :: Type}
                    (f_as8d :: k_as8c -> Type)
                    (g_as8e :: k_as8c -> Type)
                    (a_as8f :: k_as8c).
              Sum f_as8d g_as8e a_as8f -> Type
  where
    SInL :: forall {k_as8c :: Type}
                    (f_as8d :: k_as8c -> Type)
                    (g_as8e :: k_as8c -> Type)
                    (a_as8f :: k_as8c)
                    (n_a29bL :: f_as8d a_as8f).
            (Sing n_a29bL) -> SSum ('InL n_a29bL :: Sum f_as8d g_as8e a_as8f)
    SInR :: forall {k_as8c :: Type}
                    (f_as8d :: k_as8c -> Type)
                    (g_as8e :: k_as8c -> Type)
                    (a_as8f :: k_as8c)
                    (n_a29bN :: g_as8e a_as8f).
            (Sing n_a29bN) -> SSum ('InR n_a29bN :: Sum f_as8d g_as8e a_as8f)
type instance Sing @(Sum f_as8d g_as8e a_as8f) = SSum
instance SingI n_a29bL =>
          SingI ('InL (n_a29bL :: f_as8d a_as8f)) where
  sing = SInL sing
instance SingI1 'InL where
  liftSing = SInL
instance SingI (InLSym0 :: (~>) (f_as8d a_as8f) (Sum f_as8d g_as8e a_as8f)) where
  sing = singFun1 @InLSym0 SInL
instance SingI n_a29bN =>
          SingI ('InR (n_a29bN :: g_as8e a_as8f)) where
  sing = SInR sing
instance SingI1 'InR where
  liftSing = SInR
instance SingI (InRSym0 :: (~>) (g_as8e a_as8f) (Sum f_as8d g_as8e a_as8f)) where
  sing = singFun1 @InRSym0 SInR

type TFHelper_6989586621679523706 :: forall f_a29Cz
                                                g_a29CB
                                                a_a29CA. Sum f_a29Cz g_a29CB a_a29CA
                                                         -> Sum f_a29Cz g_a29CB a_a29CA -> Bool
type family TFHelper_6989586621679523706 @f_a29Cz @g_a29CB @a_a29CA (a_a29GY :: Sum f_a29Cz g_a29CB a_a29CA) (a_a29GZ :: Sum f_a29Cz g_a29CB a_a29CA) :: Bool where
  TFHelper_6989586621679523706 @f_a29Cz @g_a29CB @a_a29CA ('InL a_6989586621679523664_a29H3 :: Sum f_a29Cz g_a29CB a_a29CA) ('InL b_6989586621679523666_a29H4 :: Sum f_a29Cz g_a29CB a_a29CA) = Apply (Apply (==@#@$) a_6989586621679523664_a29H3) b_6989586621679523666_a29H4
  TFHelper_6989586621679523706 @f_a29Cz @g_a29CB @a_a29CA ('InL _ :: Sum f_a29Cz g_a29CB a_a29CA) ('InR _ :: Sum f_a29Cz g_a29CB a_a29CA) = FalseSym0
  TFHelper_6989586621679523706 @f_a29Cz @g_a29CB @a_a29CA ('InR _ :: Sum f_a29Cz g_a29CB a_a29CA) ('InL _ :: Sum f_a29Cz g_a29CB a_a29CA) = FalseSym0
  TFHelper_6989586621679523706 @f_a29Cz @g_a29CB @a_a29CA ('InR a_6989586621679523668_a29H5 :: Sum f_a29Cz g_a29CB a_a29CA) ('InR b_6989586621679523670_a29H6 :: Sum f_a29Cz g_a29CB a_a29CA) = Apply (Apply (==@#@$) a_6989586621679523668_a29H5) b_6989586621679523670_a29H6
instance PEq (Sum f_a29Cz g_a29CB a_a29CA) where
  type (==) a_a29GU a_a29GV = TFHelper_6989586621679523706 a_a29GU a_a29GV
type Compare_6989586621679523763 :: forall f_a29CC
                                            g_a29CE
                                            a_a29CD. Sum f_a29CC g_a29CE a_a29CD
                                                    -> Sum f_a29CC g_a29CE a_a29CD -> Ordering
type family Compare_6989586621679523763 @f_a29CC @g_a29CE @a_a29CD (a_a29HT :: Sum f_a29CC g_a29CE a_a29CD) (a_a29HU :: Sum f_a29CC g_a29CE a_a29CD) :: Ordering where
  Compare_6989586621679523763 @f_a29CC @g_a29CE @a_a29CD ('InL a_6989586621679523680_a29HY :: Sum f_a29CC g_a29CE a_a29CD) ('InL b_6989586621679523682_a29HZ :: Sum f_a29CC g_a29CE a_a29CD) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679523680_a29HY) b_6989586621679523682_a29HZ)) NilSym0)
  Compare_6989586621679523763 @f_a29CC @g_a29CE @a_a29CD ('InR a_6989586621679523684_a29I0 :: Sum f_a29CC g_a29CE a_a29CD) ('InR b_6989586621679523686_a29I1 :: Sum f_a29CC g_a29CE a_a29CD) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679523684_a29I0) b_6989586621679523686_a29I1)) NilSym0)
  Compare_6989586621679523763 @f_a29CC @g_a29CE @a_a29CD ('InL _ :: Sum f_a29CC g_a29CE a_a29CD) ('InR _ :: Sum f_a29CC g_a29CE a_a29CD) = LTSym0
  Compare_6989586621679523763 @f_a29CC @g_a29CE @a_a29CD ('InR _ :: Sum f_a29CC g_a29CE a_a29CD) ('InL _ :: Sum f_a29CC g_a29CE a_a29CD) = GTSym0
instance POrd (Sum f_a29CC g_a29CE a_a29CD) where
  type Compare a_a29HP a_a29HQ = Compare_6989586621679523763 a_a29HP a_a29HQ
type Fmap_6989586621679523862 :: forall f_a29CF
                                        g_a29CG
                                        a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> Sum f_a29CF g_a29CG a_iYSL
                                                    -> Sum f_a29CF g_a29CG b_iYSM
type family Fmap_6989586621679523862 @f_a29CF @g_a29CG @a_iYSL @b_iYSM (a_a29Ju :: (~>) a_iYSL b_iYSM) (a_a29Jv :: Sum f_a29CF g_a29CG a_iYSL) :: Sum f_a29CF g_a29CG b_iYSM where
  Fmap_6989586621679523862 @f_a29CF @g_a29CG @a_iYSL @b_iYSM (f_a29Jz :: (~>) a_iYSL b_iYSM) ('InL x_a29JA :: Sum f_a29CF g_a29CG a_iYSL) = Apply InLSym0 (Apply (Apply FmapSym0 f_a29Jz) x_a29JA)
  Fmap_6989586621679523862 @f_a29CF @g_a29CG @a_iYSL @b_iYSM (f_a29JB :: (~>) a_iYSL b_iYSM) ('InR y_a29JC :: Sum f_a29CF g_a29CG a_iYSL) = Apply InRSym0 (Apply (Apply FmapSym0 f_a29JB) y_a29JC)
type TFHelper_6989586621679523875 :: forall f_a29CF
                                            g_a29CG
                                            a_iYSP
                                            b_iYSQ. a_iYSP
                                                    -> Sum f_a29CF g_a29CG b_iYSQ
                                                        -> Sum f_a29CF g_a29CG a_iYSP
type family TFHelper_6989586621679523875 @f_a29CF @g_a29CG @a_iYSP @b_iYSQ (a_a29JH :: a_iYSP) (a_a29JI :: Sum f_a29CF g_a29CG b_iYSQ) :: Sum f_a29CF g_a29CG a_iYSP where
  TFHelper_6989586621679523875 @f_a29CF @g_a29CG @a_iYSP @b_iYSQ (a_a29JM :: a_iYSP) ('InL x_a29JN :: Sum f_a29CF g_a29CG b_iYSQ) = Apply InLSym0 (Apply (Apply (<$@#@$) a_a29JM) x_a29JN)
  TFHelper_6989586621679523875 @f_a29CF @g_a29CG @a_iYSP @b_iYSQ (a_a29JO :: a_iYSP) ('InR y_a29JP :: Sum f_a29CF g_a29CG b_iYSQ) = Apply InRSym0 (Apply (Apply (<$@#@$) a_a29JO) y_a29JP)
instance PFunctor (Sum f_a29CF g_a29CG) where
  type Fmap a_a29Jq a_a29Jr = Fmap_6989586621679523862 a_a29Jq a_a29Jr
  type (<$) a_a29JD a_a29JE = TFHelper_6989586621679523875 a_a29JD a_a29JE
type FoldMap_6989586621679524198 :: forall f_a29CP
                                            g_a29CQ
                                            a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU
                                                    -> Sum f_a29CP g_a29CQ a_iYVT -> m_iYVU
type family FoldMap_6989586621679524198 @f_a29CP @g_a29CQ @a_iYVT @m_iYVU (a_a29OU :: (~>) a_iYVT m_iYVU) (a_a29OV :: Sum f_a29CP g_a29CQ a_iYVT) :: m_iYVU where
  FoldMap_6989586621679524198 @f_a29CP @g_a29CQ @a_iYVT @m_iYVU (f_a29OZ :: (~>) a_iYVT m_iYVU) ('InL x_a29P0 :: Sum f_a29CP g_a29CQ a_iYVT) = Apply (Apply FoldMapSym0 f_a29OZ) x_a29P0
  FoldMap_6989586621679524198 @f_a29CP @g_a29CQ @a_iYVT @m_iYVU (f_a29P1 :: (~>) a_iYVT m_iYVU) ('InR y_a29P2 :: Sum f_a29CP g_a29CQ a_iYVT) = Apply (Apply FoldMapSym0 f_a29P1) y_a29P2
instance PFoldable (Sum f_a29CP g_a29CQ) where
  type FoldMap a_a29OQ a_a29OR = FoldMap_6989586621679524198 a_a29OQ a_a29OR
type Traverse_6989586621679524323 :: forall f_a29CV
                                            g_a29CW
                                            a_i1u58
                                            f_i1u59
                                            b_i1u5a. (~>) a_i1u58 (f_i1u59 b_i1u5a)
                                                      -> Sum f_a29CV g_a29CW a_i1u58
                                                        -> f_i1u59 (Sum f_a29CV g_a29CW b_i1u5a)
type family Traverse_6989586621679524323 @f_a29CV @g_a29CW @a_i1u58 @f_i1u59 @b_i1u5a (a_a29QV :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) (a_a29QW :: Sum f_a29CV g_a29CW a_i1u58) :: f_i1u59 (Sum f_a29CV g_a29CW b_i1u5a) where
  Traverse_6989586621679524323 @f_a29CV @g_a29CW @a_i1u58 @f_i1u59 @b_i1u5a (f_a29R0 :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) ('InL x_a29R1 :: Sum f_a29CV g_a29CW a_i1u58) = Apply (Apply (<$>@#@$) InLSym0) (Apply (Apply TraverseSym0 f_a29R0) x_a29R1)
  Traverse_6989586621679524323 @f_a29CV @g_a29CW @a_i1u58 @f_i1u59 @b_i1u5a (f_a29R2 :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) ('InR y_a29R3 :: Sum f_a29CV g_a29CW a_i1u58) = Apply (Apply (<$>@#@$) InRSym0) (Apply (Apply TraverseSym0 f_a29R2) y_a29R3)
instance PTraversable (Sum f_a29CV g_a29CW) where
  type Traverse a_a29QR a_a29QS = Traverse_6989586621679524323 a_a29QR a_a29QS
instance (SEq (f_a29Cz a_a29CA), SEq (g_a29CB a_a29CA)) =>
          SEq (Sum f_a29Cz g_a29CB a_a29CA) where
  (%==)
    (SInL (sA_6989586621679523664 :: Sing a_6989586621679523664_a29H3))
    (SInL (sB_6989586621679523666 :: Sing b_6989586621679523666_a29H4))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679523664)
        sB_6989586621679523666
  (%==) (SInL _) (SInR _) = SFalse
  (%==) (SInR _) (SInL _) = SFalse
  (%==)
    (SInR (sA_6989586621679523668 :: Sing a_6989586621679523668_a29H5))
    (SInR (sB_6989586621679523670 :: Sing b_6989586621679523670_a29H6))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679523668)
        sB_6989586621679523670
instance (SOrd (f_a29CC a_a29CD), SOrd (g_a29CE a_a29CD)) =>
          SOrd (Sum f_a29CC g_a29CE a_a29CD) where
  sCompare
    (SInL (sA_6989586621679523680 :: Sing a_6989586621679523680_a29HY))
    (SInL (sB_6989586621679523682 :: Sing b_6989586621679523682_a29HZ))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679523680)
                  sB_6989586621679523682))
            SNil)
  sCompare
    (SInR (sA_6989586621679523684 :: Sing a_6989586621679523684_a29I0))
    (SInR (sB_6989586621679523686 :: Sing b_6989586621679523686_a29I1))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679523684)
                  sB_6989586621679523686))
            SNil)
  sCompare (SInL _) (SInR _) = SLT
  sCompare (SInR _) (SInL _) = SGT
instance (SFunctor f_a29CF, SFunctor g_a29CG) =>
          SFunctor (Sum f_a29CF g_a29CG) where
  sFmap (sF :: Sing f_a29Jz) (SInL (sX :: Sing x_a29JA))
    = applySing
        (singFun1 @InLSym0 SInL)
        (applySing (applySing (singFun2 @FmapSym0 sFmap) sF) sX)
  sFmap (sF :: Sing f_a29JB) (SInR (sY :: Sing y_a29JC))
    = applySing
        (singFun1 @InRSym0 SInR)
        (applySing (applySing (singFun2 @FmapSym0 sFmap) sF) sY)
  (%<$) (sA :: Sing a_a29JM) (SInL (sX :: Sing x_a29JN))
    = applySing
        (singFun1 @InLSym0 SInL)
        (applySing (applySing (singFun2 @(<$@#@$) (%<$)) sA) sX)
  (%<$) (sA :: Sing a_a29JO) (SInR (sY :: Sing y_a29JP))
    = applySing
        (singFun1 @InRSym0 SInR)
        (applySing (applySing (singFun2 @(<$@#@$) (%<$)) sA) sY)
instance (SFoldable f_a29CP, SFoldable g_a29CQ) =>
          SFoldable (Sum f_a29CP g_a29CQ) where
  sFoldMap (sF :: Sing f_a29OZ) (SInL (sX :: Sing x_a29P0))
    = applySing (applySing (singFun2 @FoldMapSym0 sFoldMap) sF) sX
  sFoldMap (sF :: Sing f_a29P1) (SInR (sY :: Sing y_a29P2))
    = applySing (applySing (singFun2 @FoldMapSym0 sFoldMap) sF) sY
instance (STraversable f_a29CV, STraversable g_a29CW) =>
          STraversable (Sum f_a29CV g_a29CW) where
  sTraverse (sF :: Sing f_a29R0) (SInL (sX :: Sing x_a29R1))
    = applySing
        (applySing (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @InLSym0 SInL))
        (applySing (applySing (singFun2 @TraverseSym0 sTraverse) sF) sX)
  sTraverse (sF :: Sing f_a29R2) (SInR (sY :: Sing y_a29R3))
    = applySing
        (applySing (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @InRSym0 SInR))
        (applySing (applySing (singFun2 @TraverseSym0 sTraverse) sF) sY)
instance (SDecide (f_a29Cz a_a29CA), SDecide (g_a29CB a_a29CA)) =>
          SDecide (Sum f_a29Cz g_a29CB a_a29CA) where
  (%~) (SInL a_a29Rd) (SInL b_a29Re)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a29Rf)
            -> Disproved (\cases Refl -> contra_a29Rf Refl))
        ((%~) a_a29Rd b_a29Re)
  (%~) (SInL _) (SInR _) = Disproved (\case)
  (%~) (SInR _) (SInL _) = Disproved (\case)
  (%~) (SInR a_a29Rg) (SInR b_a29Rh)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a29Ri)
            -> Disproved (\cases Refl -> contra_a29Ri Refl))
        ((%~) a_a29Rg b_a29Rh)
instance Eq (SSum (z_a29Rj :: Sum f_a29Cz g_a29CB a_a29CA)) where
  (==) _ _ = True
instance (SDecide (f_a29Cz a_a29CA), SDecide (g_a29CB a_a29CA)) =>
          Data.Type.Equality.TestEquality (SSum :: Sum f_a29Cz g_a29CB a_a29CA
                                                  -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide (f_a29Cz a_a29CA), SDecide (g_a29CB a_a29CA)) =>
          Data.Type.Coercion.TestCoercion (SSum :: Sum f_a29Cz g_a29CB a_a29CA
                                                  -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance Ord (SSum (z_a29Rk :: Sum f_a29CC g_a29CE a_a29CD)) where
  compare _ _ = EQ

