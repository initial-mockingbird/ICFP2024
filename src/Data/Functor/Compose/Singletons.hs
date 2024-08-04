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
-- Module      :  Data.Functor.Compose.Singletons
-- Copyright   :  (C) 2021 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Exports the promoted and singled versions of the 'Compose' data type.
--
-----------------------------------------------------------------------------

module Data.Functor.Compose.Singletons (
  -- * The 'Compose' singleton
  Sing, SCompose(..), GetCompose, sGetCompose,

  -- * Defunctionalization symbols
  ComposeSym0, ComposeSym1,
  GetComposeSym0, GetComposeSym1
  ) where

import Control.Applicative.Singletons
import Data.Eq.Singletons
import Data.Foldable.Singletons
import Data.Functor.Compose
import Data.Functor.Singletons
import Data.Ord.Singletons
import Data.Kind
import Data.Semigroup.Singletons
import Data.Singletons.Base.Instances (SList(..), (:@#@$), NilSym0)
import Data.Singletons.TH
import Data.Traversable.Singletons
import qualified Data.Type.Equality 
import qualified Data.Singletons.Decide 
import qualified Data.Type.Coercion


type ComposeSym0 :: forall {k_ar1E :: Type}
                               {k1_ar1F :: Type}
                               (f_ar1G :: k_ar1E -> Type)
                               (g_ar1H :: k1_ar1F -> k_ar1E)
                               (a_ar1I :: k1_ar1F). (~>) (f_ar1G (g_ar1H a_ar1I)) (Compose f_ar1G g_ar1H a_ar1I)
data ComposeSym0 :: (~>) (f_ar1G (g_ar1H a_ar1I)) (Compose f_ar1G g_ar1H a_ar1I)
  where
    ComposeSym0KindInference :: SameKind (Apply ComposeSym0 arg_a2gMM) (ComposeSym1 arg_a2gMM) =>
                                ComposeSym0 a6989586621679550977
type instance Apply @(f_ar1G (g_ar1H a_ar1I)) @(Compose f_ar1G g_ar1H a_ar1I) ComposeSym0 a6989586621679550977 = 'Compose a6989586621679550977
instance SuppressUnusedWarnings ComposeSym0 where
  suppressUnusedWarnings = snd ((,) ComposeSym0KindInference ())
infixr 9 `ComposeSym0`
type ComposeSym1 :: forall {k_ar1E :: Type}
                            {k1_ar1F :: Type}
                            (f_ar1G :: k_ar1E -> Type)
                            (g_ar1H :: k1_ar1F -> k_ar1E)
                            (a_ar1I :: k1_ar1F). f_ar1G (g_ar1H a_ar1I)
                                                -> Compose f_ar1G g_ar1H a_ar1I
type family ComposeSym1 @(f_ar1G :: k_ar1E
                                    -> Type) @(g_ar1H :: k1_ar1F
                                                          -> k_ar1E) @(a_ar1I :: k1_ar1F) (a6989586621679550977 :: f_ar1G (g_ar1H a_ar1I)) :: Compose f_ar1G g_ar1H a_ar1I where
  ComposeSym1 a6989586621679550977 = 'Compose a6989586621679550977
infixr 9 `ComposeSym1`
type GetComposeSym0 :: forall {k_ar1E :: Type}
                              {k1_ar1F :: Type}
                              (f_ar1G :: k_ar1E -> Type)
                              (g_ar1H :: k1_ar1F -> k_ar1E)
                              (a_ar1I :: k1_ar1F). (~>) (Compose f_ar1G g_ar1H a_ar1I) (f_ar1G (g_ar1H a_ar1I))
data GetComposeSym0 :: (~>) (Compose f_ar1G g_ar1H a_ar1I) (f_ar1G (g_ar1H a_ar1I))
  where
    GetComposeSym0KindInference :: SameKind (Apply GetComposeSym0 arg_a2gMP) (GetComposeSym1 arg_a2gMP) =>
                                    GetComposeSym0 a6989586621679550980
type instance Apply @(Compose f_ar1G g_ar1H a_ar1I) @(f_ar1G (g_ar1H a_ar1I)) GetComposeSym0 a6989586621679550980 = GetCompose a6989586621679550980
instance SuppressUnusedWarnings GetComposeSym0 where
  suppressUnusedWarnings = snd ((,) GetComposeSym0KindInference ())
type GetComposeSym1 :: forall {k_ar1E :: Type}
                              {k1_ar1F :: Type}
                              (f_ar1G :: k_ar1E -> Type)
                              (g_ar1H :: k1_ar1F -> k_ar1E)
                              (a_ar1I :: k1_ar1F). Compose f_ar1G g_ar1H a_ar1I
                                                    -> f_ar1G (g_ar1H a_ar1I)
type family GetComposeSym1 @(f_ar1G :: k_ar1E
                                        -> Type) @(g_ar1H :: k1_ar1F
                                                            -> k_ar1E) @(a_ar1I :: k1_ar1F) (a6989586621679550980 :: Compose f_ar1G g_ar1H a_ar1I) :: f_ar1G (g_ar1H a_ar1I) where
  GetComposeSym1 a6989586621679550980 = GetCompose a6989586621679550980
type GetCompose :: forall {k_ar1E :: Type}
                          {k1_ar1F :: Type}
                          (f_ar1G :: k_ar1E -> Type)
                          (g_ar1H :: k1_ar1F -> k_ar1E)
                          (a_ar1I :: k1_ar1F). Compose f_ar1G g_ar1H a_ar1I
                                                -> f_ar1G (g_ar1H a_ar1I)
type family GetCompose @(f_ar1G :: k_ar1E
                                    -> Type) @(g_ar1H :: k1_ar1F
                                                        -> k_ar1E) @(a_ar1I :: k1_ar1F) (a_a2gMO :: Compose f_ar1G g_ar1H a_ar1I) :: f_ar1G (g_ar1H a_ar1I) where
  GetCompose @f_ar1G @g_ar1H @a_ar1I ('Compose field_a2gMR :: Compose f_ar1G g_ar1H a_ar1I) = field_a2gMR
sGetCompose ::
  forall {k_ar1E :: Type}
          {k1_ar1F :: Type}
          (f_ar1G :: k_ar1E -> Type)
          (g_ar1H :: k1_ar1F -> k_ar1E)
          (a_ar1I :: k1_ar1F)
          (t_a2gMS :: Compose f_ar1G g_ar1H a_ar1I). Sing t_a2gMS
                                                    -> Sing (GetCompose t_a2gMS :: f_ar1G (g_ar1H a_ar1I))
sGetCompose (SCompose (sField :: Sing field_a2gMR)) = sField
instance SingI (GetComposeSym0 :: (~>) (Compose f_ar1G g_ar1H a_ar1I) (f_ar1G (g_ar1H a_ar1I))) where
  sing = singFun1 @GetComposeSym0 sGetCompose
type SCompose :: forall {k_ar1E :: Type}
                        {k1_ar1F :: Type}
                        (f_ar1G :: k_ar1E -> Type)
                        (g_ar1H :: k1_ar1F -> k_ar1E)
                        (a_ar1I :: k1_ar1F). Compose f_ar1G g_ar1H a_ar1I -> Type
data SCompose :: forall {k_ar1E :: Type}
                        {k1_ar1F :: Type}
                        (f_ar1G :: k_ar1E -> Type)
                        (g_ar1H :: k1_ar1F -> k_ar1E)
                        (a_ar1I :: k1_ar1F).
                  Compose f_ar1G g_ar1H a_ar1I -> Type
  where
    SCompose :: forall {k_ar1E :: Type}
                        {k1_ar1F :: Type}
                        (f_ar1G :: k_ar1E -> Type)
                        (g_ar1H :: k1_ar1F -> k_ar1E)
                        (a_ar1I :: k1_ar1F)
                        (n_a2gMU :: f_ar1G (g_ar1H a_ar1I)).
                (Sing n_a2gMU) ->
                SCompose ('Compose n_a2gMU :: Compose f_ar1G g_ar1H a_ar1I)
type instance Sing @(Compose f_ar1G g_ar1H a_ar1I) = SCompose
infixr 9 `SCompose`
instance SingI n_a2gMU =>
          SingI ('Compose (n_a2gMU :: f_ar1G (g_ar1H a_ar1I))) where
  sing = SCompose sing
instance SingI1 'Compose where
  liftSing = SCompose
instance SingI (ComposeSym0 :: (~>) (f_ar1G (g_ar1H a_ar1I)) (Compose f_ar1G g_ar1H a_ar1I)) where
  sing = singFun1 @ComposeSym0 SCompose

type TFHelper_6989586621679553113 :: forall f_a2hhZ
                                                g_a2hi0
                                                a_a2hi1. Compose f_a2hhZ g_a2hi0 a_a2hi1
                                                         -> Compose f_a2hhZ g_a2hi0 a_a2hi1 -> Bool
type family TFHelper_6989586621679553113 @f_a2hhZ @g_a2hi0 @a_a2hi1 (a_a2hlh :: Compose f_a2hhZ g_a2hi0 a_a2hi1) (a_a2hli :: Compose f_a2hhZ g_a2hi0 a_a2hi1) :: Bool where
  TFHelper_6989586621679553113 @f_a2hhZ @g_a2hi0 @a_a2hi1 ('Compose a_6989586621679553098_a2hlm :: Compose f_a2hhZ g_a2hi0 a_a2hi1) ('Compose b_6989586621679553100_a2hln :: Compose f_a2hhZ g_a2hi0 a_a2hi1) = Apply (Apply (==@#@$) a_6989586621679553098_a2hlm) b_6989586621679553100_a2hln
instance PEq (Compose f_a2hhZ g_a2hi0 a_a2hi1) where
  type (==) a_a2hld a_a2hle = TFHelper_6989586621679553113 a_a2hld a_a2hle
type Compare_6989586621679553124 :: forall f_a2hi2
                                            g_a2hi3
                                            a_a2hi4. Compose f_a2hi2 g_a2hi3 a_a2hi4
                                                    -> Compose f_a2hi2 g_a2hi3 a_a2hi4
                                                        -> Ordering
type family Compare_6989586621679553124 @f_a2hi2 @g_a2hi3 @a_a2hi4 (a_a2hls :: Compose f_a2hi2 g_a2hi3 a_a2hi4) (a_a2hlt :: Compose f_a2hi2 g_a2hi3 a_a2hi4) :: Ordering where
  Compare_6989586621679553124 @f_a2hi2 @g_a2hi3 @a_a2hi4 ('Compose a_6989586621679553107_a2hlx :: Compose f_a2hi2 g_a2hi3 a_a2hi4) ('Compose b_6989586621679553109_a2hly :: Compose f_a2hi2 g_a2hi3 a_a2hi4) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679553107_a2hlx) b_6989586621679553109_a2hly)) NilSym0)
instance POrd (Compose f_a2hi2 g_a2hi3 a_a2hi4) where
  type Compare a_a2hlo a_a2hlp = Compare_6989586621679553124 a_a2hlo a_a2hlp
type Fmap_6989586621679553135 :: forall (f_a2hi5 :: Type -> Type)
                                        g_a2hi6
                                        a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> Compose (f_a2hi5 :: Type
                                                                        -> Type) g_a2hi6 a_iYSL
                                                    -> Compose (f_a2hi5 :: Type
                                                                          -> Type) g_a2hi6 b_iYSM
type family Fmap_6989586621679553135 @(f_a2hi5 :: Type
                                                  -> Type) @g_a2hi6 @a_iYSL @b_iYSM (a_a2hlD :: (~>) a_iYSL b_iYSM) (a_a2hlE :: Compose (f_a2hi5 :: Type
                                                                                                                                                    -> Type) g_a2hi6 a_iYSL) :: Compose (f_a2hi5 :: Type
                                                                                                                                                                                                    -> Type) g_a2hi6 b_iYSM where
  Fmap_6989586621679553135 @f_a2hi5 @g_a2hi6 @a_iYSL @b_iYSM (f_a2hlI :: (~>) a_iYSL b_iYSM) ('Compose x_a2hlJ :: Compose (f_a2hi5 :: Type
                                                                                                                                      -> Type) g_a2hi6 a_iYSL) = Apply ComposeSym0 (Apply (Apply FmapSym0 (Apply FmapSym0 f_a2hlI)) x_a2hlJ)
type TFHelper_6989586621679553146 :: forall (f_a2hi5 :: Type
                                                        -> Type)
                                            g_a2hi6
                                            a_iYSP
                                            b_iYSQ. a_iYSP
                                                    -> Compose (f_a2hi5 :: Type
                                                                            -> Type) g_a2hi6 b_iYSQ
                                                        -> Compose (f_a2hi5 :: Type
                                                                              -> Type) g_a2hi6 a_iYSP
type family TFHelper_6989586621679553146 @(f_a2hi5 :: Type
                                                      -> Type) @g_a2hi6 @a_iYSP @b_iYSQ (a_a2hlO :: a_iYSP) (a_a2hlP :: Compose (f_a2hi5 :: Type
                                                                                                                                            -> Type) g_a2hi6 b_iYSQ) :: Compose (f_a2hi5 :: Type
                                                                                                                                                                                            -> Type) g_a2hi6 a_iYSP where
  TFHelper_6989586621679553146 @f_a2hi5 @g_a2hi6 @a_iYSP @b_iYSQ (a_a2hlT :: a_iYSP) ('Compose x_a2hlU :: Compose (f_a2hi5 :: Type
                                                                                                                              -> Type) g_a2hi6 b_iYSQ) = Apply ComposeSym0 (Apply (Apply FmapSym0 (Apply (<$@#@$) a_a2hlT)) x_a2hlU)
instance PFunctor (Compose (f_a2hi5 :: Type -> Type) g_a2hi6) where
  type Fmap a_a2hlz a_a2hlA = Fmap_6989586621679553135 a_a2hlz a_a2hlA
  type (<$) a_a2hlK a_a2hlL = TFHelper_6989586621679553146 a_a2hlK a_a2hlL
type FoldMap_6989586621679553157 :: forall (f_a2hib :: Type
                                                        -> Type)
                                            g_a2hic
                                            a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU
                                                    -> Compose (f_a2hib :: Type
                                                                          -> Type) g_a2hic a_iYVT
                                                      -> m_iYVU
type family FoldMap_6989586621679553157 @(f_a2hib :: Type
                                                      -> Type) @g_a2hic @a_iYVT @m_iYVU (a_a2hlZ :: (~>) a_iYVT m_iYVU) (a_a2hm0 :: Compose (f_a2hib :: Type
                                                                                                                                                        -> Type) g_a2hic a_iYVT) :: m_iYVU where
  FoldMap_6989586621679553157 @f_a2hib @g_a2hic @a_iYVT @m_iYVU (f_a2hm4 :: (~>) a_iYVT m_iYVU) ('Compose t_a2hm5 :: Compose (f_a2hib :: Type
                                                                                                                                          -> Type) g_a2hic a_iYVT) = Apply (Apply FoldMapSym0 (Apply FoldMapSym0 f_a2hm4)) t_a2hm5
instance PFoldable (Compose (f_a2hib :: Type
                                        -> Type) g_a2hic) where
  type FoldMap a_a2hlV a_a2hlW = FoldMap_6989586621679553157 a_a2hlV a_a2hlW
type Traverse_6989586621679553168 :: forall (f_a2hif :: Type
                                                        -> Type)
                                            g_a2hig
                                            a_i1u58
                                            f_i1u59
                                            b_i1u5a. (~>) a_i1u58 (f_i1u59 b_i1u5a)
                                                      -> Compose (f_a2hif :: Type
                                                                            -> Type) g_a2hig a_i1u58
                                                        -> f_i1u59 (Compose (f_a2hif :: Type
                                                                                        -> Type) g_a2hig b_i1u5a)
type family Traverse_6989586621679553168 @(f_a2hif :: Type
                                                      -> Type) @g_a2hig @a_i1u58 @f_i1u59 @b_i1u5a (a_a2hma :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) (a_a2hmb :: Compose (f_a2hif :: Type
                                                                                                                                                                                -> Type) g_a2hig a_i1u58) :: f_i1u59 (Compose (f_a2hif :: Type
                                                                                                                                                                                                                                          -> Type) g_a2hig b_i1u5a) where
  Traverse_6989586621679553168 @f_a2hif @g_a2hig @a_i1u58 @f_i1u59 @b_i1u5a (f_a2hmf :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) ('Compose t_a2hmg :: Compose (f_a2hif :: Type
                                                                                                                                                                  -> Type) g_a2hig a_i1u58) = Apply (Apply (<$>@#@$) ComposeSym0) (Apply (Apply TraverseSym0 (Apply TraverseSym0 f_a2hmf)) t_a2hmg)
instance PTraversable (Compose (f_a2hif :: Type
                                            -> Type) g_a2hig) where
  type Traverse a_a2hm6 a_a2hm7 = Traverse_6989586621679553168 a_a2hm6 a_a2hm7
type Pure_6989586621679553340 :: forall (f_a2hij :: Type -> Type)
                                        g_a2hik
                                        a_iv9m. a_iv9m
                                                -> Compose (f_a2hij :: Type
                                                                        -> Type) g_a2hik a_iv9m
type family Pure_6989586621679553340 @(f_a2hij :: Type
                                                  -> Type) @g_a2hik @a_iv9m (a_a2hoW :: a_iv9m) :: Compose (f_a2hij :: Type
                                                                                                                        -> Type) g_a2hik a_iv9m where
  Pure_6989586621679553340 @f_a2hij @g_a2hik @a_iv9m (x_a2hoZ :: a_iv9m) = Apply ComposeSym0 (Apply PureSym0 (Apply PureSym0 x_a2hoZ))
type TFHelper_6989586621679553348 :: forall (f_a2hij :: Type
                                                        -> Type)
                                            g_a2hik
                                            a_iv9o
                                            b_iv9p. Compose (f_a2hij :: Type
                                                                        -> Type) g_a2hik ((~>) a_iv9o b_iv9p)
                                                    -> Compose (f_a2hij :: Type
                                                                            -> Type) g_a2hik a_iv9o
                                                        -> Compose (f_a2hij :: Type
                                                                              -> Type) g_a2hik b_iv9p
type family TFHelper_6989586621679553348 @(f_a2hij :: Type
                                                      -> Type) @g_a2hik @a_iv9o @b_iv9p (a_a2hp4 :: Compose (f_a2hij :: Type
                                                                                                                        -> Type) g_a2hik ((~>) a_iv9o b_iv9p)) (a_a2hp5 :: Compose (f_a2hij :: Type
                                                                                                                                                                                                -> Type) g_a2hik a_iv9o) :: Compose (f_a2hij :: Type
                                                                                                                                                                                                                                                -> Type) g_a2hik b_iv9p where
  TFHelper_6989586621679553348 @f_a2hij @g_a2hik @a_iv9o @b_iv9p ('Compose f_a2hp9 :: Compose (f_a2hij :: Type
                                                                                                          -> Type) g_a2hik ((~>) a_iv9o b_iv9p)) ('Compose x_a2hpa :: Compose (f_a2hij :: Type
                                                                                                                                                                                          -> Type) g_a2hik a_iv9o) = Apply ComposeSym0 (Apply (Apply (Apply LiftA2Sym0 (<*>@#@$)) f_a2hp9) x_a2hpa)
type LiftA2_6989586621679553360 :: forall (f_a2hij :: Type -> Type)
                                          g_a2hik
                                          a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> Compose (f_a2hij :: Type
                                                                          -> Type) g_a2hik a_iv9s
                                                      -> Compose (f_a2hij :: Type
                                                                            -> Type) g_a2hik b_iv9t
                                                        -> Compose (f_a2hij :: Type
                                                                                -> Type) g_a2hik c_iv9u
type family LiftA2_6989586621679553360 @(f_a2hij :: Type
                                                    -> Type) @g_a2hik @a_iv9s @b_iv9t @c_iv9u (a_a2hpg :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a2hph :: Compose (f_a2hij :: Type
                                                                                                                                                                            -> Type) g_a2hik a_iv9s) (a_a2hpi :: Compose (f_a2hij :: Type
                                                                                                                                                                                                                                      -> Type) g_a2hik b_iv9t) :: Compose (f_a2hij :: Type
                                                                                                                                                                                                                                                                                      -> Type) g_a2hik c_iv9u where
  LiftA2_6989586621679553360 @f_a2hij @g_a2hik @a_iv9s @b_iv9t @c_iv9u (f_a2hpn :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) ('Compose x_a2hpo :: Compose (f_a2hij :: Type
                                                                                                                                                              -> Type) g_a2hik a_iv9s) ('Compose y_a2hpp :: Compose (f_a2hij :: Type
                                                                                                                                                                                                                                -> Type) g_a2hik b_iv9t) = Apply ComposeSym0 (Apply (Apply (Apply LiftA2Sym0 (Apply LiftA2Sym0 f_a2hpn)) x_a2hpo) y_a2hpp)
instance PApplicative (Compose (f_a2hij :: Type
                                            -> Type) g_a2hik) where
  type Pure a_a2hoT = Pure_6989586621679553340 a_a2hoT
  type (<*>) a_a2hp0 a_a2hp1 = TFHelper_6989586621679553348 a_a2hp0 a_a2hp1
  type LiftA2 a_a2hpb a_a2hpc a_a2hpd = LiftA2_6989586621679553360 a_a2hpb a_a2hpc a_a2hpd
type Empty_6989586621679553398 :: forall (f_a2hir :: Type -> Type)
                                          g_a2his
                                          a_iv8T. Compose (f_a2hir :: Type
                                                                      -> Type) g_a2his a_iv8T
type family Empty_6989586621679553398 @(f_a2hir :: Type
                                                    -> Type) @g_a2his @a_iv8T :: Compose (f_a2hir :: Type
                                                                                                    -> Type) g_a2his a_iv8T where
  Empty_6989586621679553398 @f_a2hir @g_a2his @a_iv8T = Apply ComposeSym0 EmptySym0
type TFHelper_6989586621679553403 :: forall (f_a2hir :: Type
                                                        -> Type)
                                            g_a2his
                                            a_iv8U. Compose (f_a2hir :: Type
                                                                        -> Type) g_a2his a_iv8U
                                                    -> Compose (f_a2hir :: Type
                                                                            -> Type) g_a2his a_iv8U
                                                        -> Compose (f_a2hir :: Type
                                                                              -> Type) g_a2his a_iv8U
type family TFHelper_6989586621679553403 @(f_a2hir :: Type
                                                      -> Type) @g_a2his @a_iv8U (a_a2hpX :: Compose (f_a2hir :: Type
                                                                                                                -> Type) g_a2his a_iv8U) (a_a2hpY :: Compose (f_a2hir :: Type
                                                                                                                                                                          -> Type) g_a2his a_iv8U) :: Compose (f_a2hir :: Type
                                                                                                                                                                                                                          -> Type) g_a2his a_iv8U where
  TFHelper_6989586621679553403 @f_a2hir @g_a2his @a_iv8U ('Compose x_a2hq2 :: Compose (f_a2hir :: Type
                                                                                                  -> Type) g_a2his a_iv8U) ('Compose y_a2hq3 :: Compose (f_a2hir :: Type
                                                                                                                                                                    -> Type) g_a2his a_iv8U) = Apply ComposeSym0 (Apply (Apply (<|>@#@$) x_a2hq2) y_a2hq3)
instance PAlternative (Compose (f_a2hir :: Type
                                            -> Type) g_a2his) where
  type Empty = Empty_6989586621679553398
  type (<|>) a_a2hpT a_a2hpU = TFHelper_6989586621679553403 a_a2hpT a_a2hpU
instance SEq (f_a2hhZ (g_a2hi0 a_a2hi1)) =>
          SEq (Compose f_a2hhZ g_a2hi0 a_a2hi1) where
  (%==)
    (SCompose (sA_6989586621679553098 :: Sing a_6989586621679553098_a2hlm))
    (SCompose (sB_6989586621679553100 :: Sing b_6989586621679553100_a2hln))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679553098)
        sB_6989586621679553100
instance SOrd (f_a2hi2 (g_a2hi3 a_a2hi4)) =>
          SOrd (Compose f_a2hi2 g_a2hi3 a_a2hi4) where
  sCompare
    (SCompose (sA_6989586621679553107 :: Sing a_6989586621679553107_a2hlx))
    (SCompose (sB_6989586621679553109 :: Sing b_6989586621679553109_a2hly))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679553107)
                  sB_6989586621679553109))
            SNil)
instance (SFunctor f_a2hi5, SFunctor g_a2hi6) =>
          SFunctor (Compose (f_a2hi5 :: Type -> Type) g_a2hi6) where
  sFmap (sF :: Sing f_a2hlI) (SCompose (sX :: Sing x_a2hlJ))
    = applySing
        (singFun1 @ComposeSym0 SCompose)
        (applySing
            (applySing
              (singFun2 @FmapSym0 sFmap)
              (applySing (singFun2 @FmapSym0 sFmap) sF))
            sX)
  (%<$) (sA :: Sing a_a2hlT) (SCompose (sX :: Sing x_a2hlU))
    = applySing
        (singFun1 @ComposeSym0 SCompose)
        (applySing
            (applySing
              (singFun2 @FmapSym0 sFmap)
              (applySing (singFun2 @(<$@#@$) (%<$)) sA))
            sX)
instance (SFoldable f_a2hib, SFoldable g_a2hic) =>
          SFoldable (Compose (f_a2hib :: Type -> Type) g_a2hic) where
  sFoldMap (sF :: Sing f_a2hm4) (SCompose (sT :: Sing t_a2hm5))
    = applySing
        (applySing
            (singFun2 @FoldMapSym0 sFoldMap)
            (applySing (singFun2 @FoldMapSym0 sFoldMap) sF))
        sT
instance (STraversable f_a2hif, STraversable g_a2hig) =>
          STraversable (Compose (f_a2hif :: Type -> Type) g_a2hig) where
  sTraverse (sF :: Sing f_a2hmf) (SCompose (sT :: Sing t_a2hmg))
    = applySing
        (applySing
            (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @ComposeSym0 SCompose))
        (applySing
            (applySing
              (singFun2 @TraverseSym0 sTraverse)
              (applySing (singFun2 @TraverseSym0 sTraverse) sF))
            sT)
instance (SApplicative f_a2hij, SApplicative g_a2hik) =>
          SApplicative (Compose (f_a2hij :: Type -> Type) g_a2hik) where
  sPure (sX :: Sing x_a2hoZ)
    = applySing
        (singFun1 @ComposeSym0 SCompose)
        (applySing
            (singFun1 @PureSym0 sPure)
            (applySing (singFun1 @PureSym0 sPure) sX))
  (%<*>)
    (SCompose (sF :: Sing f_a2hp9))
    (SCompose (sX :: Sing x_a2hpa))
    = applySing
        (singFun1 @ComposeSym0 SCompose)
        (applySing
            (applySing
              (applySing
                  (singFun3 @LiftA2Sym0 sLiftA2) (singFun2 @(<*>@#@$) (%<*>)))
              sF)
            sX)
  sLiftA2
    (sF :: Sing f_a2hpn)
    (SCompose (sX :: Sing x_a2hpo))
    (SCompose (sY :: Sing y_a2hpp))
    = applySing
        (singFun1 @ComposeSym0 SCompose)
        (applySing
            (applySing
              (applySing
                  (singFun3 @LiftA2Sym0 sLiftA2)
                  (applySing (singFun3 @LiftA2Sym0 sLiftA2) sF))
              sX)
            sY)
instance (SAlternative f_a2hir, SApplicative g_a2his) =>
          SAlternative (Compose (f_a2hir :: Type -> Type) g_a2his) where
  sEmpty = applySing (singFun1 @ComposeSym0 SCompose) sEmpty
  (%<|>)
    (SCompose (sX :: Sing x_a2hq2))
    (SCompose (sY :: Sing y_a2hq3))
    = applySing
        (singFun1 @ComposeSym0 SCompose)
        (applySing (applySing (singFun2 @(<|>@#@$) (%<|>)) sX) sY)
instance SDecide (f_a2hhZ (g_a2hi0 a_a2hi1)) =>
          SDecide (Compose f_a2hhZ g_a2hi0 a_a2hi1) where
  (%~) (SCompose a_a2hq6) (SCompose b_a2hq7)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_a2hq8)
            -> Disproved (\cases Refl -> contra_a2hq8 Refl))
        ((%~) a_a2hq6 b_a2hq7)
instance Eq (SCompose (z_a2hq9 :: Compose f_a2hhZ g_a2hi0 a_a2hi1)) where
  (==) _ _ = True
instance SDecide (f_a2hhZ (g_a2hi0 a_a2hi1)) =>
          Data.Type.Equality.TestEquality (SCompose :: Compose f_a2hhZ g_a2hi0 a_a2hi1
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide (f_a2hhZ (g_a2hi0 a_a2hi1)) =>
          Data.Type.Coercion.TestCoercion (SCompose :: Compose f_a2hhZ g_a2hi0 a_a2hi1
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance Ord (SCompose (z_a2hqa :: Compose f_a2hi2 g_a2hi3 a_a2hi4)) where
  compare _ _ = EQ
