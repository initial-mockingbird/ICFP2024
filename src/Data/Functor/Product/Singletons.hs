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
-- Module      :  Data.Functor.Product.Singletons
-- Copyright   :  (C) 2021 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Exports the promoted and singled versions of the 'Product' data type.
--
-----------------------------------------------------------------------------

module Data.Functor.Product.Singletons (
  -- * The 'Product' singleton
  Sing, SProduct(..),

  -- * Defunctionalization symbols
  PairSym0, PairSym1, PairSym2
  ) where


import Control.Applicative.Singletons

import Control.Monad.Singletons

import Control.Monad.Zip.Singletons
import Data.Bool.Singletons
import Data.Eq.Singletons
import Data.Foldable.Singletons hiding (Product)
import Data.Function.Singletons
import Data.Functor.Product
import Data.Kind
import Data.Monoid.Singletons hiding (SProduct(..))
import Data.Semigroup.Singletons hiding (SProduct(..))
import Data.Singletons.Base.Instances (SList(..), (:@#@$), NilSym0)
import Data.Ord.Singletons
import Data.Singletons.TH

import Data.Traversable.Singletons
import qualified Data.Type.Equality
import qualified Data.Singletons.Decide
import qualified Data.Type.Coercion
type PairSym0 :: forall {k_ar25 :: Type}
                            (f_ar26 :: k_ar25 -> Type)
                            (g_ar27 :: k_ar25 -> Type)
                            (a_ar28 :: k_ar25). (~>) (f_ar26 a_ar28) ((~>) (g_ar27 a_ar28) (Product f_ar26 g_ar27 a_ar28))
data PairSym0 :: (~>) (f_ar26 a_ar28) ((~>) (g_ar27 a_ar28) (Product f_ar26 g_ar27 a_ar28))
  where
    PairSym0KindInference :: SameKind (Apply PairSym0 arg_a2vzu) (PairSym1 arg_a2vzu) =>
                              PairSym0 a6989586621679607813
type instance Apply @(f_ar26 a_ar28) @((~>) (g_ar27 a_ar28) (Product f_ar26 g_ar27 a_ar28)) PairSym0 a6989586621679607813 = PairSym1 a6989586621679607813
instance SuppressUnusedWarnings PairSym0 where
  suppressUnusedWarnings = snd ((,) PairSym0KindInference ())
type PairSym1 :: forall {k_ar25 :: Type}
                        (f_ar26 :: k_ar25 -> Type)
                        (g_ar27 :: k_ar25 -> Type)
                        (a_ar28 :: k_ar25). f_ar26 a_ar28
                                            -> (~>) (g_ar27 a_ar28) (Product f_ar26 g_ar27 a_ar28)
data PairSym1 (a6989586621679607813 :: f_ar26 a_ar28) :: (~>) (g_ar27 a_ar28) (Product f_ar26 g_ar27 a_ar28)
  where
    PairSym1KindInference :: SameKind (Apply (PairSym1 a6989586621679607813) arg_a2vzu) (PairSym2 a6989586621679607813 arg_a2vzu) =>
                              PairSym1 a6989586621679607813 a6989586621679607814
type instance Apply @(g_ar27 a_ar28) @(Product f_ar26 g_ar27 a_ar28) (PairSym1 a6989586621679607813) a6989586621679607814 = 'Pair a6989586621679607813 a6989586621679607814
instance SuppressUnusedWarnings (PairSym1 a6989586621679607813) where
  suppressUnusedWarnings = snd ((,) PairSym1KindInference ())
type PairSym2 :: forall {k_ar25 :: Type}
                        (f_ar26 :: k_ar25 -> Type)
                        (g_ar27 :: k_ar25 -> Type)
                        (a_ar28 :: k_ar25). f_ar26 a_ar28
                                            -> g_ar27 a_ar28 -> Product f_ar26 g_ar27 a_ar28
type family PairSym2 @(f_ar26 :: k_ar25 -> Type) @(g_ar27 :: k_ar25
                                                              -> Type) @(a_ar28 :: k_ar25) (a6989586621679607813 :: f_ar26 a_ar28) (a6989586621679607814 :: g_ar27 a_ar28) :: Product f_ar26 g_ar27 a_ar28 where
  PairSym2 a6989586621679607813 a6989586621679607814 = 'Pair a6989586621679607813 a6989586621679607814
type SProduct :: forall {k_ar25 :: Type}
                        (f_ar26 :: k_ar25 -> Type)
                        (g_ar27 :: k_ar25 -> Type)
                        (a_ar28 :: k_ar25). Product f_ar26 g_ar27 a_ar28 -> Type
data SProduct :: forall {k_ar25 :: Type}
                        (f_ar26 :: k_ar25 -> Type)
                        (g_ar27 :: k_ar25 -> Type)
                        (a_ar28 :: k_ar25).
                  Product f_ar26 g_ar27 a_ar28 -> Type
  where
    SPair :: forall {k_ar25 :: Type}
                    (f_ar26 :: k_ar25 -> Type)
                    (g_ar27 :: k_ar25 -> Type)
                    (a_ar28 :: k_ar25)
                    (n_a2vzx :: f_ar26 a_ar28)
                    (n_a2vzy :: g_ar27 a_ar28).
              (Sing n_a2vzx) ->
              (Sing n_a2vzy) ->
              SProduct ('Pair n_a2vzx n_a2vzy :: Product f_ar26 g_ar27 a_ar28)
type instance Sing @(Product f_ar26 g_ar27 a_ar28) = SProduct
instance (SingI n_a2vzx, SingI n_a2vzy) =>
          SingI ('Pair (n_a2vzx :: f_ar26 a_ar28) (n_a2vzy :: g_ar27 a_ar28)) where
  sing = SPair sing sing
instance SingI n_a2vzx =>
          SingI1 ('Pair (n_a2vzx :: f_ar26 a_ar28)) where
  liftSing = SPair sing
instance SingI2 'Pair where
  liftSing2 = SPair
instance SingI (PairSym0 :: (~>) (f_ar26 a_ar28) ((~>) (g_ar27 a_ar28) (Product f_ar26 g_ar27 a_ar28))) where
  sing = singFun2 @PairSym0 SPair
instance SingI d_a2vzz =>
          SingI (PairSym1 (d_a2vzz :: f_ar26 a_ar28) :: (~>) (g_ar27 a_ar28) (Product f_ar26 g_ar27 a_ar28)) where
  sing
    = singFun1
        @(PairSym1 (d_a2vzz :: f_ar26 a_ar28)) (SPair (sing @d_a2vzz))
instance SingI1 (PairSym1 :: f_ar26 a_ar28
                              -> (~>) (g_ar27 a_ar28) (Product f_ar26 g_ar27 a_ar28)) where
  liftSing (s_a2vzB :: Sing (d_a2vzz :: f_ar26 a_ar28))
    = singFun1 @(PairSym1 (d_a2vzz :: f_ar26 a_ar28)) (SPair s_a2vzB)

type TFHelper_6989586621679610634 :: forall f_a2weQ
                                                g_a2weS
                                                a_a2weR. Product f_a2weQ g_a2weS a_a2weR
                                                         -> Product f_a2weQ g_a2weS a_a2weR -> Bool
type family TFHelper_6989586621679610634 @f_a2weQ @g_a2weS @a_a2weR (a_a2wj2 :: Product f_a2weQ g_a2weS a_a2weR) (a_a2wj3 :: Product f_a2weQ g_a2weS a_a2weR) :: Bool where
  TFHelper_6989586621679610634 @f_a2weQ @g_a2weS @a_a2weR ('Pair a_6989586621679610612_a2wj7 a_6989586621679610614_a2wj8 :: Product f_a2weQ g_a2weS a_a2weR) ('Pair b_6989586621679610616_a2wj9 b_6989586621679610618_a2wja :: Product f_a2weQ g_a2weS a_a2weR) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679610612_a2wj7) b_6989586621679610616_a2wj9)) (Apply (Apply (==@#@$) a_6989586621679610614_a2wj8) b_6989586621679610618_a2wja)
instance PEq (Product f_a2weQ g_a2weS a_a2weR) where
  type (==) a_a2wiY a_a2wiZ = TFHelper_6989586621679610634 a_a2wiY a_a2wiZ
type Compare_6989586621679610647 :: forall f_a2weT
                                            g_a2weV
                                            a_a2weU. Product f_a2weT g_a2weV a_a2weU
                                                    -> Product f_a2weT g_a2weV a_a2weU
                                                        -> Ordering
type family Compare_6989586621679610647 @f_a2weT @g_a2weV @a_a2weU (a_a2wjf :: Product f_a2weT g_a2weV a_a2weU) (a_a2wjg :: Product f_a2weT g_a2weV a_a2weU) :: Ordering where
  Compare_6989586621679610647 @f_a2weT @g_a2weV @a_a2weU ('Pair a_6989586621679610624_a2wjk a_6989586621679610626_a2wjl :: Product f_a2weT g_a2weV a_a2weU) ('Pair b_6989586621679610628_a2wjm b_6989586621679610630_a2wjn :: Product f_a2weT g_a2weV a_a2weU) = Apply (Apply (Apply FoldlSym0 (<>@#@$)) EQSym0) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679610624_a2wjk) b_6989586621679610628_a2wjm)) (Apply (Apply (:@#@$) (Apply (Apply CompareSym0 a_6989586621679610626_a2wjl) b_6989586621679610630_a2wjn)) NilSym0))
instance POrd (Product f_a2weT g_a2weV a_a2weU) where
  type Compare a_a2wjb a_a2wjc = Compare_6989586621679610647 a_a2wjb a_a2wjc
type Fmap_6989586621679610660 :: forall f_a2weW
                                        g_a2weX
                                        a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> Product f_a2weW g_a2weX a_iYSL
                                                    -> Product f_a2weW g_a2weX b_iYSM
type family Fmap_6989586621679610660 @f_a2weW @g_a2weX @a_iYSL @b_iYSM (a_a2wjs :: (~>) a_iYSL b_iYSM) (a_a2wjt :: Product f_a2weW g_a2weX a_iYSL) :: Product f_a2weW g_a2weX b_iYSM where
  Fmap_6989586621679610660 @f_a2weW @g_a2weX @a_iYSL @b_iYSM (f_a2wjx :: (~>) a_iYSL b_iYSM) ('Pair x_a2wjy y_a2wjz :: Product f_a2weW g_a2weX a_iYSL) = Apply (Apply PairSym0 (Apply (Apply FmapSym0 f_a2wjx) x_a2wjy)) (Apply (Apply FmapSym0 f_a2wjx) y_a2wjz)
type TFHelper_6989586621679610672 :: forall f_a2weW
                                            g_a2weX
                                            a_iYSP
                                            b_iYSQ. a_iYSP
                                                    -> Product f_a2weW g_a2weX b_iYSQ
                                                        -> Product f_a2weW g_a2weX a_iYSP
type family TFHelper_6989586621679610672 @f_a2weW @g_a2weX @a_iYSP @b_iYSQ (a_a2wjE :: a_iYSP) (a_a2wjF :: Product f_a2weW g_a2weX b_iYSQ) :: Product f_a2weW g_a2weX a_iYSP where
  TFHelper_6989586621679610672 @f_a2weW @g_a2weX @a_iYSP @b_iYSQ (a_a2wjJ :: a_iYSP) ('Pair x_a2wjK y_a2wjL :: Product f_a2weW g_a2weX b_iYSQ) = Apply (Apply PairSym0 (Apply (Apply (<$@#@$) a_a2wjJ) x_a2wjK)) (Apply (Apply (<$@#@$) a_a2wjJ) y_a2wjL)
instance PFunctor (Product f_a2weW g_a2weX) where
  type Fmap a_a2wjo a_a2wjp = Fmap_6989586621679610660 a_a2wjo a_a2wjp
  type (<$) a_a2wjA a_a2wjB = TFHelper_6989586621679610672 a_a2wjA a_a2wjB
type FoldMap_6989586621679610684 :: forall f_a2wf4
                                            g_a2wf5
                                            a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU
                                                    -> Product f_a2wf4 g_a2wf5 a_iYVT -> m_iYVU
type family FoldMap_6989586621679610684 @f_a2wf4 @g_a2wf5 @a_iYVT @m_iYVU (a_a2wjQ :: (~>) a_iYVT m_iYVU) (a_a2wjR :: Product f_a2wf4 g_a2wf5 a_iYVT) :: m_iYVU where
  FoldMap_6989586621679610684 @f_a2wf4 @g_a2wf5 @a_iYVT @m_iYVU (f_a2wjV :: (~>) a_iYVT m_iYVU) ('Pair x_a2wjW y_a2wjX :: Product f_a2wf4 g_a2wf5 a_iYVT) = Apply (Apply MappendSym0 (Apply (Apply FoldMapSym0 f_a2wjV) x_a2wjW)) (Apply (Apply FoldMapSym0 f_a2wjV) y_a2wjX)
instance PFoldable (Product f_a2wf4 g_a2wf5) where
  type FoldMap a_a2wjM a_a2wjN = FoldMap_6989586621679610684 a_a2wjM a_a2wjN
type Traverse_6989586621679610696 :: forall f_a2wf9
                                            g_a2wfa
                                            a_i1u58
                                            f_i1u59
                                            b_i1u5a. (~>) a_i1u58 (f_i1u59 b_i1u5a)
                                                      -> Product f_a2wf9 g_a2wfa a_i1u58
                                                        -> f_i1u59 (Product f_a2wf9 g_a2wfa b_i1u5a)
type family Traverse_6989586621679610696 @f_a2wf9 @g_a2wfa @a_i1u58 @f_i1u59 @b_i1u5a (a_a2wk2 :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) (a_a2wk3 :: Product f_a2wf9 g_a2wfa a_i1u58) :: f_i1u59 (Product f_a2wf9 g_a2wfa b_i1u5a) where
  Traverse_6989586621679610696 @f_a2wf9 @g_a2wfa @a_i1u58 @f_i1u59 @b_i1u5a (f_a2wk7 :: (~>) a_i1u58 (f_i1u59 b_i1u5a)) ('Pair x_a2wk8 y_a2wk9 :: Product f_a2wf9 g_a2wfa a_i1u58) = Apply (Apply (Apply LiftA2Sym0 PairSym0) (Apply (Apply TraverseSym0 f_a2wk7) x_a2wk8)) (Apply (Apply TraverseSym0 f_a2wk7) y_a2wk9)
instance PTraversable (Product f_a2wf9 g_a2wfa) where
  type Traverse a_a2wjY a_a2wjZ = Traverse_6989586621679610696 a_a2wjY a_a2wjZ
type Pure_6989586621679610707 :: forall f_a2wfe
                                        g_a2wff
                                        a_iv9m. a_iv9m -> Product f_a2wfe g_a2wff a_iv9m
type family Pure_6989586621679610707 @f_a2wfe @g_a2wff @a_iv9m (a_a2wkd :: a_iv9m) :: Product f_a2wfe g_a2wff a_iv9m where
  Pure_6989586621679610707 @f_a2wfe @g_a2wff @a_iv9m (x_a2wkg :: a_iv9m) = Apply (Apply PairSym0 (Apply PureSym0 x_a2wkg)) (Apply PureSym0 x_a2wkg)
type TFHelper_6989586621679610715 :: forall f_a2wfe
                                            g_a2wff
                                            a_iv9o
                                            b_iv9p. Product f_a2wfe g_a2wff ((~>) a_iv9o b_iv9p)
                                                    -> Product f_a2wfe g_a2wff a_iv9o
                                                        -> Product f_a2wfe g_a2wff b_iv9p
type family TFHelper_6989586621679610715 @f_a2wfe @g_a2wff @a_iv9o @b_iv9p (a_a2wkl :: Product f_a2wfe g_a2wff ((~>) a_iv9o b_iv9p)) (a_a2wkm :: Product f_a2wfe g_a2wff a_iv9o) :: Product f_a2wfe g_a2wff b_iv9p where
  TFHelper_6989586621679610715 @f_a2wfe @g_a2wff @a_iv9o @b_iv9p ('Pair f_a2wkq g_a2wkr :: Product f_a2wfe g_a2wff ((~>) a_iv9o b_iv9p)) ('Pair x_a2wks y_a2wkt :: Product f_a2wfe g_a2wff a_iv9o) = Apply (Apply PairSym0 (Apply (Apply (<*>@#@$) f_a2wkq) x_a2wks)) (Apply (Apply (<*>@#@$) g_a2wkr) y_a2wkt)
type LiftA2_6989586621679610729 :: forall f_a2wfe
                                          g_a2wff
                                          a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> Product f_a2wfe g_a2wff a_iv9s
                                                      -> Product f_a2wfe g_a2wff b_iv9t
                                                        -> Product f_a2wfe g_a2wff c_iv9u
type family LiftA2_6989586621679610729 @f_a2wfe @g_a2wff @a_iv9s @b_iv9t @c_iv9u (a_a2wkz :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a2wkA :: Product f_a2wfe g_a2wff a_iv9s) (a_a2wkB :: Product f_a2wfe g_a2wff b_iv9t) :: Product f_a2wfe g_a2wff c_iv9u where
  LiftA2_6989586621679610729 @f_a2wfe @g_a2wff @a_iv9s @b_iv9t @c_iv9u (f_a2wkG :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) ('Pair a_a2wkH b_a2wkI :: Product f_a2wfe g_a2wff a_iv9s) ('Pair x_a2wkJ y_a2wkK :: Product f_a2wfe g_a2wff b_iv9t) = Apply (Apply PairSym0 (Apply (Apply (Apply LiftA2Sym0 f_a2wkG) a_a2wkH) x_a2wkJ)) (Apply (Apply (Apply LiftA2Sym0 f_a2wkG) b_a2wkI) y_a2wkK)
instance PApplicative (Product f_a2wfe g_a2wff) where
  type Pure a_a2wka = Pure_6989586621679610707 a_a2wka
  type (<*>) a_a2wkh a_a2wki = TFHelper_6989586621679610715 a_a2wkh a_a2wki
  type LiftA2 a_a2wku a_a2wkv a_a2wkw = LiftA2_6989586621679610729 a_a2wku a_a2wkv a_a2wkw
data Let6989586621679610829SndPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 (f6989586621679610828 :: (~>) a7566047373982553006 (Product f6989586621679610412 g6989586621679610413 b7566047373982553007)) a6989586621679610830
  where
    Let6989586621679610829SndPSym0KindInference :: SameKind (Apply (Let6989586621679610829SndPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828) arg_a2wmb) (Let6989586621679610829SndPSym1 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 arg_a2wmb) =>
                                                    Let6989586621679610829SndPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 a6989586621679610830
type instance Apply @_ @_ (Let6989586621679610829SndPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828) a6989586621679610830 = Let6989586621679610829SndP f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 a6989586621679610830
instance SuppressUnusedWarnings (Let6989586621679610829SndPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679610829SndPSym0KindInference ())
type family Let6989586621679610829SndPSym1 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 (f6989586621679610828 :: (~>) a7566047373982553006 (Product f6989586621679610412 g6989586621679610413 b7566047373982553007)) a6989586621679610830 where
  Let6989586621679610829SndPSym1 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 a6989586621679610830 = Let6989586621679610829SndP f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 a6989586621679610830
data Let6989586621679610829FstPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 (f6989586621679610828 :: (~>) a7566047373982553006 (Product f6989586621679610412 g6989586621679610413 b7566047373982553007)) a6989586621679610833
  where
    Let6989586621679610829FstPSym0KindInference :: SameKind (Apply (Let6989586621679610829FstPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828) arg_a2wme) (Let6989586621679610829FstPSym1 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 arg_a2wme) =>
                                                    Let6989586621679610829FstPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 a6989586621679610833
type instance Apply @_ @_ (Let6989586621679610829FstPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828) a6989586621679610833 = Let6989586621679610829FstP f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 a6989586621679610833
instance SuppressUnusedWarnings (Let6989586621679610829FstPSym0 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679610829FstPSym0KindInference ())
type family Let6989586621679610829FstPSym1 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 (f6989586621679610828 :: (~>) a7566047373982553006 (Product f6989586621679610412 g6989586621679610413 b7566047373982553007)) a6989586621679610833 where
  Let6989586621679610829FstPSym1 f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 a6989586621679610833 = Let6989586621679610829FstP f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 f6989586621679610828 a6989586621679610833
type family Let6989586621679610829SndP f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 (f6989586621679610828 :: (~>) a7566047373982553006 (Product f6989586621679610412 g6989586621679610413 b7566047373982553007)) a_a2wma where
  Let6989586621679610829SndP f_a2wfq g_a2wfr m_a2wm6 n_a2wm7 f_a2wm8 ('Pair _ b_a2wmc) = b_a2wmc
type family Let6989586621679610829FstP f6989586621679610412 g6989586621679610413 m6989586621679610826 n6989586621679610827 (f6989586621679610828 :: (~>) a7566047373982553006 (Product f6989586621679610412 g6989586621679610413 b7566047373982553007)) a_a2wmd where
  Let6989586621679610829FstP f_a2wfq g_a2wfr m_a2wm6 n_a2wm7 f_a2wm8 ('Pair a_a2wmf _) = a_a2wmf
type TFHelper_6989586621679610819 :: forall f_a2wfq
                                            g_a2wfr
                                            a_iv94
                                            b_iv95. Product f_a2wfq g_a2wfr a_iv94
                                                    -> (~>) a_iv94 (Product f_a2wfq g_a2wfr b_iv95)
                                                        -> Product f_a2wfq g_a2wfr b_iv95
type family TFHelper_6989586621679610819 @f_a2wfq @g_a2wfr @a_iv94 @b_iv95 (a_a2wm1 :: Product f_a2wfq g_a2wfr a_iv94) (a_a2wm2 :: (~>) a_iv94 (Product f_a2wfq g_a2wfr b_iv95)) :: Product f_a2wfq g_a2wfr b_iv95 where
  TFHelper_6989586621679610819 @f_a2wfq @g_a2wfr @a_iv94 @b_iv95 ('Pair m_a2wm6 n_a2wm7 :: Product f_a2wfq g_a2wfr a_iv94) (f_a2wm8 :: (~>) a_iv94 (Product f_a2wfq g_a2wfr b_iv95)) = Apply (Apply PairSym0 (Apply (Apply (>>=@#@$) m_a2wm6) (Apply (Apply (.@#@$) (Let6989586621679610829FstPSym0 f_a2wfq g_a2wfr m_a2wm6 n_a2wm7 f_a2wm8)) f_a2wm8))) (Apply (Apply (>>=@#@$) n_a2wm7) (Apply (Apply (.@#@$) (Let6989586621679610829SndPSym0 f_a2wfq g_a2wfr m_a2wm6 n_a2wm7 f_a2wm8)) f_a2wm8))
instance PMonad (Product f_a2wfq g_a2wfr) where
  type (>>=) a_a2wlX a_a2wlY = TFHelper_6989586621679610819 a_a2wlX a_a2wlY
type MzipWith_6989586621679610839 :: forall f_a2wfz
                                            g_a2wfA
                                            a_i1QVU
                                            b_i1QVV
                                            c_i1QVW. (~>) a_i1QVU ((~>) b_i1QVV c_i1QVW)
                                                      -> Product f_a2wfz g_a2wfA a_i1QVU
                                                        -> Product f_a2wfz g_a2wfA b_i1QVV
                                                            -> Product f_a2wfz g_a2wfA c_i1QVW
type family MzipWith_6989586621679610839 @f_a2wfz @g_a2wfA @a_i1QVU @b_i1QVV @c_i1QVW (a_a2wml :: (~>) a_i1QVU ((~>) b_i1QVV c_i1QVW)) (a_a2wmm :: Product f_a2wfz g_a2wfA a_i1QVU) (a_a2wmn :: Product f_a2wfz g_a2wfA b_i1QVV) :: Product f_a2wfz g_a2wfA c_i1QVW where
  MzipWith_6989586621679610839 @f_a2wfz @g_a2wfA @a_i1QVU @b_i1QVV @c_i1QVW (f_a2wms :: (~>) a_i1QVU ((~>) b_i1QVV c_i1QVW)) ('Pair x1_a2wmt y1_a2wmu :: Product f_a2wfz g_a2wfA a_i1QVU) ('Pair x2_a2wmv y2_a2wmw :: Product f_a2wfz g_a2wfA b_i1QVV) = Apply (Apply PairSym0 (Apply (Apply (Apply MzipWithSym0 f_a2wms) x1_a2wmt) x2_a2wmv)) (Apply (Apply (Apply MzipWithSym0 f_a2wms) y1_a2wmu) y2_a2wmw)
instance PMonadZip (Product f_a2wfz g_a2wfA) where
  type MzipWith a_a2wmg a_a2wmh a_a2wmi = MzipWith_6989586621679610839 a_a2wmg a_a2wmh a_a2wmi
type Empty_6989586621679610853 :: forall (f_a2wfG :: Type -> Type)
                                          g_a2wfH
                                          a_iv8T. Product (f_a2wfG :: Type
                                                                      -> Type) g_a2wfH a_iv8T
type family Empty_6989586621679610853 @(f_a2wfG :: Type
                                                    -> Type) @g_a2wfH @a_iv8T :: Product (f_a2wfG :: Type
                                                                                                    -> Type) g_a2wfH a_iv8T where
  Empty_6989586621679610853 @f_a2wfG @g_a2wfH @a_iv8T = Apply (Apply PairSym0 EmptySym0) EmptySym0
type TFHelper_6989586621679610858 :: forall (f_a2wfG :: Type
                                                        -> Type)
                                            g_a2wfH
                                            a_iv8U. Product (f_a2wfG :: Type
                                                                        -> Type) g_a2wfH a_iv8U
                                                    -> Product (f_a2wfG :: Type
                                                                            -> Type) g_a2wfH a_iv8U
                                                        -> Product (f_a2wfG :: Type
                                                                              -> Type) g_a2wfH a_iv8U
type family TFHelper_6989586621679610858 @(f_a2wfG :: Type
                                                      -> Type) @g_a2wfH @a_iv8U (a_a2wmE :: Product (f_a2wfG :: Type
                                                                                                                -> Type) g_a2wfH a_iv8U) (a_a2wmF :: Product (f_a2wfG :: Type
                                                                                                                                                                          -> Type) g_a2wfH a_iv8U) :: Product (f_a2wfG :: Type
                                                                                                                                                                                                                          -> Type) g_a2wfH a_iv8U where
  TFHelper_6989586621679610858 @f_a2wfG @g_a2wfH @a_iv8U ('Pair x1_a2wmJ y1_a2wmK :: Product (f_a2wfG :: Type
                                                                                                          -> Type) g_a2wfH a_iv8U) ('Pair x2_a2wmL y2_a2wmM :: Product (f_a2wfG :: Type
                                                                                                                                                                                  -> Type) g_a2wfH a_iv8U) = Apply (Apply PairSym0 (Apply (Apply (<|>@#@$) x1_a2wmJ) x2_a2wmL)) (Apply (Apply (<|>@#@$) y1_a2wmK) y2_a2wmM)
instance PAlternative (Product (f_a2wfG :: Type
                                            -> Type) g_a2wfH) where
  type Empty = Empty_6989586621679610853
  type (<|>) a_a2wmA a_a2wmB = TFHelper_6989586621679610858 a_a2wmA a_a2wmB
type Mzero_6989586621679610887 :: forall (f_a2wfM :: Type -> Type)
                                          g_a2wfN
                                          a_i19rf. Product (f_a2wfM :: Type
                                                                      -> Type) g_a2wfN a_i19rf
type family Mzero_6989586621679610887 @(f_a2wfM :: Type
                                                    -> Type) @g_a2wfN @a_i19rf :: Product (f_a2wfM :: Type
                                                                                                      -> Type) g_a2wfN a_i19rf where
  Mzero_6989586621679610887 @f_a2wfM @g_a2wfN @a_i19rf = Apply (Apply PairSym0 MzeroSym0) MzeroSym0
type Mplus_6989586621679610892 :: forall (f_a2wfM :: Type -> Type)
                                          g_a2wfN
                                          a_i19rg. Product (f_a2wfM :: Type
                                                                      -> Type) g_a2wfN a_i19rg
                                                  -> Product (f_a2wfM :: Type
                                                                          -> Type) g_a2wfN a_i19rg
                                                      -> Product (f_a2wfM :: Type
                                                                            -> Type) g_a2wfN a_i19rg
type family Mplus_6989586621679610892 @(f_a2wfM :: Type
                                                    -> Type) @g_a2wfN @a_i19rg (a_a2wnc :: Product (f_a2wfM :: Type
                                                                                                              -> Type) g_a2wfN a_i19rg) (a_a2wnd :: Product (f_a2wfM :: Type
                                                                                                                                                                        -> Type) g_a2wfN a_i19rg) :: Product (f_a2wfM :: Type
                                                                                                                                                                                                                          -> Type) g_a2wfN a_i19rg where
  Mplus_6989586621679610892 @f_a2wfM @g_a2wfN @a_i19rg ('Pair x1_a2wnh y1_a2wni :: Product (f_a2wfM :: Type
                                                                                                        -> Type) g_a2wfN a_i19rg) ('Pair x2_a2wnj y2_a2wnk :: Product (f_a2wfM :: Type
                                                                                                                                                                                  -> Type) g_a2wfN a_i19rg) = Apply (Apply PairSym0 (Apply (Apply MplusSym0 x1_a2wnh) x2_a2wnj)) (Apply (Apply MplusSym0 y1_a2wni) y2_a2wnk)
instance PMonadPlus (Product (f_a2wfM :: Type
                                          -> Type) g_a2wfN) where
  type Mzero = Mzero_6989586621679610887
  type Mplus a_a2wn8 a_a2wn9 = Mplus_6989586621679610892 a_a2wn8 a_a2wn9
instance (SEq (f_a2weQ a_a2weR), SEq (g_a2weS a_a2weR)) =>
          SEq (Product f_a2weQ g_a2weS a_a2weR) where
  (%==)
    (SPair (sA_6989586621679610612 :: Sing a_6989586621679610612_a2wj7)
            (sA_6989586621679610614 :: Sing a_6989586621679610614_a2wj8))
    (SPair (sB_6989586621679610616 :: Sing b_6989586621679610616_a2wj9)
            (sB_6989586621679610618 :: Sing b_6989586621679610618_a2wja))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679610612)
              sB_6989586621679610616))
        (applySing
            (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679610614)
            sB_6989586621679610618)
instance (SOrd (f_a2weT a_a2weU), SOrd (g_a2weV a_a2weU)) =>
          SOrd (Product f_a2weT g_a2weV a_a2weU) where
  sCompare
    (SPair (sA_6989586621679610624 :: Sing a_6989586621679610624_a2wjk)
            (sA_6989586621679610626 :: Sing a_6989586621679610626_a2wjl))
    (SPair (sB_6989586621679610628 :: Sing b_6989586621679610628_a2wjm)
            (sB_6989586621679610630 :: Sing b_6989586621679610630_a2wjn))
    = applySing
        (applySing
            (applySing (singFun3 @FoldlSym0 sFoldl) (singFun2 @(<>@#@$) (%<>)))
            SEQ)
        (applySing
            (applySing
              (singFun2 @(:@#@$) SCons)
              (applySing
                  (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679610624)
                  sB_6989586621679610628))
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing
                    (applySing (singFun2 @CompareSym0 sCompare) sA_6989586621679610626)
                    sB_6989586621679610630))
              SNil))
instance (SFunctor f_a2weW, SFunctor g_a2weX) =>
          SFunctor (Product f_a2weW g_a2weX) where
  sFmap
    (sF :: Sing f_a2wjx)
    (SPair (sX :: Sing x_a2wjy) (sY :: Sing y_a2wjz))
    = applySing
        (applySing
            (singFun2 @PairSym0 SPair)
            (applySing (applySing (singFun2 @FmapSym0 sFmap) sF) sX))
        (applySing (applySing (singFun2 @FmapSym0 sFmap) sF) sY)
  (%<$)
    (sA :: Sing a_a2wjJ)
    (SPair (sX :: Sing x_a2wjK) (sY :: Sing y_a2wjL))
    = applySing
        (applySing
            (singFun2 @PairSym0 SPair)
            (applySing (applySing (singFun2 @(<$@#@$) (%<$)) sA) sX))
        (applySing (applySing (singFun2 @(<$@#@$) (%<$)) sA) sY)
instance (SFoldable f_a2wf4, SFoldable g_a2wf5) =>
          SFoldable (Product f_a2wf4 g_a2wf5) where
  sFoldMap
    (sF :: Sing f_a2wjV)
    (SPair (sX :: Sing x_a2wjW) (sY :: Sing y_a2wjX))
    = applySing
        (applySing
            (singFun2 @MappendSym0 sMappend)
            (applySing (applySing (singFun2 @FoldMapSym0 sFoldMap) sF) sX))
        (applySing (applySing (singFun2 @FoldMapSym0 sFoldMap) sF) sY)
instance (STraversable f_a2wf9, STraversable g_a2wfa) =>
          STraversable (Product f_a2wf9 g_a2wfa) where
  sTraverse
    (sF :: Sing f_a2wk7)
    (SPair (sX :: Sing x_a2wk8) (sY :: Sing y_a2wk9))
    = applySing
        (applySing
            (applySing
              (singFun3 @LiftA2Sym0 sLiftA2) (singFun2 @PairSym0 SPair))
            (applySing (applySing (singFun2 @TraverseSym0 sTraverse) sF) sX))
        (applySing (applySing (singFun2 @TraverseSym0 sTraverse) sF) sY)
instance (SApplicative f_a2wfe, SApplicative g_a2wff) =>
          SApplicative (Product f_a2wfe g_a2wff) where
  sPure (sX :: Sing x_a2wkg)
    = applySing
        (applySing
            (singFun2 @PairSym0 SPair)
            (applySing (singFun1 @PureSym0 sPure) sX))
        (applySing (singFun1 @PureSym0 sPure) sX)
  (%<*>)
    (SPair (sF :: Sing f_a2wkq) (sG :: Sing g_a2wkr))
    (SPair (sX :: Sing x_a2wks) (sY :: Sing y_a2wkt))
    = applySing
        (applySing
            (singFun2 @PairSym0 SPair)
            (applySing (applySing (singFun2 @(<*>@#@$) (%<*>)) sF) sX))
        (applySing (applySing (singFun2 @(<*>@#@$) (%<*>)) sG) sY)
  sLiftA2
    (sF :: Sing f_a2wkG)
    (SPair (sA :: Sing a_a2wkH) (sB :: Sing b_a2wkI))
    (SPair (sX :: Sing x_a2wkJ) (sY :: Sing y_a2wkK))
    = applySing
        (applySing
            (singFun2 @PairSym0 SPair)
            (applySing
              (applySing (applySing (singFun3 @LiftA2Sym0 sLiftA2) sF) sA) sX))
        (applySing
            (applySing (applySing (singFun3 @LiftA2Sym0 sLiftA2) sF) sB) sY)
instance (SMonad f_a2wfq, SMonad g_a2wfr) =>
          SMonad (Product f_a2wfq g_a2wfr) where
  (%>>=)
    (SPair (sM :: Sing m_a2wm6) (sN :: Sing n_a2wm7))
    (sF :: Sing f_a2wm8)
    = let
        sSndP ::
          forall arg_a2wnl. Sing arg_a2wnl
                            -> Sing (Let6989586621679610829SndP f_a2wfq g_a2wfr m_a2wm6 n_a2wm7 f_a2wm8 arg_a2wnl)
        sFstP ::
          forall arg_a2wnn. Sing arg_a2wnn
                            -> Sing (Let6989586621679610829FstP f_a2wfq g_a2wfr m_a2wm6 n_a2wm7 f_a2wm8 arg_a2wnn)
        sSndP (SPair _ (sB :: Sing b_a2wmc)) = sB
        sFstP (SPair (sA :: Sing a_a2wmf) _) = sA
      in
        applySing
          (applySing
              (singFun2 @PairSym0 SPair)
              (applySing
                (applySing (singFun2 @(>>=@#@$) (%>>=)) sM)
                (applySing
                    (applySing
                      (singFun3 @(.@#@$) (%.))
                      (singFun1
                          @(Let6989586621679610829FstPSym0 f_a2wfq g_a2wfr m_a2wm6 n_a2wm7 f_a2wm8)
                          sFstP))
                    sF)))
          (applySing
              (applySing (singFun2 @(>>=@#@$) (%>>=)) sN)
              (applySing
                (applySing
                    (singFun3 @(.@#@$) (%.))
                    (singFun1
                      @(Let6989586621679610829SndPSym0 f_a2wfq g_a2wfr m_a2wm6 n_a2wm7 f_a2wm8)
                      sSndP))
                sF))
instance (SMonadZip f_a2wfz, SMonadZip g_a2wfA) =>
          SMonadZip (Product f_a2wfz g_a2wfA) where
  sMzipWith
    (sF :: Sing f_a2wms)
    (SPair (sX1 :: Sing x1_a2wmt) (sY1 :: Sing y1_a2wmu))
    (SPair (sX2 :: Sing x2_a2wmv) (sY2 :: Sing y2_a2wmw))
    = applySing
        (applySing
            (singFun2 @PairSym0 SPair)
            (applySing
              (applySing (applySing (singFun3 @MzipWithSym0 sMzipWith) sF) sX1)
              sX2))
        (applySing
            (applySing (applySing (singFun3 @MzipWithSym0 sMzipWith) sF) sY1)
            sY2)
instance (SAlternative f_a2wfG, SAlternative g_a2wfH) =>
          SAlternative (Product (f_a2wfG :: Type -> Type) g_a2wfH) where
  sEmpty
    = applySing (applySing (singFun2 @PairSym0 SPair) sEmpty) sEmpty
  (%<|>)
    (SPair (sX1 :: Sing x1_a2wmJ) (sY1 :: Sing y1_a2wmK))
    (SPair (sX2 :: Sing x2_a2wmL) (sY2 :: Sing y2_a2wmM))
    = applySing
        (applySing
            (singFun2 @PairSym0 SPair)
            (applySing (applySing (singFun2 @(<|>@#@$) (%<|>)) sX1) sX2))
        (applySing (applySing (singFun2 @(<|>@#@$) (%<|>)) sY1) sY2)
instance (SMonadPlus f_a2wfM, SMonadPlus g_a2wfN) =>
          SMonadPlus (Product (f_a2wfM :: Type -> Type) g_a2wfN) where
  sMzero
    = applySing (applySing (singFun2 @PairSym0 SPair) sMzero) sMzero
  sMplus
    (SPair (sX1 :: Sing x1_a2wnh) (sY1 :: Sing y1_a2wni))
    (SPair (sX2 :: Sing x2_a2wnj) (sY2 :: Sing y2_a2wnk))
    = applySing
        (applySing
            (singFun2 @PairSym0 SPair)
            (applySing (applySing (singFun2 @MplusSym0 sMplus) sX1) sX2))
        (applySing (applySing (singFun2 @MplusSym0 sMplus) sY1) sY2)
instance (SDecide (f_a2weQ a_a2weR), SDecide (g_a2weS a_a2weR)) =>
          SDecide (Product f_a2weQ g_a2weS a_a2weR) where
  (%~) (SPair a_a2wnx a_a2wny) (SPair b_a2wnz b_a2wnA)
    = (\cases
          (Proved Refl) (Proved Refl) -> Proved Refl
          (Disproved contra_a2wnB) _
            -> Disproved (\cases Refl -> contra_a2wnB Refl)
          _ (Disproved contra_a2wnB)
            -> Disproved (\cases Refl -> contra_a2wnB Refl))
        ((%~) a_a2wnx b_a2wnz) ((%~) a_a2wny b_a2wnA)
instance Eq (SProduct (z_a2wnC :: Product f_a2weQ g_a2weS a_a2weR)) where
  (==) _ _ = True
instance (SDecide (f_a2weQ a_a2weR), SDecide (g_a2weS a_a2weR)) =>
          Data.Type.Equality.TestEquality (SProduct :: Product f_a2weQ g_a2weS a_a2weR
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide (f_a2weQ a_a2weR), SDecide (g_a2weS a_a2weR)) =>
          Data.Type.Coercion.TestCoercion (SProduct :: Product f_a2weQ g_a2weS a_a2weR
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance Ord (SProduct (z_a2wnD :: Product f_a2weT g_a2weV a_a2weU)) where
  compare _ _ = EQ
