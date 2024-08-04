{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NoNamedWildCards #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
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
-- Module      :  Data.Traversable.Singletons
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted and singled versions of the 'Traversable' type class.
--
----------------------------------------------------------------------------

module Data.Traversable.Singletons (
  PTraversable(..), STraversable(..),
  For, sFor,
  ForM, sForM,
  MapAccumL, sMapAccumL,
  MapAccumR, sMapAccumR,
  FmapDefault, sFmapDefault,
  FoldMapDefault, sFoldMapDefault,

  -- * Defunctionalization symbols
  TraverseSym0, TraverseSym1, TraverseSym2,
  SequenceASym0, SequenceASym1,
  MapMSym0, MapMSym1, MapMSym2,
  SequenceSym0, SequenceSym1,

  ForSym0, ForSym1, ForSym2,
  ForMSym0, ForMSym1, ForMSym2,
  MapAccumLSym0, MapAccumLSym1, MapAccumLSym2, MapAccumLSym3,
  MapAccumRSym0, MapAccumRSym1, MapAccumRSym2, MapAccumRSym3,
  FmapDefaultSym0, FmapDefaultSym1, FmapDefaultSym2,
  FoldMapDefaultSym0, FoldMapDefaultSym1, FoldMapDefaultSym2
  ) where

import Control.Applicative
import Control.Monad.Singletons.Internal
import Data.Foldable.Singletons (SFoldable)
import Data.Functor.Const.Singletons
import Data.Functor.Identity
import Data.Functor.Identity.Singletons
import Data.Functor.Singletons ()
import Data.Kind
import Data.List.NonEmpty (NonEmpty(..))
import Data.Monoid
import Data.Monoid.Singletons
import Data.Proxy.Singletons
import Data.Singletons
import Data.Singletons.Base.Instances
import Data.Singletons.TH
import GHC.Base.Singletons hiding (Const, ConstSym0)

type StateL :: Type -> Type -> Type
newtype StateL s a = StateL (s ~> (s, a))
type SStateL :: forall s a. StateL s a -> Type
data SStateL state where
  SStateL :: Sing x -> SStateL ('StateL x)
type instance Sing @(StateL s a) = SStateL
type StateLSym0 :: forall s a. (s ~> (s, a)) ~> StateL s a
data StateLSym0 z
type instance Apply StateLSym0 x = 'StateL x

type StateR :: Type -> Type -> Type
newtype StateR s a = StateR (s ~> (s, a))
type SStateR :: forall s a. StateR s a -> Type
data SStateR state where
  SStateR :: Sing x -> SStateR ('StateR x)
type instance Sing @(StateR s a) = SStateR
type StateRSym0 :: forall s a. (s ~> (s, a)) ~> StateR s a
data StateRSym0 z
type instance Apply StateRSym0 x = 'StateR x

type RunStateRSym0 :: (~>) (StateR s_a19yR a_a19yS) ((~>) s_a19yR (s_a19yR,
                                                                    a_a19yS))
data RunStateRSym0 :: (~>) (StateR s_a19yR a_a19yS) ((~>) s_a19yR (s_a19yR,
                                                                    a_a19yS))
  where
    RunStateRSym0KindInference :: SameKind (Apply RunStateRSym0 arg_a19zH) (RunStateRSym1 arg_a19zH) =>
                                  RunStateRSym0 a6989586621679284930
type instance Apply @(StateR s_a19yR a_a19yS) @((~>) s_a19yR (s_a19yR,
                                                              a_a19yS)) RunStateRSym0 a6989586621679284930 = RunStateRSym1 a6989586621679284930
instance SuppressUnusedWarnings RunStateRSym0 where
  suppressUnusedWarnings = snd ((,) RunStateRSym0KindInference ())
type RunStateRSym1 :: StateR s_a19yR a_a19yS
                      -> (~>) s_a19yR (s_a19yR, a_a19yS)
data RunStateRSym1 (a6989586621679284930 :: StateR s_a19yR a_a19yS) :: (~>) s_a19yR (s_a19yR,
                                                                                      a_a19yS)
  where
    RunStateRSym1KindInference :: SameKind (Apply (RunStateRSym1 a6989586621679284930) arg_a19zH) (RunStateRSym2 a6989586621679284930 arg_a19zH) =>
                                  RunStateRSym1 a6989586621679284930 a6989586621679284931
type instance Apply @s_a19yR @(s_a19yR,
                                a_a19yS) (RunStateRSym1 a6989586621679284930) a6989586621679284931 = RunStateR a6989586621679284930 a6989586621679284931
instance SuppressUnusedWarnings (RunStateRSym1 a6989586621679284930) where
  suppressUnusedWarnings = snd ((,) RunStateRSym1KindInference ())
type RunStateRSym2 :: StateR s_a19yR a_a19yS
                      -> s_a19yR -> (s_a19yR, a_a19yS)
type family RunStateRSym2 @s_a19yR @a_a19yS (a6989586621679284930 :: StateR s_a19yR a_a19yS) (a6989586621679284931 :: s_a19yR) :: (s_a19yR,
                                                                                                                                    a_a19yS) where
  RunStateRSym2 a6989586621679284930 a6989586621679284931 = RunStateR a6989586621679284930 a6989586621679284931
type RunStateLSym0 :: (~>) (StateL s_a19yT a_a19yU) ((~>) s_a19yT (s_a19yT,
                                                                    a_a19yU))
data RunStateLSym0 :: (~>) (StateL s_a19yT a_a19yU) ((~>) s_a19yT (s_a19yT,
                                                                    a_a19yU))
  where
    RunStateLSym0KindInference :: SameKind (Apply RunStateLSym0 arg_a19zQ) (RunStateLSym1 arg_a19zQ) =>
                                  RunStateLSym0 a6989586621679284939
type instance Apply @(StateL s_a19yT a_a19yU) @((~>) s_a19yT (s_a19yT,
                                                              a_a19yU)) RunStateLSym0 a6989586621679284939 = RunStateLSym1 a6989586621679284939
instance SuppressUnusedWarnings RunStateLSym0 where
  suppressUnusedWarnings = snd ((,) RunStateLSym0KindInference ())
type RunStateLSym1 :: StateL s_a19yT a_a19yU
                      -> (~>) s_a19yT (s_a19yT, a_a19yU)
data RunStateLSym1 (a6989586621679284939 :: StateL s_a19yT a_a19yU) :: (~>) s_a19yT (s_a19yT,
                                                                                      a_a19yU)
  where
    RunStateLSym1KindInference :: SameKind (Apply (RunStateLSym1 a6989586621679284939) arg_a19zQ) (RunStateLSym2 a6989586621679284939 arg_a19zQ) =>
                                  RunStateLSym1 a6989586621679284939 a6989586621679284940
type instance Apply @s_a19yT @(s_a19yT,
                                a_a19yU) (RunStateLSym1 a6989586621679284939) a6989586621679284940 = RunStateL a6989586621679284939 a6989586621679284940
instance SuppressUnusedWarnings (RunStateLSym1 a6989586621679284939) where
  suppressUnusedWarnings = snd ((,) RunStateLSym1KindInference ())
type RunStateLSym2 :: StateL s_a19yT a_a19yU
                      -> s_a19yT -> (s_a19yT, a_a19yU)
type family RunStateLSym2 @s_a19yT @a_a19yU (a6989586621679284939 :: StateL s_a19yT a_a19yU) (a6989586621679284940 :: s_a19yT) :: (s_a19yT,
                                                                                                                                    a_a19yU) where
  RunStateLSym2 a6989586621679284939 a6989586621679284940 = RunStateL a6989586621679284939 a6989586621679284940
type RunStateR :: StateR s_a19yR a_a19yS
                  -> s_a19yR -> (s_a19yR, a_a19yS)
type family RunStateR @s_a19yR @a_a19yS (a_a19zF :: StateR s_a19yR a_a19yS) (a_a19zG :: s_a19yR) :: (s_a19yR,
                                                                                                      a_a19yS) where
  RunStateR ('StateR x_a19zK) a_6989586621679284925_a19zL = Apply x_a19zK a_6989586621679284925_a19zL
type RunStateL :: StateL s_a19yT a_a19yU
                  -> s_a19yT -> (s_a19yT, a_a19yU)
type family RunStateL @s_a19yT @a_a19yU (a_a19zO :: StateL s_a19yT a_a19yU) (a_a19zP :: s_a19yT) :: (s_a19yT,
                                                                                                      a_a19yU) where
  RunStateL ('StateL x_a19zT) a_6989586621679284934_a19zU = Apply x_a19zT a_6989586621679284934_a19zU
sRunStateR ::
  (forall (t_a19zV :: StateR s_a19yR a_a19yS) (t_a19zW :: s_a19yR).
    Sing t_a19zV
    -> Sing t_a19zW
      -> Sing (RunStateR t_a19zV t_a19zW :: (s_a19yR, a_a19yS)) :: Type)
sRunStateL ::
  (forall (t_a19A0 :: StateL s_a19yT a_a19yU) (t_a19A1 :: s_a19yT).
    Sing t_a19A0
    -> Sing t_a19A1
      -> Sing (RunStateL t_a19A0 t_a19A1 :: (s_a19yT, a_a19yU)) :: Type)
sRunStateR
  (SStateR (sX :: Sing x_a19zK))
  (sA_6989586621679284925 :: Sing a_6989586621679284925_a19zL)
  = applySing sX sA_6989586621679284925
sRunStateL
  (SStateL (sX :: Sing x_a19zT))
  (sA_6989586621679284934 :: Sing a_6989586621679284934_a19zU)
  = applySing sX sA_6989586621679284934
instance SingI (RunStateRSym0 :: (~>) (StateR s_a19yR a_a19yS) ((~>) s_a19yR (s_a19yR,
                                                                              a_a19yS))) where
  sing = singFun2 @RunStateRSym0 sRunStateR
instance SingI d_a19zX =>
          SingI (RunStateRSym1 (d_a19zX :: StateR s_a19yR a_a19yS) :: (~>) s_a19yR (s_a19yR,
                                                                                    a_a19yS)) where
  sing
    = singFun1
        @(RunStateRSym1 (d_a19zX :: StateR s_a19yR a_a19yS))
        (sRunStateR (sing @d_a19zX))
instance SingI1 (RunStateRSym1 :: StateR s_a19yR a_a19yS
                                  -> (~>) s_a19yR (s_a19yR, a_a19yS)) where
  liftSing (s_a19zZ :: Sing (d_a19zX :: StateR s_a19yR a_a19yS))
    = singFun1
        @(RunStateRSym1 (d_a19zX :: StateR s_a19yR a_a19yS))
        (sRunStateR s_a19zZ)
instance SingI (RunStateLSym0 :: (~>) (StateL s_a19yT a_a19yU) ((~>) s_a19yT (s_a19yT,
                                                                              a_a19yU))) where
  sing = singFun2 @RunStateLSym0 sRunStateL
instance SingI d_a19A2 =>
          SingI (RunStateLSym1 (d_a19A2 :: StateL s_a19yT a_a19yU) :: (~>) s_a19yT (s_a19yT,
                                                                                    a_a19yU)) where
  sing
    = singFun1
        @(RunStateLSym1 (d_a19A2 :: StateL s_a19yT a_a19yU))
        (sRunStateL (sing @d_a19A2))
instance SingI1 (RunStateLSym1 :: StateL s_a19yT a_a19yU
                                  -> (~>) s_a19yT (s_a19yT, a_a19yU)) where
  liftSing (s_a19A4 :: Sing (d_a19A2 :: StateL s_a19yT a_a19yU))
    = singFun1
        @(RunStateLSym1 (d_a19A2 :: StateL s_a19yT a_a19yU))
        (sRunStateL s_a19A4)

type TraverseSym0 :: forall (t_a19YT :: Type -> Type)
                                a_a19YV
                                f_a19YU
                                b_a19YW. (~>) ((~>) a_a19YV (f_a19YU b_a19YW)) ((~>) (t_a19YT a_a19YV) (f_a19YU (t_a19YT b_a19YW)))
data TraverseSym0 :: (~>) ((~>) a_a19YV (f_a19YU b_a19YW)) ((~>) (t_a19YT a_a19YV) (f_a19YU (t_a19YT b_a19YW)))
  where
    TraverseSym0KindInference :: SameKind (Apply TraverseSym0 arg_a19Z7) (TraverseSym1 arg_a19Z7) =>
                                  TraverseSym0 a6989586621679286506
type instance Apply @((~>) a_a19YV (f_a19YU b_a19YW)) @((~>) (t_a19YT a_a19YV) (f_a19YU (t_a19YT b_a19YW))) TraverseSym0 a6989586621679286506 = TraverseSym1 a6989586621679286506
instance SuppressUnusedWarnings TraverseSym0 where
  suppressUnusedWarnings = snd ((,) TraverseSym0KindInference ())
type TraverseSym1 :: forall (t_a19YT :: Type -> Type)
                            a_a19YV
                            f_a19YU
                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                      -> (~>) (t_a19YT a_a19YV) (f_a19YU (t_a19YT b_a19YW))
data TraverseSym1 (a6989586621679286506 :: (~>) a_a19YV (f_a19YU b_a19YW)) :: (~>) (t_a19YT a_a19YV) (f_a19YU (t_a19YT b_a19YW))
  where
    TraverseSym1KindInference :: SameKind (Apply (TraverseSym1 a6989586621679286506) arg_a19Z7) (TraverseSym2 a6989586621679286506 arg_a19Z7) =>
                                  TraverseSym1 a6989586621679286506 a6989586621679286507
type instance Apply @(t_a19YT a_a19YV) @(f_a19YU (t_a19YT b_a19YW)) (TraverseSym1 a6989586621679286506) a6989586621679286507 = Traverse a6989586621679286506 a6989586621679286507
instance SuppressUnusedWarnings (TraverseSym1 a6989586621679286506) where
  suppressUnusedWarnings = snd ((,) TraverseSym1KindInference ())
type TraverseSym2 :: forall (t_a19YT :: Type -> Type)
                            a_a19YV
                            f_a19YU
                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                      -> t_a19YT a_a19YV -> f_a19YU (t_a19YT b_a19YW)
type family TraverseSym2 @(t_a19YT :: Type
                                      -> Type) @a_a19YV @f_a19YU @b_a19YW (a6989586621679286506 :: (~>) a_a19YV (f_a19YU b_a19YW)) (a6989586621679286507 :: t_a19YT a_a19YV) :: f_a19YU (t_a19YT b_a19YW) where
  TraverseSym2 a6989586621679286506 a6989586621679286507 = Traverse a6989586621679286506 a6989586621679286507
type SequenceASym0 :: forall (t_a19YT :: Type -> Type)
                              f_a19YX
                              a_a19YY. (~>) (t_a19YT (f_a19YX a_a19YY)) (f_a19YX (t_a19YT a_a19YY))
data SequenceASym0 :: (~>) (t_a19YT (f_a19YX a_a19YY)) (f_a19YX (t_a19YT a_a19YY))
  where
    SequenceASym0KindInference :: SameKind (Apply SequenceASym0 arg_a19Zb) (SequenceASym1 arg_a19Zb) =>
                                  SequenceASym0 a6989586621679286510
type instance Apply @(t_a19YT (f_a19YX a_a19YY)) @(f_a19YX (t_a19YT a_a19YY)) SequenceASym0 a6989586621679286510 = SequenceA a6989586621679286510
instance SuppressUnusedWarnings SequenceASym0 where
  suppressUnusedWarnings = snd ((,) SequenceASym0KindInference ())
type SequenceASym1 :: forall (t_a19YT :: Type -> Type)
                              f_a19YX
                              a_a19YY. t_a19YT (f_a19YX a_a19YY) -> f_a19YX (t_a19YT a_a19YY)
type family SequenceASym1 @(t_a19YT :: Type
                                        -> Type) @f_a19YX @a_a19YY (a6989586621679286510 :: t_a19YT (f_a19YX a_a19YY)) :: f_a19YX (t_a19YT a_a19YY) where
  SequenceASym1 a6989586621679286510 = SequenceA a6989586621679286510
type MapMSym0 :: forall (t_a19YT :: Type -> Type)
                        a_a19Z0
                        m_a19YZ
                        b_a19Z1. (~>) ((~>) a_a19Z0 (m_a19YZ b_a19Z1)) ((~>) (t_a19YT a_a19Z0) (m_a19YZ (t_a19YT b_a19Z1)))
data MapMSym0 :: (~>) ((~>) a_a19Z0 (m_a19YZ b_a19Z1)) ((~>) (t_a19YT a_a19Z0) (m_a19YZ (t_a19YT b_a19Z1)))
  where
    MapMSym0KindInference :: SameKind (Apply MapMSym0 arg_a19Zf) (MapMSym1 arg_a19Zf) =>
                              MapMSym0 a6989586621679286514
type instance Apply @((~>) a_a19Z0 (m_a19YZ b_a19Z1)) @((~>) (t_a19YT a_a19Z0) (m_a19YZ (t_a19YT b_a19Z1))) MapMSym0 a6989586621679286514 = MapMSym1 a6989586621679286514
instance SuppressUnusedWarnings MapMSym0 where
  suppressUnusedWarnings = snd ((,) MapMSym0KindInference ())
type MapMSym1 :: forall (t_a19YT :: Type -> Type)
                        a_a19Z0
                        m_a19YZ
                        b_a19Z1. (~>) a_a19Z0 (m_a19YZ b_a19Z1)
                                  -> (~>) (t_a19YT a_a19Z0) (m_a19YZ (t_a19YT b_a19Z1))
data MapMSym1 (a6989586621679286514 :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)) :: (~>) (t_a19YT a_a19Z0) (m_a19YZ (t_a19YT b_a19Z1))
  where
    MapMSym1KindInference :: SameKind (Apply (MapMSym1 a6989586621679286514) arg_a19Zf) (MapMSym2 a6989586621679286514 arg_a19Zf) =>
                              MapMSym1 a6989586621679286514 a6989586621679286515
type instance Apply @(t_a19YT a_a19Z0) @(m_a19YZ (t_a19YT b_a19Z1)) (MapMSym1 a6989586621679286514) a6989586621679286515 = MapM a6989586621679286514 a6989586621679286515
instance SuppressUnusedWarnings (MapMSym1 a6989586621679286514) where
  suppressUnusedWarnings = snd ((,) MapMSym1KindInference ())
type MapMSym2 :: forall (t_a19YT :: Type -> Type)
                        a_a19Z0
                        m_a19YZ
                        b_a19Z1. (~>) a_a19Z0 (m_a19YZ b_a19Z1)
                                  -> t_a19YT a_a19Z0 -> m_a19YZ (t_a19YT b_a19Z1)
type family MapMSym2 @(t_a19YT :: Type
                                  -> Type) @a_a19Z0 @m_a19YZ @b_a19Z1 (a6989586621679286514 :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)) (a6989586621679286515 :: t_a19YT a_a19Z0) :: m_a19YZ (t_a19YT b_a19Z1) where
  MapMSym2 a6989586621679286514 a6989586621679286515 = MapM a6989586621679286514 a6989586621679286515
type SequenceSym0 :: forall (t_a19YT :: Type -> Type)
                            m_a19Z2
                            a_a19Z3. (~>) (t_a19YT (m_a19Z2 a_a19Z3)) (m_a19Z2 (t_a19YT a_a19Z3))
data SequenceSym0 :: (~>) (t_a19YT (m_a19Z2 a_a19Z3)) (m_a19Z2 (t_a19YT a_a19Z3))
  where
    SequenceSym0KindInference :: SameKind (Apply SequenceSym0 arg_a19Zj) (SequenceSym1 arg_a19Zj) =>
                                  SequenceSym0 a6989586621679286518
type instance Apply @(t_a19YT (m_a19Z2 a_a19Z3)) @(m_a19Z2 (t_a19YT a_a19Z3)) SequenceSym0 a6989586621679286518 = Sequence a6989586621679286518
instance SuppressUnusedWarnings SequenceSym0 where
  suppressUnusedWarnings = snd ((,) SequenceSym0KindInference ())
type SequenceSym1 :: forall (t_a19YT :: Type -> Type)
                            m_a19Z2
                            a_a19Z3. t_a19YT (m_a19Z2 a_a19Z3) -> m_a19Z2 (t_a19YT a_a19Z3)
type family SequenceSym1 @(t_a19YT :: Type
                                      -> Type) @m_a19Z2 @a_a19Z3 (a6989586621679286518 :: t_a19YT (m_a19Z2 a_a19Z3)) :: m_a19Z2 (t_a19YT a_a19Z3) where
  SequenceSym1 a6989586621679286518 = Sequence a6989586621679286518
type Traverse_6989586621679286521 :: forall (t_a19YT :: Type
                                                        -> Type)
                                            a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> t_a19YT a_a19YV
                                                        -> f_a19YU (t_a19YT b_a19YW)
type family Traverse_6989586621679286521 @(t_a19YT :: Type
                                                      -> Type) @a_a19YV @f_a19YU @b_a19YW (a_a19Zr :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a19Zs :: t_a19YT a_a19YV) :: f_a19YU (t_a19YT b_a19YW) where
  Traverse_6989586621679286521 @t_a19YT @a_a19YV @f_a19YU @b_a19YW (f_a19Zw :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_6989586621679286523_a19Zx :: t_a19YT a_a19YV) = Apply (Apply (Apply (.@#@$) SequenceASym0) (Apply FmapSym0 f_a19Zw)) a_6989586621679286523_a19Zx
type SequenceA_6989586621679286533 :: forall (t_a19YT :: Type
                                                          -> Type)
                                              f_a19YX
                                              a_a19YY. t_a19YT (f_a19YX a_a19YY)
                                                      -> f_a19YX (t_a19YT a_a19YY)
type family SequenceA_6989586621679286533 @(t_a19YT :: Type
                                                        -> Type) @f_a19YX @a_a19YY (a_a19ZD :: t_a19YT (f_a19YX a_a19YY)) :: f_a19YX (t_a19YT a_a19YY) where
  SequenceA_6989586621679286533 @t_a19YT @f_a19YX @a_a19YY (a_6989586621679286535_a19ZG :: t_a19YT (f_a19YX a_a19YY)) = Apply (Apply TraverseSym0 IdSym0) a_6989586621679286535_a19ZG
type MapM_6989586621679286543 :: forall (t_a19YT :: Type -> Type)
                                        a_a19Z0
                                        m_a19YZ
                                        b_a19Z1. (~>) a_a19Z0 (m_a19YZ b_a19Z1)
                                                  -> t_a19YT a_a19Z0 -> m_a19YZ (t_a19YT b_a19Z1)
type family MapM_6989586621679286543 @(t_a19YT :: Type
                                                  -> Type) @a_a19Z0 @m_a19YZ @b_a19Z1 (a_a19ZP :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)) (a_a19ZQ :: t_a19YT a_a19Z0) :: m_a19YZ (t_a19YT b_a19Z1) where
  MapM_6989586621679286543 @t_a19YT @a_a19Z0 @m_a19YZ @b_a19Z1 (a_6989586621679286545_a19ZU :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)) (a_6989586621679286547_a19ZV :: t_a19YT a_a19Z0) = Apply (Apply TraverseSym0 a_6989586621679286545_a19ZU) a_6989586621679286547_a19ZV
type Sequence_6989586621679286557 :: forall (t_a19YT :: Type
                                                        -> Type)
                                            m_a19Z2
                                            a_a19Z3. t_a19YT (m_a19Z2 a_a19Z3)
                                                      -> m_a19Z2 (t_a19YT a_a19Z3)
type family Sequence_6989586621679286557 @(t_a19YT :: Type
                                                      -> Type) @m_a19Z2 @a_a19Z3 (a_a1a01 :: t_a19YT (m_a19Z2 a_a19Z3)) :: m_a19Z2 (t_a19YT a_a19Z3) where
  Sequence_6989586621679286557 @t_a19YT @m_a19Z2 @a_a19Z3 (a_6989586621679286559_a1a04 :: t_a19YT (m_a19Z2 a_a19Z3)) = Apply SequenceASym0 a_6989586621679286559_a1a04
type PTraversable :: (Type -> Type) -> Constraint
class PTraversable t_a19YT where
  type family Traverse (arg_a19Z5 :: (~>) a_a19YV (f_a19YU b_a19YW)) (arg_a19Z6 :: t_a19YT a_a19YV) :: f_a19YU (t_a19YT b_a19YW)
  type family SequenceA (arg_a19Za :: t_a19YT (f_a19YX a_a19YY)) :: f_a19YX (t_a19YT a_a19YY)
  type family MapM (arg_a19Zd :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)) (arg_a19Ze :: t_a19YT a_a19Z0) :: m_a19YZ (t_a19YT b_a19Z1)
  type family Sequence (arg_a19Zi :: t_a19YT (m_a19Z2 a_a19Z3)) :: m_a19Z2 (t_a19YT a_a19Z3)
  type Traverse a_a19Zl a_a19Zm = Traverse_6989586621679286521 a_a19Zl a_a19Zm
  type SequenceA a_a19Zy = SequenceA_6989586621679286533 a_a19Zy
  type MapM a_a19ZH a_a19ZI = MapM_6989586621679286543 a_a19ZH a_a19ZI
  type Sequence a_a19ZW = Sequence_6989586621679286557 a_a19ZW
class (SFunctor t_a19YT,
        SFoldable t_a19YT) => STraversable t_a19YT where
  sTraverse ::
    (forall (t_a1a05 :: (~>) a_a19YV (f_a19YU b_a19YW))
            (t_a1a06 :: t_a19YT a_a19YV).
      SApplicative f_a19YU =>
      Sing t_a1a05
      -> Sing t_a1a06
        -> Sing (Traverse t_a1a05 t_a1a06 :: f_a19YU (t_a19YT b_a19YW)) :: Type)
  sSequenceA ::
    (forall (t_a1a0a :: t_a19YT (f_a19YX a_a19YY)).
      SApplicative f_a19YX =>
      Sing t_a1a0a
      -> Sing (SequenceA t_a1a0a :: f_a19YX (t_a19YT a_a19YY)) :: Type)
  sMapM ::
    (forall (t_a1a0c :: (~>) a_a19Z0 (m_a19YZ b_a19Z1))
            (t_a1a0d :: t_a19YT a_a19Z0).
      SMonad m_a19YZ =>
      Sing t_a1a0c
      -> Sing t_a1a0d
        -> Sing (MapM t_a1a0c t_a1a0d :: m_a19YZ (t_a19YT b_a19Z1)) :: Type)
  sSequence ::
    (forall (t_a1a0h :: t_a19YT (m_a19Z2 a_a19Z3)).
      SMonad m_a19Z2 =>
      Sing t_a1a0h
      -> Sing (Sequence t_a1a0h :: m_a19Z2 (t_a19YT a_a19Z3)) :: Type)
  default sTraverse ::
            (forall (t_a1a05 :: (~>) a_a19YV (f_a19YU b_a19YW))
                    (t_a1a06 :: t_a19YT a_a19YV).
              ((Traverse t_a1a05 t_a1a06 :: f_a19YU (t_a19YT b_a19YW))
              ~ Traverse_6989586621679286521 t_a1a05 t_a1a06,
              SApplicative f_a19YU) =>
              Sing t_a1a05
              -> Sing t_a1a06
                -> Sing (Traverse t_a1a05 t_a1a06 :: f_a19YU (t_a19YT b_a19YW)) :: Type)
  default sSequenceA ::
            (forall (t_a1a0a :: t_a19YT (f_a19YX a_a19YY)).
              ((SequenceA t_a1a0a :: f_a19YX (t_a19YT a_a19YY))
              ~ SequenceA_6989586621679286533 t_a1a0a,
              SApplicative f_a19YX) =>
              Sing t_a1a0a
              -> Sing (SequenceA t_a1a0a :: f_a19YX (t_a19YT a_a19YY)) :: Type)
  default sMapM ::
            (forall (t_a1a0c :: (~>) a_a19Z0 (m_a19YZ b_a19Z1))
                    (t_a1a0d :: t_a19YT a_a19Z0).
              ((MapM t_a1a0c t_a1a0d :: m_a19YZ (t_a19YT b_a19Z1))
              ~ MapM_6989586621679286543 t_a1a0c t_a1a0d,
              SMonad m_a19YZ) =>
              Sing t_a1a0c
              -> Sing t_a1a0d
                -> Sing (MapM t_a1a0c t_a1a0d :: m_a19YZ (t_a19YT b_a19Z1)) :: Type)
  default sSequence ::
            (forall (t_a1a0h :: t_a19YT (m_a19Z2 a_a19Z3)).
              ((Sequence t_a1a0h :: m_a19Z2 (t_a19YT a_a19Z3))
              ~ Sequence_6989586621679286557 t_a1a0h,
              SMonad m_a19Z2) =>
              Sing t_a1a0h
              -> Sing (Sequence t_a1a0h :: m_a19Z2 (t_a19YT a_a19Z3)) :: Type)
  sTraverse
    (sF :: Sing f_a19Zw)
    (sA_6989586621679286523 :: Sing a_6989586621679286523_a19Zx)
    = applySing
        (applySing
            (applySing
              (singFun3 @(.@#@$) (%.)) (singFun1 @SequenceASym0 sSequenceA))
            (applySing (singFun2 @FmapSym0 sFmap) sF))
        sA_6989586621679286523
  sSequenceA
    (sA_6989586621679286535 :: Sing a_6989586621679286535_a19ZG)
    = applySing
        (applySing
            (singFun2 @TraverseSym0 sTraverse) (singFun1 @IdSym0 sId))
        sA_6989586621679286535
  sMapM
    (sA_6989586621679286545 :: Sing a_6989586621679286545_a19ZU)
    (sA_6989586621679286547 :: Sing a_6989586621679286547_a19ZV)
    = applySing
        (applySing
            (singFun2 @TraverseSym0 sTraverse) sA_6989586621679286545)
        sA_6989586621679286547
  sSequence
    (sA_6989586621679286559 :: Sing a_6989586621679286559_a1a04)
    = applySing
        (singFun1 @SequenceASym0 sSequenceA) sA_6989586621679286559
type STraversable :: (Type -> Type) -> Constraint
instance (STraversable t_a19YT, SApplicative f_a19YU) =>
          SingI (TraverseSym0 :: (~>) ((~>) a_a19YV (f_a19YU b_a19YW)) ((~>) (t_a19YT a_a19YV) (f_a19YU (t_a19YT b_a19YW)))) where
  sing = singFun2 @TraverseSym0 sTraverse
instance (STraversable t_a19YT,
          SApplicative f_a19YU,
          SingI d_a1a07) =>
          SingI (TraverseSym1 (d_a1a07 :: (~>) a_a19YV (f_a19YU b_a19YW)) :: (~>) (t_a19YT a_a19YV) (f_a19YU (t_a19YT b_a19YW))) where
  sing
    = singFun1
        @(TraverseSym1 (d_a1a07 :: (~>) a_a19YV (f_a19YU b_a19YW)))
        (sTraverse (sing @d_a1a07))
instance (STraversable t_a19YT, SApplicative f_a19YU) =>
          SingI1 (TraverseSym1 :: (~>) a_a19YV (f_a19YU b_a19YW)
                                  -> (~>) (t_a19YT a_a19YV) (f_a19YU (t_a19YT b_a19YW))) where
  liftSing
    (s_a1a09 :: Sing (d_a1a07 :: (~>) a_a19YV (f_a19YU b_a19YW)))
    = singFun1
        @(TraverseSym1 (d_a1a07 :: (~>) a_a19YV (f_a19YU b_a19YW)))
        (sTraverse s_a1a09)
instance (STraversable t_a19YT, SApplicative f_a19YX) =>
          SingI (SequenceASym0 :: (~>) (t_a19YT (f_a19YX a_a19YY)) (f_a19YX (t_a19YT a_a19YY))) where
  sing = singFun1 @SequenceASym0 sSequenceA
instance (STraversable t_a19YT, SMonad m_a19YZ) =>
          SingI (MapMSym0 :: (~>) ((~>) a_a19Z0 (m_a19YZ b_a19Z1)) ((~>) (t_a19YT a_a19Z0) (m_a19YZ (t_a19YT b_a19Z1)))) where
  sing = singFun2 @MapMSym0 sMapM
instance (STraversable t_a19YT, SMonad m_a19YZ, SingI d_a1a0e) =>
          SingI (MapMSym1 (d_a1a0e :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)) :: (~>) (t_a19YT a_a19Z0) (m_a19YZ (t_a19YT b_a19Z1))) where
  sing
    = singFun1
        @(MapMSym1 (d_a1a0e :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)))
        (sMapM (sing @d_a1a0e))
instance (STraversable t_a19YT, SMonad m_a19YZ) =>
          SingI1 (MapMSym1 :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)
                              -> (~>) (t_a19YT a_a19Z0) (m_a19YZ (t_a19YT b_a19Z1))) where
  liftSing
    (s_a1a0g :: Sing (d_a1a0e :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)))
    = singFun1
        @(MapMSym1 (d_a1a0e :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)))
        (sMapM s_a1a0g)
instance (STraversable t_a19YT, SMonad m_a19Z2) =>
          SingI (SequenceSym0 :: (~>) (t_a19YT (m_a19Z2 a_a19Z3)) (m_a19Z2 (t_a19YT a_a19Z3))) where
  sing = singFun1 @SequenceSym0 sSequence

data Let6989586621679292376MkConstSym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 (f6989586621679292374 :: (~>) a6989586621679291882 m6989586621679291881) (x6989586621679292375 :: t6989586621679291880 a6989586621679291882) :: (~>) m6989586621679291881 (Const m6989586621679291881 ())
      where
        Let6989586621679292376MkConstSym0KindInference :: SameKind (Apply (Let6989586621679292376MkConstSym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375) arg_a1bvS) (Let6989586621679292376MkConstSym1 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 arg_a1bvS) =>
                                                          Let6989586621679292376MkConstSym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 a6989586621679292379
type instance Apply @m6989586621679291881 @(Const m6989586621679291881 ()) (Let6989586621679292376MkConstSym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375) a6989586621679292379 = Let6989586621679292376MkConst t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 a6989586621679292379
instance SuppressUnusedWarnings (Let6989586621679292376MkConstSym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679292376MkConstSym0KindInference ())
type family Let6989586621679292376MkConstSym1 t6989586621679291880 m6989586621679291881 a6989586621679291882 (f6989586621679292374 :: (~>) a6989586621679291882 m6989586621679291881) (x6989586621679292375 :: t6989586621679291880 a6989586621679291882) (a6989586621679292379 :: m6989586621679291881) :: Const m6989586621679291881 () where
  Let6989586621679292376MkConstSym1 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 a6989586621679292379 = Let6989586621679292376MkConst t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 a6989586621679292379
type family Let6989586621679292376MkConst t6989586621679291880 m6989586621679291881 a6989586621679291882 (f6989586621679292374 :: (~>) a6989586621679291882 m6989586621679291881) (x6989586621679292375 :: t6989586621679291880 a6989586621679291882) (a_a1bvR :: m6989586621679291881) :: Const m6989586621679291881 () where
  Let6989586621679292376MkConst t_a1bnO m_a1bnP a_a1bnQ f_a1bvM x_a1bvN a_6989586621679292377_a1bvT = Apply ConstSym0 a_6989586621679292377_a1bvT
type family LamCases_6989586621679292382_a1bvV t6989586621679291880 m6989586621679291881 a6989586621679291882 (f6989586621679292374 :: (~>) a6989586621679291882 m6989586621679291881) (x6989586621679292375 :: t6989586621679291880 a6989586621679291882) a_6989586621679292385_a1bvY where
  LamCases_6989586621679292382_a1bvV t_a1bnO m_a1bnP a_a1bnQ f_a1bvM x_a1bvN ('Const y_a1bvW) = y_a1bvW
data LamCases_6989586621679292382Sym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 (f6989586621679292374 :: (~>) a6989586621679291882 m6989586621679291881) (x6989586621679292375 :: t6989586621679291880 a6989586621679291882) a_69895866216792923856989586621679292386
  where
    LamCases_6989586621679292382Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292382Sym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375) arg_a1bvZ) (LamCases_6989586621679292382Sym1 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 arg_a1bvZ) =>
                                                      LamCases_6989586621679292382Sym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 a_69895866216792923856989586621679292386
type instance Apply @_ @_ (LamCases_6989586621679292382Sym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375) a_69895866216792923856989586621679292386 = LamCases_6989586621679292382_a1bvV t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 a_69895866216792923856989586621679292386
instance SuppressUnusedWarnings (LamCases_6989586621679292382Sym0 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292382Sym0KindInference ())
type family LamCases_6989586621679292382Sym1 t6989586621679291880 m6989586621679291881 a6989586621679291882 (f6989586621679292374 :: (~>) a6989586621679291882 m6989586621679291881) (x6989586621679292375 :: t6989586621679291880 a6989586621679291882) a_69895866216792923856989586621679292386 where
  LamCases_6989586621679292382Sym1 t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 a_69895866216792923856989586621679292386 = LamCases_6989586621679292382_a1bvV t6989586621679291880 m6989586621679291881 a6989586621679291882 f6989586621679292374 x6989586621679292375 a_69895866216792923856989586621679292386
type family LamCases_6989586621679292395_a1bw8 t6989586621679291883 a6989586621679291884 b6989586621679291885 (f6989586621679292393 :: (~>) a6989586621679291884 b6989586621679291885) (x6989586621679292394 :: t6989586621679291883 a6989586621679291884) a_6989586621679292398_a1bwb where
  LamCases_6989586621679292395_a1bw8 t_a1bnR a_a1bnS b_a1bnT f_a1bw5 x_a1bw6 ('Identity y_a1bw9) = y_a1bw9
data LamCases_6989586621679292395Sym0 t6989586621679291883 a6989586621679291884 b6989586621679291885 (f6989586621679292393 :: (~>) a6989586621679291884 b6989586621679291885) (x6989586621679292394 :: t6989586621679291883 a6989586621679291884) a_69895866216792923986989586621679292399
  where
    LamCases_6989586621679292395Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292395Sym0 t6989586621679291883 a6989586621679291884 b6989586621679291885 f6989586621679292393 x6989586621679292394) arg_a1bwc) (LamCases_6989586621679292395Sym1 t6989586621679291883 a6989586621679291884 b6989586621679291885 f6989586621679292393 x6989586621679292394 arg_a1bwc) =>
                                                      LamCases_6989586621679292395Sym0 t6989586621679291883 a6989586621679291884 b6989586621679291885 f6989586621679292393 x6989586621679292394 a_69895866216792923986989586621679292399
type instance Apply @_ @_ (LamCases_6989586621679292395Sym0 t6989586621679291883 a6989586621679291884 b6989586621679291885 f6989586621679292393 x6989586621679292394) a_69895866216792923986989586621679292399 = LamCases_6989586621679292395_a1bw8 t6989586621679291883 a6989586621679291884 b6989586621679291885 f6989586621679292393 x6989586621679292394 a_69895866216792923986989586621679292399
instance SuppressUnusedWarnings (LamCases_6989586621679292395Sym0 t6989586621679291883 a6989586621679291884 b6989586621679291885 f6989586621679292393 x6989586621679292394) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292395Sym0KindInference ())
type family LamCases_6989586621679292395Sym1 t6989586621679291883 a6989586621679291884 b6989586621679291885 (f6989586621679292393 :: (~>) a6989586621679291884 b6989586621679291885) (x6989586621679292394 :: t6989586621679291883 a6989586621679291884) a_69895866216792923986989586621679292399 where
  LamCases_6989586621679292395Sym1 t6989586621679291883 a6989586621679291884 b6989586621679291885 f6989586621679292393 x6989586621679292394 a_69895866216792923986989586621679292399 = LamCases_6989586621679292395_a1bw8 t6989586621679291883 a6989586621679291884 b6989586621679291885 f6989586621679292393 x6989586621679292394 a_69895866216792923986989586621679292399
type FoldMapDefaultSym0 :: forall t_a1bnO
                                  m_a1bnP
                                  a_a1bnQ. (~>) ((~>) a_a1bnQ m_a1bnP) ((~>) (t_a1bnO a_a1bnQ) m_a1bnP)
data FoldMapDefaultSym0 :: (~>) ((~>) a_a1bnQ m_a1bnP) ((~>) (t_a1bnO a_a1bnQ) m_a1bnP)
  where
    FoldMapDefaultSym0KindInference :: SameKind (Apply FoldMapDefaultSym0 arg_a1bvJ) (FoldMapDefaultSym1 arg_a1bvJ) =>
                                        FoldMapDefaultSym0 a6989586621679292372
type instance Apply @((~>) a_a1bnQ m_a1bnP) @((~>) (t_a1bnO a_a1bnQ) m_a1bnP) FoldMapDefaultSym0 a6989586621679292372 = FoldMapDefaultSym1 a6989586621679292372
instance SuppressUnusedWarnings FoldMapDefaultSym0 where
  suppressUnusedWarnings
    = snd ((,) FoldMapDefaultSym0KindInference ())
type FoldMapDefaultSym1 :: forall t_a1bnO
                                  m_a1bnP
                                  a_a1bnQ. (~>) a_a1bnQ m_a1bnP
                                            -> (~>) (t_a1bnO a_a1bnQ) m_a1bnP
data FoldMapDefaultSym1 (a6989586621679292372 :: (~>) a_a1bnQ m_a1bnP) :: (~>) (t_a1bnO a_a1bnQ) m_a1bnP
  where
    FoldMapDefaultSym1KindInference :: SameKind (Apply (FoldMapDefaultSym1 a6989586621679292372) arg_a1bvJ) (FoldMapDefaultSym2 a6989586621679292372 arg_a1bvJ) =>
                                        FoldMapDefaultSym1 a6989586621679292372 a6989586621679292373
type instance Apply @(t_a1bnO a_a1bnQ) @m_a1bnP (FoldMapDefaultSym1 a6989586621679292372) a6989586621679292373 = FoldMapDefault a6989586621679292372 a6989586621679292373
instance SuppressUnusedWarnings (FoldMapDefaultSym1 a6989586621679292372) where
  suppressUnusedWarnings
    = snd ((,) FoldMapDefaultSym1KindInference ())
type FoldMapDefaultSym2 :: forall t_a1bnO
                                  m_a1bnP
                                  a_a1bnQ. (~>) a_a1bnQ m_a1bnP -> t_a1bnO a_a1bnQ -> m_a1bnP
type family FoldMapDefaultSym2 @t_a1bnO @m_a1bnP @a_a1bnQ (a6989586621679292372 :: (~>) a_a1bnQ m_a1bnP) (a6989586621679292373 :: t_a1bnO a_a1bnQ) :: m_a1bnP where
  FoldMapDefaultSym2 a6989586621679292372 a6989586621679292373 = FoldMapDefault a6989586621679292372 a6989586621679292373
type FmapDefaultSym0 :: forall t_a1bnR
                                a_a1bnS
                                b_a1bnT. (~>) ((~>) a_a1bnS b_a1bnT) ((~>) (t_a1bnR a_a1bnS) (t_a1bnR b_a1bnT))
data FmapDefaultSym0 :: (~>) ((~>) a_a1bnS b_a1bnT) ((~>) (t_a1bnR a_a1bnS) (t_a1bnR b_a1bnT))
  where
    FmapDefaultSym0KindInference :: SameKind (Apply FmapDefaultSym0 arg_a1bw2) (FmapDefaultSym1 arg_a1bw2) =>
                                    FmapDefaultSym0 a6989586621679292391
type instance Apply @((~>) a_a1bnS b_a1bnT) @((~>) (t_a1bnR a_a1bnS) (t_a1bnR b_a1bnT)) FmapDefaultSym0 a6989586621679292391 = FmapDefaultSym1 a6989586621679292391
instance SuppressUnusedWarnings FmapDefaultSym0 where
  suppressUnusedWarnings = snd ((,) FmapDefaultSym0KindInference ())
type FmapDefaultSym1 :: forall t_a1bnR
                                a_a1bnS
                                b_a1bnT. (~>) a_a1bnS b_a1bnT
                                        -> (~>) (t_a1bnR a_a1bnS) (t_a1bnR b_a1bnT)
data FmapDefaultSym1 (a6989586621679292391 :: (~>) a_a1bnS b_a1bnT) :: (~>) (t_a1bnR a_a1bnS) (t_a1bnR b_a1bnT)
  where
    FmapDefaultSym1KindInference :: SameKind (Apply (FmapDefaultSym1 a6989586621679292391) arg_a1bw2) (FmapDefaultSym2 a6989586621679292391 arg_a1bw2) =>
                                    FmapDefaultSym1 a6989586621679292391 a6989586621679292392
type instance Apply @(t_a1bnR a_a1bnS) @(t_a1bnR b_a1bnT) (FmapDefaultSym1 a6989586621679292391) a6989586621679292392 = FmapDefault a6989586621679292391 a6989586621679292392
instance SuppressUnusedWarnings (FmapDefaultSym1 a6989586621679292391) where
  suppressUnusedWarnings = snd ((,) FmapDefaultSym1KindInference ())
type FmapDefaultSym2 :: forall t_a1bnR
                                a_a1bnS
                                b_a1bnT. (~>) a_a1bnS b_a1bnT
                                        -> t_a1bnR a_a1bnS -> t_a1bnR b_a1bnT
type family FmapDefaultSym2 @t_a1bnR @a_a1bnS @b_a1bnT (a6989586621679292391 :: (~>) a_a1bnS b_a1bnT) (a6989586621679292392 :: t_a1bnR a_a1bnS) :: t_a1bnR b_a1bnT where
  FmapDefaultSym2 a6989586621679292391 a6989586621679292392 = FmapDefault a6989586621679292391 a6989586621679292392
type MapAccumRSym0 :: (~>) ((~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                        c_a1bnX))) ((~>) a_a1bnV ((~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                                                          t_a1bnU c_a1bnX)))
data MapAccumRSym0 :: (~>) ((~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                        c_a1bnX))) ((~>) a_a1bnV ((~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                                                          t_a1bnU c_a1bnX)))
  where
    MapAccumRSym0KindInference :: SameKind (Apply MapAccumRSym0 arg_a1bwg) (MapAccumRSym1 arg_a1bwg) =>
                                  MapAccumRSym0 a6989586621679292405
type instance Apply @((~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                  c_a1bnX))) @((~>) a_a1bnV ((~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                                                      t_a1bnU c_a1bnX))) MapAccumRSym0 a6989586621679292405 = MapAccumRSym1 a6989586621679292405
instance SuppressUnusedWarnings MapAccumRSym0 where
  suppressUnusedWarnings = snd ((,) MapAccumRSym0KindInference ())
type MapAccumRSym1 :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                  c_a1bnX))
                      -> (~>) a_a1bnV ((~>) (t_a1bnU b_a1bnW) (a_a1bnV, t_a1bnU c_a1bnX))
data MapAccumRSym1 (a6989586621679292405 :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                        c_a1bnX))) :: (~>) a_a1bnV ((~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                                                                            t_a1bnU c_a1bnX))
  where
    MapAccumRSym1KindInference :: SameKind (Apply (MapAccumRSym1 a6989586621679292405) arg_a1bwg) (MapAccumRSym2 a6989586621679292405 arg_a1bwg) =>
                                  MapAccumRSym1 a6989586621679292405 a6989586621679292406
type instance Apply @a_a1bnV @((~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                        t_a1bnU c_a1bnX)) (MapAccumRSym1 a6989586621679292405) a6989586621679292406 = MapAccumRSym2 a6989586621679292405 a6989586621679292406
instance SuppressUnusedWarnings (MapAccumRSym1 a6989586621679292405) where
  suppressUnusedWarnings = snd ((,) MapAccumRSym1KindInference ())
type MapAccumRSym2 :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                  c_a1bnX))
                      -> a_a1bnV -> (~>) (t_a1bnU b_a1bnW) (a_a1bnV, t_a1bnU c_a1bnX)
data MapAccumRSym2 (a6989586621679292405 :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                        c_a1bnX))) (a6989586621679292406 :: a_a1bnV) :: (~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                                                                                                t_a1bnU c_a1bnX)
  where
    MapAccumRSym2KindInference :: SameKind (Apply (MapAccumRSym2 a6989586621679292405 a6989586621679292406) arg_a1bwg) (MapAccumRSym3 a6989586621679292405 a6989586621679292406 arg_a1bwg) =>
                                  MapAccumRSym2 a6989586621679292405 a6989586621679292406 a6989586621679292407
type instance Apply @(t_a1bnU b_a1bnW) @(a_a1bnV,
                                          t_a1bnU c_a1bnX) (MapAccumRSym2 a6989586621679292405 a6989586621679292406) a6989586621679292407 = MapAccumR a6989586621679292405 a6989586621679292406 a6989586621679292407
instance SuppressUnusedWarnings (MapAccumRSym2 a6989586621679292405 a6989586621679292406) where
  suppressUnusedWarnings = snd ((,) MapAccumRSym2KindInference ())
type MapAccumRSym3 :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                  c_a1bnX))
                      -> a_a1bnV -> t_a1bnU b_a1bnW -> (a_a1bnV, t_a1bnU c_a1bnX)
type family MapAccumRSym3 @a_a1bnV @b_a1bnW @c_a1bnX @t_a1bnU (a6989586621679292405 :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                                                                    c_a1bnX))) (a6989586621679292406 :: a_a1bnV) (a6989586621679292407 :: t_a1bnU b_a1bnW) :: (a_a1bnV,
                                                                                                                                                                                                              t_a1bnU c_a1bnX) where
  MapAccumRSym3 a6989586621679292405 a6989586621679292406 a6989586621679292407 = MapAccumR a6989586621679292405 a6989586621679292406 a6989586621679292407
type MapAccumLSym0 :: forall t_a1bnY
                              a_a1bnZ
                              b_a1bo0
                              c_a1bo1. (~>) ((~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                        c_a1bo1))) ((~>) a_a1bnZ ((~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                                                          t_a1bnY c_a1bo1)))
data MapAccumLSym0 :: (~>) ((~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                        c_a1bo1))) ((~>) a_a1bnZ ((~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                                          t_a1bnY c_a1bo1)))
  where
    MapAccumLSym0KindInference :: SameKind (Apply MapAccumLSym0 arg_a1bwq) (MapAccumLSym1 arg_a1bwq) =>
                                  MapAccumLSym0 a6989586621679292415
type instance Apply @((~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                  c_a1bo1))) @((~>) a_a1bnZ ((~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                                      t_a1bnY c_a1bo1))) MapAccumLSym0 a6989586621679292415 = MapAccumLSym1 a6989586621679292415
instance SuppressUnusedWarnings MapAccumLSym0 where
  suppressUnusedWarnings = snd ((,) MapAccumLSym0KindInference ())
type MapAccumLSym1 :: forall t_a1bnY
                              a_a1bnZ
                              b_a1bo0
                              c_a1bo1. (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ, c_a1bo1))
                                      -> (~>) a_a1bnZ ((~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                t_a1bnY c_a1bo1))
data MapAccumLSym1 (a6989586621679292415 :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                        c_a1bo1))) :: (~>) a_a1bnZ ((~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                                                            t_a1bnY c_a1bo1))
  where
    MapAccumLSym1KindInference :: SameKind (Apply (MapAccumLSym1 a6989586621679292415) arg_a1bwq) (MapAccumLSym2 a6989586621679292415 arg_a1bwq) =>
                                  MapAccumLSym1 a6989586621679292415 a6989586621679292416
type instance Apply @a_a1bnZ @((~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                        t_a1bnY c_a1bo1)) (MapAccumLSym1 a6989586621679292415) a6989586621679292416 = MapAccumLSym2 a6989586621679292415 a6989586621679292416
instance SuppressUnusedWarnings (MapAccumLSym1 a6989586621679292415) where
  suppressUnusedWarnings = snd ((,) MapAccumLSym1KindInference ())
type MapAccumLSym2 :: forall t_a1bnY
                              a_a1bnZ
                              b_a1bo0
                              c_a1bo1. (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ, c_a1bo1))
                                      -> a_a1bnZ
                                          -> (~>) (t_a1bnY b_a1bo0) (a_a1bnZ, t_a1bnY c_a1bo1)
data MapAccumLSym2 (a6989586621679292415 :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                        c_a1bo1))) (a6989586621679292416 :: a_a1bnZ) :: (~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                                                                                t_a1bnY c_a1bo1)
  where
    MapAccumLSym2KindInference :: SameKind (Apply (MapAccumLSym2 a6989586621679292415 a6989586621679292416) arg_a1bwq) (MapAccumLSym3 a6989586621679292415 a6989586621679292416 arg_a1bwq) =>
                                  MapAccumLSym2 a6989586621679292415 a6989586621679292416 a6989586621679292417
type instance Apply @(t_a1bnY b_a1bo0) @(a_a1bnZ,
                                          t_a1bnY c_a1bo1) (MapAccumLSym2 a6989586621679292415 a6989586621679292416) a6989586621679292417 = MapAccumL a6989586621679292415 a6989586621679292416 a6989586621679292417
instance SuppressUnusedWarnings (MapAccumLSym2 a6989586621679292415 a6989586621679292416) where
  suppressUnusedWarnings = snd ((,) MapAccumLSym2KindInference ())
type MapAccumLSym3 :: forall t_a1bnY
                              a_a1bnZ
                              b_a1bo0
                              c_a1bo1. (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ, c_a1bo1))
                                      -> a_a1bnZ
                                          -> t_a1bnY b_a1bo0 -> (a_a1bnZ, t_a1bnY c_a1bo1)
type family MapAccumLSym3 @t_a1bnY @a_a1bnZ @b_a1bo0 @c_a1bo1 (a6989586621679292415 :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                                                                    c_a1bo1))) (a6989586621679292416 :: a_a1bnZ) (a6989586621679292417 :: t_a1bnY b_a1bo0) :: (a_a1bnZ,
                                                                                                                                                                                                              t_a1bnY c_a1bo1) where
  MapAccumLSym3 a6989586621679292415 a6989586621679292416 a6989586621679292417 = MapAccumL a6989586621679292415 a6989586621679292416 a6989586621679292417
type ForMSym0 :: (~>) (t_a1bo2 a_a1bo4) ((~>) ((~>) a_a1bo4 (m_a1bo3 b_a1bo5)) (m_a1bo3 (t_a1bo2 b_a1bo5)))
data ForMSym0 :: (~>) (t_a1bo2 a_a1bo4) ((~>) ((~>) a_a1bo4 (m_a1bo3 b_a1bo5)) (m_a1bo3 (t_a1bo2 b_a1bo5)))
  where
    ForMSym0KindInference :: SameKind (Apply ForMSym0 arg_a1bwD) (ForMSym1 arg_a1bwD) =>
                              ForMSym0 a6989586621679292428
type instance Apply @(t_a1bo2 a_a1bo4) @((~>) ((~>) a_a1bo4 (m_a1bo3 b_a1bo5)) (m_a1bo3 (t_a1bo2 b_a1bo5))) ForMSym0 a6989586621679292428 = ForMSym1 a6989586621679292428
instance SuppressUnusedWarnings ForMSym0 where
  suppressUnusedWarnings = snd ((,) ForMSym0KindInference ())
type ForMSym1 :: t_a1bo2 a_a1bo4
                  -> (~>) ((~>) a_a1bo4 (m_a1bo3 b_a1bo5)) (m_a1bo3 (t_a1bo2 b_a1bo5))
data ForMSym1 (a6989586621679292428 :: t_a1bo2 a_a1bo4) :: (~>) ((~>) a_a1bo4 (m_a1bo3 b_a1bo5)) (m_a1bo3 (t_a1bo2 b_a1bo5))
  where
    ForMSym1KindInference :: SameKind (Apply (ForMSym1 a6989586621679292428) arg_a1bwD) (ForMSym2 a6989586621679292428 arg_a1bwD) =>
                              ForMSym1 a6989586621679292428 a6989586621679292429
type instance Apply @((~>) a_a1bo4 (m_a1bo3 b_a1bo5)) @(m_a1bo3 (t_a1bo2 b_a1bo5)) (ForMSym1 a6989586621679292428) a6989586621679292429 = ForM a6989586621679292428 a6989586621679292429
instance SuppressUnusedWarnings (ForMSym1 a6989586621679292428) where
  suppressUnusedWarnings = snd ((,) ForMSym1KindInference ())
type ForMSym2 :: t_a1bo2 a_a1bo4
                  -> (~>) a_a1bo4 (m_a1bo3 b_a1bo5) -> m_a1bo3 (t_a1bo2 b_a1bo5)
type family ForMSym2 @t_a1bo2 @a_a1bo4 @m_a1bo3 @b_a1bo5 (a6989586621679292428 :: t_a1bo2 a_a1bo4) (a6989586621679292429 :: (~>) a_a1bo4 (m_a1bo3 b_a1bo5)) :: m_a1bo3 (t_a1bo2 b_a1bo5) where
  ForMSym2 a6989586621679292428 a6989586621679292429 = ForM a6989586621679292428 a6989586621679292429
type ForSym0 :: (~>) (t_a1bo6 a_a1bo8) ((~>) ((~>) a_a1bo8 (f_a1bo7 b_a1bo9)) (f_a1bo7 (t_a1bo6 b_a1bo9)))
data ForSym0 :: (~>) (t_a1bo6 a_a1bo8) ((~>) ((~>) a_a1bo8 (f_a1bo7 b_a1bo9)) (f_a1bo7 (t_a1bo6 b_a1bo9)))
  where
    ForSym0KindInference :: SameKind (Apply ForSym0 arg_a1bwO) (ForSym1 arg_a1bwO) =>
                            ForSym0 a6989586621679292439
type instance Apply @(t_a1bo6 a_a1bo8) @((~>) ((~>) a_a1bo8 (f_a1bo7 b_a1bo9)) (f_a1bo7 (t_a1bo6 b_a1bo9))) ForSym0 a6989586621679292439 = ForSym1 a6989586621679292439
instance SuppressUnusedWarnings ForSym0 where
  suppressUnusedWarnings = snd ((,) ForSym0KindInference ())
type ForSym1 :: t_a1bo6 a_a1bo8
                -> (~>) ((~>) a_a1bo8 (f_a1bo7 b_a1bo9)) (f_a1bo7 (t_a1bo6 b_a1bo9))
data ForSym1 (a6989586621679292439 :: t_a1bo6 a_a1bo8) :: (~>) ((~>) a_a1bo8 (f_a1bo7 b_a1bo9)) (f_a1bo7 (t_a1bo6 b_a1bo9))
  where
    ForSym1KindInference :: SameKind (Apply (ForSym1 a6989586621679292439) arg_a1bwO) (ForSym2 a6989586621679292439 arg_a1bwO) =>
                            ForSym1 a6989586621679292439 a6989586621679292440
type instance Apply @((~>) a_a1bo8 (f_a1bo7 b_a1bo9)) @(f_a1bo7 (t_a1bo6 b_a1bo9)) (ForSym1 a6989586621679292439) a6989586621679292440 = For a6989586621679292439 a6989586621679292440
instance SuppressUnusedWarnings (ForSym1 a6989586621679292439) where
  suppressUnusedWarnings = snd ((,) ForSym1KindInference ())
type ForSym2 :: t_a1bo6 a_a1bo8
                -> (~>) a_a1bo8 (f_a1bo7 b_a1bo9) -> f_a1bo7 (t_a1bo6 b_a1bo9)
type family ForSym2 @t_a1bo6 @a_a1bo8 @f_a1bo7 @b_a1bo9 (a6989586621679292439 :: t_a1bo6 a_a1bo8) (a6989586621679292440 :: (~>) a_a1bo8 (f_a1bo7 b_a1bo9)) :: f_a1bo7 (t_a1bo6 b_a1bo9) where
  ForSym2 a6989586621679292439 a6989586621679292440 = For a6989586621679292439 a6989586621679292440
type FoldMapDefault :: forall t_a1bnO
                              m_a1bnP
                              a_a1bnQ. (~>) a_a1bnQ m_a1bnP -> t_a1bnO a_a1bnQ -> m_a1bnP
type family FoldMapDefault @t_a1bnO @m_a1bnP @a_a1bnQ (a_a1bvH :: (~>) a_a1bnQ m_a1bnP) (a_a1bvI :: t_a1bnO a_a1bnQ) :: m_a1bnP where
  FoldMapDefault @t_a1bnO @m_a1bnP @a_a1bnQ (f_a1bvM :: (~>) a_a1bnQ m_a1bnP) (x_a1bvN :: t_a1bnO a_a1bnQ) = Apply (LamCases_6989586621679292382Sym0 t_a1bnO m_a1bnP a_a1bnQ f_a1bvM x_a1bvN) (Apply (Apply TraverseSym0 (Apply (Apply (.@#@$) (Let6989586621679292376MkConstSym0 t_a1bnO m_a1bnP a_a1bnQ f_a1bvM x_a1bvN)) f_a1bvM)) x_a1bvN)
type FmapDefault :: forall t_a1bnR
                            a_a1bnS
                            b_a1bnT. (~>) a_a1bnS b_a1bnT -> t_a1bnR a_a1bnS -> t_a1bnR b_a1bnT
type family FmapDefault @t_a1bnR @a_a1bnS @b_a1bnT (a_a1bw0 :: (~>) a_a1bnS b_a1bnT) (a_a1bw1 :: t_a1bnR a_a1bnS) :: t_a1bnR b_a1bnT where
  FmapDefault @t_a1bnR @a_a1bnS @b_a1bnT (f_a1bw5 :: (~>) a_a1bnS b_a1bnT) (x_a1bw6 :: t_a1bnR a_a1bnS) = Apply (LamCases_6989586621679292395Sym0 t_a1bnR a_a1bnS b_a1bnT f_a1bw5 x_a1bw6) (Apply (Apply TraverseSym0 (Apply (Apply (.@#@$) IdentitySym0) f_a1bw5)) x_a1bw6)
type MapAccumR :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV, c_a1bnX))
                  -> a_a1bnV -> t_a1bnU b_a1bnW -> (a_a1bnV, t_a1bnU c_a1bnX)
type family MapAccumR @a_a1bnV @b_a1bnW @c_a1bnX @t_a1bnU (a_a1bwd :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                                                  c_a1bnX))) (a_a1bwe :: a_a1bnV) (a_a1bwf :: t_a1bnU b_a1bnW) :: (a_a1bnV,
                                                                                                                                                                    t_a1bnU c_a1bnX) where
  MapAccumR f_a1bwk s_a1bwl t_a1bwm = Apply (Apply RunStateRSym0 (Apply (Apply TraverseSym0 (Apply (Apply (.@#@$) StateRSym0) (Apply FlipSym0 f_a1bwk))) t_a1bwm)) s_a1bwl
type MapAccumL :: forall t_a1bnY
                          a_a1bnZ
                          b_a1bo0
                          c_a1bo1. (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ, c_a1bo1))
                                  -> a_a1bnZ -> t_a1bnY b_a1bo0 -> (a_a1bnZ, t_a1bnY c_a1bo1)
type family MapAccumL @t_a1bnY @a_a1bnZ @b_a1bo0 @c_a1bo1 (a_a1bwn :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                                                  c_a1bo1))) (a_a1bwo :: a_a1bnZ) (a_a1bwp :: t_a1bnY b_a1bo0) :: (a_a1bnZ,
                                                                                                                                                                    t_a1bnY c_a1bo1) where
  MapAccumL @t_a1bnY @a_a1bnZ @b_a1bo0 @c_a1bo1 (f_a1bwu :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                                        c_a1bo1))) (s_a1bwv :: a_a1bnZ) (t_a1bww :: t_a1bnY b_a1bo0) = Apply (Apply RunStateLSym0 (Apply (Apply TraverseSym0 (Apply (Apply (.@#@$) StateLSym0) (Apply FlipSym0 f_a1bwu))) t_a1bww)) s_a1bwv
type ForM :: t_a1bo2 a_a1bo4
              -> (~>) a_a1bo4 (m_a1bo3 b_a1bo5) -> m_a1bo3 (t_a1bo2 b_a1bo5)
type family ForM @t_a1bo2 @a_a1bo4 @m_a1bo3 @b_a1bo5 (a_a1bwB :: t_a1bo2 a_a1bo4) (a_a1bwC :: (~>) a_a1bo4 (m_a1bo3 b_a1bo5)) :: m_a1bo3 (t_a1bo2 b_a1bo5) where
  ForM a_6989586621679292421_a1bwG a_6989586621679292423_a1bwH = Apply (Apply (Apply FlipSym0 MapMSym0) a_6989586621679292421_a1bwG) a_6989586621679292423_a1bwH
type For :: t_a1bo6 a_a1bo8
            -> (~>) a_a1bo8 (f_a1bo7 b_a1bo9) -> f_a1bo7 (t_a1bo6 b_a1bo9)
type family For @t_a1bo6 @a_a1bo8 @f_a1bo7 @b_a1bo9 (a_a1bwM :: t_a1bo6 a_a1bo8) (a_a1bwN :: (~>) a_a1bo8 (f_a1bo7 b_a1bo9)) :: f_a1bo7 (t_a1bo6 b_a1bo9) where
  For a_6989586621679292432_a1bwR a_6989586621679292434_a1bwS = Apply (Apply (Apply FlipSym0 TraverseSym0) a_6989586621679292432_a1bwR) a_6989586621679292434_a1bwS
type Traverse_6989586621679292445 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> Maybe a_a19YV -> f_a19YU (Maybe b_a19YW)
type family Traverse_6989586621679292445 @a_a19YV @f_a19YU @b_a19YW (a_a1bwX :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bwY :: Maybe a_a19YV) :: f_a19YU (Maybe b_a19YW) where
  Traverse_6989586621679292445 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292247_a1bx2 'Nothing = Apply PureSym0 NothingSym0
  Traverse_6989586621679292445 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292247_a1bx3 ('Just a_6989586621679292249_a1bx4) = Apply (Apply FmapSym0 JustSym0) (Apply _f_6989586621679292247_a1bx3 a_6989586621679292249_a1bx4)
instance PTraversable Maybe where
  type Traverse a_a1bwT a_a1bwU = Traverse_6989586621679292445 a_a1bwT a_a1bwU
type Traverse_6989586621679292457 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> [a_a19YV] -> f_a19YU [b_a19YW]
type family Traverse_6989586621679292457 @a_a19YV @f_a19YU @b_a19YW (a_a1bx9 :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bxa :: [a_a19YV]) :: f_a19YU [b_a19YW] where
  Traverse_6989586621679292457 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292259_a1bxe '[] = Apply PureSym0 NilSym0
  Traverse_6989586621679292457 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292259_a1bxf ('(:) a_6989586621679292267_a1bxg a_6989586621679292269_a1bxh) = Apply (Apply (Apply LiftA2Sym0 (:@#@$)) (Apply _f_6989586621679292259_a1bxf a_6989586621679292267_a1bxg)) (Apply (Apply TraverseSym0 _f_6989586621679292259_a1bxf) a_6989586621679292269_a1bxh)
instance PTraversable [] where
  type Traverse a_a1bx5 a_a1bx6 = Traverse_6989586621679292457 a_a1bx5 a_a1bx6
type Traverse_6989586621679292470 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> NonEmpty a_a19YV
                                                        -> f_a19YU (NonEmpty b_a19YW)
type family Traverse_6989586621679292470 @a_a19YV @f_a19YU @b_a19YW (a_a1bxm :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bxn :: NonEmpty a_a19YV) :: f_a19YU (NonEmpty b_a19YW) where
  Traverse_6989586621679292470 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292278_a1bxr ('(:|) a_6989586621679292286_a1bxs a_6989586621679292288_a1bxt) = Apply (Apply (Apply LiftA2Sym0 (:|@#@$)) (Apply _f_6989586621679292278_a1bxr a_6989586621679292286_a1bxs)) (Apply (Apply TraverseSym0 _f_6989586621679292278_a1bxr) a_6989586621679292288_a1bxt)
instance PTraversable NonEmpty where
  type Traverse a_a1bxi a_a1bxj = Traverse_6989586621679292470 a_a1bxi a_a1bxj
type Traverse_6989586621679292482 :: forall a_a1bog
                                            a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> Either a_a1bog a_a19YV
                                                        -> f_a19YU (Either a_a1bog b_a19YW)
type family Traverse_6989586621679292482 @a_a1bog @a_a19YV @f_a19YU @b_a19YW (a_a1bxy :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bxz :: Either a_a1bog a_a19YV) :: f_a19YU (Either a_a1bog b_a19YW) where
  Traverse_6989586621679292482 @a_a1bog @a_a19YV @f_a19YU @b_a19YW (_f_6989586621679292294_a1bxD :: (~>) a_a19YV (f_a19YU b_a19YW)) ('Left a_6989586621679292296_a1bxE :: Either a_a1bog a_a19YV) = Apply (Apply FmapSym0 LeftSym0) (Apply PureSym0 a_6989586621679292296_a1bxE)
  Traverse_6989586621679292482 @a_a1bog @a_a19YV @f_a19YU @b_a19YW (_f_6989586621679292294_a1bxF :: (~>) a_a19YV (f_a19YU b_a19YW)) ('Right a_6989586621679292298_a1bxG :: Either a_a1bog a_a19YV) = Apply (Apply FmapSym0 RightSym0) (Apply _f_6989586621679292294_a1bxF a_6989586621679292298_a1bxG)
instance PTraversable (Either a_a1bog) where
  type Traverse a_a1bxu a_a1bxv = Traverse_6989586621679292482 a_a1bxu a_a1bxv
type Traverse_6989586621679292495 :: forall a_a1boh
                                            a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> (a_a1boh, a_a19YV)
                                                        -> f_a19YU (a_a1boh, b_a19YW)
type family Traverse_6989586621679292495 @a_a1boh @a_a19YV @f_a19YU @b_a19YW (a_a1bxL :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bxM :: (a_a1boh,
                                                                                                                                      a_a19YV)) :: f_a19YU (a_a1boh,
                                                                                                                                                            b_a19YW) where
  Traverse_6989586621679292495 @a_a1boh @a_a19YV @f_a19YU @b_a19YW (_f_6989586621679292302_a1bxQ :: (~>) a_a19YV (f_a19YU b_a19YW)) ('(a_6989586621679292304_a1bxR,
                                                                                                                                        a_6989586621679292306_a1bxS) :: (a_a1boh,
                                                                                                                                                                        a_a19YV)) = Apply (Apply (Apply LiftA2Sym0 Tuple2Sym0) (Apply PureSym0 a_6989586621679292304_a1bxR)) (Apply _f_6989586621679292302_a1bxQ a_6989586621679292306_a1bxS)
instance PTraversable ((,) a_a1boh) where
  type Traverse a_a1bxH a_a1bxI = Traverse_6989586621679292495 a_a1bxH a_a1bxI
type Traverse_6989586621679292507 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> Proxy a_a19YV -> f_a19YU (Proxy b_a19YW)
type family Traverse_6989586621679292507 @a_a19YV @f_a19YU @b_a19YW (a_a1bxX :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bxY :: Proxy a_a19YV) :: f_a19YU (Proxy b_a19YW) where
  Traverse_6989586621679292507 @a_a19YV @f_a19YU @b_a19YW _ _ = Apply PureSym0 ProxySym0
type SequenceA_6989586621679292515 :: forall f_a19YX
                                              a_a19YY. Proxy (f_a19YX a_a19YY)
                                                      -> f_a19YX (Proxy a_a19YY)
type family SequenceA_6989586621679292515 @f_a19YX @a_a19YY (a_a1by5 :: Proxy (f_a19YX a_a19YY)) :: f_a19YX (Proxy a_a19YY) where
  SequenceA_6989586621679292515 @f_a19YX @a_a19YY _ = Apply PureSym0 ProxySym0
type MapM_6989586621679292522 :: forall a_a19Z0
                                        m_a19YZ
                                        b_a19Z1. (~>) a_a19Z0 (m_a19YZ b_a19Z1)
                                                  -> Proxy a_a19Z0 -> m_a19YZ (Proxy b_a19Z1)
type family MapM_6989586621679292522 @a_a19Z0 @m_a19YZ @b_a19Z1 (a_a1byc :: (~>) a_a19Z0 (m_a19YZ b_a19Z1)) (a_a1byd :: Proxy a_a19Z0) :: m_a19YZ (Proxy b_a19Z1) where
  MapM_6989586621679292522 @a_a19Z0 @m_a19YZ @b_a19Z1 _ _ = Apply PureSym0 ProxySym0
type Sequence_6989586621679292530 :: forall m_a19Z2
                                            a_a19Z3. Proxy (m_a19Z2 a_a19Z3)
                                                      -> m_a19Z2 (Proxy a_a19Z3)
type family Sequence_6989586621679292530 @m_a19Z2 @a_a19Z3 (a_a1byk :: Proxy (m_a19Z2 a_a19Z3)) :: m_a19Z2 (Proxy a_a19Z3) where
  Sequence_6989586621679292530 @m_a19Z2 @a_a19Z3 _ = Apply PureSym0 ProxySym0
instance PTraversable Proxy where
  type Traverse a_a1bxT a_a1bxU = Traverse_6989586621679292507 a_a1bxT a_a1bxU
  type SequenceA a_a1by2 = SequenceA_6989586621679292515 a_a1by2
  type MapM a_a1by8 a_a1by9 = MapM_6989586621679292522 a_a1by8 a_a1by9
  type Sequence a_a1byh = Sequence_6989586621679292530 a_a1byh
type Traverse_6989586621679292537 :: forall m_a1boi
                                            a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> Const m_a1boi a_a19YV
                                                        -> f_a19YU (Const m_a1boi b_a19YW)
type family Traverse_6989586621679292537 @m_a1boi @a_a19YV @f_a19YU @b_a19YW (a_a1byr :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bys :: Const m_a1boi a_a19YV) :: f_a19YU (Const m_a1boi b_a19YW) where
  Traverse_6989586621679292537 @m_a1boi @a_a19YV @f_a19YU @b_a19YW (_f_6989586621679292311_a1byw :: (~>) a_a19YV (f_a19YU b_a19YW)) ('Const a_6989586621679292313_a1byx :: Const m_a1boi a_a19YV) = Apply (Apply FmapSym0 ConstSym0) (Apply PureSym0 a_6989586621679292313_a1byx)
instance PTraversable (Const m_a1boi) where
  type Traverse a_a1byn a_a1byo = Traverse_6989586621679292537 a_a1byn a_a1byo
type Traverse_6989586621679292548 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> Dual a_a19YV -> f_a19YU (Dual b_a19YW)
type family Traverse_6989586621679292548 @a_a19YV @f_a19YU @b_a19YW (a_a1byC :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1byD :: Dual a_a19YV) :: f_a19YU (Dual b_a19YW) where
  Traverse_6989586621679292548 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292316_a1byH ('Dual a_6989586621679292318_a1byI) = Apply (Apply FmapSym0 DualSym0) (Apply _f_6989586621679292316_a1byH a_6989586621679292318_a1byI)
instance PTraversable Dual where
  type Traverse a_a1byy a_a1byz = Traverse_6989586621679292548 a_a1byy a_a1byz
type Traverse_6989586621679292559 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> Sum a_a19YV -> f_a19YU (Sum b_a19YW)
type family Traverse_6989586621679292559 @a_a19YV @f_a19YU @b_a19YW (a_a1byN :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1byO :: Sum a_a19YV) :: f_a19YU (Sum b_a19YW) where
  Traverse_6989586621679292559 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292321_a1byS ('Sum a_6989586621679292323_a1byT) = Apply (Apply FmapSym0 SumSym0) (Apply _f_6989586621679292321_a1byS a_6989586621679292323_a1byT)
instance PTraversable Sum where
  type Traverse a_a1byJ a_a1byK = Traverse_6989586621679292559 a_a1byJ a_a1byK
type Traverse_6989586621679292570 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> Product a_a19YV
                                                        -> f_a19YU (Product b_a19YW)
type family Traverse_6989586621679292570 @a_a19YV @f_a19YU @b_a19YW (a_a1byY :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1byZ :: Product a_a19YV) :: f_a19YU (Product b_a19YW) where
  Traverse_6989586621679292570 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292326_a1bz3 ('Product a_6989586621679292328_a1bz4) = Apply (Apply FmapSym0 ProductSym0) (Apply _f_6989586621679292326_a1bz3 a_6989586621679292328_a1bz4)
instance PTraversable Product where
  type Traverse a_a1byU a_a1byV = Traverse_6989586621679292570 a_a1byU a_a1byV
type Traverse_6989586621679292581 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> First a_a19YV -> f_a19YU (First b_a19YW)
type family Traverse_6989586621679292581 @a_a19YV @f_a19YU @b_a19YW (a_a1bz9 :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bza :: First a_a19YV) :: f_a19YU (First b_a19YW) where
  Traverse_6989586621679292581 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292337_a1bze ('First a_6989586621679292345_a1bzf) = Apply (Apply FmapSym0 FirstSym0) (Apply (Apply TraverseSym0 _f_6989586621679292337_a1bze) a_6989586621679292345_a1bzf)
instance PTraversable First where
  type Traverse a_a1bz5 a_a1bz6 = Traverse_6989586621679292581 a_a1bz5 a_a1bz6
type Traverse_6989586621679292592 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> Last a_a19YV -> f_a19YU (Last b_a19YW)
type family Traverse_6989586621679292592 @a_a19YV @f_a19YU @b_a19YW (a_a1bzk :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bzl :: Last a_a19YV) :: f_a19YU (Last b_a19YW) where
  Traverse_6989586621679292592 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292354_a1bzp ('Last a_6989586621679292362_a1bzq) = Apply (Apply FmapSym0 LastSym0) (Apply (Apply TraverseSym0 _f_6989586621679292354_a1bzp) a_6989586621679292362_a1bzq)
instance PTraversable Last where
  type Traverse a_a1bzg a_a1bzh = Traverse_6989586621679292592 a_a1bzg a_a1bzh
type Traverse_6989586621679292603 :: forall a_a19YV
                                            f_a19YU
                                            b_a19YW. (~>) a_a19YV (f_a19YU b_a19YW)
                                                      -> Identity a_a19YV
                                                        -> f_a19YU (Identity b_a19YW)
type family Traverse_6989586621679292603 @a_a19YV @f_a19YU @b_a19YW (a_a1bzv :: (~>) a_a19YV (f_a19YU b_a19YW)) (a_a1bzw :: Identity a_a19YV) :: f_a19YU (Identity b_a19YW) where
  Traverse_6989586621679292603 @a_a19YV @f_a19YU @b_a19YW _f_6989586621679292365_a1bzA ('Identity a_6989586621679292367_a1bzB) = Apply (Apply FmapSym0 IdentitySym0) (Apply _f_6989586621679292365_a1bzA a_6989586621679292367_a1bzB)
instance PTraversable Identity where
  type Traverse a_a1bzr a_a1bzs = Traverse_6989586621679292603 a_a1bzr a_a1bzs
type family LamCases_6989586621679292659_a1bAo s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 a_6989586621679292662_a1bAr where
  LamCases_6989586621679292659_a1bAo s_a1boj s_a1bAe f_a1bAa k_a1bAb '(_,
                                                                  y_6989586621679292656_a1bAp) = y_6989586621679292656_a1bAp
data LamCases_6989586621679292659Sym0 s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 a_69895866216792926626989586621679292663
  where
    LamCases_6989586621679292659Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292659Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647) arg_a1bAs) (LamCases_6989586621679292659Sym1 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 arg_a1bAs) =>
                                                      LamCases_6989586621679292659Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 a_69895866216792926626989586621679292663
type instance Apply @_ @_ (LamCases_6989586621679292659Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647) a_69895866216792926626989586621679292663 = LamCases_6989586621679292659_a1bAo s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 a_69895866216792926626989586621679292663
instance SuppressUnusedWarnings (LamCases_6989586621679292659Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292659Sym0KindInference ())
type family LamCases_6989586621679292659Sym1 s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 a_69895866216792926626989586621679292663 where
  LamCases_6989586621679292659Sym1 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 a_69895866216792926626989586621679292663 = LamCases_6989586621679292659_a1bAo s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 a_69895866216792926626989586621679292663
type family LamCases_6989586621679292666_a1bAv s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 a_6989586621679292669_a1bAy where
  LamCases_6989586621679292666_a1bAv s_a1boj s_a1bAe f_a1bAa k_a1bAb '(y_6989586621679292654_a1bAw,
                                                                  _) = y_6989586621679292654_a1bAw
data LamCases_6989586621679292666Sym0 s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 a_69895866216792926696989586621679292670
  where
    LamCases_6989586621679292666Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292666Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647) arg_a1bAz) (LamCases_6989586621679292666Sym1 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 arg_a1bAz) =>
                                                      LamCases_6989586621679292666Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 a_69895866216792926696989586621679292670
type instance Apply @_ @_ (LamCases_6989586621679292666Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647) a_69895866216792926696989586621679292670 = LamCases_6989586621679292666_a1bAv s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 a_69895866216792926696989586621679292670
instance SuppressUnusedWarnings (LamCases_6989586621679292666Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292666Sym0KindInference ())
type family LamCases_6989586621679292666Sym1 s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 a_69895866216792926696989586621679292670 where
  LamCases_6989586621679292666Sym1 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 a_69895866216792926696989586621679292670 = LamCases_6989586621679292666_a1bAv s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 a_69895866216792926696989586621679292670
type family Let6989586621679292651VSym0 s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 where
  Let6989586621679292651VSym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 = Let6989586621679292651V s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647
type family Let6989586621679292651S'Sym0 s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 where
  Let6989586621679292651S'Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 = Let6989586621679292651S' s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647
type family Let6989586621679292651X_6989586621679292652Sym0 s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 where
  Let6989586621679292651X_6989586621679292652Sym0 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647 = Let6989586621679292651X_6989586621679292652 s6989586621679291911 s6989586621679292650 f6989586621679292646 k6989586621679292647
type family Let6989586621679292651V s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 where
  Let6989586621679292651V s_a1boj s_a1bAe f_a1bAa k_a1bAb = Apply (LamCases_6989586621679292659Sym0 s_a1boj s_a1bAe f_a1bAa k_a1bAb) (Let6989586621679292651X_6989586621679292652Sym0 s_a1boj s_a1bAe f_a1bAa k_a1bAb)
type family Let6989586621679292651S' s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 where
  Let6989586621679292651S' s_a1boj s_a1bAe f_a1bAa k_a1bAb = Apply (LamCases_6989586621679292666Sym0 s_a1boj s_a1bAe f_a1bAa k_a1bAb) (Let6989586621679292651X_6989586621679292652Sym0 s_a1boj s_a1bAe f_a1bAa k_a1bAb)
type family Let6989586621679292651X_6989586621679292652 s6989586621679291911 s6989586621679292650 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 where
  Let6989586621679292651X_6989586621679292652 s_a1boj s_a1bAe f_a1bAa k_a1bAb = Apply k_a1bAb s_a1bAe
type family LamCases_6989586621679292648_a1bAd s6989586621679291911 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 a_6989586621679292673_a1bAC where
  LamCases_6989586621679292648_a1bAd s_a1boj f_a1bAa k_a1bAb s_a1bAe = Apply (Apply Tuple2Sym0 (Let6989586621679292651S'Sym0 s_a1boj s_a1bAe f_a1bAa k_a1bAb)) (Apply f_a1bAa (Let6989586621679292651VSym0 s_a1boj s_a1bAe f_a1bAa k_a1bAb))
data LamCases_6989586621679292648Sym0 s6989586621679291911 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 a_69895866216792926736989586621679292674
  where
    LamCases_6989586621679292648Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292648Sym0 s6989586621679291911 f6989586621679292646 k6989586621679292647) arg_a1bAD) (LamCases_6989586621679292648Sym1 s6989586621679291911 f6989586621679292646 k6989586621679292647 arg_a1bAD) =>
                                                      LamCases_6989586621679292648Sym0 s6989586621679291911 f6989586621679292646 k6989586621679292647 a_69895866216792926736989586621679292674
type instance Apply @_ @_ (LamCases_6989586621679292648Sym0 s6989586621679291911 f6989586621679292646 k6989586621679292647) a_69895866216792926736989586621679292674 = LamCases_6989586621679292648_a1bAd s6989586621679291911 f6989586621679292646 k6989586621679292647 a_69895866216792926736989586621679292674
instance SuppressUnusedWarnings (LamCases_6989586621679292648Sym0 s6989586621679291911 f6989586621679292646 k6989586621679292647) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292648Sym0KindInference ())
type family LamCases_6989586621679292648Sym1 s6989586621679291911 (f6989586621679292646 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292647 a_69895866216792926736989586621679292674 where
  LamCases_6989586621679292648Sym1 s6989586621679291911 f6989586621679292646 k6989586621679292647 a_69895866216792926736989586621679292674 = LamCases_6989586621679292648_a1bAd s6989586621679291911 f6989586621679292646 k6989586621679292647 a_69895866216792926736989586621679292674
type Fmap_6989586621679292639 :: forall s_a1boj
                                        a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> StateL s_a1boj a_iYSL
                                                    -> StateL s_a1boj b_iYSM
type family Fmap_6989586621679292639 @s_a1boj @a_iYSL @b_iYSM (a_a1bA5 :: (~>) a_iYSL b_iYSM) (a_a1bA6 :: StateL s_a1boj a_iYSL) :: StateL s_a1boj b_iYSM where
  Fmap_6989586621679292639 @s_a1boj @a_iYSL @b_iYSM (f_a1bAa :: (~>) a_iYSL b_iYSM) ('StateL k_a1bAb :: StateL s_a1boj a_iYSL) = Apply (Apply ($@#@$) StateLSym0) (LamCases_6989586621679292648Sym0 s_a1boj f_a1bAa k_a1bAb)
instance PFunctor (StateL s_a1boj) where
  type Fmap a_a1bA1 a_a1bA2 = Fmap_6989586621679292639 a_a1bA1 a_a1bA2
type family LamCases_6989586621679292725_a1bBs s6989586621679291917 (x6989586621679292724 :: a7566047373982553024) a_6989586621679292728_a1bBv where
  LamCases_6989586621679292725_a1bBs s_a1bop x_a1bBq s_a1bBt = Apply (Apply Tuple2Sym0 s_a1bBt) x_a1bBq
data LamCases_6989586621679292725Sym0 s6989586621679291917 (x6989586621679292724 :: a7566047373982553024) a_69895866216792927286989586621679292729
  where
    LamCases_6989586621679292725Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292725Sym0 s6989586621679291917 x6989586621679292724) arg_a1bBw) (LamCases_6989586621679292725Sym1 s6989586621679291917 x6989586621679292724 arg_a1bBw) =>
                                                      LamCases_6989586621679292725Sym0 s6989586621679291917 x6989586621679292724 a_69895866216792927286989586621679292729
type instance Apply @_ @_ (LamCases_6989586621679292725Sym0 s6989586621679291917 x6989586621679292724) a_69895866216792927286989586621679292729 = LamCases_6989586621679292725_a1bBs s6989586621679291917 x6989586621679292724 a_69895866216792927286989586621679292729
instance SuppressUnusedWarnings (LamCases_6989586621679292725Sym0 s6989586621679291917 x6989586621679292724) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292725Sym0KindInference ())
type family LamCases_6989586621679292725Sym1 s6989586621679291917 (x6989586621679292724 :: a7566047373982553024) a_69895866216792927286989586621679292729 where
  LamCases_6989586621679292725Sym1 s6989586621679291917 x6989586621679292724 a_69895866216792927286989586621679292729 = LamCases_6989586621679292725_a1bBs s6989586621679291917 x6989586621679292724 a_69895866216792927286989586621679292729
type Pure_6989586621679292719 :: forall s_a1bop a_iv9m. a_iv9m
                                                        -> StateL s_a1bop a_iv9m
type family Pure_6989586621679292719 @s_a1bop @a_iv9m (a_a1bBn :: a_iv9m) :: StateL s_a1bop a_iv9m where
  Pure_6989586621679292719 @s_a1bop @a_iv9m (x_a1bBq :: a_iv9m) = Apply StateLSym0 (LamCases_6989586621679292725Sym0 s_a1bop x_a1bBq)
type family LamCases_6989586621679292759_a1bC0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_6989586621679292762_a1bC3 where
  LamCases_6989586621679292759_a1bC0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH '(_,
                                                                    y_6989586621679292756_a1bC1) = y_6989586621679292756_a1bC1
data LamCases_6989586621679292759Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927626989586621679292763
  where
    LamCases_6989586621679292759Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292759Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) arg_a1bC4) (LamCases_6989586621679292759Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 arg_a1bC4) =>
                                                      LamCases_6989586621679292759Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927626989586621679292763
type instance Apply @_ @_ (LamCases_6989586621679292759Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) a_69895866216792927626989586621679292763 = LamCases_6989586621679292759_a1bC0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927626989586621679292763
instance SuppressUnusedWarnings (LamCases_6989586621679292759Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292759Sym0KindInference ())
type family LamCases_6989586621679292759Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927626989586621679292763 where
  LamCases_6989586621679292759Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927626989586621679292763 = LamCases_6989586621679292759_a1bC0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927626989586621679292763
type family LamCases_6989586621679292766_a1bC7 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_6989586621679292769_a1bCa where
  LamCases_6989586621679292766_a1bC7 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH '(y_6989586621679292754_a1bC8,
                                                                    _) = y_6989586621679292754_a1bC8
data LamCases_6989586621679292766Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927696989586621679292770
  where
    LamCases_6989586621679292766Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292766Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) arg_a1bCb) (LamCases_6989586621679292766Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 arg_a1bCb) =>
                                                      LamCases_6989586621679292766Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927696989586621679292770
type instance Apply @_ @_ (LamCases_6989586621679292766Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) a_69895866216792927696989586621679292770 = LamCases_6989586621679292766_a1bC7 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927696989586621679292770
instance SuppressUnusedWarnings (LamCases_6989586621679292766Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292766Sym0KindInference ())
type family LamCases_6989586621679292766Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927696989586621679292770 where
  LamCases_6989586621679292766Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927696989586621679292770 = LamCases_6989586621679292766_a1bC7 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927696989586621679292770
type family LamCases_6989586621679292774_a1bCf s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_6989586621679292777_a1bCi where
  LamCases_6989586621679292774_a1bCf s_a1bop s_a1bBK kf_a1bBG kv_a1bBH '(_,
                                                                    y_6989586621679292750_a1bCg) = y_6989586621679292750_a1bCg
data LamCases_6989586621679292774Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927776989586621679292778
  where
    LamCases_6989586621679292774Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292774Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) arg_a1bCj) (LamCases_6989586621679292774Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 arg_a1bCj) =>
                                                      LamCases_6989586621679292774Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927776989586621679292778
type instance Apply @_ @_ (LamCases_6989586621679292774Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) a_69895866216792927776989586621679292778 = LamCases_6989586621679292774_a1bCf s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927776989586621679292778
instance SuppressUnusedWarnings (LamCases_6989586621679292774Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292774Sym0KindInference ())
type family LamCases_6989586621679292774Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927776989586621679292778 where
  LamCases_6989586621679292774Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927776989586621679292778 = LamCases_6989586621679292774_a1bCf s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927776989586621679292778
type family LamCases_6989586621679292781_a1bCm s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_6989586621679292784_a1bCp where
  LamCases_6989586621679292781_a1bCm s_a1bop s_a1bBK kf_a1bBG kv_a1bBH '(y_6989586621679292748_a1bCn,
                                                                    _) = y_6989586621679292748_a1bCn
data LamCases_6989586621679292781Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927846989586621679292785
  where
    LamCases_6989586621679292781Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292781Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) arg_a1bCq) (LamCases_6989586621679292781Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 arg_a1bCq) =>
                                                      LamCases_6989586621679292781Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927846989586621679292785
type instance Apply @_ @_ (LamCases_6989586621679292781Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) a_69895866216792927846989586621679292785 = LamCases_6989586621679292781_a1bCm s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927846989586621679292785
instance SuppressUnusedWarnings (LamCases_6989586621679292781Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292781Sym0KindInference ())
type family LamCases_6989586621679292781Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927846989586621679292785 where
  LamCases_6989586621679292781Sym1 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927846989586621679292785 = LamCases_6989586621679292781_a1bCm s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 a_69895866216792927846989586621679292785
type family Let6989586621679292745VSym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745VSym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 = Let6989586621679292745V s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741
type family Let6989586621679292745S''Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745S''Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 = Let6989586621679292745S'' s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741
type family Let6989586621679292745X_6989586621679292752Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745X_6989586621679292752Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 = Let6989586621679292745X_6989586621679292752 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741
type family Let6989586621679292745FSym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745FSym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 = Let6989586621679292745F s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741
type family Let6989586621679292745S'Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745S'Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 = Let6989586621679292745S' s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741
type family Let6989586621679292745X_6989586621679292746Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745X_6989586621679292746Sym0 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 = Let6989586621679292745X_6989586621679292746 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741
type family Let6989586621679292745V s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745V s_a1bop s_a1bBK kf_a1bBG kv_a1bBH = Apply (LamCases_6989586621679292759Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH) (Let6989586621679292745X_6989586621679292752Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
type family Let6989586621679292745S'' s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745S'' s_a1bop s_a1bBK kf_a1bBG kv_a1bBH = Apply (LamCases_6989586621679292766Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH) (Let6989586621679292745X_6989586621679292752Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
type family Let6989586621679292745X_6989586621679292752 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745X_6989586621679292752 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH = Apply kv_a1bBH (Let6989586621679292745S'Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
type family Let6989586621679292745F s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745F s_a1bop s_a1bBK kf_a1bBG kv_a1bBH = Apply (LamCases_6989586621679292774Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH) (Let6989586621679292745X_6989586621679292746Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
type family Let6989586621679292745S' s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745S' s_a1bop s_a1bBK kf_a1bBG kv_a1bBH = Apply (LamCases_6989586621679292781Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH) (Let6989586621679292745X_6989586621679292746Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
type family Let6989586621679292745X_6989586621679292746 s6989586621679291917 s6989586621679292744 kf6989586621679292740 kv6989586621679292741 where
  Let6989586621679292745X_6989586621679292746 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH = Apply kf_a1bBG s_a1bBK
type family LamCases_6989586621679292742_a1bBJ s6989586621679291917 kf6989586621679292740 kv6989586621679292741 a_6989586621679292788_a1bCt where
  LamCases_6989586621679292742_a1bBJ s_a1bop kf_a1bBG kv_a1bBH s_a1bBK = Apply (Apply Tuple2Sym0 (Let6989586621679292745S''Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)) (Apply (Let6989586621679292745FSym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH) (Let6989586621679292745VSym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH))
data LamCases_6989586621679292742Sym0 s6989586621679291917 kf6989586621679292740 kv6989586621679292741 a_69895866216792927886989586621679292789
  where
    LamCases_6989586621679292742Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292742Sym0 s6989586621679291917 kf6989586621679292740 kv6989586621679292741) arg_a1bCu) (LamCases_6989586621679292742Sym1 s6989586621679291917 kf6989586621679292740 kv6989586621679292741 arg_a1bCu) =>
                                                      LamCases_6989586621679292742Sym0 s6989586621679291917 kf6989586621679292740 kv6989586621679292741 a_69895866216792927886989586621679292789
type instance Apply @_ @_ (LamCases_6989586621679292742Sym0 s6989586621679291917 kf6989586621679292740 kv6989586621679292741) a_69895866216792927886989586621679292789 = LamCases_6989586621679292742_a1bBJ s6989586621679291917 kf6989586621679292740 kv6989586621679292741 a_69895866216792927886989586621679292789
instance SuppressUnusedWarnings (LamCases_6989586621679292742Sym0 s6989586621679291917 kf6989586621679292740 kv6989586621679292741) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292742Sym0KindInference ())
type family LamCases_6989586621679292742Sym1 s6989586621679291917 kf6989586621679292740 kv6989586621679292741 a_69895866216792927886989586621679292789 where
  LamCases_6989586621679292742Sym1 s6989586621679291917 kf6989586621679292740 kv6989586621679292741 a_69895866216792927886989586621679292789 = LamCases_6989586621679292742_a1bBJ s6989586621679291917 kf6989586621679292740 kv6989586621679292741 a_69895866216792927886989586621679292789
type TFHelper_6989586621679292733 :: forall s_a1bop
                                            a_iv9o
                                            b_iv9p. StateL s_a1bop ((~>) a_iv9o b_iv9p)
                                                    -> StateL s_a1bop a_iv9o
                                                        -> StateL s_a1bop b_iv9p
type family TFHelper_6989586621679292733 @s_a1bop @a_iv9o @b_iv9p (a_a1bBB :: StateL s_a1bop ((~>) a_iv9o b_iv9p)) (a_a1bBC :: StateL s_a1bop a_iv9o) :: StateL s_a1bop b_iv9p where
  TFHelper_6989586621679292733 @s_a1bop @a_iv9o @b_iv9p ('StateL kf_a1bBG :: StateL s_a1bop ((~>) a_iv9o b_iv9p)) ('StateL kv_a1bBH :: StateL s_a1bop a_iv9o) = Apply (Apply ($@#@$) StateLSym0) (LamCases_6989586621679292742Sym0 s_a1bop kf_a1bBG kv_a1bBH)
type family LamCases_6989586621679292823_a1bD2 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_6989586621679292826_a1bD5 where
  LamCases_6989586621679292823_a1bD2 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ '(_,
                                                                            y_6989586621679292820_a1bD3) = y_6989586621679292820_a1bD3
data LamCases_6989586621679292823Sym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928266989586621679292827
  where
    LamCases_6989586621679292823Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292823Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) arg_a1bD6) (LamCases_6989586621679292823Sym1 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 arg_a1bD6) =>
                                                      LamCases_6989586621679292823Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928266989586621679292827
type instance Apply @_ @_ (LamCases_6989586621679292823Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) a_69895866216792928266989586621679292827 = LamCases_6989586621679292823_a1bD2 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928266989586621679292827
instance SuppressUnusedWarnings (LamCases_6989586621679292823Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292823Sym0KindInference ())
type family LamCases_6989586621679292823Sym1 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928266989586621679292827 where
  LamCases_6989586621679292823Sym1 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928266989586621679292827 = LamCases_6989586621679292823_a1bD2 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928266989586621679292827
type family LamCases_6989586621679292830_a1bD9 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_6989586621679292833_a1bDc where
  LamCases_6989586621679292830_a1bD9 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ '(y_6989586621679292818_a1bDa,
                                                                            _) = y_6989586621679292818_a1bDa
data LamCases_6989586621679292830Sym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928336989586621679292834
  where
    LamCases_6989586621679292830Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292830Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) arg_a1bDd) (LamCases_6989586621679292830Sym1 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 arg_a1bDd) =>
                                                      LamCases_6989586621679292830Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928336989586621679292834
type instance Apply @_ @_ (LamCases_6989586621679292830Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) a_69895866216792928336989586621679292834 = LamCases_6989586621679292830_a1bD9 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928336989586621679292834
instance SuppressUnusedWarnings (LamCases_6989586621679292830Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292830Sym0KindInference ())
type family LamCases_6989586621679292830Sym1 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928336989586621679292834 where
  LamCases_6989586621679292830Sym1 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928336989586621679292834 = LamCases_6989586621679292830_a1bD9 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928336989586621679292834
type family LamCases_6989586621679292838_a1bDh s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_6989586621679292841_a1bDk where
  LamCases_6989586621679292838_a1bDh s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ '(_,
                                                                            y_6989586621679292814_a1bDi) = y_6989586621679292814_a1bDi
data LamCases_6989586621679292838Sym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928416989586621679292842
  where
    LamCases_6989586621679292838Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292838Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) arg_a1bDl) (LamCases_6989586621679292838Sym1 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 arg_a1bDl) =>
                                                      LamCases_6989586621679292838Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928416989586621679292842
type instance Apply @_ @_ (LamCases_6989586621679292838Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) a_69895866216792928416989586621679292842 = LamCases_6989586621679292838_a1bDh s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928416989586621679292842
instance SuppressUnusedWarnings (LamCases_6989586621679292838Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292838Sym0KindInference ())
type family LamCases_6989586621679292838Sym1 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928416989586621679292842 where
  LamCases_6989586621679292838Sym1 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928416989586621679292842 = LamCases_6989586621679292838_a1bDh s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928416989586621679292842
type family LamCases_6989586621679292845_a1bDo s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_6989586621679292848_a1bDr where
  LamCases_6989586621679292845_a1bDo s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ '(y_6989586621679292812_a1bDp,
                                                                            _) = y_6989586621679292812_a1bDp
data LamCases_6989586621679292845Sym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928486989586621679292849
  where
    LamCases_6989586621679292845Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292845Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) arg_a1bDs) (LamCases_6989586621679292845Sym1 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 arg_a1bDs) =>
                                                      LamCases_6989586621679292845Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928486989586621679292849
type instance Apply @_ @_ (LamCases_6989586621679292845Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) a_69895866216792928486989586621679292849 = LamCases_6989586621679292845_a1bDo s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928486989586621679292849
instance SuppressUnusedWarnings (LamCases_6989586621679292845Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292845Sym0KindInference ())
type family LamCases_6989586621679292845Sym1 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928486989586621679292849 where
  LamCases_6989586621679292845Sym1 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928486989586621679292849 = LamCases_6989586621679292845_a1bDo s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928486989586621679292849
type family Let6989586621679292809YSym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809YSym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 = Let6989586621679292809Y s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805
type family Let6989586621679292809S''Sym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809S''Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 = Let6989586621679292809S'' s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805
type family Let6989586621679292809X_6989586621679292816Sym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809X_6989586621679292816Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 = Let6989586621679292809X_6989586621679292816 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805
type family Let6989586621679292809XSym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809XSym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 = Let6989586621679292809X s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805
type family Let6989586621679292809S'Sym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809S'Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 = Let6989586621679292809S' s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805
type family Let6989586621679292809X_6989586621679292810Sym0 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809X_6989586621679292810Sym0 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 = Let6989586621679292809X_6989586621679292810 s6989586621679291917 s6989586621679292808 f6989586621679292803 kx6989586621679292804 ky6989586621679292805
type family Let6989586621679292809Y s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809Y s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ = Apply (LamCases_6989586621679292823Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ) (Let6989586621679292809X_6989586621679292816Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
type family Let6989586621679292809S'' s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809S'' s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ = Apply (LamCases_6989586621679292830Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ) (Let6989586621679292809X_6989586621679292816Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
type family Let6989586621679292809X_6989586621679292816 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809X_6989586621679292816 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ = Apply ky_a1bCJ (Let6989586621679292809S'Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
type family Let6989586621679292809X s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809X s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ = Apply (LamCases_6989586621679292838Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ) (Let6989586621679292809X_6989586621679292810Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
type family Let6989586621679292809S' s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809S' s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ = Apply (LamCases_6989586621679292845Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ) (Let6989586621679292809X_6989586621679292810Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
type family Let6989586621679292809X_6989586621679292810 s6989586621679291917 s6989586621679292808 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 where
  Let6989586621679292809X_6989586621679292810 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ = Apply kx_a1bCI s_a1bCM
type family LamCases_6989586621679292806_a1bCL s6989586621679291917 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_6989586621679292852_a1bDv where
  LamCases_6989586621679292806_a1bCL s_a1bop f_a1bCH kx_a1bCI ky_a1bCJ s_a1bCM = Apply (Apply Tuple2Sym0 (Let6989586621679292809S''Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)) (Apply (Apply f_a1bCH (Let6989586621679292809XSym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)) (Let6989586621679292809YSym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ))
data LamCases_6989586621679292806Sym0 s6989586621679291917 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928526989586621679292853
  where
    LamCases_6989586621679292806Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292806Sym0 s6989586621679291917 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) arg_a1bDw) (LamCases_6989586621679292806Sym1 s6989586621679291917 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 arg_a1bDw) =>
                                                      LamCases_6989586621679292806Sym0 s6989586621679291917 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928526989586621679292853
type instance Apply @_ @_ (LamCases_6989586621679292806Sym0 s6989586621679291917 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) a_69895866216792928526989586621679292853 = LamCases_6989586621679292806_a1bCL s6989586621679291917 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928526989586621679292853
instance SuppressUnusedWarnings (LamCases_6989586621679292806Sym0 s6989586621679291917 f6989586621679292803 kx6989586621679292804 ky6989586621679292805) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292806Sym0KindInference ())
type family LamCases_6989586621679292806Sym1 s6989586621679291917 (f6989586621679292803 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292804 ky6989586621679292805 a_69895866216792928526989586621679292853 where
  LamCases_6989586621679292806Sym1 s6989586621679291917 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928526989586621679292853 = LamCases_6989586621679292806_a1bCL s6989586621679291917 f6989586621679292803 kx6989586621679292804 ky6989586621679292805 a_69895866216792928526989586621679292853
type LiftA2_6989586621679292794 :: forall s_a1bop
                                          a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> StateL s_a1bop a_iv9s
                                                      -> StateL s_a1bop b_iv9t
                                                        -> StateL s_a1bop c_iv9u
type family LiftA2_6989586621679292794 @s_a1bop @a_iv9s @b_iv9t @c_iv9u (a_a1bCA :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a1bCB :: StateL s_a1bop a_iv9s) (a_a1bCC :: StateL s_a1bop b_iv9t) :: StateL s_a1bop c_iv9u where
  LiftA2_6989586621679292794 @s_a1bop @a_iv9s @b_iv9t @c_iv9u (f_a1bCH :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) ('StateL kx_a1bCI :: StateL s_a1bop a_iv9s) ('StateL ky_a1bCJ :: StateL s_a1bop b_iv9t) = Apply (Apply ($@#@$) StateLSym0) (LamCases_6989586621679292806Sym0 s_a1bop f_a1bCH kx_a1bCI ky_a1bCJ)
instance PApplicative (StateL s_a1bop) where
  type Pure a_a1bBk = Pure_6989586621679292719 a_a1bBk
  type (<*>) a_a1bBx a_a1bBy = TFHelper_6989586621679292733 a_a1bBx a_a1bBy
  type LiftA2 a_a1bCv a_a1bCw a_a1bCx = LiftA2_6989586621679292794 a_a1bCv a_a1bCw a_a1bCx
type family LamCases_6989586621679292877_a1bDU s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 a_6989586621679292880_a1bDX where
  LamCases_6989586621679292877_a1bDU s_a1boH s_a1bDK f_a1bDG k_a1bDH '(_,
                                                                  y_6989586621679292874_a1bDV) = y_6989586621679292874_a1bDV
data LamCases_6989586621679292877Sym0 s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 a_69895866216792928806989586621679292881
  where
    LamCases_6989586621679292877Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292877Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865) arg_a1bDY) (LamCases_6989586621679292877Sym1 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 arg_a1bDY) =>
                                                      LamCases_6989586621679292877Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 a_69895866216792928806989586621679292881
type instance Apply @_ @_ (LamCases_6989586621679292877Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865) a_69895866216792928806989586621679292881 = LamCases_6989586621679292877_a1bDU s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 a_69895866216792928806989586621679292881
instance SuppressUnusedWarnings (LamCases_6989586621679292877Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292877Sym0KindInference ())
type family LamCases_6989586621679292877Sym1 s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 a_69895866216792928806989586621679292881 where
  LamCases_6989586621679292877Sym1 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 a_69895866216792928806989586621679292881 = LamCases_6989586621679292877_a1bDU s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 a_69895866216792928806989586621679292881
type family LamCases_6989586621679292884_a1bE1 s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 a_6989586621679292887_a1bE4 where
  LamCases_6989586621679292884_a1bE1 s_a1boH s_a1bDK f_a1bDG k_a1bDH '(y_6989586621679292872_a1bE2,
                                                                  _) = y_6989586621679292872_a1bE2
data LamCases_6989586621679292884Sym0 s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 a_69895866216792928876989586621679292888
  where
    LamCases_6989586621679292884Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292884Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865) arg_a1bE5) (LamCases_6989586621679292884Sym1 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 arg_a1bE5) =>
                                                      LamCases_6989586621679292884Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 a_69895866216792928876989586621679292888
type instance Apply @_ @_ (LamCases_6989586621679292884Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865) a_69895866216792928876989586621679292888 = LamCases_6989586621679292884_a1bE1 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 a_69895866216792928876989586621679292888
instance SuppressUnusedWarnings (LamCases_6989586621679292884Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292884Sym0KindInference ())
type family LamCases_6989586621679292884Sym1 s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 a_69895866216792928876989586621679292888 where
  LamCases_6989586621679292884Sym1 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 a_69895866216792928876989586621679292888 = LamCases_6989586621679292884_a1bE1 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 a_69895866216792928876989586621679292888
type family Let6989586621679292869VSym0 s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 where
  Let6989586621679292869VSym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 = Let6989586621679292869V s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865
type family Let6989586621679292869S'Sym0 s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 where
  Let6989586621679292869S'Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 = Let6989586621679292869S' s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865
type family Let6989586621679292869X_6989586621679292870Sym0 s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 where
  Let6989586621679292869X_6989586621679292870Sym0 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865 = Let6989586621679292869X_6989586621679292870 s6989586621679291935 s6989586621679292868 f6989586621679292864 k6989586621679292865
type family Let6989586621679292869V s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 where
  Let6989586621679292869V s_a1boH s_a1bDK f_a1bDG k_a1bDH = Apply (LamCases_6989586621679292877Sym0 s_a1boH s_a1bDK f_a1bDG k_a1bDH) (Let6989586621679292869X_6989586621679292870Sym0 s_a1boH s_a1bDK f_a1bDG k_a1bDH)
type family Let6989586621679292869S' s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 where
  Let6989586621679292869S' s_a1boH s_a1bDK f_a1bDG k_a1bDH = Apply (LamCases_6989586621679292884Sym0 s_a1boH s_a1bDK f_a1bDG k_a1bDH) (Let6989586621679292869X_6989586621679292870Sym0 s_a1boH s_a1bDK f_a1bDG k_a1bDH)
type family Let6989586621679292869X_6989586621679292870 s6989586621679291935 s6989586621679292868 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 where
  Let6989586621679292869X_6989586621679292870 s_a1boH s_a1bDK f_a1bDG k_a1bDH = Apply k_a1bDH s_a1bDK
type family LamCases_6989586621679292866_a1bDJ s6989586621679291935 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 a_6989586621679292891_a1bE8 where
  LamCases_6989586621679292866_a1bDJ s_a1boH f_a1bDG k_a1bDH s_a1bDK = Apply (Apply Tuple2Sym0 (Let6989586621679292869S'Sym0 s_a1boH s_a1bDK f_a1bDG k_a1bDH)) (Apply f_a1bDG (Let6989586621679292869VSym0 s_a1boH s_a1bDK f_a1bDG k_a1bDH))
data LamCases_6989586621679292866Sym0 s6989586621679291935 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 a_69895866216792928916989586621679292892
  where
    LamCases_6989586621679292866Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292866Sym0 s6989586621679291935 f6989586621679292864 k6989586621679292865) arg_a1bE9) (LamCases_6989586621679292866Sym1 s6989586621679291935 f6989586621679292864 k6989586621679292865 arg_a1bE9) =>
                                                      LamCases_6989586621679292866Sym0 s6989586621679291935 f6989586621679292864 k6989586621679292865 a_69895866216792928916989586621679292892
type instance Apply @_ @_ (LamCases_6989586621679292866Sym0 s6989586621679291935 f6989586621679292864 k6989586621679292865) a_69895866216792928916989586621679292892 = LamCases_6989586621679292866_a1bDJ s6989586621679291935 f6989586621679292864 k6989586621679292865 a_69895866216792928916989586621679292892
instance SuppressUnusedWarnings (LamCases_6989586621679292866Sym0 s6989586621679291935 f6989586621679292864 k6989586621679292865) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292866Sym0KindInference ())
type family LamCases_6989586621679292866Sym1 s6989586621679291935 (f6989586621679292864 :: (~>) a7566047373982667315 b7566047373982667316) k6989586621679292865 a_69895866216792928916989586621679292892 where
  LamCases_6989586621679292866Sym1 s6989586621679291935 f6989586621679292864 k6989586621679292865 a_69895866216792928916989586621679292892 = LamCases_6989586621679292866_a1bDJ s6989586621679291935 f6989586621679292864 k6989586621679292865 a_69895866216792928916989586621679292892
type Fmap_6989586621679292857 :: forall s_a1boH
                                        a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> StateR s_a1boH a_iYSL
                                                    -> StateR s_a1boH b_iYSM
type family Fmap_6989586621679292857 @s_a1boH @a_iYSL @b_iYSM (a_a1bDB :: (~>) a_iYSL b_iYSM) (a_a1bDC :: StateR s_a1boH a_iYSL) :: StateR s_a1boH b_iYSM where
  Fmap_6989586621679292857 @s_a1boH @a_iYSL @b_iYSM (f_a1bDG :: (~>) a_iYSL b_iYSM) ('StateR k_a1bDH :: StateR s_a1boH a_iYSL) = Apply (Apply ($@#@$) StateRSym0) (LamCases_6989586621679292866Sym0 s_a1boH f_a1bDG k_a1bDH)
instance PFunctor (StateR s_a1boH) where
  type Fmap a_a1bDx a_a1bDy = Fmap_6989586621679292857 a_a1bDx a_a1bDy
type family LamCases_6989586621679292901_a1bEi s6989586621679291941 (x6989586621679292900 :: a7566047373982553024) a_6989586621679292904_a1bEl where
  LamCases_6989586621679292901_a1bEi s_a1boN x_a1bEg s_a1bEj = Apply (Apply Tuple2Sym0 s_a1bEj) x_a1bEg
data LamCases_6989586621679292901Sym0 s6989586621679291941 (x6989586621679292900 :: a7566047373982553024) a_69895866216792929046989586621679292905
  where
    LamCases_6989586621679292901Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292901Sym0 s6989586621679291941 x6989586621679292900) arg_a1bEm) (LamCases_6989586621679292901Sym1 s6989586621679291941 x6989586621679292900 arg_a1bEm) =>
                                                      LamCases_6989586621679292901Sym0 s6989586621679291941 x6989586621679292900 a_69895866216792929046989586621679292905
type instance Apply @_ @_ (LamCases_6989586621679292901Sym0 s6989586621679291941 x6989586621679292900) a_69895866216792929046989586621679292905 = LamCases_6989586621679292901_a1bEi s6989586621679291941 x6989586621679292900 a_69895866216792929046989586621679292905
instance SuppressUnusedWarnings (LamCases_6989586621679292901Sym0 s6989586621679291941 x6989586621679292900) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292901Sym0KindInference ())
type family LamCases_6989586621679292901Sym1 s6989586621679291941 (x6989586621679292900 :: a7566047373982553024) a_69895866216792929046989586621679292905 where
  LamCases_6989586621679292901Sym1 s6989586621679291941 x6989586621679292900 a_69895866216792929046989586621679292905 = LamCases_6989586621679292901_a1bEi s6989586621679291941 x6989586621679292900 a_69895866216792929046989586621679292905
type Pure_6989586621679292895 :: forall s_a1boN a_iv9m. a_iv9m
                                                        -> StateR s_a1boN a_iv9m
type family Pure_6989586621679292895 @s_a1boN @a_iv9m (a_a1bEd :: a_iv9m) :: StateR s_a1boN a_iv9m where
  Pure_6989586621679292895 @s_a1boN @a_iv9m (x_a1bEg :: a_iv9m) = Apply StateRSym0 (LamCases_6989586621679292901Sym0 s_a1boN x_a1bEg)
type family LamCases_6989586621679292935_a1bEQ s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_6989586621679292938_a1bET where
  LamCases_6989586621679292935_a1bEQ s_a1boN s_a1bEA kf_a1bEw kv_a1bEx '(_,
                                                                    y_6989586621679292932_a1bER) = y_6989586621679292932_a1bER
data LamCases_6989586621679292935Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929386989586621679292939
  where
    LamCases_6989586621679292935Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292935Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) arg_a1bEU) (LamCases_6989586621679292935Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 arg_a1bEU) =>
                                                      LamCases_6989586621679292935Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929386989586621679292939
type instance Apply @_ @_ (LamCases_6989586621679292935Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) a_69895866216792929386989586621679292939 = LamCases_6989586621679292935_a1bEQ s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929386989586621679292939
instance SuppressUnusedWarnings (LamCases_6989586621679292935Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292935Sym0KindInference ())
type family LamCases_6989586621679292935Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929386989586621679292939 where
  LamCases_6989586621679292935Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929386989586621679292939 = LamCases_6989586621679292935_a1bEQ s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929386989586621679292939
type family LamCases_6989586621679292942_a1bEX s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_6989586621679292945_a1bF0 where
  LamCases_6989586621679292942_a1bEX s_a1boN s_a1bEA kf_a1bEw kv_a1bEx '(y_6989586621679292930_a1bEY,
                                                                    _) = y_6989586621679292930_a1bEY
data LamCases_6989586621679292942Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929456989586621679292946
  where
    LamCases_6989586621679292942Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292942Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) arg_a1bF1) (LamCases_6989586621679292942Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 arg_a1bF1) =>
                                                      LamCases_6989586621679292942Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929456989586621679292946
type instance Apply @_ @_ (LamCases_6989586621679292942Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) a_69895866216792929456989586621679292946 = LamCases_6989586621679292942_a1bEX s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929456989586621679292946
instance SuppressUnusedWarnings (LamCases_6989586621679292942Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292942Sym0KindInference ())
type family LamCases_6989586621679292942Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929456989586621679292946 where
  LamCases_6989586621679292942Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929456989586621679292946 = LamCases_6989586621679292942_a1bEX s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929456989586621679292946
type family LamCases_6989586621679292950_a1bF5 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_6989586621679292953_a1bF8 where
  LamCases_6989586621679292950_a1bF5 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx '(_,
                                                                    y_6989586621679292926_a1bF6) = y_6989586621679292926_a1bF6
data LamCases_6989586621679292950Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929536989586621679292954
  where
    LamCases_6989586621679292950Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292950Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) arg_a1bF9) (LamCases_6989586621679292950Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 arg_a1bF9) =>
                                                      LamCases_6989586621679292950Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929536989586621679292954
type instance Apply @_ @_ (LamCases_6989586621679292950Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) a_69895866216792929536989586621679292954 = LamCases_6989586621679292950_a1bF5 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929536989586621679292954
instance SuppressUnusedWarnings (LamCases_6989586621679292950Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292950Sym0KindInference ())
type family LamCases_6989586621679292950Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929536989586621679292954 where
  LamCases_6989586621679292950Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929536989586621679292954 = LamCases_6989586621679292950_a1bF5 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929536989586621679292954
type family LamCases_6989586621679292957_a1bFc s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_6989586621679292960_a1bFf where
  LamCases_6989586621679292957_a1bFc s_a1boN s_a1bEA kf_a1bEw kv_a1bEx '(y_6989586621679292924_a1bFd,
                                                                    _) = y_6989586621679292924_a1bFd
data LamCases_6989586621679292957Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929606989586621679292961
  where
    LamCases_6989586621679292957Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292957Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) arg_a1bFg) (LamCases_6989586621679292957Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 arg_a1bFg) =>
                                                      LamCases_6989586621679292957Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929606989586621679292961
type instance Apply @_ @_ (LamCases_6989586621679292957Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) a_69895866216792929606989586621679292961 = LamCases_6989586621679292957_a1bFc s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929606989586621679292961
instance SuppressUnusedWarnings (LamCases_6989586621679292957Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292957Sym0KindInference ())
type family LamCases_6989586621679292957Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929606989586621679292961 where
  LamCases_6989586621679292957Sym1 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929606989586621679292961 = LamCases_6989586621679292957_a1bFc s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 a_69895866216792929606989586621679292961
type family Let6989586621679292921FSym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921FSym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 = Let6989586621679292921F s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917
type family Let6989586621679292921S''Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921S''Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 = Let6989586621679292921S'' s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917
type family Let6989586621679292921X_6989586621679292928Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921X_6989586621679292928Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 = Let6989586621679292921X_6989586621679292928 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917
type family Let6989586621679292921VSym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921VSym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 = Let6989586621679292921V s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917
type family Let6989586621679292921S'Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921S'Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 = Let6989586621679292921S' s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917
type family Let6989586621679292921X_6989586621679292922Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921X_6989586621679292922Sym0 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 = Let6989586621679292921X_6989586621679292922 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917
type family Let6989586621679292921F s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921F s_a1boN s_a1bEA kf_a1bEw kv_a1bEx = Apply (LamCases_6989586621679292935Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx) (Let6989586621679292921X_6989586621679292928Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
type family Let6989586621679292921S'' s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921S'' s_a1boN s_a1bEA kf_a1bEw kv_a1bEx = Apply (LamCases_6989586621679292942Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx) (Let6989586621679292921X_6989586621679292928Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
type family Let6989586621679292921X_6989586621679292928 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921X_6989586621679292928 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx = Apply kf_a1bEw (Let6989586621679292921S'Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
type family Let6989586621679292921V s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921V s_a1boN s_a1bEA kf_a1bEw kv_a1bEx = Apply (LamCases_6989586621679292950Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx) (Let6989586621679292921X_6989586621679292922Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
type family Let6989586621679292921S' s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921S' s_a1boN s_a1bEA kf_a1bEw kv_a1bEx = Apply (LamCases_6989586621679292957Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx) (Let6989586621679292921X_6989586621679292922Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
type family Let6989586621679292921X_6989586621679292922 s6989586621679291941 s6989586621679292920 kf6989586621679292916 kv6989586621679292917 where
  Let6989586621679292921X_6989586621679292922 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx = Apply kv_a1bEx s_a1bEA
type family LamCases_6989586621679292918_a1bEz s6989586621679291941 kf6989586621679292916 kv6989586621679292917 a_6989586621679292964_a1bFj where
  LamCases_6989586621679292918_a1bEz s_a1boN kf_a1bEw kv_a1bEx s_a1bEA = Apply (Apply Tuple2Sym0 (Let6989586621679292921S''Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)) (Apply (Let6989586621679292921FSym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx) (Let6989586621679292921VSym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx))
data LamCases_6989586621679292918Sym0 s6989586621679291941 kf6989586621679292916 kv6989586621679292917 a_69895866216792929646989586621679292965
  where
    LamCases_6989586621679292918Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292918Sym0 s6989586621679291941 kf6989586621679292916 kv6989586621679292917) arg_a1bFk) (LamCases_6989586621679292918Sym1 s6989586621679291941 kf6989586621679292916 kv6989586621679292917 arg_a1bFk) =>
                                                      LamCases_6989586621679292918Sym0 s6989586621679291941 kf6989586621679292916 kv6989586621679292917 a_69895866216792929646989586621679292965
type instance Apply @_ @_ (LamCases_6989586621679292918Sym0 s6989586621679291941 kf6989586621679292916 kv6989586621679292917) a_69895866216792929646989586621679292965 = LamCases_6989586621679292918_a1bEz s6989586621679291941 kf6989586621679292916 kv6989586621679292917 a_69895866216792929646989586621679292965
instance SuppressUnusedWarnings (LamCases_6989586621679292918Sym0 s6989586621679291941 kf6989586621679292916 kv6989586621679292917) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292918Sym0KindInference ())
type family LamCases_6989586621679292918Sym1 s6989586621679291941 kf6989586621679292916 kv6989586621679292917 a_69895866216792929646989586621679292965 where
  LamCases_6989586621679292918Sym1 s6989586621679291941 kf6989586621679292916 kv6989586621679292917 a_69895866216792929646989586621679292965 = LamCases_6989586621679292918_a1bEz s6989586621679291941 kf6989586621679292916 kv6989586621679292917 a_69895866216792929646989586621679292965
type TFHelper_6989586621679292909 :: forall s_a1boN
                                            a_iv9o
                                            b_iv9p. StateR s_a1boN ((~>) a_iv9o b_iv9p)
                                                    -> StateR s_a1boN a_iv9o
                                                        -> StateR s_a1boN b_iv9p
type family TFHelper_6989586621679292909 @s_a1boN @a_iv9o @b_iv9p (a_a1bEr :: StateR s_a1boN ((~>) a_iv9o b_iv9p)) (a_a1bEs :: StateR s_a1boN a_iv9o) :: StateR s_a1boN b_iv9p where
  TFHelper_6989586621679292909 @s_a1boN @a_iv9o @b_iv9p ('StateR kf_a1bEw :: StateR s_a1boN ((~>) a_iv9o b_iv9p)) ('StateR kv_a1bEx :: StateR s_a1boN a_iv9o) = Apply (Apply ($@#@$) StateRSym0) (LamCases_6989586621679292918Sym0 s_a1boN kf_a1bEw kv_a1bEx)
type family LamCases_6989586621679292999_a1bFS s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_6989586621679293002_a1bFV where
  LamCases_6989586621679292999_a1bFS s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz '(_,
                                                                            y_6989586621679292996_a1bFT) = y_6989586621679292996_a1bFT
data LamCases_6989586621679292999Sym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930026989586621679293003
  where
    LamCases_6989586621679292999Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292999Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) arg_a1bFW) (LamCases_6989586621679292999Sym1 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 arg_a1bFW) =>
                                                      LamCases_6989586621679292999Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930026989586621679293003
type instance Apply @_ @_ (LamCases_6989586621679292999Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) a_69895866216792930026989586621679293003 = LamCases_6989586621679292999_a1bFS s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930026989586621679293003
instance SuppressUnusedWarnings (LamCases_6989586621679292999Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292999Sym0KindInference ())
type family LamCases_6989586621679292999Sym1 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930026989586621679293003 where
  LamCases_6989586621679292999Sym1 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930026989586621679293003 = LamCases_6989586621679292999_a1bFS s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930026989586621679293003
type family LamCases_6989586621679293006_a1bFZ s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_6989586621679293009_a1bG2 where
  LamCases_6989586621679293006_a1bFZ s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz '(y_6989586621679292994_a1bG0,
                                                                            _) = y_6989586621679292994_a1bG0
data LamCases_6989586621679293006Sym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930096989586621679293010
  where
    LamCases_6989586621679293006Sym0KindInference :: SameKind (Apply (LamCases_6989586621679293006Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) arg_a1bG3) (LamCases_6989586621679293006Sym1 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 arg_a1bG3) =>
                                                      LamCases_6989586621679293006Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930096989586621679293010
type instance Apply @_ @_ (LamCases_6989586621679293006Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) a_69895866216792930096989586621679293010 = LamCases_6989586621679293006_a1bFZ s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930096989586621679293010
instance SuppressUnusedWarnings (LamCases_6989586621679293006Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679293006Sym0KindInference ())
type family LamCases_6989586621679293006Sym1 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930096989586621679293010 where
  LamCases_6989586621679293006Sym1 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930096989586621679293010 = LamCases_6989586621679293006_a1bFZ s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930096989586621679293010
type family LamCases_6989586621679293014_a1bG7 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_6989586621679293017_a1bGa where
  LamCases_6989586621679293014_a1bG7 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz '(_,
                                                                            y_6989586621679292990_a1bG8) = y_6989586621679292990_a1bG8
data LamCases_6989586621679293014Sym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930176989586621679293018
  where
    LamCases_6989586621679293014Sym0KindInference :: SameKind (Apply (LamCases_6989586621679293014Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) arg_a1bGb) (LamCases_6989586621679293014Sym1 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 arg_a1bGb) =>
                                                      LamCases_6989586621679293014Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930176989586621679293018
type instance Apply @_ @_ (LamCases_6989586621679293014Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) a_69895866216792930176989586621679293018 = LamCases_6989586621679293014_a1bG7 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930176989586621679293018
instance SuppressUnusedWarnings (LamCases_6989586621679293014Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679293014Sym0KindInference ())
type family LamCases_6989586621679293014Sym1 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930176989586621679293018 where
  LamCases_6989586621679293014Sym1 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930176989586621679293018 = LamCases_6989586621679293014_a1bG7 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930176989586621679293018
type family LamCases_6989586621679293021_a1bGe s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_6989586621679293024_a1bGh where
  LamCases_6989586621679293021_a1bGe s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz '(y_6989586621679292988_a1bGf,
                                                                            _) = y_6989586621679292988_a1bGf
data LamCases_6989586621679293021Sym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930246989586621679293025
  where
    LamCases_6989586621679293021Sym0KindInference :: SameKind (Apply (LamCases_6989586621679293021Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) arg_a1bGi) (LamCases_6989586621679293021Sym1 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 arg_a1bGi) =>
                                                      LamCases_6989586621679293021Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930246989586621679293025
type instance Apply @_ @_ (LamCases_6989586621679293021Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) a_69895866216792930246989586621679293025 = LamCases_6989586621679293021_a1bGe s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930246989586621679293025
instance SuppressUnusedWarnings (LamCases_6989586621679293021Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679293021Sym0KindInference ())
type family LamCases_6989586621679293021Sym1 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930246989586621679293025 where
  LamCases_6989586621679293021Sym1 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930246989586621679293025 = LamCases_6989586621679293021_a1bGe s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930246989586621679293025
type family Let6989586621679292985XSym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985XSym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 = Let6989586621679292985X s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981
type family Let6989586621679292985S''Sym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985S''Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 = Let6989586621679292985S'' s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981
type family Let6989586621679292985X_6989586621679292992Sym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985X_6989586621679292992Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 = Let6989586621679292985X_6989586621679292992 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981
type family Let6989586621679292985YSym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985YSym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 = Let6989586621679292985Y s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981
type family Let6989586621679292985S'Sym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985S'Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 = Let6989586621679292985S' s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981
type family Let6989586621679292985X_6989586621679292986Sym0 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985X_6989586621679292986Sym0 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 = Let6989586621679292985X_6989586621679292986 s6989586621679291941 s6989586621679292984 f6989586621679292979 kx6989586621679292980 ky6989586621679292981
type family Let6989586621679292985X s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985X s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz = Apply (LamCases_6989586621679292999Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz) (Let6989586621679292985X_6989586621679292992Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
type family Let6989586621679292985S'' s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985S'' s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz = Apply (LamCases_6989586621679293006Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz) (Let6989586621679292985X_6989586621679292992Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
type family Let6989586621679292985X_6989586621679292992 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985X_6989586621679292992 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz = Apply kx_a1bFy (Let6989586621679292985S'Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
type family Let6989586621679292985Y s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985Y s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz = Apply (LamCases_6989586621679293014Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz) (Let6989586621679292985X_6989586621679292986Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
type family Let6989586621679292985S' s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985S' s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz = Apply (LamCases_6989586621679293021Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz) (Let6989586621679292985X_6989586621679292986Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
type family Let6989586621679292985X_6989586621679292986 s6989586621679291941 s6989586621679292984 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 where
  Let6989586621679292985X_6989586621679292986 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz = Apply ky_a1bFz s_a1bFC
type family LamCases_6989586621679292982_a1bFB s6989586621679291941 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_6989586621679293028_a1bGl where
  LamCases_6989586621679292982_a1bFB s_a1boN f_a1bFx kx_a1bFy ky_a1bFz s_a1bFC = Apply (Apply Tuple2Sym0 (Let6989586621679292985S''Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)) (Apply (Apply f_a1bFx (Let6989586621679292985XSym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)) (Let6989586621679292985YSym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz))
data LamCases_6989586621679292982Sym0 s6989586621679291941 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930286989586621679293029
  where
    LamCases_6989586621679292982Sym0KindInference :: SameKind (Apply (LamCases_6989586621679292982Sym0 s6989586621679291941 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) arg_a1bGm) (LamCases_6989586621679292982Sym1 s6989586621679291941 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 arg_a1bGm) =>
                                                      LamCases_6989586621679292982Sym0 s6989586621679291941 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930286989586621679293029
type instance Apply @_ @_ (LamCases_6989586621679292982Sym0 s6989586621679291941 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) a_69895866216792930286989586621679293029 = LamCases_6989586621679292982_a1bFB s6989586621679291941 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930286989586621679293029
instance SuppressUnusedWarnings (LamCases_6989586621679292982Sym0 s6989586621679291941 f6989586621679292979 kx6989586621679292980 ky6989586621679292981) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679292982Sym0KindInference ())
type family LamCases_6989586621679292982Sym1 s6989586621679291941 (f6989586621679292979 :: (~>) a7566047373982553030 ((~>) b7566047373982553031 c7566047373982553032)) kx6989586621679292980 ky6989586621679292981 a_69895866216792930286989586621679293029 where
  LamCases_6989586621679292982Sym1 s6989586621679291941 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930286989586621679293029 = LamCases_6989586621679292982_a1bFB s6989586621679291941 f6989586621679292979 kx6989586621679292980 ky6989586621679292981 a_69895866216792930286989586621679293029
type LiftA2_6989586621679292970 :: forall s_a1boN
                                          a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> StateR s_a1boN a_iv9s
                                                      -> StateR s_a1boN b_iv9t
                                                        -> StateR s_a1boN c_iv9u
type family LiftA2_6989586621679292970 @s_a1boN @a_iv9s @b_iv9t @c_iv9u (a_a1bFq :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a1bFr :: StateR s_a1boN a_iv9s) (a_a1bFs :: StateR s_a1boN b_iv9t) :: StateR s_a1boN c_iv9u where
  LiftA2_6989586621679292970 @s_a1boN @a_iv9s @b_iv9t @c_iv9u (f_a1bFx :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) ('StateR kx_a1bFy :: StateR s_a1boN a_iv9s) ('StateR ky_a1bFz :: StateR s_a1boN b_iv9t) = Apply (Apply ($@#@$) StateRSym0) (LamCases_6989586621679292982Sym0 s_a1boN f_a1bFx kx_a1bFy ky_a1bFz)
instance PApplicative (StateR s_a1boN) where
  type Pure a_a1bEa = Pure_6989586621679292895 a_a1bEa
  type (<*>) a_a1bEn a_a1bEo = TFHelper_6989586621679292909 a_a1bEn a_a1bEo
  type LiftA2 a_a1bFl a_a1bFm a_a1bFn = LiftA2_6989586621679292970 a_a1bFl a_a1bFm a_a1bFn
sFoldMapDefault ::
  forall t_a1bnO
          m_a1bnP
          a_a1bnQ
          (t_a1bGn :: (~>) a_a1bnQ m_a1bnP)
          (t_a1bGo :: t_a1bnO a_a1bnQ). (STraversable t_a1bnO,
                                        SMonoid m_a1bnP) =>
                                        Sing t_a1bGn
                                        -> Sing t_a1bGo
                                          -> Sing (FoldMapDefault t_a1bGn t_a1bGo :: m_a1bnP)
sFmapDefault ::
  forall t_a1bnR
          a_a1bnS
          b_a1bnT
          (t_a1bGs :: (~>) a_a1bnS b_a1bnT)
          (t_a1bGt :: t_a1bnR a_a1bnS). STraversable t_a1bnR =>
                                        Sing t_a1bGs
                                        -> Sing t_a1bGt
                                          -> Sing (FmapDefault t_a1bGs t_a1bGt :: t_a1bnR b_a1bnT)
sMapAccumR ::
  (forall (t_a1bGx :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV, c_a1bnX)))
          (t_a1bGy :: a_a1bnV)
          (t_a1bGz :: t_a1bnU b_a1bnW).
    STraversable t_a1bnU =>
    Sing t_a1bGx
    -> Sing t_a1bGy
      -> Sing t_a1bGz
          -> Sing (MapAccumR t_a1bGx t_a1bGy t_a1bGz :: (a_a1bnV,
                                                        t_a1bnU c_a1bnX)) :: Type)
sMapAccumL ::
  forall t_a1bnY
          a_a1bnZ
          b_a1bo0
          c_a1bo1
          (t_a1bGH :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ, c_a1bo1)))
          (t_a1bGI :: a_a1bnZ)
          (t_a1bGJ :: t_a1bnY b_a1bo0). STraversable t_a1bnY =>
                                        Sing t_a1bGH
                                        -> Sing t_a1bGI
                                          -> Sing t_a1bGJ
                                              -> Sing (MapAccumL t_a1bGH t_a1bGI t_a1bGJ :: (a_a1bnZ,
                                                                                            t_a1bnY c_a1bo1))
sForM ::
  (forall (t_a1bGR :: t_a1bo2 a_a1bo4)
          (t_a1bGS :: (~>) a_a1bo4 (m_a1bo3 b_a1bo5)).
    (STraversable t_a1bo2, SMonad m_a1bo3) =>
    Sing t_a1bGR
    -> Sing t_a1bGS
      -> Sing (ForM t_a1bGR t_a1bGS :: m_a1bo3 (t_a1bo2 b_a1bo5)) :: Type)
sFor ::
  (forall (t_a1bGW :: t_a1bo6 a_a1bo8)
          (t_a1bGX :: (~>) a_a1bo8 (f_a1bo7 b_a1bo9)).
    (STraversable t_a1bo6, SApplicative f_a1bo7) =>
    Sing t_a1bGW
    -> Sing t_a1bGX
      -> Sing (For t_a1bGW t_a1bGX :: f_a1bo7 (t_a1bo6 b_a1bo9)) :: Type)
sFoldMapDefault (sF :: Sing f_a1bvM) (sX :: Sing x_a1bvN)
  = let
      sMkConst ::
        (forall (t_a1bH1 :: m_a1bnP).
          Sing t_a1bH1
          -> Sing (Let6989586621679292376MkConst t_a1bnO m_a1bnP a_a1bnQ f_a1bvM x_a1bvN t_a1bH1 :: Const m_a1bnP ()) :: Type)
      sMkConst
        (sA_6989586621679292377 :: Sing a_6989586621679292377_a1bvT)
        = applySing (singFun1 @ConstSym0 SConst) sA_6989586621679292377
    in
      applySing
        (singFun1
            @(LamCases_6989586621679292382Sym0 t_a1bnO m_a1bnP a_a1bnQ f_a1bvM x_a1bvN)
            (\cases (SConst (sY :: Sing y_a1bvW)) -> sY))
        (applySing
            (applySing
              (singFun2 @TraverseSym0 sTraverse)
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (singFun1
                        @(Let6989586621679292376MkConstSym0 t_a1bnO m_a1bnP a_a1bnQ f_a1bvM x_a1bvN)
                        sMkConst))
                  sF))
            sX)
sFmapDefault (sF :: Sing f_a1bw5) (sX :: Sing x_a1bw6)
  = applySing
      (singFun1
          @(LamCases_6989586621679292395Sym0 t_a1bnR a_a1bnS b_a1bnT f_a1bw5 x_a1bw6)
          (\cases (SIdentity (sY :: Sing y_a1bw9)) -> sY))
      (applySing
          (applySing
            (singFun2 @TraverseSym0 sTraverse)
            (applySing
                (applySing
                  (singFun3 @(.@#@$) (%.)) (singFun1 @IdentitySym0 SIdentity))
                sF))
          sX)
sMapAccumR
  (sF :: Sing f_a1bwk)
  (sS :: Sing s_a1bwl)
  (sT :: Sing t_a1bwm)
  = applySing
      (applySing
          (singFun2 @RunStateRSym0 sRunStateR)
          (applySing
            (applySing
                (singFun2 @TraverseSym0 sTraverse)
                (applySing
                  (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @StateRSym0 SStateR))
                  (applySing (singFun3 @FlipSym0 sFlip) sF)))
            sT))
      sS
sMapAccumL
  (sF :: Sing f_a1bwu)
  (sS :: Sing s_a1bwv)
  (sT :: Sing t_a1bww)
  = applySing
      (applySing
          (singFun2 @RunStateLSym0 sRunStateL)
          (applySing
            (applySing
                (singFun2 @TraverseSym0 sTraverse)
                (applySing
                  (applySing (singFun3 @(.@#@$) (%.)) (singFun1 @StateLSym0 SStateL))
                  (applySing (singFun3 @FlipSym0 sFlip) sF)))
            sT))
      sS
sForM
  (sA_6989586621679292421 :: Sing a_6989586621679292421_a1bwG)
  (sA_6989586621679292423 :: Sing a_6989586621679292423_a1bwH)
  = applySing
      (applySing
          (applySing (singFun3 @FlipSym0 sFlip) (singFun2 @MapMSym0 sMapM))
          sA_6989586621679292421)
      sA_6989586621679292423
sFor
  (sA_6989586621679292432 :: Sing a_6989586621679292432_a1bwR)
  (sA_6989586621679292434 :: Sing a_6989586621679292434_a1bwS)
  = applySing
      (applySing
          (applySing
            (singFun3 @FlipSym0 sFlip) (singFun2 @TraverseSym0 sTraverse))
          sA_6989586621679292432)
      sA_6989586621679292434
instance (STraversable t_a1bnO, SMonoid m_a1bnP) =>
          SingI (FoldMapDefaultSym0 :: (~>) ((~>) a_a1bnQ m_a1bnP) ((~>) (t_a1bnO a_a1bnQ) m_a1bnP)) where
  sing = singFun2 @FoldMapDefaultSym0 sFoldMapDefault
instance (STraversable t_a1bnO, SMonoid m_a1bnP, SingI d_a1bGp) =>
          SingI (FoldMapDefaultSym1 (d_a1bGp :: (~>) a_a1bnQ m_a1bnP) :: (~>) (t_a1bnO a_a1bnQ) m_a1bnP) where
  sing
    = singFun1
        @(FoldMapDefaultSym1 (d_a1bGp :: (~>) a_a1bnQ m_a1bnP))
        (sFoldMapDefault (sing @d_a1bGp))
instance (STraversable t_a1bnO, SMonoid m_a1bnP) =>
          SingI1 (FoldMapDefaultSym1 :: (~>) a_a1bnQ m_a1bnP
                                        -> (~>) (t_a1bnO a_a1bnQ) m_a1bnP) where
  liftSing (s_a1bGr :: Sing (d_a1bGp :: (~>) a_a1bnQ m_a1bnP))
    = singFun1
        @(FoldMapDefaultSym1 (d_a1bGp :: (~>) a_a1bnQ m_a1bnP))
        (sFoldMapDefault s_a1bGr)
instance STraversable t_a1bnR =>
          SingI (FmapDefaultSym0 :: (~>) ((~>) a_a1bnS b_a1bnT) ((~>) (t_a1bnR a_a1bnS) (t_a1bnR b_a1bnT))) where
  sing = singFun2 @FmapDefaultSym0 sFmapDefault
instance (STraversable t_a1bnR, SingI d_a1bGu) =>
          SingI (FmapDefaultSym1 (d_a1bGu :: (~>) a_a1bnS b_a1bnT) :: (~>) (t_a1bnR a_a1bnS) (t_a1bnR b_a1bnT)) where
  sing
    = singFun1
        @(FmapDefaultSym1 (d_a1bGu :: (~>) a_a1bnS b_a1bnT))
        (sFmapDefault (sing @d_a1bGu))
instance STraversable t_a1bnR =>
          SingI1 (FmapDefaultSym1 :: (~>) a_a1bnS b_a1bnT
                                    -> (~>) (t_a1bnR a_a1bnS) (t_a1bnR b_a1bnT)) where
  liftSing (s_a1bGw :: Sing (d_a1bGu :: (~>) a_a1bnS b_a1bnT))
    = singFun1
        @(FmapDefaultSym1 (d_a1bGu :: (~>) a_a1bnS b_a1bnT))
        (sFmapDefault s_a1bGw)
instance STraversable t_a1bnU =>
          SingI (MapAccumRSym0 :: (~>) ((~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                    c_a1bnX))) ((~>) a_a1bnV ((~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                                                                      t_a1bnU c_a1bnX)))) where
  sing = singFun3 @MapAccumRSym0 sMapAccumR
instance (STraversable t_a1bnU, SingI d_a1bGA) =>
          SingI (MapAccumRSym1 (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                      c_a1bnX))) :: (~>) a_a1bnV ((~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                                                                          t_a1bnU c_a1bnX))) where
  sing
    = singFun2
        @(MapAccumRSym1 (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                c_a1bnX))))
        (sMapAccumR (sing @d_a1bGA))
instance STraversable t_a1bnU =>
          SingI1 (MapAccumRSym1 :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                              c_a1bnX))
                                  -> (~>) a_a1bnV ((~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                            t_a1bnU c_a1bnX))) where
  liftSing
    (s_a1bGG :: Sing (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                              c_a1bnX))))
    = singFun2
        @(MapAccumRSym1 (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                c_a1bnX))))
        (sMapAccumR s_a1bGG)
instance (STraversable t_a1bnU, SingI d_a1bGA, SingI d_a1bGB) =>
          SingI (MapAccumRSym2 (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                      c_a1bnX))) (d_a1bGB :: a_a1bnV) :: (~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                                                                                  t_a1bnU c_a1bnX)) where
  sing
    = singFun1
        @(MapAccumRSym2 (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                c_a1bnX))) (d_a1bGB :: a_a1bnV))
        (sMapAccumR (sing @d_a1bGA) (sing @d_a1bGB))
instance (STraversable t_a1bnU, SingI d_a1bGA) =>
          SingI1 (MapAccumRSym2 (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                        c_a1bnX))) :: a_a1bnV
                                                                                      -> (~>) (t_a1bnU b_a1bnW) (a_a1bnV,
                                                                                                                t_a1bnU c_a1bnX)) where
  liftSing (s_a1bGD :: Sing (d_a1bGB :: a_a1bnV))
    = singFun1
        @(MapAccumRSym2 (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                c_a1bnX))) (d_a1bGB :: a_a1bnV))
        (sMapAccumR (sing @d_a1bGA) s_a1bGD)
instance STraversable t_a1bnU =>
          SingI2 (MapAccumRSym2 :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                              c_a1bnX))
                                  -> a_a1bnV
                                      -> (~>) (t_a1bnU b_a1bnW) (a_a1bnV, t_a1bnU c_a1bnX)) where
  liftSing2
    (s_a1bGE :: Sing (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                              c_a1bnX))))
    (s_a1bGF :: Sing (d_a1bGB :: a_a1bnV))
    = singFun1
        @(MapAccumRSym2 (d_a1bGA :: (~>) a_a1bnV ((~>) b_a1bnW (a_a1bnV,
                                                                c_a1bnX))) (d_a1bGB :: a_a1bnV))
        (sMapAccumR s_a1bGE s_a1bGF)
instance STraversable t_a1bnY =>
          SingI (MapAccumLSym0 :: (~>) ((~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                    c_a1bo1))) ((~>) a_a1bnZ ((~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                                                      t_a1bnY c_a1bo1)))) where
  sing = singFun3 @MapAccumLSym0 sMapAccumL
instance (STraversable t_a1bnY, SingI d_a1bGK) =>
          SingI (MapAccumLSym1 (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                      c_a1bo1))) :: (~>) a_a1bnZ ((~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                                                          t_a1bnY c_a1bo1))) where
  sing
    = singFun2
        @(MapAccumLSym1 (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                c_a1bo1))))
        (sMapAccumL (sing @d_a1bGK))
instance STraversable t_a1bnY =>
          SingI1 (MapAccumLSym1 :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                              c_a1bo1))
                                  -> (~>) a_a1bnZ ((~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                            t_a1bnY c_a1bo1))) where
  liftSing
    (s_a1bGQ :: Sing (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                              c_a1bo1))))
    = singFun2
        @(MapAccumLSym1 (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                c_a1bo1))))
        (sMapAccumL s_a1bGQ)
instance (STraversable t_a1bnY, SingI d_a1bGK, SingI d_a1bGL) =>
          SingI (MapAccumLSym2 (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                      c_a1bo1))) (d_a1bGL :: a_a1bnZ) :: (~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                                                                  t_a1bnY c_a1bo1)) where
  sing
    = singFun1
        @(MapAccumLSym2 (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                c_a1bo1))) (d_a1bGL :: a_a1bnZ))
        (sMapAccumL (sing @d_a1bGK) (sing @d_a1bGL))
instance (STraversable t_a1bnY, SingI d_a1bGK) =>
          SingI1 (MapAccumLSym2 (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                        c_a1bo1))) :: a_a1bnZ
                                                                                      -> (~>) (t_a1bnY b_a1bo0) (a_a1bnZ,
                                                                                                                t_a1bnY c_a1bo1)) where
  liftSing (s_a1bGN :: Sing (d_a1bGL :: a_a1bnZ))
    = singFun1
        @(MapAccumLSym2 (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                c_a1bo1))) (d_a1bGL :: a_a1bnZ))
        (sMapAccumL (sing @d_a1bGK) s_a1bGN)
instance STraversable t_a1bnY =>
          SingI2 (MapAccumLSym2 :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                              c_a1bo1))
                                  -> a_a1bnZ
                                      -> (~>) (t_a1bnY b_a1bo0) (a_a1bnZ, t_a1bnY c_a1bo1)) where
  liftSing2
    (s_a1bGO :: Sing (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                              c_a1bo1))))
    (s_a1bGP :: Sing (d_a1bGL :: a_a1bnZ))
    = singFun1
        @(MapAccumLSym2 (d_a1bGK :: (~>) a_a1bnZ ((~>) b_a1bo0 (a_a1bnZ,
                                                                c_a1bo1))) (d_a1bGL :: a_a1bnZ))
        (sMapAccumL s_a1bGO s_a1bGP)
instance (STraversable t_a1bo2, SMonad m_a1bo3) =>
          SingI (ForMSym0 :: (~>) (t_a1bo2 a_a1bo4) ((~>) ((~>) a_a1bo4 (m_a1bo3 b_a1bo5)) (m_a1bo3 (t_a1bo2 b_a1bo5)))) where
  sing = singFun2 @ForMSym0 sForM
instance (STraversable t_a1bo2, SMonad m_a1bo3, SingI d_a1bGT) =>
          SingI (ForMSym1 (d_a1bGT :: t_a1bo2 a_a1bo4) :: (~>) ((~>) a_a1bo4 (m_a1bo3 b_a1bo5)) (m_a1bo3 (t_a1bo2 b_a1bo5))) where
  sing
    = singFun1
        @(ForMSym1 (d_a1bGT :: t_a1bo2 a_a1bo4)) (sForM (sing @d_a1bGT))
instance (STraversable t_a1bo2, SMonad m_a1bo3) =>
          SingI1 (ForMSym1 :: t_a1bo2 a_a1bo4
                              -> (~>) ((~>) a_a1bo4 (m_a1bo3 b_a1bo5)) (m_a1bo3 (t_a1bo2 b_a1bo5))) where
  liftSing (s_a1bGV :: Sing (d_a1bGT :: t_a1bo2 a_a1bo4))
    = singFun1 @(ForMSym1 (d_a1bGT :: t_a1bo2 a_a1bo4)) (sForM s_a1bGV)
instance (STraversable t_a1bo6, SApplicative f_a1bo7) =>
          SingI (ForSym0 :: (~>) (t_a1bo6 a_a1bo8) ((~>) ((~>) a_a1bo8 (f_a1bo7 b_a1bo9)) (f_a1bo7 (t_a1bo6 b_a1bo9)))) where
  sing = singFun2 @ForSym0 sFor
instance (STraversable t_a1bo6,
          SApplicative f_a1bo7,
          SingI d_a1bGY) =>
          SingI (ForSym1 (d_a1bGY :: t_a1bo6 a_a1bo8) :: (~>) ((~>) a_a1bo8 (f_a1bo7 b_a1bo9)) (f_a1bo7 (t_a1bo6 b_a1bo9))) where
  sing
    = singFun1
        @(ForSym1 (d_a1bGY :: t_a1bo6 a_a1bo8)) (sFor (sing @d_a1bGY))
instance (STraversable t_a1bo6, SApplicative f_a1bo7) =>
          SingI1 (ForSym1 :: t_a1bo6 a_a1bo8
                            -> (~>) ((~>) a_a1bo8 (f_a1bo7 b_a1bo9)) (f_a1bo7 (t_a1bo6 b_a1bo9))) where
  liftSing (s_a1bH0 :: Sing (d_a1bGY :: t_a1bo6 a_a1bo8))
    = singFun1 @(ForSym1 (d_a1bGY :: t_a1bo6 a_a1bo8)) (sFor s_a1bH0)
instance STraversable Maybe where
  sTraverse
    (_sf_6989586621679292247 :: Sing _f_6989586621679292247_a1bx2)
    SNothing
    = applySing (singFun1 @PureSym0 sPure) SNothing
  sTraverse
    (_sf_6989586621679292247 :: Sing _f_6989586621679292247_a1bx3)
    (SJust (sA_6989586621679292249 :: Sing a_6989586621679292249_a1bx4))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @JustSym0 SJust))
        (applySing _sf_6989586621679292247 sA_6989586621679292249)
instance STraversable [] where
  sTraverse
    (_sf_6989586621679292259 :: Sing _f_6989586621679292259_a1bxe)
    SNil
    = applySing (singFun1 @PureSym0 sPure) SNil
  sTraverse
    (_sf_6989586621679292259 :: Sing _f_6989586621679292259_a1bxf)
    (SCons (sA_6989586621679292267 :: Sing a_6989586621679292267_a1bxg)
            (sA_6989586621679292269 :: Sing a_6989586621679292269_a1bxh))
    = applySing
        (applySing
            (applySing
              (singFun3 @LiftA2Sym0 sLiftA2) (singFun2 @(:@#@$) SCons))
            (applySing _sf_6989586621679292259 sA_6989586621679292267))
        (applySing
            (applySing
              (singFun2 @TraverseSym0 sTraverse) _sf_6989586621679292259)
            sA_6989586621679292269)
instance STraversable NonEmpty where
  sTraverse
    (_sf_6989586621679292278 :: Sing _f_6989586621679292278_a1bxr)
    ((:%|) (sA_6989586621679292286 :: Sing a_6989586621679292286_a1bxs)
            (sA_6989586621679292288 :: Sing a_6989586621679292288_a1bxt))
    = applySing
        (applySing
            (applySing
              (singFun3 @LiftA2Sym0 sLiftA2) (singFun2 @(:|@#@$) (:%|)))
            (applySing _sf_6989586621679292278 sA_6989586621679292286))
        (applySing
            (applySing
              (singFun2 @TraverseSym0 sTraverse) _sf_6989586621679292278)
            sA_6989586621679292288)
instance STraversable (Either a_a1bog) where
  sTraverse
    (_sf_6989586621679292294 :: Sing _f_6989586621679292294_a1bxD)
    (SLeft (sA_6989586621679292296 :: Sing a_6989586621679292296_a1bxE))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @LeftSym0 SLeft))
        (applySing (singFun1 @PureSym0 sPure) sA_6989586621679292296)
  sTraverse
    (_sf_6989586621679292294 :: Sing _f_6989586621679292294_a1bxF)
    (SRight (sA_6989586621679292298 :: Sing a_6989586621679292298_a1bxG))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @RightSym0 SRight))
        (applySing _sf_6989586621679292294 sA_6989586621679292298)
instance STraversable ((,) a_a1boh) where
  sTraverse
    (_sf_6989586621679292302 :: Sing _f_6989586621679292302_a1bxQ)
    (STuple2 (sA_6989586621679292304 :: Sing a_6989586621679292304_a1bxR)
              (sA_6989586621679292306 :: Sing a_6989586621679292306_a1bxS))
    = applySing
        (applySing
            (applySing
              (singFun3 @LiftA2Sym0 sLiftA2) (singFun2 @Tuple2Sym0 STuple2))
            (applySing (singFun1 @PureSym0 sPure) sA_6989586621679292304))
        (applySing _sf_6989586621679292302 sA_6989586621679292306)
instance STraversable Proxy where
  sTraverse _ _ = applySing (singFun1 @PureSym0 sPure) SProxy
  sSequenceA _ = applySing (singFun1 @PureSym0 sPure) SProxy
  sMapM _ _ = applySing (singFun1 @PureSym0 sPure) SProxy
  sSequence _ = applySing (singFun1 @PureSym0 sPure) SProxy
instance STraversable (Const m_a1boi) where
  sTraverse
    (_sf_6989586621679292311 :: Sing _f_6989586621679292311_a1byw)
    (SConst (sA_6989586621679292313 :: Sing a_6989586621679292313_a1byx))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @ConstSym0 SConst))
        (applySing (singFun1 @PureSym0 sPure) sA_6989586621679292313)
instance STraversable Dual where
  sTraverse
    (_sf_6989586621679292316 :: Sing _f_6989586621679292316_a1byH)
    (SDual (sA_6989586621679292318 :: Sing a_6989586621679292318_a1byI))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @DualSym0 SDual))
        (applySing _sf_6989586621679292316 sA_6989586621679292318)
instance STraversable Sum where
  sTraverse
    (_sf_6989586621679292321 :: Sing _f_6989586621679292321_a1byS)
    (SSum (sA_6989586621679292323 :: Sing a_6989586621679292323_a1byT))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @SumSym0 SSum))
        (applySing _sf_6989586621679292321 sA_6989586621679292323)
instance STraversable Product where
  sTraverse
    (_sf_6989586621679292326 :: Sing _f_6989586621679292326_a1bz3)
    (SProduct (sA_6989586621679292328 :: Sing a_6989586621679292328_a1bz4))
    = applySing
        (applySing
            (singFun2 @FmapSym0 sFmap) (singFun1 @ProductSym0 SProduct))
        (applySing _sf_6989586621679292326 sA_6989586621679292328)
instance STraversable First where
  sTraverse
    (_sf_6989586621679292337 :: Sing _f_6989586621679292337_a1bze)
    (SFirst (sA_6989586621679292345 :: Sing a_6989586621679292345_a1bzf))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @FirstSym0 SFirst))
        (applySing
            (applySing
              (singFun2 @TraverseSym0 sTraverse) _sf_6989586621679292337)
            sA_6989586621679292345)
instance STraversable Last where
  sTraverse
    (_sf_6989586621679292354 :: Sing _f_6989586621679292354_a1bzp)
    (SLast (sA_6989586621679292362 :: Sing a_6989586621679292362_a1bzq))
    = applySing
        (applySing (singFun2 @FmapSym0 sFmap) (singFun1 @LastSym0 SLast))
        (applySing
            (applySing
              (singFun2 @TraverseSym0 sTraverse) _sf_6989586621679292354)
            sA_6989586621679292362)
instance STraversable Identity where
  sTraverse
    (_sf_6989586621679292365 :: Sing _f_6989586621679292365_a1bzA)
    (SIdentity (sA_6989586621679292367 :: Sing a_6989586621679292367_a1bzB))
    = applySing
        (applySing
            (singFun2 @FmapSym0 sFmap) (singFun1 @IdentitySym0 SIdentity))
        (applySing _sf_6989586621679292365 sA_6989586621679292367)
instance SFunctor (StateL s_a1boj) where
  sFmap (sF :: Sing f_a1bAa) (SStateL (sK :: Sing k_a1bAb))
    = applySing
        (applySing (singFun2 @($@#@$) (%$)) (singFun1 @StateLSym0 SStateL))
        (singFun1
            @(LamCases_6989586621679292648Sym0 s_a1boj f_a1bAa k_a1bAb)
            (\cases
              (sS :: Sing s_a1bAe)
                -> let
                      sV ::
                        Sing @_ (Let6989586621679292651V s_a1boj s_a1bAe f_a1bAa k_a1bAb)
                      sS' ::
                        Sing @_ (Let6989586621679292651S' s_a1boj s_a1bAe f_a1bAa k_a1bAb)
                      sX_6989586621679292652 ::
                        Sing @_ (Let6989586621679292651X_6989586621679292652 s_a1boj s_a1bAe f_a1bAa k_a1bAb)
                      sV
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292659Sym0 s_a1boj s_a1bAe f_a1bAa k_a1bAb)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292656 :: Sing y_6989586621679292656_a1bAp))
                                    -> sY_6989586621679292656))
                            sX_6989586621679292652
                      sS'
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292666Sym0 s_a1boj s_a1bAe f_a1bAa k_a1bAb)
                              (\cases
                                  (STuple2 (sY_6989586621679292654 :: Sing y_6989586621679292654_a1bAw)
                                          _)
                                    -> sY_6989586621679292654))
                            sX_6989586621679292652
                      sX_6989586621679292652 = applySing sK sS
                    in
                      applySing
                        (applySing (singFun2 @Tuple2Sym0 STuple2) sS') (applySing sF sV)))
instance SApplicative (StateL s_a1bop) where
  sPure (sX :: Sing x_a1bBq)
    = applySing
        (singFun1 @StateLSym0 SStateL)
        (singFun1
            @(LamCases_6989586621679292725Sym0 s_a1bop x_a1bBq)
            (\cases
              (sS :: Sing s_a1bBt)
                -> applySing (applySing (singFun2 @Tuple2Sym0 STuple2) sS) sX))
  (%<*>)
    (SStateL (sKf :: Sing kf_a1bBG))
    (SStateL (sKv :: Sing kv_a1bBH))
    = applySing
        (applySing (singFun2 @($@#@$) (%$)) (singFun1 @StateLSym0 SStateL))
        (singFun1
            @(LamCases_6989586621679292742Sym0 s_a1bop kf_a1bBG kv_a1bBH)
            (\cases
              (sS :: Sing s_a1bBK)
                -> let
                      sV ::
                        Sing @_ (Let6989586621679292745V s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                      sS'' ::
                        Sing @_ (Let6989586621679292745S'' s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                      sX_6989586621679292752 ::
                        Sing @_ (Let6989586621679292745X_6989586621679292752 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                      sF ::
                        Sing @_ (Let6989586621679292745F s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                      sS' ::
                        Sing @_ (Let6989586621679292745S' s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                      sX_6989586621679292746 ::
                        Sing @_ (Let6989586621679292745X_6989586621679292746 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                      sV
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292759Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292756 :: Sing y_6989586621679292756_a1bC1))
                                    -> sY_6989586621679292756))
                            sX_6989586621679292752
                      sS''
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292766Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                              (\cases
                                  (STuple2 (sY_6989586621679292754 :: Sing y_6989586621679292754_a1bC8)
                                          _)
                                    -> sY_6989586621679292754))
                            sX_6989586621679292752
                      sX_6989586621679292752 = applySing sKv sS'
                      sF
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292774Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292750 :: Sing y_6989586621679292750_a1bCg))
                                    -> sY_6989586621679292750))
                            sX_6989586621679292746
                      sS'
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292781Sym0 s_a1bop s_a1bBK kf_a1bBG kv_a1bBH)
                              (\cases
                                  (STuple2 (sY_6989586621679292748 :: Sing y_6989586621679292748_a1bCn)
                                          _)
                                    -> sY_6989586621679292748))
                            sX_6989586621679292746
                      sX_6989586621679292746 = applySing sKf sS
                    in
                      applySing
                        (applySing (singFun2 @Tuple2Sym0 STuple2) sS'') (applySing sF sV)))
  sLiftA2
    (sF :: Sing f_a1bCH)
    (SStateL (sKx :: Sing kx_a1bCI))
    (SStateL (sKy :: Sing ky_a1bCJ))
    = applySing
        (applySing (singFun2 @($@#@$) (%$)) (singFun1 @StateLSym0 SStateL))
        (singFun1
            @(LamCases_6989586621679292806Sym0 s_a1bop f_a1bCH kx_a1bCI ky_a1bCJ)
            (\cases
              (sS :: Sing s_a1bCM)
                -> let
                      sY ::
                        Sing @_ (Let6989586621679292809Y s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                      sS'' ::
                        Sing @_ (Let6989586621679292809S'' s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                      sX_6989586621679292816 ::
                        Sing @_ (Let6989586621679292809X_6989586621679292816 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                      sX ::
                        Sing @_ (Let6989586621679292809X s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                      sS' ::
                        Sing @_ (Let6989586621679292809S' s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                      sX_6989586621679292810 ::
                        Sing @_ (Let6989586621679292809X_6989586621679292810 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                      sY
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292823Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292820 :: Sing y_6989586621679292820_a1bD3))
                                    -> sY_6989586621679292820))
                            sX_6989586621679292816
                      sS''
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292830Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                              (\cases
                                  (STuple2 (sY_6989586621679292818 :: Sing y_6989586621679292818_a1bDa)
                                          _)
                                    -> sY_6989586621679292818))
                            sX_6989586621679292816
                      sX_6989586621679292816 = applySing sKy sS'
                      sX
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292838Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292814 :: Sing y_6989586621679292814_a1bDi))
                                    -> sY_6989586621679292814))
                            sX_6989586621679292810
                      sS'
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292845Sym0 s_a1bop s_a1bCM f_a1bCH kx_a1bCI ky_a1bCJ)
                              (\cases
                                  (STuple2 (sY_6989586621679292812 :: Sing y_6989586621679292812_a1bDp)
                                          _)
                                    -> sY_6989586621679292812))
                            sX_6989586621679292810
                      sX_6989586621679292810 = applySing sKx sS
                    in
                      applySing
                        (applySing (singFun2 @Tuple2Sym0 STuple2) sS'')
                        (applySing (applySing sF sX) sY)))
instance SFunctor (StateR s_a1boH) where
  sFmap (sF :: Sing f_a1bDG) (SStateR (sK :: Sing k_a1bDH))
    = applySing
        (applySing (singFun2 @($@#@$) (%$)) (singFun1 @StateRSym0 SStateR))
        (singFun1
            @(LamCases_6989586621679292866Sym0 s_a1boH f_a1bDG k_a1bDH)
            (\cases
              (sS :: Sing s_a1bDK)
                -> let
                      sV ::
                        Sing @_ (Let6989586621679292869V s_a1boH s_a1bDK f_a1bDG k_a1bDH)
                      sS' ::
                        Sing @_ (Let6989586621679292869S' s_a1boH s_a1bDK f_a1bDG k_a1bDH)
                      sX_6989586621679292870 ::
                        Sing @_ (Let6989586621679292869X_6989586621679292870 s_a1boH s_a1bDK f_a1bDG k_a1bDH)
                      sV
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292877Sym0 s_a1boH s_a1bDK f_a1bDG k_a1bDH)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292874 :: Sing y_6989586621679292874_a1bDV))
                                    -> sY_6989586621679292874))
                            sX_6989586621679292870
                      sS'
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292884Sym0 s_a1boH s_a1bDK f_a1bDG k_a1bDH)
                              (\cases
                                  (STuple2 (sY_6989586621679292872 :: Sing y_6989586621679292872_a1bE2)
                                          _)
                                    -> sY_6989586621679292872))
                            sX_6989586621679292870
                      sX_6989586621679292870 = applySing sK sS
                    in
                      applySing
                        (applySing (singFun2 @Tuple2Sym0 STuple2) sS') (applySing sF sV)))
instance SApplicative (StateR s_a1boN) where
  sPure (sX :: Sing x_a1bEg)
    = applySing
        (singFun1 @StateRSym0 SStateR)
        (singFun1
            @(LamCases_6989586621679292901Sym0 s_a1boN x_a1bEg)
            (\cases
              (sS :: Sing s_a1bEj)
                -> applySing (applySing (singFun2 @Tuple2Sym0 STuple2) sS) sX))
  (%<*>)
    (SStateR (sKf :: Sing kf_a1bEw))
    (SStateR (sKv :: Sing kv_a1bEx))
    = applySing
        (applySing (singFun2 @($@#@$) (%$)) (singFun1 @StateRSym0 SStateR))
        (singFun1
            @(LamCases_6989586621679292918Sym0 s_a1boN kf_a1bEw kv_a1bEx)
            (\cases
              (sS :: Sing s_a1bEA)
                -> let
                      sF ::
                        Sing @_ (Let6989586621679292921F s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                      sS'' ::
                        Sing @_ (Let6989586621679292921S'' s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                      sX_6989586621679292928 ::
                        Sing @_ (Let6989586621679292921X_6989586621679292928 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                      sV ::
                        Sing @_ (Let6989586621679292921V s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                      sS' ::
                        Sing @_ (Let6989586621679292921S' s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                      sX_6989586621679292922 ::
                        Sing @_ (Let6989586621679292921X_6989586621679292922 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                      sF
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292935Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292932 :: Sing y_6989586621679292932_a1bER))
                                    -> sY_6989586621679292932))
                            sX_6989586621679292928
                      sS''
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292942Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                              (\cases
                                  (STuple2 (sY_6989586621679292930 :: Sing y_6989586621679292930_a1bEY)
                                          _)
                                    -> sY_6989586621679292930))
                            sX_6989586621679292928
                      sX_6989586621679292928 = applySing sKf sS'
                      sV
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292950Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292926 :: Sing y_6989586621679292926_a1bF6))
                                    -> sY_6989586621679292926))
                            sX_6989586621679292922
                      sS'
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292957Sym0 s_a1boN s_a1bEA kf_a1bEw kv_a1bEx)
                              (\cases
                                  (STuple2 (sY_6989586621679292924 :: Sing y_6989586621679292924_a1bFd)
                                          _)
                                    -> sY_6989586621679292924))
                            sX_6989586621679292922
                      sX_6989586621679292922 = applySing sKv sS
                    in
                      applySing
                        (applySing (singFun2 @Tuple2Sym0 STuple2) sS'') (applySing sF sV)))
  sLiftA2
    (sF :: Sing f_a1bFx)
    (SStateR (sKx :: Sing kx_a1bFy))
    (SStateR (sKy :: Sing ky_a1bFz))
    = applySing
        (applySing (singFun2 @($@#@$) (%$)) (singFun1 @StateRSym0 SStateR))
        (singFun1
            @(LamCases_6989586621679292982Sym0 s_a1boN f_a1bFx kx_a1bFy ky_a1bFz)
            (\cases
              (sS :: Sing s_a1bFC)
                -> let
                      sX ::
                        Sing @_ (Let6989586621679292985X s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                      sS'' ::
                        Sing @_ (Let6989586621679292985S'' s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                      sX_6989586621679292992 ::
                        Sing @_ (Let6989586621679292985X_6989586621679292992 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                      sY ::
                        Sing @_ (Let6989586621679292985Y s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                      sS' ::
                        Sing @_ (Let6989586621679292985S' s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                      sX_6989586621679292986 ::
                        Sing @_ (Let6989586621679292985X_6989586621679292986 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                      sX
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679292999Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292996 :: Sing y_6989586621679292996_a1bFT))
                                    -> sY_6989586621679292996))
                            sX_6989586621679292992
                      sS''
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679293006Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                              (\cases
                                  (STuple2 (sY_6989586621679292994 :: Sing y_6989586621679292994_a1bG0)
                                          _)
                                    -> sY_6989586621679292994))
                            sX_6989586621679292992
                      sX_6989586621679292992 = applySing sKx sS'
                      sY
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679293014Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                              (\cases
                                  (STuple2 _
                                          (sY_6989586621679292990 :: Sing y_6989586621679292990_a1bG8))
                                    -> sY_6989586621679292990))
                            sX_6989586621679292986
                      sS'
                        = applySing
                            (singFun1
                              @(LamCases_6989586621679293021Sym0 s_a1boN s_a1bFC f_a1bFx kx_a1bFy ky_a1bFz)
                              (\cases
                                  (STuple2 (sY_6989586621679292988 :: Sing y_6989586621679292988_a1bGf)
                                          _)
                                    -> sY_6989586621679292988))
                            sX_6989586621679292986
                      sX_6989586621679292986 = applySing sKy sS
                    in
                      applySing
                        (applySing (singFun2 @Tuple2Sym0 STuple2) sS'')
                        (applySing (applySing sF sX) sY)))
