{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}

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
-- Module      :  Control.Monad.Zip.Singletons
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted and singled versions of the 'MonadZip' type class.
--
----------------------------------------------------------------------------

module Control.Monad.Zip.Singletons (
  PMonadZip(..), SMonadZip(..),

  -- * Defunctionalization symbols
  MzipSym0, MzipSym1, MzipSym2,
  MzipWithSym0, MzipWithSym1, MzipWithSym2, MzipWithSym3,
  MunzipSym0, MunzipSym1,
  ) where

import Control.Monad.Singletons.Internal
import Data.Functor.Identity
import Data.Functor.Identity.Singletons
import Data.Kind
import Data.List.Singletons
       ( ZipSym0, ZipWithSym0, UnzipSym0
       , sZip,    sZipWith,    sUnzip )
import Data.Monoid
import Data.Monoid.Singletons ()
import Data.Proxy
import Data.Proxy.Singletons
import Data.Singletons.Base.Instances
import Data.Singletons.TH
import Data.Tuple.Singletons

type MzipSym0 :: forall (m_a1LGi :: Type -> Type)
                            a_a1LGj
                            b_a1LGk. (~>) (m_a1LGi a_a1LGj) ((~>) (m_a1LGi b_a1LGk) (m_a1LGi (a_a1LGj,
                                                                                              b_a1LGk)))
data MzipSym0 :: (~>) (m_a1LGi a_a1LGj) ((~>) (m_a1LGi b_a1LGk) (m_a1LGi (a_a1LGj,
                                                                          b_a1LGk)))
  where
    MzipSym0KindInference :: SameKind (Apply MzipSym0 arg_a1LHs) (MzipSym1 arg_a1LHs) =>
                              MzipSym0 a6989586621679431483
type instance Apply @(m_a1LGi a_a1LGj) @((~>) (m_a1LGi b_a1LGk) (m_a1LGi (a_a1LGj,
                                                                          b_a1LGk))) MzipSym0 a6989586621679431483 = MzipSym1 a6989586621679431483
instance SuppressUnusedWarnings MzipSym0 where
  suppressUnusedWarnings = snd ((,) MzipSym0KindInference ())
type MzipSym1 :: forall (m_a1LGi :: Type -> Type)
                        a_a1LGj
                        b_a1LGk. m_a1LGi a_a1LGj
                                  -> (~>) (m_a1LGi b_a1LGk) (m_a1LGi (a_a1LGj, b_a1LGk))
data MzipSym1 (a6989586621679431483 :: m_a1LGi a_a1LGj) :: (~>) (m_a1LGi b_a1LGk) (m_a1LGi (a_a1LGj,
                                                                                            b_a1LGk))
  where
    MzipSym1KindInference :: SameKind (Apply (MzipSym1 a6989586621679431483) arg_a1LHs) (MzipSym2 a6989586621679431483 arg_a1LHs) =>
                              MzipSym1 a6989586621679431483 a6989586621679431484
type instance Apply @(m_a1LGi b_a1LGk) @(m_a1LGi (a_a1LGj,
                                                  b_a1LGk)) (MzipSym1 a6989586621679431483) a6989586621679431484 = Mzip a6989586621679431483 a6989586621679431484
instance SuppressUnusedWarnings (MzipSym1 a6989586621679431483) where
  suppressUnusedWarnings = snd ((,) MzipSym1KindInference ())
type MzipSym2 :: forall (m_a1LGi :: Type -> Type)
                        a_a1LGj
                        b_a1LGk. m_a1LGi a_a1LGj
                                  -> m_a1LGi b_a1LGk -> m_a1LGi (a_a1LGj, b_a1LGk)
type family MzipSym2 @(m_a1LGi :: Type
                                  -> Type) @a_a1LGj @b_a1LGk (a6989586621679431483 :: m_a1LGi a_a1LGj) (a6989586621679431484 :: m_a1LGi b_a1LGk) :: m_a1LGi (a_a1LGj,
                                                                                                                                                              b_a1LGk) where
  MzipSym2 a6989586621679431483 a6989586621679431484 = Mzip a6989586621679431483 a6989586621679431484
type MzipWithSym0 :: forall (m_a1LGi :: Type -> Type)
                            a_a1LGl
                            b_a1LGm
                            c_a1LGn. (~>) ((~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) ((~>) (m_a1LGi a_a1LGl) ((~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn)))
data MzipWithSym0 :: (~>) ((~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) ((~>) (m_a1LGi a_a1LGl) ((~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn)))
  where
    MzipWithSym0KindInference :: SameKind (Apply MzipWithSym0 arg_a1LHy) (MzipWithSym1 arg_a1LHy) =>
                                  MzipWithSym0 a6989586621679431489
type instance Apply @((~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) @((~>) (m_a1LGi a_a1LGl) ((~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn))) MzipWithSym0 a6989586621679431489 = MzipWithSym1 a6989586621679431489
instance SuppressUnusedWarnings MzipWithSym0 where
  suppressUnusedWarnings = snd ((,) MzipWithSym0KindInference ())
type MzipWithSym1 :: forall (m_a1LGi :: Type -> Type)
                            a_a1LGl
                            b_a1LGm
                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                      -> (~>) (m_a1LGi a_a1LGl) ((~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn))
data MzipWithSym1 (a6989586621679431489 :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) :: (~>) (m_a1LGi a_a1LGl) ((~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn))
  where
    MzipWithSym1KindInference :: SameKind (Apply (MzipWithSym1 a6989586621679431489) arg_a1LHy) (MzipWithSym2 a6989586621679431489 arg_a1LHy) =>
                                  MzipWithSym1 a6989586621679431489 a6989586621679431490
type instance Apply @(m_a1LGi a_a1LGl) @((~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn)) (MzipWithSym1 a6989586621679431489) a6989586621679431490 = MzipWithSym2 a6989586621679431489 a6989586621679431490
instance SuppressUnusedWarnings (MzipWithSym1 a6989586621679431489) where
  suppressUnusedWarnings = snd ((,) MzipWithSym1KindInference ())
type MzipWithSym2 :: forall (m_a1LGi :: Type -> Type)
                            a_a1LGl
                            b_a1LGm
                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                      -> m_a1LGi a_a1LGl
                                        -> (~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn)
data MzipWithSym2 (a6989586621679431489 :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a6989586621679431490 :: m_a1LGi a_a1LGl) :: (~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn)
  where
    MzipWithSym2KindInference :: SameKind (Apply (MzipWithSym2 a6989586621679431489 a6989586621679431490) arg_a1LHy) (MzipWithSym3 a6989586621679431489 a6989586621679431490 arg_a1LHy) =>
                                  MzipWithSym2 a6989586621679431489 a6989586621679431490 a6989586621679431491
type instance Apply @(m_a1LGi b_a1LGm) @(m_a1LGi c_a1LGn) (MzipWithSym2 a6989586621679431489 a6989586621679431490) a6989586621679431491 = MzipWith a6989586621679431489 a6989586621679431490 a6989586621679431491
instance SuppressUnusedWarnings (MzipWithSym2 a6989586621679431489 a6989586621679431490) where
  suppressUnusedWarnings = snd ((,) MzipWithSym2KindInference ())
type MzipWithSym3 :: forall (m_a1LGi :: Type -> Type)
                            a_a1LGl
                            b_a1LGm
                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                      -> m_a1LGi a_a1LGl -> m_a1LGi b_a1LGm -> m_a1LGi c_a1LGn
type family MzipWithSym3 @(m_a1LGi :: Type
                                      -> Type) @a_a1LGl @b_a1LGm @c_a1LGn (a6989586621679431489 :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a6989586621679431490 :: m_a1LGi a_a1LGl) (a6989586621679431491 :: m_a1LGi b_a1LGm) :: m_a1LGi c_a1LGn where
  MzipWithSym3 a6989586621679431489 a6989586621679431490 a6989586621679431491 = MzipWith a6989586621679431489 a6989586621679431490 a6989586621679431491
type MunzipSym0 :: forall (m_a1LGi :: Type -> Type)
                          a_a1LGo
                          b_a1LGp. (~>) (m_a1LGi (a_a1LGo, b_a1LGp)) (m_a1LGi a_a1LGo,
                                                                      m_a1LGi b_a1LGp)
data MunzipSym0 :: (~>) (m_a1LGi (a_a1LGo,
                                  b_a1LGp)) (m_a1LGi a_a1LGo, m_a1LGi b_a1LGp)
  where
    MunzipSym0KindInference :: SameKind (Apply MunzipSym0 arg_a1LHD) (MunzipSym1 arg_a1LHD) =>
                                MunzipSym0 a6989586621679431494
type instance Apply @(m_a1LGi (a_a1LGo,
                                b_a1LGp)) @(m_a1LGi a_a1LGo,
                                            m_a1LGi b_a1LGp) MunzipSym0 a6989586621679431494 = Munzip a6989586621679431494
instance SuppressUnusedWarnings MunzipSym0 where
  suppressUnusedWarnings = snd ((,) MunzipSym0KindInference ())
type MunzipSym1 :: forall (m_a1LGi :: Type -> Type)
                          a_a1LGo
                          b_a1LGp. m_a1LGi (a_a1LGo, b_a1LGp)
                                    -> (m_a1LGi a_a1LGo, m_a1LGi b_a1LGp)
type family MunzipSym1 @(m_a1LGi :: Type
                                    -> Type) @a_a1LGo @b_a1LGp (a6989586621679431494 :: m_a1LGi (a_a1LGo,
                                                                                                  b_a1LGp)) :: (m_a1LGi a_a1LGo,
                                                                                                                m_a1LGi b_a1LGp) where
  MunzipSym1 a6989586621679431494 = Munzip a6989586621679431494
type Mzip_6989586621679431497 :: forall (m_a1LGi :: Type -> Type)
                                        a_a1LGj
                                        b_a1LGk. m_a1LGi a_a1LGj
                                                  -> m_a1LGi b_a1LGk
                                                    -> m_a1LGi (a_a1LGj, b_a1LGk)
type family Mzip_6989586621679431497 @(m_a1LGi :: Type
                                                  -> Type) @a_a1LGj @b_a1LGk (a_a1LHN :: m_a1LGi a_a1LGj) (a_a1LHO :: m_a1LGi b_a1LGk) :: m_a1LGi (a_a1LGj,
                                                                                                                                                    b_a1LGk) where
  Mzip_6989586621679431497 @m_a1LGi @a_a1LGj @b_a1LGk (a_6989586621679431499_a1LHS :: m_a1LGi a_a1LGj) (a_6989586621679431501_a1LHT :: m_a1LGi b_a1LGk) = Apply (Apply (Apply MzipWithSym0 Tuple2Sym0) a_6989586621679431499_a1LHS) a_6989586621679431501_a1LHT
type MzipWith_6989586621679431513 :: forall (m_a1LGi :: Type
                                                        -> Type)
                                            a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> m_a1LGi a_a1LGl
                                                        -> m_a1LGi b_a1LGm -> m_a1LGi c_a1LGn
type family MzipWith_6989586621679431513 @(m_a1LGi :: Type
                                                      -> Type) @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LHZ :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LI0 :: m_a1LGi a_a1LGl) (a_a1LI1 :: m_a1LGi b_a1LGm) :: m_a1LGi c_a1LGn where
  MzipWith_6989586621679431513 @m_a1LGi @a_a1LGl @b_a1LGm @c_a1LGn (f_a1LI6 :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (ma_a1LI7 :: m_a1LGi a_a1LGl) (mb_a1LI8 :: m_a1LGi b_a1LGm) = Apply (Apply LiftMSym0 (Apply UncurrySym0 f_a1LI6)) (Apply (Apply MzipSym0 ma_a1LI7) mb_a1LI8)
type Munzip_6989586621679431526 :: forall (m_a1LGi :: Type -> Type)
                                          a_a1LGo
                                          b_a1LGp. m_a1LGi (a_a1LGo, b_a1LGp)
                                                    -> (m_a1LGi a_a1LGo, m_a1LGi b_a1LGp)
type family Munzip_6989586621679431526 @(m_a1LGi :: Type
                                                    -> Type) @a_a1LGo @b_a1LGp (a_a1LIc :: m_a1LGi (a_a1LGo,
                                                                                                    b_a1LGp)) :: (m_a1LGi a_a1LGo,
                                                                                                                  m_a1LGi b_a1LGp) where
  Munzip_6989586621679431526 @m_a1LGi @a_a1LGo @b_a1LGp (mab_a1LIf :: m_a1LGi (a_a1LGo,
                                                                                b_a1LGp)) = Apply (Apply Tuple2Sym0 (Apply (Apply LiftMSym0 FstSym0) mab_a1LIf)) (Apply (Apply LiftMSym0 SndSym0) mab_a1LIf)
type PMonadZip :: (Type -> Type) -> Constraint
class PMonadZip m_a1LGi where
  type family Mzip (arg_a1LHq :: m_a1LGi a_a1LGj) (arg_a1LHr :: m_a1LGi b_a1LGk) :: m_a1LGi (a_a1LGj,
                                                                                              b_a1LGk)
  type family MzipWith (arg_a1LHv :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (arg_a1LHw :: m_a1LGi a_a1LGl) (arg_a1LHx :: m_a1LGi b_a1LGm) :: m_a1LGi c_a1LGn
  type family Munzip (arg_a1LHC :: m_a1LGi (a_a1LGo,
                                            b_a1LGp)) :: (m_a1LGi a_a1LGo, m_a1LGi b_a1LGp)
  type Mzip a_a1LHF a_a1LHG = Mzip_6989586621679431497 a_a1LHF a_a1LHG
  type MzipWith a_a1LHU a_a1LHV a_a1LHW = MzipWith_6989586621679431513 a_a1LHU a_a1LHV a_a1LHW
  type Munzip a_a1LI9 = Munzip_6989586621679431526 a_a1LI9
type Mzip_6989586621679431534 :: forall a_a1LGj b_a1LGk. [a_a1LGj]
                                                          -> [b_a1LGk] -> [(a_a1LGj, b_a1LGk)]
type family Mzip_6989586621679431534 @a_a1LGj @b_a1LGk (a_a1LIo :: [a_a1LGj]) (a_a1LIp :: [b_a1LGk]) :: [(a_a1LGj,
                                                                                                          b_a1LGk)] where
  Mzip_6989586621679431534 @a_a1LGj @b_a1LGk a_6989586621679431536_a1LIt a_6989586621679431538_a1LIu = Apply (Apply ZipSym0 a_6989586621679431536_a1LIt) a_6989586621679431538_a1LIu
type MzipWith_6989586621679431550 :: forall a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> [a_a1LGl] -> [b_a1LGm] -> [c_a1LGn]
type family MzipWith_6989586621679431550 @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LIG :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LIH :: [a_a1LGl]) (a_a1LII :: [b_a1LGm]) :: [c_a1LGn] where
  MzipWith_6989586621679431550 @a_a1LGl @b_a1LGm @c_a1LGn a_6989586621679431552_a1LIN a_6989586621679431554_a1LIO a_6989586621679431556_a1LIP = Apply (Apply (Apply ZipWithSym0 a_6989586621679431552_a1LIN) a_6989586621679431554_a1LIO) a_6989586621679431556_a1LIP
type Munzip_6989586621679431569 :: forall a_a1LGo
                                          b_a1LGp. [(a_a1LGo, b_a1LGp)]
                                                    -> ([a_a1LGo], [b_a1LGp])
type family Munzip_6989586621679431569 @a_a1LGo @b_a1LGp (a_a1LIV :: [(a_a1LGo,
                                                                        b_a1LGp)]) :: ([a_a1LGo],
                                                                                      [b_a1LGp]) where
  Munzip_6989586621679431569 @a_a1LGo @b_a1LGp a_6989586621679431571_a1LIY = Apply UnzipSym0 a_6989586621679431571_a1LIY
instance PMonadZip [] where
  type Mzip a_a1LIg a_a1LIh = Mzip_6989586621679431534 a_a1LIg a_a1LIh
  type MzipWith a_a1LIv a_a1LIw a_a1LIx = MzipWith_6989586621679431550 a_a1LIv a_a1LIw a_a1LIx
  type Munzip a_a1LIQ = Munzip_6989586621679431569 a_a1LIQ
type MzipWith_6989586621679431580 :: forall a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> Identity a_a1LGl
                                                        -> Identity b_a1LGm -> Identity c_a1LGn
type family MzipWith_6989586621679431580 @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LJa :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LJb :: Identity a_a1LGl) (a_a1LJc :: Identity b_a1LGm) :: Identity c_a1LGn where
  MzipWith_6989586621679431580 @a_a1LGl @b_a1LGm @c_a1LGn a_6989586621679431582_a1LJh a_6989586621679431584_a1LJi a_6989586621679431586_a1LJj = Apply (Apply (Apply LiftM2Sym0 a_6989586621679431582_a1LJh) a_6989586621679431584_a1LJi) a_6989586621679431586_a1LJj
type Munzip_6989586621679431599 :: forall a_a1LGo
                                          b_a1LGp. Identity (a_a1LGo, b_a1LGp)
                                                    -> (Identity a_a1LGo, Identity b_a1LGp)
type family Munzip_6989586621679431599 @a_a1LGo @b_a1LGp (a_a1LJn :: Identity (a_a1LGo,
                                                                                b_a1LGp)) :: (Identity a_a1LGo,
                                                                                              Identity b_a1LGp) where
  Munzip_6989586621679431599 @a_a1LGo @b_a1LGp ('Identity '(a_a1LJq,
                                                            b_a1LJr)) = Apply (Apply Tuple2Sym0 (Apply IdentitySym0 a_a1LJq)) (Apply IdentitySym0 b_a1LJr)
instance PMonadZip Identity where
  type MzipWith a_a1LIZ a_a1LJ0 a_a1LJ1 = MzipWith_6989586621679431580 a_a1LIZ a_a1LJ0 a_a1LJ1
  type Munzip a_a1LJk = Munzip_6989586621679431599 a_a1LJk
type MzipWith_6989586621679431609 :: forall a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> Dual a_a1LGl
                                                        -> Dual b_a1LGm -> Dual c_a1LGn
type family MzipWith_6989586621679431609 @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LJD :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LJE :: Dual a_a1LGl) (a_a1LJF :: Dual b_a1LGm) :: Dual c_a1LGn where
  MzipWith_6989586621679431609 @a_a1LGl @b_a1LGm @c_a1LGn a_6989586621679431611_a1LJK a_6989586621679431613_a1LJL a_6989586621679431615_a1LJM = Apply (Apply (Apply LiftM2Sym0 a_6989586621679431611_a1LJK) a_6989586621679431613_a1LJL) a_6989586621679431615_a1LJM
instance PMonadZip Dual where
  type MzipWith a_a1LJs a_a1LJt a_a1LJu = MzipWith_6989586621679431609 a_a1LJs a_a1LJt a_a1LJu
type MzipWith_6989586621679431630 :: forall a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> Sum a_a1LGl
                                                        -> Sum b_a1LGm -> Sum c_a1LGn
type family MzipWith_6989586621679431630 @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LJY :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LJZ :: Sum a_a1LGl) (a_a1LK0 :: Sum b_a1LGm) :: Sum c_a1LGn where
  MzipWith_6989586621679431630 @a_a1LGl @b_a1LGm @c_a1LGn a_6989586621679431632_a1LK5 a_6989586621679431634_a1LK6 a_6989586621679431636_a1LK7 = Apply (Apply (Apply LiftM2Sym0 a_6989586621679431632_a1LK5) a_6989586621679431634_a1LK6) a_6989586621679431636_a1LK7
instance PMonadZip Sum where
  type MzipWith a_a1LJN a_a1LJO a_a1LJP = MzipWith_6989586621679431630 a_a1LJN a_a1LJO a_a1LJP
type MzipWith_6989586621679431651 :: forall a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> Product a_a1LGl
                                                        -> Product b_a1LGm -> Product c_a1LGn
type family MzipWith_6989586621679431651 @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LKj :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LKk :: Product a_a1LGl) (a_a1LKl :: Product b_a1LGm) :: Product c_a1LGn where
  MzipWith_6989586621679431651 @a_a1LGl @b_a1LGm @c_a1LGn a_6989586621679431653_a1LKq a_6989586621679431655_a1LKr a_6989586621679431657_a1LKs = Apply (Apply (Apply LiftM2Sym0 a_6989586621679431653_a1LKq) a_6989586621679431655_a1LKr) a_6989586621679431657_a1LKs
instance PMonadZip Product where
  type MzipWith a_a1LK8 a_a1LK9 a_a1LKa = MzipWith_6989586621679431651 a_a1LK8 a_a1LK9 a_a1LKa
type MzipWith_6989586621679431672 :: forall a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> Maybe a_a1LGl
                                                        -> Maybe b_a1LGm -> Maybe c_a1LGn
type family MzipWith_6989586621679431672 @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LKE :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LKF :: Maybe a_a1LGl) (a_a1LKG :: Maybe b_a1LGm) :: Maybe c_a1LGn where
  MzipWith_6989586621679431672 @a_a1LGl @b_a1LGm @c_a1LGn a_6989586621679431674_a1LKL a_6989586621679431676_a1LKM a_6989586621679431678_a1LKN = Apply (Apply (Apply LiftM2Sym0 a_6989586621679431674_a1LKL) a_6989586621679431676_a1LKM) a_6989586621679431678_a1LKN
instance PMonadZip Maybe where
  type MzipWith a_a1LKt a_a1LKu a_a1LKv = MzipWith_6989586621679431672 a_a1LKt a_a1LKu a_a1LKv
type MzipWith_6989586621679431693 :: forall a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> First a_a1LGl
                                                        -> First b_a1LGm -> First c_a1LGn
type family MzipWith_6989586621679431693 @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LKZ :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LL0 :: First a_a1LGl) (a_a1LL1 :: First b_a1LGm) :: First c_a1LGn where
  MzipWith_6989586621679431693 @a_a1LGl @b_a1LGm @c_a1LGn a_6989586621679431695_a1LL6 a_6989586621679431697_a1LL7 a_6989586621679431699_a1LL8 = Apply (Apply (Apply LiftM2Sym0 a_6989586621679431695_a1LL6) a_6989586621679431697_a1LL7) a_6989586621679431699_a1LL8
instance PMonadZip First where
  type MzipWith a_a1LKO a_a1LKP a_a1LKQ = MzipWith_6989586621679431693 a_a1LKO a_a1LKP a_a1LKQ
type MzipWith_6989586621679431714 :: forall a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> Last a_a1LGl
                                                        -> Last b_a1LGm -> Last c_a1LGn
type family MzipWith_6989586621679431714 @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LLk :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LLl :: Last a_a1LGl) (a_a1LLm :: Last b_a1LGm) :: Last c_a1LGn where
  MzipWith_6989586621679431714 @a_a1LGl @b_a1LGm @c_a1LGn a_6989586621679431716_a1LLr a_6989586621679431718_a1LLs a_6989586621679431720_a1LLt = Apply (Apply (Apply LiftM2Sym0 a_6989586621679431716_a1LLr) a_6989586621679431718_a1LLs) a_6989586621679431720_a1LLt
instance PMonadZip Last where
  type MzipWith a_a1LL9 a_a1LLa a_a1LLb = MzipWith_6989586621679431714 a_a1LL9 a_a1LLa a_a1LLb
type MzipWith_6989586621679431735 :: forall a_a1LGl
                                            b_a1LGm
                                            c_a1LGn. (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                                      -> Proxy a_a1LGl
                                                        -> Proxy b_a1LGm -> Proxy c_a1LGn
type family MzipWith_6989586621679431735 @a_a1LGl @b_a1LGm @c_a1LGn (a_a1LLz :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (a_a1LLA :: Proxy a_a1LGl) (a_a1LLB :: Proxy b_a1LGm) :: Proxy c_a1LGn where
  MzipWith_6989586621679431735 @a_a1LGl @b_a1LGm @c_a1LGn _ _ _ = ProxySym0
instance PMonadZip Proxy where
  type MzipWith a_a1LLu a_a1LLv a_a1LLw = MzipWith_6989586621679431735 a_a1LLu a_a1LLv a_a1LLw
class SMonad m_a1LGi => SMonadZip m_a1LGi where
  sMzip ::
    (forall (t_a1LLG :: m_a1LGi a_a1LGj) (t_a1LLH :: m_a1LGi b_a1LGk).
      Sing t_a1LLG
      -> Sing t_a1LLH
        -> Sing (Mzip t_a1LLG t_a1LLH :: m_a1LGi (a_a1LGj,
                                                  b_a1LGk)) :: Type)
  sMzipWith ::
    (forall (t_a1LLL :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn))
            (t_a1LLM :: m_a1LGi a_a1LGl)
            (t_a1LLN :: m_a1LGi b_a1LGm).
      Sing t_a1LLL
      -> Sing t_a1LLM
        -> Sing t_a1LLN
            -> Sing (MzipWith t_a1LLL t_a1LLM t_a1LLN :: m_a1LGi c_a1LGn) :: Type)
  sMunzip ::
    (forall (t_a1LLV :: m_a1LGi (a_a1LGo, b_a1LGp)).
      Sing t_a1LLV
      -> Sing (Munzip t_a1LLV :: (m_a1LGi a_a1LGo,
                                  m_a1LGi b_a1LGp)) :: Type)
  default sMzip ::
            (forall (t_a1LLG :: m_a1LGi a_a1LGj) (t_a1LLH :: m_a1LGi b_a1LGk).
              ((Mzip t_a1LLG t_a1LLH :: m_a1LGi (a_a1LGj, b_a1LGk))
              ~ Mzip_6989586621679431497 t_a1LLG t_a1LLH) =>
              Sing t_a1LLG
              -> Sing t_a1LLH
                -> Sing (Mzip t_a1LLG t_a1LLH :: m_a1LGi (a_a1LGj,
                                                          b_a1LGk)) :: Type)
  default sMzipWith ::
            (forall (t_a1LLL :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn))
                    (t_a1LLM :: m_a1LGi a_a1LGl)
                    (t_a1LLN :: m_a1LGi b_a1LGm).
              ((MzipWith t_a1LLL t_a1LLM t_a1LLN :: m_a1LGi c_a1LGn)
              ~ MzipWith_6989586621679431513 t_a1LLL t_a1LLM t_a1LLN) =>
              Sing t_a1LLL
              -> Sing t_a1LLM
                -> Sing t_a1LLN
                    -> Sing (MzipWith t_a1LLL t_a1LLM t_a1LLN :: m_a1LGi c_a1LGn) :: Type)
  default sMunzip ::
            (forall (t_a1LLV :: m_a1LGi (a_a1LGo, b_a1LGp)).
              ((Munzip t_a1LLV :: (m_a1LGi a_a1LGo, m_a1LGi b_a1LGp))
              ~ Munzip_6989586621679431526 t_a1LLV) =>
              Sing t_a1LLV
              -> Sing (Munzip t_a1LLV :: (m_a1LGi a_a1LGo,
                                          m_a1LGi b_a1LGp)) :: Type)
  sMzip
    (sA_6989586621679431499 :: Sing a_6989586621679431499_a1LHS)
    (sA_6989586621679431501 :: Sing a_6989586621679431501_a1LHT)
    = applySing
        (applySing
            (applySing
              (singFun3 @MzipWithSym0 sMzipWith) (singFun2 @Tuple2Sym0 STuple2))
            sA_6989586621679431499)
        sA_6989586621679431501
  sMzipWith
    (sF :: Sing f_a1LI6)
    (sMa :: Sing ma_a1LI7)
    (sMb :: Sing mb_a1LI8)
    = applySing
        (applySing
            (singFun2 @LiftMSym0 sLiftM)
            (applySing (singFun2 @UncurrySym0 sUncurry) sF))
        (applySing (applySing (singFun2 @MzipSym0 sMzip) sMa) sMb)
  sMunzip (sMab :: Sing mab_a1LIf)
    = applySing
        (applySing
            (singFun2 @Tuple2Sym0 STuple2)
            (applySing
              (applySing (singFun2 @LiftMSym0 sLiftM) (singFun1 @FstSym0 sFst))
              sMab))
        (applySing
            (applySing (singFun2 @LiftMSym0 sLiftM) (singFun1 @SndSym0 sSnd))
            sMab)
instance SMonadZip [] where
  sMzip
    (sA_6989586621679431536 :: Sing a_6989586621679431536_a1LIt)
    (sA_6989586621679431538 :: Sing a_6989586621679431538_a1LIu)
    = applySing
        (applySing (singFun2 @ZipSym0 sZip) sA_6989586621679431536)
        sA_6989586621679431538
  sMzipWith
    (sA_6989586621679431552 :: Sing a_6989586621679431552_a1LIN)
    (sA_6989586621679431554 :: Sing a_6989586621679431554_a1LIO)
    (sA_6989586621679431556 :: Sing a_6989586621679431556_a1LIP)
    = applySing
        (applySing
            (applySing (singFun3 @ZipWithSym0 sZipWith) sA_6989586621679431552)
            sA_6989586621679431554)
        sA_6989586621679431556
  sMunzip
    (sA_6989586621679431571 :: Sing a_6989586621679431571_a1LIY)
    = applySing (singFun1 @UnzipSym0 sUnzip) sA_6989586621679431571
instance SMonadZip Identity where
  sMzipWith
    (sA_6989586621679431582 :: Sing a_6989586621679431582_a1LJh)
    (sA_6989586621679431584 :: Sing a_6989586621679431584_a1LJi)
    (sA_6989586621679431586 :: Sing a_6989586621679431586_a1LJj)
    = applySing
        (applySing
            (applySing (singFun3 @LiftM2Sym0 sLiftM2) sA_6989586621679431582)
            sA_6989586621679431584)
        sA_6989586621679431586
  sMunzip
    (SIdentity (STuple2 (sA :: Sing a_a1LJq) (sB :: Sing b_a1LJr)))
    = applySing
        (applySing
            (singFun2 @Tuple2Sym0 STuple2)
            (applySing (singFun1 @IdentitySym0 SIdentity) sA))
        (applySing (singFun1 @IdentitySym0 SIdentity) sB)
instance SMonadZip Dual where
  sMzipWith
    (sA_6989586621679431611 :: Sing a_6989586621679431611_a1LJK)
    (sA_6989586621679431613 :: Sing a_6989586621679431613_a1LJL)
    (sA_6989586621679431615 :: Sing a_6989586621679431615_a1LJM)
    = applySing
        (applySing
            (applySing (singFun3 @LiftM2Sym0 sLiftM2) sA_6989586621679431611)
            sA_6989586621679431613)
        sA_6989586621679431615
instance SMonadZip Sum where
  sMzipWith
    (sA_6989586621679431632 :: Sing a_6989586621679431632_a1LK5)
    (sA_6989586621679431634 :: Sing a_6989586621679431634_a1LK6)
    (sA_6989586621679431636 :: Sing a_6989586621679431636_a1LK7)
    = applySing
        (applySing
            (applySing (singFun3 @LiftM2Sym0 sLiftM2) sA_6989586621679431632)
            sA_6989586621679431634)
        sA_6989586621679431636
instance SMonadZip Product where
  sMzipWith
    (sA_6989586621679431653 :: Sing a_6989586621679431653_a1LKq)
    (sA_6989586621679431655 :: Sing a_6989586621679431655_a1LKr)
    (sA_6989586621679431657 :: Sing a_6989586621679431657_a1LKs)
    = applySing
        (applySing
            (applySing (singFun3 @LiftM2Sym0 sLiftM2) sA_6989586621679431653)
            sA_6989586621679431655)
        sA_6989586621679431657
instance SMonadZip Maybe where
  sMzipWith
    (sA_6989586621679431674 :: Sing a_6989586621679431674_a1LKL)
    (sA_6989586621679431676 :: Sing a_6989586621679431676_a1LKM)
    (sA_6989586621679431678 :: Sing a_6989586621679431678_a1LKN)
    = applySing
        (applySing
            (applySing (singFun3 @LiftM2Sym0 sLiftM2) sA_6989586621679431674)
            sA_6989586621679431676)
        sA_6989586621679431678
instance SMonadZip First where
  sMzipWith
    (sA_6989586621679431695 :: Sing a_6989586621679431695_a1LL6)
    (sA_6989586621679431697 :: Sing a_6989586621679431697_a1LL7)
    (sA_6989586621679431699 :: Sing a_6989586621679431699_a1LL8)
    = applySing
        (applySing
            (applySing (singFun3 @LiftM2Sym0 sLiftM2) sA_6989586621679431695)
            sA_6989586621679431697)
        sA_6989586621679431699
instance SMonadZip Last where
  sMzipWith
    (sA_6989586621679431716 :: Sing a_6989586621679431716_a1LLr)
    (sA_6989586621679431718 :: Sing a_6989586621679431718_a1LLs)
    (sA_6989586621679431720 :: Sing a_6989586621679431720_a1LLt)
    = applySing
        (applySing
            (applySing (singFun3 @LiftM2Sym0 sLiftM2) sA_6989586621679431716)
            sA_6989586621679431718)
        sA_6989586621679431720
instance SMonadZip Proxy where
  sMzipWith _ _ _ = SProxy
type SMonadZip :: (Type -> Type) -> Constraint
instance SMonadZip m_a1LGi =>
          SingI (MzipSym0 :: (~>) (m_a1LGi a_a1LGj) ((~>) (m_a1LGi b_a1LGk) (m_a1LGi (a_a1LGj,
                                                                                      b_a1LGk)))) where
  sing = singFun2 @MzipSym0 sMzip
instance (SMonadZip m_a1LGi, SingI d_a1LLI) =>
          SingI (MzipSym1 (d_a1LLI :: m_a1LGi a_a1LGj) :: (~>) (m_a1LGi b_a1LGk) (m_a1LGi (a_a1LGj,
                                                                                          b_a1LGk))) where
  sing
    = singFun1
        @(MzipSym1 (d_a1LLI :: m_a1LGi a_a1LGj)) (sMzip (sing @d_a1LLI))
instance SMonadZip m_a1LGi =>
          SingI1 (MzipSym1 :: m_a1LGi a_a1LGj
                              -> (~>) (m_a1LGi b_a1LGk) (m_a1LGi (a_a1LGj, b_a1LGk))) where
  liftSing (s_a1LLK :: Sing (d_a1LLI :: m_a1LGi a_a1LGj))
    = singFun1 @(MzipSym1 (d_a1LLI :: m_a1LGi a_a1LGj)) (sMzip s_a1LLK)
instance SMonadZip m_a1LGi =>
          SingI (MzipWithSym0 :: (~>) ((~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) ((~>) (m_a1LGi a_a1LGl) ((~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn)))) where
  sing = singFun3 @MzipWithSym0 sMzipWith
instance (SMonadZip m_a1LGi, SingI d_a1LLO) =>
          SingI (MzipWithSym1 (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) :: (~>) (m_a1LGi a_a1LGl) ((~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn))) where
  sing
    = singFun2
        @(MzipWithSym1 (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)))
        (sMzipWith (sing @d_a1LLO))
instance SMonadZip m_a1LGi =>
          SingI1 (MzipWithSym1 :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                  -> (~>) (m_a1LGi a_a1LGl) ((~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn))) where
  liftSing
    (s_a1LLU :: Sing (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)))
    = singFun2
        @(MzipWithSym1 (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)))
        (sMzipWith s_a1LLU)
instance (SMonadZip m_a1LGi, SingI d_a1LLO, SingI d_a1LLP) =>
          SingI (MzipWithSym2 (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (d_a1LLP :: m_a1LGi a_a1LGl) :: (~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn)) where
  sing
    = singFun1
        @(MzipWithSym2 (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (d_a1LLP :: m_a1LGi a_a1LGl))
        (sMzipWith (sing @d_a1LLO) (sing @d_a1LLP))
instance (SMonadZip m_a1LGi, SingI d_a1LLO) =>
          SingI1 (MzipWithSym2 (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) :: m_a1LGi a_a1LGl
                                                                                  -> (~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn)) where
  liftSing (s_a1LLR :: Sing (d_a1LLP :: m_a1LGi a_a1LGl))
    = singFun1
        @(MzipWithSym2 (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (d_a1LLP :: m_a1LGi a_a1LGl))
        (sMzipWith (sing @d_a1LLO) s_a1LLR)
instance SMonadZip m_a1LGi =>
          SingI2 (MzipWithSym2 :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)
                                  -> m_a1LGi a_a1LGl
                                    -> (~>) (m_a1LGi b_a1LGm) (m_a1LGi c_a1LGn)) where
  liftSing2
    (s_a1LLS :: Sing (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)))
    (s_a1LLT :: Sing (d_a1LLP :: m_a1LGi a_a1LGl))
    = singFun1
        @(MzipWithSym2 (d_a1LLO :: (~>) a_a1LGl ((~>) b_a1LGm c_a1LGn)) (d_a1LLP :: m_a1LGi a_a1LGl))
        (sMzipWith s_a1LLS s_a1LLT)
instance SMonadZip m_a1LGi =>
          SingI (MunzipSym0 :: (~>) (m_a1LGi (a_a1LGo,
                                              b_a1LGp)) (m_a1LGi a_a1LGo, m_a1LGi b_a1LGp)) where
  sing = singFun1 @MunzipSym0 sMunzip
