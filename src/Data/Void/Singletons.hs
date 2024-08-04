{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
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
-- Module      :  Data.Void.Singletons
-- Copyright   :  (C) 2017 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines functions and datatypes relating to the singleton for 'Void',
-- including singled versions of all the definitions in @Data.Void@.
--
-- Because many of these definitions are produced by Template Haskell,
-- it is not possible to create proper Haddock documentation. Please look
-- up the corresponding operation in @Data.Void@. Also, please excuse
-- the apparent repeated variable names. This is due to an interaction
-- between Template Haskell and Haddock.
--
----------------------------------------------------------------------------
module Data.Void.Singletons (
  -- * The 'Void' singleton
  Sing, SVoid,
  -- | Just as 'Void' has no constructors, 'SVoid' also has no constructors.

  -- * Singletons from @Data.Void@
  Absurd, sAbsurd,

  -- * Defunctionalization symbols
  AbsurdSym0, AbsurdSym1
  ) where

import Data.Singletons
import Data.Singletons.Base.Instances
import Data.Singletons.TH
import Data.Kind (Type)

type family LamCases_6989586621679166455_aEKQ (a6989586621679166454 :: Void) a_6989586621679166457_aEKS where
data LamCases_6989586621679166455Sym0 (a6989586621679166454 :: Void) a_69895866216791664576989586621679166458
  where
    LamCases_6989586621679166455Sym0KindInference :: SameKind (Apply (LamCases_6989586621679166455Sym0 a6989586621679166454) arg_aEKT) (LamCases_6989586621679166455Sym1 a6989586621679166454 arg_aEKT) =>
                                                      LamCases_6989586621679166455Sym0 a6989586621679166454 a_69895866216791664576989586621679166458
type instance Apply @_ @_ (LamCases_6989586621679166455Sym0 a6989586621679166454) a_69895866216791664576989586621679166458 = LamCases_6989586621679166455_aEKQ a6989586621679166454 a_69895866216791664576989586621679166458
instance SuppressUnusedWarnings (LamCases_6989586621679166455Sym0 a6989586621679166454) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679166455Sym0KindInference ())
type family LamCases_6989586621679166455Sym1 (a6989586621679166454 :: Void) a_69895866216791664576989586621679166458 where
  LamCases_6989586621679166455Sym1 a6989586621679166454 a_69895866216791664576989586621679166458 = LamCases_6989586621679166455_aEKQ a6989586621679166454 a_69895866216791664576989586621679166458
type AbsurdSym0 :: (~>) Void a_aEKI
data AbsurdSym0 :: (~>) Void a_aEKI
  where
    AbsurdSym0KindInference :: SameKind (Apply AbsurdSym0 arg_aEKM) (AbsurdSym1 arg_aEKM) =>
                                AbsurdSym0 a6989586621679166453
type instance Apply @Void @a_aEKI AbsurdSym0 a6989586621679166453 = Absurd a6989586621679166453
instance SuppressUnusedWarnings AbsurdSym0 where
  suppressUnusedWarnings = snd ((,) AbsurdSym0KindInference ())
type AbsurdSym1 :: Void -> a_aEKI
type family AbsurdSym1 @a_aEKI (a6989586621679166453 :: Void) :: a_aEKI where
  AbsurdSym1 a6989586621679166453 = Absurd a6989586621679166453
type Absurd :: Void -> a_aEKI
type family Absurd @a_aEKI (a_aEKL :: Void) :: a_aEKI where
  Absurd a_aEKO = Apply (LamCases_6989586621679166455Sym0 a_aEKO) a_aEKO
sAbsurd ::
  (forall (t_aEKU :: Void).
    Sing t_aEKU -> Sing (Absurd t_aEKU :: a_aEKI) :: Type)
sAbsurd (sA :: Sing a_aEKO)
  = applySing
      (singFun1 @(LamCases_6989586621679166455Sym0 a_aEKO) (\case)) sA
instance SingI (AbsurdSym0 :: (~>) Void a_aEKI) where
  sing = singFun1 @AbsurdSym0 sAbsurd

