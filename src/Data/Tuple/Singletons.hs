{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -ddump-splices #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
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
-- Module      :  Data.Tuple.Singletons
-- Copyright   :  (C) 2013 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines functions and datatypes relating to the singleton for tuples,
-- including singled versions of all the definitions in @Data.Tuple@.
--
-- Because many of these definitions are produced by Template Haskell,
-- it is not possible to create proper Haddock documentation. Please look
-- up the corresponding operation in @Data.Tuple@. Also, please excuse
-- the apparent repeated variable names. This is due to an interaction
-- between Template Haskell and Haddock.
--
----------------------------------------------------------------------------

module Data.Tuple.Singletons (
  -- * Singleton definitions
  -- | See 'Sing' for more info.

  Sing, STuple0(..), STuple2(..), STuple3(..),
  STuple4(..), STuple5(..), STuple6(..), STuple7(..),

  -- * Singletons from @Data.Tuple@
  Fst, sFst, Snd, sSnd, Curry, sCurry, Uncurry, sUncurry, Swap, sSwap,

  -- * Defunctionalization symbols
  Tuple0Sym0,
  Tuple2Sym0, Tuple2Sym1, Tuple2Sym2,
  Tuple3Sym0, Tuple3Sym1, Tuple3Sym2, Tuple3Sym3,
  Tuple4Sym0, Tuple4Sym1, Tuple4Sym2, Tuple4Sym3, Tuple4Sym4,
  Tuple5Sym0, Tuple5Sym1, Tuple5Sym2, Tuple5Sym3, Tuple5Sym4, Tuple5Sym5,
  Tuple6Sym0, Tuple6Sym1, Tuple6Sym2, Tuple6Sym3, Tuple6Sym4, Tuple6Sym5, Tuple6Sym6,
  Tuple7Sym0, Tuple7Sym1, Tuple7Sym2, Tuple7Sym3, Tuple7Sym4, Tuple7Sym5, Tuple7Sym6, Tuple7Sym7,

  FstSym0, FstSym1, SndSym0, SndSym1,
  CurrySym0, CurrySym1, CurrySym2, CurrySym3,
  UncurrySym0, UncurrySym1, UncurrySym2,
  SwapSym0, SwapSym1
  ) where

import Data.Singletons.Base.Instances
import Data.Singletons.TH
import Data.Kind (Type)

type SwapSym0 :: (~>) (a_aDpN, b_aDpO) (b_aDpO, a_aDpN)
data SwapSym0 :: (~>) (a_aDpN, b_aDpO) (b_aDpO, a_aDpN)
  where
    SwapSym0KindInference :: SameKind (Apply SwapSym0 arg_aDrg) (SwapSym1 arg_aDrg) =>
                              SwapSym0 a6989586621679161399
type instance Apply @(a_aDpN, b_aDpO) @(b_aDpO,
                                        a_aDpN) SwapSym0 a6989586621679161399 = Swap a6989586621679161399
instance SuppressUnusedWarnings SwapSym0 where
  suppressUnusedWarnings = snd ((,) SwapSym0KindInference ())
type SwapSym1 :: (a_aDpN, b_aDpO) -> (b_aDpO, a_aDpN)
type family SwapSym1 @a_aDpN @b_aDpO (a6989586621679161399 :: (a_aDpN,
                                                                b_aDpO)) :: (b_aDpO,
                                                                            a_aDpN) where
  SwapSym1 a6989586621679161399 = Swap a6989586621679161399
type UncurrySym0 :: (~>) ((~>) a_aDpP ((~>) b_aDpQ c_aDpR)) ((~>) (a_aDpP,
                                                                    b_aDpQ) c_aDpR)
data UncurrySym0 :: (~>) ((~>) a_aDpP ((~>) b_aDpQ c_aDpR)) ((~>) (a_aDpP,
                                                                    b_aDpQ) c_aDpR)
  where
    UncurrySym0KindInference :: SameKind (Apply UncurrySym0 arg_aDrm) (UncurrySym1 arg_aDrm) =>
                                UncurrySym0 a6989586621679161405
type instance Apply @((~>) a_aDpP ((~>) b_aDpQ c_aDpR)) @((~>) (a_aDpP,
                                                                b_aDpQ) c_aDpR) UncurrySym0 a6989586621679161405 = UncurrySym1 a6989586621679161405
instance SuppressUnusedWarnings UncurrySym0 where
  suppressUnusedWarnings = snd ((,) UncurrySym0KindInference ())
type UncurrySym1 :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)
                    -> (~>) (a_aDpP, b_aDpQ) c_aDpR
data UncurrySym1 (a6989586621679161405 :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)) :: (~>) (a_aDpP,
                                                                                      b_aDpQ) c_aDpR
  where
    UncurrySym1KindInference :: SameKind (Apply (UncurrySym1 a6989586621679161405) arg_aDrm) (UncurrySym2 a6989586621679161405 arg_aDrm) =>
                                UncurrySym1 a6989586621679161405 a6989586621679161406
type instance Apply @(a_aDpP,
                      b_aDpQ) @c_aDpR (UncurrySym1 a6989586621679161405) a6989586621679161406 = Uncurry a6989586621679161405 a6989586621679161406
instance SuppressUnusedWarnings (UncurrySym1 a6989586621679161405) where
  suppressUnusedWarnings = snd ((,) UncurrySym1KindInference ())
type UncurrySym2 :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)
                    -> (a_aDpP, b_aDpQ) -> c_aDpR
type family UncurrySym2 @a_aDpP @b_aDpQ @c_aDpR (a6989586621679161405 :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)) (a6989586621679161406 :: (a_aDpP,
                                                                                                                                      b_aDpQ)) :: c_aDpR where
  UncurrySym2 a6989586621679161405 a6989586621679161406 = Uncurry a6989586621679161405 a6989586621679161406
type CurrySym0 :: (~>) ((~>) (a_aDpS,
                              b_aDpT) c_aDpU) ((~>) a_aDpS ((~>) b_aDpT c_aDpU))
data CurrySym0 :: (~>) ((~>) (a_aDpS,
                              b_aDpT) c_aDpU) ((~>) a_aDpS ((~>) b_aDpT c_aDpU))
  where
    CurrySym0KindInference :: SameKind (Apply CurrySym0 arg_aDru) (CurrySym1 arg_aDru) =>
                              CurrySym0 a6989586621679161413
type instance Apply @((~>) (a_aDpS,
                            b_aDpT) c_aDpU) @((~>) a_aDpS ((~>) b_aDpT c_aDpU)) CurrySym0 a6989586621679161413 = CurrySym1 a6989586621679161413
instance SuppressUnusedWarnings CurrySym0 where
  suppressUnusedWarnings = snd ((,) CurrySym0KindInference ())
type CurrySym1 :: (~>) (a_aDpS, b_aDpT) c_aDpU
                  -> (~>) a_aDpS ((~>) b_aDpT c_aDpU)
data CurrySym1 (a6989586621679161413 :: (~>) (a_aDpS,
                                              b_aDpT) c_aDpU) :: (~>) a_aDpS ((~>) b_aDpT c_aDpU)
  where
    CurrySym1KindInference :: SameKind (Apply (CurrySym1 a6989586621679161413) arg_aDru) (CurrySym2 a6989586621679161413 arg_aDru) =>
                              CurrySym1 a6989586621679161413 a6989586621679161414
type instance Apply @a_aDpS @((~>) b_aDpT c_aDpU) (CurrySym1 a6989586621679161413) a6989586621679161414 = CurrySym2 a6989586621679161413 a6989586621679161414
instance SuppressUnusedWarnings (CurrySym1 a6989586621679161413) where
  suppressUnusedWarnings = snd ((,) CurrySym1KindInference ())
type CurrySym2 :: (~>) (a_aDpS, b_aDpT) c_aDpU
                  -> a_aDpS -> (~>) b_aDpT c_aDpU
data CurrySym2 (a6989586621679161413 :: (~>) (a_aDpS,
                                              b_aDpT) c_aDpU) (a6989586621679161414 :: a_aDpS) :: (~>) b_aDpT c_aDpU
  where
    CurrySym2KindInference :: SameKind (Apply (CurrySym2 a6989586621679161413 a6989586621679161414) arg_aDru) (CurrySym3 a6989586621679161413 a6989586621679161414 arg_aDru) =>
                              CurrySym2 a6989586621679161413 a6989586621679161414 a6989586621679161415
type instance Apply @b_aDpT @c_aDpU (CurrySym2 a6989586621679161413 a6989586621679161414) a6989586621679161415 = Curry a6989586621679161413 a6989586621679161414 a6989586621679161415
instance SuppressUnusedWarnings (CurrySym2 a6989586621679161413 a6989586621679161414) where
  suppressUnusedWarnings = snd ((,) CurrySym2KindInference ())
type CurrySym3 :: (~>) (a_aDpS, b_aDpT) c_aDpU
                  -> a_aDpS -> b_aDpT -> c_aDpU
type family CurrySym3 @a_aDpS @b_aDpT @c_aDpU (a6989586621679161413 :: (~>) (a_aDpS,
                                                                              b_aDpT) c_aDpU) (a6989586621679161414 :: a_aDpS) (a6989586621679161415 :: b_aDpT) :: c_aDpU where
  CurrySym3 a6989586621679161413 a6989586621679161414 a6989586621679161415 = Curry a6989586621679161413 a6989586621679161414 a6989586621679161415
type SndSym0 :: (~>) (a_aDpV, b_aDpW) b_aDpW
data SndSym0 :: (~>) (a_aDpV, b_aDpW) b_aDpW
  where
    SndSym0KindInference :: SameKind (Apply SndSym0 arg_aDrC) (SndSym1 arg_aDrC) =>
                            SndSym0 a6989586621679161421
type instance Apply @(a_aDpV,
                      b_aDpW) @b_aDpW SndSym0 a6989586621679161421 = Snd a6989586621679161421
instance SuppressUnusedWarnings SndSym0 where
  suppressUnusedWarnings = snd ((,) SndSym0KindInference ())
type SndSym1 :: (a_aDpV, b_aDpW) -> b_aDpW
type family SndSym1 @a_aDpV @b_aDpW (a6989586621679161421 :: (a_aDpV,
                                                              b_aDpW)) :: b_aDpW where
  SndSym1 a6989586621679161421 = Snd a6989586621679161421
type FstSym0 :: (~>) (a_aDpX, b_aDpY) a_aDpX
data FstSym0 :: (~>) (a_aDpX, b_aDpY) a_aDpX
  where
    FstSym0KindInference :: SameKind (Apply FstSym0 arg_aDrG) (FstSym1 arg_aDrG) =>
                            FstSym0 a6989586621679161425
type instance Apply @(a_aDpX,
                      b_aDpY) @a_aDpX FstSym0 a6989586621679161425 = Fst a6989586621679161425
instance SuppressUnusedWarnings FstSym0 where
  suppressUnusedWarnings = snd ((,) FstSym0KindInference ())
type FstSym1 :: (a_aDpX, b_aDpY) -> a_aDpX
type family FstSym1 @a_aDpX @b_aDpY (a6989586621679161425 :: (a_aDpX,
                                                              b_aDpY)) :: a_aDpX where
  FstSym1 a6989586621679161425 = Fst a6989586621679161425
type Swap :: (a_aDpN, b_aDpO) -> (b_aDpO, a_aDpN)
type family Swap @a_aDpN @b_aDpO (a_aDrf :: (a_aDpN,
                                              b_aDpO)) :: (b_aDpO, a_aDpN) where
  Swap '(a_aDri, b_aDrj) = Apply (Apply Tuple2Sym0 b_aDrj) a_aDri
type Uncurry :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)
                -> (a_aDpP, b_aDpQ) -> c_aDpR
type family Uncurry @a_aDpP @b_aDpQ @c_aDpR (a_aDrk :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)) (a_aDrl :: (a_aDpP,
                                                                                                      b_aDpQ)) :: c_aDpR where
  Uncurry f_aDrp p_aDrq = Apply (Apply f_aDrp (Apply FstSym0 p_aDrq)) (Apply SndSym0 p_aDrq)
type Curry :: (~>) (a_aDpS, b_aDpT) c_aDpU
              -> a_aDpS -> b_aDpT -> c_aDpU
type family Curry @a_aDpS @b_aDpT @c_aDpU (a_aDrr :: (~>) (a_aDpS,
                                                            b_aDpT) c_aDpU) (a_aDrs :: a_aDpS) (a_aDrt :: b_aDpT) :: c_aDpU where
  Curry f_aDry x_aDrz y_aDrA = Apply f_aDry (Apply (Apply Tuple2Sym0 x_aDrz) y_aDrA)
type Snd :: (a_aDpV, b_aDpW) -> b_aDpW
type family Snd @a_aDpV @b_aDpW (a_aDrB :: (a_aDpV,
                                            b_aDpW)) :: b_aDpW where
  Snd '(_, y_aDrE) = y_aDrE
type Fst :: (a_aDpX, b_aDpY) -> a_aDpX
type family Fst @a_aDpX @b_aDpY (a_aDrF :: (a_aDpX,
                                            b_aDpY)) :: a_aDpX where
  Fst '(x_aDrI, _) = x_aDrI
sSwap ::
  (forall (t_aDrJ :: (a_aDpN, b_aDpO)).
    Sing t_aDrJ -> Sing (Swap t_aDrJ :: (b_aDpO, a_aDpN)) :: Type)
sUncurry ::
  (forall (t_aDrL :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR))
          (t_aDrM :: (a_aDpP, b_aDpQ)).
    Sing t_aDrL
    -> Sing t_aDrM -> Sing (Uncurry t_aDrL t_aDrM :: c_aDpR) :: Type)
sCurry ::
  (forall (t_aDrQ :: (~>) (a_aDpS, b_aDpT) c_aDpU)
          (t_aDrR :: a_aDpS)
          (t_aDrS :: b_aDpT).
    Sing t_aDrQ
    -> Sing t_aDrR
      -> Sing t_aDrS
          -> Sing (Curry t_aDrQ t_aDrR t_aDrS :: c_aDpU) :: Type)
sSnd ::
  (forall (t_aDs0 :: (a_aDpV, b_aDpW)).
    Sing t_aDs0 -> Sing (Snd t_aDs0 :: b_aDpW) :: Type)
sFst ::
  (forall (t_aDs2 :: (a_aDpX, b_aDpY)).
    Sing t_aDs2 -> Sing (Fst t_aDs2 :: a_aDpX) :: Type)
sSwap (STuple2 (sA :: Sing a_aDri) (sB :: Sing b_aDrj))
  = applySing (applySing (singFun2 @Tuple2Sym0 STuple2) sB) sA
sUncurry (sF :: Sing f_aDrp) (sP :: Sing p_aDrq)
  = applySing
      (applySing sF (applySing (singFun1 @FstSym0 sFst) sP))
      (applySing (singFun1 @SndSym0 sSnd) sP)
sCurry (sF :: Sing f_aDry) (sX :: Sing x_aDrz) (sY :: Sing y_aDrA)
  = applySing
      sF (applySing (applySing (singFun2 @Tuple2Sym0 STuple2) sX) sY)
sSnd (STuple2 _ (sY :: Sing y_aDrE)) = sY
sFst (STuple2 (sX :: Sing x_aDrI) _) = sX
instance SingI (SwapSym0 :: (~>) (a_aDpN, b_aDpO) (b_aDpO,
                                                    a_aDpN)) where
  sing = singFun1 @SwapSym0 sSwap
instance SingI (UncurrySym0 :: (~>) ((~>) a_aDpP ((~>) b_aDpQ c_aDpR)) ((~>) (a_aDpP,
                                                                              b_aDpQ) c_aDpR)) where
  sing = singFun2 @UncurrySym0 sUncurry
instance SingI d_aDrN =>
          SingI (UncurrySym1 (d_aDrN :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)) :: (~>) (a_aDpP,
                                                                                  b_aDpQ) c_aDpR) where
  sing
    = singFun1
        @(UncurrySym1 (d_aDrN :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)))
        (sUncurry (sing @d_aDrN))
instance SingI1 (UncurrySym1 :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)
                                -> (~>) (a_aDpP, b_aDpQ) c_aDpR) where
  liftSing
    (s_aDrP :: Sing (d_aDrN :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)))
    = singFun1
        @(UncurrySym1 (d_aDrN :: (~>) a_aDpP ((~>) b_aDpQ c_aDpR)))
        (sUncurry s_aDrP)
instance SingI (CurrySym0 :: (~>) ((~>) (a_aDpS,
                                          b_aDpT) c_aDpU) ((~>) a_aDpS ((~>) b_aDpT c_aDpU))) where
  sing = singFun3 @CurrySym0 sCurry
instance SingI d_aDrT =>
          SingI (CurrySym1 (d_aDrT :: (~>) (a_aDpS,
                                            b_aDpT) c_aDpU) :: (~>) a_aDpS ((~>) b_aDpT c_aDpU)) where
  sing
    = singFun2
        @(CurrySym1 (d_aDrT :: (~>) (a_aDpS, b_aDpT) c_aDpU))
        (sCurry (sing @d_aDrT))
instance SingI1 (CurrySym1 :: (~>) (a_aDpS, b_aDpT) c_aDpU
                              -> (~>) a_aDpS ((~>) b_aDpT c_aDpU)) where
  liftSing (s_aDrZ :: Sing (d_aDrT :: (~>) (a_aDpS, b_aDpT) c_aDpU))
    = singFun2
        @(CurrySym1 (d_aDrT :: (~>) (a_aDpS, b_aDpT) c_aDpU))
        (sCurry s_aDrZ)
instance (SingI d_aDrT, SingI d_aDrU) =>
          SingI (CurrySym2 (d_aDrT :: (~>) (a_aDpS,
                                            b_aDpT) c_aDpU) (d_aDrU :: a_aDpS) :: (~>) b_aDpT c_aDpU) where
  sing
    = singFun1
        @(CurrySym2 (d_aDrT :: (~>) (a_aDpS,
                                      b_aDpT) c_aDpU) (d_aDrU :: a_aDpS))
        (sCurry (sing @d_aDrT) (sing @d_aDrU))
instance SingI d_aDrT =>
          SingI1 (CurrySym2 (d_aDrT :: (~>) (a_aDpS,
                                            b_aDpT) c_aDpU) :: a_aDpS
                                                                -> (~>) b_aDpT c_aDpU) where
  liftSing (s_aDrW :: Sing (d_aDrU :: a_aDpS))
    = singFun1
        @(CurrySym2 (d_aDrT :: (~>) (a_aDpS,
                                      b_aDpT) c_aDpU) (d_aDrU :: a_aDpS))
        (sCurry (sing @d_aDrT) s_aDrW)
instance SingI2 (CurrySym2 :: (~>) (a_aDpS, b_aDpT) c_aDpU
                              -> a_aDpS -> (~>) b_aDpT c_aDpU) where
  liftSing2
    (s_aDrX :: Sing (d_aDrT :: (~>) (a_aDpS, b_aDpT) c_aDpU))
    (s_aDrY :: Sing (d_aDrU :: a_aDpS))
    = singFun1
        @(CurrySym2 (d_aDrT :: (~>) (a_aDpS,
                                      b_aDpT) c_aDpU) (d_aDrU :: a_aDpS))
        (sCurry s_aDrX s_aDrY)
instance SingI (SndSym0 :: (~>) (a_aDpV, b_aDpW) b_aDpW) where
  sing = singFun1 @SndSym0 sSnd
instance SingI (FstSym0 :: (~>) (a_aDpX, b_aDpY) a_aDpX) where
  sing = singFun1 @FstSym0 sFst

