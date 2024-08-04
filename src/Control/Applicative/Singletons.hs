{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
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
-- Module      :  Control.Applicative.Singletons
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted and singled versions of the 'Applicative' type class.
--
----------------------------------------------------------------------------

module Control.Applicative.Singletons (
  PApplicative(..), SApplicative(..),
  PAlternative(..), SAlternative(..),
  Sing, SConst(..), Const, GetConst, sGetConst,
  type (<$>), (%<$>), type (<$), (%<$), type (<**>), (%<**>),
  LiftA, sLiftA, LiftA3, sLiftA3, Optional, sOptional,

  -- * Defunctionalization symbols
  PureSym0, PureSym1,
  type (<*>@#@$), type (<*>@#@$$), type (<*>@#@$$$),
  type (*>@#@$),  type (*>@#@$$),  type (*>@#@$$$),
  type (<*@#@$),  type (<*@#@$$),  type (<*@#@$$$),
  EmptySym0, type (<|>@#@$), type (<|>@#@$$), type (<|>@#@$$$),
  ConstSym0, ConstSym1, GetConstSym0, GetConstSym1,
  type (<$>@#@$),  type (<$>@#@$$),  type (<$>@#@$$$),
  type (<$@#@$),   type (<$@#@$$),   type (<$@#@$$$),
  type (<**>@#@$), type (<**>@#@$$), type (<**>@#@$$$),
  LiftASym0,  LiftASym1,  LiftASym2,
  LiftA2Sym0, LiftA2Sym1, LiftA2Sym2, LiftA2Sym3,
  LiftA3Sym0, LiftA3Sym1, LiftA3Sym2, LiftA3Sym3,
  OptionalSym0, OptionalSym1
  ) where

import Control.Applicative
import Control.Monad.Singletons.Internal
import Data.Functor.Const.Singletons
import Data.Functor.Singletons
import Data.Monoid.Singletons
import Data.Ord (Down(..))
import Data.Ord.Singletons
import Data.Singletons.Base.Instances
import Data.Singletons.TH
import Data.Kind (Type)

type OptionalSym0 :: (~>) (f_a2fPi a_a2fPj) (f_a2fPi (Maybe a_a2fPj))
data OptionalSym0 :: (~>) (f_a2fPi a_a2fPj) (f_a2fPi (Maybe a_a2fPj))
  where
    OptionalSym0KindInference :: SameKind (Apply OptionalSym0 arg_a2fPU) (OptionalSym1 arg_a2fPU) =>
                                  OptionalSym0 a6989586621679547327
type instance Apply @(f_a2fPi a_a2fPj) @(f_a2fPi (Maybe a_a2fPj)) OptionalSym0 a6989586621679547327 = Optional a6989586621679547327
instance SuppressUnusedWarnings OptionalSym0 where
  suppressUnusedWarnings = snd ((,) OptionalSym0KindInference ())
type OptionalSym1 :: f_a2fPi a_a2fPj -> f_a2fPi (Maybe a_a2fPj)
type family OptionalSym1 @f_a2fPi @a_a2fPj (a6989586621679547327 :: f_a2fPi a_a2fPj) :: f_a2fPi (Maybe a_a2fPj) where
  OptionalSym1 a6989586621679547327 = Optional a6989586621679547327
type Optional :: f_a2fPi a_a2fPj -> f_a2fPi (Maybe a_a2fPj)
type family Optional @f_a2fPi @a_a2fPj (a_a2fPT :: f_a2fPi a_a2fPj) :: f_a2fPi (Maybe a_a2fPj) where
  Optional v_a2fPW = Apply (Apply (<|>@#@$) (Apply (Apply (<$>@#@$) JustSym0) v_a2fPW)) (Apply PureSym0 NothingSym0)
type Pure_6989586621679547330 :: forall a_a2fPm a_iv9m. a_iv9m
                                                        -> (a_a2fPm, a_iv9m)
type family Pure_6989586621679547330 @a_a2fPm @a_iv9m (a_a2fQ0 :: a_iv9m) :: (a_a2fPm,
                                                                              a_iv9m) where
  Pure_6989586621679547330 @a_a2fPm @a_iv9m (x_a2fQ3 :: a_iv9m) = Apply (Apply Tuple2Sym0 MemptySym0) x_a2fQ3
type TFHelper_6989586621679547338 :: forall a_a2fPm
                                            a_iv9o
                                            b_iv9p. (a_a2fPm, (~>) a_iv9o b_iv9p)
                                                    -> (a_a2fPm, a_iv9o) -> (a_a2fPm, b_iv9p)
type family TFHelper_6989586621679547338 @a_a2fPm @a_iv9o @b_iv9p (a_a2fQ8 :: (a_a2fPm,
                                                                                (~>) a_iv9o b_iv9p)) (a_a2fQ9 :: (a_a2fPm,
                                                                                                                  a_iv9o)) :: (a_a2fPm,
                                                                                                                              b_iv9p) where
  TFHelper_6989586621679547338 @a_a2fPm @a_iv9o @b_iv9p ('(u_a2fQd,
                                                            f_a2fQe) :: (a_a2fPm,
                                                                        (~>) a_iv9o b_iv9p)) ('(v_a2fQf,
                                                                                                x_a2fQg) :: (a_a2fPm,
                                                                                                              a_iv9o)) = Apply (Apply Tuple2Sym0 (Apply (Apply MappendSym0 u_a2fQd) v_a2fQf)) (Apply f_a2fQe x_a2fQg)
type LiftA2_6989586621679547352 :: forall a_a2fPm
                                          a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> (a_a2fPm, a_iv9s)
                                                      -> (a_a2fPm, b_iv9t) -> (a_a2fPm, c_iv9u)
type family LiftA2_6989586621679547352 @a_a2fPm @a_iv9s @b_iv9t @c_iv9u (a_a2fQm :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_a2fQn :: (a_a2fPm,
                                                                                                                                    a_iv9s)) (a_a2fQo :: (a_a2fPm,
                                                                                                                                                          b_iv9t)) :: (a_a2fPm,
                                                                                                                                                                      c_iv9u) where
  LiftA2_6989586621679547352 @a_a2fPm @a_iv9s @b_iv9t @c_iv9u (f_a2fQt :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) ('(u_a2fQu,
                                                                                                                x_a2fQv) :: (a_a2fPm,
                                                                                                                            a_iv9s)) ('(v_a2fQw,
                                                                                                                                        y_a2fQx) :: (a_a2fPm,
                                                                                                                                                      b_iv9t)) = Apply (Apply Tuple2Sym0 (Apply (Apply MappendSym0 u_a2fQu) v_a2fQw)) (Apply (Apply f_a2fQt x_a2fQv) y_a2fQx)
instance PApplicative ((,) a_a2fPm) where
  type Pure a_a2fPX = Pure_6989586621679547330 a_a2fPX
  type (<*>) a_a2fQ4 a_a2fQ5 = TFHelper_6989586621679547338 a_a2fQ4 a_a2fQ5
  type LiftA2 a_a2fQh a_a2fQi a_a2fQj = LiftA2_6989586621679547352 a_a2fQh a_a2fQi a_a2fQj
type Pure_6989586621679547367 :: forall a_iv9m. a_iv9m
                                                -> Down a_iv9m
type family Pure_6989586621679547367 @a_iv9m (a_a2fQD :: a_iv9m) :: Down a_iv9m where
  Pure_6989586621679547367 @a_iv9m a_6989586621679547369_a2fQG = Apply DownSym0 a_6989586621679547369_a2fQG
type TFHelper_6989586621679547377 :: forall a_iv9o
                                            b_iv9p. Down ((~>) a_iv9o b_iv9p)
                                                    -> Down a_iv9o -> Down b_iv9p
type family TFHelper_6989586621679547377 @a_iv9o @b_iv9p (a_a2fQL :: Down ((~>) a_iv9o b_iv9p)) (a_a2fQM :: Down a_iv9o) :: Down b_iv9p where
  TFHelper_6989586621679547377 @a_iv9o @b_iv9p ('Down f_a2fQQ) ('Down x_a2fQR) = Apply DownSym0 (Apply f_a2fQQ x_a2fQR)
instance PApplicative Down where
  type Pure a_a2fQy = Pure_6989586621679547367 a_a2fQy
  type (<*>) a_a2fQH a_a2fQI = TFHelper_6989586621679547377 a_a2fQH a_a2fQI
sOptional ::
  (forall (t_a2fQS :: f_a2fPi a_a2fPj).
    SAlternative f_a2fPi =>
    Sing t_a2fQS
    -> Sing (Optional t_a2fQS :: f_a2fPi (Maybe a_a2fPj)) :: Type)
sOptional (sV :: Sing v_a2fPW)
  = applySing
      (applySing
          (singFun2 @(<|>@#@$) (%<|>))
          (applySing
            (applySing (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @JustSym0 SJust))
            sV))
      (applySing (singFun1 @PureSym0 sPure) SNothing)
instance SAlternative f_a2fPi =>
          SingI (OptionalSym0 :: (~>) (f_a2fPi a_a2fPj) (f_a2fPi (Maybe a_a2fPj))) where
  sing = singFun1 @OptionalSym0 sOptional
instance SMonoid a_a2fPm => SApplicative ((,) a_a2fPm) where
  sPure (sX :: Sing x_a2fQ3)
    = applySing (applySing (singFun2 @Tuple2Sym0 STuple2) sMempty) sX
  (%<*>)
    (STuple2 (sU :: Sing u_a2fQd) (sF :: Sing f_a2fQe))
    (STuple2 (sV :: Sing v_a2fQf) (sX :: Sing x_a2fQg))
    = applySing
        (applySing
            (singFun2 @Tuple2Sym0 STuple2)
            (applySing (applySing (singFun2 @MappendSym0 sMappend) sU) sV))
        (applySing sF sX)
  sLiftA2
    (sF :: Sing f_a2fQt)
    (STuple2 (sU :: Sing u_a2fQu) (sX :: Sing x_a2fQv))
    (STuple2 (sV :: Sing v_a2fQw) (sY :: Sing y_a2fQx))
    = applySing
        (applySing
            (singFun2 @Tuple2Sym0 STuple2)
            (applySing (applySing (singFun2 @MappendSym0 sMappend) sU) sV))
        (applySing (applySing sF sX) sY)
instance SApplicative Down where
  sPure (sA_6989586621679547369 :: Sing a_6989586621679547369_a2fQG)
    = applySing (singFun1 @DownSym0 SDown) sA_6989586621679547369
  (%<*>) (SDown (sF :: Sing f_a2fQQ)) (SDown (sX :: Sing x_a2fQR))
    = applySing (singFun1 @DownSym0 SDown) (applySing sF sX)

