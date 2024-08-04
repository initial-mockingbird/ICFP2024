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
-- Module      :  Data.Function.Singletons
-- Copyright   :  (C) 2016 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines singleton versions of the definitions in @Data.Function@.
--
-- Because many of these definitions are produced by Template Haskell,
-- it is not possible to create proper Haddock documentation. Please look
-- up the corresponding operation in @Data.Function@. Also, please excuse
-- the apparent repeated variable names. This is due to an interaction
-- between Template Haskell and Haddock.
--
----------------------------------------------------------------------------

module Data.Function.Singletons (
    -- * "Prelude" re-exports
    Id, sId, Const, sConst, type (.), (%.), Flip, sFlip, type ($), (%$)
    -- * Other combinators
  , type (&), (%&), On, sOn

    -- * Defunctionalization symbols
  , IdSym0, IdSym1
  , ConstSym0, ConstSym1, ConstSym2
  , type (.@#@$), type (.@#@$$), type (.@#@$$$), type (.@#@$$$$)
  , FlipSym0, FlipSym1, FlipSym2, FlipSym3
  , type ($@#@$), type ($@#@$$), type ($@#@$$$)
  , type (&@#@$), type (&@#@$$), type (&@#@$$$)
  , OnSym0, OnSym1, OnSym2, OnSym3, OnSym4
  ) where

import Data.Singletons.TH
import GHC.Base.Singletons
import Data.Kind (Type)

type family LamCases_6989586621679264372_a14e9 (ty6989586621679264368 :: (~>) b6989586621679264337 ((~>) b6989586621679264337 c6989586621679264338)) (f6989586621679264369 :: (~>) a6989586621679264339 b6989586621679264337) (a_69895866216792643556989586621679264370 :: a6989586621679264339) (a_69895866216792643576989586621679264371 :: a6989586621679264339) a_6989586621679264376_a14ed a_6989586621679264378_a14ef where
      LamCases_6989586621679264372_a14e9 ty_a14e4 f_a14e5 a_6989586621679264355_a14e6 a_6989586621679264357_a14e7 x_a14ea y_a14eb = Apply (Apply ty_a14e4 (Apply f_a14e5 x_a14ea)) (Apply f_a14e5 y_a14eb)
data LamCases_6989586621679264372Sym0 (ty6989586621679264368 :: (~>) b6989586621679264337 ((~>) b6989586621679264337 c6989586621679264338)) (f6989586621679264369 :: (~>) a6989586621679264339 b6989586621679264337) (a_69895866216792643556989586621679264370 :: a6989586621679264339) (a_69895866216792643576989586621679264371 :: a6989586621679264339) a_69895866216792643766989586621679264377
  where
    LamCases_6989586621679264372Sym0KindInference :: SameKind (Apply (LamCases_6989586621679264372Sym0 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371) arg_a14eg) (LamCases_6989586621679264372Sym1 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 arg_a14eg) =>
                                                      LamCases_6989586621679264372Sym0 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377
type instance Apply @_ @_ (LamCases_6989586621679264372Sym0 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371) a_69895866216792643766989586621679264377 = LamCases_6989586621679264372Sym1 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377
instance SuppressUnusedWarnings (LamCases_6989586621679264372Sym0 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679264372Sym0KindInference ())
data LamCases_6989586621679264372Sym1 (ty6989586621679264368 :: (~>) b6989586621679264337 ((~>) b6989586621679264337 c6989586621679264338)) (f6989586621679264369 :: (~>) a6989586621679264339 b6989586621679264337) (a_69895866216792643556989586621679264370 :: a6989586621679264339) (a_69895866216792643576989586621679264371 :: a6989586621679264339) a_69895866216792643766989586621679264377 a_69895866216792643786989586621679264379
  where
    LamCases_6989586621679264372Sym1KindInference :: SameKind (Apply (LamCases_6989586621679264372Sym1 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377) arg_a14eg) (LamCases_6989586621679264372Sym2 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377 arg_a14eg) =>
                                                      LamCases_6989586621679264372Sym1 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377 a_69895866216792643786989586621679264379
type instance Apply @_ @_ (LamCases_6989586621679264372Sym1 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377) a_69895866216792643786989586621679264379 = LamCases_6989586621679264372_a14e9 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377 a_69895866216792643786989586621679264379
instance SuppressUnusedWarnings (LamCases_6989586621679264372Sym1 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679264372Sym1KindInference ())
type family LamCases_6989586621679264372Sym2 (ty6989586621679264368 :: (~>) b6989586621679264337 ((~>) b6989586621679264337 c6989586621679264338)) (f6989586621679264369 :: (~>) a6989586621679264339 b6989586621679264337) (a_69895866216792643556989586621679264370 :: a6989586621679264339) (a_69895866216792643576989586621679264371 :: a6989586621679264339) a_69895866216792643766989586621679264377 a_69895866216792643786989586621679264379 where
  LamCases_6989586621679264372Sym2 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377 a_69895866216792643786989586621679264379 = LamCases_6989586621679264372_a14e9 ty6989586621679264368 f6989586621679264369 a_69895866216792643556989586621679264370 a_69895866216792643576989586621679264371 a_69895866216792643766989586621679264377 a_69895866216792643786989586621679264379
type (&@#@$) :: (~>) a_a14dx ((~>) ((~>) a_a14dx b_a14dy) b_a14dy)
data (&@#@$) :: (~>) a_a14dx ((~>) ((~>) a_a14dx b_a14dy) b_a14dy)
  where
    (:&@#@$###) :: SameKind (Apply (&@#@$) arg_a14dM) ((&@#@$$) arg_a14dM) =>
                    (&@#@$) a6989586621679264351
type instance Apply @a_a14dx @((~>) ((~>) a_a14dx b_a14dy) b_a14dy) (&@#@$) a6989586621679264351 = (&@#@$$) a6989586621679264351
instance SuppressUnusedWarnings (&@#@$) where
  suppressUnusedWarnings = snd ((,) (:&@#@$###) ())
infixl 1 &@#@$
type (&@#@$$) :: a_a14dx -> (~>) ((~>) a_a14dx b_a14dy) b_a14dy
data (&@#@$$) (a6989586621679264351 :: a_a14dx) :: (~>) ((~>) a_a14dx b_a14dy) b_a14dy
  where
    (:&@#@$$###) :: SameKind (Apply ((&@#@$$) a6989586621679264351) arg_a14dM) ((&@#@$$$) a6989586621679264351 arg_a14dM) =>
                    (&@#@$$) a6989586621679264351 a6989586621679264352
type instance Apply @((~>) a_a14dx b_a14dy) @b_a14dy ((&@#@$$) a6989586621679264351) a6989586621679264352 = (&) a6989586621679264351 a6989586621679264352
instance SuppressUnusedWarnings ((&@#@$$) a6989586621679264351) where
  suppressUnusedWarnings = snd ((,) (:&@#@$$###) ())
infixl 1 &@#@$$
type (&@#@$$$) :: a_a14dx -> (~>) a_a14dx b_a14dy -> b_a14dy
type family (&@#@$$$) @a_a14dx @b_a14dy (a6989586621679264351 :: a_a14dx) (a6989586621679264352 :: (~>) a_a14dx b_a14dy) :: b_a14dy where
  (&@#@$$$) a6989586621679264351 a6989586621679264352 = (&) a6989586621679264351 a6989586621679264352
infixl 1 &@#@$$$
type OnSym0 :: (~>) ((~>) b_a14dz ((~>) b_a14dz c_a14dA)) ((~>) ((~>) a_a14dB b_a14dz) ((~>) a_a14dB ((~>) a_a14dB c_a14dA)))
data OnSym0 :: (~>) ((~>) b_a14dz ((~>) b_a14dz c_a14dA)) ((~>) ((~>) a_a14dB b_a14dz) ((~>) a_a14dB ((~>) a_a14dB c_a14dA)))
  where
    OnSym0KindInference :: SameKind (Apply OnSym0 arg_a14dZ) (OnSym1 arg_a14dZ) =>
                            OnSym0 a6989586621679264364
type instance Apply @((~>) b_a14dz ((~>) b_a14dz c_a14dA)) @((~>) ((~>) a_a14dB b_a14dz) ((~>) a_a14dB ((~>) a_a14dB c_a14dA))) OnSym0 a6989586621679264364 = OnSym1 a6989586621679264364
instance SuppressUnusedWarnings OnSym0 where
  suppressUnusedWarnings = snd ((,) OnSym0KindInference ())
infixl 0 `OnSym0`
type OnSym1 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)
                -> (~>) ((~>) a_a14dB b_a14dz) ((~>) a_a14dB ((~>) a_a14dB c_a14dA))
data OnSym1 (a6989586621679264364 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) :: (~>) ((~>) a_a14dB b_a14dz) ((~>) a_a14dB ((~>) a_a14dB c_a14dA))
  where
    OnSym1KindInference :: SameKind (Apply (OnSym1 a6989586621679264364) arg_a14dZ) (OnSym2 a6989586621679264364 arg_a14dZ) =>
                            OnSym1 a6989586621679264364 a6989586621679264365
type instance Apply @((~>) a_a14dB b_a14dz) @((~>) a_a14dB ((~>) a_a14dB c_a14dA)) (OnSym1 a6989586621679264364) a6989586621679264365 = OnSym2 a6989586621679264364 a6989586621679264365
instance SuppressUnusedWarnings (OnSym1 a6989586621679264364) where
  suppressUnusedWarnings = snd ((,) OnSym1KindInference ())
infixl 0 `OnSym1`
type OnSym2 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)
                -> (~>) a_a14dB b_a14dz -> (~>) a_a14dB ((~>) a_a14dB c_a14dA)
data OnSym2 (a6989586621679264364 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (a6989586621679264365 :: (~>) a_a14dB b_a14dz) :: (~>) a_a14dB ((~>) a_a14dB c_a14dA)
  where
    OnSym2KindInference :: SameKind (Apply (OnSym2 a6989586621679264364 a6989586621679264365) arg_a14dZ) (OnSym3 a6989586621679264364 a6989586621679264365 arg_a14dZ) =>
                            OnSym2 a6989586621679264364 a6989586621679264365 a6989586621679264366
type instance Apply @a_a14dB @((~>) a_a14dB c_a14dA) (OnSym2 a6989586621679264364 a6989586621679264365) a6989586621679264366 = OnSym3 a6989586621679264364 a6989586621679264365 a6989586621679264366
instance SuppressUnusedWarnings (OnSym2 a6989586621679264364 a6989586621679264365) where
  suppressUnusedWarnings = snd ((,) OnSym2KindInference ())
infixl 0 `OnSym2`
type OnSym3 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)
                -> (~>) a_a14dB b_a14dz -> a_a14dB -> (~>) a_a14dB c_a14dA
data OnSym3 (a6989586621679264364 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (a6989586621679264365 :: (~>) a_a14dB b_a14dz) (a6989586621679264366 :: a_a14dB) :: (~>) a_a14dB c_a14dA
  where
    OnSym3KindInference :: SameKind (Apply (OnSym3 a6989586621679264364 a6989586621679264365 a6989586621679264366) arg_a14dZ) (OnSym4 a6989586621679264364 a6989586621679264365 a6989586621679264366 arg_a14dZ) =>
                            OnSym3 a6989586621679264364 a6989586621679264365 a6989586621679264366 a6989586621679264367
type instance Apply @a_a14dB @c_a14dA (OnSym3 a6989586621679264364 a6989586621679264365 a6989586621679264366) a6989586621679264367 = On a6989586621679264364 a6989586621679264365 a6989586621679264366 a6989586621679264367
instance SuppressUnusedWarnings (OnSym3 a6989586621679264364 a6989586621679264365 a6989586621679264366) where
  suppressUnusedWarnings = snd ((,) OnSym3KindInference ())
infixl 0 `OnSym3`
type OnSym4 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)
                -> (~>) a_a14dB b_a14dz -> a_a14dB -> a_a14dB -> c_a14dA
type family OnSym4 @b_a14dz @c_a14dA @a_a14dB (a6989586621679264364 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (a6989586621679264365 :: (~>) a_a14dB b_a14dz) (a6989586621679264366 :: a_a14dB) (a6989586621679264367 :: a_a14dB) :: c_a14dA where
  OnSym4 a6989586621679264364 a6989586621679264365 a6989586621679264366 a6989586621679264367 = On a6989586621679264364 a6989586621679264365 a6989586621679264366 a6989586621679264367
infixl 0 `OnSym4`
type (&) :: a_a14dx -> (~>) a_a14dx b_a14dy -> b_a14dy
type family (&) @a_a14dx @b_a14dy (a_a14dK :: a_a14dx) (a_a14dL :: (~>) a_a14dx b_a14dy) :: b_a14dy where
  (&) x_a14dP f_a14dQ = Apply f_a14dQ x_a14dP
type On :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)
            -> (~>) a_a14dB b_a14dz -> a_a14dB -> a_a14dB -> c_a14dA
type family On @b_a14dz @c_a14dA @a_a14dB (a_a14dV :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (a_a14dW :: (~>) a_a14dB b_a14dz) (a_a14dX :: a_a14dB) (a_a14dY :: a_a14dB) :: c_a14dA where
  On ty_a14e4 f_a14e5 a_6989586621679264355_a14e6 a_6989586621679264357_a14e7 = Apply (Apply (LamCases_6989586621679264372Sym0 ty_a14e4 f_a14e5 a_6989586621679264355_a14e6 a_6989586621679264357_a14e7) a_6989586621679264355_a14e6) a_6989586621679264357_a14e7
infixl 1 &
infixl 0 `On`
infixl 1 %&
infixl 0 `sOn`
(%&) ::
  (forall (t_a14eh :: a_a14dx) (t_a14ei :: (~>) a_a14dx b_a14dy).
    Sing t_a14eh
    -> Sing t_a14ei -> Sing ((&) t_a14eh t_a14ei :: b_a14dy) :: Type)
sOn ::
  (forall (t_a14em :: (~>) b_a14dz ((~>) b_a14dz c_a14dA))
          (t_a14en :: (~>) a_a14dB b_a14dz)
          (t_a14eo :: a_a14dB)
          (t_a14ep :: a_a14dB).
    Sing t_a14em
    -> Sing t_a14en
      -> Sing t_a14eo
          -> Sing t_a14ep
            -> Sing (On t_a14em t_a14en t_a14eo t_a14ep :: c_a14dA) :: Type)
(%&) (sX :: Sing x_a14dP) (sF :: Sing f_a14dQ) = applySing sF sX
sOn
  ((%.*.) :: Sing ty_a14e4)
  (sF :: Sing f_a14e5)
  (sA_6989586621679264355 :: Sing a_6989586621679264355_a14e6)
  (sA_6989586621679264357 :: Sing a_6989586621679264357_a14e7)
  = applySing
      (applySing
          (singFun2
            @(LamCases_6989586621679264372Sym0 ty_a14e4 f_a14e5 a_6989586621679264355_a14e6 a_6989586621679264357_a14e7)
            (\cases
                (sX :: Sing x_a14ea) (sY :: Sing y_a14eb)
                  -> applySing
                      (applySing (%.*.) (applySing sF sX)) (applySing sF sY)))
          sA_6989586621679264355)
      sA_6989586621679264357
instance SingI ((&@#@$) :: (~>) a_a14dx ((~>) ((~>) a_a14dx b_a14dy) b_a14dy)) where
  sing = singFun2 @(&@#@$) (%&)
instance SingI d_a14ej =>
          SingI ((&@#@$$) (d_a14ej :: a_a14dx) :: (~>) ((~>) a_a14dx b_a14dy) b_a14dy) where
  sing
    = singFun1 @((&@#@$$) (d_a14ej :: a_a14dx)) ((%&) (sing @d_a14ej))
instance SingI1 ((&@#@$$) :: a_a14dx
                              -> (~>) ((~>) a_a14dx b_a14dy) b_a14dy) where
  liftSing (s_a14el :: Sing (d_a14ej :: a_a14dx))
    = singFun1 @((&@#@$$) (d_a14ej :: a_a14dx)) ((%&) s_a14el)
instance SingI (OnSym0 :: (~>) ((~>) b_a14dz ((~>) b_a14dz c_a14dA)) ((~>) ((~>) a_a14dB b_a14dz) ((~>) a_a14dB ((~>) a_a14dB c_a14dA)))) where
  sing = singFun4 @OnSym0 sOn
instance SingI d_a14eq =>
          SingI (OnSym1 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) :: (~>) ((~>) a_a14dB b_a14dz) ((~>) a_a14dB ((~>) a_a14dB c_a14dA))) where
  sing
    = singFun3
        @(OnSym1 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)))
        (sOn (sing @d_a14eq))
instance SingI1 (OnSym1 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)
                            -> (~>) ((~>) a_a14dB b_a14dz) ((~>) a_a14dB ((~>) a_a14dB c_a14dA))) where
  liftSing
    (s_a14eA :: Sing (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)))
    = singFun3
        @(OnSym1 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)))
        (sOn s_a14eA)
instance (SingI d_a14eq, SingI d_a14er) =>
          SingI (OnSym2 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (d_a14er :: (~>) a_a14dB b_a14dz) :: (~>) a_a14dB ((~>) a_a14dB c_a14dA)) where
  sing
    = singFun2
        @(OnSym2 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (d_a14er :: (~>) a_a14dB b_a14dz))
        (sOn (sing @d_a14eq) (sing @d_a14er))
instance SingI d_a14eq =>
          SingI1 (OnSym2 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) :: (~>) a_a14dB b_a14dz
                                                                            -> (~>) a_a14dB ((~>) a_a14dB c_a14dA)) where
  liftSing (s_a14ex :: Sing (d_a14er :: (~>) a_a14dB b_a14dz))
    = singFun2
        @(OnSym2 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (d_a14er :: (~>) a_a14dB b_a14dz))
        (sOn (sing @d_a14eq) s_a14ex)
instance SingI2 (OnSym2 :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)
                            -> (~>) a_a14dB b_a14dz
                              -> (~>) a_a14dB ((~>) a_a14dB c_a14dA)) where
  liftSing2
    (s_a14ey :: Sing (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)))
    (s_a14ez :: Sing (d_a14er :: (~>) a_a14dB b_a14dz))
    = singFun2
        @(OnSym2 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (d_a14er :: (~>) a_a14dB b_a14dz))
        (sOn s_a14ey s_a14ez)
instance (SingI d_a14eq, SingI d_a14er, SingI d_a14es) =>
          SingI (OnSym3 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (d_a14er :: (~>) a_a14dB b_a14dz) (d_a14es :: a_a14dB) :: (~>) a_a14dB c_a14dA) where
  sing
    = singFun1
        @(OnSym3 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (d_a14er :: (~>) a_a14dB b_a14dz) (d_a14es :: a_a14dB))
        (sOn (sing @d_a14eq) (sing @d_a14er) (sing @d_a14es))
instance (SingI d_a14eq, SingI d_a14er) =>
          SingI1 (OnSym3 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (d_a14er :: (~>) a_a14dB b_a14dz) :: a_a14dB
                                                                                                              -> (~>) a_a14dB c_a14dA) where
  liftSing (s_a14eu :: Sing (d_a14es :: a_a14dB))
    = singFun1
        @(OnSym3 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (d_a14er :: (~>) a_a14dB b_a14dz) (d_a14es :: a_a14dB))
        (sOn (sing @d_a14eq) (sing @d_a14er) s_a14eu)
instance SingI d_a14eq =>
          SingI2 (OnSym3 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) :: (~>) a_a14dB b_a14dz
                                                                            -> a_a14dB
                                                                                -> (~>) a_a14dB c_a14dA) where
  liftSing2
    (s_a14ev :: Sing (d_a14er :: (~>) a_a14dB b_a14dz))
    (s_a14ew :: Sing (d_a14es :: a_a14dB))
    = singFun1
        @(OnSym3 (d_a14eq :: (~>) b_a14dz ((~>) b_a14dz c_a14dA)) (d_a14er :: (~>) a_a14dB b_a14dz) (d_a14es :: a_a14dB))
        (sOn (sing @d_a14eq) s_a14ev s_a14ew)

