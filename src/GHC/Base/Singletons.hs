{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
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
-- Module      :  GHC.Base.Singletons
-- Copyright   :  (C) 2014 Jan Stolarek
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Jan Stolarek (jan.stolarek@p.lodz.pl)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Implements singletonized versions of functions from @GHC.Base@ module.
--
-- Because many of these definitions are produced by Template Haskell,
-- it is not possible to create proper Haddock documentation. Please look
-- up the corresponding operation in @Data.Tuple@. Also, please excuse
-- the apparent repeated variable names. This is due to an interaction
-- between Template Haskell and Haddock.
--
----------------------------------------------------------------------------

module GHC.Base.Singletons (
  -- * Basic functions
  Foldr, sFoldr, Map, sMap, type (++), (%++), Otherwise, sOtherwise,
  Id, sId, Const, sConst, type (.), (%.), type ($), type ($!), (%$), (%$!),
  Until, sUntil, Flip, sFlip, AsTypeOf, sAsTypeOf,
  Seq, sSeq,

  -- * Defunctionalization symbols
  FoldrSym0, FoldrSym1, FoldrSym2, FoldrSym3,
  MapSym0, MapSym1, MapSym2,
  type (++@#@$), type (++@#@$$), type (++@#@$$$),
  OtherwiseSym0,
  IdSym0, IdSym1,
  ConstSym0, ConstSym1, ConstSym2,
  type (.@#@$),  type (.@#@$$),  type (.@#@$$$), type (.@#@$$$$),
  type ($@#@$),  type ($@#@$$),  type ($@#@$$$),
  type ($!@#@$), type ($!@#@$$), type ($!@#@$$$),
  UntilSym0, UntilSym1, UntilSym2, UntilSym3,
  FlipSym0, FlipSym1, FlipSym2, FlipSym3,
  AsTypeOfSym0, AsTypeOfSym1, AsTypeOfSym2,
  SeqSym0, SeqSym1, SeqSym2
  ) where

import Data.Bool.Singletons
import Data.Singletons.Base.Instances
import Data.Singletons.TH
import Data.Kind (Type)

-- Promoted and singletonized versions of "otherwise" are imported and
-- re-exported from Data.Bool.Singletons. This is done to avoid cyclic
-- module dependencies.

type family LamCases_6989586621679168249_aFdM x6989586621679168248 (p6989586621679168242 :: (~>) a6989586621679168109 Bool) (f6989586621679168243 :: (~>) a6989586621679168109 a6989586621679168109) (a_69895866216791682336989586621679168244 :: a6989586621679168109) a_6989586621679168251_aFdO where
      LamCases_6989586621679168249_aFdM x_aFdK p_aFdE f_aFdF a_6989586621679168233_aFdG 'True = x_aFdK
      LamCases_6989586621679168249_aFdM x_aFdK p_aFdE f_aFdF a_6989586621679168233_aFdG 'False = Apply (Let6989586621679168245GoSym0 p_aFdE f_aFdF a_6989586621679168233_aFdG) (Apply f_aFdF x_aFdK)
data LamCases_6989586621679168249Sym0 x6989586621679168248 (p6989586621679168242 :: (~>) a6989586621679168109 Bool) (f6989586621679168243 :: (~>) a6989586621679168109 a6989586621679168109) (a_69895866216791682336989586621679168244 :: a6989586621679168109) a_69895866216791682516989586621679168252
  where
    LamCases_6989586621679168249Sym0KindInference :: SameKind (Apply (LamCases_6989586621679168249Sym0 x6989586621679168248 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244) arg_aFdP) (LamCases_6989586621679168249Sym1 x6989586621679168248 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 arg_aFdP) =>
                                                      LamCases_6989586621679168249Sym0 x6989586621679168248 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 a_69895866216791682516989586621679168252
type instance Apply @_ @_ (LamCases_6989586621679168249Sym0 x6989586621679168248 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244) a_69895866216791682516989586621679168252 = LamCases_6989586621679168249_aFdM x6989586621679168248 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 a_69895866216791682516989586621679168252
instance SuppressUnusedWarnings (LamCases_6989586621679168249Sym0 x6989586621679168248 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679168249Sym0KindInference ())
type family LamCases_6989586621679168249Sym1 x6989586621679168248 (p6989586621679168242 :: (~>) a6989586621679168109 Bool) (f6989586621679168243 :: (~>) a6989586621679168109 a6989586621679168109) (a_69895866216791682336989586621679168244 :: a6989586621679168109) a_69895866216791682516989586621679168252 where
  LamCases_6989586621679168249Sym1 x6989586621679168248 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 a_69895866216791682516989586621679168252 = LamCases_6989586621679168249_aFdM x6989586621679168248 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 a_69895866216791682516989586621679168252
data Let6989586621679168245GoSym0 (p6989586621679168242 :: (~>) a6989586621679168109 Bool) (f6989586621679168243 :: (~>) a6989586621679168109 a6989586621679168109) (a_69895866216791682336989586621679168244 :: a6989586621679168109) a6989586621679168246
  where
    Let6989586621679168245GoSym0KindInference :: SameKind (Apply (Let6989586621679168245GoSym0 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244) arg_aFdJ) (Let6989586621679168245GoSym1 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 arg_aFdJ) =>
                                                  Let6989586621679168245GoSym0 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 a6989586621679168246
type instance Apply @_ @_ (Let6989586621679168245GoSym0 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244) a6989586621679168246 = Let6989586621679168245Go p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 a6989586621679168246
instance SuppressUnusedWarnings (Let6989586621679168245GoSym0 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679168245GoSym0KindInference ())
type family Let6989586621679168245GoSym1 (p6989586621679168242 :: (~>) a6989586621679168109 Bool) (f6989586621679168243 :: (~>) a6989586621679168109 a6989586621679168109) (a_69895866216791682336989586621679168244 :: a6989586621679168109) a6989586621679168246 where
  Let6989586621679168245GoSym1 p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 a6989586621679168246 = Let6989586621679168245Go p6989586621679168242 f6989586621679168243 a_69895866216791682336989586621679168244 a6989586621679168246
type family Let6989586621679168245Go (p6989586621679168242 :: (~>) a6989586621679168109 Bool) (f6989586621679168243 :: (~>) a6989586621679168109 a6989586621679168109) (a_69895866216791682336989586621679168244 :: a6989586621679168109) a_aFdI where
  Let6989586621679168245Go p_aFdE f_aFdF a_6989586621679168233_aFdG x_aFdK = Apply (LamCases_6989586621679168249Sym0 x_aFdK p_aFdE f_aFdF a_6989586621679168233_aFdG) (Apply p_aFdE x_aFdK)
type family Let6989586621679168261VxSym0 (f6989586621679168259 :: (~>) a6989586621679168110 b6989586621679168111) (x6989586621679168260 :: a6989586621679168110) where
  Let6989586621679168261VxSym0 f6989586621679168259 x6989586621679168260 = Let6989586621679168261Vx f6989586621679168259 x6989586621679168260
type family Let6989586621679168261Vx (f6989586621679168259 :: (~>) a6989586621679168110 b6989586621679168111) (x6989586621679168260 :: a6989586621679168110) where
  Let6989586621679168261Vx f_aFdV x_aFdW = x_aFdW
type family LamCases_6989586621679168303_aFeE (f6989586621679168300 :: (~>) b6989586621679168118 c6989586621679168119) (g6989586621679168301 :: (~>) a6989586621679168120 b6989586621679168118) (a_69895866216791682916989586621679168302 :: a6989586621679168120) a_6989586621679168306_aFeH where
  LamCases_6989586621679168303_aFeE f_aFeA g_aFeB a_6989586621679168291_aFeC x_aFeF = Apply f_aFeA (Apply g_aFeB x_aFeF)
data LamCases_6989586621679168303Sym0 (f6989586621679168300 :: (~>) b6989586621679168118 c6989586621679168119) (g6989586621679168301 :: (~>) a6989586621679168120 b6989586621679168118) (a_69895866216791682916989586621679168302 :: a6989586621679168120) a_69895866216791683066989586621679168307
  where
    LamCases_6989586621679168303Sym0KindInference :: SameKind (Apply (LamCases_6989586621679168303Sym0 f6989586621679168300 g6989586621679168301 a_69895866216791682916989586621679168302) arg_aFeI) (LamCases_6989586621679168303Sym1 f6989586621679168300 g6989586621679168301 a_69895866216791682916989586621679168302 arg_aFeI) =>
                                                      LamCases_6989586621679168303Sym0 f6989586621679168300 g6989586621679168301 a_69895866216791682916989586621679168302 a_69895866216791683066989586621679168307
type instance Apply @_ @_ (LamCases_6989586621679168303Sym0 f6989586621679168300 g6989586621679168301 a_69895866216791682916989586621679168302) a_69895866216791683066989586621679168307 = LamCases_6989586621679168303_aFeE f6989586621679168300 g6989586621679168301 a_69895866216791682916989586621679168302 a_69895866216791683066989586621679168307
instance SuppressUnusedWarnings (LamCases_6989586621679168303Sym0 f6989586621679168300 g6989586621679168301 a_69895866216791682916989586621679168302) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679168303Sym0KindInference ())
type family LamCases_6989586621679168303Sym1 (f6989586621679168300 :: (~>) b6989586621679168118 c6989586621679168119) (g6989586621679168301 :: (~>) a6989586621679168120 b6989586621679168118) (a_69895866216791682916989586621679168302 :: a6989586621679168120) a_69895866216791683066989586621679168307 where
  LamCases_6989586621679168303Sym1 f6989586621679168300 g6989586621679168301 a_69895866216791682916989586621679168302 a_69895866216791683066989586621679168307 = LamCases_6989586621679168303_aFeE f6989586621679168300 g6989586621679168301 a_69895866216791682916989586621679168302 a_69895866216791683066989586621679168307
data Let6989586621679168348GoSym0 (k6989586621679168345 :: (~>) a6989586621679168127 ((~>) b6989586621679168128 b6989586621679168128)) (z6989586621679168346 :: b6989586621679168128) (a_69895866216791683366989586621679168347 :: [a6989586621679168127]) a6989586621679168349
  where
    Let6989586621679168348GoSym0KindInference :: SameKind (Apply (Let6989586621679168348GoSym0 k6989586621679168345 z6989586621679168346 a_69895866216791683366989586621679168347) arg_aFfo) (Let6989586621679168348GoSym1 k6989586621679168345 z6989586621679168346 a_69895866216791683366989586621679168347 arg_aFfo) =>
                                                  Let6989586621679168348GoSym0 k6989586621679168345 z6989586621679168346 a_69895866216791683366989586621679168347 a6989586621679168349
type instance Apply @_ @_ (Let6989586621679168348GoSym0 k6989586621679168345 z6989586621679168346 a_69895866216791683366989586621679168347) a6989586621679168349 = Let6989586621679168348Go k6989586621679168345 z6989586621679168346 a_69895866216791683366989586621679168347 a6989586621679168349
instance SuppressUnusedWarnings (Let6989586621679168348GoSym0 k6989586621679168345 z6989586621679168346 a_69895866216791683366989586621679168347) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679168348GoSym0KindInference ())
type family Let6989586621679168348GoSym1 (k6989586621679168345 :: (~>) a6989586621679168127 ((~>) b6989586621679168128 b6989586621679168128)) (z6989586621679168346 :: b6989586621679168128) (a_69895866216791683366989586621679168347 :: [a6989586621679168127]) a6989586621679168349 where
  Let6989586621679168348GoSym1 k6989586621679168345 z6989586621679168346 a_69895866216791683366989586621679168347 a6989586621679168349 = Let6989586621679168348Go k6989586621679168345 z6989586621679168346 a_69895866216791683366989586621679168347 a6989586621679168349
type family Let6989586621679168348Go (k6989586621679168345 :: (~>) a6989586621679168127 ((~>) b6989586621679168128 b6989586621679168128)) (z6989586621679168346 :: b6989586621679168128) (a_69895866216791683366989586621679168347 :: [a6989586621679168127]) a_aFfn where
  Let6989586621679168348Go k_aFfj z_aFfk a_6989586621679168336_aFfl '[] = z_aFfk
  Let6989586621679168348Go k_aFfj z_aFfk a_6989586621679168336_aFfl ('(:) y_aFfp ys_aFfq) = Apply (Apply k_aFfj y_aFfp) (Apply (Let6989586621679168348GoSym0 k_aFfj z_aFfk a_6989586621679168336_aFfl) ys_aFfq)
type SeqSym0 :: (~>) a_aFbt ((~>) b_aFbu b_aFbu)
data SeqSym0 :: (~>) a_aFbt ((~>) b_aFbu b_aFbu)
  where
    SeqSym0KindInference :: SameKind (Apply SeqSym0 arg_aFdr) (SeqSym1 arg_aFdr) =>
                            SeqSym0 a6989586621679168230
type instance Apply @a_aFbt @((~>) b_aFbu b_aFbu) SeqSym0 a6989586621679168230 = SeqSym1 a6989586621679168230
instance SuppressUnusedWarnings SeqSym0 where
  suppressUnusedWarnings = snd ((,) SeqSym0KindInference ())
infixr 0 `SeqSym0`
type SeqSym1 :: a_aFbt -> (~>) b_aFbu b_aFbu
data SeqSym1 (a6989586621679168230 :: a_aFbt) :: (~>) b_aFbu b_aFbu
  where
    SeqSym1KindInference :: SameKind (Apply (SeqSym1 a6989586621679168230) arg_aFdr) (SeqSym2 a6989586621679168230 arg_aFdr) =>
                            SeqSym1 a6989586621679168230 a6989586621679168231
type instance Apply @b_aFbu @b_aFbu (SeqSym1 a6989586621679168230) a6989586621679168231 = Seq a6989586621679168230 a6989586621679168231
instance SuppressUnusedWarnings (SeqSym1 a6989586621679168230) where
  suppressUnusedWarnings = snd ((,) SeqSym1KindInference ())
infixr 0 `SeqSym1`
type SeqSym2 :: a_aFbt -> b_aFbu -> b_aFbu
type family SeqSym2 @a_aFbt @b_aFbu (a6989586621679168230 :: a_aFbt) (a6989586621679168231 :: b_aFbu) :: b_aFbu where
  SeqSym2 a6989586621679168230 a6989586621679168231 = Seq a6989586621679168230 a6989586621679168231
infixr 0 `SeqSym2`
type UntilSym0 :: (~>) ((~>) a_aFbv Bool) ((~>) ((~>) a_aFbv a_aFbv) ((~>) a_aFbv a_aFbv))
data UntilSym0 :: (~>) ((~>) a_aFbv Bool) ((~>) ((~>) a_aFbv a_aFbv) ((~>) a_aFbv a_aFbv))
  where
    UntilSym0KindInference :: SameKind (Apply UntilSym0 arg_aFdA) (UntilSym1 arg_aFdA) =>
                              UntilSym0 a6989586621679168239
type instance Apply @((~>) a_aFbv Bool) @((~>) ((~>) a_aFbv a_aFbv) ((~>) a_aFbv a_aFbv)) UntilSym0 a6989586621679168239 = UntilSym1 a6989586621679168239
instance SuppressUnusedWarnings UntilSym0 where
  suppressUnusedWarnings = snd ((,) UntilSym0KindInference ())
type UntilSym1 :: (~>) a_aFbv Bool
                  -> (~>) ((~>) a_aFbv a_aFbv) ((~>) a_aFbv a_aFbv)
data UntilSym1 (a6989586621679168239 :: (~>) a_aFbv Bool) :: (~>) ((~>) a_aFbv a_aFbv) ((~>) a_aFbv a_aFbv)
  where
    UntilSym1KindInference :: SameKind (Apply (UntilSym1 a6989586621679168239) arg_aFdA) (UntilSym2 a6989586621679168239 arg_aFdA) =>
                              UntilSym1 a6989586621679168239 a6989586621679168240
type instance Apply @((~>) a_aFbv a_aFbv) @((~>) a_aFbv a_aFbv) (UntilSym1 a6989586621679168239) a6989586621679168240 = UntilSym2 a6989586621679168239 a6989586621679168240
instance SuppressUnusedWarnings (UntilSym1 a6989586621679168239) where
  suppressUnusedWarnings = snd ((,) UntilSym1KindInference ())
type UntilSym2 :: (~>) a_aFbv Bool
                  -> (~>) a_aFbv a_aFbv -> (~>) a_aFbv a_aFbv
data UntilSym2 (a6989586621679168239 :: (~>) a_aFbv Bool) (a6989586621679168240 :: (~>) a_aFbv a_aFbv) :: (~>) a_aFbv a_aFbv
  where
    UntilSym2KindInference :: SameKind (Apply (UntilSym2 a6989586621679168239 a6989586621679168240) arg_aFdA) (UntilSym3 a6989586621679168239 a6989586621679168240 arg_aFdA) =>
                              UntilSym2 a6989586621679168239 a6989586621679168240 a6989586621679168241
type instance Apply @a_aFbv @a_aFbv (UntilSym2 a6989586621679168239 a6989586621679168240) a6989586621679168241 = Until a6989586621679168239 a6989586621679168240 a6989586621679168241
instance SuppressUnusedWarnings (UntilSym2 a6989586621679168239 a6989586621679168240) where
  suppressUnusedWarnings = snd ((,) UntilSym2KindInference ())
type UntilSym3 :: (~>) a_aFbv Bool
                  -> (~>) a_aFbv a_aFbv -> a_aFbv -> a_aFbv
type family UntilSym3 @a_aFbv (a6989586621679168239 :: (~>) a_aFbv Bool) (a6989586621679168240 :: (~>) a_aFbv a_aFbv) (a6989586621679168241 :: a_aFbv) :: a_aFbv where
  UntilSym3 a6989586621679168239 a6989586621679168240 a6989586621679168241 = Until a6989586621679168239 a6989586621679168240 a6989586621679168241
type ($!@#@$) :: (~>) ((~>) a_aFbw b_aFbx) ((~>) a_aFbw b_aFbx)
data ($!@#@$) :: (~>) ((~>) a_aFbw b_aFbx) ((~>) a_aFbw b_aFbx)
  where
    (:$!@#@$###) :: SameKind (Apply ($!@#@$) arg_aFdS) (($!@#@$$) arg_aFdS) =>
                    ($!@#@$) a6989586621679168257
type instance Apply @((~>) a_aFbw b_aFbx) @((~>) a_aFbw b_aFbx) ($!@#@$) a6989586621679168257 = ($!@#@$$) a6989586621679168257
instance SuppressUnusedWarnings ($!@#@$) where
  suppressUnusedWarnings = snd ((,) (:$!@#@$###) ())
infixr 0 $!@#@$
type ($!@#@$$) :: (~>) a_aFbw b_aFbx -> (~>) a_aFbw b_aFbx
data ($!@#@$$) (a6989586621679168257 :: (~>) a_aFbw b_aFbx) :: (~>) a_aFbw b_aFbx
  where
    (:$!@#@$$###) :: SameKind (Apply (($!@#@$$) a6989586621679168257) arg_aFdS) (($!@#@$$$) a6989586621679168257 arg_aFdS) =>
                      ($!@#@$$) a6989586621679168257 a6989586621679168258
type instance Apply @a_aFbw @b_aFbx (($!@#@$$) a6989586621679168257) a6989586621679168258 = ($!) a6989586621679168257 a6989586621679168258
instance SuppressUnusedWarnings (($!@#@$$) a6989586621679168257) where
  suppressUnusedWarnings = snd ((,) (:$!@#@$$###) ())
infixr 0 $!@#@$$
type ($!@#@$$$) :: (~>) a_aFbw b_aFbx -> a_aFbw -> b_aFbx
type family ($!@#@$$$) @a_aFbw @b_aFbx (a6989586621679168257 :: (~>) a_aFbw b_aFbx) (a6989586621679168258 :: a_aFbw) :: b_aFbx where
  ($!@#@$$$) a6989586621679168257 a6989586621679168258 = ($!) a6989586621679168257 a6989586621679168258
infixr 0 $!@#@$$$
type ($@#@$) :: (~>) ((~>) a_aFby b_aFbz) ((~>) a_aFby b_aFbz)
data ($@#@$) :: (~>) ((~>) a_aFby b_aFbz) ((~>) a_aFby b_aFbz)
  where
    (:$@#@$###) :: SameKind (Apply ($@#@$) arg_aFe1) (($@#@$$) arg_aFe1) =>
                    ($@#@$) a6989586621679168266
type instance Apply @((~>) a_aFby b_aFbz) @((~>) a_aFby b_aFbz) ($@#@$) a6989586621679168266 = ($@#@$$) a6989586621679168266
instance SuppressUnusedWarnings ($@#@$) where
  suppressUnusedWarnings = snd ((,) (:$@#@$###) ())
infixr 0 $@#@$
type ($@#@$$) :: (~>) a_aFby b_aFbz -> (~>) a_aFby b_aFbz
data ($@#@$$) (a6989586621679168266 :: (~>) a_aFby b_aFbz) :: (~>) a_aFby b_aFbz
  where
    (:$@#@$$###) :: SameKind (Apply (($@#@$$) a6989586621679168266) arg_aFe1) (($@#@$$$) a6989586621679168266 arg_aFe1) =>
                    ($@#@$$) a6989586621679168266 a6989586621679168267
type instance Apply @a_aFby @b_aFbz (($@#@$$) a6989586621679168266) a6989586621679168267 = ($) a6989586621679168266 a6989586621679168267
instance SuppressUnusedWarnings (($@#@$$) a6989586621679168266) where
  suppressUnusedWarnings = snd ((,) (:$@#@$$###) ())
infixr 0 $@#@$$
type ($@#@$$$) :: (~>) a_aFby b_aFbz -> a_aFby -> b_aFbz
type family ($@#@$$$) @a_aFby @b_aFbz (a6989586621679168266 :: (~>) a_aFby b_aFbz) (a6989586621679168267 :: a_aFby) :: b_aFbz where
  ($@#@$$$) a6989586621679168266 a6989586621679168267 = ($) a6989586621679168266 a6989586621679168267
infixr 0 $@#@$$$
type AsTypeOfSym0 :: (~>) a_aFbA ((~>) a_aFbA a_aFbA)
data AsTypeOfSym0 :: (~>) a_aFbA ((~>) a_aFbA a_aFbA)
  where
    AsTypeOfSym0KindInference :: SameKind (Apply AsTypeOfSym0 arg_aFec) (AsTypeOfSym1 arg_aFec) =>
                                  AsTypeOfSym0 a6989586621679168277
type instance Apply @a_aFbA @((~>) a_aFbA a_aFbA) AsTypeOfSym0 a6989586621679168277 = AsTypeOfSym1 a6989586621679168277
instance SuppressUnusedWarnings AsTypeOfSym0 where
  suppressUnusedWarnings = snd ((,) AsTypeOfSym0KindInference ())
type AsTypeOfSym1 :: a_aFbA -> (~>) a_aFbA a_aFbA
data AsTypeOfSym1 (a6989586621679168277 :: a_aFbA) :: (~>) a_aFbA a_aFbA
  where
    AsTypeOfSym1KindInference :: SameKind (Apply (AsTypeOfSym1 a6989586621679168277) arg_aFec) (AsTypeOfSym2 a6989586621679168277 arg_aFec) =>
                                  AsTypeOfSym1 a6989586621679168277 a6989586621679168278
type instance Apply @a_aFbA @a_aFbA (AsTypeOfSym1 a6989586621679168277) a6989586621679168278 = AsTypeOf a6989586621679168277 a6989586621679168278
instance SuppressUnusedWarnings (AsTypeOfSym1 a6989586621679168277) where
  suppressUnusedWarnings = snd ((,) AsTypeOfSym1KindInference ())
type AsTypeOfSym2 :: a_aFbA -> a_aFbA -> a_aFbA
type family AsTypeOfSym2 @a_aFbA (a6989586621679168277 :: a_aFbA) (a6989586621679168278 :: a_aFbA) :: a_aFbA where
  AsTypeOfSym2 a6989586621679168277 a6989586621679168278 = AsTypeOf a6989586621679168277 a6989586621679168278
type FlipSym0 :: (~>) ((~>) a_aFbB ((~>) b_aFbC c_aFbD)) ((~>) b_aFbC ((~>) a_aFbB c_aFbD))
data FlipSym0 :: (~>) ((~>) a_aFbB ((~>) b_aFbC c_aFbD)) ((~>) b_aFbC ((~>) a_aFbB c_aFbD))
  where
    FlipSym0KindInference :: SameKind (Apply FlipSym0 arg_aFek) (FlipSym1 arg_aFek) =>
                              FlipSym0 a6989586621679168285
type instance Apply @((~>) a_aFbB ((~>) b_aFbC c_aFbD)) @((~>) b_aFbC ((~>) a_aFbB c_aFbD)) FlipSym0 a6989586621679168285 = FlipSym1 a6989586621679168285
instance SuppressUnusedWarnings FlipSym0 where
  suppressUnusedWarnings = snd ((,) FlipSym0KindInference ())
type FlipSym1 :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)
                  -> (~>) b_aFbC ((~>) a_aFbB c_aFbD)
data FlipSym1 (a6989586621679168285 :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) :: (~>) b_aFbC ((~>) a_aFbB c_aFbD)
  where
    FlipSym1KindInference :: SameKind (Apply (FlipSym1 a6989586621679168285) arg_aFek) (FlipSym2 a6989586621679168285 arg_aFek) =>
                              FlipSym1 a6989586621679168285 a6989586621679168286
type instance Apply @b_aFbC @((~>) a_aFbB c_aFbD) (FlipSym1 a6989586621679168285) a6989586621679168286 = FlipSym2 a6989586621679168285 a6989586621679168286
instance SuppressUnusedWarnings (FlipSym1 a6989586621679168285) where
  suppressUnusedWarnings = snd ((,) FlipSym1KindInference ())
type FlipSym2 :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)
                  -> b_aFbC -> (~>) a_aFbB c_aFbD
data FlipSym2 (a6989586621679168285 :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) (a6989586621679168286 :: b_aFbC) :: (~>) a_aFbB c_aFbD
  where
    FlipSym2KindInference :: SameKind (Apply (FlipSym2 a6989586621679168285 a6989586621679168286) arg_aFek) (FlipSym3 a6989586621679168285 a6989586621679168286 arg_aFek) =>
                              FlipSym2 a6989586621679168285 a6989586621679168286 a6989586621679168287
type instance Apply @a_aFbB @c_aFbD (FlipSym2 a6989586621679168285 a6989586621679168286) a6989586621679168287 = Flip a6989586621679168285 a6989586621679168286 a6989586621679168287
instance SuppressUnusedWarnings (FlipSym2 a6989586621679168285 a6989586621679168286) where
  suppressUnusedWarnings = snd ((,) FlipSym2KindInference ())
type FlipSym3 :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)
                  -> b_aFbC -> a_aFbB -> c_aFbD
type family FlipSym3 @a_aFbB @b_aFbC @c_aFbD (a6989586621679168285 :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) (a6989586621679168286 :: b_aFbC) (a6989586621679168287 :: a_aFbB) :: c_aFbD where
  FlipSym3 a6989586621679168285 a6989586621679168286 a6989586621679168287 = Flip a6989586621679168285 a6989586621679168286 a6989586621679168287
type (.@#@$) :: (~>) ((~>) b_aFbE c_aFbF) ((~>) ((~>) a_aFbG b_aFbE) ((~>) a_aFbG c_aFbF))
data (.@#@$) :: (~>) ((~>) b_aFbE c_aFbF) ((~>) ((~>) a_aFbG b_aFbE) ((~>) a_aFbG c_aFbF))
  where
    (:.@#@$###) :: SameKind (Apply (.@#@$) arg_aFew) ((.@#@$$) arg_aFew) =>
                    (.@#@$) a6989586621679168297
type instance Apply @((~>) b_aFbE c_aFbF) @((~>) ((~>) a_aFbG b_aFbE) ((~>) a_aFbG c_aFbF)) (.@#@$) a6989586621679168297 = (.@#@$$) a6989586621679168297
instance SuppressUnusedWarnings (.@#@$) where
  suppressUnusedWarnings = snd ((,) (:.@#@$###) ())
infixr 9 .@#@$
type (.@#@$$) :: (~>) b_aFbE c_aFbF
                  -> (~>) ((~>) a_aFbG b_aFbE) ((~>) a_aFbG c_aFbF)
data (.@#@$$) (a6989586621679168297 :: (~>) b_aFbE c_aFbF) :: (~>) ((~>) a_aFbG b_aFbE) ((~>) a_aFbG c_aFbF)
  where
    (:.@#@$$###) :: SameKind (Apply ((.@#@$$) a6989586621679168297) arg_aFew) ((.@#@$$$) a6989586621679168297 arg_aFew) =>
                    (.@#@$$) a6989586621679168297 a6989586621679168298
type instance Apply @((~>) a_aFbG b_aFbE) @((~>) a_aFbG c_aFbF) ((.@#@$$) a6989586621679168297) a6989586621679168298 = (.@#@$$$) a6989586621679168297 a6989586621679168298
instance SuppressUnusedWarnings ((.@#@$$) a6989586621679168297) where
  suppressUnusedWarnings = snd ((,) (:.@#@$$###) ())
infixr 9 .@#@$$
type (.@#@$$$) :: (~>) b_aFbE c_aFbF
                  -> (~>) a_aFbG b_aFbE -> (~>) a_aFbG c_aFbF
data (.@#@$$$) (a6989586621679168297 :: (~>) b_aFbE c_aFbF) (a6989586621679168298 :: (~>) a_aFbG b_aFbE) :: (~>) a_aFbG c_aFbF
  where
    (:.@#@$$$###) :: SameKind (Apply ((.@#@$$$) a6989586621679168297 a6989586621679168298) arg_aFew) ((.@#@$$$$) a6989586621679168297 a6989586621679168298 arg_aFew) =>
                      (.@#@$$$) a6989586621679168297 a6989586621679168298 a6989586621679168299
type instance Apply @a_aFbG @c_aFbF ((.@#@$$$) a6989586621679168297 a6989586621679168298) a6989586621679168299 = (.) a6989586621679168297 a6989586621679168298 a6989586621679168299
instance SuppressUnusedWarnings ((.@#@$$$) a6989586621679168297 a6989586621679168298) where
  suppressUnusedWarnings = snd ((,) (:.@#@$$$###) ())
infixr 9 .@#@$$$
type (.@#@$$$$) :: (~>) b_aFbE c_aFbF
                    -> (~>) a_aFbG b_aFbE -> a_aFbG -> c_aFbF
type family (.@#@$$$$) @b_aFbE @c_aFbF @a_aFbG (a6989586621679168297 :: (~>) b_aFbE c_aFbF) (a6989586621679168298 :: (~>) a_aFbG b_aFbE) (a6989586621679168299 :: a_aFbG) :: c_aFbF where
  (.@#@$$$$) a6989586621679168297 a6989586621679168298 a6989586621679168299 = (.) a6989586621679168297 a6989586621679168298 a6989586621679168299
infixr 9 .@#@$$$$
type ConstSym0 :: (~>) a_aFbH ((~>) b_aFbI a_aFbH)
data ConstSym0 :: (~>) a_aFbH ((~>) b_aFbI a_aFbH)
  where
    ConstSym0KindInference :: SameKind (Apply ConstSym0 arg_aFeL) (ConstSym1 arg_aFeL) =>
                              ConstSym0 a6989586621679168312
type instance Apply @a_aFbH @((~>) b_aFbI a_aFbH) ConstSym0 a6989586621679168312 = ConstSym1 a6989586621679168312
instance SuppressUnusedWarnings ConstSym0 where
  suppressUnusedWarnings = snd ((,) ConstSym0KindInference ())
type ConstSym1 :: a_aFbH -> (~>) b_aFbI a_aFbH
data ConstSym1 (a6989586621679168312 :: a_aFbH) :: (~>) b_aFbI a_aFbH
  where
    ConstSym1KindInference :: SameKind (Apply (ConstSym1 a6989586621679168312) arg_aFeL) (ConstSym2 a6989586621679168312 arg_aFeL) =>
                              ConstSym1 a6989586621679168312 a6989586621679168313
type instance Apply @b_aFbI @a_aFbH (ConstSym1 a6989586621679168312) a6989586621679168313 = Const a6989586621679168312 a6989586621679168313
instance SuppressUnusedWarnings (ConstSym1 a6989586621679168312) where
  suppressUnusedWarnings = snd ((,) ConstSym1KindInference ())
type ConstSym2 :: a_aFbH -> b_aFbI -> a_aFbH
type family ConstSym2 @a_aFbH @b_aFbI (a6989586621679168312 :: a_aFbH) (a6989586621679168313 :: b_aFbI) :: a_aFbH where
  ConstSym2 a6989586621679168312 a6989586621679168313 = Const a6989586621679168312 a6989586621679168313
type IdSym0 :: (~>) a_aFbJ a_aFbJ
data IdSym0 :: (~>) a_aFbJ a_aFbJ
  where
    IdSym0KindInference :: SameKind (Apply IdSym0 arg_aFeQ) (IdSym1 arg_aFeQ) =>
                            IdSym0 a6989586621679168317
type instance Apply @a_aFbJ @a_aFbJ IdSym0 a6989586621679168317 = Id a6989586621679168317
instance SuppressUnusedWarnings IdSym0 where
  suppressUnusedWarnings = snd ((,) IdSym0KindInference ())
type IdSym1 :: a_aFbJ -> a_aFbJ
type family IdSym1 @a_aFbJ (a6989586621679168317 :: a_aFbJ) :: a_aFbJ where
  IdSym1 a6989586621679168317 = Id a6989586621679168317
type (++@#@$) :: (~>) [a_aFbK] ((~>) [a_aFbK] [a_aFbK])
data (++@#@$) :: (~>) [a_aFbK] ((~>) [a_aFbK] [a_aFbK])
  where
    (:++@#@$###) :: SameKind (Apply (++@#@$) arg_aFeV) ((++@#@$$) arg_aFeV) =>
                    (++@#@$) a6989586621679168322
type instance Apply @[a_aFbK] @((~>) [a_aFbK] [a_aFbK]) (++@#@$) a6989586621679168322 = (++@#@$$) a6989586621679168322
instance SuppressUnusedWarnings (++@#@$) where
  suppressUnusedWarnings = snd ((,) (:++@#@$###) ())
infixr 5 ++@#@$
type (++@#@$$) :: [a_aFbK] -> (~>) [a_aFbK] [a_aFbK]
data (++@#@$$) (a6989586621679168322 :: [a_aFbK]) :: (~>) [a_aFbK] [a_aFbK]
  where
    (:++@#@$$###) :: SameKind (Apply ((++@#@$$) a6989586621679168322) arg_aFeV) ((++@#@$$$) a6989586621679168322 arg_aFeV) =>
                      (++@#@$$) a6989586621679168322 a6989586621679168323
type instance Apply @[a_aFbK] @[a_aFbK] ((++@#@$$) a6989586621679168322) a6989586621679168323 = (++) a6989586621679168322 a6989586621679168323
instance SuppressUnusedWarnings ((++@#@$$) a6989586621679168322) where
  suppressUnusedWarnings = snd ((,) (:++@#@$$###) ())
infixr 5 ++@#@$$
type (++@#@$$$) :: [a_aFbK] -> [a_aFbK] -> [a_aFbK]
type family (++@#@$$$) @a_aFbK (a6989586621679168322 :: [a_aFbK]) (a6989586621679168323 :: [a_aFbK]) :: [a_aFbK] where
  (++@#@$$$) a6989586621679168322 a6989586621679168323 = (++) a6989586621679168322 a6989586621679168323
infixr 5 ++@#@$$$
type MapSym0 :: (~>) ((~>) a_aFbL b_aFbM) ((~>) [a_aFbL] [b_aFbM])
data MapSym0 :: (~>) ((~>) a_aFbL b_aFbM) ((~>) [a_aFbL] [b_aFbM])
  where
    MapSym0KindInference :: SameKind (Apply MapSym0 arg_aFf4) (MapSym1 arg_aFf4) =>
                            MapSym0 a6989586621679168331
type instance Apply @((~>) a_aFbL b_aFbM) @((~>) [a_aFbL] [b_aFbM]) MapSym0 a6989586621679168331 = MapSym1 a6989586621679168331
instance SuppressUnusedWarnings MapSym0 where
  suppressUnusedWarnings = snd ((,) MapSym0KindInference ())
type MapSym1 :: (~>) a_aFbL b_aFbM -> (~>) [a_aFbL] [b_aFbM]
data MapSym1 (a6989586621679168331 :: (~>) a_aFbL b_aFbM) :: (~>) [a_aFbL] [b_aFbM]
  where
    MapSym1KindInference :: SameKind (Apply (MapSym1 a6989586621679168331) arg_aFf4) (MapSym2 a6989586621679168331 arg_aFf4) =>
                            MapSym1 a6989586621679168331 a6989586621679168332
type instance Apply @[a_aFbL] @[b_aFbM] (MapSym1 a6989586621679168331) a6989586621679168332 = Map a6989586621679168331 a6989586621679168332
instance SuppressUnusedWarnings (MapSym1 a6989586621679168331) where
  suppressUnusedWarnings = snd ((,) MapSym1KindInference ())
type MapSym2 :: (~>) a_aFbL b_aFbM -> [a_aFbL] -> [b_aFbM]
type family MapSym2 @a_aFbL @b_aFbM (a6989586621679168331 :: (~>) a_aFbL b_aFbM) (a6989586621679168332 :: [a_aFbL]) :: [b_aFbM] where
  MapSym2 a6989586621679168331 a6989586621679168332 = Map a6989586621679168331 a6989586621679168332
type FoldrSym0 :: (~>) ((~>) a_aFbN ((~>) b_aFbO b_aFbO)) ((~>) b_aFbO ((~>) [a_aFbN] b_aFbO))
data FoldrSym0 :: (~>) ((~>) a_aFbN ((~>) b_aFbO b_aFbO)) ((~>) b_aFbO ((~>) [a_aFbN] b_aFbO))
  where
    FoldrSym0KindInference :: SameKind (Apply FoldrSym0 arg_aFff) (FoldrSym1 arg_aFff) =>
                              FoldrSym0 a6989586621679168342
type instance Apply @((~>) a_aFbN ((~>) b_aFbO b_aFbO)) @((~>) b_aFbO ((~>) [a_aFbN] b_aFbO)) FoldrSym0 a6989586621679168342 = FoldrSym1 a6989586621679168342
instance SuppressUnusedWarnings FoldrSym0 where
  suppressUnusedWarnings = snd ((,) FoldrSym0KindInference ())
type FoldrSym1 :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)
                  -> (~>) b_aFbO ((~>) [a_aFbN] b_aFbO)
data FoldrSym1 (a6989586621679168342 :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) :: (~>) b_aFbO ((~>) [a_aFbN] b_aFbO)
  where
    FoldrSym1KindInference :: SameKind (Apply (FoldrSym1 a6989586621679168342) arg_aFff) (FoldrSym2 a6989586621679168342 arg_aFff) =>
                              FoldrSym1 a6989586621679168342 a6989586621679168343
type instance Apply @b_aFbO @((~>) [a_aFbN] b_aFbO) (FoldrSym1 a6989586621679168342) a6989586621679168343 = FoldrSym2 a6989586621679168342 a6989586621679168343
instance SuppressUnusedWarnings (FoldrSym1 a6989586621679168342) where
  suppressUnusedWarnings = snd ((,) FoldrSym1KindInference ())
type FoldrSym2 :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)
                  -> b_aFbO -> (~>) [a_aFbN] b_aFbO
data FoldrSym2 (a6989586621679168342 :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) (a6989586621679168343 :: b_aFbO) :: (~>) [a_aFbN] b_aFbO
  where
    FoldrSym2KindInference :: SameKind (Apply (FoldrSym2 a6989586621679168342 a6989586621679168343) arg_aFff) (FoldrSym3 a6989586621679168342 a6989586621679168343 arg_aFff) =>
                              FoldrSym2 a6989586621679168342 a6989586621679168343 a6989586621679168344
type instance Apply @[a_aFbN] @b_aFbO (FoldrSym2 a6989586621679168342 a6989586621679168343) a6989586621679168344 = Foldr a6989586621679168342 a6989586621679168343 a6989586621679168344
instance SuppressUnusedWarnings (FoldrSym2 a6989586621679168342 a6989586621679168343) where
  suppressUnusedWarnings = snd ((,) FoldrSym2KindInference ())
type FoldrSym3 :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)
                  -> b_aFbO -> [a_aFbN] -> b_aFbO
type family FoldrSym3 @a_aFbN @b_aFbO (a6989586621679168342 :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) (a6989586621679168343 :: b_aFbO) (a6989586621679168344 :: [a_aFbN]) :: b_aFbO where
  FoldrSym3 a6989586621679168342 a6989586621679168343 a6989586621679168344 = Foldr a6989586621679168342 a6989586621679168343 a6989586621679168344
type Seq :: a_aFbt -> b_aFbu -> b_aFbu
type family Seq @a_aFbt @b_aFbu (a_aFdp :: a_aFbt) (a_aFdq :: b_aFbu) :: b_aFbu where
  Seq _ x_aFdu = x_aFdu
type Until :: (~>) a_aFbv Bool
              -> (~>) a_aFbv a_aFbv -> a_aFbv -> a_aFbv
type family Until @a_aFbv (a_aFdx :: (~>) a_aFbv Bool) (a_aFdy :: (~>) a_aFbv a_aFbv) (a_aFdz :: a_aFbv) :: a_aFbv where
  Until p_aFdE f_aFdF a_6989586621679168233_aFdG = Apply (Let6989586621679168245GoSym0 p_aFdE f_aFdF a_6989586621679168233_aFdG) a_6989586621679168233_aFdG
type ($!) :: (~>) a_aFbw b_aFbx -> a_aFbw -> b_aFbx
type family ($!) @a_aFbw @b_aFbx (a_aFdQ :: (~>) a_aFbw b_aFbx) (a_aFdR :: a_aFbw) :: b_aFbx where
  ($!) f_aFdV x_aFdW = Apply f_aFdV (Let6989586621679168261VxSym0 f_aFdV x_aFdW)
type ($) :: (~>) a_aFby b_aFbz -> a_aFby -> b_aFbz
type family ($) @a_aFby @b_aFbz (a_aFdZ :: (~>) a_aFby b_aFbz) (a_aFe0 :: a_aFby) :: b_aFbz where
  ($) f_aFe4 x_aFe5 = Apply f_aFe4 x_aFe5
type AsTypeOf :: a_aFbA -> a_aFbA -> a_aFbA
type family AsTypeOf @a_aFbA (a_aFea :: a_aFbA) (a_aFeb :: a_aFbA) :: a_aFbA where
  AsTypeOf a_6989586621679168270_aFef a_6989586621679168272_aFeg = Apply (Apply ConstSym0 a_6989586621679168270_aFef) a_6989586621679168272_aFeg
type Flip :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)
              -> b_aFbC -> a_aFbB -> c_aFbD
type family Flip @a_aFbB @b_aFbC @c_aFbD (a_aFeh :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) (a_aFei :: b_aFbC) (a_aFej :: a_aFbB) :: c_aFbD where
  Flip f_aFeo x_aFep y_aFeq = Apply (Apply f_aFeo y_aFeq) x_aFep
type (.) :: (~>) b_aFbE c_aFbF
            -> (~>) a_aFbG b_aFbE -> a_aFbG -> c_aFbF
type family (.) @b_aFbE @c_aFbF @a_aFbG (a_aFet :: (~>) b_aFbE c_aFbF) (a_aFeu :: (~>) a_aFbG b_aFbE) (a_aFev :: a_aFbG) :: c_aFbF where
  (.) f_aFeA g_aFeB a_6989586621679168291_aFeC = Apply (LamCases_6989586621679168303Sym0 f_aFeA g_aFeB a_6989586621679168291_aFeC) a_6989586621679168291_aFeC
type Const :: a_aFbH -> b_aFbI -> a_aFbH
type family Const @a_aFbH @b_aFbI (a_aFeJ :: a_aFbH) (a_aFeK :: b_aFbI) :: a_aFbH where
  Const x_aFeO _ = x_aFeO
type Id :: a_aFbJ -> a_aFbJ
type family Id @a_aFbJ (a_aFeP :: a_aFbJ) :: a_aFbJ where
  Id x_aFeS = x_aFeS
type (++) :: [a_aFbK] -> [a_aFbK] -> [a_aFbK]
type family (++) @a_aFbK (a_aFeT :: [a_aFbK]) (a_aFeU :: [a_aFbK]) :: [a_aFbK] where
  (++) '[] ys_aFeY = ys_aFeY
  (++) ('(:) x_aFeZ xs_aFf0) ys_aFf1 = Apply (Apply (:@#@$) x_aFeZ) (Apply (Apply (++@#@$) xs_aFf0) ys_aFf1)
type Map :: (~>) a_aFbL b_aFbM -> [a_aFbL] -> [b_aFbM]
type family Map @a_aFbL @b_aFbM (a_aFf2 :: (~>) a_aFbL b_aFbM) (a_aFf3 :: [a_aFbL]) :: [b_aFbM] where
  Map _ '[] = NilSym0
  Map f_aFf7 ('(:) x_aFf8 xs_aFf9) = Apply (Apply (:@#@$) (Apply f_aFf7 x_aFf8)) (Apply (Apply MapSym0 f_aFf7) xs_aFf9)
type Foldr :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)
              -> b_aFbO -> [a_aFbN] -> b_aFbO
type family Foldr @a_aFbN @b_aFbO (a_aFfc :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) (a_aFfd :: b_aFbO) (a_aFfe :: [a_aFbN]) :: b_aFbO where
  Foldr k_aFfj z_aFfk a_6989586621679168336_aFfl = Apply (Let6989586621679168348GoSym0 k_aFfj z_aFfk a_6989586621679168336_aFfl) a_6989586621679168336_aFfl
infixr 0 `Seq`
infixr 0 $!
infixr 0 $
infixr 9 .
infixr 5 ++
infixr 0 `sSeq`
infixr 0 %$!
infixr 0 %$
infixr 9 %.
infixr 5 %++
sSeq ::
  (forall (t_aFfr :: a_aFbt) (t_aFfs :: b_aFbu).
    Sing t_aFfr
    -> Sing t_aFfs -> Sing (Seq t_aFfr t_aFfs :: b_aFbu) :: Type)
sUntil ::
  (forall (t_aFfw :: (~>) a_aFbv Bool)
          (t_aFfx :: (~>) a_aFbv a_aFbv)
          (t_aFfy :: a_aFbv).
    Sing t_aFfw
    -> Sing t_aFfx
      -> Sing t_aFfy
          -> Sing (Until t_aFfw t_aFfx t_aFfy :: a_aFbv) :: Type)
(%$!) ::
  (forall (t_aFfG :: (~>) a_aFbw b_aFbx) (t_aFfH :: a_aFbw).
    Sing t_aFfG
    -> Sing t_aFfH -> Sing (($!) t_aFfG t_aFfH :: b_aFbx) :: Type)
(%$) ::
  (forall (t_aFfL :: (~>) a_aFby b_aFbz) (t_aFfM :: a_aFby).
    Sing t_aFfL
    -> Sing t_aFfM -> Sing (($) t_aFfL t_aFfM :: b_aFbz) :: Type)
sAsTypeOf ::
  (forall (t_aFfQ :: a_aFbA) (t_aFfR :: a_aFbA).
    Sing t_aFfQ
    -> Sing t_aFfR -> Sing (AsTypeOf t_aFfQ t_aFfR :: a_aFbA) :: Type)
sFlip ::
  (forall (t_aFfV :: (~>) a_aFbB ((~>) b_aFbC c_aFbD))
          (t_aFfW :: b_aFbC)
          (t_aFfX :: a_aFbB).
    Sing t_aFfV
    -> Sing t_aFfW
      -> Sing t_aFfX
          -> Sing (Flip t_aFfV t_aFfW t_aFfX :: c_aFbD) :: Type)
(%.) ::
  (forall (t_aFg5 :: (~>) b_aFbE c_aFbF)
          (t_aFg6 :: (~>) a_aFbG b_aFbE)
          (t_aFg7 :: a_aFbG).
    Sing t_aFg5
    -> Sing t_aFg6
      -> Sing t_aFg7
          -> Sing ((.) t_aFg5 t_aFg6 t_aFg7 :: c_aFbF) :: Type)
sConst ::
  (forall (t_aFgf :: a_aFbH) (t_aFgg :: b_aFbI).
    Sing t_aFgf
    -> Sing t_aFgg -> Sing (Const t_aFgf t_aFgg :: a_aFbH) :: Type)
sId ::
  (forall (t_aFgk :: a_aFbJ).
    Sing t_aFgk -> Sing (Id t_aFgk :: a_aFbJ) :: Type)
(%++) ::
  (forall (t_aFgm :: [a_aFbK]) (t_aFgn :: [a_aFbK]).
    Sing t_aFgm
    -> Sing t_aFgn -> Sing ((++) t_aFgm t_aFgn :: [a_aFbK]) :: Type)
sMap ::
  (forall (t_aFgr :: (~>) a_aFbL b_aFbM) (t_aFgs :: [a_aFbL]).
    Sing t_aFgr
    -> Sing t_aFgs -> Sing (Map t_aFgr t_aFgs :: [b_aFbM]) :: Type)
sFoldr ::
  (forall (t_aFgw :: (~>) a_aFbN ((~>) b_aFbO b_aFbO))
          (t_aFgx :: b_aFbO)
          (t_aFgy :: [a_aFbN]).
    Sing t_aFgw
    -> Sing t_aFgx
      -> Sing t_aFgy
          -> Sing (Foldr t_aFgw t_aFgx t_aFgy :: b_aFbO) :: Type)
sSeq _ (sX :: Sing x_aFdu) = sX
sUntil
  (sP :: Sing p_aFdE)
  (sF :: Sing f_aFdF)
  (sA_6989586621679168233 :: Sing a_6989586621679168233_aFdG)
  = applySing
      (let
          sGo ::
            forall arg_aFgG. Sing arg_aFgG
                            -> Sing (Let6989586621679168245Go p_aFdE f_aFdF a_6989586621679168233_aFdG arg_aFgG)
          sGo (sX :: Sing x_aFdK)
            = applySing
                (singFun1
                  @(LamCases_6989586621679168249Sym0 x_aFdK p_aFdE f_aFdF a_6989586621679168233_aFdG)
                  (\cases
                      STrue -> sX
                      SFalse
                        -> applySing
                            (singFun1
                                @(Let6989586621679168245GoSym0 p_aFdE f_aFdF a_6989586621679168233_aFdG)
                                sGo)
                            (applySing sF sX)))
                (applySing sP sX)
        in
          singFun1
            @(Let6989586621679168245GoSym0 p_aFdE f_aFdF a_6989586621679168233_aFdG)
            sGo)
      sA_6989586621679168233
(%$!) (sF :: Sing f_aFdV) (sX :: Sing x_aFdW)
  = let
      sVx :: Sing @_ (Let6989586621679168261Vx f_aFdV x_aFdW)
      sVx = sX
    in applySing sF sVx
(%$) (sF :: Sing f_aFe4) (sX :: Sing x_aFe5) = applySing sF sX
sAsTypeOf
  (sA_6989586621679168270 :: Sing a_6989586621679168270_aFef)
  (sA_6989586621679168272 :: Sing a_6989586621679168272_aFeg)
  = applySing
      (applySing (singFun2 @ConstSym0 sConst) sA_6989586621679168270)
      sA_6989586621679168272
sFlip (sF :: Sing f_aFeo) (sX :: Sing x_aFep) (sY :: Sing y_aFeq)
  = applySing (applySing sF sY) sX
(%.)
  (sF :: Sing f_aFeA)
  (sG :: Sing g_aFeB)
  (sA_6989586621679168291 :: Sing a_6989586621679168291_aFeC)
  = applySing
      (singFun1
          @(LamCases_6989586621679168303Sym0 f_aFeA g_aFeB a_6989586621679168291_aFeC)
          (\cases (sX :: Sing x_aFeF) -> applySing sF (applySing sG sX)))
      sA_6989586621679168291
sConst (sX :: Sing x_aFeO) _ = sX
sId (sX :: Sing x_aFeS) = sX
(%++) SNil (sYs :: Sing ys_aFeY) = sYs
(%++)
  (SCons (sX :: Sing x_aFeZ) (sXs :: Sing xs_aFf0))
  (sYs :: Sing ys_aFf1)
  = applySing
      (applySing (singFun2 @(:@#@$) SCons) sX)
      (applySing (applySing (singFun2 @(++@#@$) (%++)) sXs) sYs)
sMap _ SNil = SNil
sMap
  (sF :: Sing f_aFf7)
  (SCons (sX :: Sing x_aFf8) (sXs :: Sing xs_aFf9))
  = applySing
      (applySing (singFun2 @(:@#@$) SCons) (applySing sF sX))
      (applySing (applySing (singFun2 @MapSym0 sMap) sF) sXs)
sFoldr
  (sK :: Sing k_aFfj)
  (sZ :: Sing z_aFfk)
  (sA_6989586621679168336 :: Sing a_6989586621679168336_aFfl)
  = applySing
      (let
          sGo ::
            forall arg_aFgI. Sing arg_aFgI
                            -> Sing (Let6989586621679168348Go k_aFfj z_aFfk a_6989586621679168336_aFfl arg_aFgI)
          sGo SNil = sZ
          sGo (SCons (sY :: Sing y_aFfp) (sYs :: Sing ys_aFfq))
            = applySing
                (applySing sK sY)
                (applySing
                  (singFun1
                      @(Let6989586621679168348GoSym0 k_aFfj z_aFfk a_6989586621679168336_aFfl)
                      sGo)
                  sYs)
        in
          singFun1
            @(Let6989586621679168348GoSym0 k_aFfj z_aFfk a_6989586621679168336_aFfl)
            sGo)
      sA_6989586621679168336
instance SingI (SeqSym0 :: (~>) a_aFbt ((~>) b_aFbu b_aFbu)) where
  sing = singFun2 @SeqSym0 sSeq
instance SingI d_aFft =>
          SingI (SeqSym1 (d_aFft :: a_aFbt) :: (~>) b_aFbu b_aFbu) where
  sing = singFun1 @(SeqSym1 (d_aFft :: a_aFbt)) (sSeq (sing @d_aFft))
instance SingI1 (SeqSym1 :: a_aFbt -> (~>) b_aFbu b_aFbu) where
  liftSing (s_aFfv :: Sing (d_aFft :: a_aFbt))
    = singFun1 @(SeqSym1 (d_aFft :: a_aFbt)) (sSeq s_aFfv)
instance SingI (UntilSym0 :: (~>) ((~>) a_aFbv Bool) ((~>) ((~>) a_aFbv a_aFbv) ((~>) a_aFbv a_aFbv))) where
  sing = singFun3 @UntilSym0 sUntil
instance SingI d_aFfz =>
          SingI (UntilSym1 (d_aFfz :: (~>) a_aFbv Bool) :: (~>) ((~>) a_aFbv a_aFbv) ((~>) a_aFbv a_aFbv)) where
  sing
    = singFun2
        @(UntilSym1 (d_aFfz :: (~>) a_aFbv Bool)) (sUntil (sing @d_aFfz))
instance SingI1 (UntilSym1 :: (~>) a_aFbv Bool
                              -> (~>) ((~>) a_aFbv a_aFbv) ((~>) a_aFbv a_aFbv)) where
  liftSing (s_aFfF :: Sing (d_aFfz :: (~>) a_aFbv Bool))
    = singFun2
        @(UntilSym1 (d_aFfz :: (~>) a_aFbv Bool)) (sUntil s_aFfF)
instance (SingI d_aFfz, SingI d_aFfA) =>
          SingI (UntilSym2 (d_aFfz :: (~>) a_aFbv Bool) (d_aFfA :: (~>) a_aFbv a_aFbv) :: (~>) a_aFbv a_aFbv) where
  sing
    = singFun1
        @(UntilSym2 (d_aFfz :: (~>) a_aFbv Bool) (d_aFfA :: (~>) a_aFbv a_aFbv))
        (sUntil (sing @d_aFfz) (sing @d_aFfA))
instance SingI d_aFfz =>
          SingI1 (UntilSym2 (d_aFfz :: (~>) a_aFbv Bool) :: (~>) a_aFbv a_aFbv
                                                            -> (~>) a_aFbv a_aFbv) where
  liftSing (s_aFfC :: Sing (d_aFfA :: (~>) a_aFbv a_aFbv))
    = singFun1
        @(UntilSym2 (d_aFfz :: (~>) a_aFbv Bool) (d_aFfA :: (~>) a_aFbv a_aFbv))
        (sUntil (sing @d_aFfz) s_aFfC)
instance SingI2 (UntilSym2 :: (~>) a_aFbv Bool
                              -> (~>) a_aFbv a_aFbv -> (~>) a_aFbv a_aFbv) where
  liftSing2
    (s_aFfD :: Sing (d_aFfz :: (~>) a_aFbv Bool))
    (s_aFfE :: Sing (d_aFfA :: (~>) a_aFbv a_aFbv))
    = singFun1
        @(UntilSym2 (d_aFfz :: (~>) a_aFbv Bool) (d_aFfA :: (~>) a_aFbv a_aFbv))
        (sUntil s_aFfD s_aFfE)
instance SingI (($!@#@$) :: (~>) ((~>) a_aFbw b_aFbx) ((~>) a_aFbw b_aFbx)) where
  sing = singFun2 @($!@#@$) (%$!)
instance SingI d_aFfI =>
          SingI (($!@#@$$) (d_aFfI :: (~>) a_aFbw b_aFbx) :: (~>) a_aFbw b_aFbx) where
  sing
    = singFun1
        @(($!@#@$$) (d_aFfI :: (~>) a_aFbw b_aFbx)) ((%$!) (sing @d_aFfI))
instance SingI1 (($!@#@$$) :: (~>) a_aFbw b_aFbx
                              -> (~>) a_aFbw b_aFbx) where
  liftSing (s_aFfK :: Sing (d_aFfI :: (~>) a_aFbw b_aFbx))
    = singFun1
        @(($!@#@$$) (d_aFfI :: (~>) a_aFbw b_aFbx)) ((%$!) s_aFfK)
instance SingI (($@#@$) :: (~>) ((~>) a_aFby b_aFbz) ((~>) a_aFby b_aFbz)) where
  sing = singFun2 @($@#@$) (%$)
instance SingI d_aFfN =>
          SingI (($@#@$$) (d_aFfN :: (~>) a_aFby b_aFbz) :: (~>) a_aFby b_aFbz) where
  sing
    = singFun1
        @(($@#@$$) (d_aFfN :: (~>) a_aFby b_aFbz)) ((%$) (sing @d_aFfN))
instance SingI1 (($@#@$$) :: (~>) a_aFby b_aFbz
                              -> (~>) a_aFby b_aFbz) where
  liftSing (s_aFfP :: Sing (d_aFfN :: (~>) a_aFby b_aFbz))
    = singFun1 @(($@#@$$) (d_aFfN :: (~>) a_aFby b_aFbz)) ((%$) s_aFfP)
instance SingI (AsTypeOfSym0 :: (~>) a_aFbA ((~>) a_aFbA a_aFbA)) where
  sing = singFun2 @AsTypeOfSym0 sAsTypeOf
instance SingI d_aFfS =>
          SingI (AsTypeOfSym1 (d_aFfS :: a_aFbA) :: (~>) a_aFbA a_aFbA) where
  sing
    = singFun1
        @(AsTypeOfSym1 (d_aFfS :: a_aFbA)) (sAsTypeOf (sing @d_aFfS))
instance SingI1 (AsTypeOfSym1 :: a_aFbA
                                  -> (~>) a_aFbA a_aFbA) where
  liftSing (s_aFfU :: Sing (d_aFfS :: a_aFbA))
    = singFun1 @(AsTypeOfSym1 (d_aFfS :: a_aFbA)) (sAsTypeOf s_aFfU)
instance SingI (FlipSym0 :: (~>) ((~>) a_aFbB ((~>) b_aFbC c_aFbD)) ((~>) b_aFbC ((~>) a_aFbB c_aFbD))) where
  sing = singFun3 @FlipSym0 sFlip
instance SingI d_aFfY =>
          SingI (FlipSym1 (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) :: (~>) b_aFbC ((~>) a_aFbB c_aFbD)) where
  sing
    = singFun2
        @(FlipSym1 (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)))
        (sFlip (sing @d_aFfY))
instance SingI1 (FlipSym1 :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)
                              -> (~>) b_aFbC ((~>) a_aFbB c_aFbD)) where
  liftSing
    (s_aFg4 :: Sing (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)))
    = singFun2
        @(FlipSym1 (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)))
        (sFlip s_aFg4)
instance (SingI d_aFfY, SingI d_aFfZ) =>
          SingI (FlipSym2 (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) (d_aFfZ :: b_aFbC) :: (~>) a_aFbB c_aFbD) where
  sing
    = singFun1
        @(FlipSym2 (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) (d_aFfZ :: b_aFbC))
        (sFlip (sing @d_aFfY) (sing @d_aFfZ))
instance SingI d_aFfY =>
          SingI1 (FlipSym2 (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) :: b_aFbC
                                                                          -> (~>) a_aFbB c_aFbD) where
  liftSing (s_aFg1 :: Sing (d_aFfZ :: b_aFbC))
    = singFun1
        @(FlipSym2 (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) (d_aFfZ :: b_aFbC))
        (sFlip (sing @d_aFfY) s_aFg1)
instance SingI2 (FlipSym2 :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)
                              -> b_aFbC -> (~>) a_aFbB c_aFbD) where
  liftSing2
    (s_aFg2 :: Sing (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)))
    (s_aFg3 :: Sing (d_aFfZ :: b_aFbC))
    = singFun1
        @(FlipSym2 (d_aFfY :: (~>) a_aFbB ((~>) b_aFbC c_aFbD)) (d_aFfZ :: b_aFbC))
        (sFlip s_aFg2 s_aFg3)
instance SingI ((.@#@$) :: (~>) ((~>) b_aFbE c_aFbF) ((~>) ((~>) a_aFbG b_aFbE) ((~>) a_aFbG c_aFbF))) where
  sing = singFun3 @(.@#@$) (%.)
instance SingI d_aFg8 =>
          SingI ((.@#@$$) (d_aFg8 :: (~>) b_aFbE c_aFbF) :: (~>) ((~>) a_aFbG b_aFbE) ((~>) a_aFbG c_aFbF)) where
  sing
    = singFun2
        @((.@#@$$) (d_aFg8 :: (~>) b_aFbE c_aFbF)) ((%.) (sing @d_aFg8))
instance SingI1 ((.@#@$$) :: (~>) b_aFbE c_aFbF
                              -> (~>) ((~>) a_aFbG b_aFbE) ((~>) a_aFbG c_aFbF)) where
  liftSing (s_aFge :: Sing (d_aFg8 :: (~>) b_aFbE c_aFbF))
    = singFun2 @((.@#@$$) (d_aFg8 :: (~>) b_aFbE c_aFbF)) ((%.) s_aFge)
instance (SingI d_aFg8, SingI d_aFg9) =>
          SingI ((.@#@$$$) (d_aFg8 :: (~>) b_aFbE c_aFbF) (d_aFg9 :: (~>) a_aFbG b_aFbE) :: (~>) a_aFbG c_aFbF) where
  sing
    = singFun1
        @((.@#@$$$) (d_aFg8 :: (~>) b_aFbE c_aFbF) (d_aFg9 :: (~>) a_aFbG b_aFbE))
        ((%.) (sing @d_aFg8) (sing @d_aFg9))
instance SingI d_aFg8 =>
          SingI1 ((.@#@$$$) (d_aFg8 :: (~>) b_aFbE c_aFbF) :: (~>) a_aFbG b_aFbE
                                                              -> (~>) a_aFbG c_aFbF) where
  liftSing (s_aFgb :: Sing (d_aFg9 :: (~>) a_aFbG b_aFbE))
    = singFun1
        @((.@#@$$$) (d_aFg8 :: (~>) b_aFbE c_aFbF) (d_aFg9 :: (~>) a_aFbG b_aFbE))
        ((%.) (sing @d_aFg8) s_aFgb)
instance SingI2 ((.@#@$$$) :: (~>) b_aFbE c_aFbF
                              -> (~>) a_aFbG b_aFbE -> (~>) a_aFbG c_aFbF) where
  liftSing2
    (s_aFgc :: Sing (d_aFg8 :: (~>) b_aFbE c_aFbF))
    (s_aFgd :: Sing (d_aFg9 :: (~>) a_aFbG b_aFbE))
    = singFun1
        @((.@#@$$$) (d_aFg8 :: (~>) b_aFbE c_aFbF) (d_aFg9 :: (~>) a_aFbG b_aFbE))
        ((%.) s_aFgc s_aFgd)
instance SingI (ConstSym0 :: (~>) a_aFbH ((~>) b_aFbI a_aFbH)) where
  sing = singFun2 @ConstSym0 sConst
instance SingI d_aFgh =>
          SingI (ConstSym1 (d_aFgh :: a_aFbH) :: (~>) b_aFbI a_aFbH) where
  sing
    = singFun1 @(ConstSym1 (d_aFgh :: a_aFbH)) (sConst (sing @d_aFgh))
instance SingI1 (ConstSym1 :: a_aFbH -> (~>) b_aFbI a_aFbH) where
  liftSing (s_aFgj :: Sing (d_aFgh :: a_aFbH))
    = singFun1 @(ConstSym1 (d_aFgh :: a_aFbH)) (sConst s_aFgj)
instance SingI (IdSym0 :: (~>) a_aFbJ a_aFbJ) where
  sing = singFun1 @IdSym0 sId
instance SingI ((++@#@$) :: (~>) [a_aFbK] ((~>) [a_aFbK] [a_aFbK])) where
  sing = singFun2 @(++@#@$) (%++)
instance SingI d_aFgo =>
          SingI ((++@#@$$) (d_aFgo :: [a_aFbK]) :: (~>) [a_aFbK] [a_aFbK]) where
  sing
    = singFun1 @((++@#@$$) (d_aFgo :: [a_aFbK])) ((%++) (sing @d_aFgo))
instance SingI1 ((++@#@$$) :: [a_aFbK]
                              -> (~>) [a_aFbK] [a_aFbK]) where
  liftSing (s_aFgq :: Sing (d_aFgo :: [a_aFbK]))
    = singFun1 @((++@#@$$) (d_aFgo :: [a_aFbK])) ((%++) s_aFgq)
instance SingI (MapSym0 :: (~>) ((~>) a_aFbL b_aFbM) ((~>) [a_aFbL] [b_aFbM])) where
  sing = singFun2 @MapSym0 sMap
instance SingI d_aFgt =>
          SingI (MapSym1 (d_aFgt :: (~>) a_aFbL b_aFbM) :: (~>) [a_aFbL] [b_aFbM]) where
  sing
    = singFun1
        @(MapSym1 (d_aFgt :: (~>) a_aFbL b_aFbM)) (sMap (sing @d_aFgt))
instance SingI1 (MapSym1 :: (~>) a_aFbL b_aFbM
                            -> (~>) [a_aFbL] [b_aFbM]) where
  liftSing (s_aFgv :: Sing (d_aFgt :: (~>) a_aFbL b_aFbM))
    = singFun1 @(MapSym1 (d_aFgt :: (~>) a_aFbL b_aFbM)) (sMap s_aFgv)
instance SingI (FoldrSym0 :: (~>) ((~>) a_aFbN ((~>) b_aFbO b_aFbO)) ((~>) b_aFbO ((~>) [a_aFbN] b_aFbO))) where
  sing = singFun3 @FoldrSym0 sFoldr
instance SingI d_aFgz =>
          SingI (FoldrSym1 (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) :: (~>) b_aFbO ((~>) [a_aFbN] b_aFbO)) where
  sing
    = singFun2
        @(FoldrSym1 (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)))
        (sFoldr (sing @d_aFgz))
instance SingI1 (FoldrSym1 :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)
                              -> (~>) b_aFbO ((~>) [a_aFbN] b_aFbO)) where
  liftSing
    (s_aFgF :: Sing (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)))
    = singFun2
        @(FoldrSym1 (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)))
        (sFoldr s_aFgF)
instance (SingI d_aFgz, SingI d_aFgA) =>
          SingI (FoldrSym2 (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) (d_aFgA :: b_aFbO) :: (~>) [a_aFbN] b_aFbO) where
  sing
    = singFun1
        @(FoldrSym2 (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) (d_aFgA :: b_aFbO))
        (sFoldr (sing @d_aFgz) (sing @d_aFgA))
instance SingI d_aFgz =>
          SingI1 (FoldrSym2 (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) :: b_aFbO
                                                                            -> (~>) [a_aFbN] b_aFbO) where
  liftSing (s_aFgC :: Sing (d_aFgA :: b_aFbO))
    = singFun1
        @(FoldrSym2 (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) (d_aFgA :: b_aFbO))
        (sFoldr (sing @d_aFgz) s_aFgC)
instance SingI2 (FoldrSym2 :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)
                              -> b_aFbO -> (~>) [a_aFbN] b_aFbO) where
  liftSing2
    (s_aFgD :: Sing (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)))
    (s_aFgE :: Sing (d_aFgA :: b_aFbO))
    = singFun1
        @(FoldrSym2 (d_aFgz :: (~>) a_aFbN ((~>) b_aFbO b_aFbO)) (d_aFgA :: b_aFbO))
        (sFoldr s_aFgD s_aFgE)
