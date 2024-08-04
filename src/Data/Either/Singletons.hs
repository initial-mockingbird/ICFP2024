{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
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
-- Module      :  Data.Either.Singletons
-- Copyright   :  (C) 2013-2014 Richard Eisenberg, Jan Stolarek
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines functions and datatypes relating to the singleton for 'Either',
-- including singled versions of all the definitions in @Data.Either@.
--
-- Because many of these definitions are produced by Template Haskell,
-- it is not possible to create proper Haddock documentation. Please look
-- up the corresponding operation in @Data.Either@. Also, please excuse
-- the apparent repeated variable names. This is due to an interaction
-- between Template Haskell and Haddock.
--
----------------------------------------------------------------------------

module Data.Either.Singletons (
  -- * The 'Either' singleton
  Sing, SEither(..),

  -- * Singletons from @Data.Either@
  either_, Either_, sEither_,
  -- | The preceding two definitions are derived from the function 'either' in
  -- @Data.Either@. The extra underscore is to avoid name clashes with the type
  -- 'Either'.

  Lefts, sLefts, Rights, sRights,
  PartitionEithers, sPartitionEithers, IsLeft, sIsLeft, IsRight, sIsRight,

  -- * Defunctionalization symbols
  LeftSym0, LeftSym1, RightSym0, RightSym1,

  Either_Sym0, Either_Sym1, Either_Sym2, Either_Sym3,
  LeftsSym0, LeftsSym1, RightsSym0, RightsSym1,
  IsLeftSym0, IsLeftSym1, IsRightSym0, IsRightSym1
  ) where

import Data.Singletons.Base.Instances
import Data.Singletons.TH
import GHC.Base.Singletons
import Data.Kind (Type)

-- NB: The haddock comments are disabled because TH can't deal with them.

either_ ::
      (a_a15Im -> c_a15In)
      -> (b_a15Io -> c_a15In) -> Either a_a15Im b_a15Io -> c_a15In
either_ f_a15Iq _ (Left x_a15Ir) = f_a15Iq x_a15Ir
either_ _ g_a15Is (Right y_a15It) = g_a15Is y_a15It
type Either_Sym0 :: (~>) ((~>) a_a15Im c_a15In) ((~>) ((~>) b_a15Io c_a15In) ((~>) (Either a_a15Im b_a15Io) c_a15In))
data Either_Sym0 :: (~>) ((~>) a_a15Im c_a15In) ((~>) ((~>) b_a15Io c_a15In) ((~>) (Either a_a15Im b_a15Io) c_a15In))
  where
    Either_Sym0KindInference :: SameKind (Apply Either_Sym0 arg_a15IZ) (Either_Sym1 arg_a15IZ) =>
                                Either_Sym0 a6989586621679270130
type instance Apply @((~>) a_a15Im c_a15In) @((~>) ((~>) b_a15Io c_a15In) ((~>) (Either a_a15Im b_a15Io) c_a15In)) Either_Sym0 a6989586621679270130 = Either_Sym1 a6989586621679270130
instance SuppressUnusedWarnings Either_Sym0 where
  suppressUnusedWarnings = snd ((,) Either_Sym0KindInference ())
type Either_Sym1 :: (~>) a_a15Im c_a15In
                    -> (~>) ((~>) b_a15Io c_a15In) ((~>) (Either a_a15Im b_a15Io) c_a15In)
data Either_Sym1 (a6989586621679270130 :: (~>) a_a15Im c_a15In) :: (~>) ((~>) b_a15Io c_a15In) ((~>) (Either a_a15Im b_a15Io) c_a15In)
  where
    Either_Sym1KindInference :: SameKind (Apply (Either_Sym1 a6989586621679270130) arg_a15IZ) (Either_Sym2 a6989586621679270130 arg_a15IZ) =>
                                Either_Sym1 a6989586621679270130 a6989586621679270131
type instance Apply @((~>) b_a15Io c_a15In) @((~>) (Either a_a15Im b_a15Io) c_a15In) (Either_Sym1 a6989586621679270130) a6989586621679270131 = Either_Sym2 a6989586621679270130 a6989586621679270131
instance SuppressUnusedWarnings (Either_Sym1 a6989586621679270130) where
  suppressUnusedWarnings = snd ((,) Either_Sym1KindInference ())
type Either_Sym2 :: (~>) a_a15Im c_a15In
                    -> (~>) b_a15Io c_a15In -> (~>) (Either a_a15Im b_a15Io) c_a15In
data Either_Sym2 (a6989586621679270130 :: (~>) a_a15Im c_a15In) (a6989586621679270131 :: (~>) b_a15Io c_a15In) :: (~>) (Either a_a15Im b_a15Io) c_a15In
  where
    Either_Sym2KindInference :: SameKind (Apply (Either_Sym2 a6989586621679270130 a6989586621679270131) arg_a15IZ) (Either_Sym3 a6989586621679270130 a6989586621679270131 arg_a15IZ) =>
                                Either_Sym2 a6989586621679270130 a6989586621679270131 a6989586621679270132
type instance Apply @(Either a_a15Im b_a15Io) @c_a15In (Either_Sym2 a6989586621679270130 a6989586621679270131) a6989586621679270132 = Either_ a6989586621679270130 a6989586621679270131 a6989586621679270132
instance SuppressUnusedWarnings (Either_Sym2 a6989586621679270130 a6989586621679270131) where
  suppressUnusedWarnings = snd ((,) Either_Sym2KindInference ())
type Either_Sym3 :: (~>) a_a15Im c_a15In
                    -> (~>) b_a15Io c_a15In -> Either a_a15Im b_a15Io -> c_a15In
type family Either_Sym3 @a_a15Im @c_a15In @b_a15Io (a6989586621679270130 :: (~>) a_a15Im c_a15In) (a6989586621679270131 :: (~>) b_a15Io c_a15In) (a6989586621679270132 :: Either a_a15Im b_a15Io) :: c_a15In where
  Either_Sym3 a6989586621679270130 a6989586621679270131 a6989586621679270132 = Either_ a6989586621679270130 a6989586621679270131 a6989586621679270132
type Either_ :: (~>) a_a15Im c_a15In
                -> (~>) b_a15Io c_a15In -> Either a_a15Im b_a15Io -> c_a15In
type family Either_ @a_a15Im @c_a15In @b_a15Io (a_a15IW :: (~>) a_a15Im c_a15In) (a_a15IX :: (~>) b_a15Io c_a15In) (a_a15IY :: Either a_a15Im b_a15Io) :: c_a15In where
  Either_ f_a15J3 _ ('Left x_a15J4) = Apply f_a15J3 x_a15J4
  Either_ _ g_a15J5 ('Right y_a15J6) = Apply g_a15J5 y_a15J6
sEither_ ::
  (forall (t_a15J7 :: (~>) a_a15Im c_a15In)
          (t_a15J8 :: (~>) b_a15Io c_a15In)
          (t_a15J9 :: Either a_a15Im b_a15Io).
    Sing t_a15J7
    -> Sing t_a15J8
      -> Sing t_a15J9
          -> Sing (Either_ t_a15J7 t_a15J8 t_a15J9 :: c_a15In) :: Type)
sEither_ (sF :: Sing f_a15J3) _ (SLeft (sX :: Sing x_a15J4))
  = applySing sF sX
sEither_ _ (sG :: Sing g_a15J5) (SRight (sY :: Sing y_a15J6))
  = applySing sG sY
instance SingI (Either_Sym0 :: (~>) ((~>) a_a15Im c_a15In) ((~>) ((~>) b_a15Io c_a15In) ((~>) (Either a_a15Im b_a15Io) c_a15In))) where
  sing = singFun3 @Either_Sym0 sEither_
instance SingI d_a15Ja =>
          SingI (Either_Sym1 (d_a15Ja :: (~>) a_a15Im c_a15In) :: (~>) ((~>) b_a15Io c_a15In) ((~>) (Either a_a15Im b_a15Io) c_a15In)) where
  sing
    = singFun2
        @(Either_Sym1 (d_a15Ja :: (~>) a_a15Im c_a15In))
        (sEither_ (sing @d_a15Ja))
instance SingI1 (Either_Sym1 :: (~>) a_a15Im c_a15In
                                -> (~>) ((~>) b_a15Io c_a15In) ((~>) (Either a_a15Im b_a15Io) c_a15In)) where
  liftSing (s_a15Jg :: Sing (d_a15Ja :: (~>) a_a15Im c_a15In))
    = singFun2
        @(Either_Sym1 (d_a15Ja :: (~>) a_a15Im c_a15In)) (sEither_ s_a15Jg)
instance (SingI d_a15Ja, SingI d_a15Jb) =>
          SingI (Either_Sym2 (d_a15Ja :: (~>) a_a15Im c_a15In) (d_a15Jb :: (~>) b_a15Io c_a15In) :: (~>) (Either a_a15Im b_a15Io) c_a15In) where
  sing
    = singFun1
        @(Either_Sym2 (d_a15Ja :: (~>) a_a15Im c_a15In) (d_a15Jb :: (~>) b_a15Io c_a15In))
        (sEither_ (sing @d_a15Ja) (sing @d_a15Jb))
instance SingI d_a15Ja =>
          SingI1 (Either_Sym2 (d_a15Ja :: (~>) a_a15Im c_a15In) :: (~>) b_a15Io c_a15In
                                                                  -> (~>) (Either a_a15Im b_a15Io) c_a15In) where
  liftSing (s_a15Jd :: Sing (d_a15Jb :: (~>) b_a15Io c_a15In))
    = singFun1
        @(Either_Sym2 (d_a15Ja :: (~>) a_a15Im c_a15In) (d_a15Jb :: (~>) b_a15Io c_a15In))
        (sEither_ (sing @d_a15Ja) s_a15Jd)
instance SingI2 (Either_Sym2 :: (~>) a_a15Im c_a15In
                                -> (~>) b_a15Io c_a15In
                                    -> (~>) (Either a_a15Im b_a15Io) c_a15In) where
  liftSing2
    (s_a15Je :: Sing (d_a15Ja :: (~>) a_a15Im c_a15In))
    (s_a15Jf :: Sing (d_a15Jb :: (~>) b_a15Io c_a15In))
    = singFun1
        @(Either_Sym2 (d_a15Ja :: (~>) a_a15Im c_a15In) (d_a15Jb :: (~>) b_a15Io c_a15In))
        (sEither_ s_a15Je s_a15Jf)

data Let6989586621679272254RightSym0 (a_69895866216792722486989586621679272253 :: [Either a6989586621679272043 b6989586621679272044]) a6989586621679272255
      where
        Let6989586621679272254RightSym0KindInference :: SameKind (Apply (Let6989586621679272254RightSym0 a_69895866216792722486989586621679272253) arg_a16hj) (Let6989586621679272254RightSym1 a_69895866216792722486989586621679272253 arg_a16hj) =>
                                                        Let6989586621679272254RightSym0 a_69895866216792722486989586621679272253 a6989586621679272255
type instance Apply @_ @_ (Let6989586621679272254RightSym0 a_69895866216792722486989586621679272253) a6989586621679272255 = Let6989586621679272254RightSym1 a_69895866216792722486989586621679272253 a6989586621679272255
instance SuppressUnusedWarnings (Let6989586621679272254RightSym0 a_69895866216792722486989586621679272253) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679272254RightSym0KindInference ())
data Let6989586621679272254RightSym1 (a_69895866216792722486989586621679272253 :: [Either a6989586621679272043 b6989586621679272044]) a6989586621679272255 a6989586621679272256
  where
    Let6989586621679272254RightSym1KindInference :: SameKind (Apply (Let6989586621679272254RightSym1 a_69895866216792722486989586621679272253 a6989586621679272255) arg_a16hj) (Let6989586621679272254RightSym2 a_69895866216792722486989586621679272253 a6989586621679272255 arg_a16hj) =>
                                                    Let6989586621679272254RightSym1 a_69895866216792722486989586621679272253 a6989586621679272255 a6989586621679272256
type instance Apply @_ @_ (Let6989586621679272254RightSym1 a_69895866216792722486989586621679272253 a6989586621679272255) a6989586621679272256 = Let6989586621679272254Right a_69895866216792722486989586621679272253 a6989586621679272255 a6989586621679272256
instance SuppressUnusedWarnings (Let6989586621679272254RightSym1 a_69895866216792722486989586621679272253 a6989586621679272255) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679272254RightSym1KindInference ())
type family Let6989586621679272254RightSym2 (a_69895866216792722486989586621679272253 :: [Either a6989586621679272043 b6989586621679272044]) a6989586621679272255 a6989586621679272256 where
  Let6989586621679272254RightSym2 a_69895866216792722486989586621679272253 a6989586621679272255 a6989586621679272256 = Let6989586621679272254Right a_69895866216792722486989586621679272253 a6989586621679272255 a6989586621679272256
data Let6989586621679272254LeftSym0 (a_69895866216792722486989586621679272253 :: [Either a6989586621679272043 b6989586621679272044]) a6989586621679272261
  where
    Let6989586621679272254LeftSym0KindInference :: SameKind (Apply (Let6989586621679272254LeftSym0 a_69895866216792722486989586621679272253) arg_a16hp) (Let6989586621679272254LeftSym1 a_69895866216792722486989586621679272253 arg_a16hp) =>
                                                    Let6989586621679272254LeftSym0 a_69895866216792722486989586621679272253 a6989586621679272261
type instance Apply @_ @_ (Let6989586621679272254LeftSym0 a_69895866216792722486989586621679272253) a6989586621679272261 = Let6989586621679272254LeftSym1 a_69895866216792722486989586621679272253 a6989586621679272261
instance SuppressUnusedWarnings (Let6989586621679272254LeftSym0 a_69895866216792722486989586621679272253) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679272254LeftSym0KindInference ())
data Let6989586621679272254LeftSym1 (a_69895866216792722486989586621679272253 :: [Either a6989586621679272043 b6989586621679272044]) a6989586621679272261 a6989586621679272262
  where
    Let6989586621679272254LeftSym1KindInference :: SameKind (Apply (Let6989586621679272254LeftSym1 a_69895866216792722486989586621679272253 a6989586621679272261) arg_a16hp) (Let6989586621679272254LeftSym2 a_69895866216792722486989586621679272253 a6989586621679272261 arg_a16hp) =>
                                                    Let6989586621679272254LeftSym1 a_69895866216792722486989586621679272253 a6989586621679272261 a6989586621679272262
type instance Apply @_ @_ (Let6989586621679272254LeftSym1 a_69895866216792722486989586621679272253 a6989586621679272261) a6989586621679272262 = Let6989586621679272254Left a_69895866216792722486989586621679272253 a6989586621679272261 a6989586621679272262
instance SuppressUnusedWarnings (Let6989586621679272254LeftSym1 a_69895866216792722486989586621679272253 a6989586621679272261) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679272254LeftSym1KindInference ())
type family Let6989586621679272254LeftSym2 (a_69895866216792722486989586621679272253 :: [Either a6989586621679272043 b6989586621679272044]) a6989586621679272261 a6989586621679272262 where
  Let6989586621679272254LeftSym2 a_69895866216792722486989586621679272253 a6989586621679272261 a6989586621679272262 = Let6989586621679272254Left a_69895866216792722486989586621679272253 a6989586621679272261 a6989586621679272262
type family Let6989586621679272254Right (a_69895866216792722486989586621679272253 :: [Either a6989586621679272043 b6989586621679272044]) a_a16hh a_a16hi where
  Let6989586621679272254Right a_6989586621679272248_a16hf a_a16hk '(l_a16hl,
                                                                    r_a16hm) = Apply (Apply Tuple2Sym0 l_a16hl) (Apply (Apply (:@#@$) a_a16hk) r_a16hm)
type family Let6989586621679272254Left (a_69895866216792722486989586621679272253 :: [Either a6989586621679272043 b6989586621679272044]) a_a16hn a_a16ho where
  Let6989586621679272254Left a_6989586621679272248_a16hf a_a16hq '(l_a16hr,
                                                                    r_a16hs) = Apply (Apply Tuple2Sym0 (Apply (Apply (:@#@$) a_a16hq) l_a16hr)) r_a16hs
type IsRightSym0 :: (~>) (Either a_a16dN b_a16dO) Bool
data IsRightSym0 :: (~>) (Either a_a16dN b_a16dO) Bool
  where
    IsRightSym0KindInference :: SameKind (Apply IsRightSym0 arg_a16h5) (IsRightSym1 arg_a16h5) =>
                                IsRightSym0 a6989586621679272244
type instance Apply @(Either a_a16dN b_a16dO) @Bool IsRightSym0 a6989586621679272244 = IsRight a6989586621679272244
instance SuppressUnusedWarnings IsRightSym0 where
  suppressUnusedWarnings = snd ((,) IsRightSym0KindInference ())
type IsRightSym1 :: Either a_a16dN b_a16dO -> Bool
type family IsRightSym1 @a_a16dN @b_a16dO (a6989586621679272244 :: Either a_a16dN b_a16dO) :: Bool where
  IsRightSym1 a6989586621679272244 = IsRight a6989586621679272244
type IsLeftSym0 :: (~>) (Either a_a16dP b_a16dQ) Bool
data IsLeftSym0 :: (~>) (Either a_a16dP b_a16dQ) Bool
  where
    IsLeftSym0KindInference :: SameKind (Apply IsLeftSym0 arg_a16h8) (IsLeftSym1 arg_a16h8) =>
                                IsLeftSym0 a6989586621679272247
type instance Apply @(Either a_a16dP b_a16dQ) @Bool IsLeftSym0 a6989586621679272247 = IsLeft a6989586621679272247
instance SuppressUnusedWarnings IsLeftSym0 where
  suppressUnusedWarnings = snd ((,) IsLeftSym0KindInference ())
type IsLeftSym1 :: Either a_a16dP b_a16dQ -> Bool
type family IsLeftSym1 @a_a16dP @b_a16dQ (a6989586621679272247 :: Either a_a16dP b_a16dQ) :: Bool where
  IsLeftSym1 a6989586621679272247 = IsLeft a6989586621679272247
type PartitionEithersSym0 :: (~>) [Either a_a16dR b_a16dS] ([a_a16dR],
                                                            [b_a16dS])
data PartitionEithersSym0 :: (~>) [Either a_a16dR b_a16dS] ([a_a16dR],
                                                            [b_a16dS])
  where
    PartitionEithersSym0KindInference :: SameKind (Apply PartitionEithersSym0 arg_a16hd) (PartitionEithersSym1 arg_a16hd) =>
                                          PartitionEithersSym0 a6989586621679272252
type instance Apply @[Either a_a16dR b_a16dS] @([a_a16dR],
                                                [b_a16dS]) PartitionEithersSym0 a6989586621679272252 = PartitionEithers a6989586621679272252
instance SuppressUnusedWarnings PartitionEithersSym0 where
  suppressUnusedWarnings
    = snd ((,) PartitionEithersSym0KindInference ())
type PartitionEithersSym1 :: [Either a_a16dR b_a16dS]
                              -> ([a_a16dR], [b_a16dS])
type family PartitionEithersSym1 @a_a16dR @b_a16dS (a6989586621679272252 :: [Either a_a16dR b_a16dS]) :: ([a_a16dR],
                                                                                                          [b_a16dS]) where
  PartitionEithersSym1 a6989586621679272252 = PartitionEithers a6989586621679272252
type RightsSym0 :: (~>) [Either a_a16dT b_a16dU] [b_a16dU]
data RightsSym0 :: (~>) [Either a_a16dT b_a16dU] [b_a16dU]
  where
    RightsSym0KindInference :: SameKind (Apply RightsSym0 arg_a16hu) (RightsSym1 arg_a16hu) =>
                                RightsSym0 a6989586621679272269
type instance Apply @[Either a_a16dT b_a16dU] @[b_a16dU] RightsSym0 a6989586621679272269 = Rights a6989586621679272269
instance SuppressUnusedWarnings RightsSym0 where
  suppressUnusedWarnings = snd ((,) RightsSym0KindInference ())
type RightsSym1 :: [Either a_a16dT b_a16dU] -> [b_a16dU]
type family RightsSym1 @a_a16dT @b_a16dU (a6989586621679272269 :: [Either a_a16dT b_a16dU]) :: [b_a16dU] where
  RightsSym1 a6989586621679272269 = Rights a6989586621679272269
type LeftsSym0 :: (~>) [Either a_a16dV b_a16dW] [a_a16dV]
data LeftsSym0 :: (~>) [Either a_a16dV b_a16dW] [a_a16dV]
  where
    LeftsSym0KindInference :: SameKind (Apply LeftsSym0 arg_a16hA) (LeftsSym1 arg_a16hA) =>
                              LeftsSym0 a6989586621679272275
type instance Apply @[Either a_a16dV b_a16dW] @[a_a16dV] LeftsSym0 a6989586621679272275 = Lefts a6989586621679272275
instance SuppressUnusedWarnings LeftsSym0 where
  suppressUnusedWarnings = snd ((,) LeftsSym0KindInference ())
type LeftsSym1 :: [Either a_a16dV b_a16dW] -> [a_a16dV]
type family LeftsSym1 @a_a16dV @b_a16dW (a6989586621679272275 :: [Either a_a16dV b_a16dW]) :: [a_a16dV] where
  LeftsSym1 a6989586621679272275 = Lefts a6989586621679272275
type IsRight :: Either a_a16dN b_a16dO -> Bool
type family IsRight @a_a16dN @b_a16dO (a_a16h4 :: Either a_a16dN b_a16dO) :: Bool where
  IsRight ('Left _) = FalseSym0
  IsRight ('Right _) = TrueSym0
type IsLeft :: Either a_a16dP b_a16dQ -> Bool
type family IsLeft @a_a16dP @b_a16dQ (a_a16h7 :: Either a_a16dP b_a16dQ) :: Bool where
  IsLeft ('Left _) = TrueSym0
  IsLeft ('Right _) = FalseSym0
type PartitionEithers :: [Either a_a16dR b_a16dS]
                          -> ([a_a16dR], [b_a16dS])
type family PartitionEithers @a_a16dR @b_a16dS (a_a16hc :: [Either a_a16dR b_a16dS]) :: ([a_a16dR],
                                                                                          [b_a16dS]) where
  PartitionEithers a_6989586621679272248_a16hf = Apply (Apply (Apply FoldrSym0 (Apply (Apply Either_Sym0 (Let6989586621679272254LeftSym0 a_6989586621679272248_a16hf)) (Let6989586621679272254RightSym0 a_6989586621679272248_a16hf))) (Apply (Apply Tuple2Sym0 NilSym0) NilSym0)) a_6989586621679272248_a16hf
type Rights :: [Either a_a16dT b_a16dU] -> [b_a16dU]
type family Rights @a_a16dT @b_a16dU (a_a16ht :: [Either a_a16dT b_a16dU]) :: [b_a16dU] where
  Rights '[] = NilSym0
  Rights ('(:) ('Left _) xs_a16hw) = Apply RightsSym0 xs_a16hw
  Rights ('(:) ('Right x_a16hx) xs_a16hy) = Apply (Apply (:@#@$) x_a16hx) (Apply RightsSym0 xs_a16hy)
type Lefts :: [Either a_a16dV b_a16dW] -> [a_a16dV]
type family Lefts @a_a16dV @b_a16dW (a_a16hz :: [Either a_a16dV b_a16dW]) :: [a_a16dV] where
  Lefts '[] = NilSym0
  Lefts ('(:) ('Left x_a16hC) xs_a16hD) = Apply (Apply (:@#@$) x_a16hC) (Apply LeftsSym0 xs_a16hD)
  Lefts ('(:) ('Right _) xs_a16hE) = Apply LeftsSym0 xs_a16hE
sIsRight ::
  (forall (t_a16hF :: Either a_a16dN b_a16dO).
    Sing t_a16hF -> Sing (IsRight t_a16hF :: Bool) :: Type)
sIsLeft ::
  (forall (t_a16hH :: Either a_a16dP b_a16dQ).
    Sing t_a16hH -> Sing (IsLeft t_a16hH :: Bool) :: Type)
sPartitionEithers ::
  (forall (t_a16hJ :: [Either a_a16dR b_a16dS]).
    Sing t_a16hJ
    -> Sing (PartitionEithers t_a16hJ :: ([a_a16dR],
                                          [b_a16dS])) :: Type)
sRights ::
  (forall (t_a16hL :: [Either a_a16dT b_a16dU]).
    Sing t_a16hL -> Sing (Rights t_a16hL :: [b_a16dU]) :: Type)
sLefts ::
  (forall (t_a16hN :: [Either a_a16dV b_a16dW]).
    Sing t_a16hN -> Sing (Lefts t_a16hN :: [a_a16dV]) :: Type)
sIsRight (SLeft _) = SFalse
sIsRight (SRight _) = STrue
sIsLeft (SLeft _) = STrue
sIsLeft (SRight _) = SFalse
sPartitionEithers
  (sA_6989586621679272248 :: Sing a_6989586621679272248_a16hf)
  = applySing
      (let
          sRight ::
            forall arg_a16hP arg_a16hQ. Sing arg_a16hP
                                        -> Sing arg_a16hQ
                                          -> Sing (Let6989586621679272254Right a_6989586621679272248_a16hf arg_a16hP arg_a16hQ)
          sLeft ::
            forall arg_a16hU arg_a16hV. Sing arg_a16hU
                                        -> Sing arg_a16hV
                                          -> Sing (Let6989586621679272254Left a_6989586621679272248_a16hf arg_a16hU arg_a16hV)
          sRight
            (sA :: Sing a_a16hk)
            (STuple2 (sL :: Sing l_a16hl) (sR :: Sing r_a16hm))
            = applySing
                (applySing (singFun2 @Tuple2Sym0 STuple2) sL)
                (applySing (applySing (singFun2 @(:@#@$) SCons) sA) sR)
          sLeft
            (sA :: Sing a_a16hq)
            (STuple2 (sL :: Sing l_a16hr) (sR :: Sing r_a16hs))
            = applySing
                (applySing
                  (singFun2 @Tuple2Sym0 STuple2)
                  (applySing (applySing (singFun2 @(:@#@$) SCons) sA) sL))
                sR
        in
          applySing
            (applySing
              (singFun3 @FoldrSym0 sFoldr)
              (applySing
                  (applySing
                    (singFun3 @Either_Sym0 sEither_)
                    (singFun2
                        @(Let6989586621679272254LeftSym0 a_6989586621679272248_a16hf)
                        sLeft))
                  (singFun2
                    @(Let6989586621679272254RightSym0 a_6989586621679272248_a16hf)
                    sRight)))
            (applySing (applySing (singFun2 @Tuple2Sym0 STuple2) SNil) SNil))
      sA_6989586621679272248
sRights SNil = SNil
sRights (SCons (SLeft _) (sXs :: Sing xs_a16hw))
  = applySing (singFun1 @RightsSym0 sRights) sXs
sRights
  (SCons (SRight (sX :: Sing x_a16hx)) (sXs :: Sing xs_a16hy))
  = applySing
      (applySing (singFun2 @(:@#@$) SCons) sX)
      (applySing (singFun1 @RightsSym0 sRights) sXs)
sLefts SNil = SNil
sLefts (SCons (SLeft (sX :: Sing x_a16hC)) (sXs :: Sing xs_a16hD))
  = applySing
      (applySing (singFun2 @(:@#@$) SCons) sX)
      (applySing (singFun1 @LeftsSym0 sLefts) sXs)
sLefts (SCons (SRight _) (sXs :: Sing xs_a16hE))
  = applySing (singFun1 @LeftsSym0 sLefts) sXs
instance SingI (IsRightSym0 :: (~>) (Either a_a16dN b_a16dO) Bool) where
  sing = singFun1 @IsRightSym0 sIsRight
instance SingI (IsLeftSym0 :: (~>) (Either a_a16dP b_a16dQ) Bool) where
  sing = singFun1 @IsLeftSym0 sIsLeft
instance SingI (PartitionEithersSym0 :: (~>) [Either a_a16dR b_a16dS] ([a_a16dR],
                                                                        [b_a16dS])) where
  sing = singFun1 @PartitionEithersSym0 sPartitionEithers
instance SingI (RightsSym0 :: (~>) [Either a_a16dT b_a16dU] [b_a16dU]) where
  sing = singFun1 @RightsSym0 sRights
instance SingI (LeftsSym0 :: (~>) [Either a_a16dV b_a16dW] [a_a16dV]) where
  sing = singFun1 @LeftsSym0 sLefts

