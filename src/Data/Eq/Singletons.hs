{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}

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
-- Module      :  Data.Eq.Singletons
-- Copyright   :  (C) 2013 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted version of 'Eq', 'PEq', and the singleton version,
-- 'SEq'. Also defines the 'DefaultEq' type family, which is useful for
-- implementing boolean equality for non-inductively defined data types.
--
-----------------------------------------------------------------------------

module Data.Eq.Singletons (
  PEq(..), SEq(..),
  DefaultEq,

  -- * Defunctionalization symbols
  type (==@#@$), type (==@#@$$), type (==@#@$$$),
  type (/=@#@$), type (/=@#@$$), type (/=@#@$$$),
  DefaultEqSym0, DefaultEqSym1, DefaultEqSym2
  ) where

import Data.Bool.Singletons
import Data.Singletons.Base.Instances
import Data.Functor.Identity
import GHC.Base

import Data.Singletons.TH
-- The imports below are only needed for Haddock purposes.
import qualified Data.Kind as Kind ()
import qualified Data.Type.Equality as DTE ()
import qualified GHC.TypeLits as Lit ()
import Data.Kind (Type)

infix 4 /=
infix 4 ==
type (==@#@$) :: forall a_ax7h. (~>) a_ax7h ((~>) a_ax7h Bool)
data (==@#@$) :: (~>) a_ax7h ((~>) a_ax7h Bool)
  where
    (:==@#@$###) :: SameKind (Apply (==@#@$) arg_ax7o) ((==@#@$$) arg_ax7o) =>
                    (==@#@$) a6989586621679137103
type instance Apply @a_ax7h @((~>) a_ax7h Bool) (==@#@$) a6989586621679137103 = (==@#@$$) a6989586621679137103
instance SuppressUnusedWarnings (==@#@$) where
  suppressUnusedWarnings = snd ((,) (:==@#@$###) ())
infix 4 ==@#@$
type (==@#@$$) :: forall a_ax7h. a_ax7h -> (~>) a_ax7h Bool
data (==@#@$$) (a6989586621679137103 :: a_ax7h) :: (~>) a_ax7h Bool
  where
    (:==@#@$$###) :: SameKind (Apply ((==@#@$$) a6989586621679137103) arg_ax7o) ((==@#@$$$) a6989586621679137103 arg_ax7o) =>
                      (==@#@$$) a6989586621679137103 a6989586621679137104
type instance Apply @a_ax7h @Bool ((==@#@$$) a6989586621679137103) a6989586621679137104 = (==) a6989586621679137103 a6989586621679137104
instance SuppressUnusedWarnings ((==@#@$$) a6989586621679137103) where
  suppressUnusedWarnings = snd ((,) (:==@#@$$###) ())
infix 4 ==@#@$$
type (==@#@$$$) :: forall a_ax7h. a_ax7h -> a_ax7h -> Bool
type family (==@#@$$$) @a_ax7h (a6989586621679137103 :: a_ax7h) (a6989586621679137104 :: a_ax7h) :: Bool where
  (==@#@$$$) a6989586621679137103 a6989586621679137104 = (==) a6989586621679137103 a6989586621679137104
infix 4 ==@#@$$$
type (/=@#@$) :: forall a_ax7h. (~>) a_ax7h ((~>) a_ax7h Bool)
data (/=@#@$) :: (~>) a_ax7h ((~>) a_ax7h Bool)
  where
    (:/=@#@$###) :: SameKind (Apply (/=@#@$) arg_ax7t) ((/=@#@$$) arg_ax7t) =>
                    (/=@#@$) a6989586621679137108
type instance Apply @a_ax7h @((~>) a_ax7h Bool) (/=@#@$) a6989586621679137108 = (/=@#@$$) a6989586621679137108
instance SuppressUnusedWarnings (/=@#@$) where
  suppressUnusedWarnings = snd ((,) (:/=@#@$###) ())
infix 4 /=@#@$
type (/=@#@$$) :: forall a_ax7h. a_ax7h -> (~>) a_ax7h Bool
data (/=@#@$$) (a6989586621679137108 :: a_ax7h) :: (~>) a_ax7h Bool
  where
    (:/=@#@$$###) :: SameKind (Apply ((/=@#@$$) a6989586621679137108) arg_ax7t) ((/=@#@$$$) a6989586621679137108 arg_ax7t) =>
                      (/=@#@$$) a6989586621679137108 a6989586621679137109
type instance Apply @a_ax7h @Bool ((/=@#@$$) a6989586621679137108) a6989586621679137109 = (/=) a6989586621679137108 a6989586621679137109
instance SuppressUnusedWarnings ((/=@#@$$) a6989586621679137108) where
  suppressUnusedWarnings = snd ((,) (:/=@#@$$###) ())
infix 4 /=@#@$$
type (/=@#@$$$) :: forall a_ax7h. a_ax7h -> a_ax7h -> Bool
type family (/=@#@$$$) @a_ax7h (a6989586621679137108 :: a_ax7h) (a6989586621679137109 :: a_ax7h) :: Bool where
  (/=@#@$$$) a6989586621679137108 a6989586621679137109 = (/=) a6989586621679137108 a6989586621679137109
infix 4 /=@#@$$$
type TFHelper_6989586621679137112 :: forall a_ax7h. a_ax7h
                                                    -> a_ax7h -> Bool
type family TFHelper_6989586621679137112 @a_ax7h (a_ax7A :: a_ax7h) (a_ax7B :: a_ax7h) :: Bool where
  TFHelper_6989586621679137112 @a_ax7h (x_ax7F :: a_ax7h) (y_ax7G :: a_ax7h) = Apply NotSym0 (Apply (Apply (==@#@$) x_ax7F) y_ax7G)
type TFHelper_6989586621679137123 :: forall a_ax7h. a_ax7h
                                                    -> a_ax7h -> Bool
type family TFHelper_6989586621679137123 @a_ax7h (a_ax7L :: a_ax7h) (a_ax7M :: a_ax7h) :: Bool where
  TFHelper_6989586621679137123 @a_ax7h (x_ax7Q :: a_ax7h) (y_ax7R :: a_ax7h) = Apply NotSym0 (Apply (Apply (/=@#@$) x_ax7Q) y_ax7R)
class PEq a_ax7h where
  type family (==) (arg_ax7m :: a_ax7h) (arg_ax7n :: a_ax7h) :: Bool
  type family (/=) (arg_ax7r :: a_ax7h) (arg_ax7s :: a_ax7h) :: Bool
  type (/=) a_ax7w a_ax7x = TFHelper_6989586621679137112 a_ax7w a_ax7x
  type (==) a_ax7H a_ax7I = TFHelper_6989586621679137123 a_ax7H a_ax7I
infix 4 %/=
infix 4 %==
class SEq a_ax7h where
  (%==) ::
    (forall (t_ax7S :: a_ax7h) (t_ax7T :: a_ax7h).
      Sing t_ax7S
      -> Sing t_ax7T -> Sing ((==) t_ax7S t_ax7T :: Bool) :: Type)
  (%/=) ::
    (forall (t_ax7X :: a_ax7h) (t_ax7Y :: a_ax7h).
      Sing t_ax7X
      -> Sing t_ax7Y -> Sing ((/=) t_ax7X t_ax7Y :: Bool) :: Type)
  default (%==) ::
            (forall (t_ax7S :: a_ax7h) (t_ax7T :: a_ax7h).
              (((==) t_ax7S t_ax7T :: Bool)
              ~ TFHelper_6989586621679137123 t_ax7S t_ax7T) =>
              Sing t_ax7S
              -> Sing t_ax7T -> Sing ((==) t_ax7S t_ax7T :: Bool) :: Type)
  default (%/=) ::
            (forall (t_ax7X :: a_ax7h) (t_ax7Y :: a_ax7h).
              (((/=) t_ax7X t_ax7Y :: Bool)
              ~ TFHelper_6989586621679137112 t_ax7X t_ax7Y) =>
              Sing t_ax7X
              -> Sing t_ax7Y -> Sing ((/=) t_ax7X t_ax7Y :: Bool) :: Type)
  (%/=) (sX :: Sing x_ax7F) (sY :: Sing y_ax7G)
    = applySing
        (singFun1 @NotSym0 sNot)
        (applySing (applySing (singFun2 @(==@#@$) (%==)) sX) sY)
  (%==) (sX :: Sing x_ax7Q) (sY :: Sing y_ax7R)
    = applySing
        (singFun1 @NotSym0 sNot)
        (applySing (applySing (singFun2 @(/=@#@$) (%/=)) sX) sY)
instance SEq a_ax7h =>
          SingI ((==@#@$) :: (~>) a_ax7h ((~>) a_ax7h Bool)) where
  sing = singFun2 @(==@#@$) (%==)
instance (SEq a_ax7h, SingI d_ax7U) =>
          SingI ((==@#@$$) (d_ax7U :: a_ax7h) :: (~>) a_ax7h Bool) where
  sing
    = singFun1 @((==@#@$$) (d_ax7U :: a_ax7h)) ((%==) (sing @d_ax7U))
instance SEq a_ax7h =>
          SingI1 ((==@#@$$) :: a_ax7h -> (~>) a_ax7h Bool) where
  liftSing (s_ax7W :: Sing (d_ax7U :: a_ax7h))
    = singFun1 @((==@#@$$) (d_ax7U :: a_ax7h)) ((%==) s_ax7W)
instance SEq a_ax7h =>
          SingI ((/=@#@$) :: (~>) a_ax7h ((~>) a_ax7h Bool)) where
  sing = singFun2 @(/=@#@$) (%/=)
instance (SEq a_ax7h, SingI d_ax7Z) =>
          SingI ((/=@#@$$) (d_ax7Z :: a_ax7h) :: (~>) a_ax7h Bool) where
  sing
    = singFun1 @((/=@#@$$) (d_ax7Z :: a_ax7h)) ((%/=) (sing @d_ax7Z))
instance SEq a_ax7h =>
          SingI1 ((/=@#@$$) :: a_ax7h -> (~>) a_ax7h Bool) where
  liftSing (s_ax81 :: Sing (d_ax7Z :: a_ax7h))
    = singFun1 @((/=@#@$$) (d_ax7Z :: a_ax7h)) ((%/=) s_ax81)

-- | One way to compute Boolean equality for types of any kind. This will
-- return 'True' if the two arguments are known to be the same type and 'False'
-- if they are known to be apart. Examples:
--
-- @
-- >>> 'DefaultEq' 'Nothing' 'Nothing'
-- 'True'
-- >>> 'DefaultEq' 'Nothing' ('Just' a)
-- 'False'
-- >>> 'DefaultEq' a a
-- 'True'
-- @
--
-- 'DefaultEq' is most suited for data types that are not inductively defined.
-- Four concrete examples of this are 'Natural', 'Lit.Symbol', 'Lit.Char', and
-- 'Kind.Type'. One cannot implement boolean equality for these types by
-- pattern matching alone, so 'DefaultEq' is a good fit instead.
--
-- The downside to 'DefaultEq' is that it can fail to reduce if it is unable
-- to determine if two types are equal or apart. Here is one such example:
--
-- @
-- 'DefaultEq' ('Just' a) ('Just' b)
-- @
--
-- What should this reduce to? It depends on what @a@ and @b@ are. 'DefaultEq'
-- has no way of knowing what these two types are, and as a result, this type
-- will be stuck. This is a pitfall that you can run into if you use
-- 'DefaultEq' to implement boolean equality for an inductive data type like
-- 'Maybe'. For this reason, it is usually recommended to implement boolean
-- equality for inductive data types using pattern matching and recursion, not
-- 'DefaultEq'.
--
-- Note that this definition is slightly different from the '(DTE.==)' type
-- family from "Data.Type.Equality" in @base@, as '(DTE.==)' attempts to
-- distinguish applications of type constructors from other types. As a result,
-- @a == a@ does not reduce to 'True' for every @a@, but @'DefaultEq' a a@
-- /does/ reduce to 'True' for every @a@. The latter behavior is more desirable
-- for @singletons@' purposes, so we use it instead of '(DTE.==)'.
type DefaultEq :: k -> k -> Bool
type family DefaultEq (a :: k) (b :: k) :: Bool where
  DefaultEq a a = 'True
  DefaultEq a b = 'False
type DefaultEqSym0 :: forall (k_ax8m :: Type). (~>) k_ax8m ((~>) k_ax8m Bool)
data DefaultEqSym0 :: (~>) k_ax8m ((~>) k_ax8m Bool)
  where
    DefaultEqSym0KindInference :: SameKind (Apply DefaultEqSym0 arg_axyp) (DefaultEqSym1 arg_axyp) =>
                                  DefaultEqSym0 a6989586621679138778
type instance Apply @k_ax8m @((~>) k_ax8m Bool) DefaultEqSym0 a6989586621679138778 = DefaultEqSym1 a6989586621679138778
instance SuppressUnusedWarnings DefaultEqSym0 where
  suppressUnusedWarnings = snd ((,) DefaultEqSym0KindInference ())
type DefaultEqSym1 :: forall (k_ax8m :: Type). k_ax8m
                                                -> (~>) k_ax8m Bool
data DefaultEqSym1 (a6989586621679138778 :: k_ax8m) :: (~>) k_ax8m Bool
  where
    DefaultEqSym1KindInference :: SameKind (Apply (DefaultEqSym1 a6989586621679138778) arg_axyp) (DefaultEqSym2 a6989586621679138778 arg_axyp) =>
                                  DefaultEqSym1 a6989586621679138778 a6989586621679138779
type instance Apply @k_ax8m @Bool (DefaultEqSym1 a6989586621679138778) a6989586621679138779 = DefaultEq a6989586621679138778 a6989586621679138779
instance SuppressUnusedWarnings (DefaultEqSym1 a6989586621679138778) where
  suppressUnusedWarnings = snd ((,) DefaultEqSym1KindInference ())
type DefaultEqSym2 :: forall (k_ax8m :: Type). k_ax8m
                                                -> k_ax8m -> Bool
type family DefaultEqSym2 @(k_ax8m :: Type) (a6989586621679138778 :: k_ax8m) (a6989586621679138779 :: k_ax8m) :: Bool where
  DefaultEqSym2 a6989586621679138778 a6989586621679138779 = DefaultEq a6989586621679138778 a6989586621679138779

type TFHelper_6989586621679139138 :: forall a_11. Maybe a_11
                                                      -> Maybe a_11 -> Bool
type family TFHelper_6989586621679139138 @a_11 (a_axEg :: Maybe a_11) (a_axEh :: Maybe a_11) :: Bool where
  TFHelper_6989586621679139138 @a_11 ('Nothing :: Maybe a_11) ('Nothing :: Maybe a_11) = TrueSym0
  TFHelper_6989586621679139138 @a_11 ('Nothing :: Maybe a_11) ('Just _ :: Maybe a_11) = FalseSym0
  TFHelper_6989586621679139138 @a_11 ('Just _ :: Maybe a_11) ('Nothing :: Maybe a_11) = FalseSym0
  TFHelper_6989586621679139138 @a_11 ('Just a_6989586621679139132_axEl :: Maybe a_11) ('Just b_6989586621679139134_axEm :: Maybe a_11) = Apply (Apply (==@#@$) a_6989586621679139132_axEl) b_6989586621679139134_axEm
instance PEq (Maybe a_11) where
  type (==) a_axEc a_axEd = TFHelper_6989586621679139138 a_axEc a_axEd
instance SEq a_11 => SEq (Maybe a_11) where
  (%==) SNothing SNothing = STrue
  (%==) SNothing (SJust _) = SFalse
  (%==) (SJust _) SNothing = SFalse
  (%==)
    (SJust (sA_6989586621679139132 :: Sing a_6989586621679139132_axEl))
    (SJust (sB_6989586621679139134 :: Sing b_6989586621679139134_axEm))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139132)
        sB_6989586621679139134
type TFHelper_6989586621679139167 :: forall a_11. [a_11]
                                                  -> [a_11] -> Bool
type family TFHelper_6989586621679139167 @a_11 (a_axEJ :: [a_11]) (a_axEK :: [a_11]) :: Bool where
  TFHelper_6989586621679139167 @a_11 ('[] :: [a_11]) ('[] :: [a_11]) = TrueSym0
  TFHelper_6989586621679139167 @a_11 ('[] :: [a_11]) ('(:) _ _ :: [a_11]) = FalseSym0
  TFHelper_6989586621679139167 @a_11 ('(:) _ _ :: [a_11]) ('[] :: [a_11]) = FalseSym0
  TFHelper_6989586621679139167 @a_11 ('(:) a_6989586621679139157_axEO a_6989586621679139159_axEP :: [a_11]) ('(:) b_6989586621679139161_axEQ b_6989586621679139163_axER :: [a_11]) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139157_axEO) b_6989586621679139161_axEQ)) (Apply (Apply (==@#@$) a_6989586621679139159_axEP) b_6989586621679139163_axER)
instance PEq [a_11] where
  type (==) a_axEF a_axEG = TFHelper_6989586621679139167 a_axEF a_axEG
instance (SEq a_11, SEq [a_11]) => SEq [a_11] where
  (%==) SNil SNil = STrue
  (%==) SNil (SCons _ _) = SFalse
  (%==) (SCons _ _) SNil = SFalse
  (%==)
    (SCons (sA_6989586621679139157 :: Sing a_6989586621679139157_axEO)
            (sA_6989586621679139159 :: Sing a_6989586621679139159_axEP))
    (SCons (sB_6989586621679139161 :: Sing b_6989586621679139161_axEQ)
            (sB_6989586621679139163 :: Sing b_6989586621679139163_axER))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139157)
              sB_6989586621679139161))
        (applySing
            (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139159)
            sB_6989586621679139163)
type TFHelper_6989586621679139210 :: forall a_a8ep
                                            b_a8eq. Either a_a8ep b_a8eq
                                                    -> Either a_a8ep b_a8eq -> Bool
type family TFHelper_6989586621679139210 @a_a8ep @b_a8eq (a_axFq :: Either a_a8ep b_a8eq) (a_axFr :: Either a_a8ep b_a8eq) :: Bool where
  TFHelper_6989586621679139210 @a_a8ep @b_a8eq ('Left a_6989586621679139200_axFv :: Either a_a8ep b_a8eq) ('Left b_6989586621679139202_axFw :: Either a_a8ep b_a8eq) = Apply (Apply (==@#@$) a_6989586621679139200_axFv) b_6989586621679139202_axFw
  TFHelper_6989586621679139210 @a_a8ep @b_a8eq ('Left _ :: Either a_a8ep b_a8eq) ('Right _ :: Either a_a8ep b_a8eq) = FalseSym0
  TFHelper_6989586621679139210 @a_a8ep @b_a8eq ('Right _ :: Either a_a8ep b_a8eq) ('Left _ :: Either a_a8ep b_a8eq) = FalseSym0
  TFHelper_6989586621679139210 @a_a8ep @b_a8eq ('Right a_6989586621679139204_axFx :: Either a_a8ep b_a8eq) ('Right b_6989586621679139206_axFy :: Either a_a8ep b_a8eq) = Apply (Apply (==@#@$) a_6989586621679139204_axFx) b_6989586621679139206_axFy
instance PEq (Either a_a8ep b_a8eq) where
  type (==) a_axFm a_axFn = TFHelper_6989586621679139210 a_axFm a_axFn
instance (SEq a_a8ep, SEq b_a8eq) =>
          SEq (Either a_a8ep b_a8eq) where
  (%==)
    (SLeft (sA_6989586621679139200 :: Sing a_6989586621679139200_axFv))
    (SLeft (sB_6989586621679139202 :: Sing b_6989586621679139202_axFw))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139200)
        sB_6989586621679139202
  (%==) (SLeft _) (SRight _) = SFalse
  (%==) (SRight _) (SLeft _) = SFalse
  (%==)
    (SRight (sA_6989586621679139204 :: Sing a_6989586621679139204_axFx))
    (SRight (sB_6989586621679139206 :: Sing b_6989586621679139206_axFy))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139204)
        sB_6989586621679139206
type TFHelper_6989586621679139234 :: forall a_a8fb. GHC.Base.NonEmpty a_a8fb
                                                    -> GHC.Base.NonEmpty a_a8fb -> Bool
type family TFHelper_6989586621679139234 @a_a8fb (a_axFO :: GHC.Base.NonEmpty a_a8fb) (a_axFP :: GHC.Base.NonEmpty a_a8fb) :: Bool where
  TFHelper_6989586621679139234 @a_a8fb ('(GHC.Base.:|) a_6989586621679139224_axFT a_6989586621679139226_axFU :: GHC.Base.NonEmpty a_a8fb) ('(GHC.Base.:|) b_6989586621679139228_axFV b_6989586621679139230_axFW :: GHC.Base.NonEmpty a_a8fb) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139224_axFT) b_6989586621679139228_axFV)) (Apply (Apply (==@#@$) a_6989586621679139226_axFU) b_6989586621679139230_axFW)
instance PEq (GHC.Base.NonEmpty a_a8fb) where
  type (==) a_axFK a_axFL = TFHelper_6989586621679139234 a_axFK a_axFL
instance (SEq a_a8fb, SEq [a_a8fb]) =>
          SEq (GHC.Base.NonEmpty a_a8fb) where
  (%==)
    ((:%|) (sA_6989586621679139224 :: Sing a_6989586621679139224_axFT)
            (sA_6989586621679139226 :: Sing a_6989586621679139226_axFU))
    ((:%|) (sB_6989586621679139228 :: Sing b_6989586621679139228_axFV)
            (sB_6989586621679139230 :: Sing b_6989586621679139230_axFW))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139224)
              sB_6989586621679139228))
        (applySing
            (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139226)
            sB_6989586621679139230)
type TFHelper_6989586621679139247 :: Void -> Void -> Bool
type family TFHelper_6989586621679139247 (a_axG1 :: Void) (a_axG2 :: Void) :: Bool where
  TFHelper_6989586621679139247 _ _ = TrueSym0
instance PEq Void where
  type (==) a_axFX a_axFY = TFHelper_6989586621679139247 a_axFX a_axFY
instance SEq Void where
  (%==) _ _ = STrue
type TFHelper_6989586621679139270 :: forall a_11 b_12. (a_11, b_12)
                                                        -> (a_11, b_12) -> Bool
type family TFHelper_6989586621679139270 @a_11 @b_12 (a_axGo :: (a_11,
                                                                  b_12)) (a_axGp :: (a_11,
                                                                                    b_12)) :: Bool where
  TFHelper_6989586621679139270 @a_11 @b_12 ('(a_6989586621679139260_axGt,
                                              a_6989586621679139262_axGu) :: (a_11,
                                                                              b_12)) ('(b_6989586621679139264_axGv,
                                                                                        b_6989586621679139266_axGw) :: (a_11,
                                                                                                                        b_12)) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139260_axGt) b_6989586621679139264_axGv)) (Apply (Apply (==@#@$) a_6989586621679139262_axGu) b_6989586621679139266_axGw)
instance PEq (a_11, b_12) where
  type (==) a_axGk a_axGl = TFHelper_6989586621679139270 a_axGk a_axGl
instance (SEq a_11, SEq b_12) => SEq (a_11, b_12) where
  (%==)
    (STuple2 (sA_6989586621679139260 :: Sing a_6989586621679139260_axGt)
              (sA_6989586621679139262 :: Sing a_6989586621679139262_axGu))
    (STuple2 (sB_6989586621679139264 :: Sing b_6989586621679139264_axGv)
              (sB_6989586621679139266 :: Sing b_6989586621679139266_axGw))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139260)
              sB_6989586621679139264))
        (applySing
            (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139262)
            sB_6989586621679139266)
type TFHelper_6989586621679139304 :: forall a_11 b_12 c_13. (a_11,
                                                              b_12, c_13)
                                                            -> (a_11, b_12, c_13) -> Bool
type family TFHelper_6989586621679139304 @a_11 @b_12 @c_13 (a_axGW :: (a_11,
                                                                        b_12,
                                                                        c_13)) (a_axGX :: (a_11,
                                                                                          b_12,
                                                                                          c_13)) :: Bool where
  TFHelper_6989586621679139304 @a_11 @b_12 @c_13 ('(a_6989586621679139290_axH1,
                                                    a_6989586621679139292_axH2,
                                                    a_6989586621679139294_axH3) :: (a_11, b_12,
                                                                                    c_13)) ('(b_6989586621679139296_axH4,
                                                                                              b_6989586621679139298_axH5,
                                                                                              b_6989586621679139300_axH6) :: (a_11,
                                                                                                                              b_12,
                                                                                                                              c_13)) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139290_axH1) b_6989586621679139296_axH4)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139292_axH2) b_6989586621679139298_axH5)) (Apply (Apply (==@#@$) a_6989586621679139294_axH3) b_6989586621679139300_axH6))
instance PEq (a_11, b_12, c_13) where
  type (==) a_axGS a_axGT = TFHelper_6989586621679139304 a_axGS a_axGT
instance (SEq a_11, SEq b_12, SEq c_13) =>
          SEq (a_11, b_12, c_13) where
  (%==)
    (STuple3 (sA_6989586621679139290 :: Sing a_6989586621679139290_axH1)
              (sA_6989586621679139292 :: Sing a_6989586621679139292_axH2)
              (sA_6989586621679139294 :: Sing a_6989586621679139294_axH3))
    (STuple3 (sB_6989586621679139296 :: Sing b_6989586621679139296_axH4)
              (sB_6989586621679139298 :: Sing b_6989586621679139298_axH5)
              (sB_6989586621679139300 :: Sing b_6989586621679139300_axH6))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139290)
              sB_6989586621679139296))
        (applySing
            (applySing
              (singFun2 @(&&@#@$) (%&&))
              (applySing
                  (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139292)
                  sB_6989586621679139298))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139294)
              sB_6989586621679139300))
type TFHelper_6989586621679139347 :: forall a_11
                                            b_12
                                            c_13
                                            d_14. (a_11, b_12, c_13, d_14)
                                                  -> (a_11, b_12, c_13, d_14) -> Bool
type family TFHelper_6989586621679139347 @a_11 @b_12 @c_13 @d_14 (a_axHD :: (a_11,
                                                                              b_12, c_13,
                                                                              d_14)) (a_axHE :: (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14)) :: Bool where
  TFHelper_6989586621679139347 @a_11 @b_12 @c_13 @d_14 ('(a_6989586621679139329_axHI,
                                                          a_6989586621679139331_axHJ,
                                                          a_6989586621679139333_axHK,
                                                          a_6989586621679139335_axHL) :: (a_11,
                                                                                          b_12,
                                                                                          c_13,
                                                                                          d_14)) ('(b_6989586621679139337_axHM,
                                                                                                    b_6989586621679139339_axHN,
                                                                                                    b_6989586621679139341_axHO,
                                                                                                    b_6989586621679139343_axHP) :: (a_11,
                                                                                                                                    b_12,
                                                                                                                                    c_13,
                                                                                                                                    d_14)) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139329_axHI) b_6989586621679139337_axHM)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139331_axHJ) b_6989586621679139339_axHN)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139333_axHK) b_6989586621679139341_axHO)) (Apply (Apply (==@#@$) a_6989586621679139335_axHL) b_6989586621679139343_axHP)))
instance PEq (a_11, b_12, c_13, d_14) where
  type (==) a_axHz a_axHA = TFHelper_6989586621679139347 a_axHz a_axHA
instance (SEq a_11, SEq b_12, SEq c_13, SEq d_14) =>
          SEq (a_11, b_12, c_13, d_14) where
  (%==)
    (STuple4 (sA_6989586621679139329 :: Sing a_6989586621679139329_axHI)
              (sA_6989586621679139331 :: Sing a_6989586621679139331_axHJ)
              (sA_6989586621679139333 :: Sing a_6989586621679139333_axHK)
              (sA_6989586621679139335 :: Sing a_6989586621679139335_axHL))
    (STuple4 (sB_6989586621679139337 :: Sing b_6989586621679139337_axHM)
              (sB_6989586621679139339 :: Sing b_6989586621679139339_axHN)
              (sB_6989586621679139341 :: Sing b_6989586621679139341_axHO)
              (sB_6989586621679139343 :: Sing b_6989586621679139343_axHP))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139329)
              sB_6989586621679139337))
        (applySing
            (applySing
              (singFun2 @(&&@#@$) (%&&))
              (applySing
                  (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139331)
                  sB_6989586621679139339))
            (applySing
              (applySing
                  (singFun2 @(&&@#@$) (%&&))
                  (applySing
                    (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139333)
                    sB_6989586621679139341))
              (applySing
                  (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139335)
                  sB_6989586621679139343)))
type TFHelper_6989586621679139399 :: forall a_11
                                            b_12
                                            c_13
                                            d_14
                                            e_15. (a_11, b_12, c_13, d_14, e_15)
                                                  -> (a_11, b_12, c_13, d_14, e_15) -> Bool
type family TFHelper_6989586621679139399 @a_11 @b_12 @c_13 @d_14 @e_15 (a_axIt :: (a_11,
                                                                                    b_12, c_13,
                                                                                    d_14,
                                                                                    e_15)) (a_axIu :: (a_11,
                                                                                                      b_12,
                                                                                                      c_13,
                                                                                                      d_14,
                                                                                                      e_15)) :: Bool where
  TFHelper_6989586621679139399 @a_11 @b_12 @c_13 @d_14 @e_15 ('(a_6989586621679139377_axIy,
                                                                a_6989586621679139379_axIz,
                                                                a_6989586621679139381_axIA,
                                                                a_6989586621679139383_axIB,
                                                                a_6989586621679139385_axIC) :: (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14,
                                                                                                e_15)) ('(b_6989586621679139387_axID,
                                                                                                          b_6989586621679139389_axIE,
                                                                                                          b_6989586621679139391_axIF,
                                                                                                          b_6989586621679139393_axIG,
                                                                                                          b_6989586621679139395_axIH) :: (a_11,
                                                                                                                                          b_12,
                                                                                                                                          c_13,
                                                                                                                                          d_14,
                                                                                                                                          e_15)) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139377_axIy) b_6989586621679139387_axID)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139379_axIz) b_6989586621679139389_axIE)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139381_axIA) b_6989586621679139391_axIF)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139383_axIB) b_6989586621679139393_axIG)) (Apply (Apply (==@#@$) a_6989586621679139385_axIC) b_6989586621679139395_axIH))))
instance PEq (a_11, b_12, c_13, d_14, e_15) where
  type (==) a_axIp a_axIq = TFHelper_6989586621679139399 a_axIp a_axIq
instance (SEq a_11, SEq b_12, SEq c_13, SEq d_14, SEq e_15) =>
          SEq (a_11, b_12, c_13, d_14, e_15) where
  (%==)
    (STuple5 (sA_6989586621679139377 :: Sing a_6989586621679139377_axIy)
              (sA_6989586621679139379 :: Sing a_6989586621679139379_axIz)
              (sA_6989586621679139381 :: Sing a_6989586621679139381_axIA)
              (sA_6989586621679139383 :: Sing a_6989586621679139383_axIB)
              (sA_6989586621679139385 :: Sing a_6989586621679139385_axIC))
    (STuple5 (sB_6989586621679139387 :: Sing b_6989586621679139387_axID)
              (sB_6989586621679139389 :: Sing b_6989586621679139389_axIE)
              (sB_6989586621679139391 :: Sing b_6989586621679139391_axIF)
              (sB_6989586621679139393 :: Sing b_6989586621679139393_axIG)
              (sB_6989586621679139395 :: Sing b_6989586621679139395_axIH))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139377)
              sB_6989586621679139387))
        (applySing
            (applySing
              (singFun2 @(&&@#@$) (%&&))
              (applySing
                  (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139379)
                  sB_6989586621679139389))
            (applySing
              (applySing
                  (singFun2 @(&&@#@$) (%&&))
                  (applySing
                    (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139381)
                    sB_6989586621679139391))
              (applySing
                  (applySing
                    (singFun2 @(&&@#@$) (%&&))
                    (applySing
                        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139383)
                        sB_6989586621679139393))
                  (applySing
                    (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139385)
                    sB_6989586621679139395))))
type TFHelper_6989586621679139460 :: forall a_11
                                            b_12
                                            c_13
                                            d_14
                                            e_15
                                            f_16. (a_11, b_12, c_13, d_14, e_15, f_16)
                                                  -> (a_11, b_12, c_13, d_14, e_15, f_16)
                                                      -> Bool
type family TFHelper_6989586621679139460 @a_11 @b_12 @c_13 @d_14 @e_15 @f_16 (a_axJs :: (a_11,
                                                                                          b_12,
                                                                                          c_13,
                                                                                          d_14,
                                                                                          e_15,
                                                                                          f_16)) (a_axJt :: (a_11,
                                                                                                            b_12,
                                                                                                            c_13,
                                                                                                            d_14,
                                                                                                            e_15,
                                                                                                            f_16)) :: Bool where
  TFHelper_6989586621679139460 @a_11 @b_12 @c_13 @d_14 @e_15 @f_16 ('(a_6989586621679139434_axJx,
                                                                      a_6989586621679139436_axJy,
                                                                      a_6989586621679139438_axJz,
                                                                      a_6989586621679139440_axJA,
                                                                      a_6989586621679139442_axJB,
                                                                      a_6989586621679139444_axJC) :: (a_11,
                                                                                                      b_12,
                                                                                                      c_13,
                                                                                                      d_14,
                                                                                                      e_15,
                                                                                                      f_16)) ('(b_6989586621679139446_axJD,
                                                                                                                b_6989586621679139448_axJE,
                                                                                                                b_6989586621679139450_axJF,
                                                                                                                b_6989586621679139452_axJG,
                                                                                                                b_6989586621679139454_axJH,
                                                                                                                b_6989586621679139456_axJI) :: (a_11,
                                                                                                                                                b_12,
                                                                                                                                                c_13,
                                                                                                                                                d_14,
                                                                                                                                                e_15,
                                                                                                                                                f_16)) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139434_axJx) b_6989586621679139446_axJD)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139436_axJy) b_6989586621679139448_axJE)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139438_axJz) b_6989586621679139450_axJF)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139440_axJA) b_6989586621679139452_axJG)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139442_axJB) b_6989586621679139454_axJH)) (Apply (Apply (==@#@$) a_6989586621679139444_axJC) b_6989586621679139456_axJI)))))
instance PEq (a_11, b_12, c_13, d_14, e_15, f_16) where
  type (==) a_axJo a_axJp = TFHelper_6989586621679139460 a_axJo a_axJp
instance (SEq a_11,
          SEq b_12,
          SEq c_13,
          SEq d_14,
          SEq e_15,
          SEq f_16) =>
          SEq (a_11, b_12, c_13, d_14, e_15, f_16) where
  (%==)
    (STuple6 (sA_6989586621679139434 :: Sing a_6989586621679139434_axJx)
              (sA_6989586621679139436 :: Sing a_6989586621679139436_axJy)
              (sA_6989586621679139438 :: Sing a_6989586621679139438_axJz)
              (sA_6989586621679139440 :: Sing a_6989586621679139440_axJA)
              (sA_6989586621679139442 :: Sing a_6989586621679139442_axJB)
              (sA_6989586621679139444 :: Sing a_6989586621679139444_axJC))
    (STuple6 (sB_6989586621679139446 :: Sing b_6989586621679139446_axJD)
              (sB_6989586621679139448 :: Sing b_6989586621679139448_axJE)
              (sB_6989586621679139450 :: Sing b_6989586621679139450_axJF)
              (sB_6989586621679139452 :: Sing b_6989586621679139452_axJG)
              (sB_6989586621679139454 :: Sing b_6989586621679139454_axJH)
              (sB_6989586621679139456 :: Sing b_6989586621679139456_axJI))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139434)
              sB_6989586621679139446))
        (applySing
            (applySing
              (singFun2 @(&&@#@$) (%&&))
              (applySing
                  (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139436)
                  sB_6989586621679139448))
            (applySing
              (applySing
                  (singFun2 @(&&@#@$) (%&&))
                  (applySing
                    (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139438)
                    sB_6989586621679139450))
              (applySing
                  (applySing
                    (singFun2 @(&&@#@$) (%&&))
                    (applySing
                        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139440)
                        sB_6989586621679139452))
                  (applySing
                    (applySing
                        (singFun2 @(&&@#@$) (%&&))
                        (applySing
                          (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139442)
                          sB_6989586621679139454))
                    (applySing
                        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139444)
                        sB_6989586621679139456)))))
type TFHelper_6989586621679139530 :: forall a_11
                                            b_12
                                            c_13
                                            d_14
                                            e_15
                                            f_16
                                            g_17. (a_11, b_12, c_13, d_14, e_15, f_16, g_17)
                                                  -> (a_11, b_12, c_13, d_14, e_15, f_16, g_17)
                                                      -> Bool
type family TFHelper_6989586621679139530 @a_11 @b_12 @c_13 @d_14 @e_15 @f_16 @g_17 (a_axKA :: (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14,
                                                                                                e_15,
                                                                                                f_16,
                                                                                                g_17)) (a_axKB :: (a_11,
                                                                                                                  b_12,
                                                                                                                  c_13,
                                                                                                                  d_14,
                                                                                                                  e_15,
                                                                                                                  f_16,
                                                                                                                  g_17)) :: Bool where
  TFHelper_6989586621679139530 @a_11 @b_12 @c_13 @d_14 @e_15 @f_16 @g_17 ('(a_6989586621679139500_axKF,
                                                                            a_6989586621679139502_axKG,
                                                                            a_6989586621679139504_axKH,
                                                                            a_6989586621679139506_axKI,
                                                                            a_6989586621679139508_axKJ,
                                                                            a_6989586621679139510_axKK,
                                                                            a_6989586621679139512_axKL) :: (a_11,
                                                                                                            b_12,
                                                                                                            c_13,
                                                                                                            d_14,
                                                                                                            e_15,
                                                                                                            f_16,
                                                                                                            g_17)) ('(b_6989586621679139514_axKM,
                                                                                                                      b_6989586621679139516_axKN,
                                                                                                                      b_6989586621679139518_axKO,
                                                                                                                      b_6989586621679139520_axKP,
                                                                                                                      b_6989586621679139522_axKQ,
                                                                                                                      b_6989586621679139524_axKR,
                                                                                                                      b_6989586621679139526_axKS) :: (a_11,
                                                                                                                                                      b_12,
                                                                                                                                                      c_13,
                                                                                                                                                      d_14,
                                                                                                                                                      e_15,
                                                                                                                                                      f_16,
                                                                                                                                                      g_17)) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139500_axKF) b_6989586621679139514_axKM)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139502_axKG) b_6989586621679139516_axKN)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139504_axKH) b_6989586621679139518_axKO)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139506_axKI) b_6989586621679139520_axKP)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139508_axKJ) b_6989586621679139522_axKQ)) (Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679139510_axKK) b_6989586621679139524_axKR)) (Apply (Apply (==@#@$) a_6989586621679139512_axKL) b_6989586621679139526_axKS))))))
instance PEq (a_11, b_12, c_13, d_14, e_15, f_16, g_17) where
  type (==) a_axKw a_axKx = TFHelper_6989586621679139530 a_axKw a_axKx
instance (SEq a_11,
          SEq b_12,
          SEq c_13,
          SEq d_14,
          SEq e_15,
          SEq f_16,
          SEq g_17) =>
          SEq (a_11, b_12, c_13, d_14, e_15, f_16, g_17) where
  (%==)
    (STuple7 (sA_6989586621679139500 :: Sing a_6989586621679139500_axKF)
              (sA_6989586621679139502 :: Sing a_6989586621679139502_axKG)
              (sA_6989586621679139504 :: Sing a_6989586621679139504_axKH)
              (sA_6989586621679139506 :: Sing a_6989586621679139506_axKI)
              (sA_6989586621679139508 :: Sing a_6989586621679139508_axKJ)
              (sA_6989586621679139510 :: Sing a_6989586621679139510_axKK)
              (sA_6989586621679139512 :: Sing a_6989586621679139512_axKL))
    (STuple7 (sB_6989586621679139514 :: Sing b_6989586621679139514_axKM)
              (sB_6989586621679139516 :: Sing b_6989586621679139516_axKN)
              (sB_6989586621679139518 :: Sing b_6989586621679139518_axKO)
              (sB_6989586621679139520 :: Sing b_6989586621679139520_axKP)
              (sB_6989586621679139522 :: Sing b_6989586621679139522_axKQ)
              (sB_6989586621679139524 :: Sing b_6989586621679139524_axKR)
              (sB_6989586621679139526 :: Sing b_6989586621679139526_axKS))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139500)
              sB_6989586621679139514))
        (applySing
            (applySing
              (singFun2 @(&&@#@$) (%&&))
              (applySing
                  (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139502)
                  sB_6989586621679139516))
            (applySing
              (applySing
                  (singFun2 @(&&@#@$) (%&&))
                  (applySing
                    (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139504)
                    sB_6989586621679139518))
              (applySing
                  (applySing
                    (singFun2 @(&&@#@$) (%&&))
                    (applySing
                        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139506)
                        sB_6989586621679139520))
                  (applySing
                    (applySing
                        (singFun2 @(&&@#@$) (%&&))
                        (applySing
                          (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139508)
                          sB_6989586621679139522))
                    (applySing
                        (applySing
                          (singFun2 @(&&@#@$) (%&&))
                          (applySing
                              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139510)
                              sB_6989586621679139524))
                        (applySing
                          (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139512)
                          sB_6989586621679139526))))))
type TFHelper_6989586621679139560 :: forall a_a8sO. Data.Functor.Identity.Identity a_a8sO
                                                    -> Data.Functor.Identity.Identity a_a8sO
                                                        -> Bool
type family TFHelper_6989586621679139560 @a_a8sO (a_axL4 :: Data.Functor.Identity.Identity a_a8sO) (a_axL5 :: Data.Functor.Identity.Identity a_a8sO) :: Bool where
  TFHelper_6989586621679139560 @a_a8sO ('Data.Functor.Identity.Identity a_6989586621679139554_axL9 :: Data.Functor.Identity.Identity a_a8sO) ('Data.Functor.Identity.Identity b_6989586621679139556_axLa :: Data.Functor.Identity.Identity a_a8sO) = Apply (Apply (==@#@$) a_6989586621679139554_axL9) b_6989586621679139556_axLa
instance PEq (Data.Functor.Identity.Identity a_a8sO) where
  type (==) a_axL0 a_axL1 = TFHelper_6989586621679139560 a_axL0 a_axL1
instance SEq a_a8sO =>
          SEq (Data.Functor.Identity.Identity a_a8sO) where
  (%==)
    (SIdentity (sA_6989586621679139554 :: Sing a_6989586621679139554_axL9))
    (SIdentity (sB_6989586621679139556 :: Sing b_6989586621679139556_axLa))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679139554)
        sB_6989586621679139556
type TFHelper_6989586621679139571 :: Bool -> Bool -> Bool
type family TFHelper_6989586621679139571 (a_axLf :: Bool) (a_axLg :: Bool) :: Bool where
  TFHelper_6989586621679139571 'False 'False = TrueSym0
  TFHelper_6989586621679139571 'False 'True = FalseSym0
  TFHelper_6989586621679139571 'True 'False = FalseSym0
  TFHelper_6989586621679139571 'True 'True = TrueSym0
instance PEq Bool where
  type (==) a_axLb a_axLc = TFHelper_6989586621679139571 a_axLb a_axLc
instance SEq Bool where
  (%==) SFalse SFalse = STrue
  (%==) SFalse STrue = SFalse
  (%==) STrue SFalse = SFalse
  (%==) STrue STrue = STrue
type TFHelper_6989586621679139580 :: Ordering -> Ordering -> Bool
type family TFHelper_6989586621679139580 (a_axLo :: Ordering) (a_axLp :: Ordering) :: Bool where
  TFHelper_6989586621679139580 'LT 'LT = TrueSym0
  TFHelper_6989586621679139580 'LT 'EQ = FalseSym0
  TFHelper_6989586621679139580 'LT 'GT = FalseSym0
  TFHelper_6989586621679139580 'EQ 'LT = FalseSym0
  TFHelper_6989586621679139580 'EQ 'EQ = TrueSym0
  TFHelper_6989586621679139580 'EQ 'GT = FalseSym0
  TFHelper_6989586621679139580 'GT 'LT = FalseSym0
  TFHelper_6989586621679139580 'GT 'EQ = FalseSym0
  TFHelper_6989586621679139580 'GT 'GT = TrueSym0
instance PEq Ordering where
  type (==) a_axLk a_axLl = TFHelper_6989586621679139580 a_axLk a_axLl
instance SEq Ordering where
  (%==) SLT SLT = STrue
  (%==) SLT SEQ = SFalse
  (%==) SLT SGT = SFalse
  (%==) SEQ SLT = SFalse
  (%==) SEQ SEQ = STrue
  (%==) SEQ SGT = SFalse
  (%==) SGT SLT = SFalse
  (%==) SGT SEQ = SFalse
  (%==) SGT SGT = STrue
type TFHelper_6989586621679139589 :: () -> () -> Bool
type family TFHelper_6989586621679139589 (a_axLx :: ()) (a_axLy :: ()) :: Bool where
  TFHelper_6989586621679139589 '() '() = TrueSym0
instance PEq () where
  type (==) a_axLt a_axLu = TFHelper_6989586621679139589 a_axLt a_axLu
instance SEq () where
  (%==) STuple0 STuple0 = STrue

