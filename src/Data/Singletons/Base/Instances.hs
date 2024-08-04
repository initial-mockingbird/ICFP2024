{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -ddump-splices #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
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
{- Data/Singletons/Base/Instances.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu

This (internal) module contains the main class definitions for singletons-base,
re-exported from various places.

-}

module Data.Singletons.Base.Instances (
    module Data.Singletons.Base.Instances
  , Sing
  ) where

import Data.Singletons

import Data.Singletons.TH
import Data.Kind (Type)
import qualified GHC.Base
import qualified Data.Functor.Identity
import qualified Data.Type.Equality
import qualified Data.Type.Coercion
import qualified Data.Singletons.ShowSing
import qualified Data.Singletons.Decide

type NothingSym0 :: forall (a_11 :: Type). Maybe a_11
type family NothingSym0 @(a_11 :: Type) :: Maybe a_11 where
  NothingSym0 = 'Nothing
type JustSym0 :: forall (a_11 :: Type). (~>) a_11 (Maybe a_11)
data JustSym0 :: (~>) a_11 (Maybe a_11)
  where
    JustSym0KindInference :: SameKind (Apply JustSym0 arg_a8dL) (JustSym1 arg_a8dL) =>
                              JustSym0 a6989586621679041398
type instance Apply @a_11 @(Maybe a_11) JustSym0 a6989586621679041398 = 'Just a6989586621679041398
instance SuppressUnusedWarnings JustSym0 where
  suppressUnusedWarnings = snd ((,) JustSym0KindInference ())
type JustSym1 :: forall (a_11 :: Type). a_11 -> Maybe a_11
type family JustSym1 @(a_11 :: Type) (a6989586621679041398 :: a_11) :: Maybe a_11 where
  JustSym1 a6989586621679041398 = 'Just a6989586621679041398
type SMaybe :: forall (a_11 :: Type). Maybe a_11 -> Type
data SMaybe :: forall (a_11 :: Type). Maybe a_11 -> Type
  where
    SNothing :: forall (a_11 :: Type). SMaybe ('Nothing :: Maybe a_11)
    SJust :: forall (a_11 :: Type) (n_a8dN :: a_11).
              (Sing n_a8dN) -> SMaybe ('Just n_a8dN :: Maybe a_11)
type instance Sing @(Maybe a_11) = SMaybe
instance SingKind a_11 => SingKind (Maybe a_11) where
  type Demote (Maybe a_11) = Maybe (Demote a_11)
  fromSing SNothing = Nothing
  fromSing (SJust b_a8dP) = Just (fromSing b_a8dP)
  toSing Nothing = SomeSing SNothing
  toSing (Just (b_a8dR :: Demote a_11))
    = (\cases (SomeSing c_a8dS) -> SomeSing (SJust c_a8dS))
        (toSing b_a8dR :: SomeSing a_11)
instance SingI 'Nothing where
  sing = SNothing
instance SingI n_a8dN => SingI ('Just (n_a8dN :: a_11)) where
  sing = SJust sing
instance SingI1 'Just where
  liftSing = SJust
instance SingI (JustSym0 :: (~>) a_11 (Maybe a_11)) where
  sing = singFun1 @JustSym0 SJust
type NilSym0 :: forall (a_11 :: Type). [a_11]
type family NilSym0 @(a_11 :: Type) :: [a_11] where
  NilSym0 = '[]
type (:@#@$) :: forall (a_11 :: Type). (~>) a_11 ((~>) [a_11] [a_11])
data (:@#@$) :: (~>) a_11 ((~>) [a_11] [a_11])
  where
    (::@#@$###) :: SameKind (Apply (:@#@$) arg_a8e9) ((:@#@$$) arg_a8e9) =>
                    (:@#@$) a6989586621679041422
type instance Apply @a_11 @((~>) [a_11] [a_11]) (:@#@$) a6989586621679041422 = (:@#@$$) a6989586621679041422
instance SuppressUnusedWarnings (:@#@$) where
  suppressUnusedWarnings = snd ((,) (::@#@$###) ())
infixr 5 :@#@$
type (:@#@$$) :: forall (a_11 :: Type). a_11 -> (~>) [a_11] [a_11]
data (:@#@$$) (a6989586621679041422 :: a_11) :: (~>) [a_11] [a_11]
  where
    (::@#@$$###) :: SameKind (Apply ((:@#@$$) a6989586621679041422) arg_a8e9) ((:@#@$$$) a6989586621679041422 arg_a8e9) =>
                    (:@#@$$) a6989586621679041422 a6989586621679041423
type instance Apply @[a_11] @[a_11] ((:@#@$$) a6989586621679041422) a6989586621679041423 = '(:) a6989586621679041422 a6989586621679041423
instance SuppressUnusedWarnings ((:@#@$$) a6989586621679041422) where
  suppressUnusedWarnings = snd ((,) (::@#@$$###) ())
infixr 5 :@#@$$
type (:@#@$$$) :: forall (a_11 :: Type). a_11 -> [a_11] -> [a_11]
type family (:@#@$$$) @(a_11 :: Type) (a6989586621679041422 :: a_11) (a6989586621679041423 :: [a_11]) :: [a_11] where
  (:@#@$$$) a6989586621679041422 a6989586621679041423 = '(:) a6989586621679041422 a6989586621679041423
infixr 5 :@#@$$$
type SList :: forall (a_11 :: Type). [a_11] -> Type
data SList :: forall (a_11 :: Type). [a_11] -> Type
  where
    SNil :: forall (a_11 :: Type). SList ('[] :: [a_11])
    SCons :: forall (a_11 :: Type) (n_a8ec :: a_11) (n_a8ed :: [a_11]).
              (Sing n_a8ec) ->
              (Sing n_a8ed) ->
              SList ('(:) n_a8ec n_a8ed :: [a_11])
type instance Sing @[a_11] = SList
instance SingKind a_11 => SingKind [a_11] where
  type Demote [a_11] = [Demote a_11]
  fromSing SNil = []
  fromSing (SCons b_a8eh b_a8ei)
    = (:) (fromSing b_a8eh) (fromSing b_a8ei)
  toSing [] = SomeSing SNil
  toSing ((:) (b_a8ek :: Demote a_11) (b_a8el :: Demote [a_11]))
    = (\cases
          (SomeSing c_a8em) (SomeSing c_a8en)
            -> SomeSing (SCons c_a8em c_a8en))
        (toSing b_a8ek :: SomeSing a_11) (toSing b_a8el :: SomeSing [a_11])
infixr 5 `SCons`
instance SingI '[] where
  sing = SNil
instance (SingI n_a8ec, SingI n_a8ed) =>
          SingI ('(:) (n_a8ec :: a_11) (n_a8ed :: [a_11])) where
  sing = SCons sing sing
instance SingI n_a8ec => SingI1 ('(:) (n_a8ec :: a_11)) where
  liftSing = SCons sing
instance SingI2 '(:) where
  liftSing2 = SCons
instance SingI ((:@#@$) :: (~>) a_11 ((~>) [a_11] [a_11])) where
  sing = singFun2 @(:@#@$) SCons
instance SingI d_a8ee =>
          SingI ((:@#@$$) (d_a8ee :: a_11) :: (~>) [a_11] [a_11]) where
  sing = singFun1 @((:@#@$$) (d_a8ee :: a_11)) (SCons (sing @d_a8ee))
instance SingI1 ((:@#@$$) :: a_11 -> (~>) [a_11] [a_11]) where
  liftSing (s_a8eg :: Sing (d_a8ee :: a_11))
    = singFun1 @((:@#@$$) (d_a8ee :: a_11)) (SCons s_a8eg)
type LeftSym0 :: forall (a_a8ep :: Type)
                        (b_a8eq :: Type). (~>) a_a8ep (Either a_a8ep b_a8eq)
data LeftSym0 :: (~>) a_a8ep (Either a_a8ep b_a8eq)
  where
    LeftSym0KindInference :: SameKind (Apply LeftSym0 arg_a8eV) (LeftSym1 arg_a8eV) =>
                              LeftSym0 a6989586621679041470
type instance Apply @a_a8ep @(Either a_a8ep b_a8eq) LeftSym0 a6989586621679041470 = 'Left a6989586621679041470
instance SuppressUnusedWarnings LeftSym0 where
  suppressUnusedWarnings = snd ((,) LeftSym0KindInference ())
type LeftSym1 :: forall (a_a8ep :: Type) (b_a8eq :: Type). a_a8ep
                                                            -> Either a_a8ep b_a8eq
type family LeftSym1 @(a_a8ep :: Type) @(b_a8eq :: Type) (a6989586621679041470 :: a_a8ep) :: Either a_a8ep b_a8eq where
  LeftSym1 a6989586621679041470 = 'Left a6989586621679041470
type RightSym0 :: forall (a_a8ep :: Type)
                          (b_a8eq :: Type). (~>) b_a8eq (Either a_a8ep b_a8eq)
data RightSym0 :: (~>) b_a8eq (Either a_a8ep b_a8eq)
  where
    RightSym0KindInference :: SameKind (Apply RightSym0 arg_a8eX) (RightSym1 arg_a8eX) =>
                              RightSym0 a6989586621679041472
type instance Apply @b_a8eq @(Either a_a8ep b_a8eq) RightSym0 a6989586621679041472 = 'Right a6989586621679041472
instance SuppressUnusedWarnings RightSym0 where
  suppressUnusedWarnings = snd ((,) RightSym0KindInference ())
type RightSym1 :: forall (a_a8ep :: Type) (b_a8eq :: Type). b_a8eq
                                                            -> Either a_a8ep b_a8eq
type family RightSym1 @(a_a8ep :: Type) @(b_a8eq :: Type) (a6989586621679041472 :: b_a8eq) :: Either a_a8ep b_a8eq where
  RightSym1 a6989586621679041472 = 'Right a6989586621679041472
type SEither :: forall (a_a8ep :: Type)
                        (b_a8eq :: Type). Either a_a8ep b_a8eq -> Type
data SEither :: forall (a_a8ep :: Type) (b_a8eq :: Type).
                Either a_a8ep b_a8eq -> Type
  where
    SLeft :: forall (a_a8ep :: Type)
                    (b_a8eq :: Type)
                    (n_a8eZ :: a_a8ep).
              (Sing n_a8eZ) -> SEither ('Left n_a8eZ :: Either a_a8ep b_a8eq)
    SRight :: forall (a_a8ep :: Type)
                      (b_a8eq :: Type)
                      (n_a8f1 :: b_a8eq).
              (Sing n_a8f1) -> SEither ('Right n_a8f1 :: Either a_a8ep b_a8eq)
type instance Sing @(Either a_a8ep b_a8eq) = SEither
instance (SingKind a_a8ep, SingKind b_a8eq) =>
          SingKind (Either a_a8ep b_a8eq) where
  type Demote (Either a_a8ep b_a8eq) = Either (Demote a_a8ep) (Demote b_a8eq)
  fromSing (SLeft b_a8f3) = Left (fromSing b_a8f3)
  fromSing (SRight b_a8f4) = Right (fromSing b_a8f4)
  toSing (Left (b_a8f6 :: Demote a_a8ep))
    = (\cases (SomeSing c_a8f7) -> SomeSing (SLeft c_a8f7))
        (toSing b_a8f6 :: SomeSing a_a8ep)
  toSing (Right (b_a8f8 :: Demote b_a8eq))
    = (\cases (SomeSing c_a8f9) -> SomeSing (SRight c_a8f9))
        (toSing b_a8f8 :: SomeSing b_a8eq)
instance SingI n_a8eZ => SingI ('Left (n_a8eZ :: a_a8ep)) where
  sing = SLeft sing
instance SingI1 'Left where
  liftSing = SLeft
instance SingI (LeftSym0 :: (~>) a_a8ep (Either a_a8ep b_a8eq)) where
  sing = singFun1 @LeftSym0 SLeft
instance SingI n_a8f1 => SingI ('Right (n_a8f1 :: b_a8eq)) where
  sing = SRight sing
instance SingI1 'Right where
  liftSing = SRight
instance SingI (RightSym0 :: (~>) b_a8eq (Either a_a8ep b_a8eq)) where
  sing = singFun1 @RightSym0 SRight
type (:|@#@$) :: forall (a_a8fb :: Type). (~>) a_a8fb ((~>) [a_a8fb] (GHC.Base.NonEmpty a_a8fb))
data (:|@#@$) :: (~>) a_a8fb ((~>) [a_a8fb] (GHC.Base.NonEmpty a_a8fb))
  where
    (::|@#@$###) :: SameKind (Apply (:|@#@$) arg_a8fk) ((:|@#@$$) arg_a8fk) =>
                    (:|@#@$) a6989586621679041495
type instance Apply @a_a8fb @((~>) [a_a8fb] (GHC.Base.NonEmpty a_a8fb)) (:|@#@$) a6989586621679041495 = (:|@#@$$) a6989586621679041495
instance SuppressUnusedWarnings (:|@#@$) where
  suppressUnusedWarnings = snd ((,) (::|@#@$###) ())
infixr 5 :|@#@$
type (:|@#@$$) :: forall (a_a8fb :: Type). a_a8fb
                                            -> (~>) [a_a8fb] (GHC.Base.NonEmpty a_a8fb)
data (:|@#@$$) (a6989586621679041495 :: a_a8fb) :: (~>) [a_a8fb] (GHC.Base.NonEmpty a_a8fb)
  where
    (::|@#@$$###) :: SameKind (Apply ((:|@#@$$) a6989586621679041495) arg_a8fk) ((:|@#@$$$) a6989586621679041495 arg_a8fk) =>
                      (:|@#@$$) a6989586621679041495 a6989586621679041496
type instance Apply @[a_a8fb] @(GHC.Base.NonEmpty a_a8fb) ((:|@#@$$) a6989586621679041495) a6989586621679041496 = '(GHC.Base.:|) a6989586621679041495 a6989586621679041496
instance SuppressUnusedWarnings ((:|@#@$$) a6989586621679041495) where
  suppressUnusedWarnings = snd ((,) (::|@#@$$###) ())
infixr 5 :|@#@$$
type (:|@#@$$$) :: forall (a_a8fb :: Type). a_a8fb
                                            -> [a_a8fb] -> GHC.Base.NonEmpty a_a8fb
type family (:|@#@$$$) @(a_a8fb :: Type) (a6989586621679041495 :: a_a8fb) (a6989586621679041496 :: [a_a8fb]) :: GHC.Base.NonEmpty a_a8fb where
  (:|@#@$$$) a6989586621679041495 a6989586621679041496 = '(GHC.Base.:|) a6989586621679041495 a6989586621679041496
infixr 5 :|@#@$$$
type SNonEmpty :: forall (a_a8fb :: Type). GHC.Base.NonEmpty a_a8fb
                                            -> Type
data SNonEmpty :: forall (a_a8fb :: Type).
                  GHC.Base.NonEmpty a_a8fb -> Type
  where
    (:%|) :: forall (a_a8fb :: Type)
                    (n_a8fn :: a_a8fb)
                    (n_a8fo :: [a_a8fb]).
              (Sing n_a8fn) ->
              (Sing n_a8fo) ->
              SNonEmpty ('(GHC.Base.:|) n_a8fn n_a8fo :: GHC.Base.NonEmpty a_a8fb)
type instance Sing @(GHC.Base.NonEmpty a_a8fb) = SNonEmpty
instance SingKind a_a8fb =>
          SingKind (GHC.Base.NonEmpty a_a8fb) where
  type Demote (GHC.Base.NonEmpty a_a8fb) = GHC.Base.NonEmpty (Demote a_a8fb)
  fromSing ((:%|) b_a8fs b_a8ft)
    = (GHC.Base.:|) (fromSing b_a8fs) (fromSing b_a8ft)
  toSing
    ((GHC.Base.:|) (b_a8fv :: Demote a_a8fb)
                    (b_a8fw :: Demote [a_a8fb]))
    = (\cases
          (SomeSing c_a8fx) (SomeSing c_a8fy)
            -> SomeSing ((:%|) c_a8fx c_a8fy))
        (toSing b_a8fv :: SomeSing a_a8fb)
        (toSing b_a8fw :: SomeSing [a_a8fb])
infixr 5 :%|
instance (SingI n_a8fn, SingI n_a8fo) =>
          SingI ('(GHC.Base.:|) (n_a8fn :: a_a8fb) (n_a8fo :: [a_a8fb])) where
  sing = (:%|) sing sing
instance SingI n_a8fn =>
          SingI1 ('(GHC.Base.:|) (n_a8fn :: a_a8fb)) where
  liftSing = (:%|) sing
instance SingI2 '(GHC.Base.:|) where
  liftSing2 = (:%|)
instance SingI ((:|@#@$) :: (~>) a_a8fb ((~>) [a_a8fb] (GHC.Base.NonEmpty a_a8fb))) where
  sing = singFun2 @(:|@#@$) (:%|)
instance SingI d_a8fp =>
          SingI ((:|@#@$$) (d_a8fp :: a_a8fb) :: (~>) [a_a8fb] (GHC.Base.NonEmpty a_a8fb)) where
  sing
    = singFun1 @((:|@#@$$) (d_a8fp :: a_a8fb)) ((:%|) (sing @d_a8fp))
instance SingI1 ((:|@#@$$) :: a_a8fb
                              -> (~>) [a_a8fb] (GHC.Base.NonEmpty a_a8fb)) where
  liftSing (s_a8fr :: Sing (d_a8fp :: a_a8fb))
    = singFun1 @((:|@#@$$) (d_a8fp :: a_a8fb)) ((:%|) s_a8fr)
type SVoid :: Void -> Type
data SVoid :: Void -> Type
type instance Sing @Void = SVoid
instance SingKind Void where
  type Demote Void = Void
  fromSing x_a8fA = (\case) x_a8fA
  toSing x_a8fB = SomeSing ((\case) x_a8fB)
type Tuple2Sym0 :: forall (a_11 :: Type)
                          (b_12 :: Type). (~>) a_11 ((~>) b_12 (a_11, b_12))
data Tuple2Sym0 :: (~>) a_11 ((~>) b_12 (a_11, b_12))
  where
    Tuple2Sym0KindInference :: SameKind (Apply Tuple2Sym0 arg_a8m6) (Tuple2Sym1 arg_a8m6) =>
                                Tuple2Sym0 a6989586621679041915
type instance Apply @a_11 @((~>) b_12 (a_11,
                                        b_12)) Tuple2Sym0 a6989586621679041915 = Tuple2Sym1 a6989586621679041915
instance SuppressUnusedWarnings Tuple2Sym0 where
  suppressUnusedWarnings = snd ((,) Tuple2Sym0KindInference ())
type Tuple2Sym1 :: forall (a_11 :: Type) (b_12 :: Type). a_11
                                                          -> (~>) b_12 (a_11, b_12)
data Tuple2Sym1 (a6989586621679041915 :: a_11) :: (~>) b_12 (a_11,
                                                              b_12)
  where
    Tuple2Sym1KindInference :: SameKind (Apply (Tuple2Sym1 a6989586621679041915) arg_a8m6) (Tuple2Sym2 a6989586621679041915 arg_a8m6) =>
                                Tuple2Sym1 a6989586621679041915 a6989586621679041916
type instance Apply @b_12 @(a_11,
                            b_12) (Tuple2Sym1 a6989586621679041915) a6989586621679041916 = '(a6989586621679041915,
                                                                                              a6989586621679041916)
instance SuppressUnusedWarnings (Tuple2Sym1 a6989586621679041915) where
  suppressUnusedWarnings = snd ((,) Tuple2Sym1KindInference ())
type Tuple2Sym2 :: forall (a_11 :: Type) (b_12 :: Type). a_11
                                                          -> b_12 -> (a_11, b_12)
type family Tuple2Sym2 @(a_11 :: Type) @(b_12 :: Type) (a6989586621679041915 :: a_11) (a6989586621679041916 :: b_12) :: (a_11,
                                                                                                                          b_12) where
  Tuple2Sym2 a6989586621679041915 a6989586621679041916 = '(a6989586621679041915,
                                                            a6989586621679041916)
type STuple2 :: forall (a_11 :: Type) (b_12 :: Type). (a_11, b_12)
                                                      -> Type
data STuple2 :: forall (a_11 :: Type) (b_12 :: Type).
                (a_11, b_12) -> Type
  where
    STuple2 :: forall (a_11 :: Type)
                      (b_12 :: Type)
                      (n_a8m9 :: a_11)
                      (n_a8ma :: b_12).
                (Sing n_a8m9) ->
                (Sing n_a8ma) ->
                STuple2 ('(n_a8m9, n_a8ma) :: (a_11, b_12))
type instance Sing @(a_11, b_12) = STuple2
instance (SingKind a_11, SingKind b_12) =>
          SingKind (a_11, b_12) where
  type Demote (a_11, b_12) = (Demote a_11, Demote b_12)
  fromSing (STuple2 b_a8me b_a8mf)
    = (,) (fromSing b_a8me) (fromSing b_a8mf)
  toSing ((,) (b_a8mh :: Demote a_11) (b_a8mi :: Demote b_12))
    = (\cases
          (SomeSing c_a8mj) (SomeSing c_a8mk)
            -> SomeSing (STuple2 c_a8mj c_a8mk))
        (toSing b_a8mh :: SomeSing a_11) (toSing b_a8mi :: SomeSing b_12)
instance (SingI n_a8m9, SingI n_a8ma) =>
          SingI '(n_a8m9 :: a_11, n_a8ma :: b_12) where
  sing = STuple2 sing sing
instance SingI n_a8m9 => SingI1 ('(,) (n_a8m9 :: a_11)) where
  liftSing = STuple2 sing
instance SingI2 '(,) where
  liftSing2 = STuple2
instance SingI (Tuple2Sym0 :: (~>) a_11 ((~>) b_12 (a_11,
                                                    b_12))) where
  sing = singFun2 @Tuple2Sym0 STuple2
instance SingI d_a8mb =>
          SingI (Tuple2Sym1 (d_a8mb :: a_11) :: (~>) b_12 (a_11, b_12)) where
  sing
    = singFun1 @(Tuple2Sym1 (d_a8mb :: a_11)) (STuple2 (sing @d_a8mb))
instance SingI1 (Tuple2Sym1 :: a_11
                                -> (~>) b_12 (a_11, b_12)) where
  liftSing (s_a8md :: Sing (d_a8mb :: a_11))
    = singFun1 @(Tuple2Sym1 (d_a8mb :: a_11)) (STuple2 s_a8md)
type Tuple3Sym0 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type). (~>) a_11 ((~>) b_12 ((~>) c_13 (a_11, b_12,
                                                                            c_13)))
data Tuple3Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 (a_11, b_12,
                                                    c_13)))
  where
    Tuple3Sym0KindInference :: SameKind (Apply Tuple3Sym0 arg_a8mB) (Tuple3Sym1 arg_a8mB) =>
                                Tuple3Sym0 a6989586621679041946
type instance Apply @a_11 @((~>) b_12 ((~>) c_13 (a_11, b_12,
                                                  c_13))) Tuple3Sym0 a6989586621679041946 = Tuple3Sym1 a6989586621679041946
instance SuppressUnusedWarnings Tuple3Sym0 where
  suppressUnusedWarnings = snd ((,) Tuple3Sym0KindInference ())
type Tuple3Sym1 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type). a_11 -> (~>) b_12 ((~>) c_13 (a_11, b_12, c_13))
data Tuple3Sym1 (a6989586621679041946 :: a_11) :: (~>) b_12 ((~>) c_13 (a_11,
                                                                        b_12, c_13))
  where
    Tuple3Sym1KindInference :: SameKind (Apply (Tuple3Sym1 a6989586621679041946) arg_a8mB) (Tuple3Sym2 a6989586621679041946 arg_a8mB) =>
                                Tuple3Sym1 a6989586621679041946 a6989586621679041947
type instance Apply @b_12 @((~>) c_13 (a_11, b_12,
                                        c_13)) (Tuple3Sym1 a6989586621679041946) a6989586621679041947 = Tuple3Sym2 a6989586621679041946 a6989586621679041947
instance SuppressUnusedWarnings (Tuple3Sym1 a6989586621679041946) where
  suppressUnusedWarnings = snd ((,) Tuple3Sym1KindInference ())
type Tuple3Sym2 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type). a_11 -> b_12 -> (~>) c_13 (a_11, b_12, c_13)
data Tuple3Sym2 (a6989586621679041946 :: a_11) (a6989586621679041947 :: b_12) :: (~>) c_13 (a_11,
                                                                                            b_12,
                                                                                            c_13)
  where
    Tuple3Sym2KindInference :: SameKind (Apply (Tuple3Sym2 a6989586621679041946 a6989586621679041947) arg_a8mB) (Tuple3Sym3 a6989586621679041946 a6989586621679041947 arg_a8mB) =>
                                Tuple3Sym2 a6989586621679041946 a6989586621679041947 a6989586621679041948
type instance Apply @c_13 @(a_11, b_12,
                            c_13) (Tuple3Sym2 a6989586621679041946 a6989586621679041947) a6989586621679041948 = '(a6989586621679041946,
                                                                                                                  a6989586621679041947,
                                                                                                                  a6989586621679041948)
instance SuppressUnusedWarnings (Tuple3Sym2 a6989586621679041946 a6989586621679041947) where
  suppressUnusedWarnings = snd ((,) Tuple3Sym2KindInference ())
type Tuple3Sym3 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type). a_11 -> b_12 -> c_13 -> (a_11, b_12, c_13)
type family Tuple3Sym3 @(a_11 :: Type) @(b_12 :: Type) @(c_13 :: Type) (a6989586621679041946 :: a_11) (a6989586621679041947 :: b_12) (a6989586621679041948 :: c_13) :: (a_11,
                                                                                                                                                                        b_12,
                                                                                                                                                                        c_13) where
  Tuple3Sym3 a6989586621679041946 a6989586621679041947 a6989586621679041948 = '(a6989586621679041946,
                                                                                a6989586621679041947,
                                                                                a6989586621679041948)
type STuple3 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type). (a_11, b_12, c_13) -> Type
data STuple3 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type).
                (a_11, b_12, c_13) -> Type
  where
    STuple3 :: forall (a_11 :: Type)
                      (b_12 :: Type)
                      (c_13 :: Type)
                      (n_a8mF :: a_11)
                      (n_a8mG :: b_12)
                      (n_a8mH :: c_13).
                (Sing n_a8mF) ->
                (Sing n_a8mG) ->
                (Sing n_a8mH) ->
                STuple3 ('(n_a8mF, n_a8mG, n_a8mH) :: (a_11, b_12, c_13))
type instance Sing @(a_11, b_12, c_13) = STuple3
instance (SingKind a_11, SingKind b_12, SingKind c_13) =>
          SingKind (a_11, b_12, c_13) where
  type Demote (a_11, b_12, c_13) = (Demote a_11, Demote b_12,
                                    Demote c_13)
  fromSing (STuple3 b_a8mP b_a8mQ b_a8mR)
    = (,,) (fromSing b_a8mP) (fromSing b_a8mQ) (fromSing b_a8mR)
  toSing
    ((,,) (b_a8mT :: Demote a_11) (b_a8mU :: Demote b_12)
          (b_a8mV :: Demote c_13))
    = (\cases
          (SomeSing c_a8mW) (SomeSing c_a8mX) (SomeSing c_a8mY)
            -> SomeSing (STuple3 c_a8mW c_a8mX c_a8mY))
        (toSing b_a8mT :: SomeSing a_11) (toSing b_a8mU :: SomeSing b_12)
        (toSing b_a8mV :: SomeSing c_13)
instance (SingI n_a8mF, SingI n_a8mG, SingI n_a8mH) =>
          SingI '(n_a8mF :: a_11, n_a8mG :: b_12, n_a8mH :: c_13) where
  sing = STuple3 sing sing sing
instance (SingI n_a8mF, SingI n_a8mG) =>
          SingI1 ('(,,) (n_a8mF :: a_11) (n_a8mG :: b_12)) where
  liftSing = STuple3 sing sing
instance SingI n_a8mF => SingI2 ('(,,) (n_a8mF :: a_11)) where
  liftSing2 = STuple3 sing
instance SingI (Tuple3Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 (a_11,
                                                                b_12, c_13)))) where
  sing = singFun3 @Tuple3Sym0 STuple3
instance SingI d_a8mI =>
          SingI (Tuple3Sym1 (d_a8mI :: a_11) :: (~>) b_12 ((~>) c_13 (a_11,
                                                                      b_12, c_13))) where
  sing
    = singFun2 @(Tuple3Sym1 (d_a8mI :: a_11)) (STuple3 (sing @d_a8mI))
instance SingI1 (Tuple3Sym1 :: a_11
                                -> (~>) b_12 ((~>) c_13 (a_11, b_12, c_13))) where
  liftSing (s_a8mO :: Sing (d_a8mI :: a_11))
    = singFun2 @(Tuple3Sym1 (d_a8mI :: a_11)) (STuple3 s_a8mO)
instance (SingI d_a8mI, SingI d_a8mJ) =>
          SingI (Tuple3Sym2 (d_a8mI :: a_11) (d_a8mJ :: b_12) :: (~>) c_13 (a_11,
                                                                            b_12, c_13)) where
  sing
    = singFun1
        @(Tuple3Sym2 (d_a8mI :: a_11) (d_a8mJ :: b_12))
        (STuple3 (sing @d_a8mI) (sing @d_a8mJ))
instance SingI d_a8mI =>
          SingI1 (Tuple3Sym2 (d_a8mI :: a_11) :: b_12
                                                -> (~>) c_13 (a_11, b_12, c_13)) where
  liftSing (s_a8mL :: Sing (d_a8mJ :: b_12))
    = singFun1
        @(Tuple3Sym2 (d_a8mI :: a_11) (d_a8mJ :: b_12))
        (STuple3 (sing @d_a8mI) s_a8mL)
instance SingI2 (Tuple3Sym2 :: a_11
                                -> b_12 -> (~>) c_13 (a_11, b_12, c_13)) where
  liftSing2
    (s_a8mM :: Sing (d_a8mI :: a_11))
    (s_a8mN :: Sing (d_a8mJ :: b_12))
    = singFun1
        @(Tuple3Sym2 (d_a8mI :: a_11) (d_a8mJ :: b_12))
        (STuple3 s_a8mM s_a8mN)
type Tuple4Sym0 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type). (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 (a_11,
                                                                                      b_12,
                                                                                      c_13,
                                                                                      d_14))))
data Tuple4Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 (a_11,
                                                                b_12, c_13, d_14))))
  where
    Tuple4Sym0KindInference :: SameKind (Apply Tuple4Sym0 arg_a8no) (Tuple4Sym1 arg_a8no) =>
                                Tuple4Sym0 a6989586621679041995
type instance Apply @a_11 @((~>) b_12 ((~>) c_13 ((~>) d_14 (a_11,
                                                              b_12, c_13,
                                                              d_14)))) Tuple4Sym0 a6989586621679041995 = Tuple4Sym1 a6989586621679041995
instance SuppressUnusedWarnings Tuple4Sym0 where
  suppressUnusedWarnings = snd ((,) Tuple4Sym0KindInference ())
type Tuple4Sym1 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type). a_11
                                          -> (~>) b_12 ((~>) c_13 ((~>) d_14 (a_11, b_12, c_13,
                                                                              d_14)))
data Tuple4Sym1 (a6989586621679041995 :: a_11) :: (~>) b_12 ((~>) c_13 ((~>) d_14 (a_11,
                                                                                    b_12, c_13,
                                                                                    d_14)))
  where
    Tuple4Sym1KindInference :: SameKind (Apply (Tuple4Sym1 a6989586621679041995) arg_a8no) (Tuple4Sym2 a6989586621679041995 arg_a8no) =>
                                Tuple4Sym1 a6989586621679041995 a6989586621679041996
type instance Apply @b_12 @((~>) c_13 ((~>) d_14 (a_11, b_12, c_13,
                                                  d_14))) (Tuple4Sym1 a6989586621679041995) a6989586621679041996 = Tuple4Sym2 a6989586621679041995 a6989586621679041996
instance SuppressUnusedWarnings (Tuple4Sym1 a6989586621679041995) where
  suppressUnusedWarnings = snd ((,) Tuple4Sym1KindInference ())
type Tuple4Sym2 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type). a_11
                                          -> b_12
                                              -> (~>) c_13 ((~>) d_14 (a_11, b_12, c_13, d_14))
data Tuple4Sym2 (a6989586621679041995 :: a_11) (a6989586621679041996 :: b_12) :: (~>) c_13 ((~>) d_14 (a_11,
                                                                                                        b_12,
                                                                                                        c_13,
                                                                                                        d_14))
  where
    Tuple4Sym2KindInference :: SameKind (Apply (Tuple4Sym2 a6989586621679041995 a6989586621679041996) arg_a8no) (Tuple4Sym3 a6989586621679041995 a6989586621679041996 arg_a8no) =>
                                Tuple4Sym2 a6989586621679041995 a6989586621679041996 a6989586621679041997
type instance Apply @c_13 @((~>) d_14 (a_11, b_12, c_13,
                                        d_14)) (Tuple4Sym2 a6989586621679041995 a6989586621679041996) a6989586621679041997 = Tuple4Sym3 a6989586621679041995 a6989586621679041996 a6989586621679041997
instance SuppressUnusedWarnings (Tuple4Sym2 a6989586621679041995 a6989586621679041996) where
  suppressUnusedWarnings = snd ((,) Tuple4Sym2KindInference ())
type Tuple4Sym3 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type). a_11
                                          -> b_12 -> c_13 -> (~>) d_14 (a_11, b_12, c_13, d_14)
data Tuple4Sym3 (a6989586621679041995 :: a_11) (a6989586621679041996 :: b_12) (a6989586621679041997 :: c_13) :: (~>) d_14 (a_11,
                                                                                                                            b_12,
                                                                                                                            c_13,
                                                                                                                            d_14)
  where
    Tuple4Sym3KindInference :: SameKind (Apply (Tuple4Sym3 a6989586621679041995 a6989586621679041996 a6989586621679041997) arg_a8no) (Tuple4Sym4 a6989586621679041995 a6989586621679041996 a6989586621679041997 arg_a8no) =>
                                Tuple4Sym3 a6989586621679041995 a6989586621679041996 a6989586621679041997 a6989586621679041998
type instance Apply @d_14 @(a_11, b_12, c_13,
                            d_14) (Tuple4Sym3 a6989586621679041995 a6989586621679041996 a6989586621679041997) a6989586621679041998 = '(a6989586621679041995,
                                                                                                                                        a6989586621679041996,
                                                                                                                                        a6989586621679041997,
                                                                                                                                        a6989586621679041998)
instance SuppressUnusedWarnings (Tuple4Sym3 a6989586621679041995 a6989586621679041996 a6989586621679041997) where
  suppressUnusedWarnings = snd ((,) Tuple4Sym3KindInference ())
type Tuple4Sym4 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type). a_11
                                          -> b_12 -> c_13 -> d_14 -> (a_11, b_12, c_13, d_14)
type family Tuple4Sym4 @(a_11 :: Type) @(b_12 :: Type) @(c_13 :: Type) @(d_14 :: Type) (a6989586621679041995 :: a_11) (a6989586621679041996 :: b_12) (a6989586621679041997 :: c_13) (a6989586621679041998 :: d_14) :: (a_11,
                                                                                                                                                                                                                        b_12,
                                                                                                                                                                                                                        c_13,
                                                                                                                                                                                                                        d_14) where
  Tuple4Sym4 a6989586621679041995 a6989586621679041996 a6989586621679041997 a6989586621679041998 = '(a6989586621679041995,
                                                                                                      a6989586621679041996,
                                                                                                      a6989586621679041997,
                                                                                                      a6989586621679041998)
type STuple4 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type)
                        (d_14 :: Type). (a_11, b_12, c_13, d_14) -> Type
data STuple4 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type)
                        (d_14 :: Type).
                (a_11, b_12, c_13, d_14) -> Type
  where
    STuple4 :: forall (a_11 :: Type)
                      (b_12 :: Type)
                      (c_13 :: Type)
                      (d_14 :: Type)
                      (n_a8nt :: a_11)
                      (n_a8nu :: b_12)
                      (n_a8nv :: c_13)
                      (n_a8nw :: d_14).
                (Sing n_a8nt) ->
                (Sing n_a8nu) ->
                (Sing n_a8nv) ->
                (Sing n_a8nw) ->
                STuple4 ('(n_a8nt, n_a8nu, n_a8nv, n_a8nw) :: (a_11, b_12, c_13,
                                                              d_14))
type instance Sing @(a_11, b_12, c_13, d_14) = STuple4
instance (SingKind a_11,
          SingKind b_12,
          SingKind c_13,
          SingKind d_14) =>
          SingKind (a_11, b_12, c_13, d_14) where
  type Demote (a_11, b_12, c_13, d_14) = (Demote a_11, Demote b_12,
                                          Demote c_13, Demote d_14)
  fromSing (STuple4 b_a8nI b_a8nJ b_a8nK b_a8nL)
    = (,,,)
        (fromSing b_a8nI) (fromSing b_a8nJ) (fromSing b_a8nK)
        (fromSing b_a8nL)
  toSing
    ((,,,) (b_a8nN :: Demote a_11) (b_a8nO :: Demote b_12)
            (b_a8nP :: Demote c_13) (b_a8nQ :: Demote d_14))
    = (\cases
          (SomeSing c_a8nR)
            (SomeSing c_a8nS)
            (SomeSing c_a8nT)
            (SomeSing c_a8nU)
            -> SomeSing (STuple4 c_a8nR c_a8nS c_a8nT c_a8nU))
        (toSing b_a8nN :: SomeSing a_11) (toSing b_a8nO :: SomeSing b_12)
        (toSing b_a8nP :: SomeSing c_13) (toSing b_a8nQ :: SomeSing d_14)
instance (SingI n_a8nt,
          SingI n_a8nu,
          SingI n_a8nv,
          SingI n_a8nw) =>
          SingI '(n_a8nt :: a_11,
                  n_a8nu :: b_12,
                  n_a8nv :: c_13,
                  n_a8nw :: d_14) where
  sing = STuple4 sing sing sing sing
instance (SingI n_a8nt, SingI n_a8nu, SingI n_a8nv) =>
          SingI1 ('(,,,) (n_a8nt :: a_11) (n_a8nu :: b_12) (n_a8nv :: c_13)) where
  liftSing = STuple4 sing sing sing
instance (SingI n_a8nt, SingI n_a8nu) =>
          SingI2 ('(,,,) (n_a8nt :: a_11) (n_a8nu :: b_12)) where
  liftSing2 = STuple4 sing sing
instance SingI (Tuple4Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 (a_11,
                                                                          b_12, c_13,
                                                                          d_14))))) where
  sing = singFun4 @Tuple4Sym0 STuple4
instance SingI d_a8nx =>
          SingI (Tuple4Sym1 (d_a8nx :: a_11) :: (~>) b_12 ((~>) c_13 ((~>) d_14 (a_11,
                                                                                b_12, c_13,
                                                                                d_14)))) where
  sing
    = singFun3 @(Tuple4Sym1 (d_a8nx :: a_11)) (STuple4 (sing @d_a8nx))
instance SingI1 (Tuple4Sym1 :: a_11
                                -> (~>) b_12 ((~>) c_13 ((~>) d_14 (a_11, b_12, c_13,
                                                                    d_14)))) where
  liftSing (s_a8nH :: Sing (d_a8nx :: a_11))
    = singFun3 @(Tuple4Sym1 (d_a8nx :: a_11)) (STuple4 s_a8nH)
instance (SingI d_a8nx, SingI d_a8ny) =>
          SingI (Tuple4Sym2 (d_a8nx :: a_11) (d_a8ny :: b_12) :: (~>) c_13 ((~>) d_14 (a_11,
                                                                                      b_12,
                                                                                      c_13,
                                                                                      d_14))) where
  sing
    = singFun2
        @(Tuple4Sym2 (d_a8nx :: a_11) (d_a8ny :: b_12))
        (STuple4 (sing @d_a8nx) (sing @d_a8ny))
instance SingI d_a8nx =>
          SingI1 (Tuple4Sym2 (d_a8nx :: a_11) :: b_12
                                                -> (~>) c_13 ((~>) d_14 (a_11, b_12, c_13,
                                                                          d_14))) where
  liftSing (s_a8nE :: Sing (d_a8ny :: b_12))
    = singFun2
        @(Tuple4Sym2 (d_a8nx :: a_11) (d_a8ny :: b_12))
        (STuple4 (sing @d_a8nx) s_a8nE)
instance SingI2 (Tuple4Sym2 :: a_11
                                -> b_12 -> (~>) c_13 ((~>) d_14 (a_11, b_12, c_13, d_14))) where
  liftSing2
    (s_a8nF :: Sing (d_a8nx :: a_11))
    (s_a8nG :: Sing (d_a8ny :: b_12))
    = singFun2
        @(Tuple4Sym2 (d_a8nx :: a_11) (d_a8ny :: b_12))
        (STuple4 s_a8nF s_a8nG)
instance (SingI d_a8nx, SingI d_a8ny, SingI d_a8nz) =>
          SingI (Tuple4Sym3 (d_a8nx :: a_11) (d_a8ny :: b_12) (d_a8nz :: c_13) :: (~>) d_14 (a_11,
                                                                                            b_12,
                                                                                            c_13,
                                                                                            d_14)) where
  sing
    = singFun1
        @(Tuple4Sym3 (d_a8nx :: a_11) (d_a8ny :: b_12) (d_a8nz :: c_13))
        (STuple4 (sing @d_a8nx) (sing @d_a8ny) (sing @d_a8nz))
instance (SingI d_a8nx, SingI d_a8ny) =>
          SingI1 (Tuple4Sym3 (d_a8nx :: a_11) (d_a8ny :: b_12) :: c_13
                                                                  -> (~>) d_14 (a_11, b_12, c_13,
                                                                                d_14)) where
  liftSing (s_a8nB :: Sing (d_a8nz :: c_13))
    = singFun1
        @(Tuple4Sym3 (d_a8nx :: a_11) (d_a8ny :: b_12) (d_a8nz :: c_13))
        (STuple4 (sing @d_a8nx) (sing @d_a8ny) s_a8nB)
instance SingI d_a8nx =>
          SingI2 (Tuple4Sym3 (d_a8nx :: a_11) :: b_12
                                                -> c_13
                                                    -> (~>) d_14 (a_11, b_12, c_13, d_14)) where
  liftSing2
    (s_a8nC :: Sing (d_a8ny :: b_12))
    (s_a8nD :: Sing (d_a8nz :: c_13))
    = singFun1
        @(Tuple4Sym3 (d_a8nx :: a_11) (d_a8ny :: b_12) (d_a8nz :: c_13))
        (STuple4 (sing @d_a8nx) s_a8nC s_a8nD)
type Tuple5Sym0 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type). (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                                                                  b_12,
                                                                                                  c_13,
                                                                                                  d_14,
                                                                                                  e_15)))))
data Tuple5Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                                          b_12, c_13, d_14,
                                                                          e_15)))))
  where
    Tuple5Sym0KindInference :: SameKind (Apply Tuple5Sym0 arg_a8ov) (Tuple5Sym1 arg_a8ov) =>
                                Tuple5Sym0 a6989586621679042064
type instance Apply @a_11 @((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                                        b_12, c_13, d_14,
                                                                        e_15))))) Tuple5Sym0 a6989586621679042064 = Tuple5Sym1 a6989586621679042064
instance SuppressUnusedWarnings Tuple5Sym0 where
  suppressUnusedWarnings = snd ((,) Tuple5Sym0KindInference ())
type Tuple5Sym1 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type). a_11
                                          -> (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                                                          b_12,
                                                                                          c_13,
                                                                                          d_14,
                                                                                          e_15))))
data Tuple5Sym1 (a6989586621679042064 :: a_11) :: (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                                                              b_12,
                                                                                              c_13,
                                                                                              d_14,
                                                                                              e_15))))
  where
    Tuple5Sym1KindInference :: SameKind (Apply (Tuple5Sym1 a6989586621679042064) arg_a8ov) (Tuple5Sym2 a6989586621679042064 arg_a8ov) =>
                                Tuple5Sym1 a6989586621679042064 a6989586621679042065
type instance Apply @b_12 @((~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                              b_12, c_13, d_14,
                                                              e_15)))) (Tuple5Sym1 a6989586621679042064) a6989586621679042065 = Tuple5Sym2 a6989586621679042064 a6989586621679042065
instance SuppressUnusedWarnings (Tuple5Sym1 a6989586621679042064) where
  suppressUnusedWarnings = snd ((,) Tuple5Sym1KindInference ())
type Tuple5Sym2 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type). a_11
                                          -> b_12
                                              -> (~>) c_13 ((~>) d_14 ((~>) e_15 (a_11, b_12,
                                                                                  c_13, d_14,
                                                                                  e_15)))
data Tuple5Sym2 (a6989586621679042064 :: a_11) (a6989586621679042065 :: b_12) :: (~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                                                                                  b_12,
                                                                                                                  c_13,
                                                                                                                  d_14,
                                                                                                                  e_15)))
  where
    Tuple5Sym2KindInference :: SameKind (Apply (Tuple5Sym2 a6989586621679042064 a6989586621679042065) arg_a8ov) (Tuple5Sym3 a6989586621679042064 a6989586621679042065 arg_a8ov) =>
                                Tuple5Sym2 a6989586621679042064 a6989586621679042065 a6989586621679042066
type instance Apply @c_13 @((~>) d_14 ((~>) e_15 (a_11, b_12, c_13,
                                                  d_14,
                                                  e_15))) (Tuple5Sym2 a6989586621679042064 a6989586621679042065) a6989586621679042066 = Tuple5Sym3 a6989586621679042064 a6989586621679042065 a6989586621679042066
instance SuppressUnusedWarnings (Tuple5Sym2 a6989586621679042064 a6989586621679042065) where
  suppressUnusedWarnings = snd ((,) Tuple5Sym2KindInference ())
type Tuple5Sym3 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> (~>) d_14 ((~>) e_15 (a_11, b_12, c_13, d_14,
                                                                          e_15))
data Tuple5Sym3 (a6989586621679042064 :: a_11) (a6989586621679042065 :: b_12) (a6989586621679042066 :: c_13) :: (~>) d_14 ((~>) e_15 (a_11,
                                                                                                                                      b_12,
                                                                                                                                      c_13,
                                                                                                                                      d_14,
                                                                                                                                      e_15))
  where
    Tuple5Sym3KindInference :: SameKind (Apply (Tuple5Sym3 a6989586621679042064 a6989586621679042065 a6989586621679042066) arg_a8ov) (Tuple5Sym4 a6989586621679042064 a6989586621679042065 a6989586621679042066 arg_a8ov) =>
                                Tuple5Sym3 a6989586621679042064 a6989586621679042065 a6989586621679042066 a6989586621679042067
type instance Apply @d_14 @((~>) e_15 (a_11, b_12, c_13, d_14,
                                        e_15)) (Tuple5Sym3 a6989586621679042064 a6989586621679042065 a6989586621679042066) a6989586621679042067 = Tuple5Sym4 a6989586621679042064 a6989586621679042065 a6989586621679042066 a6989586621679042067
instance SuppressUnusedWarnings (Tuple5Sym3 a6989586621679042064 a6989586621679042065 a6989586621679042066) where
  suppressUnusedWarnings = snd ((,) Tuple5Sym3KindInference ())
type Tuple5Sym4 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> d_14
                                                    -> (~>) e_15 (a_11, b_12, c_13, d_14, e_15)
data Tuple5Sym4 (a6989586621679042064 :: a_11) (a6989586621679042065 :: b_12) (a6989586621679042066 :: c_13) (a6989586621679042067 :: d_14) :: (~>) e_15 (a_11,
                                                                                                                                                          b_12,
                                                                                                                                                          c_13,
                                                                                                                                                          d_14,
                                                                                                                                                          e_15)
  where
    Tuple5Sym4KindInference :: SameKind (Apply (Tuple5Sym4 a6989586621679042064 a6989586621679042065 a6989586621679042066 a6989586621679042067) arg_a8ov) (Tuple5Sym5 a6989586621679042064 a6989586621679042065 a6989586621679042066 a6989586621679042067 arg_a8ov) =>
                                Tuple5Sym4 a6989586621679042064 a6989586621679042065 a6989586621679042066 a6989586621679042067 a6989586621679042068
type instance Apply @e_15 @(a_11, b_12, c_13, d_14,
                            e_15) (Tuple5Sym4 a6989586621679042064 a6989586621679042065 a6989586621679042066 a6989586621679042067) a6989586621679042068 = '(a6989586621679042064,
                                                                                                                                                            a6989586621679042065,
                                                                                                                                                            a6989586621679042066,
                                                                                                                                                            a6989586621679042067,
                                                                                                                                                            a6989586621679042068)
instance SuppressUnusedWarnings (Tuple5Sym4 a6989586621679042064 a6989586621679042065 a6989586621679042066 a6989586621679042067) where
  suppressUnusedWarnings = snd ((,) Tuple5Sym4KindInference ())
type Tuple5Sym5 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> d_14
                                                    -> e_15 -> (a_11, b_12, c_13, d_14, e_15)
type family Tuple5Sym5 @(a_11 :: Type) @(b_12 :: Type) @(c_13 :: Type) @(d_14 :: Type) @(e_15 :: Type) (a6989586621679042064 :: a_11) (a6989586621679042065 :: b_12) (a6989586621679042066 :: c_13) (a6989586621679042067 :: d_14) (a6989586621679042068 :: e_15) :: (a_11,
                                                                                                                                                                                                                                                                      b_12,
                                                                                                                                                                                                                                                                      c_13,
                                                                                                                                                                                                                                                                      d_14,
                                                                                                                                                                                                                                                                      e_15) where
  Tuple5Sym5 a6989586621679042064 a6989586621679042065 a6989586621679042066 a6989586621679042067 a6989586621679042068 = '(a6989586621679042064,
                                                                                                                          a6989586621679042065,
                                                                                                                          a6989586621679042066,
                                                                                                                          a6989586621679042067,
                                                                                                                          a6989586621679042068)
type STuple5 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type)
                        (d_14 :: Type)
                        (e_15 :: Type). (a_11, b_12, c_13, d_14, e_15) -> Type
data STuple5 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type)
                        (d_14 :: Type)
                        (e_15 :: Type).
                (a_11, b_12, c_13, d_14, e_15) -> Type
  where
    STuple5 :: forall (a_11 :: Type)
                      (b_12 :: Type)
                      (c_13 :: Type)
                      (d_14 :: Type)
                      (e_15 :: Type)
                      (n_a8oB :: a_11)
                      (n_a8oC :: b_12)
                      (n_a8oD :: c_13)
                      (n_a8oE :: d_14)
                      (n_a8oF :: e_15).
                (Sing n_a8oB) ->
                (Sing n_a8oC) ->
                (Sing n_a8oD) ->
                (Sing n_a8oE) ->
                (Sing n_a8oF) ->
                STuple5 ('(n_a8oB, n_a8oC, n_a8oD, n_a8oE, n_a8oF) :: (a_11, b_12,
                                                                      c_13, d_14, e_15))
type instance Sing @(a_11, b_12, c_13, d_14, e_15) = STuple5
instance (SingKind a_11,
          SingKind b_12,
          SingKind c_13,
          SingKind d_14,
          SingKind e_15) =>
          SingKind (a_11, b_12, c_13, d_14, e_15) where
  type Demote (a_11, b_12, c_13, d_14, e_15) = (Demote a_11,
                                                Demote b_12, Demote c_13, Demote d_14,
                                                Demote e_15)
  fromSing (STuple5 b_a8oV b_a8oW b_a8oX b_a8oY b_a8oZ)
    = (,,,,)
        (fromSing b_a8oV) (fromSing b_a8oW) (fromSing b_a8oX)
        (fromSing b_a8oY) (fromSing b_a8oZ)
  toSing
    ((,,,,) (b_a8p1 :: Demote a_11) (b_a8p2 :: Demote b_12)
            (b_a8p3 :: Demote c_13) (b_a8p4 :: Demote d_14)
            (b_a8p5 :: Demote e_15))
    = (\cases
          (SomeSing c_a8p6)
            (SomeSing c_a8p7)
            (SomeSing c_a8p8)
            (SomeSing c_a8p9)
            (SomeSing c_a8pa)
            -> SomeSing (STuple5 c_a8p6 c_a8p7 c_a8p8 c_a8p9 c_a8pa))
        (toSing b_a8p1 :: SomeSing a_11) (toSing b_a8p2 :: SomeSing b_12)
        (toSing b_a8p3 :: SomeSing c_13) (toSing b_a8p4 :: SomeSing d_14)
        (toSing b_a8p5 :: SomeSing e_15)
instance (SingI n_a8oB,
          SingI n_a8oC,
          SingI n_a8oD,
          SingI n_a8oE,
          SingI n_a8oF) =>
          SingI '(n_a8oB :: a_11,
                  n_a8oC :: b_12,
                  n_a8oD :: c_13,
                  n_a8oE :: d_14,
                  n_a8oF :: e_15) where
  sing = STuple5 sing sing sing sing sing
instance (SingI n_a8oB,
          SingI n_a8oC,
          SingI n_a8oD,
          SingI n_a8oE) =>
          SingI1 ('(,,,,) (n_a8oB :: a_11) (n_a8oC :: b_12) (n_a8oD :: c_13) (n_a8oE :: d_14)) where
  liftSing = STuple5 sing sing sing sing
instance (SingI n_a8oB, SingI n_a8oC, SingI n_a8oD) =>
          SingI2 ('(,,,,) (n_a8oB :: a_11) (n_a8oC :: b_12) (n_a8oD :: c_13)) where
  liftSing2 = STuple5 sing sing sing
instance SingI (Tuple5Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                                                      b_12, c_13,
                                                                                      d_14,
                                                                                      e_15)))))) where
  sing = singFun5 @Tuple5Sym0 STuple5
instance SingI d_a8oG =>
          SingI (Tuple5Sym1 (d_a8oG :: a_11) :: (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                                                            b_12,
                                                                                            c_13,
                                                                                            d_14,
                                                                                            e_15))))) where
  sing
    = singFun4 @(Tuple5Sym1 (d_a8oG :: a_11)) (STuple5 (sing @d_a8oG))
instance SingI1 (Tuple5Sym1 :: a_11
                                -> (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 (a_11, b_12, c_13,
                                                                              d_14,
                                                                              e_15))))) where
  liftSing (s_a8oU :: Sing (d_a8oG :: a_11))
    = singFun4 @(Tuple5Sym1 (d_a8oG :: a_11)) (STuple5 s_a8oU)
instance (SingI d_a8oG, SingI d_a8oH) =>
          SingI (Tuple5Sym2 (d_a8oG :: a_11) (d_a8oH :: b_12) :: (~>) c_13 ((~>) d_14 ((~>) e_15 (a_11,
                                                                                                  b_12,
                                                                                                  c_13,
                                                                                                  d_14,
                                                                                                  e_15)))) where
  sing
    = singFun3
        @(Tuple5Sym2 (d_a8oG :: a_11) (d_a8oH :: b_12))
        (STuple5 (sing @d_a8oG) (sing @d_a8oH))
instance SingI d_a8oG =>
          SingI1 (Tuple5Sym2 (d_a8oG :: a_11) :: b_12
                                                -> (~>) c_13 ((~>) d_14 ((~>) e_15 (a_11, b_12,
                                                                                    c_13, d_14,
                                                                                    e_15)))) where
  liftSing (s_a8oR :: Sing (d_a8oH :: b_12))
    = singFun3
        @(Tuple5Sym2 (d_a8oG :: a_11) (d_a8oH :: b_12))
        (STuple5 (sing @d_a8oG) s_a8oR)
instance SingI2 (Tuple5Sym2 :: a_11
                                -> b_12
                                  -> (~>) c_13 ((~>) d_14 ((~>) e_15 (a_11, b_12, c_13, d_14,
                                                                      e_15)))) where
  liftSing2
    (s_a8oS :: Sing (d_a8oG :: a_11))
    (s_a8oT :: Sing (d_a8oH :: b_12))
    = singFun3
        @(Tuple5Sym2 (d_a8oG :: a_11) (d_a8oH :: b_12))
        (STuple5 s_a8oS s_a8oT)
instance (SingI d_a8oG, SingI d_a8oH, SingI d_a8oI) =>
          SingI (Tuple5Sym3 (d_a8oG :: a_11) (d_a8oH :: b_12) (d_a8oI :: c_13) :: (~>) d_14 ((~>) e_15 (a_11,
                                                                                                        b_12,
                                                                                                        c_13,
                                                                                                        d_14,
                                                                                                        e_15))) where
  sing
    = singFun2
        @(Tuple5Sym3 (d_a8oG :: a_11) (d_a8oH :: b_12) (d_a8oI :: c_13))
        (STuple5 (sing @d_a8oG) (sing @d_a8oH) (sing @d_a8oI))
instance (SingI d_a8oG, SingI d_a8oH) =>
          SingI1 (Tuple5Sym3 (d_a8oG :: a_11) (d_a8oH :: b_12) :: c_13
                                                                  -> (~>) d_14 ((~>) e_15 (a_11,
                                                                                          b_12,
                                                                                          c_13,
                                                                                          d_14,
                                                                                          e_15))) where
  liftSing (s_a8oO :: Sing (d_a8oI :: c_13))
    = singFun2
        @(Tuple5Sym3 (d_a8oG :: a_11) (d_a8oH :: b_12) (d_a8oI :: c_13))
        (STuple5 (sing @d_a8oG) (sing @d_a8oH) s_a8oO)
instance SingI d_a8oG =>
          SingI2 (Tuple5Sym3 (d_a8oG :: a_11) :: b_12
                                                -> c_13
                                                    -> (~>) d_14 ((~>) e_15 (a_11, b_12, c_13,
                                                                            d_14, e_15))) where
  liftSing2
    (s_a8oP :: Sing (d_a8oH :: b_12))
    (s_a8oQ :: Sing (d_a8oI :: c_13))
    = singFun2
        @(Tuple5Sym3 (d_a8oG :: a_11) (d_a8oH :: b_12) (d_a8oI :: c_13))
        (STuple5 (sing @d_a8oG) s_a8oP s_a8oQ)
instance (SingI d_a8oG,
          SingI d_a8oH,
          SingI d_a8oI,
          SingI d_a8oJ) =>
          SingI (Tuple5Sym4 (d_a8oG :: a_11) (d_a8oH :: b_12) (d_a8oI :: c_13) (d_a8oJ :: d_14) :: (~>) e_15 (a_11,
                                                                                                              b_12,
                                                                                                              c_13,
                                                                                                              d_14,
                                                                                                              e_15)) where
  sing
    = singFun1
        @(Tuple5Sym4 (d_a8oG :: a_11) (d_a8oH :: b_12) (d_a8oI :: c_13) (d_a8oJ :: d_14))
        (STuple5
            (sing @d_a8oG) (sing @d_a8oH) (sing @d_a8oI) (sing @d_a8oJ))
instance (SingI d_a8oG, SingI d_a8oH, SingI d_a8oI) =>
          SingI1 (Tuple5Sym4 (d_a8oG :: a_11) (d_a8oH :: b_12) (d_a8oI :: c_13) :: d_14
                                                                                  -> (~>) e_15 (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14,
                                                                                                e_15)) where
  liftSing (s_a8oL :: Sing (d_a8oJ :: d_14))
    = singFun1
        @(Tuple5Sym4 (d_a8oG :: a_11) (d_a8oH :: b_12) (d_a8oI :: c_13) (d_a8oJ :: d_14))
        (STuple5 (sing @d_a8oG) (sing @d_a8oH) (sing @d_a8oI) s_a8oL)
instance (SingI d_a8oG, SingI d_a8oH) =>
          SingI2 (Tuple5Sym4 (d_a8oG :: a_11) (d_a8oH :: b_12) :: c_13
                                                                  -> d_14
                                                                    -> (~>) e_15 (a_11, b_12,
                                                                                  c_13, d_14,
                                                                                  e_15)) where
  liftSing2
    (s_a8oM :: Sing (d_a8oI :: c_13))
    (s_a8oN :: Sing (d_a8oJ :: d_14))
    = singFun1
        @(Tuple5Sym4 (d_a8oG :: a_11) (d_a8oH :: b_12) (d_a8oI :: c_13) (d_a8oJ :: d_14))
        (STuple5 (sing @d_a8oG) (sing @d_a8oH) s_a8oM s_a8oN)
type Tuple6Sym0 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type). (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                            b_12,
                                                                                                            c_13,
                                                                                                            d_14,
                                                                                                            e_15,
                                                                                                            f_16))))))
data Tuple6Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                      b_12, c_13,
                                                                                      d_14, e_15,
                                                                                      f_16))))))
  where
    Tuple6Sym0KindInference :: SameKind (Apply Tuple6Sym0 arg_a8pY) (Tuple6Sym1 arg_a8pY) =>
                                Tuple6Sym0 a6989586621679042155
type instance Apply @a_11 @((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                    b_12, c_13,
                                                                                    d_14, e_15,
                                                                                    f_16)))))) Tuple6Sym0 a6989586621679042155 = Tuple6Sym1 a6989586621679042155
instance SuppressUnusedWarnings Tuple6Sym0 where
  suppressUnusedWarnings = snd ((,) Tuple6Sym0KindInference ())
type Tuple6Sym1 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type). a_11
                                          -> (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                    b_12,
                                                                                                    c_13,
                                                                                                    d_14,
                                                                                                    e_15,
                                                                                                    f_16)))))
data Tuple6Sym1 (a6989586621679042155 :: a_11) :: (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                          b_12,
                                                                                                          c_13,
                                                                                                          d_14,
                                                                                                          e_15,
                                                                                                          f_16)))))
  where
    Tuple6Sym1KindInference :: SameKind (Apply (Tuple6Sym1 a6989586621679042155) arg_a8pY) (Tuple6Sym2 a6989586621679042155 arg_a8pY) =>
                                Tuple6Sym1 a6989586621679042155 a6989586621679042156
type instance Apply @b_12 @((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                        b_12, c_13, d_14, e_15,
                                                                        f_16))))) (Tuple6Sym1 a6989586621679042155) a6989586621679042156 = Tuple6Sym2 a6989586621679042155 a6989586621679042156
instance SuppressUnusedWarnings (Tuple6Sym1 a6989586621679042155) where
  suppressUnusedWarnings = snd ((,) Tuple6Sym1KindInference ())
type Tuple6Sym2 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type). a_11
                                          -> b_12
                                              -> (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                            b_12,
                                                                                            c_13,
                                                                                            d_14,
                                                                                            e_15,
                                                                                            f_16))))
data Tuple6Sym2 (a6989586621679042155 :: a_11) (a6989586621679042156 :: b_12) :: (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                                              b_12,
                                                                                                                              c_13,
                                                                                                                              d_14,
                                                                                                                              e_15,
                                                                                                                              f_16))))
  where
    Tuple6Sym2KindInference :: SameKind (Apply (Tuple6Sym2 a6989586621679042155 a6989586621679042156) arg_a8pY) (Tuple6Sym3 a6989586621679042155 a6989586621679042156 arg_a8pY) =>
                                Tuple6Sym2 a6989586621679042155 a6989586621679042156 a6989586621679042157
type instance Apply @c_13 @((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                              b_12, c_13, d_14, e_15,
                                                              f_16)))) (Tuple6Sym2 a6989586621679042155 a6989586621679042156) a6989586621679042157 = Tuple6Sym3 a6989586621679042155 a6989586621679042156 a6989586621679042157
instance SuppressUnusedWarnings (Tuple6Sym2 a6989586621679042155 a6989586621679042156) where
  suppressUnusedWarnings = snd ((,) Tuple6Sym2KindInference ())
type Tuple6Sym3 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> (~>) d_14 ((~>) e_15 ((~>) f_16 (a_11, b_12,
                                                                                    c_13, d_14,
                                                                                    e_15,
                                                                                    f_16)))
data Tuple6Sym3 (a6989586621679042155 :: a_11) (a6989586621679042156 :: b_12) (a6989586621679042157 :: c_13) :: (~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                                                                  b_12,
                                                                                                                                                  c_13,
                                                                                                                                                  d_14,
                                                                                                                                                  e_15,
                                                                                                                                                  f_16)))
  where
    Tuple6Sym3KindInference :: SameKind (Apply (Tuple6Sym3 a6989586621679042155 a6989586621679042156 a6989586621679042157) arg_a8pY) (Tuple6Sym4 a6989586621679042155 a6989586621679042156 a6989586621679042157 arg_a8pY) =>
                                Tuple6Sym3 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158
type instance Apply @d_14 @((~>) e_15 ((~>) f_16 (a_11, b_12, c_13,
                                                  d_14, e_15,
                                                  f_16))) (Tuple6Sym3 a6989586621679042155 a6989586621679042156 a6989586621679042157) a6989586621679042158 = Tuple6Sym4 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158
instance SuppressUnusedWarnings (Tuple6Sym3 a6989586621679042155 a6989586621679042156 a6989586621679042157) where
  suppressUnusedWarnings = snd ((,) Tuple6Sym3KindInference ())
type Tuple6Sym4 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> d_14
                                                    -> (~>) e_15 ((~>) f_16 (a_11, b_12, c_13,
                                                                            d_14, e_15, f_16))
data Tuple6Sym4 (a6989586621679042155 :: a_11) (a6989586621679042156 :: b_12) (a6989586621679042157 :: c_13) (a6989586621679042158 :: d_14) :: (~>) e_15 ((~>) f_16 (a_11,
                                                                                                                                                                      b_12,
                                                                                                                                                                      c_13,
                                                                                                                                                                      d_14,
                                                                                                                                                                      e_15,
                                                                                                                                                                      f_16))
  where
    Tuple6Sym4KindInference :: SameKind (Apply (Tuple6Sym4 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158) arg_a8pY) (Tuple6Sym5 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158 arg_a8pY) =>
                                Tuple6Sym4 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158 a6989586621679042159
type instance Apply @e_15 @((~>) f_16 (a_11, b_12, c_13, d_14,
                                        e_15,
                                        f_16)) (Tuple6Sym4 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158) a6989586621679042159 = Tuple6Sym5 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158 a6989586621679042159
instance SuppressUnusedWarnings (Tuple6Sym4 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158) where
  suppressUnusedWarnings = snd ((,) Tuple6Sym4KindInference ())
type Tuple6Sym5 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> d_14
                                                    -> e_15
                                                      -> (~>) f_16 (a_11, b_12, c_13, d_14,
                                                                    e_15, f_16)
data Tuple6Sym5 (a6989586621679042155 :: a_11) (a6989586621679042156 :: b_12) (a6989586621679042157 :: c_13) (a6989586621679042158 :: d_14) (a6989586621679042159 :: e_15) :: (~>) f_16 (a_11,
                                                                                                                                                                                          b_12,
                                                                                                                                                                                          c_13,
                                                                                                                                                                                          d_14,
                                                                                                                                                                                          e_15,
                                                                                                                                                                                          f_16)
  where
    Tuple6Sym5KindInference :: SameKind (Apply (Tuple6Sym5 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158 a6989586621679042159) arg_a8pY) (Tuple6Sym6 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158 a6989586621679042159 arg_a8pY) =>
                                Tuple6Sym5 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158 a6989586621679042159 a6989586621679042160
type instance Apply @f_16 @(a_11, b_12, c_13, d_14, e_15,
                            f_16) (Tuple6Sym5 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158 a6989586621679042159) a6989586621679042160 = '(a6989586621679042155,
                                                                                                                                                                                  a6989586621679042156,
                                                                                                                                                                                  a6989586621679042157,
                                                                                                                                                                                  a6989586621679042158,
                                                                                                                                                                                  a6989586621679042159,
                                                                                                                                                                                  a6989586621679042160)
instance SuppressUnusedWarnings (Tuple6Sym5 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158 a6989586621679042159) where
  suppressUnusedWarnings = snd ((,) Tuple6Sym5KindInference ())
type Tuple6Sym6 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> d_14
                                                    -> e_15
                                                      -> f_16
                                                          -> (a_11, b_12, c_13, d_14, e_15, f_16)
type family Tuple6Sym6 @(a_11 :: Type) @(b_12 :: Type) @(c_13 :: Type) @(d_14 :: Type) @(e_15 :: Type) @(f_16 :: Type) (a6989586621679042155 :: a_11) (a6989586621679042156 :: b_12) (a6989586621679042157 :: c_13) (a6989586621679042158 :: d_14) (a6989586621679042159 :: e_15) (a6989586621679042160 :: f_16) :: (a_11,
                                                                                                                                                                                                                                                                                                                      b_12,
                                                                                                                                                                                                                                                                                                                      c_13,
                                                                                                                                                                                                                                                                                                                      d_14,
                                                                                                                                                                                                                                                                                                                      e_15,
                                                                                                                                                                                                                                                                                                                      f_16) where
  Tuple6Sym6 a6989586621679042155 a6989586621679042156 a6989586621679042157 a6989586621679042158 a6989586621679042159 a6989586621679042160 = '(a6989586621679042155,
                                                                                                                                                a6989586621679042156,
                                                                                                                                                a6989586621679042157,
                                                                                                                                                a6989586621679042158,
                                                                                                                                                a6989586621679042159,
                                                                                                                                                a6989586621679042160)
type STuple6 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type)
                        (d_14 :: Type)
                        (e_15 :: Type)
                        (f_16 :: Type). (a_11, b_12, c_13, d_14, e_15, f_16) -> Type
data STuple6 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type)
                        (d_14 :: Type)
                        (e_15 :: Type)
                        (f_16 :: Type).
                (a_11, b_12, c_13, d_14, e_15, f_16) -> Type
  where
    STuple6 :: forall (a_11 :: Type)
                      (b_12 :: Type)
                      (c_13 :: Type)
                      (d_14 :: Type)
                      (e_15 :: Type)
                      (f_16 :: Type)
                      (n_a8q5 :: a_11)
                      (n_a8q6 :: b_12)
                      (n_a8q7 :: c_13)
                      (n_a8q8 :: d_14)
                      (n_a8q9 :: e_15)
                      (n_a8qa :: f_16).
                (Sing n_a8q5) ->
                (Sing n_a8q6) ->
                (Sing n_a8q7) ->
                (Sing n_a8q8) ->
                (Sing n_a8q9) ->
                (Sing n_a8qa) ->
                STuple6 ('(n_a8q5,
                          n_a8q6,
                          n_a8q7,
                          n_a8q8,
                          n_a8q9,
                          n_a8qa) :: (a_11, b_12, c_13, d_14, e_15, f_16))
type instance Sing @(a_11, b_12, c_13, d_14, e_15, f_16) = STuple6
instance (SingKind a_11,
          SingKind b_12,
          SingKind c_13,
          SingKind d_14,
          SingKind e_15,
          SingKind f_16) =>
          SingKind (a_11, b_12, c_13, d_14, e_15, f_16) where
  type Demote (a_11, b_12, c_13, d_14, e_15, f_16) = (Demote a_11,
                                                      Demote b_12, Demote c_13, Demote d_14,
                                                      Demote e_15, Demote f_16)
  fromSing (STuple6 b_a8qu b_a8qv b_a8qw b_a8qx b_a8qy b_a8qz)
    = (,,,,,)
        (fromSing b_a8qu) (fromSing b_a8qv) (fromSing b_a8qw)
        (fromSing b_a8qx) (fromSing b_a8qy) (fromSing b_a8qz)
  toSing
    ((,,,,,) (b_a8qB :: Demote a_11) (b_a8qC :: Demote b_12)
              (b_a8qD :: Demote c_13) (b_a8qE :: Demote d_14)
              (b_a8qF :: Demote e_15) (b_a8qG :: Demote f_16))
    = (\cases
          (SomeSing c_a8qH)
            (SomeSing c_a8qI)
            (SomeSing c_a8qJ)
            (SomeSing c_a8qK)
            (SomeSing c_a8qL)
            (SomeSing c_a8qM)
            -> SomeSing (STuple6 c_a8qH c_a8qI c_a8qJ c_a8qK c_a8qL c_a8qM))
        (toSing b_a8qB :: SomeSing a_11) (toSing b_a8qC :: SomeSing b_12)
        (toSing b_a8qD :: SomeSing c_13) (toSing b_a8qE :: SomeSing d_14)
        (toSing b_a8qF :: SomeSing e_15) (toSing b_a8qG :: SomeSing f_16)
instance (SingI n_a8q5,
          SingI n_a8q6,
          SingI n_a8q7,
          SingI n_a8q8,
          SingI n_a8q9,
          SingI n_a8qa) =>
          SingI '(n_a8q5 :: a_11,
                  n_a8q6 :: b_12,
                  n_a8q7 :: c_13,
                  n_a8q8 :: d_14,
                  n_a8q9 :: e_15,
                  n_a8qa :: f_16) where
  sing = STuple6 sing sing sing sing sing sing
instance (SingI n_a8q5,
          SingI n_a8q6,
          SingI n_a8q7,
          SingI n_a8q8,
          SingI n_a8q9) =>
          SingI1 ('(,,,,,) (n_a8q5 :: a_11) (n_a8q6 :: b_12) (n_a8q7 :: c_13) (n_a8q8 :: d_14) (n_a8q9 :: e_15)) where
  liftSing = STuple6 sing sing sing sing sing
instance (SingI n_a8q5,
          SingI n_a8q6,
          SingI n_a8q7,
          SingI n_a8q8) =>
          SingI2 ('(,,,,,) (n_a8q5 :: a_11) (n_a8q6 :: b_12) (n_a8q7 :: c_13) (n_a8q8 :: d_14)) where
  liftSing2 = STuple6 sing sing sing sing
instance SingI (Tuple6Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14,
                                                                                                e_15,
                                                                                                f_16))))))) where
  sing = singFun6 @Tuple6Sym0 STuple6
instance SingI d_a8qb =>
          SingI (Tuple6Sym1 (d_a8qb :: a_11) :: (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                      b_12,
                                                                                                      c_13,
                                                                                                      d_14,
                                                                                                      e_15,
                                                                                                      f_16)))))) where
  sing
    = singFun5 @(Tuple6Sym1 (d_a8qb :: a_11)) (STuple6 (sing @d_a8qb))
instance SingI1 (Tuple6Sym1 :: a_11
                                -> (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                          b_12,
                                                                                          c_13,
                                                                                          d_14,
                                                                                          e_15,
                                                                                          f_16)))))) where
  liftSing (s_a8qt :: Sing (d_a8qb :: a_11))
    = singFun5 @(Tuple6Sym1 (d_a8qb :: a_11)) (STuple6 s_a8qt)
instance (SingI d_a8qb, SingI d_a8qc) =>
          SingI (Tuple6Sym2 (d_a8qb :: a_11) (d_a8qc :: b_12) :: (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                            b_12,
                                                                                                            c_13,
                                                                                                            d_14,
                                                                                                            e_15,
                                                                                                            f_16))))) where
  sing
    = singFun4
        @(Tuple6Sym2 (d_a8qb :: a_11) (d_a8qc :: b_12))
        (STuple6 (sing @d_a8qb) (sing @d_a8qc))
instance SingI d_a8qb =>
          SingI1 (Tuple6Sym2 (d_a8qb :: a_11) :: b_12
                                                -> (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14,
                                                                                                e_15,
                                                                                                f_16))))) where
  liftSing (s_a8qq :: Sing (d_a8qc :: b_12))
    = singFun4
        @(Tuple6Sym2 (d_a8qb :: a_11) (d_a8qc :: b_12))
        (STuple6 (sing @d_a8qb) s_a8qq)
instance SingI2 (Tuple6Sym2 :: a_11
                                -> b_12
                                  -> (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 (a_11, b_12,
                                                                                  c_13, d_14,
                                                                                  e_15,
                                                                                  f_16))))) where
  liftSing2
    (s_a8qr :: Sing (d_a8qb :: a_11))
    (s_a8qs :: Sing (d_a8qc :: b_12))
    = singFun4
        @(Tuple6Sym2 (d_a8qb :: a_11) (d_a8qc :: b_12))
        (STuple6 s_a8qr s_a8qs)
instance (SingI d_a8qb, SingI d_a8qc, SingI d_a8qd) =>
          SingI (Tuple6Sym3 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) :: (~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                                  b_12,
                                                                                                                  c_13,
                                                                                                                  d_14,
                                                                                                                  e_15,
                                                                                                                  f_16)))) where
  sing
    = singFun3
        @(Tuple6Sym3 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13))
        (STuple6 (sing @d_a8qb) (sing @d_a8qc) (sing @d_a8qd))
instance (SingI d_a8qb, SingI d_a8qc) =>
          SingI1 (Tuple6Sym3 (d_a8qb :: a_11) (d_a8qc :: b_12) :: c_13
                                                                  -> (~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                                      b_12,
                                                                                                      c_13,
                                                                                                      d_14,
                                                                                                      e_15,
                                                                                                      f_16)))) where
  liftSing (s_a8qn :: Sing (d_a8qd :: c_13))
    = singFun3
        @(Tuple6Sym3 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13))
        (STuple6 (sing @d_a8qb) (sing @d_a8qc) s_a8qn)
instance SingI d_a8qb =>
          SingI2 (Tuple6Sym3 (d_a8qb :: a_11) :: b_12
                                                -> c_13
                                                    -> (~>) d_14 ((~>) e_15 ((~>) f_16 (a_11,
                                                                                        b_12,
                                                                                        c_13,
                                                                                        d_14,
                                                                                        e_15,
                                                                                        f_16)))) where
  liftSing2
    (s_a8qo :: Sing (d_a8qc :: b_12))
    (s_a8qp :: Sing (d_a8qd :: c_13))
    = singFun3
        @(Tuple6Sym3 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13))
        (STuple6 (sing @d_a8qb) s_a8qo s_a8qp)
instance (SingI d_a8qb,
          SingI d_a8qc,
          SingI d_a8qd,
          SingI d_a8qe) =>
          SingI (Tuple6Sym4 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) (d_a8qe :: d_14) :: (~>) e_15 ((~>) f_16 (a_11,
                                                                                                                        b_12,
                                                                                                                        c_13,
                                                                                                                        d_14,
                                                                                                                        e_15,
                                                                                                                        f_16))) where
  sing
    = singFun2
        @(Tuple6Sym4 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) (d_a8qe :: d_14))
        (STuple6
            (sing @d_a8qb) (sing @d_a8qc) (sing @d_a8qd) (sing @d_a8qe))
instance (SingI d_a8qb, SingI d_a8qc, SingI d_a8qd) =>
          SingI1 (Tuple6Sym4 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) :: d_14
                                                                                  -> (~>) e_15 ((~>) f_16 (a_11,
                                                                                                            b_12,
                                                                                                            c_13,
                                                                                                            d_14,
                                                                                                            e_15,
                                                                                                            f_16))) where
  liftSing (s_a8qk :: Sing (d_a8qe :: d_14))
    = singFun2
        @(Tuple6Sym4 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) (d_a8qe :: d_14))
        (STuple6 (sing @d_a8qb) (sing @d_a8qc) (sing @d_a8qd) s_a8qk)
instance (SingI d_a8qb, SingI d_a8qc) =>
          SingI2 (Tuple6Sym4 (d_a8qb :: a_11) (d_a8qc :: b_12) :: c_13
                                                                  -> d_14
                                                                    -> (~>) e_15 ((~>) f_16 (a_11,
                                                                                              b_12,
                                                                                              c_13,
                                                                                              d_14,
                                                                                              e_15,
                                                                                              f_16))) where
  liftSing2
    (s_a8ql :: Sing (d_a8qd :: c_13))
    (s_a8qm :: Sing (d_a8qe :: d_14))
    = singFun2
        @(Tuple6Sym4 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) (d_a8qe :: d_14))
        (STuple6 (sing @d_a8qb) (sing @d_a8qc) s_a8ql s_a8qm)
instance (SingI d_a8qb,
          SingI d_a8qc,
          SingI d_a8qd,
          SingI d_a8qe,
          SingI d_a8qf) =>
          SingI (Tuple6Sym5 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) (d_a8qe :: d_14) (d_a8qf :: e_15) :: (~>) f_16 (a_11,
                                                                                                                              b_12,
                                                                                                                              c_13,
                                                                                                                              d_14,
                                                                                                                              e_15,
                                                                                                                              f_16)) where
  sing
    = singFun1
        @(Tuple6Sym5 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) (d_a8qe :: d_14) (d_a8qf :: e_15))
        (STuple6
            (sing @d_a8qb) (sing @d_a8qc) (sing @d_a8qd) (sing @d_a8qe)
            (sing @d_a8qf))
instance (SingI d_a8qb,
          SingI d_a8qc,
          SingI d_a8qd,
          SingI d_a8qe) =>
          SingI1 (Tuple6Sym5 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) (d_a8qe :: d_14) :: e_15
                                                                                                    -> (~>) f_16 (a_11,
                                                                                                                  b_12,
                                                                                                                  c_13,
                                                                                                                  d_14,
                                                                                                                  e_15,
                                                                                                                  f_16)) where
  liftSing (s_a8qh :: Sing (d_a8qf :: e_15))
    = singFun1
        @(Tuple6Sym5 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) (d_a8qe :: d_14) (d_a8qf :: e_15))
        (STuple6
            (sing @d_a8qb) (sing @d_a8qc) (sing @d_a8qd) (sing @d_a8qe) s_a8qh)
instance (SingI d_a8qb, SingI d_a8qc, SingI d_a8qd) =>
          SingI2 (Tuple6Sym5 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) :: d_14
                                                                                  -> e_15
                                                                                      -> (~>) f_16 (a_11,
                                                                                                    b_12,
                                                                                                    c_13,
                                                                                                    d_14,
                                                                                                    e_15,
                                                                                                    f_16)) where
  liftSing2
    (s_a8qi :: Sing (d_a8qe :: d_14))
    (s_a8qj :: Sing (d_a8qf :: e_15))
    = singFun1
        @(Tuple6Sym5 (d_a8qb :: a_11) (d_a8qc :: b_12) (d_a8qd :: c_13) (d_a8qe :: d_14) (d_a8qf :: e_15))
        (STuple6
            (sing @d_a8qb) (sing @d_a8qc) (sing @d_a8qd) s_a8qi s_a8qj)
type Tuple7Sym0 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type)
                          (g_17 :: Type). (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                        b_12,
                                                                                                                        c_13,
                                                                                                                        d_14,
                                                                                                                        e_15,
                                                                                                                        f_16,
                                                                                                                        g_17)))))))
data Tuple7Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14,
                                                                                                e_15,
                                                                                                f_16,
                                                                                                g_17)))))))
  where
    Tuple7Sym0KindInference :: SameKind (Apply Tuple7Sym0 arg_a8rP) (Tuple7Sym1 arg_a8rP) =>
                                Tuple7Sym0 a6989586621679042270
type instance Apply @a_11 @((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                              b_12,
                                                                                              c_13,
                                                                                              d_14,
                                                                                              e_15,
                                                                                              f_16,
                                                                                              g_17))))))) Tuple7Sym0 a6989586621679042270 = Tuple7Sym1 a6989586621679042270
instance SuppressUnusedWarnings Tuple7Sym0 where
  suppressUnusedWarnings = snd ((,) Tuple7Sym0KindInference ())
type Tuple7Sym1 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type)
                          (g_17 :: Type). a_11
                                          -> (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                b_12,
                                                                                                                c_13,
                                                                                                                d_14,
                                                                                                                e_15,
                                                                                                                f_16,
                                                                                                                g_17))))))
data Tuple7Sym1 (a6989586621679042270 :: a_11) :: (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                    b_12,
                                                                                                                    c_13,
                                                                                                                    d_14,
                                                                                                                    e_15,
                                                                                                                    f_16,
                                                                                                                    g_17))))))
  where
    Tuple7Sym1KindInference :: SameKind (Apply (Tuple7Sym1 a6989586621679042270) arg_a8rP) (Tuple7Sym2 a6989586621679042270 arg_a8rP) =>
                                Tuple7Sym1 a6989586621679042270 a6989586621679042271
type instance Apply @b_12 @((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                    b_12, c_13,
                                                                                    d_14, e_15,
                                                                                    f_16,
                                                                                    g_17)))))) (Tuple7Sym1 a6989586621679042270) a6989586621679042271 = Tuple7Sym2 a6989586621679042270 a6989586621679042271
instance SuppressUnusedWarnings (Tuple7Sym1 a6989586621679042270) where
  suppressUnusedWarnings = snd ((,) Tuple7Sym1KindInference ())
type Tuple7Sym2 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type)
                          (g_17 :: Type). a_11
                                          -> b_12
                                              -> (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                        b_12,
                                                                                                        c_13,
                                                                                                        d_14,
                                                                                                        e_15,
                                                                                                        f_16,
                                                                                                        g_17)))))
data Tuple7Sym2 (a6989586621679042270 :: a_11) (a6989586621679042271 :: b_12) :: (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                                        b_12,
                                                                                                                                        c_13,
                                                                                                                                        d_14,
                                                                                                                                        e_15,
                                                                                                                                        f_16,
                                                                                                                                        g_17)))))
  where
    Tuple7Sym2KindInference :: SameKind (Apply (Tuple7Sym2 a6989586621679042270 a6989586621679042271) arg_a8rP) (Tuple7Sym3 a6989586621679042270 a6989586621679042271 arg_a8rP) =>
                                Tuple7Sym2 a6989586621679042270 a6989586621679042271 a6989586621679042272
type instance Apply @c_13 @((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                        b_12, c_13, d_14, e_15,
                                                                        f_16,
                                                                        g_17))))) (Tuple7Sym2 a6989586621679042270 a6989586621679042271) a6989586621679042272 = Tuple7Sym3 a6989586621679042270 a6989586621679042271 a6989586621679042272
instance SuppressUnusedWarnings (Tuple7Sym2 a6989586621679042270 a6989586621679042271) where
  suppressUnusedWarnings = snd ((,) Tuple7Sym2KindInference ())
type Tuple7Sym3 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type)
                          (g_17 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> (~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                b_12,
                                                                                                c_13,
                                                                                                d_14,
                                                                                                e_15,
                                                                                                f_16,
                                                                                                g_17))))
data Tuple7Sym3 (a6989586621679042270 :: a_11) (a6989586621679042271 :: b_12) (a6989586621679042272 :: c_13) :: (~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                                                            b_12,
                                                                                                                                                            c_13,
                                                                                                                                                            d_14,
                                                                                                                                                            e_15,
                                                                                                                                                            f_16,
                                                                                                                                                            g_17))))
  where
    Tuple7Sym3KindInference :: SameKind (Apply (Tuple7Sym3 a6989586621679042270 a6989586621679042271 a6989586621679042272) arg_a8rP) (Tuple7Sym4 a6989586621679042270 a6989586621679042271 a6989586621679042272 arg_a8rP) =>
                                Tuple7Sym3 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273
type instance Apply @d_14 @((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                              b_12, c_13, d_14, e_15, f_16,
                                                              g_17)))) (Tuple7Sym3 a6989586621679042270 a6989586621679042271 a6989586621679042272) a6989586621679042273 = Tuple7Sym4 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273
instance SuppressUnusedWarnings (Tuple7Sym3 a6989586621679042270 a6989586621679042271 a6989586621679042272) where
  suppressUnusedWarnings = snd ((,) Tuple7Sym3KindInference ())
type Tuple7Sym4 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type)
                          (g_17 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> d_14
                                                    -> (~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                        b_12,
                                                                                        c_13,
                                                                                        d_14,
                                                                                        e_15,
                                                                                        f_16,
                                                                                        g_17)))
data Tuple7Sym4 (a6989586621679042270 :: a_11) (a6989586621679042271 :: b_12) (a6989586621679042272 :: c_13) (a6989586621679042273 :: d_14) :: (~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                                                                                b_12,
                                                                                                                                                                                c_13,
                                                                                                                                                                                d_14,
                                                                                                                                                                                e_15,
                                                                                                                                                                                f_16,
                                                                                                                                                                                g_17)))
  where
    Tuple7Sym4KindInference :: SameKind (Apply (Tuple7Sym4 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273) arg_a8rP) (Tuple7Sym5 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 arg_a8rP) =>
                                Tuple7Sym4 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274
type instance Apply @e_15 @((~>) f_16 ((~>) g_17 (a_11, b_12, c_13,
                                                  d_14, e_15, f_16,
                                                  g_17))) (Tuple7Sym4 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273) a6989586621679042274 = Tuple7Sym5 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274
instance SuppressUnusedWarnings (Tuple7Sym4 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273) where
  suppressUnusedWarnings = snd ((,) Tuple7Sym4KindInference ())
type Tuple7Sym5 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type)
                          (g_17 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> d_14
                                                    -> e_15
                                                      -> (~>) f_16 ((~>) g_17 (a_11, b_12, c_13,
                                                                                d_14, e_15, f_16,
                                                                                g_17))
data Tuple7Sym5 (a6989586621679042270 :: a_11) (a6989586621679042271 :: b_12) (a6989586621679042272 :: c_13) (a6989586621679042273 :: d_14) (a6989586621679042274 :: e_15) :: (~>) f_16 ((~>) g_17 (a_11,
                                                                                                                                                                                                    b_12,
                                                                                                                                                                                                    c_13,
                                                                                                                                                                                                    d_14,
                                                                                                                                                                                                    e_15,
                                                                                                                                                                                                    f_16,
                                                                                                                                                                                                    g_17))
  where
    Tuple7Sym5KindInference :: SameKind (Apply (Tuple7Sym5 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274) arg_a8rP) (Tuple7Sym6 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274 arg_a8rP) =>
                                Tuple7Sym5 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274 a6989586621679042275
type instance Apply @f_16 @((~>) g_17 (a_11, b_12, c_13, d_14,
                                        e_15, f_16,
                                        g_17)) (Tuple7Sym5 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274) a6989586621679042275 = Tuple7Sym6 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274 a6989586621679042275
instance SuppressUnusedWarnings (Tuple7Sym5 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274) where
  suppressUnusedWarnings = snd ((,) Tuple7Sym5KindInference ())
type Tuple7Sym6 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type)
                          (g_17 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> d_14
                                                    -> e_15
                                                      -> f_16
                                                          -> (~>) g_17 (a_11, b_12, c_13, d_14,
                                                                        e_15, f_16, g_17)
data Tuple7Sym6 (a6989586621679042270 :: a_11) (a6989586621679042271 :: b_12) (a6989586621679042272 :: c_13) (a6989586621679042273 :: d_14) (a6989586621679042274 :: e_15) (a6989586621679042275 :: f_16) :: (~>) g_17 (a_11,
                                                                                                                                                                                                                        b_12,
                                                                                                                                                                                                                        c_13,
                                                                                                                                                                                                                        d_14,
                                                                                                                                                                                                                        e_15,
                                                                                                                                                                                                                        f_16,
                                                                                                                                                                                                                        g_17)
  where
    Tuple7Sym6KindInference :: SameKind (Apply (Tuple7Sym6 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274 a6989586621679042275) arg_a8rP) (Tuple7Sym7 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274 a6989586621679042275 arg_a8rP) =>
                                Tuple7Sym6 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274 a6989586621679042275 a6989586621679042276
type instance Apply @g_17 @(a_11, b_12, c_13, d_14, e_15, f_16,
                            g_17) (Tuple7Sym6 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274 a6989586621679042275) a6989586621679042276 = '(a6989586621679042270,
                                                                                                                                                                                                      a6989586621679042271,
                                                                                                                                                                                                      a6989586621679042272,
                                                                                                                                                                                                      a6989586621679042273,
                                                                                                                                                                                                      a6989586621679042274,
                                                                                                                                                                                                      a6989586621679042275,
                                                                                                                                                                                                      a6989586621679042276)
instance SuppressUnusedWarnings (Tuple7Sym6 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274 a6989586621679042275) where
  suppressUnusedWarnings = snd ((,) Tuple7Sym6KindInference ())
type Tuple7Sym7 :: forall (a_11 :: Type)
                          (b_12 :: Type)
                          (c_13 :: Type)
                          (d_14 :: Type)
                          (e_15 :: Type)
                          (f_16 :: Type)
                          (g_17 :: Type). a_11
                                          -> b_12
                                              -> c_13
                                                -> d_14
                                                    -> e_15
                                                      -> f_16
                                                          -> g_17
                                                            -> (a_11, b_12, c_13, d_14, e_15,
                                                                f_16, g_17)
type family Tuple7Sym7 @(a_11 :: Type) @(b_12 :: Type) @(c_13 :: Type) @(d_14 :: Type) @(e_15 :: Type) @(f_16 :: Type) @(g_17 :: Type) (a6989586621679042270 :: a_11) (a6989586621679042271 :: b_12) (a6989586621679042272 :: c_13) (a6989586621679042273 :: d_14) (a6989586621679042274 :: e_15) (a6989586621679042275 :: f_16) (a6989586621679042276 :: g_17) :: (a_11,
                                                                                                                                                                                                                                                                                                                                                                    b_12,
                                                                                                                                                                                                                                                                                                                                                                    c_13,
                                                                                                                                                                                                                                                                                                                                                                    d_14,
                                                                                                                                                                                                                                                                                                                                                                    e_15,
                                                                                                                                                                                                                                                                                                                                                                    f_16,
                                                                                                                                                                                                                                                                                                                                                                    g_17) where
  Tuple7Sym7 a6989586621679042270 a6989586621679042271 a6989586621679042272 a6989586621679042273 a6989586621679042274 a6989586621679042275 a6989586621679042276 = '(a6989586621679042270,
                                                                                                                                                                    a6989586621679042271,
                                                                                                                                                                    a6989586621679042272,
                                                                                                                                                                    a6989586621679042273,
                                                                                                                                                                    a6989586621679042274,
                                                                                                                                                                    a6989586621679042275,
                                                                                                                                                                    a6989586621679042276)
type STuple7 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type)
                        (d_14 :: Type)
                        (e_15 :: Type)
                        (f_16 :: Type)
                        (g_17 :: Type). (a_11, b_12, c_13, d_14, e_15, f_16, g_17) -> Type
data STuple7 :: forall (a_11 :: Type)
                        (b_12 :: Type)
                        (c_13 :: Type)
                        (d_14 :: Type)
                        (e_15 :: Type)
                        (f_16 :: Type)
                        (g_17 :: Type).
                (a_11, b_12, c_13, d_14, e_15, f_16, g_17) -> Type
  where
    STuple7 :: forall (a_11 :: Type)
                      (b_12 :: Type)
                      (c_13 :: Type)
                      (d_14 :: Type)
                      (e_15 :: Type)
                      (f_16 :: Type)
                      (g_17 :: Type)
                      (n_a8rX :: a_11)
                      (n_a8rY :: b_12)
                      (n_a8rZ :: c_13)
                      (n_a8s0 :: d_14)
                      (n_a8s1 :: e_15)
                      (n_a8s2 :: f_16)
                      (n_a8s3 :: g_17).
                (Sing n_a8rX) ->
                (Sing n_a8rY) ->
                (Sing n_a8rZ) ->
                (Sing n_a8s0) ->
                (Sing n_a8s1) ->
                (Sing n_a8s2) ->
                (Sing n_a8s3) ->
                STuple7 ('(n_a8rX,
                          n_a8rY,
                          n_a8rZ,
                          n_a8s0,
                          n_a8s1,
                          n_a8s2,
                          n_a8s3) :: (a_11, b_12, c_13, d_14, e_15, f_16, g_17))
type instance Sing @(a_11, b_12, c_13, d_14, e_15, f_16,
                      g_17) = STuple7
instance (SingKind a_11,
          SingKind b_12,
          SingKind c_13,
          SingKind d_14,
          SingKind e_15,
          SingKind f_16,
          SingKind g_17) =>
          SingKind (a_11, b_12, c_13, d_14, e_15, f_16, g_17) where
  type Demote (a_11, b_12, c_13, d_14, e_15, f_16,
                g_17) = (Demote a_11, Demote b_12, Demote c_13, Demote d_14,
                        Demote e_15, Demote f_16, Demote g_17)
  fromSing (STuple7 b_a8sr b_a8ss b_a8st b_a8su b_a8sv b_a8sw b_a8sx)
    = (,,,,,,)
        (fromSing b_a8sr) (fromSing b_a8ss) (fromSing b_a8st)
        (fromSing b_a8su) (fromSing b_a8sv) (fromSing b_a8sw)
        (fromSing b_a8sx)
  toSing
    ((,,,,,,) (b_a8sz :: Demote a_11) (b_a8sA :: Demote b_12)
              (b_a8sB :: Demote c_13) (b_a8sC :: Demote d_14)
              (b_a8sD :: Demote e_15) (b_a8sE :: Demote f_16)
              (b_a8sF :: Demote g_17))
    = (\cases
          (SomeSing c_a8sG)
            (SomeSing c_a8sH)
            (SomeSing c_a8sI)
            (SomeSing c_a8sJ)
            (SomeSing c_a8sK)
            (SomeSing c_a8sL)
            (SomeSing c_a8sM)
            -> SomeSing
                (STuple7 c_a8sG c_a8sH c_a8sI c_a8sJ c_a8sK c_a8sL c_a8sM))
        (toSing b_a8sz :: SomeSing a_11) (toSing b_a8sA :: SomeSing b_12)
        (toSing b_a8sB :: SomeSing c_13) (toSing b_a8sC :: SomeSing d_14)
        (toSing b_a8sD :: SomeSing e_15) (toSing b_a8sE :: SomeSing f_16)
        (toSing b_a8sF :: SomeSing g_17)
instance (SingI n_a8rX,
          SingI n_a8rY,
          SingI n_a8rZ,
          SingI n_a8s0,
          SingI n_a8s1,
          SingI n_a8s2,
          SingI n_a8s3) =>
          SingI '(n_a8rX :: a_11,
                  n_a8rY :: b_12,
                  n_a8rZ :: c_13,
                  n_a8s0 :: d_14,
                  n_a8s1 :: e_15,
                  n_a8s2 :: f_16,
                  n_a8s3 :: g_17) where
  sing = STuple7 sing sing sing sing sing sing sing
instance (SingI n_a8rX,
          SingI n_a8rY,
          SingI n_a8rZ,
          SingI n_a8s0,
          SingI n_a8s1,
          SingI n_a8s2) =>
          SingI1 ('(,,,,,,) (n_a8rX :: a_11) (n_a8rY :: b_12) (n_a8rZ :: c_13) (n_a8s0 :: d_14) (n_a8s1 :: e_15) (n_a8s2 :: f_16)) where
  liftSing = STuple7 sing sing sing sing sing sing
instance (SingI n_a8rX,
          SingI n_a8rY,
          SingI n_a8rZ,
          SingI n_a8s0,
          SingI n_a8s1) =>
          SingI2 ('(,,,,,,) (n_a8rX :: a_11) (n_a8rY :: b_12) (n_a8rZ :: c_13) (n_a8s0 :: d_14) (n_a8s1 :: e_15)) where
  liftSing2 = STuple7 sing sing sing sing sing
instance SingI (Tuple7Sym0 :: (~>) a_11 ((~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                            b_12,
                                                                                                            c_13,
                                                                                                            d_14,
                                                                                                            e_15,
                                                                                                            f_16,
                                                                                                            g_17)))))))) where
  sing = singFun7 @Tuple7Sym0 STuple7
instance SingI d_a8s4 =>
          SingI (Tuple7Sym1 (d_a8s4 :: a_11) :: (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                  b_12,
                                                                                                                  c_13,
                                                                                                                  d_14,
                                                                                                                  e_15,
                                                                                                                  f_16,
                                                                                                                  g_17))))))) where
  sing
    = singFun6 @(Tuple7Sym1 (d_a8s4 :: a_11)) (STuple7 (sing @d_a8s4))
instance SingI1 (Tuple7Sym1 :: a_11
                                -> (~>) b_12 ((~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                    b_12,
                                                                                                    c_13,
                                                                                                    d_14,
                                                                                                    e_15,
                                                                                                    f_16,
                                                                                                    g_17))))))) where
  liftSing (s_a8sq :: Sing (d_a8s4 :: a_11))
    = singFun6 @(Tuple7Sym1 (d_a8s4 :: a_11)) (STuple7 s_a8sq)
instance (SingI d_a8s4, SingI d_a8s5) =>
          SingI (Tuple7Sym2 (d_a8s4 :: a_11) (d_a8s5 :: b_12) :: (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                        b_12,
                                                                                                                        c_13,
                                                                                                                        d_14,
                                                                                                                        e_15,
                                                                                                                        f_16,
                                                                                                                        g_17)))))) where
  sing
    = singFun5
        @(Tuple7Sym2 (d_a8s4 :: a_11) (d_a8s5 :: b_12))
        (STuple7 (sing @d_a8s4) (sing @d_a8s5))
instance SingI d_a8s4 =>
          SingI1 (Tuple7Sym2 (d_a8s4 :: a_11) :: b_12
                                                -> (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                          b_12,
                                                                                                          c_13,
                                                                                                          d_14,
                                                                                                          e_15,
                                                                                                          f_16,
                                                                                                          g_17)))))) where
  liftSing (s_a8sn :: Sing (d_a8s5 :: b_12))
    = singFun5
        @(Tuple7Sym2 (d_a8s4 :: a_11) (d_a8s5 :: b_12))
        (STuple7 (sing @d_a8s4) s_a8sn)
instance SingI2 (Tuple7Sym2 :: a_11
                                -> b_12
                                  -> (~>) c_13 ((~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                            b_12,
                                                                                            c_13,
                                                                                            d_14,
                                                                                            e_15,
                                                                                            f_16,
                                                                                            g_17)))))) where
  liftSing2
    (s_a8so :: Sing (d_a8s4 :: a_11))
    (s_a8sp :: Sing (d_a8s5 :: b_12))
    = singFun5
        @(Tuple7Sym2 (d_a8s4 :: a_11) (d_a8s5 :: b_12))
        (STuple7 s_a8so s_a8sp)
instance (SingI d_a8s4, SingI d_a8s5, SingI d_a8s6) =>
          SingI (Tuple7Sym3 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) :: (~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                              b_12,
                                                                                                                              c_13,
                                                                                                                              d_14,
                                                                                                                              e_15,
                                                                                                                              f_16,
                                                                                                                              g_17))))) where
  sing
    = singFun4
        @(Tuple7Sym3 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13))
        (STuple7 (sing @d_a8s4) (sing @d_a8s5) (sing @d_a8s6))
instance (SingI d_a8s4, SingI d_a8s5) =>
          SingI1 (Tuple7Sym3 (d_a8s4 :: a_11) (d_a8s5 :: b_12) :: c_13
                                                                  -> (~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                b_12,
                                                                                                                c_13,
                                                                                                                d_14,
                                                                                                                e_15,
                                                                                                                f_16,
                                                                                                                g_17))))) where
  liftSing (s_a8sk :: Sing (d_a8s6 :: c_13))
    = singFun4
        @(Tuple7Sym3 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13))
        (STuple7 (sing @d_a8s4) (sing @d_a8s5) s_a8sk)
instance SingI d_a8s4 =>
          SingI2 (Tuple7Sym3 (d_a8s4 :: a_11) :: b_12
                                                -> c_13
                                                    -> (~>) d_14 ((~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                  b_12,
                                                                                                  c_13,
                                                                                                  d_14,
                                                                                                  e_15,
                                                                                                  f_16,
                                                                                                  g_17))))) where
  liftSing2
    (s_a8sl :: Sing (d_a8s5 :: b_12))
    (s_a8sm :: Sing (d_a8s6 :: c_13))
    = singFun4
        @(Tuple7Sym3 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13))
        (STuple7 (sing @d_a8s4) s_a8sl s_a8sm)
instance (SingI d_a8s4,
          SingI d_a8s5,
          SingI d_a8s6,
          SingI d_a8s7) =>
          SingI (Tuple7Sym4 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) :: (~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                                    b_12,
                                                                                                                                    c_13,
                                                                                                                                    d_14,
                                                                                                                                    e_15,
                                                                                                                                    f_16,
                                                                                                                                    g_17)))) where
  sing
    = singFun3
        @(Tuple7Sym4 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14))
        (STuple7
            (sing @d_a8s4) (sing @d_a8s5) (sing @d_a8s6) (sing @d_a8s7))
instance (SingI d_a8s4, SingI d_a8s5, SingI d_a8s6) =>
          SingI1 (Tuple7Sym4 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) :: d_14
                                                                                  -> (~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                                      b_12,
                                                                                                                      c_13,
                                                                                                                      d_14,
                                                                                                                      e_15,
                                                                                                                      f_16,
                                                                                                                      g_17)))) where
  liftSing (s_a8sh :: Sing (d_a8s7 :: d_14))
    = singFun3
        @(Tuple7Sym4 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14))
        (STuple7 (sing @d_a8s4) (sing @d_a8s5) (sing @d_a8s6) s_a8sh)
instance (SingI d_a8s4, SingI d_a8s5) =>
          SingI2 (Tuple7Sym4 (d_a8s4 :: a_11) (d_a8s5 :: b_12) :: c_13
                                                                  -> d_14
                                                                    -> (~>) e_15 ((~>) f_16 ((~>) g_17 (a_11,
                                                                                                        b_12,
                                                                                                        c_13,
                                                                                                        d_14,
                                                                                                        e_15,
                                                                                                        f_16,
                                                                                                        g_17)))) where
  liftSing2
    (s_a8si :: Sing (d_a8s6 :: c_13))
    (s_a8sj :: Sing (d_a8s7 :: d_14))
    = singFun3
        @(Tuple7Sym4 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14))
        (STuple7 (sing @d_a8s4) (sing @d_a8s5) s_a8si s_a8sj)
instance (SingI d_a8s4,
          SingI d_a8s5,
          SingI d_a8s6,
          SingI d_a8s7,
          SingI d_a8s8) =>
          SingI (Tuple7Sym5 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) (d_a8s8 :: e_15) :: (~>) f_16 ((~>) g_17 (a_11,
                                                                                                                                          b_12,
                                                                                                                                          c_13,
                                                                                                                                          d_14,
                                                                                                                                          e_15,
                                                                                                                                          f_16,
                                                                                                                                          g_17))) where
  sing
    = singFun2
        @(Tuple7Sym5 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) (d_a8s8 :: e_15))
        (STuple7
            (sing @d_a8s4) (sing @d_a8s5) (sing @d_a8s6) (sing @d_a8s7)
            (sing @d_a8s8))
instance (SingI d_a8s4,
          SingI d_a8s5,
          SingI d_a8s6,
          SingI d_a8s7) =>
          SingI1 (Tuple7Sym5 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) :: e_15
                                                                                                    -> (~>) f_16 ((~>) g_17 (a_11,
                                                                                                                            b_12,
                                                                                                                            c_13,
                                                                                                                            d_14,
                                                                                                                            e_15,
                                                                                                                            f_16,
                                                                                                                            g_17))) where
  liftSing (s_a8se :: Sing (d_a8s8 :: e_15))
    = singFun2
        @(Tuple7Sym5 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) (d_a8s8 :: e_15))
        (STuple7
            (sing @d_a8s4) (sing @d_a8s5) (sing @d_a8s6) (sing @d_a8s7) s_a8se)
instance (SingI d_a8s4, SingI d_a8s5, SingI d_a8s6) =>
          SingI2 (Tuple7Sym5 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) :: d_14
                                                                                  -> e_15
                                                                                      -> (~>) f_16 ((~>) g_17 (a_11,
                                                                                                              b_12,
                                                                                                              c_13,
                                                                                                              d_14,
                                                                                                              e_15,
                                                                                                              f_16,
                                                                                                              g_17))) where
  liftSing2
    (s_a8sf :: Sing (d_a8s7 :: d_14))
    (s_a8sg :: Sing (d_a8s8 :: e_15))
    = singFun2
        @(Tuple7Sym5 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) (d_a8s8 :: e_15))
        (STuple7
            (sing @d_a8s4) (sing @d_a8s5) (sing @d_a8s6) s_a8sf s_a8sg)
instance (SingI d_a8s4,
          SingI d_a8s5,
          SingI d_a8s6,
          SingI d_a8s7,
          SingI d_a8s8,
          SingI d_a8s9) =>
          SingI (Tuple7Sym6 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) (d_a8s8 :: e_15) (d_a8s9 :: f_16) :: (~>) g_17 (a_11,
                                                                                                                                                b_12,
                                                                                                                                                c_13,
                                                                                                                                                d_14,
                                                                                                                                                e_15,
                                                                                                                                                f_16,
                                                                                                                                                g_17)) where
  sing
    = singFun1
        @(Tuple7Sym6 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) (d_a8s8 :: e_15) (d_a8s9 :: f_16))
        (STuple7
            (sing @d_a8s4) (sing @d_a8s5) (sing @d_a8s6) (sing @d_a8s7)
            (sing @d_a8s8) (sing @d_a8s9))
instance (SingI d_a8s4,
          SingI d_a8s5,
          SingI d_a8s6,
          SingI d_a8s7,
          SingI d_a8s8) =>
          SingI1 (Tuple7Sym6 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) (d_a8s8 :: e_15) :: f_16
                                                                                                                    -> (~>) g_17 (a_11,
                                                                                                                                  b_12,
                                                                                                                                  c_13,
                                                                                                                                  d_14,
                                                                                                                                  e_15,
                                                                                                                                  f_16,
                                                                                                                                  g_17)) where
  liftSing (s_a8sb :: Sing (d_a8s9 :: f_16))
    = singFun1
        @(Tuple7Sym6 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) (d_a8s8 :: e_15) (d_a8s9 :: f_16))
        (STuple7
            (sing @d_a8s4) (sing @d_a8s5) (sing @d_a8s6) (sing @d_a8s7)
            (sing @d_a8s8) s_a8sb)
instance (SingI d_a8s4,
          SingI d_a8s5,
          SingI d_a8s6,
          SingI d_a8s7) =>
          SingI2 (Tuple7Sym6 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) :: e_15
                                                                                                    -> f_16
                                                                                                      -> (~>) g_17 (a_11,
                                                                                                                    b_12,
                                                                                                                    c_13,
                                                                                                                    d_14,
                                                                                                                    e_15,
                                                                                                                    f_16,
                                                                                                                    g_17)) where
  liftSing2
    (s_a8sc :: Sing (d_a8s8 :: e_15))
    (s_a8sd :: Sing (d_a8s9 :: f_16))
    = singFun1
        @(Tuple7Sym6 (d_a8s4 :: a_11) (d_a8s5 :: b_12) (d_a8s6 :: c_13) (d_a8s7 :: d_14) (d_a8s8 :: e_15) (d_a8s9 :: f_16))
        (STuple7
            (sing @d_a8s4) (sing @d_a8s5) (sing @d_a8s6) (sing @d_a8s7) s_a8sc
            s_a8sd)
type IdentitySym0 :: forall (a_a8sO :: Type). (~>) a_a8sO (Data.Functor.Identity.Identity a_a8sO)
data IdentitySym0 :: (~>) a_a8sO (Data.Functor.Identity.Identity a_a8sO)
  where
    IdentitySym0KindInference :: SameKind (Apply IdentitySym0 arg_a8sU) (IdentitySym1 arg_a8sU) =>
                                  IdentitySym0 a6989586621679042337
type instance Apply @a_a8sO @(Data.Functor.Identity.Identity a_a8sO) IdentitySym0 a6989586621679042337 = 'Data.Functor.Identity.Identity a6989586621679042337
instance SuppressUnusedWarnings IdentitySym0 where
  suppressUnusedWarnings = snd ((,) IdentitySym0KindInference ())
type IdentitySym1 :: forall (a_a8sO :: Type). a_a8sO
                                              -> Data.Functor.Identity.Identity a_a8sO
type family IdentitySym1 @(a_a8sO :: Type) (a6989586621679042337 :: a_a8sO) :: Data.Functor.Identity.Identity a_a8sO where
  IdentitySym1 a6989586621679042337 = 'Data.Functor.Identity.Identity a6989586621679042337
type RunIdentitySym0 :: forall (a_a8sO :: Type). (~>) (Data.Functor.Identity.Identity a_a8sO) a_a8sO
data RunIdentitySym0 :: (~>) (Data.Functor.Identity.Identity a_a8sO) a_a8sO
  where
    RunIdentitySym0KindInference :: SameKind (Apply RunIdentitySym0 arg_a8sX) (RunIdentitySym1 arg_a8sX) =>
                                    RunIdentitySym0 a6989586621679042340
type instance Apply @(Data.Functor.Identity.Identity a_a8sO) @a_a8sO RunIdentitySym0 a6989586621679042340 = RunIdentity a6989586621679042340
instance SuppressUnusedWarnings RunIdentitySym0 where
  suppressUnusedWarnings = snd ((,) RunIdentitySym0KindInference ())
type RunIdentitySym1 :: forall (a_a8sO :: Type). Data.Functor.Identity.Identity a_a8sO
                                                  -> a_a8sO
type family RunIdentitySym1 @(a_a8sO :: Type) (a6989586621679042340 :: Data.Functor.Identity.Identity a_a8sO) :: a_a8sO where
  RunIdentitySym1 a6989586621679042340 = RunIdentity a6989586621679042340
type RunIdentity :: forall (a_a8sO :: Type). Data.Functor.Identity.Identity a_a8sO
                                              -> a_a8sO
type family RunIdentity @(a_a8sO :: Type) (a_a8sW :: Data.Functor.Identity.Identity a_a8sO) :: a_a8sO where
  RunIdentity @a_a8sO ('Data.Functor.Identity.Identity field_a8sZ :: Data.Functor.Identity.Identity a_a8sO) = field_a8sZ
sRunIdentity ::
  forall (a_a8sO :: Type)
          (t_a8t0 :: Data.Functor.Identity.Identity a_a8sO). Sing t_a8t0
                                                            -> Sing (RunIdentity t_a8t0 :: a_a8sO)
sRunIdentity (SIdentity (sField :: Sing field_a8sZ)) = sField
instance SingI (RunIdentitySym0 :: (~>) (Data.Functor.Identity.Identity a_a8sO) a_a8sO) where
  sing = singFun1 @RunIdentitySym0 sRunIdentity
type SIdentity :: forall (a_a8sO :: Type). Data.Functor.Identity.Identity a_a8sO
                                            -> Type
data SIdentity :: forall (a_a8sO :: Type).
                  Data.Functor.Identity.Identity a_a8sO -> Type
  where
    SIdentity :: forall (a_a8sO :: Type) (n_a8t2 :: a_a8sO).
                  (Sing n_a8t2) ->
                  SIdentity ('Data.Functor.Identity.Identity n_a8t2 :: Data.Functor.Identity.Identity a_a8sO)
type instance Sing @(Data.Functor.Identity.Identity a_a8sO) = SIdentity
instance SingKind a_a8sO =>
          SingKind (Data.Functor.Identity.Identity a_a8sO) where
  type Demote (Data.Functor.Identity.Identity a_a8sO) = Data.Functor.Identity.Identity (Demote a_a8sO)
  fromSing (SIdentity b_a8t4)
    = Data.Functor.Identity.Identity (fromSing b_a8t4)
  toSing (Data.Functor.Identity.Identity (b_a8t6 :: Demote a_a8sO))
    = (\cases (SomeSing c_a8t7) -> SomeSing (SIdentity c_a8t7))
        (toSing b_a8t6 :: SomeSing a_a8sO)
instance SingI n_a8t2 =>
          SingI ('Data.Functor.Identity.Identity (n_a8t2 :: a_a8sO)) where
  sing = SIdentity sing
instance SingI1 'Data.Functor.Identity.Identity where
  liftSing = SIdentity
instance SingI (IdentitySym0 :: (~>) a_a8sO (Data.Functor.Identity.Identity a_a8sO)) where
  sing = singFun1 @IdentitySym0 SIdentity
type FalseSym0 :: Bool
type family FalseSym0 :: Bool where
  FalseSym0 = 'False
type TrueSym0 :: Bool
type family TrueSym0 :: Bool where
  TrueSym0 = 'True
type SBool :: Bool -> Type
data SBool :: Bool -> Type
  where
    SFalse :: SBool ('False :: Bool)
    STrue :: SBool ('True :: Bool)
type instance Sing @Bool = SBool
instance SingKind Bool where
  type Demote Bool = Bool
  fromSing SFalse = False
  fromSing STrue = True
  toSing False = SomeSing SFalse
  toSing True = SomeSing STrue
instance SingI 'False where
  sing = SFalse
instance SingI 'True where
  sing = STrue
type LTSym0 :: Ordering
type family LTSym0 :: Ordering where
  LTSym0 = 'LT
type EQSym0 :: Ordering
type family EQSym0 :: Ordering where
  EQSym0 = 'EQ
type GTSym0 :: Ordering
type family GTSym0 :: Ordering where
  GTSym0 = 'GT
type SOrdering :: Ordering -> Type
data SOrdering :: Ordering -> Type
  where
    SLT :: SOrdering ('LT :: Ordering)
    SEQ :: SOrdering ('EQ :: Ordering)
    SGT :: SOrdering ('GT :: Ordering)
type instance Sing @Ordering = SOrdering
instance SingKind Ordering where
  type Demote Ordering = Ordering
  fromSing SLT = LT
  fromSing SEQ = EQ
  fromSing SGT = GT
  toSing LT = SomeSing SLT
  toSing EQ = SomeSing SEQ
  toSing GT = SomeSing SGT
instance SingI 'LT where
  sing = SLT
instance SingI 'EQ where
  sing = SEQ
instance SingI 'GT where
  sing = SGT
type Tuple0Sym0 :: ()
type family Tuple0Sym0 :: () where
  Tuple0Sym0 = '()
type STuple0 :: () -> Type
data STuple0 :: () -> Type where STuple0 :: STuple0 ('() :: ())
type instance Sing @() = STuple0
instance SingKind () where
  type Demote () = ()
  fromSing STuple0 = ()
  toSing () = SomeSing STuple0
instance SingI '() where
  sing = STuple0

instance SDecide a_11 => SDecide (Maybe a_11) where
  (%~) SNothing SNothing = Proved Refl
  (%~) SNothing (SJust _) = Disproved (\case)
  (%~) (SJust _) SNothing = Disproved (\case)
  (%~) (SJust a_aftJ) (SJust b_aftK)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_aftL)
            -> Disproved (\cases Refl -> contra_aftL Refl))
        ((%~) a_aftJ b_aftK)
instance Eq (SMaybe (z_aftU :: Maybe a_11)) where
  (==) _ _ = True
instance SDecide a_11 =>
          Data.Type.Equality.TestEquality (SMaybe :: Maybe a_11
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_11 =>
          Data.Type.Coercion.TestCoercion (SMaybe :: Maybe a_11
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance (SDecide a_11, SDecide [a_11]) => SDecide [a_11] where
  (%~) SNil SNil = Proved Refl
  (%~) SNil (SCons _ _) = Disproved (\case)
  (%~) (SCons _ _) SNil = Disproved (\case)
  (%~) (SCons a_afui a_afuj) (SCons b_afuk b_aful)
    = (\cases
          (Proved Refl) (Proved Refl) -> Proved Refl
          (Disproved contra_afum) _
            -> Disproved (\cases Refl -> contra_afum Refl)
          _ (Disproved contra_afum)
            -> Disproved (\cases Refl -> contra_afum Refl))
        ((%~) a_afui b_afuk) ((%~) a_afuj b_aful)
instance Eq (SList (z_afuv :: [a_11])) where
  (==) _ _ = True
instance (SDecide a_11, SDecide [a_11]) =>
          Data.Type.Equality.TestEquality (SList :: [a_11] -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide a_11, SDecide [a_11]) =>
          Data.Type.Coercion.TestCoercion (SList :: [a_11] -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance (SDecide a_a8ep, SDecide b_a8eq) =>
          SDecide (Either a_a8ep b_a8eq) where
  (%~) (SLeft a_afuU) (SLeft b_afuV)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_afuW)
            -> Disproved (\cases Refl -> contra_afuW Refl))
        ((%~) a_afuU b_afuV)
  (%~) (SLeft _) (SRight _) = Disproved (\case)
  (%~) (SRight _) (SLeft _) = Disproved (\case)
  (%~) (SRight a_afuX) (SRight b_afuY)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_afuZ)
            -> Disproved (\cases Refl -> contra_afuZ Refl))
        ((%~) a_afuX b_afuY)
instance Eq (SEither (z_afvg :: Either a_a8ep b_a8eq)) where
  (==) _ _ = True
instance (SDecide a_a8ep, SDecide b_a8eq) =>
          Data.Type.Equality.TestEquality (SEither :: Either a_a8ep b_a8eq
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide a_a8ep, SDecide b_a8eq) =>
          Data.Type.Coercion.TestCoercion (SEither :: Either a_a8ep b_a8eq
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance (SDecide a_a8fb, SDecide [a_a8fb]) =>
          SDecide (GHC.Base.NonEmpty a_a8fb) where
  (%~) ((:%|) a_afvT a_afvU) ((:%|) b_afvV b_afvW)
    = (\cases
          (Proved Refl) (Proved Refl) -> Proved Refl
          (Disproved contra_afvX) _
            -> Disproved (\cases Refl -> contra_afvX Refl)
          _ (Disproved contra_afvX)
            -> Disproved (\cases Refl -> contra_afvX Refl))
        ((%~) a_afvT b_afvV) ((%~) a_afvU b_afvW)
instance Eq (SNonEmpty (z_afw0 :: GHC.Base.NonEmpty a_a8fb)) where
  (==) _ _ = True
instance (SDecide a_a8fb, SDecide [a_a8fb]) =>
          Data.Type.Equality.TestEquality (SNonEmpty :: GHC.Base.NonEmpty a_a8fb
                                                        -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide a_a8fb, SDecide [a_a8fb]) =>
          Data.Type.Coercion.TestCoercion (SNonEmpty :: GHC.Base.NonEmpty a_a8fb
                                                        -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide Void where
  (%~) x_afw5 _ = Proved ((\case) x_afw5)
instance Eq (SVoid (z_afw6 :: Void)) where
  (==) _ _ = True
instance Data.Type.Equality.TestEquality (SVoid :: Void
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance Data.Type.Coercion.TestCoercion (SVoid :: Void
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance (SDecide a_11, SDecide b_12) => SDecide (a_11, b_12) where
  (%~) (STuple2 a_afwe a_afwf) (STuple2 b_afwg b_afwh)
    = (\cases
          (Proved Refl) (Proved Refl) -> Proved Refl
          (Disproved contra_afwi) _
            -> Disproved (\cases Refl -> contra_afwi Refl)
          _ (Disproved contra_afwi)
            -> Disproved (\cases Refl -> contra_afwi Refl))
        ((%~) a_afwe b_afwg) ((%~) a_afwf b_afwh)
instance Eq (STuple2 (z_afwn :: (a_11, b_12))) where
  (==) _ _ = True
instance (SDecide a_11, SDecide b_12) =>
          Data.Type.Equality.TestEquality (STuple2 :: (a_11, b_12)
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide a_11, SDecide b_12) =>
          Data.Type.Coercion.TestCoercion (STuple2 :: (a_11, b_12)
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance (SDecide a_11, SDecide b_12, SDecide c_13) =>
          SDecide (a_11, b_12, c_13) where
  (%~) (STuple3 a_afwJ a_afwK a_afwL) (STuple3 b_afwM b_afwN b_afwO)
    = (\cases
          (Proved Refl) (Proved Refl) (Proved Refl) -> Proved Refl
          (Disproved contra_afwP) _ _
            -> Disproved (\cases Refl -> contra_afwP Refl)
          _ (Disproved contra_afwP) _
            -> Disproved (\cases Refl -> contra_afwP Refl)
          _ _ (Disproved contra_afwP)
            -> Disproved (\cases Refl -> contra_afwP Refl))
        ((%~) a_afwJ b_afwM) ((%~) a_afwK b_afwN) ((%~) a_afwL b_afwO)
instance Eq (STuple3 (z_afwW :: (a_11, b_12, c_13))) where
  (==) _ _ = True
instance (SDecide a_11, SDecide b_12, SDecide c_13) =>
          Data.Type.Equality.TestEquality (STuple3 :: (a_11, b_12, c_13)
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide a_11, SDecide b_12, SDecide c_13) =>
          Data.Type.Coercion.TestCoercion (STuple3 :: (a_11, b_12, c_13)
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14) =>
          SDecide (a_11, b_12, c_13, d_14) where
  (%~)
    (STuple4 a_afxs a_afxt a_afxu a_afxv)
    (STuple4 b_afxw b_afxx b_afxy b_afxz)
    = (\cases
          (Proved Refl) (Proved Refl) (Proved Refl) (Proved Refl)
            -> Proved Refl
          (Disproved contra_afxA) _ _ _
            -> Disproved (\cases Refl -> contra_afxA Refl)
          _ (Disproved contra_afxA) _ _
            -> Disproved (\cases Refl -> contra_afxA Refl)
          _ _ (Disproved contra_afxA) _
            -> Disproved (\cases Refl -> contra_afxA Refl)
          _ _ _ (Disproved contra_afxA)
            -> Disproved (\cases Refl -> contra_afxA Refl))
        ((%~) a_afxs b_afxw) ((%~) a_afxt b_afxx) ((%~) a_afxu b_afxy)
        ((%~) a_afxv b_afxz)
instance Eq (STuple4 (z_afxJ :: (a_11, b_12, c_13, d_14))) where
  (==) _ _ = True
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14) =>
          Data.Type.Equality.TestEquality (STuple4 :: (a_11, b_12, c_13,
                                                      d_14)
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14) =>
          Data.Type.Coercion.TestCoercion (STuple4 :: (a_11, b_12, c_13,
                                                      d_14)
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14,
          SDecide e_15) =>
          SDecide (a_11, b_12, c_13, d_14, e_15) where
  (%~)
    (STuple5 a_afyp a_afyq a_afyr a_afys a_afyt)
    (STuple5 b_afyu b_afyv b_afyw b_afyx b_afyy)
    = (\cases
          (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            -> Proved Refl
          (Disproved contra_afyz) _ _ _ _
            -> Disproved (\cases Refl -> contra_afyz Refl)
          _ (Disproved contra_afyz) _ _ _
            -> Disproved (\cases Refl -> contra_afyz Refl)
          _ _ (Disproved contra_afyz) _ _
            -> Disproved (\cases Refl -> contra_afyz Refl)
          _ _ _ (Disproved contra_afyz) _
            -> Disproved (\cases Refl -> contra_afyz Refl)
          _ _ _ _ (Disproved contra_afyz)
            -> Disproved (\cases Refl -> contra_afyz Refl))
        ((%~) a_afyp b_afyu) ((%~) a_afyq b_afyv) ((%~) a_afyr b_afyw)
        ((%~) a_afys b_afyx) ((%~) a_afyt b_afyy)
instance Eq (STuple5 (z_afyK :: (a_11, b_12, c_13, d_14,
                                  e_15))) where
  (==) _ _ = True
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14,
          SDecide e_15) =>
          Data.Type.Equality.TestEquality (STuple5 :: (a_11, b_12, c_13,
                                                      d_14, e_15)
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14,
          SDecide e_15) =>
          Data.Type.Coercion.TestCoercion (STuple5 :: (a_11, b_12, c_13,
                                                      d_14, e_15)
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14,
          SDecide e_15,
          SDecide f_16) =>
          SDecide (a_11, b_12, c_13, d_14, e_15, f_16) where
  (%~)
    (STuple6 a_afzA a_afzB a_afzC a_afzD a_afzE a_afzF)
    (STuple6 b_afzG b_afzH b_afzI b_afzJ b_afzK b_afzL)
    = (\cases
          (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            -> Proved Refl
          (Disproved contra_afzM) _ _ _ _ _
            -> Disproved (\cases Refl -> contra_afzM Refl)
          _ (Disproved contra_afzM) _ _ _ _
            -> Disproved (\cases Refl -> contra_afzM Refl)
          _ _ (Disproved contra_afzM) _ _ _
            -> Disproved (\cases Refl -> contra_afzM Refl)
          _ _ _ (Disproved contra_afzM) _ _
            -> Disproved (\cases Refl -> contra_afzM Refl)
          _ _ _ _ (Disproved contra_afzM) _
            -> Disproved (\cases Refl -> contra_afzM Refl)
          _ _ _ _ _ (Disproved contra_afzM)
            -> Disproved (\cases Refl -> contra_afzM Refl))
        ((%~) a_afzA b_afzG) ((%~) a_afzB b_afzH) ((%~) a_afzC b_afzI)
        ((%~) a_afzD b_afzJ) ((%~) a_afzE b_afzK) ((%~) a_afzF b_afzL)
instance Eq (STuple6 (z_afzZ :: (a_11, b_12, c_13, d_14, e_15,
                                  f_16))) where
  (==) _ _ = True
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14,
          SDecide e_15,
          SDecide f_16) =>
          Data.Type.Equality.TestEquality (STuple6 :: (a_11, b_12, c_13,
                                                      d_14, e_15, f_16)
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14,
          SDecide e_15,
          SDecide f_16) =>
          Data.Type.Coercion.TestCoercion (STuple6 :: (a_11, b_12, c_13,
                                                      d_14, e_15, f_16)
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14,
          SDecide e_15,
          SDecide f_16,
          SDecide g_17) =>
          SDecide (a_11, b_12, c_13, d_14, e_15, f_16, g_17) where
  (%~)
    (STuple7 a_afAZ a_afB0 a_afB1 a_afB2 a_afB3 a_afB4 a_afB5)
    (STuple7 b_afB6 b_afB7 b_afB8 b_afB9 b_afBa b_afBb b_afBc)
    = (\cases
          (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            (Proved Refl)
            -> Proved Refl
          (Disproved contra_afBd) _ _ _ _ _ _
            -> Disproved (\cases Refl -> contra_afBd Refl)
          _ (Disproved contra_afBd) _ _ _ _ _
            -> Disproved (\cases Refl -> contra_afBd Refl)
          _ _ (Disproved contra_afBd) _ _ _ _
            -> Disproved (\cases Refl -> contra_afBd Refl)
          _ _ _ (Disproved contra_afBd) _ _ _
            -> Disproved (\cases Refl -> contra_afBd Refl)
          _ _ _ _ (Disproved contra_afBd) _ _
            -> Disproved (\cases Refl -> contra_afBd Refl)
          _ _ _ _ _ (Disproved contra_afBd) _
            -> Disproved (\cases Refl -> contra_afBd Refl)
          _ _ _ _ _ _ (Disproved contra_afBd)
            -> Disproved (\cases Refl -> contra_afBd Refl))
        ((%~) a_afAZ b_afB6) ((%~) a_afB0 b_afB7) ((%~) a_afB1 b_afB8)
        ((%~) a_afB2 b_afB9) ((%~) a_afB3 b_afBa) ((%~) a_afB4 b_afBb)
        ((%~) a_afB5 b_afBc)
instance Eq (STuple7 (z_afBs :: (a_11, b_12, c_13, d_14, e_15,
                                  f_16, g_17))) where
  (==) _ _ = True
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14,
          SDecide e_15,
          SDecide f_16,
          SDecide g_17) =>
          Data.Type.Equality.TestEquality (STuple7 :: (a_11, b_12, c_13,
                                                      d_14, e_15, f_16, g_17)
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance (SDecide a_11,
          SDecide b_12,
          SDecide c_13,
          SDecide d_14,
          SDecide e_15,
          SDecide f_16,
          SDecide g_17) =>
          Data.Type.Coercion.TestCoercion (STuple7 :: (a_11, b_12, c_13,
                                                      d_14, e_15, f_16, g_17)
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide a_a8sO =>
          SDecide (Data.Functor.Identity.Identity a_a8sO) where
  (%~) (SIdentity a_afBY) (SIdentity b_afBZ)
    = (\cases
          (Proved Refl) -> Proved Refl
          (Disproved contra_afC0)
            -> Disproved (\cases Refl -> contra_afC0 Refl))
        ((%~) a_afBY b_afBZ)
instance Eq (SIdentity (z_afC3 :: Data.Functor.Identity.Identity a_a8sO)) where
  (==) _ _ = True
instance SDecide a_a8sO =>
          Data.Type.Equality.TestEquality (SIdentity :: Data.Functor.Identity.Identity a_a8sO
                                                        -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance SDecide a_a8sO =>
          Data.Type.Coercion.TestCoercion (SIdentity :: Data.Functor.Identity.Identity a_a8sO
                                                        -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide Bool where
  (%~) SFalse SFalse = Proved Refl
  (%~) SFalse STrue = Disproved (\case)
  (%~) STrue SFalse = Disproved (\case)
  (%~) STrue STrue = Proved Refl
instance Eq (SBool (z_afC8 :: Bool)) where
  (==) _ _ = True
instance Data.Type.Equality.TestEquality (SBool :: Bool
                                                    -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance Data.Type.Coercion.TestCoercion (SBool :: Bool
                                                    -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide Ordering where
  (%~) SLT SLT = Proved Refl
  (%~) SLT SEQ = Disproved (\case)
  (%~) SLT SGT = Disproved (\case)
  (%~) SEQ SLT = Disproved (\case)
  (%~) SEQ SEQ = Proved Refl
  (%~) SEQ SGT = Disproved (\case)
  (%~) SGT SLT = Disproved (\case)
  (%~) SGT SEQ = Disproved (\case)
  (%~) SGT SGT = Proved Refl
instance Eq (SOrdering (z_afC9 :: Ordering)) where
  (==) _ _ = True
instance Data.Type.Equality.TestEquality (SOrdering :: Ordering
                                                        -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance Data.Type.Coercion.TestCoercion (SOrdering :: Ordering
                                                        -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion
instance SDecide () where
  (%~) STuple0 STuple0 = Proved Refl
instance Eq (STuple0 (z_afCa :: ())) where
  (==) _ _ = True
instance Data.Type.Equality.TestEquality (STuple0 :: ()
                                                      -> Type) where
  testEquality
    = Data.Singletons.Decide.decideEquality
instance Data.Type.Coercion.TestCoercion (STuple0 :: ()
                                                      -> Type) where
  testCoercion
    = Data.Singletons.Decide.decideCoercion

deriving instance Data.Singletons.ShowSing.ShowSing a_11 =>
                  Show (SMaybe (z_ahf3 :: Maybe a_11))
deriving instance (Data.Singletons.ShowSing.ShowSing a_11,
                    Data.Singletons.ShowSing.ShowSing [a_11]) =>
                  Show (SList (z_ahfe :: [a_11]))
deriving instance (Data.Singletons.ShowSing.ShowSing a_a8ep,
                    Data.Singletons.ShowSing.ShowSing b_a8eq) =>
                  Show (SEither (z_ahfr :: Either a_a8ep b_a8eq))
deriving instance (Data.Singletons.ShowSing.ShowSing a_a8fb,
                    Data.Singletons.ShowSing.ShowSing [a_a8fb]) =>
                  Show (SNonEmpty (z_ahfJ :: GHC.Base.NonEmpty a_a8fb))
deriving instance Show (SVoid (z_ahfM :: Void))
deriving instance (Data.Singletons.ShowSing.ShowSing a_11,
                    Data.Singletons.ShowSing.ShowSing b_12) =>
                  Show (STuple2 (z_ahfP :: (a_11, b_12)))
deriving instance (Data.Singletons.ShowSing.ShowSing a_11,
                    Data.Singletons.ShowSing.ShowSing b_12,
                    Data.Singletons.ShowSing.ShowSing c_13) =>
                  Show (STuple3 (z_ahfX :: (a_11, b_12, c_13)))
deriving instance (Data.Singletons.ShowSing.ShowSing a_11,
                    Data.Singletons.ShowSing.ShowSing b_12,
                    Data.Singletons.ShowSing.ShowSing c_13,
                    Data.Singletons.ShowSing.ShowSing d_14) =>
                  Show (STuple4 (z_ahg8 :: (a_11, b_12, c_13, d_14)))
deriving instance (Data.Singletons.ShowSing.ShowSing a_11,
                    Data.Singletons.ShowSing.ShowSing b_12,
                    Data.Singletons.ShowSing.ShowSing c_13,
                    Data.Singletons.ShowSing.ShowSing d_14,
                    Data.Singletons.ShowSing.ShowSing e_15) =>
                  Show (STuple5 (z_ahgm :: (a_11, b_12, c_13, d_14, e_15)))
deriving instance (Data.Singletons.ShowSing.ShowSing a_11,
                    Data.Singletons.ShowSing.ShowSing b_12,
                    Data.Singletons.ShowSing.ShowSing c_13,
                    Data.Singletons.ShowSing.ShowSing d_14,
                    Data.Singletons.ShowSing.ShowSing e_15,
                    Data.Singletons.ShowSing.ShowSing f_16) =>
                  Show (STuple6 (z_ahgD :: (a_11, b_12, c_13, d_14, e_15, f_16)))
deriving instance (Data.Singletons.ShowSing.ShowSing a_11,
                    Data.Singletons.ShowSing.ShowSing b_12,
                    Data.Singletons.ShowSing.ShowSing c_13,
                    Data.Singletons.ShowSing.ShowSing d_14,
                    Data.Singletons.ShowSing.ShowSing e_15,
                    Data.Singletons.ShowSing.ShowSing f_16,
                    Data.Singletons.ShowSing.ShowSing g_17) =>
                  Show (STuple7 (z_ahgX :: (a_11, b_12, c_13, d_14, e_15, f_16,
                                            g_17)))
deriving instance Data.Singletons.ShowSing.ShowSing a_a8sO =>
                  Show (SIdentity (z_ahhd :: Data.Functor.Identity.Identity a_a8sO))
deriving instance Show (SBool (z_ahhg :: Bool))
deriving instance Show (SOrdering (z_ahhh :: Ordering))
deriving instance Show (STuple0 (z_ahhi :: ()))

data Let6989586621679078929LgoSym0 a6989586621679078884 b6989586621679078885 (f6989586621679078926 :: (~>) b6989586621679078885 ((~>) a6989586621679078884 b6989586621679078885)) (z06989586621679078927 :: b6989586621679078885) (xs06989586621679078928 :: [a6989586621679078884]) :: (~>) b6989586621679078885 ((~>) [a6989586621679078884] b6989586621679078885)
  where
    Let6989586621679078929LgoSym0KindInference :: SameKind (Apply (Let6989586621679078929LgoSym0 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928) arg_ahZa) (Let6989586621679078929LgoSym1 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 arg_ahZa) =>
                                                  Let6989586621679078929LgoSym0 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930
type instance Apply @b6989586621679078885 @((~>) [a6989586621679078884] b6989586621679078885) (Let6989586621679078929LgoSym0 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928) a6989586621679078930 = Let6989586621679078929LgoSym1 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930
instance SuppressUnusedWarnings (Let6989586621679078929LgoSym0 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679078929LgoSym0KindInference ())
data Let6989586621679078929LgoSym1 a6989586621679078884 b6989586621679078885 (f6989586621679078926 :: (~>) b6989586621679078885 ((~>) a6989586621679078884 b6989586621679078885)) (z06989586621679078927 :: b6989586621679078885) (xs06989586621679078928 :: [a6989586621679078884]) (a6989586621679078930 :: b6989586621679078885) :: (~>) [a6989586621679078884] b6989586621679078885
  where
    Let6989586621679078929LgoSym1KindInference :: SameKind (Apply (Let6989586621679078929LgoSym1 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930) arg_ahZa) (Let6989586621679078929LgoSym2 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930 arg_ahZa) =>
                                                  Let6989586621679078929LgoSym1 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930 a6989586621679078931
type instance Apply @[a6989586621679078884] @b6989586621679078885 (Let6989586621679078929LgoSym1 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930) a6989586621679078931 = Let6989586621679078929Lgo a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930 a6989586621679078931
instance SuppressUnusedWarnings (Let6989586621679078929LgoSym1 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679078929LgoSym1KindInference ())
type family Let6989586621679078929LgoSym2 a6989586621679078884 b6989586621679078885 (f6989586621679078926 :: (~>) b6989586621679078885 ((~>) a6989586621679078884 b6989586621679078885)) (z06989586621679078927 :: b6989586621679078885) (xs06989586621679078928 :: [a6989586621679078884]) (a6989586621679078930 :: b6989586621679078885) (a6989586621679078931 :: [a6989586621679078884]) :: b6989586621679078885 where
  Let6989586621679078929LgoSym2 a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930 a6989586621679078931 = Let6989586621679078929Lgo a6989586621679078884 b6989586621679078885 f6989586621679078926 z06989586621679078927 xs06989586621679078928 a6989586621679078930 a6989586621679078931
type family Let6989586621679078929Lgo a6989586621679078884 b6989586621679078885 (f6989586621679078926 :: (~>) b6989586621679078885 ((~>) a6989586621679078884 b6989586621679078885)) (z06989586621679078927 :: b6989586621679078885) (xs06989586621679078928 :: [a6989586621679078884]) (a_ahZ8 :: b6989586621679078885) (a_ahZ9 :: [a6989586621679078884]) :: b6989586621679078885 where
  Let6989586621679078929Lgo a_ahYo b_ahYp f_ahZ4 z0_ahZ5 xs0_ahZ6 z_ahZb '[] = z_ahZb
  Let6989586621679078929Lgo a_ahYo b_ahYp f_ahZ4 z0_ahZ5 xs0_ahZ6 z_ahZc ('(:) x_ahZd xs_ahZe) = Apply (Apply (Let6989586621679078929LgoSym0 a_ahYo b_ahYp f_ahZ4 z0_ahZ5 xs0_ahZ6) (Apply (Apply f_ahZ4 z_ahZc) x_ahZd)) xs_ahZe
type FoldlSym0 :: forall a_ahYo
                          b_ahYp. (~>) ((~>) b_ahYp ((~>) a_ahYo b_ahYp)) ((~>) b_ahYp ((~>) [a_ahYo] b_ahYp))
data FoldlSym0 :: (~>) ((~>) b_ahYp ((~>) a_ahYo b_ahYp)) ((~>) b_ahYp ((~>) [a_ahYo] b_ahYp))
  where
    FoldlSym0KindInference :: SameKind (Apply FoldlSym0 arg_ahZ0) (FoldlSym1 arg_ahZ0) =>
                              FoldlSym0 a6989586621679078923
type instance Apply @((~>) b_ahYp ((~>) a_ahYo b_ahYp)) @((~>) b_ahYp ((~>) [a_ahYo] b_ahYp)) FoldlSym0 a6989586621679078923 = FoldlSym1 a6989586621679078923
instance SuppressUnusedWarnings FoldlSym0 where
  suppressUnusedWarnings = snd ((,) FoldlSym0KindInference ())
type FoldlSym1 :: forall a_ahYo
                          b_ahYp. (~>) b_ahYp ((~>) a_ahYo b_ahYp)
                                  -> (~>) b_ahYp ((~>) [a_ahYo] b_ahYp)
data FoldlSym1 (a6989586621679078923 :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) :: (~>) b_ahYp ((~>) [a_ahYo] b_ahYp)
  where
    FoldlSym1KindInference :: SameKind (Apply (FoldlSym1 a6989586621679078923) arg_ahZ0) (FoldlSym2 a6989586621679078923 arg_ahZ0) =>
                              FoldlSym1 a6989586621679078923 a6989586621679078924
type instance Apply @b_ahYp @((~>) [a_ahYo] b_ahYp) (FoldlSym1 a6989586621679078923) a6989586621679078924 = FoldlSym2 a6989586621679078923 a6989586621679078924
instance SuppressUnusedWarnings (FoldlSym1 a6989586621679078923) where
  suppressUnusedWarnings = snd ((,) FoldlSym1KindInference ())
type FoldlSym2 :: forall a_ahYo
                          b_ahYp. (~>) b_ahYp ((~>) a_ahYo b_ahYp)
                                  -> b_ahYp -> (~>) [a_ahYo] b_ahYp
data FoldlSym2 (a6989586621679078923 :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) (a6989586621679078924 :: b_ahYp) :: (~>) [a_ahYo] b_ahYp
  where
    FoldlSym2KindInference :: SameKind (Apply (FoldlSym2 a6989586621679078923 a6989586621679078924) arg_ahZ0) (FoldlSym3 a6989586621679078923 a6989586621679078924 arg_ahZ0) =>
                              FoldlSym2 a6989586621679078923 a6989586621679078924 a6989586621679078925
type instance Apply @[a_ahYo] @b_ahYp (FoldlSym2 a6989586621679078923 a6989586621679078924) a6989586621679078925 = Foldl a6989586621679078923 a6989586621679078924 a6989586621679078925
instance SuppressUnusedWarnings (FoldlSym2 a6989586621679078923 a6989586621679078924) where
  suppressUnusedWarnings = snd ((,) FoldlSym2KindInference ())
type FoldlSym3 :: forall a_ahYo
                          b_ahYp. (~>) b_ahYp ((~>) a_ahYo b_ahYp)
                                  -> b_ahYp -> [a_ahYo] -> b_ahYp
type family FoldlSym3 @a_ahYo @b_ahYp (a6989586621679078923 :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) (a6989586621679078924 :: b_ahYp) (a6989586621679078925 :: [a_ahYo]) :: b_ahYp where
  FoldlSym3 a6989586621679078923 a6989586621679078924 a6989586621679078925 = Foldl a6989586621679078923 a6989586621679078924 a6989586621679078925
type Foldl :: forall a_ahYo
                      b_ahYp. (~>) b_ahYp ((~>) a_ahYo b_ahYp)
                              -> b_ahYp -> [a_ahYo] -> b_ahYp
type family Foldl @a_ahYo @b_ahYp (a_ahYX :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) (a_ahYY :: b_ahYp) (a_ahYZ :: [a_ahYo]) :: b_ahYp where
  Foldl @a_ahYo @b_ahYp (f_ahZ4 :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) (z0_ahZ5 :: b_ahYp) (xs0_ahZ6 :: [a_ahYo]) = Apply (Apply (Let6989586621679078929LgoSym0 a_ahYo b_ahYp f_ahZ4 z0_ahZ5 xs0_ahZ6) z0_ahZ5) xs0_ahZ6
sFoldl ::
  forall a_ahYo
          b_ahYp
          (t_ahZf :: (~>) b_ahYp ((~>) a_ahYo b_ahYp))
          (t_ahZg :: b_ahYp)
          (t_ahZh :: [a_ahYo]). Sing t_ahZf
                                -> Sing t_ahZg
                                  -> Sing t_ahZh -> Sing (Foldl t_ahZf t_ahZg t_ahZh :: b_ahYp)
sFoldl
  (sF :: Sing f_ahZ4)
  (sZ0 :: Sing z0_ahZ5)
  (sXs0 :: Sing xs0_ahZ6)
  = let
      sLgo ::
        (forall (t_ahZp :: b_ahYp) (t_ahZq :: [a_ahYo]).
          Sing t_ahZp
          -> Sing t_ahZq
            -> Sing (Let6989586621679078929Lgo a_ahYo b_ahYp f_ahZ4 z0_ahZ5 xs0_ahZ6 t_ahZp t_ahZq :: b_ahYp) :: Type)
      sLgo (sZ :: Sing z_ahZb) SNil = sZ
      sLgo
        (sZ :: Sing z_ahZc)
        (SCons (sX :: Sing x_ahZd) (sXs :: Sing xs_ahZe))
        = applySing
            (applySing
                (singFun2
                  @(Let6989586621679078929LgoSym0 a_ahYo b_ahYp f_ahZ4 z0_ahZ5 xs0_ahZ6)
                  sLgo)
                (applySing (applySing sF sZ) sX))
            sXs
    in
      applySing
        (applySing
            (singFun2
              @(Let6989586621679078929LgoSym0 a_ahYo b_ahYp f_ahZ4 z0_ahZ5 xs0_ahZ6)
              sLgo)
            sZ0)
        sXs0
instance SingI (FoldlSym0 :: (~>) ((~>) b_ahYp ((~>) a_ahYo b_ahYp)) ((~>) b_ahYp ((~>) [a_ahYo] b_ahYp))) where
  sing = singFun3 @FoldlSym0 sFoldl
instance SingI d_ahZi =>
          SingI (FoldlSym1 (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) :: (~>) b_ahYp ((~>) [a_ahYo] b_ahYp)) where
  sing
    = singFun2
        @(FoldlSym1 (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)))
        (sFoldl (sing @d_ahZi))
instance SingI1 (FoldlSym1 :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)
                              -> (~>) b_ahYp ((~>) [a_ahYo] b_ahYp)) where
  liftSing
    (s_ahZo :: Sing (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)))
    = singFun2
        @(FoldlSym1 (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)))
        (sFoldl s_ahZo)
instance (SingI d_ahZi, SingI d_ahZj) =>
          SingI (FoldlSym2 (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) (d_ahZj :: b_ahYp) :: (~>) [a_ahYo] b_ahYp) where
  sing
    = singFun1
        @(FoldlSym2 (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) (d_ahZj :: b_ahYp))
        (sFoldl (sing @d_ahZi) (sing @d_ahZj))
instance SingI d_ahZi =>
          SingI1 (FoldlSym2 (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) :: b_ahYp
                                                                            -> (~>) [a_ahYo] b_ahYp) where
  liftSing (s_ahZl :: Sing (d_ahZj :: b_ahYp))
    = singFun1
        @(FoldlSym2 (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) (d_ahZj :: b_ahYp))
        (sFoldl (sing @d_ahZi) s_ahZl)
instance SingI2 (FoldlSym2 :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)
                              -> b_ahYp -> (~>) [a_ahYo] b_ahYp) where
  liftSing2
    (s_ahZm :: Sing (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)))
    (s_ahZn :: Sing (d_ahZj :: b_ahYp))
    = singFun1
        @(FoldlSym2 (d_ahZi :: (~>) b_ahYp ((~>) a_ahYo b_ahYp)) (d_ahZj :: b_ahYp))
        (sFoldl s_ahZm s_ahZn)
