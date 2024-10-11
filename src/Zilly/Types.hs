
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ConstraintKinds          #-}
-- {-# LANGUAGE ConstraintKinds #-}

#ifndef WASM
{-# LANGUAGE TemplateHaskell          #-}
#endif


{-|
Module      : Zilly.Types
Description : Definition of types, properties and evidence injection for Zilly.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Defines the types of the Zilly language, provides some type level properties
and a way to inject them via continnuations.
-}
module Zilly.Types where


import Prelude.Singletons
    ( withSingI,
      SingI(..),
      SingKind(fromSing),
      (%&&),
      (%<$>),
      LiftA2Sym0,
      PMonad(type (>>=)),
      SApplicative(sLiftA2),
      type (&&@#@$),
      type (==@#@$),
      PEq(type (==)),
      SEq((%==)),
      type (<$>@#@$),
      FalseSym0,
      JustSym0,
      NothingSym0,
      SBool(SFalse, STrue),
      SMaybe(SJust, SNothing),
      TrueSym0 )
import Data.Singletons.Decide
import Control.Applicative (Const(..))
import Data.Kind (Type,Constraint)
import Data.Proof



---------------------------
-- Singletons definitions
---------------------------
#ifndef WASM
import Data.Singletons.TH  hiding (Const)
$(singletons [d|
  infixr 0 :->
  data Types 
      = Value Types0
      | Lazy Types 
      | LazyS Types
      | Array Types
    deriving (Eq)

  data Types0 
    = Z
    | F
    | (:->) Types Types
    deriving (Eq)

  lowerBound :: Types -> Types -> Maybe Types
  lowerBound (Array a) (Array b) = Array <$> lowerBound a b
  lowerBound (Lazy a) (Lazy b) =  Lazy <$> lowerBound a b
  lowerBound (Value (a :-> b)) (Value (c :-> d)) =  Value <$> liftA2 (:->) (upperBound a c ) (lowerBound b d)
  lowerBound (Value a) (Lazy b)  = lowerBound (Value a) b
  lowerBound (Lazy a)  (Value b) = lowerBound a (Value b)
  lowerBound (Value Z) (Value Z) = Just (Value Z)
  lowerBound (Value Z) (Value F) = Just (Value Z)
  lowerBound (Value F) (Value Z) = Just (Value Z)
  lowerBound (Value F) (Value F) = Just (Value F)
  lowerBound (Value Z) (Value (_ :-> _)) = Nothing
  lowerBound (Value (_ :-> _)) (Value Z) = Nothing
  lowerBound (Array _) (Value _)  = Nothing
  lowerBound (Value _) (Array _)  = Nothing
  lowerBound (Array _) (Lazy _)   = Nothing
  lowerBound (Lazy _) (Array _)   = Nothing
  lowerBound (Array _) (LazyS _)  = Nothing
  lowerBound (LazyS _) (Array _)  = Nothing



  upperBound :: Types -> Types -> Maybe Types
  upperBound (Array a) (Array b) = Array <$> upperBound a b
  upperBound (Value (a :-> b)) (Value (c :-> d))  =  Value <$> liftA2 (:->) (lowerBound a c) (upperBound b d)
  upperBound (Lazy a) (Lazy b)   =  Lazy <$> upperBound a b
  upperBound (Value a) (Lazy b)  =  Lazy <$> upperBound (Value a) b
  upperBound (Lazy a)  (Value b) =  Lazy <$> upperBound a (Value b)
  upperBound (Value Z) (Value Z) = Just (Value Z)
  upperBound (Value Z) (Value F) = Just (Value F)
  upperBound (Value F) (Value Z) = Just (Value F)
  upperBound (Value F) (Value F) = Just (Value F)
  upperBound (Value Z) (Value (_ :-> _)) = Nothing
  upperBound (Value (_ :-> _)) (Value Z) = Nothing
  upperBound (Array _) (Value _)  = Nothing
  upperBound (Value _) (Array _)  = Nothing
  upperBound (Array _) (Lazy _)   = Nothing
  upperBound (Lazy _) (Array _)   = Nothing
  upperBound (Array _) (LazyS _)  = Nothing
  upperBound (LazyS _) (Array _)  = Nothing


  baseType :: Types -> Types
  baseType (Array a)          = Array a
  baseType (Value Z)          = Value Z
  baseType (Value (a :-> b))  = Value (a :-> b)
  baseType (Lazy (Value a))   = Value a
  baseType (Lazy (Lazy a))    = baseType a
  baseType (Lazy (LazyS a))   = baseType a
  baseType (LazyS (Value a))  = Value a
  baseType (LazyS (Lazy a))   = baseType a
  baseType (LazyS (LazyS a))  = baseType a

  |])
#else
import qualified Data.Type.Coercion
import Data.Singletons
import Data.Singletons.TH
import Data.Kind (Type)
import qualified Data.Type.Equality
infixr 0 :->
data Types
  = Value Types0 |
    Lazy Types |
    LazyS Types
  deriving Eq
data Types0
  = Z | (:->) Types Types
  deriving Eq
lowerBound :: Types -> Types -> Maybe Types
lowerBound (Lazy a_a9uZ) (Lazy b_a9v0)
  = (Lazy <$> lowerBound a_a9uZ b_a9v0)
lowerBound
  (Value (a_a9v1 :-> b_a9v2))
  (Value (c_a9v3 :-> d_a9v4))
  = (Value
        <$>
          liftA2
            (:->) (upperBound a_a9v1 c_a9v3)
            (lowerBound b_a9v2 d_a9v4))
lowerBound (Value a_a9v5) (Lazy b_a9v6)
  = lowerBound (Value a_a9v5) b_a9v6
lowerBound (Lazy a_a9v7) (Value b_a9v8)
  = lowerBound a_a9v7 (Value b_a9v8)
lowerBound (Value Z) (Value Z)
  = Just (Value Z)
lowerBound (Value Z) (Value (_ :-> _))
  = Nothing
lowerBound (Value (_ :-> _)) (Value Z)
  = Nothing
upperBound :: Types -> Types -> Maybe Types
upperBound
  (Value (a_a9v9 :-> b_a9va))
  (Value (c_a9vb :-> d_a9vc))
  = (Value
        <$>
          liftA2
            (:->) (lowerBound a_a9v9 c_a9vb)
            (upperBound b_a9va d_a9vc))
upperBound (Lazy a_a9vd) (Lazy b_a9ve)
  = (Lazy <$> upperBound a_a9vd b_a9ve)
upperBound (Value a_a9vf) (Lazy b_a9vg)
  = (Lazy <$> upperBound (Value a_a9vf) b_a9vg)
upperBound (Lazy a_a9vh) (Value b_a9vi)
  = (Lazy <$> upperBound a_a9vh (Value b_a9vi))
upperBound (Value Z) (Value Z)
  = Just (Value Z)
upperBound (Value Z) (Value (_ :-> _))
  = Nothing
upperBound (Value (_ :-> _)) (Value Z)
  = Nothing
baseType :: Types -> Types
baseType (Value Z) = Value Z
baseType (Value (a_a9vj :-> b_a9vk))
  = Value (a_a9vj :-> b_a9vk)
baseType (Lazy (Value a_a9vl)) = Value a_a9vl
baseType (Lazy (Lazy a_a9vm)) = baseType a_a9vm
baseType (Lazy (LazyS a_a9vn))
  = baseType a_a9vn
baseType (LazyS (Value a_a9vo)) = Value a_a9vo
baseType (LazyS (Lazy a_a9vp))
  = baseType a_a9vp
baseType (LazyS (LazyS a_a9vq))
  = baseType a_a9vq
type ValueSym0 :: (Data.Singletons.~>) Types0 Types
data ValueSym0 :: (Data.Singletons.~>) Types0 Types
  where
    ValueSym0KindInference :: SameKind (Apply ValueSym0 arg_aa6X) (ValueSym1 arg_aa6X) =>
                              ValueSym0 a6989586621679048664
type instance Apply ValueSym0 a6989586621679048664 = Value a6989586621679048664
instance SuppressUnusedWarnings ValueSym0 where
  suppressUnusedWarnings = snd ((,) ValueSym0KindInference ())
type ValueSym1 :: Types0 -> Types
type family ValueSym1 (a6989586621679048664 :: Types0) :: Types where
  ValueSym1 a6989586621679048664 = Value a6989586621679048664
type LazySym0 :: (Data.Singletons.TH.~>) Types Types
data LazySym0 :: (Data.Singletons.TH.~>) Types Types
  where
    LazySym0KindInference :: SameKind (Apply LazySym0 arg_aa6Z) (LazySym1 arg_aa6Z) =>
                              LazySym0 a6989586621679048666
type instance Apply LazySym0 a6989586621679048666 = Lazy a6989586621679048666
instance SuppressUnusedWarnings LazySym0 where
  suppressUnusedWarnings = snd ((,) LazySym0KindInference ())
type LazySym1 :: Types -> Types
type family LazySym1 (a6989586621679048666 :: Types) :: Types where
  LazySym1 a6989586621679048666 = Lazy a6989586621679048666
type LazySSym0 :: (Data.Singletons.TH.~>) Types Types
data LazySSym0 :: (Data.Singletons.TH.~>) Types Types
  where
    LazySSym0KindInference :: SameKind (Apply LazySSym0 arg_aa71) (LazySSym1 arg_aa71) =>
                              LazySSym0 a6989586621679048668
type instance Apply LazySSym0 a6989586621679048668 = LazyS a6989586621679048668
instance SuppressUnusedWarnings LazySSym0 where
  suppressUnusedWarnings = snd ((,) LazySSym0KindInference ())
type LazySSym1 :: Types -> Types
type family LazySSym1 (a6989586621679048668 :: Types) :: Types where
  LazySSym1 a6989586621679048668 = LazyS a6989586621679048668
type ZSym0 :: Types0
type family ZSym0 :: Types0 where
  ZSym0 = Z
type (:->@#@$) :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types Types0)
data (:->@#@$) :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types Types0)
  where
    (::->@#@$###) :: SameKind (Apply (:->@#@$) arg_aa74) ((:->@#@$$) arg_aa74) =>
                      (:->@#@$) a6989586621679048671
type instance Apply (:->@#@$) a6989586621679048671 = (:->@#@$$) a6989586621679048671
instance SuppressUnusedWarnings (:->@#@$) where
  suppressUnusedWarnings = snd ((,) (::->@#@$###) ())
infixr 0 :->@#@$
type (:->@#@$$) :: Types -> (Data.Singletons.TH.~>) Types Types0
data (:->@#@$$) (a6989586621679048671 :: Types) :: (Data.Singletons.TH.~>) Types Types0
  where
    (::->@#@$$###) :: SameKind (Apply ((:->@#@$$) a6989586621679048671) arg_aa74) ((:->@#@$$$) a6989586621679048671 arg_aa74) =>
                      (:->@#@$$) a6989586621679048671 a6989586621679048672
type instance Apply ((:->@#@$$) a6989586621679048671) a6989586621679048672 = (:->) a6989586621679048671 a6989586621679048672
instance SuppressUnusedWarnings ((:->@#@$$) a6989586621679048671) where
  suppressUnusedWarnings = snd ((,) (::->@#@$$###) ())
infixr 0 :->@#@$$
type (:->@#@$$$) :: Types -> Types -> Types0
type family (:->@#@$$$) (a6989586621679048671 :: Types) (a6989586621679048672 :: Types) :: Types0 where
  (:->@#@$$$) a6989586621679048671 a6989586621679048672 = (:->) a6989586621679048671 a6989586621679048672
infixr 0 :->@#@$$$
type BaseTypeSym0 :: (Data.Singletons.TH.~>) Types Types
data BaseTypeSym0 :: (Data.Singletons.TH.~>) Types Types
  where
    BaseTypeSym0KindInference :: SameKind (Apply BaseTypeSym0 arg_aa78) (BaseTypeSym1 arg_aa78) =>
                                  BaseTypeSym0 a6989586621679048675
type instance Apply BaseTypeSym0 a6989586621679048675 = BaseType a6989586621679048675
instance SuppressUnusedWarnings BaseTypeSym0 where
  suppressUnusedWarnings = snd ((,) BaseTypeSym0KindInference ())
type BaseTypeSym1 :: Types -> Types
type family BaseTypeSym1 (a6989586621679048675 :: Types) :: Types where
  BaseTypeSym1 a6989586621679048675 = BaseType a6989586621679048675
type UpperBoundSym0 :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types (Maybe Types))
data UpperBoundSym0 :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types (Maybe Types))
  where
    UpperBoundSym0KindInference :: SameKind (Apply UpperBoundSym0 arg_aa7k) (UpperBoundSym1 arg_aa7k) =>
                                    UpperBoundSym0 a6989586621679048687
type instance Apply UpperBoundSym0 a6989586621679048687 = UpperBoundSym1 a6989586621679048687
instance SuppressUnusedWarnings UpperBoundSym0 where
  suppressUnusedWarnings = snd ((,) UpperBoundSym0KindInference ())
type UpperBoundSym1 :: Types
                        -> (Data.Singletons.TH.~>) Types (Maybe Types)
data UpperBoundSym1 (a6989586621679048687 :: Types) :: (Data.Singletons.TH.~>) Types (Maybe Types)
  where
    UpperBoundSym1KindInference :: SameKind (Apply (UpperBoundSym1 a6989586621679048687) arg_aa7k) (UpperBoundSym2 a6989586621679048687 arg_aa7k) =>
                                    UpperBoundSym1 a6989586621679048687 a6989586621679048688
type instance Apply (UpperBoundSym1 a6989586621679048687) a6989586621679048688 = UpperBound a6989586621679048687 a6989586621679048688
instance SuppressUnusedWarnings (UpperBoundSym1 a6989586621679048687) where
  suppressUnusedWarnings = snd ((,) UpperBoundSym1KindInference ())
type UpperBoundSym2 :: Types -> Types -> Maybe Types
type family UpperBoundSym2 (a6989586621679048687 :: Types) (a6989586621679048688 :: Types) :: Maybe Types where
  UpperBoundSym2 a6989586621679048687 a6989586621679048688 = UpperBound a6989586621679048687 a6989586621679048688
type LowerBoundSym0 :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types (Maybe Types))
data LowerBoundSym0 :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types (Maybe Types))
  where
    LowerBoundSym0KindInference :: SameKind (Apply LowerBoundSym0 arg_aa7z) (LowerBoundSym1 arg_aa7z) =>
                                    LowerBoundSym0 a6989586621679048702
type instance Apply LowerBoundSym0 a6989586621679048702 = LowerBoundSym1 a6989586621679048702
instance SuppressUnusedWarnings LowerBoundSym0 where
  suppressUnusedWarnings = snd ((,) LowerBoundSym0KindInference ())
type LowerBoundSym1 :: Types
                        -> (Data.Singletons.TH.~>) Types (Maybe Types)
data LowerBoundSym1 (a6989586621679048702 :: Types) :: (Data.Singletons.TH.~>) Types (Maybe Types)
  where
    LowerBoundSym1KindInference :: SameKind (Apply (LowerBoundSym1 a6989586621679048702) arg_aa7z) (LowerBoundSym2 a6989586621679048702 arg_aa7z) =>
                                    LowerBoundSym1 a6989586621679048702 a6989586621679048703
type instance Apply (LowerBoundSym1 a6989586621679048702) a6989586621679048703 = LowerBound a6989586621679048702 a6989586621679048703
instance SuppressUnusedWarnings (LowerBoundSym1 a6989586621679048702) where
  suppressUnusedWarnings = snd ((,) LowerBoundSym1KindInference ())
type LowerBoundSym2 :: Types -> Types -> Maybe Types
type family LowerBoundSym2 (a6989586621679048702 :: Types) (a6989586621679048703 :: Types) :: Maybe Types where
  LowerBoundSym2 a6989586621679048702 a6989586621679048703 = LowerBound a6989586621679048702 a6989586621679048703
type BaseType :: Types -> Types
type family BaseType (a_aa77 :: Types) :: Types where
  BaseType (Value Z) = Apply ValueSym0 ZSym0
  BaseType (Value ((:->) a_aa7a b_aa7b)) = Apply ValueSym0 (Apply (Apply (:->@#@$) a_aa7a) b_aa7b)
  BaseType (Lazy (Value a_aa7c)) = Apply ValueSym0 a_aa7c
  BaseType (Lazy (Lazy a_aa7d)) = Apply BaseTypeSym0 a_aa7d
  BaseType (Lazy (LazyS a_aa7e)) = Apply BaseTypeSym0 a_aa7e
  BaseType (LazyS (Value a_aa7f)) = Apply ValueSym0 a_aa7f
  BaseType (LazyS (Lazy a_aa7g)) = Apply BaseTypeSym0 a_aa7g
  BaseType (LazyS (LazyS a_aa7h)) = Apply BaseTypeSym0 a_aa7h
type UpperBound :: Types -> Types -> Maybe Types
type family UpperBound (a_aa7i :: Types) (a_aa7j :: Types) :: Maybe Types where
  UpperBound (Value ((:->) a_aa7n b_aa7o)) (Value ((:->) c_aa7p d_aa7q)) = Apply (Apply (<$>@#@$) ValueSym0) (Apply (Apply (Apply LiftA2Sym0 (:->@#@$)) (Apply (Apply LowerBoundSym0 a_aa7n) c_aa7p)) (Apply (Apply UpperBoundSym0 b_aa7o) d_aa7q))
  UpperBound (Lazy a_aa7r) (Lazy b_aa7s) = Apply (Apply (<$>@#@$) LazySym0) (Apply (Apply UpperBoundSym0 a_aa7r) b_aa7s)
  UpperBound (Value a_aa7t) (Lazy b_aa7u) = Apply (Apply (<$>@#@$) LazySym0) (Apply (Apply UpperBoundSym0 (Apply ValueSym0 a_aa7t)) b_aa7u)
  UpperBound (Lazy a_aa7v) (Value b_aa7w) = Apply (Apply (<$>@#@$) LazySym0) (Apply (Apply UpperBoundSym0 a_aa7v) (Apply ValueSym0 b_aa7w))
  UpperBound (Value Z) (Value Z) = Apply JustSym0 (Apply ValueSym0 ZSym0)
  UpperBound (Value Z) (Value ((:->) _ _)) = NothingSym0
  UpperBound (Value ((:->) _ _)) (Value Z) = NothingSym0
type LowerBound :: Types -> Types -> Maybe Types
type family LowerBound (a_aa7x :: Types) (a_aa7y :: Types) :: Maybe Types where
  LowerBound (Lazy a_aa7C) (Lazy b_aa7D) = Apply (Apply (<$>@#@$) LazySym0) (Apply (Apply LowerBoundSym0 a_aa7C) b_aa7D)
  LowerBound (Value ((:->) a_aa7E b_aa7F)) (Value ((:->) c_aa7G d_aa7H)) = Apply (Apply (<$>@#@$) ValueSym0) (Apply (Apply (Apply LiftA2Sym0 (:->@#@$)) (Apply (Apply UpperBoundSym0 a_aa7E) c_aa7G)) (Apply (Apply LowerBoundSym0 b_aa7F) d_aa7H))
  LowerBound (Value a_aa7I) (Lazy b_aa7J) = Apply (Apply LowerBoundSym0 (Apply ValueSym0 a_aa7I)) b_aa7J
  LowerBound (Lazy a_aa7K) (Value b_aa7L) = Apply (Apply LowerBoundSym0 a_aa7K) (Apply ValueSym0 b_aa7L)
  LowerBound (Value Z) (Value Z) = Apply JustSym0 (Apply ValueSym0 ZSym0)
  LowerBound (Value Z) (Value ((:->) _ _)) = NothingSym0
  LowerBound (Value ((:->) _ _)) (Value Z) = NothingSym0
type TFHelper_6989586621679050222 :: Types
                                      -> Types -> Bool
type family TFHelper_6989586621679050222 (a_aaw8 :: Types) (a_aaw9 :: Types) :: Bool where
  TFHelper_6989586621679050222 (Value a_6989586621679048643_aawd) (Value b_6989586621679048645_aawe) = Apply (Apply (==@#@$) a_6989586621679048643_aawd) b_6989586621679048645_aawe
  TFHelper_6989586621679050222 (Value _) (Lazy _) = FalseSym0
  TFHelper_6989586621679050222 (Value _) (LazyS _) = FalseSym0
  TFHelper_6989586621679050222 (Lazy _) (Value _) = FalseSym0
  TFHelper_6989586621679050222 (Lazy a_6989586621679048647_aawf) (Lazy b_6989586621679048649_aawg) = Apply (Apply (==@#@$) a_6989586621679048647_aawf) b_6989586621679048649_aawg
  TFHelper_6989586621679050222 (Lazy _) (LazyS _) = FalseSym0
  TFHelper_6989586621679050222 (LazyS _) (Value _) = FalseSym0
  TFHelper_6989586621679050222 (LazyS _) (Lazy _) = FalseSym0
  TFHelper_6989586621679050222 (LazyS a_6989586621679048651_aawh) (LazyS b_6989586621679048653_aawi) = Apply (Apply (==@#@$) a_6989586621679048651_aawh) b_6989586621679048653_aawi
type TFHelper_6989586621679050222Sym0 :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types Bool)
data TFHelper_6989586621679050222Sym0 :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types Bool)
  where
    TFHelper_6989586621679050222Sym0KindInference :: SameKind (Apply TFHelper_6989586621679050222Sym0 arg_aawa) (TFHelper_6989586621679050222Sym1 arg_aawa) =>
                                                      TFHelper_6989586621679050222Sym0 a6989586621679050227
type instance Apply TFHelper_6989586621679050222Sym0 a6989586621679050227 = TFHelper_6989586621679050222Sym1 a6989586621679050227
instance SuppressUnusedWarnings TFHelper_6989586621679050222Sym0 where
  suppressUnusedWarnings
    = snd ((,) TFHelper_6989586621679050222Sym0KindInference ())
type TFHelper_6989586621679050222Sym1 :: Types
                                          -> (Data.Singletons.TH.~>) Types Bool
data TFHelper_6989586621679050222Sym1 (a6989586621679050227 :: Types) :: (Data.Singletons.TH.~>) Types Bool
  where
    TFHelper_6989586621679050222Sym1KindInference :: SameKind (Apply (TFHelper_6989586621679050222Sym1 a6989586621679050227) arg_aawa) (TFHelper_6989586621679050222Sym2 a6989586621679050227 arg_aawa) =>
                                                      TFHelper_6989586621679050222Sym1 a6989586621679050227 a6989586621679050228
type instance Apply (TFHelper_6989586621679050222Sym1 a6989586621679050227) a6989586621679050228 = TFHelper_6989586621679050222 a6989586621679050227 a6989586621679050228
instance SuppressUnusedWarnings (TFHelper_6989586621679050222Sym1 a6989586621679050227) where
  suppressUnusedWarnings
    = snd ((,) TFHelper_6989586621679050222Sym1KindInference ())
type TFHelper_6989586621679050222Sym2 :: Types
                                          -> Types -> Bool
type family TFHelper_6989586621679050222Sym2 (a6989586621679050227 :: Types) (a6989586621679050228 :: Types) :: Bool where
  TFHelper_6989586621679050222Sym2 a6989586621679050227 a6989586621679050228 = TFHelper_6989586621679050222 a6989586621679050227 a6989586621679050228
instance PEq Types where
  type (==) a_aaw4 a_aaw5 = Apply (Apply TFHelper_6989586621679050222Sym0 a_aaw4) a_aaw5
type TFHelper_6989586621679050237 :: Types0
                                      -> Types0 -> Bool
type family TFHelper_6989586621679050237 (a_aawn :: Types0) (a_aawo :: Types0) :: Bool where
  TFHelper_6989586621679050237 Z Z = TrueSym0
  TFHelper_6989586621679050237 Z ((:->) _ _) = FalseSym0
  TFHelper_6989586621679050237 ((:->) _ _) Z = FalseSym0
  TFHelper_6989586621679050237 ((:->) a_6989586621679048655_aaws a_6989586621679048657_aawt) ((:->) b_6989586621679048659_aawu b_6989586621679048661_aawv) = Apply (Apply (&&@#@$) (Apply (Apply (==@#@$) a_6989586621679048655_aaws) b_6989586621679048659_aawu)) (Apply (Apply (==@#@$) a_6989586621679048657_aawt) b_6989586621679048661_aawv)
type TFHelper_6989586621679050237Sym0 :: (Data.Singletons.TH.~>) Types0 ((Data.Singletons.TH.~>) Types0 Bool)
data TFHelper_6989586621679050237Sym0 :: (Data.Singletons.TH.~>) Types0 ((Data.Singletons.TH.~>) Types0 Bool)
  where
    TFHelper_6989586621679050237Sym0KindInference :: SameKind (Apply TFHelper_6989586621679050237Sym0 arg_aawp) (TFHelper_6989586621679050237Sym1 arg_aawp) =>
                                                      TFHelper_6989586621679050237Sym0 a6989586621679050242
type instance Apply TFHelper_6989586621679050237Sym0 a6989586621679050242 = TFHelper_6989586621679050237Sym1 a6989586621679050242
instance SuppressUnusedWarnings TFHelper_6989586621679050237Sym0 where
  suppressUnusedWarnings
    = snd ((,) TFHelper_6989586621679050237Sym0KindInference ())
type TFHelper_6989586621679050237Sym1 :: Types0
                                          -> (Data.Singletons.TH.~>) Types0 Bool
data TFHelper_6989586621679050237Sym1 (a6989586621679050242 :: Types0) :: (Data.Singletons.TH.~>) Types0 Bool
  where
    TFHelper_6989586621679050237Sym1KindInference :: SameKind (Apply (TFHelper_6989586621679050237Sym1 a6989586621679050242) arg_aawp) (TFHelper_6989586621679050237Sym2 a6989586621679050242 arg_aawp) =>
                                                      TFHelper_6989586621679050237Sym1 a6989586621679050242 a6989586621679050243
type instance Apply (TFHelper_6989586621679050237Sym1 a6989586621679050242) a6989586621679050243 = TFHelper_6989586621679050237 a6989586621679050242 a6989586621679050243
instance SuppressUnusedWarnings (TFHelper_6989586621679050237Sym1 a6989586621679050242) where
  suppressUnusedWarnings
    = snd ((,) TFHelper_6989586621679050237Sym1KindInference ())
type TFHelper_6989586621679050237Sym2 :: Types0
                                          -> Types0 -> Bool
type family TFHelper_6989586621679050237Sym2 (a6989586621679050242 :: Types0) (a6989586621679050243 :: Types0) :: Bool where
  TFHelper_6989586621679050237Sym2 a6989586621679050242 a6989586621679050243 = TFHelper_6989586621679050237 a6989586621679050242 a6989586621679050243
instance PEq Types0 where
  type (==) a_aawj a_aawk = Apply (Apply TFHelper_6989586621679050237Sym0 a_aawj) a_aawk
infixr 0 :%->
sBaseType ::
  (forall (t_aaww :: Types).
    Sing t_aaww
    -> Sing (Apply BaseTypeSym0 t_aaww :: Types) :: Type)
sUpperBound ::
  (forall (t_aawy :: Types) (t_aawz :: Types).
    Sing t_aawy
    -> Sing t_aawz
      -> Sing (Apply (Apply UpperBoundSym0 t_aawy) t_aawz :: Maybe Types) :: Type)
sLowerBound ::
  (forall (t_aawD :: Types) (t_aawE :: Types).
    Sing t_aawD
    -> Sing t_aawE
      -> Sing (Apply (Apply LowerBoundSym0 t_aawD) t_aawE :: Maybe Types) :: Type)
sBaseType (SValue SZ) = applySing (singFun1 @ValueSym0 SValue) SZ
sBaseType (SValue ((:%->) (sA :: Sing a_aa7a) (sB :: Sing b_aa7b)))
  = applySing
      (singFun1 @ValueSym0 SValue)
      (applySing (applySing (singFun2 @(:->@#@$) (:%->)) sA) sB)
sBaseType (SLazy (SValue (sA :: Sing a_aa7c)))
  = applySing (singFun1 @ValueSym0 SValue) sA
sBaseType (SLazy (SLazy (sA :: Sing a_aa7d)))
  = applySing (singFun1 @BaseTypeSym0 sBaseType) sA
sBaseType (SLazy (SLazyS (sA :: Sing a_aa7e)))
  = applySing (singFun1 @BaseTypeSym0 sBaseType) sA
sBaseType (SLazyS (SValue (sA :: Sing a_aa7f)))
  = applySing (singFun1 @ValueSym0 SValue) sA
sBaseType (SLazyS (SLazy (sA :: Sing a_aa7g)))
  = applySing (singFun1 @BaseTypeSym0 sBaseType) sA
sBaseType (SLazyS (SLazyS (sA :: Sing a_aa7h)))
  = applySing (singFun1 @BaseTypeSym0 sBaseType) sA
sUpperBound
  (SValue ((:%->) (sA :: Sing a_aa7n) (sB :: Sing b_aa7o)))
  (SValue ((:%->) (sC :: Sing c_aa7p) (sD :: Sing d_aa7q)))
  = applySing
      (applySing
          (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @ValueSym0 SValue))
      (applySing
          (applySing
            (applySing
                (singFun3 @LiftA2Sym0 sLiftA2) (singFun2 @(:->@#@$) (:%->)))
            (applySing
                (applySing (singFun2 @LowerBoundSym0 sLowerBound) sA) sC))
          (applySing
            (applySing (singFun2 @UpperBoundSym0 sUpperBound) sB) sD))
sUpperBound (SLazy (sA :: Sing a_aa7r)) (SLazy (sB :: Sing b_aa7s))
  = applySing
      (applySing (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @LazySym0 SLazy))
      (applySing
          (applySing (singFun2 @UpperBoundSym0 sUpperBound) sA) sB)
sUpperBound
  (SValue (sA :: Sing a_aa7t))
  (SLazy (sB :: Sing b_aa7u))
  = applySing
      (applySing (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @LazySym0 SLazy))
      (applySing
          (applySing
            (singFun2 @UpperBoundSym0 sUpperBound)
            (applySing (singFun1 @ValueSym0 SValue) sA))
          sB)
sUpperBound
  (SLazy (sA :: Sing a_aa7v))
  (SValue (sB :: Sing b_aa7w))
  = applySing
      (applySing (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @LazySym0 SLazy))
      (applySing
          (applySing (singFun2 @UpperBoundSym0 sUpperBound) sA)
          (applySing (singFun1 @ValueSym0 SValue) sB))
sUpperBound (SValue SZ) (SValue SZ)
  = applySing
      (singFun1 @JustSym0 SJust)
      (applySing (singFun1 @ValueSym0 SValue) SZ)
sUpperBound (SValue SZ) (SValue ((:%->) _ _)) = SNothing
sUpperBound (SValue ((:%->) _ _)) (SValue SZ) = SNothing
sLowerBound (SLazy (sA :: Sing a_aa7C)) (SLazy (sB :: Sing b_aa7D))
  = applySing
      (applySing (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @LazySym0 SLazy))
      (applySing
          (applySing (singFun2 @LowerBoundSym0 sLowerBound) sA) sB)
sLowerBound
  (SValue ((:%->) (sA :: Sing a_aa7E) (sB :: Sing b_aa7F)))
  (SValue ((:%->) (sC :: Sing c_aa7G) (sD :: Sing d_aa7H)))
  = applySing
      (applySing
          (singFun2 @(<$>@#@$) (%<$>)) (singFun1 @ValueSym0 SValue))
      (applySing
          (applySing
            (applySing
                (singFun3 @LiftA2Sym0 sLiftA2) (singFun2 @(:->@#@$) (:%->)))
            (applySing
                (applySing (singFun2 @UpperBoundSym0 sUpperBound) sA) sC))
          (applySing
            (applySing (singFun2 @LowerBoundSym0 sLowerBound) sB) sD))
sLowerBound
  (SValue (sA :: Sing a_aa7I))
  (SLazy (sB :: Sing b_aa7J))
  = applySing
      (applySing
          (singFun2 @LowerBoundSym0 sLowerBound)
          (applySing (singFun1 @ValueSym0 SValue) sA))
      sB
sLowerBound
  (SLazy (sA :: Sing a_aa7K))
  (SValue (sB :: Sing b_aa7L))
  = applySing
      (applySing (singFun2 @LowerBoundSym0 sLowerBound) sA)
      (applySing (singFun1 @ValueSym0 SValue) sB)
sLowerBound (SValue SZ) (SValue SZ)
  = applySing
      (singFun1 @JustSym0 SJust)
      (applySing (singFun1 @ValueSym0 SValue) SZ)
sLowerBound (SValue SZ) (SValue ((:%->) _ _)) = SNothing
sLowerBound (SValue ((:%->) _ _)) (SValue SZ) = SNothing
instance SingI (BaseTypeSym0 :: (Data.Singletons.TH.~>) Types Types) where
  sing = singFun1 @BaseTypeSym0 sBaseType
instance SingI (UpperBoundSym0 :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types (Maybe Types))) where
  sing = singFun2 @UpperBoundSym0 sUpperBound
instance SingI d_aawA =>
          SingI (UpperBoundSym1 (d_aawA :: Types) :: (Data.Singletons.TH.~>) Types (Maybe Types)) where
  sing
    = singFun1
        @(UpperBoundSym1 (d_aawA :: Types))
        (sUpperBound (sing @d_aawA))
instance SingI1 (UpperBoundSym1 :: Types
                                    -> (Data.Singletons.TH.~>) Types (Maybe Types)) where
  liftSing (s_aawC :: Sing (d_aawA :: Types))
    = singFun1
        @(UpperBoundSym1 (d_aawA :: Types)) (sUpperBound s_aawC)
instance SingI (LowerBoundSym0 :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types (Maybe Types))) where
  sing = singFun2 @LowerBoundSym0 sLowerBound
instance SingI d_aawF =>
          SingI (LowerBoundSym1 (d_aawF :: Types) :: (Data.Singletons.TH.~>) Types (Maybe Types)) where
  sing
    = singFun1
        @(LowerBoundSym1 (d_aawF :: Types))
        (sLowerBound (sing @d_aawF))
instance SingI1 (LowerBoundSym1 :: Types
                                    -> (Data.Singletons.TH.~>) Types (Maybe Types)) where
  liftSing (s_aawH :: Sing (d_aawF :: Types))
    = singFun1
        @(LowerBoundSym1 (d_aawF :: Types)) (sLowerBound s_aawH)
data STypes :: Types -> Type
  where
    SValue :: forall (n_abIU :: Types0).
              (Sing n_abIU) -> STypes (Value n_abIU :: Types)
    SLazy :: forall (n_abIW :: Types).
              (Sing n_abIW) -> STypes (Lazy n_abIW :: Types)
    SLazyS :: forall (n_abIY :: Types).
              (Sing n_abIY) -> STypes (LazyS n_abIY :: Types)
type instance Sing @Types = STypes
instance SingKind Types where
  type Demote Types = Types
  fromSing (SValue b_abJ0) = Value (fromSing b_abJ0)
  fromSing (SLazy b_abJ1) = Lazy (fromSing b_abJ1)
  fromSing (SLazyS b_abJ2) = LazyS (fromSing b_abJ2)
  toSing (Value (b_abJ4 :: Demote Types0))
    = case toSing b_abJ4 :: SomeSing Types0 of
        SomeSing c_abJ5 -> SomeSing (SValue c_abJ5)
  toSing (Lazy (b_abJ6 :: Demote Types))
    = case toSing b_abJ6 :: SomeSing Types of
        SomeSing c_abJ7 -> SomeSing (SLazy c_abJ7)
  toSing (LazyS (b_abJ8 :: Demote Types))
    = case toSing b_abJ8 :: SomeSing Types of
        SomeSing c_abJ9 -> SomeSing (SLazyS c_abJ9)
data STypes0 :: Types0 -> Type
  where
    SZ :: STypes0 (Z :: Types0)
    (:%->) :: forall (n_abJb :: Types) (n_abJc :: Types).
              (Sing n_abJb) ->
              (Sing n_abJc) ->
              STypes0 ((:->) n_abJb n_abJc :: Types0)
type instance Sing @Types0 = STypes0
instance SingKind Types0 where
  type Demote Types0 = Types0
  fromSing SZ = Z
  fromSing ((:%->) b_abJg b_abJh)
    = (:->) (fromSing b_abJg) (fromSing b_abJh)
  toSing Z = SomeSing SZ
  toSing
    ((:->) (b_abJj :: Demote Types)
                (b_abJk :: Demote Types))
    = case
          (,)
            (toSing b_abJj :: SomeSing Types)
            (toSing b_abJk :: SomeSing Types)
      of
        (,) (SomeSing c_abJl) (SomeSing c_abJm)
          -> SomeSing ((:%->) c_abJl c_abJm)
instance (SEq Types0, SEq Types) => SEq Types where
  (%==) ::
    forall (t1_abJr :: Types)
            (t2_abJs :: Types). Sing t1_abJr
                                    -> Sing t2_abJs
                                        -> Sing (Apply (Apply ((==@#@$) :: TyFun Types ((Data.Singletons.TH.~>) Types Bool)
                                                                          -> Type) t1_abJr) t2_abJs)
  (%==)
    (SValue (sA_6989586621679048643 :: Sing a_6989586621679048643_aawd))
    (SValue (sB_6989586621679048645 :: Sing b_6989586621679048645_aawe))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679048643)
        sB_6989586621679048645
  (%==) (SValue _) (SLazy _) = SFalse
  (%==) (SValue _) (SLazyS _) = SFalse
  (%==) (SLazy _) (SValue _) = SFalse
  (%==)
    (SLazy (sA_6989586621679048647 :: Sing a_6989586621679048647_aawf))
    (SLazy (sB_6989586621679048649 :: Sing b_6989586621679048649_aawg))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679048647)
        sB_6989586621679048649
  (%==) (SLazy _) (SLazyS _) = SFalse
  (%==) (SLazyS _) (SValue _) = SFalse
  (%==) (SLazyS _) (SLazy _) = SFalse
  (%==)
    (SLazyS (sA_6989586621679048651 :: Sing a_6989586621679048651_aawh))
    (SLazyS (sB_6989586621679048653 :: Sing b_6989586621679048653_aawi))
    = applySing
        (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679048651)
        sB_6989586621679048653
instance SEq Types => SEq Types0 where
  (%==) ::
    forall (t1_abJr :: Types0)
            (t2_abJs :: Types0). Sing t1_abJr
                                      -> Sing t2_abJs
                                        -> Sing (Apply (Apply ((==@#@$) :: TyFun Types0 ((Data.Singletons.TH.~>) Types0 Bool)
                                                                            -> Type) t1_abJr) t2_abJs)
  (%==) SZ SZ = STrue
  (%==) SZ ((:%->) _ _) = SFalse
  (%==) ((:%->) _ _) SZ = SFalse
  (%==)
    ((:%->) (sA_6989586621679048655 :: Sing a_6989586621679048655_aaws)
            (sA_6989586621679048657 :: Sing a_6989586621679048657_aawt))
    ((:%->) (sB_6989586621679048659 :: Sing b_6989586621679048659_aawu)
            (sB_6989586621679048661 :: Sing b_6989586621679048661_aawv))
    = applySing
        (applySing
            (singFun2 @(&&@#@$) (%&&))
            (applySing
              (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679048655)
              sB_6989586621679048659))
        (applySing
            (applySing (singFun2 @(==@#@$) (%==)) sA_6989586621679048657)
            sB_6989586621679048661)
instance (SDecide Types0, SDecide Types) =>
          SDecide Types where
  (%~) (SValue a_abMM) (SValue b_abMN)
    = case (%~) a_abMM b_abMN of
        Proved Refl -> Proved Refl
        Disproved contra_abMO
          -> Disproved
                (\ refl_abMP -> case refl_abMP of Refl -> contra_abMO Refl)
  (%~) (SValue _) (SLazy _)
    = Disproved (\ x_abMQ -> case x_abMQ of {})
  (%~) (SValue _) (SLazyS _)
    = Disproved (\ x_abMR -> case x_abMR of {})
  (%~) (SLazy _) (SValue _)
    = Disproved (\ x_abMS -> case x_abMS of {})
  (%~) (SLazy a_abMT) (SLazy b_abMU)
    = case (%~) a_abMT b_abMU of
        Proved Refl -> Proved Refl
        Disproved contra_abMV
          -> Disproved
                (\ refl_abMW -> case refl_abMW of Refl -> contra_abMV Refl)
  (%~) (SLazy _) (SLazyS _)
    = Disproved (\ x_abMX -> case x_abMX of {})
  (%~) (SLazyS _) (SValue _)
    = Disproved (\ x_abMY -> case x_abMY of {})
  (%~) (SLazyS _) (SLazy _)
    = Disproved (\ x_abMZ -> case x_abMZ of {})
  (%~) (SLazyS a_abN0) (SLazyS b_abN1)
    = case (%~) a_abN0 b_abN1 of
        Proved Refl -> Proved Refl
        Disproved contra_abN2
          -> Disproved
                (\ refl_abN3 -> case refl_abN3 of Refl -> contra_abN2 Refl)
instance Eq (STypes (z_abN4 :: Types)) where
  (==) _ _ = True
instance (SDecide Types0, SDecide Types) =>
          Data.Type.Equality.TestEquality (STypes :: Types
                                                    -> Type) where
  testEquality = decideEquality
instance (SDecide Types0, SDecide Types) =>
          Data.Type.Coercion.TestCoercion (STypes :: Types
                                                    -> Type) where
  testCoercion = decideCoercion
instance SDecide Types => SDecide Types0 where
  (%~) SZ SZ = Proved Refl
  (%~) SZ ((:%->) _ _) = Disproved (\ x_abNa -> case x_abNa of {})
  (%~) ((:%->) _ _) SZ = Disproved (\ x_abNb -> case x_abNb of {})
  (%~) ((:%->) a_abNc a_abNd) ((:%->) b_abNe b_abNf)
    = case (,) ((%~) a_abNc b_abNe) ((%~) a_abNd b_abNf) of
        (,) (Proved Refl) (Proved Refl) -> Proved Refl
        (,) (Disproved contra_abNg) _
          -> Disproved
                (\ refl_abNh -> case refl_abNh of Refl -> contra_abNg Refl)
        (,) _ (Disproved contra_abNg)
          -> Disproved
                (\ refl_abNh -> case refl_abNh of Refl -> contra_abNg Refl)
instance Eq (STypes0 (z_abNi :: Types0)) where
  (==) _ _ = True
instance SDecide Types =>
          Data.Type.Equality.TestEquality (STypes0 :: Types0
                                                      -> Type) where
  testEquality = decideEquality
instance SDecide Types =>
          Data.Type.Coercion.TestCoercion (STypes0 :: Types0
                                                      -> Type) where
  testCoercion = decideCoercion
instance SingI n_abIU =>
          SingI (Value (n_abIU :: Types0)) where
  sing = SValue sing
instance SingI1 Value where
  liftSing = SValue
instance SingI (ValueSym0 :: (Data.Singletons.TH.~>) Types0 Types) where
  sing = singFun1 @ValueSym0 SValue
instance SingI n_abIW =>
          SingI (Lazy (n_abIW :: Types)) where
  sing = SLazy sing
instance SingI1 Lazy where
  liftSing = SLazy
instance SingI (LazySym0 :: (Data.Singletons.TH.~>) Types Types) where
  sing = singFun1 @LazySym0 SLazy
instance SingI n_abIY =>
          SingI (LazyS (n_abIY :: Types)) where
  sing = SLazyS sing
instance SingI1 LazyS where
  liftSing = SLazyS
instance SingI (LazySSym0 :: (Data.Singletons.TH.~>) Types Types) where
  sing = singFun1 @LazySSym0 SLazyS
instance SingI Z where
  sing = SZ
instance (SingI n_abJb, SingI n_abJc) =>
          SingI ((:->) (n_abJb :: Types) (n_abJc :: Types)) where
  sing = (:%->) sing sing
instance SingI n_abJb =>
          SingI1 ((:->) (n_abJb :: Types)) where
  liftSing = (:%->) sing
instance SingI2 (:->) where
  liftSing2 = (:%->)
instance SingI ((:->@#@$) :: (Data.Singletons.TH.~>) Types ((Data.Singletons.TH.~>) Types Types0)) where
  sing = singFun2 @(:->@#@$) (:%->)
instance SingI d_abJd =>
          SingI ((:->@#@$$) (d_abJd :: Types) :: (Data.Singletons.TH.~>) Types Types0) where
  sing
    = singFun1
        @((:->@#@$$) (d_abJd :: Types)) ((:%->) (sing @d_abJd))
instance SingI1 ((:->@#@$$) :: Types
                                -> (Data.Singletons.TH.~>) Types Types0) where
  liftSing (s_abJf :: Sing (d_abJd :: Types))
    = singFun1 @((:->@#@$$) (d_abJd :: Types)) ((:%->) s_abJf)
#endif

instance Show Types where
  showsPrec p = \case
    (Value a) -> showsPrec p a
    (Lazy a)  -> showString "Lazy <" . showsPrec p a . showString ">"
    (LazyS a) -> showString "Lazy* <" . showsPrec p a . showString ">"
    (Array a) -> showString "array[" . showsPrec p a . showString "]"
instance Show Types0 where
  showsPrec p = \case
    Z -> showString "Z"
    (a :-> b) -> showParen (p > 0) $ showsPrec 1 a . showString " -> " . shows b

---------------------------
-- Type synonyms
---------------------------

type Symbol = String

infixr 0 ~>
type (~>) a b = Value (a :-> b)

class SingI a => BasicType a where
  type HashType a :: Type


--------------------------
-- Utility functions
--------------------------


-- | Implicit equality.
decideEquality' :: forall k (a :: k) (b :: k).  (SDecide k, SingI a, SingI b) => Maybe (a :~: b) 
decideEquality' = decideEquality (sing @a) (sing @b)

--------------------------
-- Dictionary Injection
--------------------------

-- | Show implicit singleton.
withShow :: forall (z :: Types). SingI z => String
withShow = show $ fromSing (sing @z) 

{- -- | Injects base type singleton.
withBType :: forall (z :: Types) r. SingI z => (SingI  (BaseType z) => r) -> r
withBType f = case sing @z of
  (SValue @n SZ) -> case decideEquality' @_ @(Value n) @(BaseType z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SValue @n (a :%-> b)) -> case decideEquality' @_ @(Value n) @(BaseType z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) 
    -> withSingI sa 
    $ withBType @n 
    $ case decideEquality  (sing @(BaseType z)) (sing @(BaseType n) )of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) 
    -> withSingI @n sa 
    $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented" -}

-- | Injects an upper bound singleton.
withSingIUBType :: forall (z0 :: Types) (z1 :: Types) r. 
  ( SingI z0
  , SingI z1
  ) => (SingI  (UpperBound z0 z1) => r) -> r
withSingIUBType f = case sUpperBound (sing @z0) (sing @z1) of
  SJust ub -> withSingI ub f
  SNothing -> f

-- | Injects a lower bound singleton.
withSingILBType :: forall (z0 :: Types) (z1 :: Types) r. 
  ( SingI z0
  , SingI z1
  ) => (SingI  (LowerBound z0 z1) => r) -> r
withSingILBType f = undefined 


{- withBVType' :: forall (z :: Types) r. Sing z -> (SingI  (BaseType z) => r) -> r
withBVType' z f= case z of
  (SValue @n _) -> withSingI z $ case decideEquality' @_ @(Value n) @(BaseType z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) -> withSingI @n sa $ withBType @n $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl ->  f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) -> withSingI @n sa $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented" -}



--------------------------
-- Properties
--------------------------

{-| Upperbound being a meet, is axiomatically commutative. 

\[a \vee b = b \vee a\]
-}
ubIsCommutative :: forall (a :: Types) (b :: Types) cont.
  ( SingI a
  , SingI b
  )
  => ((UpperBound a b ~ UpperBound b a) => cont) -> cont
ubIsCommutative f 
  = withSingIUBType @a @b 
  $ withSingIUBType @b @a 
  $ case decideEquality (sing @(UpperBound a b)) (sing @(UpperBound b a)) of
  Just Refl -> f
  Nothing -> error "impossible case"


{-| Upperbound being a meet, is axiomatically associative. 

\[a \vee b = b \vee a\]
-}
ubIsAssociative :: forall {r1 :: Maybe Types} {r2 :: Maybe Types} (a :: Types) (b :: Types) (c :: Types) cont.
  ( SingI a 
  , SingI b
  , SingI c
  , (UpperBound a b >>= UpperBoundSym1 c) ~ r1
  , (UpperBound b c >>= UpperBoundSym1 a) ~ r2
  ) => (r1 ~ r2 => cont) -> Maybe cont
ubIsAssociative f
  = withSingIUBType @a @b 
  $ withSingIUBType @b @c
  $ case (sing @(UpperBound a b), sing @(UpperBound b c)) of
  (SJust @_ @x x,SJust @_ @y y) 
    -> withSingI x
    $ withSingI y 
    $ withSingIUBType @c @x 
    $ withSingIUBType @a @y 
    $ case decideEquality' @(Maybe Types) @(UpperBound c x) @(UpperBound a y) of
      Just Refl -> Just f
      Nothing -> Nothing
  _ -> Nothing



{-| Upperbound being a meet, is axiomatically reflexive. 

\[a \vee a = a\]
-}
ubIsIdempotent :: forall (a :: Types) cont.
  (SingI a)
  => (UpperBound a a ~ Just a => cont) -> cont
ubIsIdempotent !f = withSingIUBType @a @a $ case decideEquality (sing @(UpperBound a a)) (sing @(Just a)) of
  Just Refl -> f
  Nothing -> error "impossible case"

-- ask reddit: why I can't apply type families and ~ inside a contraint-kind?
{- type UBAxioms = 
  ( forall a b. (UpperBound a b ~ UpperBound b a)
  , forall a. UpperBound a a ~ Just a
  , forall a b c. (UpperBound a b >>= UpperBoundSym1 c) ~ (UpperBound b c >>= UpperBoundSym1 a)
  ) -}


ubIsTransitive 
  :: forall {r0 :: Types} {r1 :: Types} {r2 :: Types} a b c cont.
  ( UpperBound a b ~ Just r0
  , UpperBound b c ~ Just r1 
  )
  => (UpperBound a c ~ Just r2 => cont) -> cont
ubIsTransitive fa = error "not implemented"

{-| Convinient "transitive" property... For the time being taken as axiom... 
TODO: Make a proof, just another take on associativity.

\[a \vee b = b\]
-}
ubIsTransitive'
  :: forall {r0 :: Types} a b c cont.
  ( UpperBound a b ~ Just b
  , UpperBound b c ~ Just r0
  , SingI r0
  , SingI a
  , SingI c
  )
  => (UpperBound a c ~ Just r0 => cont) -> cont
ubIsTransitive' !f = withSingIUBType @a @c $ case decideEquality (sing @(UpperBound a c)) (sing @(Just r0)) of
  Just Refl -> f
  Nothing -> error "impossible case"

ubIsInjective
  :: forall {r0 :: Types} (f :: Types -> Types) (a :: Types) (b :: Types) cont. 
  ( UpperBound (f a) (f b) ~ Just (f r0)
  , SingI a 
  , SingI b
  , SingI r0
  ) => (UpperBound a b ~ Just r0 => cont) -> cont
ubIsInjective f =  withSingIUBType @a @b $ case decideEquality (sing @(UpperBound a b)) (sing @(Just r0)) of
  Just Refl -> f 
  Nothing   -> error "impossible case"


ubIsInjective'
  :: forall  (f :: Types -> Types) (a :: Types) (b :: Types) cont. 
  ( UpperBound (f a) (f b) ~ Nothing 
  , SingI a 
  , SingI b
  ) => (UpperBound a b ~ Nothing => cont) -> cont
ubIsInjective' f =  withSingIUBType @a @b $ case decideEquality (sing @(UpperBound a b)) (sing @Nothing) of
  Just Refl -> f 
  Nothing   -> error "impossible case"





{-| Convinient "transitive" property... For the time being taken as axiom... 
TODO: Make a proof, just another take on associativity.

\[a \vee b = c\]
\[a \vee c = c\]
-}
ubIsUb :: forall {r0 :: Types} (a :: Types) (b :: Types) cont.
  ( UpperBound a b ~ Just r0 
  , SingI a
  , SingI b
  , SingI r0
  ) 
  => (UpperBound a r0 ~ Just r0 => cont) -> cont
ubIsUb !f =  withSingIUBType @a @r0 $  case decideEquality (sing @(UpperBound a r0 )) (sing @(Just r0)) of
  Just Refl -> f
  Nothing -> error "impossible case"


btIsInductive :: forall {b} (a :: Types) cont.
  ( SingI a
  , BaseType a ~ b
  ) => (BaseType (Lazy a) ~ b => cont) -> cont
btIsInductive f = undefined


type family HasLazy (x :: Types) :: Bool where 
  HasLazy (Value _) = False 
  HasLazy (Array a) = HasLazy a
  HasLazy (LazyS a) = HasLazy a
  HasLazy (Lazy _)  = True





type TypesCaseAnalysis (c :: Types -> Constraint) = 
    ( C c Value
    , C c Lazy 
    , C c LazyS
    , C c Array 
    )

typesCaseAnalysis :: forall 
  (c :: Types -> Constraint)
  (x :: Types).
  ( TypesCaseAnalysis c
  , SingI x 
  ) => Dict (c x) 
typesCaseAnalysis = case sing @x of 
  SValue _ -> Dict 
  SLazy  _ -> Dict 
  SLazyS _ -> Dict 
  SArray _ -> Dict
