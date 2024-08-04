{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
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
-- Module      :  GHC.TypeLits.Singletons.Internal
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines and exports singletons useful for the 'Natural', 'TL.Symbol', and
-- 'Char' kinds. This exports the internal, unsafe constructors. Use import
-- "GHC.TypeLits.Singletons" for a safe interface.
--
----------------------------------------------------------------------------

module GHC.TypeLits.Singletons.Internal (
  Sing,

  Natural, TL.Symbol, Char,
  TN.SNat, pattern TN.SNat,
  TL.SSymbol, pattern TL.SSymbol, pattern SSym,
  TL.SChar, pattern TL.SChar,
  TN.withKnownNat, TL.withKnownSymbol, TL.withKnownChar,
  Error, sError,
  ErrorWithoutStackTrace, sErrorWithoutStackTrace,
  Undefined, sUndefined,
  TL.KnownNat, TN.natVal, TL.KnownSymbol, TL.symbolVal, TL.KnownChar, TL.charVal,
  type (TN.^), (%^),
  type (TN.<=?), (%<=?),

  -- * Defunctionalization symbols
  ErrorSym0, ErrorSym1,
  ErrorWithoutStackTraceSym0, ErrorWithoutStackTraceSym1,
  UndefinedSym0,
  type (^@#@$),  type (^@#@$$),  type (^@#@$$$),
  type (<=?@#@$),  type (<=?@#@$$),  type (<=?@#@$$$)
  ) where

import Data.Bool.Singletons
import Data.Eq.Singletons
import Data.Ord.Singletons as O
import Data.Semigroup.Singletons.Internal.Classes
import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.TH
import Data.Type.Equality (TestEquality(..))
import GHC.Stack (HasCallStack)
import qualified GHC.TypeLits as TL
import qualified GHC.TypeNats as TN
import Numeric.Natural (Natural)
import Unsafe.Coerce

import qualified Data.Text as T
import Data.Text ( Text )
import Data.Kind (Type)

----------------------------------------------------------------------
---- TypeLits singletons ---------------------------------------------
----------------------------------------------------------------------

-- SNat
type instance Sing @Natural = TN.SNat

instance TN.KnownNat n => SingI n where
  sing = TN.natSing

instance SingKind Natural where
  type Demote Natural = Natural
  fromSing = TN.fromSNat
  toSing n = TN.withSomeSNat n SomeSing

-- STL.Symbol
type instance Sing @TL.Symbol = TL.SSymbol

-- | An alias for the 'TL.SSymbol' pattern synonym.
pattern SSym :: forall s. () => TL.KnownSymbol s => TL.SSymbol s
pattern SSym = TL.SSymbol
{-# COMPLETE SSym #-}

instance TL.KnownSymbol n => SingI n where
  sing = TL.symbolSing

instance SingKind TL.Symbol where
  type Demote TL.Symbol = Text
  fromSing = T.pack . TL.fromSSymbol
  toSing s = TL.withSomeSSymbol (T.unpack s) SomeSing

-- SChar
type instance Sing @Char = TL.SChar

instance TL.KnownChar c => SingI c where
  sing = TL.charSing

instance SingKind Char where
  type Demote Char = Char
  fromSing = TL.fromSChar
  toSing c = TL.withSomeSChar c SomeSing

-- SDecide instances:
instance SDecide Natural where
  sn %~ sm
    | Just r <- testEquality sn sm
    = Proved r
    | otherwise
    = Disproved (\Refl -> error errStr)
    where errStr = "Broken Natural singletons"

instance SDecide TL.Symbol where
  sn %~ sm
    | Just r <- testEquality sn sm
    = Proved r
    | otherwise
    = Disproved (\Refl -> error errStr)
    where errStr = "Broken TL.Symbol singletons"

instance SDecide Char where
  sn %~ sm
    | Just r <- testEquality sn sm
    = Proved r
    | otherwise
    = Disproved (\Refl -> error errStr)
    where errStr = "Broken Char singletons"

-- PEq instances
instance PEq Natural where
  type x == y = DefaultEq x y
instance PEq TL.Symbol where
  type x == y = DefaultEq x y
instance PEq Char where
  type x == y = DefaultEq x y

-- need SEq instances for TypeLits kinds
instance SEq Natural where
  sn %== sm
    = case testEquality sn sm of
        Just Refl -> STrue
        Nothing   -> unsafeCoerce SFalse

instance SEq TL.Symbol where
  sn %== sm
    = case testEquality sn sm of
        Just Refl -> STrue
        Nothing   -> unsafeCoerce SFalse

instance SEq Char where
  sn %== sm
    = case testEquality sn sm of
        Just Refl -> STrue
        Nothing   -> unsafeCoerce SFalse

-- POrd instances
instance POrd Natural where
  type (a :: Natural) `Compare` (b :: Natural) = a `TN.CmpNat` b

instance POrd TL.Symbol where
  type (a :: TL.Symbol) `Compare` (b :: TL.Symbol) = a `TL.CmpSymbol` b

instance POrd Char where
  type (a :: Char) `Compare` (b :: Char) = a `TL.CmpChar` b

-- SOrd instances
instance SOrd Natural where
  a `sCompare` b = case fromSing a `compare` fromSing b of
                     LT -> unsafeCoerce SLT
                     EQ -> unsafeCoerce SEQ
                     GT -> unsafeCoerce SGT

instance SOrd TL.Symbol where
  a `sCompare` b = case fromSing a `compare` fromSing b of
                     LT -> unsafeCoerce SLT
                     EQ -> unsafeCoerce SEQ
                     GT -> unsafeCoerce SGT

instance SOrd Char where
  a `sCompare` b = case fromSing a `compare` fromSing b of
                     LT -> unsafeCoerce SLT
                     EQ -> unsafeCoerce SEQ
                     GT -> unsafeCoerce SGT

-- PSemigroup instance

instance PSemigroup TL.Symbol where
  type a <> b = TL.AppendSymbol a b

-- SSemigroup instance

instance SSemigroup TL.Symbol where
  sa %<> sb =
    let a  = fromSing sa
        b  = fromSing sb
    in TL.withSomeSSymbol (T.unpack (a <> b)) unsafeCoerce

-- Convenience functions

-- | A promoted version of 'error'. This implements 'Error' as a stuck type
-- family with a 'Symbol' argument. Depending on your needs, you might also
-- consider the following alternatives:
--
-- * "Data.Singletons.Base.PolyError" provides @PolyError@, which generalizes
--   the argument to be kind-polymorphic. This allows passing additional
--   information to the error besides raw 'Symbol's.
--
-- * "Data.Singletons.Base.TypeError" provides @TypeError@, a slightly modified
--   version of the custom type error machinery found in "GHC.TypeLits". This
--   allows emitting error messages as compiler errors rather than as stuck type
--   families.
type Error :: TL.Symbol -> a
type family Error (str :: TL.Symbol) :: a where {}

type ErrorSym0 :: forall (a_a1y8t :: Type). (~>) TL.Symbol a_a1y8t
data ErrorSym0 :: (~>) TL.Symbol a_a1y8t
  where
    ErrorSym0KindInference :: SameKind (Apply ErrorSym0 arg_a1yC1) (ErrorSym1 arg_a1yC1) =>
                              ErrorSym0 a6989586621679381174
type instance Apply @TL.Symbol @a_a1y8t ErrorSym0 a6989586621679381174 = Error a6989586621679381174
instance SuppressUnusedWarnings ErrorSym0 where
  suppressUnusedWarnings = snd ((,) ErrorSym0KindInference ())
type ErrorSym1 :: forall (a_a1y8t :: Type). TL.Symbol -> a_a1y8t
type family ErrorSym1 @(a_a1y8t :: Type) (a6989586621679381174 :: TL.Symbol) :: a_a1y8t where
  ErrorSym1 a6989586621679381174 = Error a6989586621679381174

instance SingI (ErrorSym0 :: TL.Symbol ~> a) where
  sing = singFun1 sError

-- | The singleton for 'error'.
sError :: forall a (str :: TL.Symbol). HasCallStack => Sing str -> Sing (Error @a str)
sError sstr = error (T.unpack (fromSing sstr))

-- | The promotion of 'errorWithoutStackTrace'.
type ErrorWithoutStackTrace :: TL.Symbol -> a
type family ErrorWithoutStackTrace (str :: TL.Symbol) :: a where {}

type ErrorWithoutStackTraceSym0 :: forall (a_a1yC8 :: Type). (~>) TL.Symbol a_a1yC8
data ErrorWithoutStackTraceSym0 :: (~>) TL.Symbol a_a1yC8
  where
    ErrorWithoutStackTraceSym0KindInference :: SameKind (Apply ErrorWithoutStackTraceSym0 arg_a1yGr) (ErrorWithoutStackTraceSym1 arg_a1yGr) =>
                                                ErrorWithoutStackTraceSym0 a6989586621679381448
type instance Apply @TL.Symbol @a_a1yC8 ErrorWithoutStackTraceSym0 a6989586621679381448 = ErrorWithoutStackTrace a6989586621679381448
instance SuppressUnusedWarnings ErrorWithoutStackTraceSym0 where
  suppressUnusedWarnings
    = snd ((,) ErrorWithoutStackTraceSym0KindInference ())
type ErrorWithoutStackTraceSym1 :: forall (a_a1yC8 :: Type). TL.Symbol
                                                              -> a_a1yC8
type family ErrorWithoutStackTraceSym1 @(a_a1yC8 :: Type) (a6989586621679381448 :: TL.Symbol) :: a_a1yC8 where
  ErrorWithoutStackTraceSym1 a6989586621679381448 = ErrorWithoutStackTrace a6989586621679381448

instance SingI (ErrorWithoutStackTraceSym0 :: TL.Symbol ~> a) where
  sing = singFun1 sErrorWithoutStackTrace

-- | The singleton for 'errorWithoutStackTrace'.
sErrorWithoutStackTrace :: forall a (str :: TL.Symbol). Sing str -> Sing (ErrorWithoutStackTrace @a str)
sErrorWithoutStackTrace sstr = errorWithoutStackTrace (T.unpack (fromSing sstr))

-- | The promotion of 'undefined'.
type Undefined :: a
type family Undefined :: a where {}


type UndefinedSym0 :: forall (a_a1yGy :: Type). a_a1yGy
type family UndefinedSym0 @(a_a1yGy :: Type) :: a_a1yGy where
  UndefinedSym0 = Undefined

-- | The singleton for 'undefined'.
sUndefined :: forall a. HasCallStack => Sing (Undefined @a)
sUndefined = undefined

-- | The singleton analogue of '(TN.^)' for 'Natural's.
(%^) :: Sing a -> Sing b -> Sing (a TN.^ b)
sa %^ sb =
  let a = fromSing sa
      b = fromSing sb
  in TN.withSomeSNat (a ^ b) unsafeCoerce
infixr 8 %^

-- Defunctionalization symbols for type-level (^)

type (^@#@$) :: (~>) Natural ((~>) Natural Natural)
data (^@#@$) :: (~>) Natural ((~>) Natural Natural)
  where
    (:^@#@$###) :: SameKind (Apply (^@#@$) arg_a1yNq) ((^@#@$$) arg_a1yNq) =>
                    (^@#@$) a6989586621679381881
type instance Apply @Natural @((~>) Natural Natural) (^@#@$) a6989586621679381881 = (^@#@$$) a6989586621679381881
instance SuppressUnusedWarnings (^@#@$) where
  suppressUnusedWarnings = snd ((,) (:^@#@$###) ())
infixr 8 ^@#@$
type (^@#@$$) :: Natural -> (~>) Natural Natural
data (^@#@$$) (a6989586621679381881 :: Natural) :: (~>) Natural Natural
  where
    (:^@#@$$###) :: SameKind (Apply ((^@#@$$) a6989586621679381881) arg_a1yNq) ((^@#@$$$) a6989586621679381881 arg_a1yNq) =>
                    (^@#@$$) a6989586621679381881 a6989586621679381882
type instance Apply @Natural @Natural ((^@#@$$) a6989586621679381881) a6989586621679381882 = (TN.^) a6989586621679381881 a6989586621679381882
instance SuppressUnusedWarnings ((^@#@$$) a6989586621679381881) where
  suppressUnusedWarnings = snd ((,) (:^@#@$$###) ())
infixr 8 ^@#@$$
type (^@#@$$$) :: Natural -> Natural -> Natural
type family (^@#@$$$) (a6989586621679381881 :: Natural) (a6989586621679381882 :: Natural) :: Natural where
  (^@#@$$$) a6989586621679381881 a6989586621679381882 = (TN.^) a6989586621679381881 a6989586621679381882
infixr 8 ^@#@$$$

instance SingI (^@#@$) where
  sing = singFun2 (%^)
instance SingI x => SingI ((^@#@$$) x) where
  sing = singFun1 (sing @x %^)
instance SingI1 (^@#@$$) where
  liftSing s = singFun1 (s %^)

-- | The singleton analogue of 'TN.<=?'
--
-- Note that, because of historical reasons in GHC's 'Natural' API, 'TN.<=?'
-- is incompatible (unification-wise) with 'O.<=' and the 'PEq', 'SEq',
-- 'POrd', and 'SOrd' instances for 'Natural'.  @(a '<=?' b) ~ 'True@ does not
-- imply anything about @a 'O.<=' b@ or any other 'PEq' / 'POrd'
-- relationships.
--
-- (Be aware that 'O.<=' in the paragraph above refers to 'O.<=' from the
-- 'POrd' typeclass, exported from "Data.Ord.Singletons", and /not/
-- the 'TN.<=' from "GHC.TypeNats".  The latter is simply a type alias for
-- @(a 'TN.<=?' b) ~ 'True@.)
--
-- This is provided here for the sake of completeness and for compatibility
-- with libraries with APIs built around '<=?'.  New code should use
-- 'CmpNat', exposed through this library through the 'POrd' and 'SOrd'
-- instances for 'Natural'.
(%<=?) :: forall (a :: Natural) (b :: Natural). Sing a -> Sing b -> Sing (a TN.<=? b)
sa %<=? sb = unsafeCoerce (sa %<= sb)
infix 4 %<=?

-- Defunctionalization symbols for (<=?)

type (<=?@#@$) :: forall (k_a1yQG :: Type). (~>) k_a1yQG ((~>) k_a1yQG Bool)
data (<=?@#@$) :: (~>) k_a1yQG ((~>) k_a1yQG Bool)
  where
    (:<=?@#@$###) :: SameKind (Apply (<=?@#@$) arg_a1yUr) ((<=?@#@$$) arg_a1yUr) =>
                      (<=?@#@$) a6989586621679382316
type instance Apply @k_a1yQG @((~>) k_a1yQG Bool) (<=?@#@$) a6989586621679382316 = (<=?@#@$$) a6989586621679382316
instance SuppressUnusedWarnings (<=?@#@$) where
  suppressUnusedWarnings = snd ((,) (:<=?@#@$###) ())
infix 4 <=?@#@$
type (<=?@#@$$) :: forall (k_a1yQG :: Type). k_a1yQG
                                              -> (~>) k_a1yQG Bool
data (<=?@#@$$) (a6989586621679382316 :: k_a1yQG) :: (~>) k_a1yQG Bool
  where
    (:<=?@#@$$###) :: SameKind (Apply ((<=?@#@$$) a6989586621679382316) arg_a1yUr) ((<=?@#@$$$) a6989586621679382316 arg_a1yUr) =>
                      (<=?@#@$$) a6989586621679382316 a6989586621679382317
type instance Apply @k_a1yQG @Bool ((<=?@#@$$) a6989586621679382316) a6989586621679382317 = (TN.<=?) a6989586621679382316 a6989586621679382317
instance SuppressUnusedWarnings ((<=?@#@$$) a6989586621679382316) where
  suppressUnusedWarnings = snd ((,) (:<=?@#@$$###) ())
infix 4 <=?@#@$$
type (<=?@#@$$$) :: forall (k_a1yQG :: Type). k_a1yQG
                                              -> k_a1yQG -> Bool
type family (<=?@#@$$$) @(k_a1yQG :: Type) (a6989586621679382316 :: k_a1yQG) (a6989586621679382317 :: k_a1yQG) :: Bool where
  (<=?@#@$$$) a6989586621679382316 a6989586621679382317 = (TN.<=?) a6989586621679382316 a6989586621679382317
infix 4 <=?@#@$$$


instance SingI ((<=?@#@$) @Natural) where
  sing = singFun2 (%<=?)
instance SingI x => SingI ((<=?@#@$$) @Natural x) where
  sing = singFun1 (sing @x %<=?)
instance SingI1 ((<=?@#@$$) @Natural) where
  liftSing s = singFun1 (s %<=?)
