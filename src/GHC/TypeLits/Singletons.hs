{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

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
-- Module      :  GHC.TypeLits.Singletons
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines and exports singletons useful for the Natural, Symbol, and Char
-- kinds.
--
----------------------------------------------------------------------------

module GHC.TypeLits.Singletons (
  Natural, Symbol, Char,
  Sing,
  SNat, pattern SNat,
  SSymbol, pattern SSymbol, pattern SSym,
  SChar, pattern SChar,
  withKnownNat, withKnownSymbol, withKnownChar,
  Error, sError,
  ErrorWithoutStackTrace, sErrorWithoutStackTrace,
  Undefined, sUndefined,
  KnownNat, natVal,
  KnownSymbol, symbolVal,
  KnownChar, charVal,

  type (^), (%^),
  type (<=?), (%<=?),

  TN.Log2, sLog2,
  Div, sDiv, Mod, sMod, DivMod, sDivMod,
  Quot, sQuot, Rem, sRem, QuotRem, sQuotRem,

  consSymbol, ConsSymbol, sConsSymbol,
  unconsSymbol, UnconsSymbol, sUnconsSymbol,
  charToNat, CharToNat, sCharToNat,
  natToChar, NatToChar, sNatToChar,

  -- * Defunctionalization symbols
  ErrorSym0, ErrorSym1,
  ErrorWithoutStackTraceSym0, ErrorWithoutStackTraceSym1,
  UndefinedSym0,
  KnownNatSym0, KnownNatSym1,
  KnownSymbolSym0, KnownSymbolSym1,
  KnownCharSym0, KnownCharSym1,
  type (^@#@$), type (^@#@$$), type (^@#@$$$),
  type (<=?@#@$), type (<=?@#@$$), type (<=?@#@$$$),
  Log2Sym0, Log2Sym1,
  DivSym0, DivSym1, DivSym2,
  ModSym0, ModSym1, ModSym2,
  DivModSym0, DivModSym1, DivModSym2,
  QuotSym0, QuotSym1, QuotSym2,
  RemSym0, RemSym1, RemSym2,
  QuotRemSym0, QuotRemSym1, QuotRemSym2,
  ConsSymbolSym0, ConsSymbolSym1, ConsSymbolSym2,
  UnconsSymbolSym0, UnconsSymbolSym1,
  CharToNatSym0, CharToNatSym1,
  NatToCharSym0, NatToCharSym1
  ) where

import Data.Char (chr, ord)
import qualified Data.List as L (uncons)
import Data.Singletons
import Data.Singletons.TH
import Data.String (IsString(..))
import qualified Data.Text as T
import Data.Tuple.Singletons
import GHC.TypeLits ( CharToNat, ConsSymbol, NatToChar, UnconsSymbol
                    , withSomeSChar, withSomeSSymbol )
import GHC.TypeLits.Singletons.Internal
import qualified GHC.TypeNats as TN
import GHC.TypeNats (Div, Mod)
import Unsafe.Coerce
import Data.Kind (Constraint)

-- | This bogus instance is helpful for people who want to define
-- functions over Symbols that will only be used at the type level or
-- as singletons.
instance Eq Symbol where
  (==)        = no_term_level_syms

instance Ord Symbol where
  compare     = no_term_level_syms

instance IsString Symbol where
  fromString  = no_term_level_syms

instance Semigroup Symbol where
  (<>) = no_term_level_syms

instance Monoid Symbol where
  mempty = no_term_level_syms

instance Show Symbol where
  showsPrec = no_term_level_syms

no_term_level_syms :: a
no_term_level_syms = error "The kind `Symbol` may not be used at the term level."

-- These are often useful in TypeLits-heavy code
type KnownNatSym0 :: (~>) TN.Nat Constraint
data KnownNatSym0 :: (~>) TN.Nat Constraint
  where
    KnownNatSym0KindInference :: SameKind (Apply KnownNatSym0 arg_a1CHN) (KnownNatSym1 arg_a1CHN) =>
                                  KnownNatSym0 a6989586621679396908
type instance Apply @TN.Nat @Constraint KnownNatSym0 a6989586621679396908 = KnownNat a6989586621679396908
instance SuppressUnusedWarnings KnownNatSym0 where
  suppressUnusedWarnings = snd ((,) KnownNatSym0KindInference ())
type KnownNatSym1 :: TN.Nat -> Constraint
type family KnownNatSym1 (a6989586621679396908 :: TN.Nat) :: Constraint where
  KnownNatSym1 a6989586621679396908 = KnownNat a6989586621679396908
type KnownSymbolSym0 :: (~>) Symbol Constraint
data KnownSymbolSym0 :: (~>) Symbol Constraint
  where
    KnownSymbolSym0KindInference :: SameKind (Apply KnownSymbolSym0 arg_a1CHP) (KnownSymbolSym1 arg_a1CHP) =>
                                    KnownSymbolSym0 a6989586621679396910
type instance Apply @Symbol @Constraint KnownSymbolSym0 a6989586621679396910 = KnownSymbol a6989586621679396910
instance SuppressUnusedWarnings KnownSymbolSym0 where
  suppressUnusedWarnings = snd ((,) KnownSymbolSym0KindInference ())
type KnownSymbolSym1 :: Symbol -> Constraint
type family KnownSymbolSym1 (a6989586621679396910 :: Symbol) :: Constraint where
  KnownSymbolSym1 a6989586621679396910 = KnownSymbol a6989586621679396910
type KnownCharSym0 :: (~>) Char Constraint
data KnownCharSym0 :: (~>) Char Constraint
  where
    KnownCharSym0KindInference :: SameKind (Apply KnownCharSym0 arg_a1CHR) (KnownCharSym1 arg_a1CHR) =>
                                  KnownCharSym0 a6989586621679396912
type instance Apply @Char @Constraint KnownCharSym0 a6989586621679396912 = KnownChar a6989586621679396912
instance SuppressUnusedWarnings KnownCharSym0 where
  suppressUnusedWarnings = snd ((,) KnownCharSym0KindInference ())
type KnownCharSym1 :: Char -> Constraint
type family KnownCharSym1 (a6989586621679396912 :: Char) :: Constraint where
  KnownCharSym1 a6989586621679396912 = KnownChar a6989586621679396912

------------------------------------------------------------
-- Log2, Div, Mod, DivMod, and friends
------------------------------------------------------------

{- | Adapted from GHC's source code.

Compute the logarithm of a number in the given base, rounded down to the
closest integer. -}
genLog2 :: Natural -> Natural
genLog2 x = exactLoop 0 x
  where
  exactLoop s i
    | i == 1     = s
    | i < 2      = s
    | otherwise  =
        let s1 = s + 1
        in s1 `seq` case divMod i 2 of
                      (j,r)
                        | r == 0    -> exactLoop s1 j
                        | otherwise -> underLoop s1 j

  underLoop s i
    | i < 2  = s
    | otherwise = let s1 = s + 1 in s1 `seq` underLoop s1 (div i 2)


sLog2 :: Sing x -> Sing (TN.Log2 x)
sLog2 sx =
    let x = fromSing sx
    in case x of
         0 -> error "log2 of 0"
         _ -> TN.withSomeSNat (genLog2 x) unsafeCoerce

type Log2Sym0 :: (~>) Natural Natural
data Log2Sym0 :: (~>) Natural Natural
  where
    Log2Sym0KindInference :: SameKind (Apply Log2Sym0 arg_a1CS6) (Log2Sym1 arg_a1CS6) =>
                              Log2Sym0 a6989586621679397547
type instance Apply @Natural @Natural Log2Sym0 a6989586621679397547 = TN.Log2 a6989586621679397547
instance SuppressUnusedWarnings Log2Sym0 where
  suppressUnusedWarnings = snd ((,) Log2Sym0KindInference ())
type Log2Sym1 :: Natural -> Natural
type family Log2Sym1 (a6989586621679397547 :: Natural) :: Natural where
  Log2Sym1 a6989586621679397547 = TN.Log2 a6989586621679397547

instance SingI Log2Sym0 where
  sing = singFun1 sLog2

sDiv :: Sing x -> Sing y -> Sing (Div x y)
sDiv sx sy =
    let x = fromSing sx
        y = fromSing sy
    in TN.withSomeSNat (x `div` y) unsafeCoerce
infixl 7 `sDiv`

type DivSym0 :: (~>) Natural ((~>) Natural Natural)
data DivSym0 :: (~>) Natural ((~>) Natural Natural)
  where
    DivSym0KindInference :: SameKind (Apply DivSym0 arg_a1CVL) (DivSym1 arg_a1CVL) =>
                            DivSym0 a6989586621679397774
type instance Apply @Natural @((~>) Natural Natural) DivSym0 a6989586621679397774 = DivSym1 a6989586621679397774
instance SuppressUnusedWarnings DivSym0 where
  suppressUnusedWarnings = snd ((,) DivSym0KindInference ())
infixl 7 `DivSym0`
type DivSym1 :: Natural -> (~>) Natural Natural
data DivSym1 (a6989586621679397774 :: Natural) :: (~>) Natural Natural
  where
    DivSym1KindInference :: SameKind (Apply (DivSym1 a6989586621679397774) arg_a1CVL) (DivSym2 a6989586621679397774 arg_a1CVL) =>
                            DivSym1 a6989586621679397774 a6989586621679397775
type instance Apply @Natural @Natural (DivSym1 a6989586621679397774) a6989586621679397775 = Div a6989586621679397774 a6989586621679397775
instance SuppressUnusedWarnings (DivSym1 a6989586621679397774) where
  suppressUnusedWarnings = snd ((,) DivSym1KindInference ())
infixl 7 `DivSym1`
type DivSym2 :: Natural -> Natural -> Natural
type family DivSym2 (a6989586621679397774 :: Natural) (a6989586621679397775 :: Natural) :: Natural where
  DivSym2 a6989586621679397774 a6989586621679397775 = Div a6989586621679397774 a6989586621679397775
infixl 7 `DivSym2`

instance SingI DivSym0 where
  sing = singFun2 sDiv
instance SingI x => SingI (DivSym1 x) where
  sing = singFun1 $ sDiv (sing @x)
instance SingI1 DivSym1 where
  liftSing s = singFun1 $ sDiv s

sMod :: Sing x -> Sing y -> Sing (Mod x y)
sMod sx sy =
    let x = fromSing sx
        y = fromSing sy
    in TN.withSomeSNat (x `mod` y) unsafeCoerce
infixl 7 `sMod`

type ModSym0 :: (~>) Natural ((~>) Natural Natural)
data ModSym0 :: (~>) Natural ((~>) Natural Natural)
  where
    ModSym0KindInference :: SameKind (Apply ModSym0 arg_a1D2S) (ModSym1 arg_a1D2S) =>
                            ModSym0 a6989586621679398215
type instance Apply @Natural @((~>) Natural Natural) ModSym0 a6989586621679398215 = ModSym1 a6989586621679398215
instance SuppressUnusedWarnings ModSym0 where
  suppressUnusedWarnings = snd ((,) ModSym0KindInference ())
infixl 7 `ModSym0`
type ModSym1 :: Natural -> (~>) Natural Natural
data ModSym1 (a6989586621679398215 :: Natural) :: (~>) Natural Natural
  where
    ModSym1KindInference :: SameKind (Apply (ModSym1 a6989586621679398215) arg_a1D2S) (ModSym2 a6989586621679398215 arg_a1D2S) =>
                            ModSym1 a6989586621679398215 a6989586621679398216
type instance Apply @Natural @Natural (ModSym1 a6989586621679398215) a6989586621679398216 = Mod a6989586621679398215 a6989586621679398216
instance SuppressUnusedWarnings (ModSym1 a6989586621679398215) where
  suppressUnusedWarnings = snd ((,) ModSym1KindInference ())
infixl 7 `ModSym1`
type ModSym2 :: Natural -> Natural -> Natural
type family ModSym2 (a6989586621679398215 :: Natural) (a6989586621679398216 :: Natural) :: Natural where
  ModSym2 a6989586621679398215 a6989586621679398216 = Mod a6989586621679398215 a6989586621679398216
infixl 7 `ModSym2`

instance SingI ModSym0 where
  sing = singFun2 sMod
instance SingI x => SingI (ModSym1 x) where
  sing = singFun1 $ sMod $ sing @x
instance SingI1 ModSym1 where
  liftSing s = singFun1 $ sMod s

type RemSym0 :: (~>) Natural ((~>) Natural Natural)
data RemSym0 :: (~>) Natural ((~>) Natural Natural)
  where
    RemSym0KindInference :: SameKind (Apply RemSym0 arg_a1DcI) (RemSym1 arg_a1DcI) =>
                            RemSym0 a6989586621679398825
type instance Apply @Natural @((~>) Natural Natural) RemSym0 a6989586621679398825 = RemSym1 a6989586621679398825
instance SuppressUnusedWarnings RemSym0 where
  suppressUnusedWarnings = snd ((,) RemSym0KindInference ())
infixl 7 `RemSym0`
type RemSym1 :: Natural -> (~>) Natural Natural
data RemSym1 (a6989586621679398825 :: Natural) :: (~>) Natural Natural
  where
    RemSym1KindInference :: SameKind (Apply (RemSym1 a6989586621679398825) arg_a1DcI) (RemSym2 a6989586621679398825 arg_a1DcI) =>
                            RemSym1 a6989586621679398825 a6989586621679398826
type instance Apply @Natural @Natural (RemSym1 a6989586621679398825) a6989586621679398826 = Rem a6989586621679398825 a6989586621679398826
instance SuppressUnusedWarnings (RemSym1 a6989586621679398825) where
  suppressUnusedWarnings = snd ((,) RemSym1KindInference ())
infixl 7 `RemSym1`
type RemSym2 :: Natural -> Natural -> Natural
type family RemSym2 (a6989586621679398825 :: Natural) (a6989586621679398826 :: Natural) :: Natural where
  RemSym2 a6989586621679398825 a6989586621679398826 = Rem a6989586621679398825 a6989586621679398826
infixl 7 `RemSym2`
type QuotSym0 :: (~>) Natural ((~>) Natural Natural)
data QuotSym0 :: (~>) Natural ((~>) Natural Natural)
  where
    QuotSym0KindInference :: SameKind (Apply QuotSym0 arg_a1DcT) (QuotSym1 arg_a1DcT) =>
                              QuotSym0 a6989586621679398836
type instance Apply @Natural @((~>) Natural Natural) QuotSym0 a6989586621679398836 = QuotSym1 a6989586621679398836
instance SuppressUnusedWarnings QuotSym0 where
  suppressUnusedWarnings = snd ((,) QuotSym0KindInference ())
infixl 7 `QuotSym0`
type QuotSym1 :: Natural -> (~>) Natural Natural
data QuotSym1 (a6989586621679398836 :: Natural) :: (~>) Natural Natural
  where
    QuotSym1KindInference :: SameKind (Apply (QuotSym1 a6989586621679398836) arg_a1DcT) (QuotSym2 a6989586621679398836 arg_a1DcT) =>
                              QuotSym1 a6989586621679398836 a6989586621679398837
type instance Apply @Natural @Natural (QuotSym1 a6989586621679398836) a6989586621679398837 = Quot a6989586621679398836 a6989586621679398837
instance SuppressUnusedWarnings (QuotSym1 a6989586621679398836) where
  suppressUnusedWarnings = snd ((,) QuotSym1KindInference ())
infixl 7 `QuotSym1`
type QuotSym2 :: Natural -> Natural -> Natural
type family QuotSym2 (a6989586621679398836 :: Natural) (a6989586621679398837 :: Natural) :: Natural where
  QuotSym2 a6989586621679398836 a6989586621679398837 = Quot a6989586621679398836 a6989586621679398837
infixl 7 `QuotSym2`
type QuotRemSym0 :: (~>) Natural ((~>) Natural (Natural, Natural))
data QuotRemSym0 :: (~>) Natural ((~>) Natural (Natural, Natural))
  where
    QuotRemSym0KindInference :: SameKind (Apply QuotRemSym0 arg_a1Dd4) (QuotRemSym1 arg_a1Dd4) =>
                                QuotRemSym0 a6989586621679398847
type instance Apply @Natural @((~>) Natural (Natural,
                                              Natural)) QuotRemSym0 a6989586621679398847 = QuotRemSym1 a6989586621679398847
instance SuppressUnusedWarnings QuotRemSym0 where
  suppressUnusedWarnings = snd ((,) QuotRemSym0KindInference ())
type QuotRemSym1 :: Natural -> (~>) Natural (Natural, Natural)
data QuotRemSym1 (a6989586621679398847 :: Natural) :: (~>) Natural (Natural,
                                                                    Natural)
  where
    QuotRemSym1KindInference :: SameKind (Apply (QuotRemSym1 a6989586621679398847) arg_a1Dd4) (QuotRemSym2 a6989586621679398847 arg_a1Dd4) =>
                                QuotRemSym1 a6989586621679398847 a6989586621679398848
type instance Apply @Natural @(Natural,
                                Natural) (QuotRemSym1 a6989586621679398847) a6989586621679398848 = QuotRem a6989586621679398847 a6989586621679398848
instance SuppressUnusedWarnings (QuotRemSym1 a6989586621679398847) where
  suppressUnusedWarnings = snd ((,) QuotRemSym1KindInference ())
type QuotRemSym2 :: Natural -> Natural -> (Natural, Natural)
type family QuotRemSym2 (a6989586621679398847 :: Natural) (a6989586621679398848 :: Natural) :: (Natural,
                                                                                                Natural) where
  QuotRemSym2 a6989586621679398847 a6989586621679398848 = QuotRem a6989586621679398847 a6989586621679398848
type DivModSym0 :: (~>) Natural ((~>) Natural (Natural, Natural))
data DivModSym0 :: (~>) Natural ((~>) Natural (Natural, Natural))
  where
    DivModSym0KindInference :: SameKind (Apply DivModSym0 arg_a1Ddb) (DivModSym1 arg_a1Ddb) =>
                                DivModSym0 a6989586621679398854
type instance Apply @Natural @((~>) Natural (Natural,
                                              Natural)) DivModSym0 a6989586621679398854 = DivModSym1 a6989586621679398854
instance SuppressUnusedWarnings DivModSym0 where
  suppressUnusedWarnings = snd ((,) DivModSym0KindInference ())
type DivModSym1 :: Natural -> (~>) Natural (Natural, Natural)
data DivModSym1 (a6989586621679398854 :: Natural) :: (~>) Natural (Natural,
                                                                    Natural)
  where
    DivModSym1KindInference :: SameKind (Apply (DivModSym1 a6989586621679398854) arg_a1Ddb) (DivModSym2 a6989586621679398854 arg_a1Ddb) =>
                                DivModSym1 a6989586621679398854 a6989586621679398855
type instance Apply @Natural @(Natural,
                                Natural) (DivModSym1 a6989586621679398854) a6989586621679398855 = DivMod a6989586621679398854 a6989586621679398855
instance SuppressUnusedWarnings (DivModSym1 a6989586621679398854) where
  suppressUnusedWarnings = snd ((,) DivModSym1KindInference ())
type DivModSym2 :: Natural -> Natural -> (Natural, Natural)
type family DivModSym2 (a6989586621679398854 :: Natural) (a6989586621679398855 :: Natural) :: (Natural,
                                                                                                Natural) where
  DivModSym2 a6989586621679398854 a6989586621679398855 = DivMod a6989586621679398854 a6989586621679398855
type Rem :: Natural -> Natural -> Natural
type family Rem (a_a1DcG :: Natural) (a_a1DcH :: Natural) :: Natural where
  Rem a_6989586621679398818_a1DcL a_6989586621679398820_a1DcM = Apply (Apply ModSym0 a_6989586621679398818_a1DcL) a_6989586621679398820_a1DcM
type Quot :: Natural -> Natural -> Natural
type family Quot (a_a1DcR :: Natural) (a_a1DcS :: Natural) :: Natural where
  Quot a_6989586621679398829_a1DcW a_6989586621679398831_a1DcX = Apply (Apply DivSym0 a_6989586621679398829_a1DcW) a_6989586621679398831_a1DcX
type QuotRem :: Natural -> Natural -> (Natural, Natural)
type family QuotRem (a_a1Dd2 :: Natural) (a_a1Dd3 :: Natural) :: (Natural,
                                                                  Natural) where
  QuotRem a_6989586621679398840_a1Dd7 a_6989586621679398842_a1Dd8 = Apply (Apply DivModSym0 a_6989586621679398840_a1Dd7) a_6989586621679398842_a1Dd8
type DivMod :: Natural -> Natural -> (Natural, Natural)
type family DivMod (a_a1Dd9 :: Natural) (a_a1Dda :: Natural) :: (Natural,
                                                                  Natural) where
  DivMod x_a1Dde y_a1Ddf = Apply (Apply Tuple2Sym0 (Apply (Apply DivSym0 x_a1Dde) y_a1Ddf)) (Apply (Apply ModSym0 x_a1Dde) y_a1Ddf)
infixl 7 `Rem`
infixl 7 `Quot`


sDivMod :: Sing x -> Sing y -> Sing (DivMod x y)
sDivMod sx sy =
    let x     = fromSing sx
        y     = fromSing sy
        (q,r) = x `divMod` y
    in TN.withSomeSNat q $ \sq ->
       TN.withSomeSNat r $ \sr ->
       unsafeCoerce (STuple2 sq sr)

sQuotRem :: Sing x -> Sing y -> Sing (QuotRem x y)
sQuotRem = sDivMod

sQuot :: Sing x -> Sing y -> Sing (Quot x y)
sQuot = sDiv
infixl 7 `sQuot`

sRem :: Sing x -> Sing y -> Sing (Rem x y)
sRem = sMod
infixl 7 `sRem`

consSymbol :: Char -> String -> String
consSymbol = (:)

sConsSymbol :: Sing x -> Sing y -> Sing (ConsSymbol x y)
sConsSymbol sx sy =
    let x = fromSing sx
        y = T.unpack (fromSing sy)
    in withSomeSSymbol (consSymbol x y) unsafeCoerce

type ConsSymbolSym0 :: (~>) Char ((~>) Symbol Symbol)
data ConsSymbolSym0 :: (~>) Char ((~>) Symbol Symbol)
  where
    ConsSymbolSym0KindInference :: SameKind (Apply ConsSymbolSym0 arg_a1Dxx) (ConsSymbolSym1 arg_a1Dxx) =>
                                    ConsSymbolSym0 a6989586621679400116
type instance Apply @Char @((~>) Symbol Symbol) ConsSymbolSym0 a6989586621679400116 = ConsSymbolSym1 a6989586621679400116
instance SuppressUnusedWarnings ConsSymbolSym0 where
  suppressUnusedWarnings = snd ((,) ConsSymbolSym0KindInference ())
type ConsSymbolSym1 :: Char -> (~>) Symbol Symbol
data ConsSymbolSym1 (a6989586621679400116 :: Char) :: (~>) Symbol Symbol
  where
    ConsSymbolSym1KindInference :: SameKind (Apply (ConsSymbolSym1 a6989586621679400116) arg_a1Dxx) (ConsSymbolSym2 a6989586621679400116 arg_a1Dxx) =>
                                    ConsSymbolSym1 a6989586621679400116 a6989586621679400117
type instance Apply @Symbol @Symbol (ConsSymbolSym1 a6989586621679400116) a6989586621679400117 = ConsSymbol a6989586621679400116 a6989586621679400117
instance SuppressUnusedWarnings (ConsSymbolSym1 a6989586621679400116) where
  suppressUnusedWarnings = snd ((,) ConsSymbolSym1KindInference ())
type ConsSymbolSym2 :: Char -> Symbol -> Symbol
type family ConsSymbolSym2 (a6989586621679400116 :: Char) (a6989586621679400117 :: Symbol) :: Symbol where
  ConsSymbolSym2 a6989586621679400116 a6989586621679400117 = ConsSymbol a6989586621679400116 a6989586621679400117

instance SingI ConsSymbolSym0 where
  sing = singFun2 sConsSymbol
instance SingI x => SingI (ConsSymbolSym1 x) where
  sing = singFun1 $ sConsSymbol $ sing @x
instance SingI1 ConsSymbolSym1 where
  liftSing s = singFun1 $ sConsSymbol s

unconsSymbol :: String -> Maybe (Char, String)
unconsSymbol = L.uncons

sUnconsSymbol :: Sing x -> Sing (UnconsSymbol x)
sUnconsSymbol sx =
    let x   = T.unpack (fromSing sx)
        res = toSing (unconsSymbol x)
    in case res of
         SomeSing s -> unsafeCoerce s

type UnconsSymbolSym0 :: (~>) Symbol (Maybe (Char, Symbol))
data UnconsSymbolSym0 :: (~>) Symbol (Maybe (Char, Symbol))
  where
    UnconsSymbolSym0KindInference :: SameKind (Apply UnconsSymbolSym0 arg_a1DFQ) (UnconsSymbolSym1 arg_a1DFQ) =>
                                      UnconsSymbolSym0 a6989586621679400631
type instance Apply @Symbol @(Maybe (Char,
                                      Symbol)) UnconsSymbolSym0 a6989586621679400631 = UnconsSymbol a6989586621679400631
instance SuppressUnusedWarnings UnconsSymbolSym0 where
  suppressUnusedWarnings = snd ((,) UnconsSymbolSym0KindInference ())
type UnconsSymbolSym1 :: Symbol -> Maybe (Char, Symbol)
type family UnconsSymbolSym1 (a6989586621679400631 :: Symbol) :: Maybe (Char,
                                                                        Symbol) where
  UnconsSymbolSym1 a6989586621679400631 = UnconsSymbol a6989586621679400631

instance SingI UnconsSymbolSym0 where
  sing = singFun1 sUnconsSymbol

charToNat :: Char -> Natural
charToNat = fromIntegral . ord

sCharToNat :: Sing x -> Sing (CharToNat x)
sCharToNat sx =
    let x = fromSing sx
    in TN.withSomeSNat (charToNat x) unsafeCoerce

type CharToNatSym0 :: (~>) Char Natural
data CharToNatSym0 :: (~>) Char Natural
  where
    CharToNatSym0KindInference :: SameKind (Apply CharToNatSym0 arg_a1DJr) (CharToNatSym1 arg_a1DJr) =>
                                  CharToNatSym0 a6989586621679400854
type instance Apply @Char @Natural CharToNatSym0 a6989586621679400854 = CharToNat a6989586621679400854
instance SuppressUnusedWarnings CharToNatSym0 where
  suppressUnusedWarnings = snd ((,) CharToNatSym0KindInference ())
type CharToNatSym1 :: Char -> Natural
type family CharToNatSym1 (a6989586621679400854 :: Char) :: Natural where
  CharToNatSym1 a6989586621679400854 = CharToNat a6989586621679400854

instance SingI CharToNatSym0 where
  sing = singFun1 sCharToNat

natToChar :: Natural -> Char
natToChar = chr . fromIntegral

sNatToChar :: Sing x -> Sing (NatToChar x)
sNatToChar sx =
    let x = fromSing sx
    in withSomeSChar (natToChar x) unsafeCoerce

type NatToCharSym0 :: (~>) Natural Char
data NatToCharSym0 :: (~>) Natural Char
  where
    NatToCharSym0KindInference :: SameKind (Apply NatToCharSym0 arg_a1DN7) (NatToCharSym1 arg_a1DN7) =>
                                  NatToCharSym0 a6989586621679401082
type instance Apply @Natural @Char NatToCharSym0 a6989586621679401082 = NatToChar a6989586621679401082
instance SuppressUnusedWarnings NatToCharSym0 where
  suppressUnusedWarnings = snd ((,) NatToCharSym0KindInference ())
type NatToCharSym1 :: Natural -> Char
type family NatToCharSym1 (a6989586621679401082 :: Natural) :: Char where
  NatToCharSym1 a6989586621679401082 = NatToChar a6989586621679401082

instance SingI NatToCharSym0 where
  sing = singFun1 sNatToChar
