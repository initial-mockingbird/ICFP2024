{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoNamedWildCards #-}

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
-- Module      :  Data.Bool.Singletons
-- Copyright   :  (C) 2013-2014 Richard Eisenberg, Jan Stolarek
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines functions and datatypes relating to the singleton for 'Bool',
-- including singled versions of all the definitions in @Data.Bool@.
--
-- Because many of these definitions are produced by Template Haskell,
-- it is not possible to create proper Haddock documentation. Please look
-- up the corresponding operation in @Data.Bool@. Also, please excuse
-- the apparent repeated variable names. This is due to an interaction
-- between Template Haskell and Haddock.
--
----------------------------------------------------------------------------

module Data.Bool.Singletons (
  -- * The 'Bool' singleton
  Sing, SBool(..),

  -- * Conditionals
  If, sIf,

  -- * Singletons from @Data.Bool@
  Not, sNot, type (&&), type (||), (%&&), (%||),

  -- | The following are derived from the function 'bool' in @Data.Bool@. The extra
  -- underscore is to avoid name clashes with the type 'Bool'.
  bool_, Bool_, sBool_, Otherwise, sOtherwise,

  -- * Defunctionalization symbols
  TrueSym0, FalseSym0,

  IfSym0, IfSym1, IfSym2, IfSym3,
  NotSym0, NotSym1,
  type (&&@#@$), type (&&@#@$$), type (&&@#@$$$),
  type (||@#@$), type (||@#@$$), type (||@#@$$$),
  Bool_Sym0, Bool_Sym1, Bool_Sym2, Bool_Sym3,
  OtherwiseSym0
  ) where

import Data.Singletons
import Data.Singletons.Base.Instances
import Data.Singletons.TH
import Data.Type.Bool ( If, type (&&), type (||), Not )
import Data.Kind (Type)


bool_ :: a_av5x -> a_av5x -> Bool -> a_av5x
bool_ fls_av5z _tru_av5A False = fls_av5z
bool_ _fls_av5B tru_av5C True = tru_av5C
type Bool_Sym0 :: (~>) a_av5x ((~>) a_av5x ((~>) Bool a_av5x))
data Bool_Sym0 :: (~>) a_av5x ((~>) a_av5x ((~>) Bool a_av5x))
  where
    Bool_Sym0KindInference :: SameKind (Apply Bool_Sym0 arg_av5G) (Bool_Sym1 arg_av5G) =>
                              Bool_Sym0 a6989586621679129309
type instance Apply @a_av5x @((~>) a_av5x ((~>) Bool a_av5x)) Bool_Sym0 a6989586621679129309 = Bool_Sym1 a6989586621679129309
instance SuppressUnusedWarnings Bool_Sym0 where
  suppressUnusedWarnings = snd ((,) Bool_Sym0KindInference ())
type Bool_Sym1 :: a_av5x -> (~>) a_av5x ((~>) Bool a_av5x)
data Bool_Sym1 (a6989586621679129309 :: a_av5x) :: (~>) a_av5x ((~>) Bool a_av5x)
  where
    Bool_Sym1KindInference :: SameKind (Apply (Bool_Sym1 a6989586621679129309) arg_av5G) (Bool_Sym2 a6989586621679129309 arg_av5G) =>
                              Bool_Sym1 a6989586621679129309 a6989586621679129310
type instance Apply @a_av5x @((~>) Bool a_av5x) (Bool_Sym1 a6989586621679129309) a6989586621679129310 = Bool_Sym2 a6989586621679129309 a6989586621679129310
instance SuppressUnusedWarnings (Bool_Sym1 a6989586621679129309) where
  suppressUnusedWarnings = snd ((,) Bool_Sym1KindInference ())
type Bool_Sym2 :: a_av5x -> a_av5x -> (~>) Bool a_av5x
data Bool_Sym2 (a6989586621679129309 :: a_av5x) (a6989586621679129310 :: a_av5x) :: (~>) Bool a_av5x
  where
    Bool_Sym2KindInference :: SameKind (Apply (Bool_Sym2 a6989586621679129309 a6989586621679129310) arg_av5G) (Bool_Sym3 a6989586621679129309 a6989586621679129310 arg_av5G) =>
                              Bool_Sym2 a6989586621679129309 a6989586621679129310 a6989586621679129311
type instance Apply @Bool @a_av5x (Bool_Sym2 a6989586621679129309 a6989586621679129310) a6989586621679129311 = Bool_ a6989586621679129309 a6989586621679129310 a6989586621679129311
instance SuppressUnusedWarnings (Bool_Sym2 a6989586621679129309 a6989586621679129310) where
  suppressUnusedWarnings = snd ((,) Bool_Sym2KindInference ())
type Bool_Sym3 :: a_av5x -> a_av5x -> Bool -> a_av5x
type family Bool_Sym3 @a_av5x (a6989586621679129309 :: a_av5x) (a6989586621679129310 :: a_av5x) (a6989586621679129311 :: Bool) :: a_av5x where
  Bool_Sym3 a6989586621679129309 a6989586621679129310 a6989586621679129311 = Bool_ a6989586621679129309 a6989586621679129310 a6989586621679129311
type Bool_ :: a_av5x -> a_av5x -> Bool -> a_av5x
type family Bool_ @a_av5x (a_av5D :: a_av5x) (a_av5E :: a_av5x) (a_av5F :: Bool) :: a_av5x where
  Bool_ fls_av5K _tru_av5L 'False = fls_av5K
  Bool_ _fls_av5M tru_av5N 'True = tru_av5N
sBool_ ::
  (forall (t_av5O :: a_av5x) (t_av5P :: a_av5x) (t_av5Q :: Bool).
    Sing t_av5O
    -> Sing t_av5P
      -> Sing t_av5Q
          -> Sing (Bool_ t_av5O t_av5P t_av5Q :: a_av5x) :: Type)
sBool_ (sFls :: Sing fls_av5K) (_stru :: Sing _tru_av5L) SFalse
  = sFls
sBool_ (_sfls :: Sing _fls_av5M) (sTru :: Sing tru_av5N) STrue
  = sTru
instance SingI (Bool_Sym0 :: (~>) a_av5x ((~>) a_av5x ((~>) Bool a_av5x))) where
  sing = singFun3 @Bool_Sym0 sBool_
instance SingI d_av5R =>
          SingI (Bool_Sym1 (d_av5R :: a_av5x) :: (~>) a_av5x ((~>) Bool a_av5x)) where
  sing
    = singFun2 @(Bool_Sym1 (d_av5R :: a_av5x)) (sBool_ (sing @d_av5R))
instance SingI1 (Bool_Sym1 :: a_av5x
                              -> (~>) a_av5x ((~>) Bool a_av5x)) where
  liftSing (s_av5X :: Sing (d_av5R :: a_av5x))
    = singFun2 @(Bool_Sym1 (d_av5R :: a_av5x)) (sBool_ s_av5X)
instance (SingI d_av5R, SingI d_av5S) =>
          SingI (Bool_Sym2 (d_av5R :: a_av5x) (d_av5S :: a_av5x) :: (~>) Bool a_av5x) where
  sing
    = singFun1
        @(Bool_Sym2 (d_av5R :: a_av5x) (d_av5S :: a_av5x))
        (sBool_ (sing @d_av5R) (sing @d_av5S))
instance SingI d_av5R =>
          SingI1 (Bool_Sym2 (d_av5R :: a_av5x) :: a_av5x
                                                  -> (~>) Bool a_av5x) where
  liftSing (s_av5U :: Sing (d_av5S :: a_av5x))
    = singFun1
        @(Bool_Sym2 (d_av5R :: a_av5x) (d_av5S :: a_av5x))
        (sBool_ (sing @d_av5R) s_av5U)
instance SingI2 (Bool_Sym2 :: a_av5x
                              -> a_av5x -> (~>) Bool a_av5x) where
  liftSing2
    (s_av5V :: Sing (d_av5R :: a_av5x))
    (s_av5W :: Sing (d_av5S :: a_av5x))
    = singFun1
        @(Bool_Sym2 (d_av5R :: a_av5x) (d_av5S :: a_av5x))
        (sBool_ s_av5V s_av5W)

type OtherwiseSym0 :: Bool
type family OtherwiseSym0 :: Bool where
  OtherwiseSym0 = Otherwise
type Otherwise :: Bool
type family Otherwise :: Bool where
  Otherwise = TrueSym0
sOtherwise :: (Sing (Otherwise :: Bool) :: Type)
sOtherwise = STrue

-- | Conjunction of singletons
(%&&) :: Sing a -> Sing b -> Sing (a && b)
SFalse %&& _ = SFalse
STrue  %&& a = a
infixr 3 %&&
type (&&@#@$) :: (~>) Bool ((~>) Bool Bool)
data (&&@#@$) :: (~>) Bool ((~>) Bool Bool)
  where
    (:&&@#@$###) :: SameKind (Apply (&&@#@$) arg_avAv) ((&&@#@$$) arg_avAv) =>
                    (&&@#@$) a6989586621679131220
type instance Apply @Bool @((~>) Bool Bool) (&&@#@$) a6989586621679131220 = (&&@#@$$) a6989586621679131220
instance SuppressUnusedWarnings (&&@#@$) where
  suppressUnusedWarnings = snd ((,) (:&&@#@$###) ())
infixr 3 &&@#@$
type (&&@#@$$) :: Bool -> (~>) Bool Bool
data (&&@#@$$) (a6989586621679131220 :: Bool) :: (~>) Bool Bool
  where
    (:&&@#@$$###) :: SameKind (Apply ((&&@#@$$) a6989586621679131220) arg_avAv) ((&&@#@$$$) a6989586621679131220 arg_avAv) =>
                      (&&@#@$$) a6989586621679131220 a6989586621679131221
type instance Apply @Bool @Bool ((&&@#@$$) a6989586621679131220) a6989586621679131221 = (&&) a6989586621679131220 a6989586621679131221
instance SuppressUnusedWarnings ((&&@#@$$) a6989586621679131220) where
  suppressUnusedWarnings = snd ((,) (:&&@#@$$###) ())
infixr 3 &&@#@$$
type (&&@#@$$$) :: Bool -> Bool -> Bool
type family (&&@#@$$$) (a6989586621679131220 :: Bool) (a6989586621679131221 :: Bool) :: Bool where
  (&&@#@$$$) a6989586621679131220 a6989586621679131221 = (&&) a6989586621679131220 a6989586621679131221
infixr 3 &&@#@$$$
instance SingI (&&@#@$) where
  sing = singFun2 (%&&)
instance SingI x => SingI ((&&@#@$$) x) where
  sing = singFun1 (sing @x %&&)

-- | Disjunction of singletons
(%||) :: Sing a -> Sing b -> Sing (a || b)
SFalse %|| a = a
STrue  %|| _ = STrue
infixr 2 %||
type (||@#@$) :: (~>) Bool ((~>) Bool Bool)
data (||@#@$) :: (~>) Bool ((~>) Bool Bool)
  where
    (:||@#@$###) :: SameKind (Apply (||@#@$) arg_avGi) ((||@#@$$) arg_avGi) =>
                    (||@#@$) a6989586621679131579
type instance Apply @Bool @((~>) Bool Bool) (||@#@$) a6989586621679131579 = (||@#@$$) a6989586621679131579
instance SuppressUnusedWarnings (||@#@$) where
  suppressUnusedWarnings = snd ((,) (:||@#@$###) ())
infixr 2 ||@#@$
type (||@#@$$) :: Bool -> (~>) Bool Bool
data (||@#@$$) (a6989586621679131579 :: Bool) :: (~>) Bool Bool
  where
    (:||@#@$$###) :: SameKind (Apply ((||@#@$$) a6989586621679131579) arg_avGi) ((||@#@$$$) a6989586621679131579 arg_avGi) =>
                      (||@#@$$) a6989586621679131579 a6989586621679131580
type instance Apply @Bool @Bool ((||@#@$$) a6989586621679131579) a6989586621679131580 = (||) a6989586621679131579 a6989586621679131580
instance SuppressUnusedWarnings ((||@#@$$) a6989586621679131579) where
  suppressUnusedWarnings = snd ((,) (:||@#@$$###) ())
infixr 2 ||@#@$$
type (||@#@$$$) :: Bool -> Bool -> Bool
type family (||@#@$$$) (a6989586621679131579 :: Bool) (a6989586621679131580 :: Bool) :: Bool where
  (||@#@$$$) a6989586621679131579 a6989586621679131580 = (||) a6989586621679131579 a6989586621679131580
infixr 2 ||@#@$$$
instance SingI (||@#@$) where
  sing = singFun2 (%||)
instance SingI x => SingI ((||@#@$$) x) where
  sing = singFun1 (sing @x %||)

-- | Negation of a singleton
sNot :: Sing a -> Sing (Not a)
sNot SFalse = STrue
sNot STrue  = SFalse

type NotSym0 :: (~>) Bool Bool
data NotSym0 :: (~>) Bool Bool
  where
    NotSym0KindInference :: SameKind (Apply NotSym0 arg_avLP) (NotSym1 arg_avLP) =>
                            NotSym0 a6989586621679131922
type instance Apply @Bool @Bool NotSym0 a6989586621679131922 = Not a6989586621679131922
instance SuppressUnusedWarnings NotSym0 where
  suppressUnusedWarnings = snd ((,) NotSym0KindInference ())
type NotSym1 :: Bool -> Bool
type family NotSym1 (a6989586621679131922 :: Bool) :: Bool where
  NotSym1 a6989586621679131922 = Not a6989586621679131922
instance SingI NotSym0 where
  sing = singFun1 sNot

-- | Conditional over singletons
sIf :: Sing a -> Sing b -> Sing c -> Sing (If a b c)
sIf STrue b _ = b
sIf SFalse _ c = c
type IfSym0 :: forall {k_avNq :: Type}. (~>) Bool ((~>) k_avNq ((~>) k_avNq k_avNq))
data IfSym0 :: (~>) Bool ((~>) k_avNq ((~>) k_avNq k_avNq))
  where
    IfSym0KindInference :: SameKind (Apply IfSym0 arg_avPp) (IfSym1 arg_avPp) =>
                            IfSym0 a6989586621679132144
type instance Apply @Bool @((~>) k_avNq ((~>) k_avNq k_avNq)) IfSym0 a6989586621679132144 = IfSym1 a6989586621679132144
instance SuppressUnusedWarnings IfSym0 where
  suppressUnusedWarnings = snd ((,) IfSym0KindInference ())
type IfSym1 :: forall {k_avNq :: Type}. Bool
                                        -> (~>) k_avNq ((~>) k_avNq k_avNq)
data IfSym1 (a6989586621679132144 :: Bool) :: (~>) k_avNq ((~>) k_avNq k_avNq)
  where
    IfSym1KindInference :: SameKind (Apply (IfSym1 a6989586621679132144) arg_avPp) (IfSym2 a6989586621679132144 arg_avPp) =>
                            IfSym1 a6989586621679132144 a6989586621679132145
type instance Apply @k_avNq @((~>) k_avNq k_avNq) (IfSym1 a6989586621679132144) a6989586621679132145 = IfSym2 a6989586621679132144 a6989586621679132145
instance SuppressUnusedWarnings (IfSym1 a6989586621679132144) where
  suppressUnusedWarnings = snd ((,) IfSym1KindInference ())
type IfSym2 :: forall {k_avNq :: Type}. Bool
                                        -> k_avNq -> (~>) k_avNq k_avNq
data IfSym2 (a6989586621679132144 :: Bool) (a6989586621679132145 :: k_avNq) :: (~>) k_avNq k_avNq
  where
    IfSym2KindInference :: SameKind (Apply (IfSym2 a6989586621679132144 a6989586621679132145) arg_avPp) (IfSym3 a6989586621679132144 a6989586621679132145 arg_avPp) =>
                            IfSym2 a6989586621679132144 a6989586621679132145 a6989586621679132146
type instance Apply @k_avNq @k_avNq (IfSym2 a6989586621679132144 a6989586621679132145) a6989586621679132146 = If a6989586621679132144 a6989586621679132145 a6989586621679132146
instance SuppressUnusedWarnings (IfSym2 a6989586621679132144 a6989586621679132145) where
  suppressUnusedWarnings = snd ((,) IfSym2KindInference ())
type IfSym3 :: forall {k_avNq :: Type}. Bool
                                        -> k_avNq -> k_avNq -> k_avNq
type family IfSym3 (a6989586621679132144 :: Bool) (a6989586621679132145 :: k_avNq) (a6989586621679132146 :: k_avNq) :: k_avNq where
  IfSym3 a6989586621679132144 a6989586621679132145 a6989586621679132146 = If a6989586621679132144 a6989586621679132145 a6989586621679132146

instance SingI IfSym0 where
  sing = singFun3 sIf
instance SingI c => SingI (IfSym1 c) where
  sing = singFun2 $ sIf (sing @c)
instance (SingI c, SingI t) => SingI (IfSym2 c t) where
  sing = singFun1 $ sIf (sing @c) (sing @t)
instance SingI1 IfSym1 where
  liftSing s = singFun2 $ sIf s
instance SingI c => SingI1 (IfSym2 c) where
  liftSing s = singFun1 $ sIf (sing @c) s
instance SingI2 IfSym2 where
  liftSing2 s1 s2 = singFun1 $ sIf s1 s2
