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
-- Module      :  Data.Singletons.Base.TypeError
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines a drop-in replacement for 'TL.TypeError' (from "GHC.TypeLits")
-- that can be used at the value level as well. Since this is a drop-in
-- replacement, it is not recommended to import all of "GHC.TypeLits"
-- and "Data.Singletons.Base.TypeError" at the same time, as many of the
-- definitions in the latter deliberately clash with the former.
--
----------------------------------------------------------------------------
module Data.Singletons.Base.TypeError (
  TypeError, sTypeError, typeError,
  ErrorMessage'(..), ErrorMessage, PErrorMessage,
  Sing, SErrorMessage(..),
  ConvertPErrorMessage, showErrorMessage,

  -- * Defunctionalization symbols
  TextSym0, TextSym1,
  ShowTypeSym0, ShowTypeSym1,
  type (:<>:@#@$), type (:<>:@#@$$), type (:<>:@#@$$$),
  type (:$$:@#@$), type (:$$:@#@$$), type (:$$:@#@$$$),
  TypeErrorSym0, TypeErrorSym1
  ) where

import Data.Kind
import Data.Singletons.TH
import qualified Data.Text as Text
import qualified GHC.TypeLits as TL (ErrorMessage(..), TypeError)
import GHC.Stack (HasCallStack)
import GHC.TypeLits.Singletons.Internal
import Prelude hiding ((<>))
import Text.PrettyPrint (Doc, text, (<>), ($$))

-- | A description of a custom type error.
--
-- This is a variation on 'TL.ErrorMessage' that is parameterized over what
-- text type is used in the 'Text' constructor. Instantiating it with
-- 'Text.Text' gives you 'ErrorMessage', and instantiating it with 'Symbol'
-- gives you 'PErrorMessage'.
type ErrorMessage' :: Type -> Type
data ErrorMessage' s
  = Text s
    -- ^ Show the text as is.
  | forall t. ShowType t
    -- ^ Pretty print the type.
    -- @ShowType :: k -> ErrorMessage@
  | ErrorMessage' s :<>: ErrorMessage' s
    -- ^ Put two pieces of error message next
    -- to each other.
  | ErrorMessage' s :$$: ErrorMessage' s
    -- ^ Stack two pieces of error message on top
    -- of each other.
infixl 6 :<>:
infixl 5 :$$:

-- | A value-level `ErrorMessage'` which uses 'Text.Text' as its text type.
type ErrorMessage :: Type
type ErrorMessage  = ErrorMessage' Text.Text

-- | A type-level `ErrorMessage'` which uses 'Symbol' as its text kind.
type PErrorMessage :: Type
type PErrorMessage = ErrorMessage' Symbol

type SErrorMessage :: PErrorMessage -> Type
data SErrorMessage :: PErrorMessage -> Type where
  SText     :: Sing t             -> SErrorMessage ('Text t)
  SShowType :: Sing ty            -> SErrorMessage ('ShowType ty)
  (:%<>:)   :: Sing e1 -> Sing e2 -> SErrorMessage (e1 ':<>: e2)
  (:%$$:)   :: Sing e1 -> Sing e2 -> SErrorMessage (e1 ':$$: e2)
infixl 6 :%<>:
infixl 5 :%$$:

type instance Sing @PErrorMessage = SErrorMessage

instance SingKind PErrorMessage where
  type Demote PErrorMessage = ErrorMessage
  fromSing (SText t)      = Text (fromSing t)
  fromSing (SShowType{})  = ShowType (error "Can't single ShowType")
  fromSing (e1 :%<>: e2)  = fromSing e1 :<>: fromSing e2
  fromSing (e1 :%$$: e2)  = fromSing e1 :$$: fromSing e2
  toSing (Text t)     = withSomeSing t  $ SomeSing . SText
  toSing (ShowType{}) = SomeSing $ SShowType (error "Can't single ShowType")
  toSing (e1 :<>: e2) = withSomeSing e1 $ \sE1 ->
                        withSomeSing e2 $ \sE2 ->
                        SomeSing (sE1 :%<>: sE2)
  toSing (e1 :$$: e2) = withSomeSing e1 $ \sE1 ->
                        withSomeSing e2 $ \sE2 ->
                        SomeSing (sE1 :%$$: sE2)

instance SingI t => SingI ('Text t :: PErrorMessage) where
  sing = SText sing
instance SingI1 ('Text :: Symbol -> PErrorMessage) where
  liftSing = SText

instance SingI ty => SingI ('ShowType ty :: PErrorMessage) where
  sing = SShowType sing
instance SingI1 ('ShowType :: t -> PErrorMessage) where
  liftSing = SShowType

instance (SingI e1, SingI e2) => SingI (e1 ':<>: e2 :: PErrorMessage) where
  sing = sing :%<>: sing
instance SingI e1 => SingI1 ('(:<>:) e1 :: PErrorMessage -> PErrorMessage) where
  liftSing s = sing :%<>: s
instance SingI2 ('(:<>:) :: PErrorMessage -> PErrorMessage -> PErrorMessage) where
  liftSing2 s1 s2 = s1 :%<>: s2

instance (SingI e1, SingI e2) => SingI (e1 ':$$: e2 :: PErrorMessage) where
  sing = sing :%$$: sing
instance SingI e1 => SingI1 ('(:$$:) e1 :: PErrorMessage -> PErrorMessage) where
  liftSing s = sing :%$$: s
instance SingI2 ('(:$$:) :: PErrorMessage -> PErrorMessage -> PErrorMessage) where
  liftSing2 s1 s2 = s1 :%$$: s2

-- | Convert an 'ErrorMessage' into a human-readable 'String'.
showErrorMessage :: ErrorMessage -> String
showErrorMessage = show . go
  where
  go :: ErrorMessage -> Doc
  go (Text t)     = text (Text.unpack t)
  go (ShowType _) = text "<type>" -- Not much we can do here
  go (e1 :<>: e2) = go e1 <> go e2
  go (e1 :$$: e2) = go e1 $$ go e2

-- | The value-level counterpart to 'TypeError'.
--
-- Note that this is not quite as expressive as 'TypeError', as it is unable
-- to print the contents of 'ShowType' constructors (it will simply print
-- @\"\<type\>\"@ in their place).
typeError :: HasCallStack => ErrorMessage -> a
typeError = error . showErrorMessage

-- | Convert a 'PErrorMessage' to a 'TL.ErrorMessage' from "GHC.TypeLits".
type ConvertPErrorMessage :: PErrorMessage -> TL.ErrorMessage
type family ConvertPErrorMessage (a :: PErrorMessage) :: TL.ErrorMessage where
  ConvertPErrorMessage ('Text t)      = 'TL.Text t
  ConvertPErrorMessage ('ShowType ty) = 'TL.ShowType ty
  ConvertPErrorMessage (e1 ':<>: e2)  = ConvertPErrorMessage e1 'TL.:<>: ConvertPErrorMessage e2
  ConvertPErrorMessage (e1 ':$$: e2)  = ConvertPErrorMessage e1 'TL.:$$: ConvertPErrorMessage e2

-- | A drop-in replacement for 'TL.TypeError'. This also exists at the
-- value-level as 'typeError'.
type TypeError :: PErrorMessage -> a
type family TypeError (x :: PErrorMessage) :: a where
  -- We cannot define this as a type synonym due to Trac #12048.
  TypeError x = TL.TypeError (ConvertPErrorMessage x)

-- | The singleton for 'typeError'.
--
-- Note that this is not quite as expressive as 'TypeError', as it is unable
-- to handle 'ShowType' constructors at all.
sTypeError :: HasCallStack => Sing err -> Sing (TypeError err)
sTypeError = typeError . fromSing

type TextSym0 :: forall (s_a3g2u :: Type). (~>) s_a3g2u (ErrorMessage' s_a3g2u)
data TextSym0 :: (~>) s_a3g2u (ErrorMessage' s_a3g2u)
  where
    TextSym0KindInference :: SameKind (Apply TextSym0 arg_a3gnj) (TextSym1 arg_a3gnj) =>
                              TextSym0 a6989586621679787726
type instance Apply @s_a3g2u @(ErrorMessage' s_a3g2u) TextSym0 a6989586621679787726 = 'Text a6989586621679787726
instance SuppressUnusedWarnings TextSym0 where
  suppressUnusedWarnings = snd ((,) TextSym0KindInference ())
type TextSym1 :: forall (s_a3g2u :: Type). s_a3g2u
                                            -> ErrorMessage' s_a3g2u
type family TextSym1 @(s_a3g2u :: Type) (a6989586621679787726 :: s_a3g2u) :: ErrorMessage' s_a3g2u where
  TextSym1 a6989586621679787726 = 'Text a6989586621679787726
type ShowTypeSym0 :: forall (s_a3g2u :: Type)
                            (t_a3g3s :: Type). (~>) t_a3g3s (ErrorMessage' s_a3g2u)
data ShowTypeSym0 :: (~>) t_a3g3s (ErrorMessage' s_a3g2u)
  where
    ShowTypeSym0KindInference :: SameKind (Apply ShowTypeSym0 arg_a3gnl) (ShowTypeSym1 arg_a3gnl) =>
                                  ShowTypeSym0 a6989586621679787728
type instance Apply @t_a3g3s @(ErrorMessage' s_a3g2u) ShowTypeSym0 a6989586621679787728 = 'ShowType a6989586621679787728
instance SuppressUnusedWarnings ShowTypeSym0 where
  suppressUnusedWarnings = snd ((,) ShowTypeSym0KindInference ())
type ShowTypeSym1 :: forall (s_a3g2u :: Type)
                            (t_a3g3s :: Type). t_a3g3s -> ErrorMessage' s_a3g2u
type family ShowTypeSym1 @(s_a3g2u :: Type) @(t_a3g3s :: Type) (a6989586621679787728 :: t_a3g3s) :: ErrorMessage' s_a3g2u where
  ShowTypeSym1 a6989586621679787728 = 'ShowType a6989586621679787728
type (:<>:@#@$) :: forall (s_a3g2u :: Type). (~>) (ErrorMessage' s_a3g2u) ((~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u))
data (:<>:@#@$) :: (~>) (ErrorMessage' s_a3g2u) ((~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u))
  where
    (::<>:@#@$###) :: SameKind (Apply (:<>:@#@$) arg_a3gnn) ((:<>:@#@$$) arg_a3gnn) =>
                      (:<>:@#@$) a6989586621679787730
type instance Apply @(ErrorMessage' s_a3g2u) @((~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u)) (:<>:@#@$) a6989586621679787730 = (:<>:@#@$$) a6989586621679787730
instance SuppressUnusedWarnings (:<>:@#@$) where
  suppressUnusedWarnings = snd ((,) (::<>:@#@$###) ())
infixl 6 :<>:@#@$
type (:<>:@#@$$) :: forall (s_a3g2u :: Type). ErrorMessage' s_a3g2u
                                              -> (~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u)
data (:<>:@#@$$) (a6989586621679787730 :: ErrorMessage' s_a3g2u) :: (~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u)
  where
    (::<>:@#@$$###) :: SameKind (Apply ((:<>:@#@$$) a6989586621679787730) arg_a3gnn) ((:<>:@#@$$$) a6989586621679787730 arg_a3gnn) =>
                        (:<>:@#@$$) a6989586621679787730 a6989586621679787731
type instance Apply @(ErrorMessage' s_a3g2u) @(ErrorMessage' s_a3g2u) ((:<>:@#@$$) a6989586621679787730) a6989586621679787731 = '(:<>:) a6989586621679787730 a6989586621679787731
instance SuppressUnusedWarnings ((:<>:@#@$$) a6989586621679787730) where
  suppressUnusedWarnings = snd ((,) (::<>:@#@$$###) ())
infixl 6 :<>:@#@$$
type (:<>:@#@$$$) :: forall (s_a3g2u :: Type). ErrorMessage' s_a3g2u
                                                -> ErrorMessage' s_a3g2u -> ErrorMessage' s_a3g2u
type family (:<>:@#@$$$) @(s_a3g2u :: Type) (a6989586621679787730 :: ErrorMessage' s_a3g2u) (a6989586621679787731 :: ErrorMessage' s_a3g2u) :: ErrorMessage' s_a3g2u where
  (:<>:@#@$$$) a6989586621679787730 a6989586621679787731 = '(:<>:) a6989586621679787730 a6989586621679787731
infixl 6 :<>:@#@$$$
type (:$$:@#@$) :: forall (s_a3g2u :: Type). (~>) (ErrorMessage' s_a3g2u) ((~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u))
data (:$$:@#@$) :: (~>) (ErrorMessage' s_a3g2u) ((~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u))
  where
    (::$$:@#@$###) :: SameKind (Apply (:$$:@#@$) arg_a3gnq) ((:$$:@#@$$) arg_a3gnq) =>
                      (:$$:@#@$) a6989586621679787733
type instance Apply @(ErrorMessage' s_a3g2u) @((~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u)) (:$$:@#@$) a6989586621679787733 = (:$$:@#@$$) a6989586621679787733
instance SuppressUnusedWarnings (:$$:@#@$) where
  suppressUnusedWarnings = snd ((,) (::$$:@#@$###) ())
infixl 5 :$$:@#@$
type (:$$:@#@$$) :: forall (s_a3g2u :: Type). ErrorMessage' s_a3g2u
                                              -> (~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u)
data (:$$:@#@$$) (a6989586621679787733 :: ErrorMessage' s_a3g2u) :: (~>) (ErrorMessage' s_a3g2u) (ErrorMessage' s_a3g2u)
  where
    (::$$:@#@$$###) :: SameKind (Apply ((:$$:@#@$$) a6989586621679787733) arg_a3gnq) ((:$$:@#@$$$) a6989586621679787733 arg_a3gnq) =>
                        (:$$:@#@$$) a6989586621679787733 a6989586621679787734
type instance Apply @(ErrorMessage' s_a3g2u) @(ErrorMessage' s_a3g2u) ((:$$:@#@$$) a6989586621679787733) a6989586621679787734 = '(:$$:) a6989586621679787733 a6989586621679787734
instance SuppressUnusedWarnings ((:$$:@#@$$) a6989586621679787733) where
  suppressUnusedWarnings = snd ((,) (::$$:@#@$$###) ())
infixl 5 :$$:@#@$$
type (:$$:@#@$$$) :: forall (s_a3g2u :: Type). ErrorMessage' s_a3g2u
                                                -> ErrorMessage' s_a3g2u -> ErrorMessage' s_a3g2u
type family (:$$:@#@$$$) @(s_a3g2u :: Type) (a6989586621679787733 :: ErrorMessage' s_a3g2u) (a6989586621679787734 :: ErrorMessage' s_a3g2u) :: ErrorMessage' s_a3g2u where
  (:$$:@#@$$$) a6989586621679787733 a6989586621679787734 = '(:$$:) a6989586621679787733 a6989586621679787734
infixl 5 :$$:@#@$$$
type TypeErrorSym0 :: forall (a_a3g2e :: Type). (~>) PErrorMessage a_a3g2e
data TypeErrorSym0 :: (~>) PErrorMessage a_a3g2e
  where
    TypeErrorSym0KindInference :: SameKind (Apply TypeErrorSym0 arg_a3gnt) (TypeErrorSym1 arg_a3gnt) =>
                                  TypeErrorSym0 a6989586621679787736
type instance Apply @PErrorMessage @a_a3g2e TypeErrorSym0 a6989586621679787736 = TypeError a6989586621679787736
instance SuppressUnusedWarnings TypeErrorSym0 where
  suppressUnusedWarnings = snd ((,) TypeErrorSym0KindInference ())
type TypeErrorSym1 :: forall (a_a3g2e :: Type). PErrorMessage
                                                -> a_a3g2e
type family TypeErrorSym1 @(a_a3g2e :: Type) (a6989586621679787736 :: PErrorMessage) :: a_a3g2e where
  TypeErrorSym1 a6989586621679787736 = TypeError a6989586621679787736


instance SingI (TextSym0 :: Symbol ~> PErrorMessage) where
  sing = singFun1 SText

instance SingI (ShowTypeSym0 :: t ~> PErrorMessage) where
  sing = singFun1 SShowType

instance SingI ((:<>:@#@$) :: PErrorMessage ~> PErrorMessage ~> PErrorMessage) where
  sing = singFun2 (:%<>:)
instance SingI x => SingI ((:<>:@#@$$) x :: PErrorMessage ~> PErrorMessage) where
  sing = singFun1 (sing @x :%<>:)
instance SingI1 ((:<>:@#@$$) :: PErrorMessage -> PErrorMessage ~> PErrorMessage) where
  liftSing s = singFun1 (s :%<>:)

instance SingI ((:$$:@#@$) :: PErrorMessage ~> PErrorMessage ~> PErrorMessage) where
  sing = singFun2 (:%$$:)
instance SingI x => SingI ((:$$:@#@$$) x :: PErrorMessage ~> PErrorMessage) where
  sing = singFun1 (sing @x :%$$:)
instance SingI1 ((:$$:@#@$$) :: PErrorMessage -> PErrorMessage ~> PErrorMessage) where
  liftSing s = singFun1 (s :%$$:)

instance SingI TypeErrorSym0 where
  sing = singFun1 sTypeError
