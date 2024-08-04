{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}

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
-- Module      :  Text.Show.Singletons
-- Copyright   :  (C) 2017 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the SShow singleton version of the Show type class.
--
-----------------------------------------------------------------------------

module Text.Show.Singletons (
  PShow(..), SShow(..), SymbolS, show_,
  Shows, sShows,
  ShowListWith, sShowListWith,
  ShowChar, sShowChar,
  ShowString, sShowString,
  ShowParen, sShowParen,
  ShowSpace, sShowSpace,
  ShowCommaSpace, sShowCommaSpace,
  AppPrec, sAppPrec,
  AppPrec1, sAppPrec1,

  -- * Defunctionalization symbols
  ShowsPrecSym0, ShowsPrecSym1, ShowsPrecSym2, ShowsPrecSym3,
  Show_Sym0, Show_Sym1,
  ShowListSym0, ShowListSym1, ShowListSym2,
  ShowsSym0, ShowsSym1, ShowsSym2,
  ShowListWithSym0, ShowListWithSym1, ShowListWithSym2, ShowListWithSym3,
  ShowCharSym0, ShowCharSym1, ShowCharSym2,
  ShowStringSym0, ShowStringSym1, ShowStringSym2,
  ShowParenSym0, ShowParenSym1, ShowParenSym2,
  ShowSpaceSym0, ShowSpaceSym1,
  ShowCommaSpaceSym0, ShowCommaSpaceSym1,
  AppPrecSym0, AppPrec1Sym0
  ) where

import           Data.Bool.Singletons
import           Data.Eq.Singletons
import           Data.Kind
import           Data.List.NonEmpty (NonEmpty)
import           Data.List.Singletons.Internal
import           Data.Ord (Down)
import           Data.Ord.Singletons
import           Data.Semigroup.Singletons.Internal.Classes
import           Data.Singletons
import           Data.Singletons.Base.Instances
import           Data.Singletons.TH
import qualified Data.Text as T
import           GHC.Base.Singletons
import           GHC.Num.Singletons
import           GHC.TypeLits
import           GHC.TypeLits.Singletons
import qualified Prelude as P
import           Prelude hiding (Show(..))
import           Unsafe.Coerce (unsafeCoerce)
import qualified GHC.Base

-- | The @shows@ functions return a function that prepends the
-- output 'Symbol' to an existing 'Symbol'.  This allows constant-time
-- concatenation of results using function composition.
type SymbolS :: Type
type SymbolS = Symbol -> Symbol


type family LamCases_6989586621679795858_a3iuv (ss6989586621679795856 :: [(~>) Symbol Symbol]) (a_69895866216797958496989586621679795857 :: Symbol) a_6989586621679795862_a3iuz a_6989586621679795864_a3iuB where
      LamCases_6989586621679795858_a3iuv ss_a3ius a_6989586621679795849_a3iut s_a3iuw r_a3iux = Apply (Apply (.@#@$) s_a3iuw) (Apply (Apply (.@#@$) (Apply ShowCharSym0 ',')) r_a3iux)
data LamCases_6989586621679795858Sym0 (ss6989586621679795856 :: [(~>) Symbol Symbol]) (a_69895866216797958496989586621679795857 :: Symbol) a_69895866216797958626989586621679795863
  where
    LamCases_6989586621679795858Sym0KindInference :: SameKind (Apply (LamCases_6989586621679795858Sym0 ss6989586621679795856 a_69895866216797958496989586621679795857) arg_a3iuC) (LamCases_6989586621679795858Sym1 ss6989586621679795856 a_69895866216797958496989586621679795857 arg_a3iuC) =>
                                                      LamCases_6989586621679795858Sym0 ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863
type instance Apply @_ @_ (LamCases_6989586621679795858Sym0 ss6989586621679795856 a_69895866216797958496989586621679795857) a_69895866216797958626989586621679795863 = LamCases_6989586621679795858Sym1 ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863
instance SuppressUnusedWarnings (LamCases_6989586621679795858Sym0 ss6989586621679795856 a_69895866216797958496989586621679795857) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679795858Sym0KindInference ())
data LamCases_6989586621679795858Sym1 (ss6989586621679795856 :: [(~>) Symbol Symbol]) (a_69895866216797958496989586621679795857 :: Symbol) a_69895866216797958626989586621679795863 a_69895866216797958646989586621679795865
  where
    LamCases_6989586621679795858Sym1KindInference :: SameKind (Apply (LamCases_6989586621679795858Sym1 ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863) arg_a3iuC) (LamCases_6989586621679795858Sym2 ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863 arg_a3iuC) =>
                                                      LamCases_6989586621679795858Sym1 ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863 a_69895866216797958646989586621679795865
type instance Apply @_ @_ (LamCases_6989586621679795858Sym1 ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863) a_69895866216797958646989586621679795865 = LamCases_6989586621679795858_a3iuv ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863 a_69895866216797958646989586621679795865
instance SuppressUnusedWarnings (LamCases_6989586621679795858Sym1 ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679795858Sym1KindInference ())
type family LamCases_6989586621679795858Sym2 (ss6989586621679795856 :: [(~>) Symbol Symbol]) (a_69895866216797958496989586621679795857 :: Symbol) a_69895866216797958626989586621679795863 a_69895866216797958646989586621679795865 where
  LamCases_6989586621679795858Sym2 ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863 a_69895866216797958646989586621679795865 = LamCases_6989586621679795858_a3iuv ss6989586621679795856 a_69895866216797958496989586621679795857 a_69895866216797958626989586621679795863 a_69895866216797958646989586621679795865
type family LamCases_6989586621679795881_a3iuS (a_69895866216797958756989586621679795880 :: Symbol) a_6989586621679795884_a3iuV where
  LamCases_6989586621679795881_a3iuS a_6989586621679795875_a3iuQ xs_a3iuT = Apply (Apply (<>@#@$) " ") xs_a3iuT
data LamCases_6989586621679795881Sym0 (a_69895866216797958756989586621679795880 :: Symbol) a_69895866216797958846989586621679795885
  where
    LamCases_6989586621679795881Sym0KindInference :: SameKind (Apply (LamCases_6989586621679795881Sym0 a_69895866216797958756989586621679795880) arg_a3iuW) (LamCases_6989586621679795881Sym1 a_69895866216797958756989586621679795880 arg_a3iuW) =>
                                                      LamCases_6989586621679795881Sym0 a_69895866216797958756989586621679795880 a_69895866216797958846989586621679795885
type instance Apply @_ @_ (LamCases_6989586621679795881Sym0 a_69895866216797958756989586621679795880) a_69895866216797958846989586621679795885 = LamCases_6989586621679795881_a3iuS a_69895866216797958756989586621679795880 a_69895866216797958846989586621679795885
instance SuppressUnusedWarnings (LamCases_6989586621679795881Sym0 a_69895866216797958756989586621679795880) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679795881Sym0KindInference ())
type family LamCases_6989586621679795881Sym1 (a_69895866216797958756989586621679795880 :: Symbol) a_69895866216797958846989586621679795885 where
  LamCases_6989586621679795881Sym1 a_69895866216797958756989586621679795880 a_69895866216797958846989586621679795885 = LamCases_6989586621679795881_a3iuS a_69895866216797958756989586621679795880 a_69895866216797958846989586621679795885
type family LamCases_6989586621679795899_a3iva (b6989586621679795896 :: Bool) (p6989586621679795897 :: (~>) Symbol Symbol) (a_69895866216797958876989586621679795898 :: Symbol) a_6989586621679795901_a3ivc where
  LamCases_6989586621679795899_a3iva b_a3iv6 p_a3iv7 a_6989586621679795887_a3iv8 'True = Apply (Apply (.@#@$) (Apply ShowCharSym0 '(')) (Apply (Apply (.@#@$) p_a3iv7) (Apply ShowCharSym0 ')'))
  LamCases_6989586621679795899_a3iva b_a3iv6 p_a3iv7 a_6989586621679795887_a3iv8 'False = p_a3iv7
data LamCases_6989586621679795899Sym0 (b6989586621679795896 :: Bool) (p6989586621679795897 :: (~>) Symbol Symbol) (a_69895866216797958876989586621679795898 :: Symbol) a_69895866216797959016989586621679795902
  where
    LamCases_6989586621679795899Sym0KindInference :: SameKind (Apply (LamCases_6989586621679795899Sym0 b6989586621679795896 p6989586621679795897 a_69895866216797958876989586621679795898) arg_a3ivd) (LamCases_6989586621679795899Sym1 b6989586621679795896 p6989586621679795897 a_69895866216797958876989586621679795898 arg_a3ivd) =>
                                                      LamCases_6989586621679795899Sym0 b6989586621679795896 p6989586621679795897 a_69895866216797958876989586621679795898 a_69895866216797959016989586621679795902
type instance Apply @_ @_ (LamCases_6989586621679795899Sym0 b6989586621679795896 p6989586621679795897 a_69895866216797958876989586621679795898) a_69895866216797959016989586621679795902 = LamCases_6989586621679795899_a3iva b6989586621679795896 p6989586621679795897 a_69895866216797958876989586621679795898 a_69895866216797959016989586621679795902
instance SuppressUnusedWarnings (LamCases_6989586621679795899Sym0 b6989586621679795896 p6989586621679795897 a_69895866216797958876989586621679795898) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679795899Sym0KindInference ())
type family LamCases_6989586621679795899Sym1 (b6989586621679795896 :: Bool) (p6989586621679795897 :: (~>) Symbol Symbol) (a_69895866216797958876989586621679795898 :: Symbol) a_69895866216797959016989586621679795902 where
  LamCases_6989586621679795899Sym1 b6989586621679795896 p6989586621679795897 a_69895866216797958876989586621679795898 a_69895866216797959016989586621679795902 = LamCases_6989586621679795899_a3iva b6989586621679795896 p6989586621679795897 a_69895866216797958876989586621679795898 a_69895866216797959016989586621679795902
data Let6989586621679795938ShowlSym0 (showx6989586621679795934 :: (~>) a6989586621679795521 ((~>) Symbol Symbol)) x6989586621679795935 xs6989586621679795936 (s6989586621679795937 :: Symbol) a6989586621679795939
  where
    Let6989586621679795938ShowlSym0KindInference :: SameKind (Apply (Let6989586621679795938ShowlSym0 showx6989586621679795934 x6989586621679795935 xs6989586621679795936 s6989586621679795937) arg_a3ivO) (Let6989586621679795938ShowlSym1 showx6989586621679795934 x6989586621679795935 xs6989586621679795936 s6989586621679795937 arg_a3ivO) =>
                                                    Let6989586621679795938ShowlSym0 showx6989586621679795934 x6989586621679795935 xs6989586621679795936 s6989586621679795937 a6989586621679795939
type instance Apply @_ @_ (Let6989586621679795938ShowlSym0 showx6989586621679795934 x6989586621679795935 xs6989586621679795936 s6989586621679795937) a6989586621679795939 = Let6989586621679795938Showl showx6989586621679795934 x6989586621679795935 xs6989586621679795936 s6989586621679795937 a6989586621679795939
instance SuppressUnusedWarnings (Let6989586621679795938ShowlSym0 showx6989586621679795934 x6989586621679795935 xs6989586621679795936 s6989586621679795937) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679795938ShowlSym0KindInference ())
type family Let6989586621679795938ShowlSym1 (showx6989586621679795934 :: (~>) a6989586621679795521 ((~>) Symbol Symbol)) x6989586621679795935 xs6989586621679795936 (s6989586621679795937 :: Symbol) a6989586621679795939 where
  Let6989586621679795938ShowlSym1 showx6989586621679795934 x6989586621679795935 xs6989586621679795936 s6989586621679795937 a6989586621679795939 = Let6989586621679795938Showl showx6989586621679795934 x6989586621679795935 xs6989586621679795936 s6989586621679795937 a6989586621679795939
type family Let6989586621679795938Showl (showx6989586621679795934 :: (~>) a6989586621679795521 ((~>) Symbol Symbol)) x6989586621679795935 xs6989586621679795936 (s6989586621679795937 :: Symbol) a_a3ivN where
  Let6989586621679795938Showl showx_a3ivI x_a3ivJ xs_a3ivK s_a3ivL '[] = Apply (Apply (<>@#@$) "]") s_a3ivL
  Let6989586621679795938Showl showx_a3ivI x_a3ivJ xs_a3ivK s_a3ivL ('(:) y_a3ivP ys_a3ivQ) = Apply (Apply (<>@#@$) ",") (Apply (Apply showx_a3ivI y_a3ivP) (Apply (Let6989586621679795938ShowlSym0 showx_a3ivI x_a3ivJ xs_a3ivK s_a3ivL) ys_a3ivQ))
type Show_tupleSym0 :: (~>) [(~>) Symbol Symbol] ((~>) Symbol Symbol)
data Show_tupleSym0 :: (~>) [(~>) Symbol Symbol] ((~>) Symbol Symbol)
  where
    Show_tupleSym0KindInference :: SameKind (Apply Show_tupleSym0 arg_a3iup) (Show_tupleSym1 arg_a3iup) =>
                                    Show_tupleSym0 a6989586621679795854
type instance Apply @[(~>) Symbol Symbol] @((~>) Symbol Symbol) Show_tupleSym0 a6989586621679795854 = Show_tupleSym1 a6989586621679795854
instance SuppressUnusedWarnings Show_tupleSym0 where
  suppressUnusedWarnings = snd ((,) Show_tupleSym0KindInference ())
type Show_tupleSym1 :: [(~>) Symbol Symbol] -> (~>) Symbol Symbol
data Show_tupleSym1 (a6989586621679795854 :: [(~>) Symbol Symbol]) :: (~>) Symbol Symbol
  where
    Show_tupleSym1KindInference :: SameKind (Apply (Show_tupleSym1 a6989586621679795854) arg_a3iup) (Show_tupleSym2 a6989586621679795854 arg_a3iup) =>
                                    Show_tupleSym1 a6989586621679795854 a6989586621679795855
type instance Apply @Symbol @Symbol (Show_tupleSym1 a6989586621679795854) a6989586621679795855 = Show_tuple a6989586621679795854 a6989586621679795855
instance SuppressUnusedWarnings (Show_tupleSym1 a6989586621679795854) where
  suppressUnusedWarnings = snd ((,) Show_tupleSym1KindInference ())
type Show_tupleSym2 :: [(~>) Symbol Symbol] -> Symbol -> Symbol
type family Show_tupleSym2 (a6989586621679795854 :: [(~>) Symbol Symbol]) (a6989586621679795855 :: Symbol) :: Symbol where
  Show_tupleSym2 a6989586621679795854 a6989586621679795855 = Show_tuple a6989586621679795854 a6989586621679795855
type AppPrec1Sym0 :: Natural
type family AppPrec1Sym0 :: Natural where
  AppPrec1Sym0 = AppPrec1
type AppPrecSym0 :: Natural
type family AppPrecSym0 :: Natural where
  AppPrecSym0 = AppPrec
type ShowCommaSpaceSym0 :: (~>) Symbol Symbol
data ShowCommaSpaceSym0 :: (~>) Symbol Symbol
  where
    ShowCommaSpaceSym0KindInference :: SameKind (Apply ShowCommaSpaceSym0 arg_a3iuI) (ShowCommaSpaceSym1 arg_a3iuI) =>
                                        ShowCommaSpaceSym0 a6989586621679795873
type instance Apply @Symbol @Symbol ShowCommaSpaceSym0 a6989586621679795873 = ShowCommaSpace a6989586621679795873
instance SuppressUnusedWarnings ShowCommaSpaceSym0 where
  suppressUnusedWarnings
    = snd ((,) ShowCommaSpaceSym0KindInference ())
type ShowCommaSpaceSym1 :: Symbol -> Symbol
type family ShowCommaSpaceSym1 (a6989586621679795873 :: Symbol) :: Symbol where
  ShowCommaSpaceSym1 a6989586621679795873 = ShowCommaSpace a6989586621679795873
type ShowSpaceSym0 :: (~>) Symbol Symbol
data ShowSpaceSym0 :: (~>) Symbol Symbol
  where
    ShowSpaceSym0KindInference :: SameKind (Apply ShowSpaceSym0 arg_a3iuO) (ShowSpaceSym1 arg_a3iuO) =>
                                  ShowSpaceSym0 a6989586621679795879
type instance Apply @Symbol @Symbol ShowSpaceSym0 a6989586621679795879 = ShowSpace a6989586621679795879
instance SuppressUnusedWarnings ShowSpaceSym0 where
  suppressUnusedWarnings = snd ((,) ShowSpaceSym0KindInference ())
type ShowSpaceSym1 :: Symbol -> Symbol
type family ShowSpaceSym1 (a6989586621679795879 :: Symbol) :: Symbol where
  ShowSpaceSym1 a6989586621679795879 = ShowSpace a6989586621679795879
type ShowParenSym0 :: (~>) Bool ((~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol))
data ShowParenSym0 :: (~>) Bool ((~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol))
  where
    ShowParenSym0KindInference :: SameKind (Apply ShowParenSym0 arg_a3iv2) (ShowParenSym1 arg_a3iv2) =>
                                  ShowParenSym0 a6989586621679795893
type instance Apply @Bool @((~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol)) ShowParenSym0 a6989586621679795893 = ShowParenSym1 a6989586621679795893
instance SuppressUnusedWarnings ShowParenSym0 where
  suppressUnusedWarnings = snd ((,) ShowParenSym0KindInference ())
type ShowParenSym1 :: Bool
                      -> (~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol)
data ShowParenSym1 (a6989586621679795893 :: Bool) :: (~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol)
  where
    ShowParenSym1KindInference :: SameKind (Apply (ShowParenSym1 a6989586621679795893) arg_a3iv2) (ShowParenSym2 a6989586621679795893 arg_a3iv2) =>
                                  ShowParenSym1 a6989586621679795893 a6989586621679795894
type instance Apply @((~>) Symbol Symbol) @((~>) Symbol Symbol) (ShowParenSym1 a6989586621679795893) a6989586621679795894 = ShowParenSym2 a6989586621679795893 a6989586621679795894
instance SuppressUnusedWarnings (ShowParenSym1 a6989586621679795893) where
  suppressUnusedWarnings = snd ((,) ShowParenSym1KindInference ())
type ShowParenSym2 :: Bool
                      -> (~>) Symbol Symbol -> (~>) Symbol Symbol
data ShowParenSym2 (a6989586621679795893 :: Bool) (a6989586621679795894 :: (~>) Symbol Symbol) :: (~>) Symbol Symbol
  where
    ShowParenSym2KindInference :: SameKind (Apply (ShowParenSym2 a6989586621679795893 a6989586621679795894) arg_a3iv2) (ShowParenSym3 a6989586621679795893 a6989586621679795894 arg_a3iv2) =>
                                  ShowParenSym2 a6989586621679795893 a6989586621679795894 a6989586621679795895
type instance Apply @Symbol @Symbol (ShowParenSym2 a6989586621679795893 a6989586621679795894) a6989586621679795895 = ShowParen a6989586621679795893 a6989586621679795894 a6989586621679795895
instance SuppressUnusedWarnings (ShowParenSym2 a6989586621679795893 a6989586621679795894) where
  suppressUnusedWarnings = snd ((,) ShowParenSym2KindInference ())
type ShowParenSym3 :: Bool
                      -> (~>) Symbol Symbol -> Symbol -> Symbol
type family ShowParenSym3 (a6989586621679795893 :: Bool) (a6989586621679795894 :: (~>) Symbol Symbol) (a6989586621679795895 :: Symbol) :: Symbol where
  ShowParenSym3 a6989586621679795893 a6989586621679795894 a6989586621679795895 = ShowParen a6989586621679795893 a6989586621679795894 a6989586621679795895
type ShowStringSym0 :: (~>) Symbol ((~>) Symbol Symbol)
data ShowStringSym0 :: (~>) Symbol ((~>) Symbol Symbol)
  where
    ShowStringSym0KindInference :: SameKind (Apply ShowStringSym0 arg_a3ivk) (ShowStringSym1 arg_a3ivk) =>
                                    ShowStringSym0 a6989586621679795911
type instance Apply @Symbol @((~>) Symbol Symbol) ShowStringSym0 a6989586621679795911 = ShowStringSym1 a6989586621679795911
instance SuppressUnusedWarnings ShowStringSym0 where
  suppressUnusedWarnings = snd ((,) ShowStringSym0KindInference ())
type ShowStringSym1 :: Symbol -> (~>) Symbol Symbol
data ShowStringSym1 (a6989586621679795911 :: Symbol) :: (~>) Symbol Symbol
  where
    ShowStringSym1KindInference :: SameKind (Apply (ShowStringSym1 a6989586621679795911) arg_a3ivk) (ShowStringSym2 a6989586621679795911 arg_a3ivk) =>
                                    ShowStringSym1 a6989586621679795911 a6989586621679795912
type instance Apply @Symbol @Symbol (ShowStringSym1 a6989586621679795911) a6989586621679795912 = ShowString a6989586621679795911 a6989586621679795912
instance SuppressUnusedWarnings (ShowStringSym1 a6989586621679795911) where
  suppressUnusedWarnings = snd ((,) ShowStringSym1KindInference ())
type ShowStringSym2 :: Symbol -> Symbol -> Symbol
type family ShowStringSym2 (a6989586621679795911 :: Symbol) (a6989586621679795912 :: Symbol) :: Symbol where
  ShowStringSym2 a6989586621679795911 a6989586621679795912 = ShowString a6989586621679795911 a6989586621679795912
type ShowCharSym0 :: (~>) Char ((~>) Symbol Symbol)
data ShowCharSym0 :: (~>) Char ((~>) Symbol Symbol)
  where
    ShowCharSym0KindInference :: SameKind (Apply ShowCharSym0 arg_a3ivv) (ShowCharSym1 arg_a3ivv) =>
                                  ShowCharSym0 a6989586621679795922
type instance Apply @Char @((~>) Symbol Symbol) ShowCharSym0 a6989586621679795922 = ShowCharSym1 a6989586621679795922
instance SuppressUnusedWarnings ShowCharSym0 where
  suppressUnusedWarnings = snd ((,) ShowCharSym0KindInference ())
type ShowCharSym1 :: Char -> (~>) Symbol Symbol
data ShowCharSym1 (a6989586621679795922 :: Char) :: (~>) Symbol Symbol
  where
    ShowCharSym1KindInference :: SameKind (Apply (ShowCharSym1 a6989586621679795922) arg_a3ivv) (ShowCharSym2 a6989586621679795922 arg_a3ivv) =>
                                  ShowCharSym1 a6989586621679795922 a6989586621679795923
type instance Apply @Symbol @Symbol (ShowCharSym1 a6989586621679795922) a6989586621679795923 = ShowChar a6989586621679795922 a6989586621679795923
instance SuppressUnusedWarnings (ShowCharSym1 a6989586621679795922) where
  suppressUnusedWarnings = snd ((,) ShowCharSym1KindInference ())
type ShowCharSym2 :: Char -> Symbol -> Symbol
type family ShowCharSym2 (a6989586621679795922 :: Char) (a6989586621679795923 :: Symbol) :: Symbol where
  ShowCharSym2 a6989586621679795922 a6989586621679795923 = ShowChar a6989586621679795922 a6989586621679795923
type ShowListWithSym0 :: (~>) ((~>) a_a3ip3 ((~>) Symbol Symbol)) ((~>) [a_a3ip3] ((~>) Symbol Symbol))
data ShowListWithSym0 :: (~>) ((~>) a_a3ip3 ((~>) Symbol Symbol)) ((~>) [a_a3ip3] ((~>) Symbol Symbol))
  where
    ShowListWithSym0KindInference :: SameKind (Apply ShowListWithSym0 arg_a3ivD) (ShowListWithSym1 arg_a3ivD) =>
                                      ShowListWithSym0 a6989586621679795930
type instance Apply @((~>) a_a3ip3 ((~>) Symbol Symbol)) @((~>) [a_a3ip3] ((~>) Symbol Symbol)) ShowListWithSym0 a6989586621679795930 = ShowListWithSym1 a6989586621679795930
instance SuppressUnusedWarnings ShowListWithSym0 where
  suppressUnusedWarnings = snd ((,) ShowListWithSym0KindInference ())
type ShowListWithSym1 :: (~>) a_a3ip3 ((~>) Symbol Symbol)
                          -> (~>) [a_a3ip3] ((~>) Symbol Symbol)
data ShowListWithSym1 (a6989586621679795930 :: (~>) a_a3ip3 ((~>) Symbol Symbol)) :: (~>) [a_a3ip3] ((~>) Symbol Symbol)
  where
    ShowListWithSym1KindInference :: SameKind (Apply (ShowListWithSym1 a6989586621679795930) arg_a3ivD) (ShowListWithSym2 a6989586621679795930 arg_a3ivD) =>
                                      ShowListWithSym1 a6989586621679795930 a6989586621679795931
type instance Apply @[a_a3ip3] @((~>) Symbol Symbol) (ShowListWithSym1 a6989586621679795930) a6989586621679795931 = ShowListWithSym2 a6989586621679795930 a6989586621679795931
instance SuppressUnusedWarnings (ShowListWithSym1 a6989586621679795930) where
  suppressUnusedWarnings = snd ((,) ShowListWithSym1KindInference ())
type ShowListWithSym2 :: (~>) a_a3ip3 ((~>) Symbol Symbol)
                          -> [a_a3ip3] -> (~>) Symbol Symbol
data ShowListWithSym2 (a6989586621679795930 :: (~>) a_a3ip3 ((~>) Symbol Symbol)) (a6989586621679795931 :: [a_a3ip3]) :: (~>) Symbol Symbol
  where
    ShowListWithSym2KindInference :: SameKind (Apply (ShowListWithSym2 a6989586621679795930 a6989586621679795931) arg_a3ivD) (ShowListWithSym3 a6989586621679795930 a6989586621679795931 arg_a3ivD) =>
                                      ShowListWithSym2 a6989586621679795930 a6989586621679795931 a6989586621679795932
type instance Apply @Symbol @Symbol (ShowListWithSym2 a6989586621679795930 a6989586621679795931) a6989586621679795932 = ShowListWith a6989586621679795930 a6989586621679795931 a6989586621679795932
instance SuppressUnusedWarnings (ShowListWithSym2 a6989586621679795930 a6989586621679795931) where
  suppressUnusedWarnings = snd ((,) ShowListWithSym2KindInference ())
type ShowListWithSym3 :: (~>) a_a3ip3 ((~>) Symbol Symbol)
                          -> [a_a3ip3] -> Symbol -> Symbol
type family ShowListWithSym3 @a_a3ip3 (a6989586621679795930 :: (~>) a_a3ip3 ((~>) Symbol Symbol)) (a6989586621679795931 :: [a_a3ip3]) (a6989586621679795932 :: Symbol) :: Symbol where
  ShowListWithSym3 a6989586621679795930 a6989586621679795931 a6989586621679795932 = ShowListWith a6989586621679795930 a6989586621679795931 a6989586621679795932
type ShowsSym0 :: (~>) a_a3ip4 ((~>) Symbol Symbol)
data ShowsSym0 :: (~>) a_a3ip4 ((~>) Symbol Symbol)
  where
    ShowsSym0KindInference :: SameKind (Apply ShowsSym0 arg_a3ivV) (ShowsSym1 arg_a3ivV) =>
                              ShowsSym0 a6989586621679795948
type instance Apply @a_a3ip4 @((~>) Symbol Symbol) ShowsSym0 a6989586621679795948 = ShowsSym1 a6989586621679795948
instance SuppressUnusedWarnings ShowsSym0 where
  suppressUnusedWarnings = snd ((,) ShowsSym0KindInference ())
type ShowsSym1 :: a_a3ip4 -> (~>) Symbol Symbol
data ShowsSym1 (a6989586621679795948 :: a_a3ip4) :: (~>) Symbol Symbol
  where
    ShowsSym1KindInference :: SameKind (Apply (ShowsSym1 a6989586621679795948) arg_a3ivV) (ShowsSym2 a6989586621679795948 arg_a3ivV) =>
                              ShowsSym1 a6989586621679795948 a6989586621679795949
type instance Apply @Symbol @Symbol (ShowsSym1 a6989586621679795948) a6989586621679795949 = Shows a6989586621679795948 a6989586621679795949
instance SuppressUnusedWarnings (ShowsSym1 a6989586621679795948) where
  suppressUnusedWarnings = snd ((,) ShowsSym1KindInference ())
type ShowsSym2 :: a_a3ip4 -> Symbol -> Symbol
type family ShowsSym2 @a_a3ip4 (a6989586621679795948 :: a_a3ip4) (a6989586621679795949 :: Symbol) :: Symbol where
  ShowsSym2 a6989586621679795948 a6989586621679795949 = Shows a6989586621679795948 a6989586621679795949
type Show_tuple :: [(~>) Symbol Symbol] -> Symbol -> Symbol
type family Show_tuple (a_a3iun :: [(~>) Symbol Symbol]) (a_a3iuo :: Symbol) :: Symbol where
  Show_tuple ss_a3ius a_6989586621679795849_a3iut = Apply (Apply (Apply (.@#@$) (Apply ShowCharSym0 '(')) (Apply (Apply (.@#@$) (Apply (Apply Foldr1Sym0 (LamCases_6989586621679795858Sym0 ss_a3ius a_6989586621679795849_a3iut)) ss_a3ius)) (Apply ShowCharSym0 ')'))) a_6989586621679795849_a3iut
type AppPrec1 :: Natural
type family AppPrec1 :: Natural where
  AppPrec1 = FromInteger 11
type AppPrec :: Natural
type family AppPrec :: Natural where
  AppPrec = FromInteger 10
type ShowCommaSpace :: Symbol -> Symbol
type family ShowCommaSpace (a_a3iuH :: Symbol) :: Symbol where
  ShowCommaSpace a_6989586621679795869_a3iuK = Apply (Apply ShowStringSym0 ", ") a_6989586621679795869_a3iuK
type ShowSpace :: Symbol -> Symbol
type family ShowSpace (a_a3iuN :: Symbol) :: Symbol where
  ShowSpace a_6989586621679795875_a3iuQ = Apply (LamCases_6989586621679795881Sym0 a_6989586621679795875_a3iuQ) a_6989586621679795875_a3iuQ
type ShowParen :: Bool -> (~>) Symbol Symbol -> Symbol -> Symbol
type family ShowParen (a_a3iuZ :: Bool) (a_a3iv0 :: (~>) Symbol Symbol) (a_a3iv1 :: Symbol) :: Symbol where
  ShowParen b_a3iv6 p_a3iv7 a_6989586621679795887_a3iv8 = Apply (Apply (LamCases_6989586621679795899Sym0 b_a3iv6 p_a3iv7 a_6989586621679795887_a3iv8) b_a3iv6) a_6989586621679795887_a3iv8
type ShowString :: Symbol -> Symbol -> Symbol
type family ShowString (a_a3ivi :: Symbol) (a_a3ivj :: Symbol) :: Symbol where
  ShowString a_6989586621679795904_a3ivn a_6989586621679795906_a3ivo = Apply (Apply (<>@#@$) a_6989586621679795904_a3ivn) a_6989586621679795906_a3ivo
type ShowChar :: Char -> Symbol -> Symbol
type family ShowChar (a_a3ivt :: Char) (a_a3ivu :: Symbol) :: Symbol where
  ShowChar a_6989586621679795915_a3ivy a_6989586621679795917_a3ivz = Apply (Apply ConsSymbolSym0 a_6989586621679795915_a3ivy) a_6989586621679795917_a3ivz
type ShowListWith :: (~>) a_a3ip3 ((~>) Symbol Symbol)
                      -> [a_a3ip3] -> Symbol -> Symbol
type family ShowListWith @a_a3ip3 (a_a3ivA :: (~>) a_a3ip3 ((~>) Symbol Symbol)) (a_a3ivB :: [a_a3ip3]) (a_a3ivC :: Symbol) :: Symbol where
  ShowListWith _ '[] s_a3ivH = Apply (Apply (<>@#@$) "[]") s_a3ivH
  ShowListWith showx_a3ivI ('(:) x_a3ivJ xs_a3ivK) s_a3ivL = Apply (Apply (<>@#@$) "[") (Apply (Apply showx_a3ivI x_a3ivJ) (Apply (Let6989586621679795938ShowlSym0 showx_a3ivI x_a3ivJ xs_a3ivK s_a3ivL) xs_a3ivK))
type Shows :: a_a3ip4 -> Symbol -> Symbol
type family Shows @a_a3ip4 (a_a3ivT :: a_a3ip4) (a_a3ivU :: Symbol) :: Symbol where
  Shows s_a3ivY a_6989586621679795943_a3ivZ = Apply (Apply (Apply ShowsPrecSym0 (FromInteger 0)) s_a3ivY) a_6989586621679795943_a3ivZ
type ShowsPrecSym0 :: forall a_a3ipj. (~>) Natural ((~>) a_a3ipj ((~>) Symbol Symbol))
data ShowsPrecSym0 :: (~>) Natural ((~>) a_a3ipj ((~>) Symbol Symbol))
  where
    ShowsPrecSym0KindInference :: SameKind (Apply ShowsPrecSym0 arg_a3iw3) (ShowsPrecSym1 arg_a3iw3) =>
                                  ShowsPrecSym0 a6989586621679795956
type instance Apply @Natural @((~>) a_a3ipj ((~>) Symbol Symbol)) ShowsPrecSym0 a6989586621679795956 = ShowsPrecSym1 a6989586621679795956
instance SuppressUnusedWarnings ShowsPrecSym0 where
  suppressUnusedWarnings = snd ((,) ShowsPrecSym0KindInference ())
type ShowsPrecSym1 :: forall a_a3ipj. Natural
                                      -> (~>) a_a3ipj ((~>) Symbol Symbol)
data ShowsPrecSym1 (a6989586621679795956 :: Natural) :: (~>) a_a3ipj ((~>) Symbol Symbol)
  where
    ShowsPrecSym1KindInference :: SameKind (Apply (ShowsPrecSym1 a6989586621679795956) arg_a3iw3) (ShowsPrecSym2 a6989586621679795956 arg_a3iw3) =>
                                  ShowsPrecSym1 a6989586621679795956 a6989586621679795957
type instance Apply @a_a3ipj @((~>) Symbol Symbol) (ShowsPrecSym1 a6989586621679795956) a6989586621679795957 = ShowsPrecSym2 a6989586621679795956 a6989586621679795957
instance SuppressUnusedWarnings (ShowsPrecSym1 a6989586621679795956) where
  suppressUnusedWarnings = snd ((,) ShowsPrecSym1KindInference ())
type ShowsPrecSym2 :: forall a_a3ipj. Natural
                                      -> a_a3ipj -> (~>) Symbol Symbol
data ShowsPrecSym2 (a6989586621679795956 :: Natural) (a6989586621679795957 :: a_a3ipj) :: (~>) Symbol Symbol
  where
    ShowsPrecSym2KindInference :: SameKind (Apply (ShowsPrecSym2 a6989586621679795956 a6989586621679795957) arg_a3iw3) (ShowsPrecSym3 a6989586621679795956 a6989586621679795957 arg_a3iw3) =>
                                  ShowsPrecSym2 a6989586621679795956 a6989586621679795957 a6989586621679795958
type instance Apply @Symbol @Symbol (ShowsPrecSym2 a6989586621679795956 a6989586621679795957) a6989586621679795958 = ShowsPrec a6989586621679795956 a6989586621679795957 a6989586621679795958
instance SuppressUnusedWarnings (ShowsPrecSym2 a6989586621679795956 a6989586621679795957) where
  suppressUnusedWarnings = snd ((,) ShowsPrecSym2KindInference ())
type ShowsPrecSym3 :: forall a_a3ipj. Natural
                                      -> a_a3ipj -> Symbol -> Symbol
type family ShowsPrecSym3 @a_a3ipj (a6989586621679795956 :: Natural) (a6989586621679795957 :: a_a3ipj) (a6989586621679795958 :: Symbol) :: Symbol where
  ShowsPrecSym3 a6989586621679795956 a6989586621679795957 a6989586621679795958 = ShowsPrec a6989586621679795956 a6989586621679795957 a6989586621679795958
type Show_Sym0 :: forall a_a3ipj. (~>) a_a3ipj Symbol
data Show_Sym0 :: (~>) a_a3ipj Symbol
  where
    Show_Sym0KindInference :: SameKind (Apply Show_Sym0 arg_a3iw8) (Show_Sym1 arg_a3iw8) =>
                              Show_Sym0 a6989586621679795961
type instance Apply @a_a3ipj @Symbol Show_Sym0 a6989586621679795961 = Show_ a6989586621679795961
instance SuppressUnusedWarnings Show_Sym0 where
  suppressUnusedWarnings = snd ((,) Show_Sym0KindInference ())
type Show_Sym1 :: forall a_a3ipj. a_a3ipj -> Symbol
type family Show_Sym1 @a_a3ipj (a6989586621679795961 :: a_a3ipj) :: Symbol where
  Show_Sym1 a6989586621679795961 = Show_ a6989586621679795961
type ShowListSym0 :: forall a_a3ipj. (~>) [a_a3ipj] ((~>) Symbol Symbol)
data ShowListSym0 :: (~>) [a_a3ipj] ((~>) Symbol Symbol)
  where
    ShowListSym0KindInference :: SameKind (Apply ShowListSym0 arg_a3iwc) (ShowListSym1 arg_a3iwc) =>
                                  ShowListSym0 a6989586621679795965
type instance Apply @[a_a3ipj] @((~>) Symbol Symbol) ShowListSym0 a6989586621679795965 = ShowListSym1 a6989586621679795965
instance SuppressUnusedWarnings ShowListSym0 where
  suppressUnusedWarnings = snd ((,) ShowListSym0KindInference ())
type ShowListSym1 :: forall a_a3ipj. [a_a3ipj]
                                      -> (~>) Symbol Symbol
data ShowListSym1 (a6989586621679795965 :: [a_a3ipj]) :: (~>) Symbol Symbol
  where
    ShowListSym1KindInference :: SameKind (Apply (ShowListSym1 a6989586621679795965) arg_a3iwc) (ShowListSym2 a6989586621679795965 arg_a3iwc) =>
                                  ShowListSym1 a6989586621679795965 a6989586621679795966
type instance Apply @Symbol @Symbol (ShowListSym1 a6989586621679795965) a6989586621679795966 = ShowList a6989586621679795965 a6989586621679795966
instance SuppressUnusedWarnings (ShowListSym1 a6989586621679795965) where
  suppressUnusedWarnings = snd ((,) ShowListSym1KindInference ())
type ShowListSym2 :: forall a_a3ipj. [a_a3ipj] -> Symbol -> Symbol
type family ShowListSym2 @a_a3ipj (a6989586621679795965 :: [a_a3ipj]) (a6989586621679795966 :: Symbol) :: Symbol where
  ShowListSym2 a6989586621679795965 a6989586621679795966 = ShowList a6989586621679795965 a6989586621679795966
type ShowsPrec_6989586621679795970 :: forall a_a3ipj. Natural
                                                      -> a_a3ipj -> Symbol -> Symbol
type family ShowsPrec_6989586621679795970 @a_a3ipj (a_a3iwk :: Natural) (a_a3iwl :: a_a3ipj) (a_a3iwm :: Symbol) :: Symbol where
  ShowsPrec_6989586621679795970 @a_a3ipj (_ :: Natural) (x_a3iwr :: a_a3ipj) (s_a3iws :: Symbol) = Apply (Apply (<>@#@$) (Apply Show_Sym0 x_a3iwr)) s_a3iws
type Show__6989586621679795982 :: forall a_a3ipj. a_a3ipj -> Symbol
type family Show__6989586621679795982 @a_a3ipj (a_a3iww :: a_a3ipj) :: Symbol where
  Show__6989586621679795982 @a_a3ipj (x_a3iwz :: a_a3ipj) = Apply (Apply ShowsSym0 x_a3iwz) ""
type ShowList_6989586621679795990 :: forall a_a3ipj. [a_a3ipj]
                                                      -> Symbol -> Symbol
type family ShowList_6989586621679795990 @a_a3ipj (a_a3iwE :: [a_a3ipj]) (a_a3iwF :: Symbol) :: Symbol where
  ShowList_6989586621679795990 @a_a3ipj (ls_a3iwJ :: [a_a3ipj]) (s_a3iwK :: Symbol) = Apply (Apply (Apply ShowListWithSym0 ShowsSym0) ls_a3iwJ) s_a3iwK
class PShow a_a3ipj where
  type family ShowsPrec (arg_a3iw0 :: Natural) (arg_a3iw1 :: a_a3ipj) (arg_a3iw2 :: Symbol) :: Symbol
  type family Show_ (arg_a3iw7 :: a_a3ipj) :: Symbol
  type family ShowList (arg_a3iwa :: [a_a3ipj]) (arg_a3iwb :: Symbol) :: Symbol
  type ShowsPrec a_a3iwf a_a3iwg a_a3iwh = ShowsPrec_6989586621679795970 a_a3iwf a_a3iwg a_a3iwh
  type Show_ a_a3iwt = Show__6989586621679795982 a_a3iwt
  type ShowList a_a3iwA a_a3iwB = ShowList_6989586621679795990 a_a3iwA a_a3iwB
type ShowsPrec_6989586621679796002 :: forall a_a3ipB. Natural
                                                      -> [a_a3ipB] -> Symbol -> Symbol
type family ShowsPrec_6989586621679796002 @a_a3ipB (a_a3iwU :: Natural) (a_a3iwV :: [a_a3ipB]) (a_a3iwW :: Symbol) :: Symbol where
  ShowsPrec_6989586621679796002 @a_a3ipB (_ :: Natural) (a_6989586621679796004_a3ix1 :: [a_a3ipB]) (a_6989586621679796006_a3ix2 :: Symbol) = Apply (Apply ShowListSym0 a_6989586621679796004_a3ix1) a_6989586621679796006_a3ix2
instance PShow [a_a3ipB] where
  type ShowsPrec a_a3iwL a_a3iwM a_a3iwN = ShowsPrec_6989586621679796002 a_a3iwL a_a3iwM a_a3iwN
type ShowsPrec_6989586621679796020 :: forall a_a3ipF
                                              b_a3ipG. Natural
                                                      -> (a_a3ipF, b_a3ipG) -> Symbol -> Symbol
type family ShowsPrec_6989586621679796020 @a_a3ipF @b_a3ipG (a_a3ix8 :: Natural) (a_a3ix9 :: (a_a3ipF,
                                                                                              b_a3ipG)) (a_a3ixa :: Symbol) :: Symbol where
  ShowsPrec_6989586621679796020 @a_a3ipF @b_a3ipG (_ :: Natural) ('(a_a3ixf,
                                                                    b_a3ixg) :: (a_a3ipF,
                                                                                  b_a3ipG)) (s_a3ixh :: Symbol) = Apply (Apply Show_tupleSym0 (Apply (Apply (:@#@$) (Apply ShowsSym0 a_a3ixf)) (Apply (Apply (:@#@$) (Apply ShowsSym0 b_a3ixg)) NilSym0))) s_a3ixh
instance PShow (a_a3ipF, b_a3ipG) where
  type ShowsPrec a_a3ix3 a_a3ix4 a_a3ix5 = ShowsPrec_6989586621679796020 a_a3ix3 a_a3ix4 a_a3ix5
type ShowsPrec_6989586621679796035 :: forall a_a3ipK
                                              b_a3ipL
                                              c_a3ipM. Natural
                                                      -> (a_a3ipK, b_a3ipL, c_a3ipM)
                                                          -> Symbol -> Symbol
type family ShowsPrec_6989586621679796035 @a_a3ipK @b_a3ipL @c_a3ipM (a_a3ixn :: Natural) (a_a3ixo :: (a_a3ipK,
                                                                                                        b_a3ipL,
                                                                                                        c_a3ipM)) (a_a3ixp :: Symbol) :: Symbol where
  ShowsPrec_6989586621679796035 @a_a3ipK @b_a3ipL @c_a3ipM (_ :: Natural) ('(a_a3ixu,
                                                                              b_a3ixv,
                                                                              c_a3ixw) :: (a_a3ipK,
                                                                                          b_a3ipL,
                                                                                          c_a3ipM)) (s_a3ixx :: Symbol) = Apply (Apply Show_tupleSym0 (Apply (Apply (:@#@$) (Apply ShowsSym0 a_a3ixu)) (Apply (Apply (:@#@$) (Apply ShowsSym0 b_a3ixv)) (Apply (Apply (:@#@$) (Apply ShowsSym0 c_a3ixw)) NilSym0)))) s_a3ixx
instance PShow (a_a3ipK, b_a3ipL, c_a3ipM) where
  type ShowsPrec a_a3ixi a_a3ixj a_a3ixk = ShowsPrec_6989586621679796035 a_a3ixi a_a3ixj a_a3ixk
type ShowsPrec_6989586621679796051 :: forall a_a3ipR
                                              b_a3ipS
                                              c_a3ipT
                                              d_a3ipU. Natural
                                                      -> (a_a3ipR, b_a3ipS, c_a3ipT, d_a3ipU)
                                                          -> Symbol -> Symbol
type family ShowsPrec_6989586621679796051 @a_a3ipR @b_a3ipS @c_a3ipT @d_a3ipU (a_a3ixD :: Natural) (a_a3ixE :: (a_a3ipR,
                                                                                                                b_a3ipS,
                                                                                                                c_a3ipT,
                                                                                                                d_a3ipU)) (a_a3ixF :: Symbol) :: Symbol where
  ShowsPrec_6989586621679796051 @a_a3ipR @b_a3ipS @c_a3ipT @d_a3ipU (_ :: Natural) ('(a_a3ixK,
                                                                                      b_a3ixL,
                                                                                      c_a3ixM,
                                                                                      d_a3ixN) :: (a_a3ipR,
                                                                                                    b_a3ipS,
                                                                                                    c_a3ipT,
                                                                                                    d_a3ipU)) (s_a3ixO :: Symbol) = Apply (Apply Show_tupleSym0 (Apply (Apply (:@#@$) (Apply ShowsSym0 a_a3ixK)) (Apply (Apply (:@#@$) (Apply ShowsSym0 b_a3ixL)) (Apply (Apply (:@#@$) (Apply ShowsSym0 c_a3ixM)) (Apply (Apply (:@#@$) (Apply ShowsSym0 d_a3ixN)) NilSym0))))) s_a3ixO
instance PShow (a_a3ipR, b_a3ipS, c_a3ipT, d_a3ipU) where
  type ShowsPrec a_a3ixy a_a3ixz a_a3ixA = ShowsPrec_6989586621679796051 a_a3ixy a_a3ixz a_a3ixA
type ShowsPrec_6989586621679796068 :: forall a_a3iq0
                                              b_a3iq1
                                              c_a3iq2
                                              d_a3iq3
                                              e_a3iq4. Natural
                                                      -> (a_a3iq0, b_a3iq1, c_a3iq2, d_a3iq3,
                                                          e_a3iq4)
                                                          -> Symbol -> Symbol
type family ShowsPrec_6989586621679796068 @a_a3iq0 @b_a3iq1 @c_a3iq2 @d_a3iq3 @e_a3iq4 (a_a3ixU :: Natural) (a_a3ixV :: (a_a3iq0,
                                                                                                                          b_a3iq1,
                                                                                                                          c_a3iq2,
                                                                                                                          d_a3iq3,
                                                                                                                          e_a3iq4)) (a_a3ixW :: Symbol) :: Symbol where
  ShowsPrec_6989586621679796068 @a_a3iq0 @b_a3iq1 @c_a3iq2 @d_a3iq3 @e_a3iq4 (_ :: Natural) ('(a_a3iy1,
                                                                                                b_a3iy2,
                                                                                                c_a3iy3,
                                                                                                d_a3iy4,
                                                                                                e_a3iy5) :: (a_a3iq0,
                                                                                                            b_a3iq1,
                                                                                                            c_a3iq2,
                                                                                                            d_a3iq3,
                                                                                                            e_a3iq4)) (s_a3iy6 :: Symbol) = Apply (Apply Show_tupleSym0 (Apply (Apply (:@#@$) (Apply ShowsSym0 a_a3iy1)) (Apply (Apply (:@#@$) (Apply ShowsSym0 b_a3iy2)) (Apply (Apply (:@#@$) (Apply ShowsSym0 c_a3iy3)) (Apply (Apply (:@#@$) (Apply ShowsSym0 d_a3iy4)) (Apply (Apply (:@#@$) (Apply ShowsSym0 e_a3iy5)) NilSym0)))))) s_a3iy6
instance PShow (a_a3iq0, b_a3iq1, c_a3iq2, d_a3iq3, e_a3iq4) where
  type ShowsPrec a_a3ixP a_a3ixQ a_a3ixR = ShowsPrec_6989586621679796068 a_a3ixP a_a3ixQ a_a3ixR
type ShowsPrec_6989586621679796086 :: forall a_a3iqb
                                              b_a3iqc
                                              c_a3iqd
                                              d_a3iqe
                                              e_a3iqf
                                              f_a3iqg. Natural
                                                      -> (a_a3iqb, b_a3iqc, c_a3iqd, d_a3iqe,
                                                          e_a3iqf, f_a3iqg)
                                                          -> Symbol -> Symbol
type family ShowsPrec_6989586621679796086 @a_a3iqb @b_a3iqc @c_a3iqd @d_a3iqe @e_a3iqf @f_a3iqg (a_a3iyc :: Natural) (a_a3iyd :: (a_a3iqb,
                                                                                                                                  b_a3iqc,
                                                                                                                                  c_a3iqd,
                                                                                                                                  d_a3iqe,
                                                                                                                                  e_a3iqf,
                                                                                                                                  f_a3iqg)) (a_a3iye :: Symbol) :: Symbol where
  ShowsPrec_6989586621679796086 @a_a3iqb @b_a3iqc @c_a3iqd @d_a3iqe @e_a3iqf @f_a3iqg (_ :: Natural) ('(a_a3iyj,
                                                                                                        b_a3iyk,
                                                                                                        c_a3iyl,
                                                                                                        d_a3iym,
                                                                                                        e_a3iyn,
                                                                                                        f_a3iyo) :: (a_a3iqb,
                                                                                                                      b_a3iqc,
                                                                                                                      c_a3iqd,
                                                                                                                      d_a3iqe,
                                                                                                                      e_a3iqf,
                                                                                                                      f_a3iqg)) (s_a3iyp :: Symbol) = Apply (Apply Show_tupleSym0 (Apply (Apply (:@#@$) (Apply ShowsSym0 a_a3iyj)) (Apply (Apply (:@#@$) (Apply ShowsSym0 b_a3iyk)) (Apply (Apply (:@#@$) (Apply ShowsSym0 c_a3iyl)) (Apply (Apply (:@#@$) (Apply ShowsSym0 d_a3iym)) (Apply (Apply (:@#@$) (Apply ShowsSym0 e_a3iyn)) (Apply (Apply (:@#@$) (Apply ShowsSym0 f_a3iyo)) NilSym0))))))) s_a3iyp
instance PShow (a_a3iqb, b_a3iqc, c_a3iqd, d_a3iqe, e_a3iqf,
                f_a3iqg) where
  type ShowsPrec a_a3iy7 a_a3iy8 a_a3iy9 = ShowsPrec_6989586621679796086 a_a3iy7 a_a3iy8 a_a3iy9
type ShowsPrec_6989586621679796105 :: forall a_a3iqo
                                              b_a3iqp
                                              c_a3iqq
                                              d_a3iqr
                                              e_a3iqs
                                              f_a3iqt
                                              g_a3iqu. Natural
                                                      -> (a_a3iqo, b_a3iqp, c_a3iqq, d_a3iqr,
                                                          e_a3iqs, f_a3iqt, g_a3iqu)
                                                          -> Symbol -> Symbol
type family ShowsPrec_6989586621679796105 @a_a3iqo @b_a3iqp @c_a3iqq @d_a3iqr @e_a3iqs @f_a3iqt @g_a3iqu (a_a3iyv :: Natural) (a_a3iyw :: (a_a3iqo,
                                                                                                                                            b_a3iqp,
                                                                                                                                            c_a3iqq,
                                                                                                                                            d_a3iqr,
                                                                                                                                            e_a3iqs,
                                                                                                                                            f_a3iqt,
                                                                                                                                            g_a3iqu)) (a_a3iyx :: Symbol) :: Symbol where
  ShowsPrec_6989586621679796105 @a_a3iqo @b_a3iqp @c_a3iqq @d_a3iqr @e_a3iqs @f_a3iqt @g_a3iqu (_ :: Natural) ('(a_a3iyC,
                                                                                                                  b_a3iyD,
                                                                                                                  c_a3iyE,
                                                                                                                  d_a3iyF,
                                                                                                                  e_a3iyG,
                                                                                                                  f_a3iyH,
                                                                                                                  g_a3iyI) :: (a_a3iqo,
                                                                                                                              b_a3iqp,
                                                                                                                              c_a3iqq,
                                                                                                                              d_a3iqr,
                                                                                                                              e_a3iqs,
                                                                                                                              f_a3iqt,
                                                                                                                              g_a3iqu)) (s_a3iyJ :: Symbol) = Apply (Apply Show_tupleSym0 (Apply (Apply (:@#@$) (Apply ShowsSym0 a_a3iyC)) (Apply (Apply (:@#@$) (Apply ShowsSym0 b_a3iyD)) (Apply (Apply (:@#@$) (Apply ShowsSym0 c_a3iyE)) (Apply (Apply (:@#@$) (Apply ShowsSym0 d_a3iyF)) (Apply (Apply (:@#@$) (Apply ShowsSym0 e_a3iyG)) (Apply (Apply (:@#@$) (Apply ShowsSym0 f_a3iyH)) (Apply (Apply (:@#@$) (Apply ShowsSym0 g_a3iyI)) NilSym0)))))))) s_a3iyJ
instance PShow (a_a3iqo, b_a3iqp, c_a3iqq, d_a3iqr, e_a3iqs,
                f_a3iqt, g_a3iqu) where
  type ShowsPrec a_a3iyq a_a3iyr a_a3iys = ShowsPrec_6989586621679796105 a_a3iyq a_a3iyr a_a3iys
sShow_tuple ::
  (forall (t_a3iyK :: [(~>) Symbol Symbol]) (t_a3iyL :: Symbol).
    Sing t_a3iyK
    -> Sing t_a3iyL
      -> Sing (Show_tuple t_a3iyK t_a3iyL :: Symbol) :: Type)
sAppPrec1 :: (Sing (AppPrec1 :: Natural) :: Type)
sAppPrec :: (Sing (AppPrec :: Natural) :: Type)
sShowCommaSpace ::
  (forall (t_a3iyP :: Symbol).
    Sing t_a3iyP -> Sing (ShowCommaSpace t_a3iyP :: Symbol) :: Type)
sShowSpace ::
  (forall (t_a3iyR :: Symbol).
    Sing t_a3iyR -> Sing (ShowSpace t_a3iyR :: Symbol) :: Type)
sShowParen ::
  (forall (t_a3iyT :: Bool)
          (t_a3iyU :: (~>) Symbol Symbol)
          (t_a3iyV :: Symbol).
    Sing t_a3iyT
    -> Sing t_a3iyU
      -> Sing t_a3iyV
          -> Sing (ShowParen t_a3iyT t_a3iyU t_a3iyV :: Symbol) :: Type)
sShowString ::
  (forall (t_a3iz3 :: Symbol) (t_a3iz4 :: Symbol).
    Sing t_a3iz3
    -> Sing t_a3iz4
      -> Sing (ShowString t_a3iz3 t_a3iz4 :: Symbol) :: Type)
sShowChar ::
  (forall (t_a3iz8 :: Char) (t_a3iz9 :: Symbol).
    Sing t_a3iz8
    -> Sing t_a3iz9
      -> Sing (ShowChar t_a3iz8 t_a3iz9 :: Symbol) :: Type)
sShowListWith ::
  (forall (t_a3izd :: (~>) a_a3ip3 ((~>) Symbol Symbol))
          (t_a3ize :: [a_a3ip3])
          (t_a3izf :: Symbol).
    Sing t_a3izd
    -> Sing t_a3ize
      -> Sing t_a3izf
          -> Sing (ShowListWith t_a3izd t_a3ize t_a3izf :: Symbol) :: Type)
sShows ::
  (forall (t_a3izn :: a_a3ip4) (t_a3izo :: Symbol).
    SShow a_a3ip4 =>
    Sing t_a3izn
    -> Sing t_a3izo -> Sing (Shows t_a3izn t_a3izo :: Symbol) :: Type)
sShow_tuple
  (sSs :: Sing ss_a3ius)
  (sA_6989586621679795849 :: Sing a_6989586621679795849_a3iut)
  = applySing
      (applySing
          (applySing
            (singFun3 @(.@#@$) (%.))
            (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '(')))
          (applySing
            (applySing
                (singFun3 @(.@#@$) (%.))
                (applySing
                  (applySing
                      (singFun2 @Foldr1Sym0 sFoldr1)
                      (singFun2
                        @(LamCases_6989586621679795858Sym0 ss_a3ius a_6989586621679795849_a3iut)
                        (\cases
                            (sS :: Sing s_a3iuw) (sR :: Sing r_a3iux)
                              -> applySing
                                  (applySing (singFun3 @(.@#@$) (%.)) sS)
                                  (applySing
                                      (applySing
                                        (singFun3 @(.@#@$) (%.))
                                        (applySing
                                            (singFun2 @ShowCharSym0 sShowChar)
                                            (sing :: Sing ',')))
                                      sR))))
                  sSs))
            (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing ')'))))
      sA_6989586621679795849
sAppPrec1 = sFromInteger (sing :: Sing 11)
sAppPrec = sFromInteger (sing :: Sing 10)
sShowCommaSpace
  (sA_6989586621679795869 :: Sing a_6989586621679795869_a3iuK)
  = applySing
      (applySing
          (singFun2 @ShowStringSym0 sShowString) (sing :: Sing ", "))
      sA_6989586621679795869
sShowSpace
  (sA_6989586621679795875 :: Sing a_6989586621679795875_a3iuQ)
  = applySing
      (singFun1
          @(LamCases_6989586621679795881Sym0 a_6989586621679795875_a3iuQ)
          (\cases
            (sXs :: Sing xs_a3iuT)
              -> applySing
                    (applySing (singFun2 @(<>@#@$) (%<>)) (sing :: Sing " ")) sXs))
      sA_6989586621679795875
sShowParen
  (sB :: Sing b_a3iv6)
  (sP :: Sing p_a3iv7)
  (sA_6989586621679795887 :: Sing a_6989586621679795887_a3iv8)
  = applySing
      (applySing
          (singFun1
            @(LamCases_6989586621679795899Sym0 b_a3iv6 p_a3iv7 a_6989586621679795887_a3iv8)
            (\cases
                STrue
                  -> applySing
                      (applySing
                          (singFun3 @(.@#@$) (%.))
                          (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing '(')))
                      (applySing
                          (applySing (singFun3 @(.@#@$) (%.)) sP)
                          (applySing (singFun2 @ShowCharSym0 sShowChar) (sing :: Sing ')')))
                SFalse -> sP))
          sB)
      sA_6989586621679795887
sShowString
  (sA_6989586621679795904 :: Sing a_6989586621679795904_a3ivn)
  (sA_6989586621679795906 :: Sing a_6989586621679795906_a3ivo)
  = applySing
      (applySing (singFun2 @(<>@#@$) (%<>)) sA_6989586621679795904)
      sA_6989586621679795906
sShowChar
  (sA_6989586621679795915 :: Sing a_6989586621679795915_a3ivy)
  (sA_6989586621679795917 :: Sing a_6989586621679795917_a3ivz)
  = applySing
      (applySing
          (singFun2 @ConsSymbolSym0 sConsSymbol) sA_6989586621679795915)
      sA_6989586621679795917
sShowListWith _ SNil (sS :: Sing s_a3ivH)
  = applySing
      (applySing (singFun2 @(<>@#@$) (%<>)) (sing :: Sing "[]")) sS
sShowListWith
  (sShowx :: Sing showx_a3ivI)
  (SCons (sX :: Sing x_a3ivJ) (sXs :: Sing xs_a3ivK))
  (sS :: Sing s_a3ivL)
  = let
      sShowl ::
        forall arg_a3izu. Sing arg_a3izu
                          -> Sing (Let6989586621679795938Showl showx_a3ivI x_a3ivJ xs_a3ivK s_a3ivL arg_a3izu)
      sShowl SNil
        = applySing
            (applySing (singFun2 @(<>@#@$) (%<>)) (sing :: Sing "]")) sS
      sShowl (SCons (sY :: Sing y_a3ivP) (sYs :: Sing ys_a3ivQ))
        = applySing
            (applySing (singFun2 @(<>@#@$) (%<>)) (sing :: Sing ","))
            (applySing
                (applySing sShowx sY)
                (applySing
                  (singFun1
                      @(Let6989586621679795938ShowlSym0 showx_a3ivI x_a3ivJ xs_a3ivK s_a3ivL)
                      sShowl)
                  sYs))
    in
      applySing
        (applySing (singFun2 @(<>@#@$) (%<>)) (sing :: Sing "["))
        (applySing
            (applySing sShowx sX)
            (applySing
              (singFun1
                  @(Let6989586621679795938ShowlSym0 showx_a3ivI x_a3ivJ xs_a3ivK s_a3ivL)
                  sShowl)
              sXs))
sShows
  (sS :: Sing s_a3ivY)
  (sA_6989586621679795943 :: Sing a_6989586621679795943_a3ivZ)
  = applySing
      (applySing
          (applySing
            (singFun3 @ShowsPrecSym0 sShowsPrec)
            (sFromInteger (sing :: Sing 0)))
          sS)
      sA_6989586621679795943
instance SingI (Show_tupleSym0 :: (~>) [(~>) Symbol Symbol] ((~>) Symbol Symbol)) where
  sing = singFun2 @Show_tupleSym0 sShow_tuple
instance SingI d_a3iyM =>
          SingI (Show_tupleSym1 (d_a3iyM :: [(~>) Symbol Symbol]) :: (~>) Symbol Symbol) where
  sing
    = singFun1
        @(Show_tupleSym1 (d_a3iyM :: [(~>) Symbol Symbol]))
        (sShow_tuple (sing @d_a3iyM))
instance SingI1 (Show_tupleSym1 :: [(~>) Symbol Symbol]
                                    -> (~>) Symbol Symbol) where
  liftSing (s_a3iyO :: Sing (d_a3iyM :: [(~>) Symbol Symbol]))
    = singFun1
        @(Show_tupleSym1 (d_a3iyM :: [(~>) Symbol Symbol]))
        (sShow_tuple s_a3iyO)
instance SingI (ShowCommaSpaceSym0 :: (~>) Symbol Symbol) where
  sing = singFun1 @ShowCommaSpaceSym0 sShowCommaSpace
instance SingI (ShowSpaceSym0 :: (~>) Symbol Symbol) where
  sing = singFun1 @ShowSpaceSym0 sShowSpace
instance SingI (ShowParenSym0 :: (~>) Bool ((~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol))) where
  sing = singFun3 @ShowParenSym0 sShowParen
instance SingI d_a3iyW =>
          SingI (ShowParenSym1 (d_a3iyW :: Bool) :: (~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol)) where
  sing
    = singFun2
        @(ShowParenSym1 (d_a3iyW :: Bool)) (sShowParen (sing @d_a3iyW))
instance SingI1 (ShowParenSym1 :: Bool
                                  -> (~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol)) where
  liftSing (s_a3iz2 :: Sing (d_a3iyW :: Bool))
    = singFun2 @(ShowParenSym1 (d_a3iyW :: Bool)) (sShowParen s_a3iz2)
instance (SingI d_a3iyW, SingI d_a3iyX) =>
          SingI (ShowParenSym2 (d_a3iyW :: Bool) (d_a3iyX :: (~>) Symbol Symbol) :: (~>) Symbol Symbol) where
  sing
    = singFun1
        @(ShowParenSym2 (d_a3iyW :: Bool) (d_a3iyX :: (~>) Symbol Symbol))
        (sShowParen (sing @d_a3iyW) (sing @d_a3iyX))
instance SingI d_a3iyW =>
          SingI1 (ShowParenSym2 (d_a3iyW :: Bool) :: (~>) Symbol Symbol
                                                    -> (~>) Symbol Symbol) where
  liftSing (s_a3iyZ :: Sing (d_a3iyX :: (~>) Symbol Symbol))
    = singFun1
        @(ShowParenSym2 (d_a3iyW :: Bool) (d_a3iyX :: (~>) Symbol Symbol))
        (sShowParen (sing @d_a3iyW) s_a3iyZ)
instance SingI2 (ShowParenSym2 :: Bool
                                  -> (~>) Symbol Symbol -> (~>) Symbol Symbol) where
  liftSing2
    (s_a3iz0 :: Sing (d_a3iyW :: Bool))
    (s_a3iz1 :: Sing (d_a3iyX :: (~>) Symbol Symbol))
    = singFun1
        @(ShowParenSym2 (d_a3iyW :: Bool) (d_a3iyX :: (~>) Symbol Symbol))
        (sShowParen s_a3iz0 s_a3iz1)
instance SingI (ShowStringSym0 :: (~>) Symbol ((~>) Symbol Symbol)) where
  sing = singFun2 @ShowStringSym0 sShowString
instance SingI d_a3iz5 =>
          SingI (ShowStringSym1 (d_a3iz5 :: Symbol) :: (~>) Symbol Symbol) where
  sing
    = singFun1
        @(ShowStringSym1 (d_a3iz5 :: Symbol)) (sShowString (sing @d_a3iz5))
instance SingI1 (ShowStringSym1 :: Symbol
                                    -> (~>) Symbol Symbol) where
  liftSing (s_a3iz7 :: Sing (d_a3iz5 :: Symbol))
    = singFun1
        @(ShowStringSym1 (d_a3iz5 :: Symbol)) (sShowString s_a3iz7)
instance SingI (ShowCharSym0 :: (~>) Char ((~>) Symbol Symbol)) where
  sing = singFun2 @ShowCharSym0 sShowChar
instance SingI d_a3iza =>
          SingI (ShowCharSym1 (d_a3iza :: Char) :: (~>) Symbol Symbol) where
  sing
    = singFun1
        @(ShowCharSym1 (d_a3iza :: Char)) (sShowChar (sing @d_a3iza))
instance SingI1 (ShowCharSym1 :: Char -> (~>) Symbol Symbol) where
  liftSing (s_a3izc :: Sing (d_a3iza :: Char))
    = singFun1 @(ShowCharSym1 (d_a3iza :: Char)) (sShowChar s_a3izc)
instance SingI (ShowListWithSym0 :: (~>) ((~>) a_a3ip3 ((~>) Symbol Symbol)) ((~>) [a_a3ip3] ((~>) Symbol Symbol))) where
  sing = singFun3 @ShowListWithSym0 sShowListWith
instance SingI d_a3izg =>
          SingI (ShowListWithSym1 (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)) :: (~>) [a_a3ip3] ((~>) Symbol Symbol)) where
  sing
    = singFun2
        @(ShowListWithSym1 (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)))
        (sShowListWith (sing @d_a3izg))
instance SingI1 (ShowListWithSym1 :: (~>) a_a3ip3 ((~>) Symbol Symbol)
                                      -> (~>) [a_a3ip3] ((~>) Symbol Symbol)) where
  liftSing
    (s_a3izm :: Sing (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)))
    = singFun2
        @(ShowListWithSym1 (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)))
        (sShowListWith s_a3izm)
instance (SingI d_a3izg, SingI d_a3izh) =>
          SingI (ShowListWithSym2 (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)) (d_a3izh :: [a_a3ip3]) :: (~>) Symbol Symbol) where
  sing
    = singFun1
        @(ShowListWithSym2 (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)) (d_a3izh :: [a_a3ip3]))
        (sShowListWith (sing @d_a3izg) (sing @d_a3izh))
instance SingI d_a3izg =>
          SingI1 (ShowListWithSym2 (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)) :: [a_a3ip3]
                                                                                    -> (~>) Symbol Symbol) where
  liftSing (s_a3izj :: Sing (d_a3izh :: [a_a3ip3]))
    = singFun1
        @(ShowListWithSym2 (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)) (d_a3izh :: [a_a3ip3]))
        (sShowListWith (sing @d_a3izg) s_a3izj)
instance SingI2 (ShowListWithSym2 :: (~>) a_a3ip3 ((~>) Symbol Symbol)
                                      -> [a_a3ip3] -> (~>) Symbol Symbol) where
  liftSing2
    (s_a3izk :: Sing (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)))
    (s_a3izl :: Sing (d_a3izh :: [a_a3ip3]))
    = singFun1
        @(ShowListWithSym2 (d_a3izg :: (~>) a_a3ip3 ((~>) Symbol Symbol)) (d_a3izh :: [a_a3ip3]))
        (sShowListWith s_a3izk s_a3izl)
instance SShow a_a3ip4 =>
          SingI (ShowsSym0 :: (~>) a_a3ip4 ((~>) Symbol Symbol)) where
  sing = singFun2 @ShowsSym0 sShows
instance (SShow a_a3ip4, SingI d_a3izp) =>
          SingI (ShowsSym1 (d_a3izp :: a_a3ip4) :: (~>) Symbol Symbol) where
  sing
    = singFun1
        @(ShowsSym1 (d_a3izp :: a_a3ip4)) (sShows (sing @d_a3izp))
instance SShow a_a3ip4 =>
          SingI1 (ShowsSym1 :: a_a3ip4 -> (~>) Symbol Symbol) where
  liftSing (s_a3izr :: Sing (d_a3izp :: a_a3ip4))
    = singFun1 @(ShowsSym1 (d_a3izp :: a_a3ip4)) (sShows s_a3izr)
class SShow a_a3ipj where
  sShowsPrec ::
    (forall (t_a3izw :: Natural)
            (t_a3izx :: a_a3ipj)
            (t_a3izy :: Symbol).
      Sing t_a3izw
      -> Sing t_a3izx
        -> Sing t_a3izy
            -> Sing (ShowsPrec t_a3izw t_a3izx t_a3izy :: Symbol) :: Type)
  sShow_ ::
    (forall (t_a3izG :: a_a3ipj).
      Sing t_a3izG -> Sing (Show_ t_a3izG :: Symbol) :: Type)
  sShowList ::
    (forall (t_a3izI :: [a_a3ipj]) (t_a3izJ :: Symbol).
      Sing t_a3izI
      -> Sing t_a3izJ
        -> Sing (ShowList t_a3izI t_a3izJ :: Symbol) :: Type)
  default sShowsPrec ::
            (forall (t_a3izw :: Natural)
                    (t_a3izx :: a_a3ipj)
                    (t_a3izy :: Symbol).
              ((ShowsPrec t_a3izw t_a3izx t_a3izy :: Symbol)
              ~ ShowsPrec_6989586621679795970 t_a3izw t_a3izx t_a3izy) =>
              Sing t_a3izw
              -> Sing t_a3izx
                -> Sing t_a3izy
                    -> Sing (ShowsPrec t_a3izw t_a3izx t_a3izy :: Symbol) :: Type)
  default sShow_ ::
            (forall (t_a3izG :: a_a3ipj).
              ((Show_ t_a3izG :: Symbol) ~ Show__6989586621679795982 t_a3izG) =>
              Sing t_a3izG -> Sing (Show_ t_a3izG :: Symbol) :: Type)
  default sShowList ::
            (forall (t_a3izI :: [a_a3ipj]) (t_a3izJ :: Symbol).
              ((ShowList t_a3izI t_a3izJ :: Symbol)
              ~ ShowList_6989586621679795990 t_a3izI t_a3izJ) =>
              Sing t_a3izI
              -> Sing t_a3izJ
                -> Sing (ShowList t_a3izI t_a3izJ :: Symbol) :: Type)
  sShowsPrec _ (sX :: Sing x_a3iwr) (sS :: Sing s_a3iws)
    = applySing
        (applySing
            (singFun2 @(<>@#@$) (%<>))
            (applySing (singFun1 @Show_Sym0 sShow_) sX))
        sS
  sShow_ (sX :: Sing x_a3iwz)
    = applySing
        (applySing (singFun2 @ShowsSym0 sShows) sX) (sing :: Sing "")
  sShowList (sLs :: Sing ls_a3iwJ) (sS :: Sing s_a3iwK)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowListWithSym0 sShowListWith)
              (singFun2 @ShowsSym0 sShows))
            sLs)
        sS
instance SShow a_a3ipB => SShow [a_a3ipB] where
  sShowsPrec
    _
    (sA_6989586621679796004 :: Sing a_6989586621679796004_a3ix1)
    (sA_6989586621679796006 :: Sing a_6989586621679796006_a3ix2)
    = applySing
        (applySing
            (singFun2 @ShowListSym0 sShowList) sA_6989586621679796004)
        sA_6989586621679796006
instance (SShow a_a3ipF, SShow b_a3ipG) =>
          SShow (a_a3ipF, b_a3ipG) where
  sShowsPrec
    _
    (STuple2 (sA :: Sing a_a3ixf) (sB :: Sing b_a3ixg))
    (sS :: Sing s_a3ixh)
    = applySing
        (applySing
            (singFun2 @Show_tupleSym0 sShow_tuple)
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing (singFun2 @ShowsSym0 sShows) sA))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing (singFun2 @ShowsSym0 sShows) sB))
                  SNil)))
        sS
instance (SShow a_a3ipK, SShow b_a3ipL, SShow c_a3ipM) =>
          SShow (a_a3ipK, b_a3ipL, c_a3ipM) where
  sShowsPrec
    _
    (STuple3 (sA :: Sing a_a3ixu) (sB :: Sing b_a3ixv)
              (sC :: Sing c_a3ixw))
    (sS :: Sing s_a3ixx)
    = applySing
        (applySing
            (singFun2 @Show_tupleSym0 sShow_tuple)
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing (singFun2 @ShowsSym0 sShows) sA))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing (singFun2 @ShowsSym0 sShows) sB))
                  (applySing
                    (applySing
                        (singFun2 @(:@#@$) SCons)
                        (applySing (singFun2 @ShowsSym0 sShows) sC))
                    SNil))))
        sS
instance (SShow a_a3ipR,
          SShow b_a3ipS,
          SShow c_a3ipT,
          SShow d_a3ipU) =>
          SShow (a_a3ipR, b_a3ipS, c_a3ipT, d_a3ipU) where
  sShowsPrec
    _
    (STuple4 (sA :: Sing a_a3ixK) (sB :: Sing b_a3ixL)
              (sC :: Sing c_a3ixM) (sD :: Sing d_a3ixN))
    (sS :: Sing s_a3ixO)
    = applySing
        (applySing
            (singFun2 @Show_tupleSym0 sShow_tuple)
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing (singFun2 @ShowsSym0 sShows) sA))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing (singFun2 @ShowsSym0 sShows) sB))
                  (applySing
                    (applySing
                        (singFun2 @(:@#@$) SCons)
                        (applySing (singFun2 @ShowsSym0 sShows) sC))
                    (applySing
                        (applySing
                          (singFun2 @(:@#@$) SCons)
                          (applySing (singFun2 @ShowsSym0 sShows) sD))
                        SNil)))))
        sS
instance (SShow a_a3iq0,
          SShow b_a3iq1,
          SShow c_a3iq2,
          SShow d_a3iq3,
          SShow e_a3iq4) =>
          SShow (a_a3iq0, b_a3iq1, c_a3iq2, d_a3iq3, e_a3iq4) where
  sShowsPrec
    _
    (STuple5 (sA :: Sing a_a3iy1) (sB :: Sing b_a3iy2)
              (sC :: Sing c_a3iy3) (sD :: Sing d_a3iy4) (sE :: Sing e_a3iy5))
    (sS :: Sing s_a3iy6)
    = applySing
        (applySing
            (singFun2 @Show_tupleSym0 sShow_tuple)
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing (singFun2 @ShowsSym0 sShows) sA))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing (singFun2 @ShowsSym0 sShows) sB))
                  (applySing
                    (applySing
                        (singFun2 @(:@#@$) SCons)
                        (applySing (singFun2 @ShowsSym0 sShows) sC))
                    (applySing
                        (applySing
                          (singFun2 @(:@#@$) SCons)
                          (applySing (singFun2 @ShowsSym0 sShows) sD))
                        (applySing
                          (applySing
                              (singFun2 @(:@#@$) SCons)
                              (applySing (singFun2 @ShowsSym0 sShows) sE))
                          SNil))))))
        sS
instance (SShow a_a3iqb,
          SShow b_a3iqc,
          SShow c_a3iqd,
          SShow d_a3iqe,
          SShow e_a3iqf,
          SShow f_a3iqg) =>
          SShow (a_a3iqb, b_a3iqc, c_a3iqd, d_a3iqe, e_a3iqf, f_a3iqg) where
  sShowsPrec
    _
    (STuple6 (sA :: Sing a_a3iyj) (sB :: Sing b_a3iyk)
              (sC :: Sing c_a3iyl) (sD :: Sing d_a3iym) (sE :: Sing e_a3iyn)
              (sF :: Sing f_a3iyo))
    (sS :: Sing s_a3iyp)
    = applySing
        (applySing
            (singFun2 @Show_tupleSym0 sShow_tuple)
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing (singFun2 @ShowsSym0 sShows) sA))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing (singFun2 @ShowsSym0 sShows) sB))
                  (applySing
                    (applySing
                        (singFun2 @(:@#@$) SCons)
                        (applySing (singFun2 @ShowsSym0 sShows) sC))
                    (applySing
                        (applySing
                          (singFun2 @(:@#@$) SCons)
                          (applySing (singFun2 @ShowsSym0 sShows) sD))
                        (applySing
                          (applySing
                              (singFun2 @(:@#@$) SCons)
                              (applySing (singFun2 @ShowsSym0 sShows) sE))
                          (applySing
                              (applySing
                                (singFun2 @(:@#@$) SCons)
                                (applySing (singFun2 @ShowsSym0 sShows) sF))
                              SNil)))))))
        sS
instance (SShow a_a3iqo,
          SShow b_a3iqp,
          SShow c_a3iqq,
          SShow d_a3iqr,
          SShow e_a3iqs,
          SShow f_a3iqt,
          SShow g_a3iqu) =>
          SShow (a_a3iqo, b_a3iqp, c_a3iqq, d_a3iqr, e_a3iqs, f_a3iqt,
                g_a3iqu) where
  sShowsPrec
    _
    (STuple7 (sA :: Sing a_a3iyC) (sB :: Sing b_a3iyD)
              (sC :: Sing c_a3iyE) (sD :: Sing d_a3iyF) (sE :: Sing e_a3iyG)
              (sF :: Sing f_a3iyH) (sG :: Sing g_a3iyI))
    (sS :: Sing s_a3iyJ)
    = applySing
        (applySing
            (singFun2 @Show_tupleSym0 sShow_tuple)
            (applySing
              (applySing
                  (singFun2 @(:@#@$) SCons)
                  (applySing (singFun2 @ShowsSym0 sShows) sA))
              (applySing
                  (applySing
                    (singFun2 @(:@#@$) SCons)
                    (applySing (singFun2 @ShowsSym0 sShows) sB))
                  (applySing
                    (applySing
                        (singFun2 @(:@#@$) SCons)
                        (applySing (singFun2 @ShowsSym0 sShows) sC))
                    (applySing
                        (applySing
                          (singFun2 @(:@#@$) SCons)
                          (applySing (singFun2 @ShowsSym0 sShows) sD))
                        (applySing
                          (applySing
                              (singFun2 @(:@#@$) SCons)
                              (applySing (singFun2 @ShowsSym0 sShows) sE))
                          (applySing
                              (applySing
                                (singFun2 @(:@#@$) SCons)
                                (applySing (singFun2 @ShowsSym0 sShows) sF))
                              (applySing
                                (applySing
                                    (singFun2 @(:@#@$) SCons)
                                    (applySing (singFun2 @ShowsSym0 sShows) sG))
                                SNil))))))))
        sS
instance SShow a_a3ipj =>
          SingI (ShowsPrecSym0 :: (~>) Natural ((~>) a_a3ipj ((~>) Symbol Symbol))) where
  sing = singFun3 @ShowsPrecSym0 sShowsPrec
instance (SShow a_a3ipj, SingI d_a3izz) =>
          SingI (ShowsPrecSym1 (d_a3izz :: Natural) :: (~>) a_a3ipj ((~>) Symbol Symbol)) where
  sing
    = singFun2
        @(ShowsPrecSym1 (d_a3izz :: Natural)) (sShowsPrec (sing @d_a3izz))
instance SShow a_a3ipj =>
          SingI1 (ShowsPrecSym1 :: Natural
                                  -> (~>) a_a3ipj ((~>) Symbol Symbol)) where
  liftSing (s_a3izF :: Sing (d_a3izz :: Natural))
    = singFun2
        @(ShowsPrecSym1 (d_a3izz :: Natural)) (sShowsPrec s_a3izF)
instance (SShow a_a3ipj, SingI d_a3izz, SingI d_a3izA) =>
          SingI (ShowsPrecSym2 (d_a3izz :: Natural) (d_a3izA :: a_a3ipj) :: (~>) Symbol Symbol) where
  sing
    = singFun1
        @(ShowsPrecSym2 (d_a3izz :: Natural) (d_a3izA :: a_a3ipj))
        (sShowsPrec (sing @d_a3izz) (sing @d_a3izA))
instance (SShow a_a3ipj, SingI d_a3izz) =>
          SingI1 (ShowsPrecSym2 (d_a3izz :: Natural) :: a_a3ipj
                                                        -> (~>) Symbol Symbol) where
  liftSing (s_a3izC :: Sing (d_a3izA :: a_a3ipj))
    = singFun1
        @(ShowsPrecSym2 (d_a3izz :: Natural) (d_a3izA :: a_a3ipj))
        (sShowsPrec (sing @d_a3izz) s_a3izC)
instance SShow a_a3ipj =>
          SingI2 (ShowsPrecSym2 :: Natural
                                  -> a_a3ipj -> (~>) Symbol Symbol) where
  liftSing2
    (s_a3izD :: Sing (d_a3izz :: Natural))
    (s_a3izE :: Sing (d_a3izA :: a_a3ipj))
    = singFun1
        @(ShowsPrecSym2 (d_a3izz :: Natural) (d_a3izA :: a_a3ipj))
        (sShowsPrec s_a3izD s_a3izE)
instance SShow a_a3ipj =>
          SingI (Show_Sym0 :: (~>) a_a3ipj Symbol) where
  sing = singFun1 @Show_Sym0 sShow_
instance SShow a_a3ipj =>
          SingI (ShowListSym0 :: (~>) [a_a3ipj] ((~>) Symbol Symbol)) where
  sing = singFun2 @ShowListSym0 sShowList
instance (SShow a_a3ipj, SingI d_a3izK) =>
          SingI (ShowListSym1 (d_a3izK :: [a_a3ipj]) :: (~>) Symbol Symbol) where
  sing
    = singFun1
        @(ShowListSym1 (d_a3izK :: [a_a3ipj])) (sShowList (sing @d_a3izK))
instance SShow a_a3ipj =>
          SingI1 (ShowListSym1 :: [a_a3ipj] -> (~>) Symbol Symbol) where
  liftSing (s_a3izM :: Sing (d_a3izK :: [a_a3ipj]))
    = singFun1
        @(ShowListSym1 (d_a3izK :: [a_a3ipj])) (sShowList s_a3izM)

type ShowsNatSym0 :: (~>) Natural ((~>) Symbol Symbol)
data ShowsNatSym0 :: (~>) Natural ((~>) Symbol Symbol)
  where
    ShowsNatSym0KindInference :: SameKind (Apply ShowsNatSym0 arg_a3mmd) (ShowsNatSym1 arg_a3mmd) =>
                                  ShowsNatSym0 a6989586621679810722
type instance Apply @Natural @((~>) Symbol Symbol) ShowsNatSym0 a6989586621679810722 = ShowsNatSym1 a6989586621679810722
instance SuppressUnusedWarnings ShowsNatSym0 where
  suppressUnusedWarnings = snd ((,) ShowsNatSym0KindInference ())
type ShowsNatSym1 :: Natural -> (~>) Symbol Symbol
data ShowsNatSym1 (a6989586621679810722 :: Natural) :: (~>) Symbol Symbol
  where
    ShowsNatSym1KindInference :: SameKind (Apply (ShowsNatSym1 a6989586621679810722) arg_a3mmd) (ShowsNatSym2 a6989586621679810722 arg_a3mmd) =>
                                  ShowsNatSym1 a6989586621679810722 a6989586621679810723
type instance Apply @Symbol @Symbol (ShowsNatSym1 a6989586621679810722) a6989586621679810723 = ShowsNat a6989586621679810722 a6989586621679810723
instance SuppressUnusedWarnings (ShowsNatSym1 a6989586621679810722) where
  suppressUnusedWarnings = snd ((,) ShowsNatSym1KindInference ())
type ShowsNatSym2 :: Natural -> Symbol -> Symbol
type family ShowsNatSym2 (a6989586621679810722 :: Natural) (a6989586621679810723 :: Symbol) :: Symbol where
  ShowsNatSym2 a6989586621679810722 a6989586621679810723 = ShowsNat a6989586621679810722 a6989586621679810723
type ShowsNat :: Natural -> Symbol -> Symbol
type family ShowsNat (a_a3mmb :: Natural) (a_a3mmc :: Symbol) :: Symbol where
  ShowsNat 0 a_6989586621679810697_a3mmg = Apply (Apply ShowCharSym0 '0') a_6989586621679810697_a3mmg
  ShowsNat 1 a_6989586621679810699_a3mmh = Apply (Apply ShowCharSym0 '1') a_6989586621679810699_a3mmh
  ShowsNat 2 a_6989586621679810701_a3mmi = Apply (Apply ShowCharSym0 '2') a_6989586621679810701_a3mmi
  ShowsNat 3 a_6989586621679810703_a3mmj = Apply (Apply ShowCharSym0 '3') a_6989586621679810703_a3mmj
  ShowsNat 4 a_6989586621679810705_a3mmk = Apply (Apply ShowCharSym0 '4') a_6989586621679810705_a3mmk
  ShowsNat 5 a_6989586621679810707_a3mml = Apply (Apply ShowCharSym0 '5') a_6989586621679810707_a3mml
  ShowsNat 6 a_6989586621679810709_a3mmm = Apply (Apply ShowCharSym0 '6') a_6989586621679810709_a3mmm
  ShowsNat 7 a_6989586621679810711_a3mmn = Apply (Apply ShowCharSym0 '7') a_6989586621679810711_a3mmn
  ShowsNat 8 a_6989586621679810713_a3mmo = Apply (Apply ShowCharSym0 '8') a_6989586621679810713_a3mmo
  ShowsNat 9 a_6989586621679810715_a3mmp = Apply (Apply ShowCharSym0 '9') a_6989586621679810715_a3mmp
  ShowsNat n_a3mmq a_6989586621679810717_a3mmr = Apply (Apply (Apply (.@#@$) (Apply ShowsNatSym0 (Apply (Apply DivSym0 n_a3mmq) (FromInteger 10)))) (Apply ShowsNatSym0 (Apply (Apply ModSym0 n_a3mmq) (FromInteger 10)))) a_6989586621679810717_a3mmr

instance PShow Natural where
  type ShowsPrec _ n x = ShowsNat n x

instance SShow Natural where
  sShowsPrec _ sn sx =
    let n = fromSing sn
        x = fromSing sx
    in withSomeSSymbol (P.show n ++ T.unpack x) unsafeCoerce


type family LamCases_6989586621679812518_a3mPd c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_6989586621679812520_a3mPf where
      LamCases_6989586621679812518_a3mPd c_a3mP9 scrutinee_6989586621679812469_a3mP6 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ 'Nothing = s_a3mP3
data LamCases_6989586621679812518Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_69895866216798125206989586621679812521
  where
    LamCases_6989586621679812518Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812518Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) arg_a3mPg) (LamCases_6989586621679812518Sym1 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 arg_a3mPg) =>
                                                      LamCases_6989586621679812518Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125206989586621679812521
type instance Apply @_ @_ (LamCases_6989586621679812518Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) a_69895866216798125206989586621679812521 = LamCases_6989586621679812518_a3mPd c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125206989586621679812521
instance SuppressUnusedWarnings (LamCases_6989586621679812518Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812518Sym0KindInference ())
type family LamCases_6989586621679812518Sym1 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_69895866216798125206989586621679812521 where
  LamCases_6989586621679812518Sym1 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125206989586621679812521 = LamCases_6989586621679812518_a3mPd c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125206989586621679812521
type family LamCases_6989586621679812516_a3mPb c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_6989586621679812523_a3mPi where
  LamCases_6989586621679812516_a3mPb c_a3mP9 scrutinee_6989586621679812469_a3mP6 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ 'True = Apply (Apply (<>@#@$) "\\&") s_a3mP3
  LamCases_6989586621679812516_a3mPb c_a3mP9 scrutinee_6989586621679812469_a3mP6 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ 'False = Apply (LamCases_6989586621679812518Sym0 c_a3mP9 scrutinee_6989586621679812469_a3mP6 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ) scrutinee_6989586621679812469_a3mP6
data LamCases_6989586621679812516Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_69895866216798125236989586621679812524
  where
    LamCases_6989586621679812516Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812516Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) arg_a3mPj) (LamCases_6989586621679812516Sym1 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 arg_a3mPj) =>
                                                      LamCases_6989586621679812516Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125236989586621679812524
type instance Apply @_ @_ (LamCases_6989586621679812516Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) a_69895866216798125236989586621679812524 = LamCases_6989586621679812516_a3mPb c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125236989586621679812524
instance SuppressUnusedWarnings (LamCases_6989586621679812516Sym0 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812516Sym0KindInference ())
type family LamCases_6989586621679812516Sym1 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_69895866216798125236989586621679812524 where
  LamCases_6989586621679812516Sym1 c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125236989586621679812524 = LamCases_6989586621679812516_a3mPb c6989586621679812515 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125236989586621679812524
type family LamCases_6989586621679812513_a3mP8 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_6989586621679812526_a3mPl where
  LamCases_6989586621679812513_a3mP8 scrutinee_6989586621679812469_a3mP6 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ ('Just '(c_a3mP9,
                                                                                                                                _)) = Apply (LamCases_6989586621679812516Sym0 c_a3mP9 scrutinee_6989586621679812469_a3mP6 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ) (Apply p_a3mOX c_a3mP9)
  LamCases_6989586621679812513_a3mP8 scrutinee_6989586621679812469_a3mP6 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ 'Nothing = s_a3mP3
data LamCases_6989586621679812513Sym0 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_69895866216798125266989586621679812527
  where
    LamCases_6989586621679812513Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812513Sym0 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) arg_a3mPm) (LamCases_6989586621679812513Sym1 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 arg_a3mPm) =>
                                                      LamCases_6989586621679812513Sym0 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125266989586621679812527
type instance Apply @_ @_ (LamCases_6989586621679812513Sym0 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) a_69895866216798125266989586621679812527 = LamCases_6989586621679812513_a3mP8 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125266989586621679812527
instance SuppressUnusedWarnings (LamCases_6989586621679812513Sym0 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812513Sym0KindInference ())
type family LamCases_6989586621679812513Sym1 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_69895866216798125266989586621679812527 where
  LamCases_6989586621679812513Sym1 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125266989586621679812527 = LamCases_6989586621679812513_a3mP8 scrutinee_69895866216798124696989586621679812512 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125266989586621679812527
type family LamCases_6989586621679812510_a3mP5 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_6989586621679812529_a3mPo where
  LamCases_6989586621679812510_a3mP5 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ scrutinee_6989586621679812469_a3mP6 = Apply (LamCases_6989586621679812513Sym0 scrutinee_6989586621679812469_a3mP6 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ) scrutinee_6989586621679812469_a3mP6
data LamCases_6989586621679812510Sym0 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_69895866216798125296989586621679812530
  where
    LamCases_6989586621679812510Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812510Sym0 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) arg_a3mPp) (LamCases_6989586621679812510Sym1 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 arg_a3mPp) =>
                                                      LamCases_6989586621679812510Sym0 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125296989586621679812530
type instance Apply @_ @_ (LamCases_6989586621679812510Sym0 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) a_69895866216798125296989586621679812530 = LamCases_6989586621679812510_a3mP5 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125296989586621679812530
instance SuppressUnusedWarnings (LamCases_6989586621679812510Sym0 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812510Sym0KindInference ())
type family LamCases_6989586621679812510Sym1 s6989586621679812509 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_69895866216798125296989586621679812530 where
  LamCases_6989586621679812510Sym1 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125296989586621679812530 = LamCases_6989586621679812510_a3mP5 s6989586621679812509 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a_69895866216798125296989586621679812530
data Let6989586621679812506ContSym0 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a6989586621679812507
  where
    Let6989586621679812506ContSym0KindInference :: SameKind (Apply (Let6989586621679812506ContSym0 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) arg_a3mP2) (Let6989586621679812506ContSym1 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 arg_a3mP2) =>
                                                    Let6989586621679812506ContSym0 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a6989586621679812507
type instance Apply @_ @_ (Let6989586621679812506ContSym0 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) a6989586621679812507 = Let6989586621679812506Cont p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a6989586621679812507
instance SuppressUnusedWarnings (Let6989586621679812506ContSym0 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505) where
  suppressUnusedWarnings
    = snd ((,) Let6989586621679812506ContSym0KindInference ())
type family Let6989586621679812506ContSym1 (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a6989586621679812507 where
  Let6989586621679812506ContSym1 p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a6989586621679812507 = Let6989586621679812506Cont p6989586621679812503 f6989586621679812504 a_69895866216798124946989586621679812505 a6989586621679812507
type family Let6989586621679812506Cont (p6989586621679812503 :: (~>) Char Bool) (f6989586621679812504 :: (~>) Symbol Symbol) (a_69895866216798124946989586621679812505 :: Symbol) a_a3mP1 where
  Let6989586621679812506Cont p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ s_a3mP3 = Apply (LamCases_6989586621679812510Sym0 s_a3mP3 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ) (Apply UnconsSymbolSym0 s_a3mP3)
type family LamCases_6989586621679812543_a3mPC (sym6989586621679812541 :: Symbol) (s6989586621679812542 :: Symbol) a_6989586621679812548_a3mPH where
  LamCases_6989586621679812543_a3mPC sym_a3mPz s_a3mPA 'Nothing = s_a3mPA
  LamCases_6989586621679812543_a3mPC sym_a3mPz s_a3mPA ('Just '( '"',
                                                          cs_a3mPD)) = Apply (Apply ShowStringSym0 "\\\"") (Apply (Apply ShowLitSymbolSym0 cs_a3mPD) s_a3mPA)
  LamCases_6989586621679812543_a3mPC sym_a3mPz s_a3mPA ('Just '(c_a3mPE,
                                                          cs_a3mPF)) = Apply (Apply ShowLitCharSym0 c_a3mPE) (Apply (Apply ShowLitSymbolSym0 cs_a3mPF) s_a3mPA)
data LamCases_6989586621679812543Sym0 (sym6989586621679812541 :: Symbol) (s6989586621679812542 :: Symbol) a_69895866216798125486989586621679812549
  where
    LamCases_6989586621679812543Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812543Sym0 sym6989586621679812541 s6989586621679812542) arg_a3mPI) (LamCases_6989586621679812543Sym1 sym6989586621679812541 s6989586621679812542 arg_a3mPI) =>
                                                      LamCases_6989586621679812543Sym0 sym6989586621679812541 s6989586621679812542 a_69895866216798125486989586621679812549
type instance Apply @_ @_ (LamCases_6989586621679812543Sym0 sym6989586621679812541 s6989586621679812542) a_69895866216798125486989586621679812549 = LamCases_6989586621679812543_a3mPC sym6989586621679812541 s6989586621679812542 a_69895866216798125486989586621679812549
instance SuppressUnusedWarnings (LamCases_6989586621679812543Sym0 sym6989586621679812541 s6989586621679812542) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812543Sym0KindInference ())
type family LamCases_6989586621679812543Sym1 (sym6989586621679812541 :: Symbol) (s6989586621679812542 :: Symbol) a_69895866216798125486989586621679812549 where
  LamCases_6989586621679812543Sym1 sym6989586621679812541 s6989586621679812542 a_69895866216798125486989586621679812549 = LamCases_6989586621679812543_a3mPC sym6989586621679812541 s6989586621679812542 a_69895866216798125486989586621679812549
type family LamCases_6989586621679812593_a3mQq s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_6989586621679812596_a3mQt where
  LamCases_6989586621679812593_a3mQq s_a3mQo c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 lhs_6989586621679812467_a3mQr = Apply (Apply (==@#@$) lhs_6989586621679812467_a3mQr) 'H'
data LamCases_6989586621679812593Sym0 s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798125966989586621679812597
  where
    LamCases_6989586621679812593Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812593Sym0 s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) arg_a3mQu) (LamCases_6989586621679812593Sym1 s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 arg_a3mQu) =>
                                                      LamCases_6989586621679812593Sym0 s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798125966989586621679812597
type instance Apply @_ @_ (LamCases_6989586621679812593Sym0 s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) a_69895866216798125966989586621679812597 = LamCases_6989586621679812593_a3mQq s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798125966989586621679812597
instance SuppressUnusedWarnings (LamCases_6989586621679812593Sym0 s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812593Sym0KindInference ())
type family LamCases_6989586621679812593Sym1 s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798125966989586621679812597 where
  LamCases_6989586621679812593Sym1 s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798125966989586621679812597 = LamCases_6989586621679812593_a3mQq s6989586621679812592 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798125966989586621679812597
type family LamCases_6989586621679812583_a3mQg c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_6989586621679812601_a3mQy a_6989586621679812603_a3mQA where
  LamCases_6989586621679812583_a3mQg c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\a' s_a3mQh = Apply (Apply ShowStringSym0 "\\a") s_a3mQh
  LamCases_6989586621679812583_a3mQg c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\b' s_a3mQi = Apply (Apply ShowStringSym0 "\\b") s_a3mQi
  LamCases_6989586621679812583_a3mQg c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\f' s_a3mQj = Apply (Apply ShowStringSym0 "\\f") s_a3mQj
  LamCases_6989586621679812583_a3mQg c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\n' s_a3mQk = Apply (Apply ShowStringSym0 "\\n") s_a3mQk
  LamCases_6989586621679812583_a3mQg c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\r' s_a3mQl = Apply (Apply ShowStringSym0 "\\r") s_a3mQl
  LamCases_6989586621679812583_a3mQg c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\t' s_a3mQm = Apply (Apply ShowStringSym0 "\\t") s_a3mQm
  LamCases_6989586621679812583_a3mQg c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\v' s_a3mQn = Apply (Apply ShowStringSym0 "\\v") s_a3mQn
  LamCases_6989586621679812583_a3mQg c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\SO' s_a3mQo = Apply (Apply (Apply ProtectEscSym0 (LamCases_6989586621679812593Sym0 s_a3mQo c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0)) (Apply ShowStringSym0 "\\SO")) s_a3mQo
  LamCases_6989586621679812583_a3mQg c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 c_a3mQv s_a3mQw = Apply (Apply ShowStringSym0 (Apply (Apply ConsSymbolSym0 '\\') (Apply (Apply (!!@#@$) AsciiTabSym0) (Apply CharToNatSym0 c_a3mQv)))) s_a3mQw
data LamCases_6989586621679812583Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126016989586621679812602
  where
    LamCases_6989586621679812583Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812583Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) arg_a3mQB) (LamCases_6989586621679812583Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 arg_a3mQB) =>
                                                      LamCases_6989586621679812583Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602
type instance Apply @_ @_ (LamCases_6989586621679812583Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) a_69895866216798126016989586621679812602 = LamCases_6989586621679812583Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602
instance SuppressUnusedWarnings (LamCases_6989586621679812583Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812583Sym0KindInference ())
data LamCases_6989586621679812583Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126016989586621679812602 a_69895866216798126036989586621679812604
  where
    LamCases_6989586621679812583Sym1KindInference :: SameKind (Apply (LamCases_6989586621679812583Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602) arg_a3mQB) (LamCases_6989586621679812583Sym2 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602 arg_a3mQB) =>
                                                      LamCases_6989586621679812583Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602 a_69895866216798126036989586621679812604
type instance Apply @_ @_ (LamCases_6989586621679812583Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602) a_69895866216798126036989586621679812604 = LamCases_6989586621679812583_a3mQg c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602 a_69895866216798126036989586621679812604
instance SuppressUnusedWarnings (LamCases_6989586621679812583Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812583Sym1KindInference ())
type family LamCases_6989586621679812583Sym2 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126016989586621679812602 a_69895866216798126036989586621679812604 where
  LamCases_6989586621679812583Sym2 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602 a_69895866216798126036989586621679812604 = LamCases_6989586621679812583_a3mQg c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126016989586621679812602 a_69895866216798126036989586621679812604
type family LamCases_6989586621679812581_a3mQe c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_6989586621679812606_a3mQD where
  LamCases_6989586621679812581_a3mQe c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 'True = Apply (Apply ShowCharSym0 c_a3mQb) s_a3mQc
  LamCases_6989586621679812581_a3mQe c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 'False = Apply (Apply (LamCases_6989586621679812583Sym0 c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0) arg_6989586621679812463_a3mPZ) arg_6989586621679812465_a3mQ0
data LamCases_6989586621679812581Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126066989586621679812607
  where
    LamCases_6989586621679812581Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812581Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) arg_a3mQE) (LamCases_6989586621679812581Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 arg_a3mQE) =>
                                                      LamCases_6989586621679812581Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126066989586621679812607
type instance Apply @_ @_ (LamCases_6989586621679812581Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) a_69895866216798126066989586621679812607 = LamCases_6989586621679812581_a3mQe c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126066989586621679812607
instance SuppressUnusedWarnings (LamCases_6989586621679812581Sym0 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812581Sym0KindInference ())
type family LamCases_6989586621679812581Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126066989586621679812607 where
  LamCases_6989586621679812581Sym1 c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126066989586621679812607 = LamCases_6989586621679812581_a3mQe c6989586621679812579 s6989586621679812580 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126066989586621679812607
type family LamCases_6989586621679812575_a3mQ8 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_6989586621679812609_a3mQG a_6989586621679812611_a3mQI where
  LamCases_6989586621679812575_a3mQ8 c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\DEL' s_a3mQ9 = Apply (Apply ShowStringSym0 "\\DEL") s_a3mQ9
  LamCases_6989586621679812575_a3mQ8 c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 '\\' s_a3mQa = Apply (Apply ShowStringSym0 "\\\\") s_a3mQa
  LamCases_6989586621679812575_a3mQ8 c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 c_a3mQb s_a3mQc = Apply (LamCases_6989586621679812581Sym0 c_a3mQb s_a3mQc c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0) (Apply (Apply (>=@#@$) c_a3mQb) ' ')
data LamCases_6989586621679812575Sym0 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126096989586621679812610
  where
    LamCases_6989586621679812575Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812575Sym0 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) arg_a3mQJ) (LamCases_6989586621679812575Sym1 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 arg_a3mQJ) =>
                                                      LamCases_6989586621679812575Sym0 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610
type instance Apply @_ @_ (LamCases_6989586621679812575Sym0 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) a_69895866216798126096989586621679812610 = LamCases_6989586621679812575Sym1 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610
instance SuppressUnusedWarnings (LamCases_6989586621679812575Sym0 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812575Sym0KindInference ())
data LamCases_6989586621679812575Sym1 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126096989586621679812610 a_69895866216798126116989586621679812612
  where
    LamCases_6989586621679812575Sym1KindInference :: SameKind (Apply (LamCases_6989586621679812575Sym1 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610) arg_a3mQJ) (LamCases_6989586621679812575Sym2 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610 arg_a3mQJ) =>
                                                      LamCases_6989586621679812575Sym1 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610 a_69895866216798126116989586621679812612
type instance Apply @_ @_ (LamCases_6989586621679812575Sym1 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610) a_69895866216798126116989586621679812612 = LamCases_6989586621679812575_a3mQ8 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610 a_69895866216798126116989586621679812612
instance SuppressUnusedWarnings (LamCases_6989586621679812575Sym1 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812575Sym1KindInference ())
type family LamCases_6989586621679812575Sym2 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126096989586621679812610 a_69895866216798126116989586621679812612 where
  LamCases_6989586621679812575Sym2 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610 a_69895866216798126116989586621679812612 = LamCases_6989586621679812575_a3mQ8 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126096989586621679812610 a_69895866216798126116989586621679812612
type family LamCases_6989586621679812573_a3mQ6 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_6989586621679812614_a3mQL where
  LamCases_6989586621679812573_a3mQ6 c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 'True = Apply (Apply ShowCharSym0 '\\') (Apply (Apply (Apply ProtectEscSym0 IsDecSym0) (Apply ShowsSym0 (Apply CharToNatSym0 c_a3mQ3))) s_a3mQ4)
  LamCases_6989586621679812573_a3mQ6 c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 'False = Apply (Apply (LamCases_6989586621679812575Sym0 c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0) arg_6989586621679812463_a3mPZ) arg_6989586621679812465_a3mQ0
data LamCases_6989586621679812573Sym0 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126146989586621679812615
  where
    LamCases_6989586621679812573Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812573Sym0 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) arg_a3mQM) (LamCases_6989586621679812573Sym1 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 arg_a3mQM) =>
                                                      LamCases_6989586621679812573Sym0 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126146989586621679812615
type instance Apply @_ @_ (LamCases_6989586621679812573Sym0 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) a_69895866216798126146989586621679812615 = LamCases_6989586621679812573_a3mQ6 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126146989586621679812615
instance SuppressUnusedWarnings (LamCases_6989586621679812573Sym0 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812573Sym0KindInference ())
type family LamCases_6989586621679812573Sym1 c6989586621679812571 s6989586621679812572 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126146989586621679812615 where
  LamCases_6989586621679812573Sym1 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126146989586621679812615 = LamCases_6989586621679812573_a3mQ6 c6989586621679812571 s6989586621679812572 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126146989586621679812615
type family LamCases_6989586621679812569_a3mQ2 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_6989586621679812617_a3mQO a_6989586621679812619_a3mQQ where
  LamCases_6989586621679812569_a3mQ2 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 c_a3mQ3 s_a3mQ4 = Apply (LamCases_6989586621679812573Sym0 c_a3mQ3 s_a3mQ4 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0) (Apply (Apply (>@#@$) c_a3mQ3) '\DEL')
data LamCases_6989586621679812569Sym0 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126176989586621679812618
  where
    LamCases_6989586621679812569Sym0KindInference :: SameKind (Apply (LamCases_6989586621679812569Sym0 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) arg_a3mQR) (LamCases_6989586621679812569Sym1 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 arg_a3mQR) =>
                                                      LamCases_6989586621679812569Sym0 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618
type instance Apply @_ @_ (LamCases_6989586621679812569Sym0 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) a_69895866216798126176989586621679812618 = LamCases_6989586621679812569Sym1 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618
instance SuppressUnusedWarnings (LamCases_6989586621679812569Sym0 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812569Sym0KindInference ())
data LamCases_6989586621679812569Sym1 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126176989586621679812618 a_69895866216798126196989586621679812620
  where
    LamCases_6989586621679812569Sym1KindInference :: SameKind (Apply (LamCases_6989586621679812569Sym1 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618) arg_a3mQR) (LamCases_6989586621679812569Sym2 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618 arg_a3mQR) =>
                                                      LamCases_6989586621679812569Sym1 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618 a_69895866216798126196989586621679812620
type instance Apply @_ @_ (LamCases_6989586621679812569Sym1 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618) a_69895866216798126196989586621679812620 = LamCases_6989586621679812569_a3mQ2 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618 a_69895866216798126196989586621679812620
instance SuppressUnusedWarnings (LamCases_6989586621679812569Sym1 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679812569Sym1KindInference ())
type family LamCases_6989586621679812569Sym2 (arg_69895866216798124636989586621679812567 :: Char) (arg_69895866216798124656989586621679812568 :: Symbol) a_69895866216798126176989586621679812618 a_69895866216798126196989586621679812620 where
  LamCases_6989586621679812569Sym2 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618 a_69895866216798126196989586621679812620 = LamCases_6989586621679812569_a3mQ2 arg_69895866216798124636989586621679812567 arg_69895866216798124656989586621679812568 a_69895866216798126176989586621679812618 a_69895866216798126196989586621679812620
type AsciiTabSym0 :: [Symbol]
type family AsciiTabSym0 :: [Symbol] where
  AsciiTabSym0 = AsciiTab
type ProtectEscSym0 :: (~>) ((~>) Char Bool) ((~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol))
data ProtectEscSym0 :: (~>) ((~>) Char Bool) ((~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol))
  where
    ProtectEscSym0KindInference :: SameKind (Apply ProtectEscSym0 arg_a3mOT) (ProtectEscSym1 arg_a3mOT) =>
                                    ProtectEscSym0 a6989586621679812500
type instance Apply @((~>) Char Bool) @((~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol)) ProtectEscSym0 a6989586621679812500 = ProtectEscSym1 a6989586621679812500
instance SuppressUnusedWarnings ProtectEscSym0 where
  suppressUnusedWarnings = snd ((,) ProtectEscSym0KindInference ())
type ProtectEscSym1 :: (~>) Char Bool
                        -> (~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol)
data ProtectEscSym1 (a6989586621679812500 :: (~>) Char Bool) :: (~>) ((~>) Symbol Symbol) ((~>) Symbol Symbol)
  where
    ProtectEscSym1KindInference :: SameKind (Apply (ProtectEscSym1 a6989586621679812500) arg_a3mOT) (ProtectEscSym2 a6989586621679812500 arg_a3mOT) =>
                                    ProtectEscSym1 a6989586621679812500 a6989586621679812501
type instance Apply @((~>) Symbol Symbol) @((~>) Symbol Symbol) (ProtectEscSym1 a6989586621679812500) a6989586621679812501 = ProtectEscSym2 a6989586621679812500 a6989586621679812501
instance SuppressUnusedWarnings (ProtectEscSym1 a6989586621679812500) where
  suppressUnusedWarnings = snd ((,) ProtectEscSym1KindInference ())
type ProtectEscSym2 :: (~>) Char Bool
                        -> (~>) Symbol Symbol -> (~>) Symbol Symbol
data ProtectEscSym2 (a6989586621679812500 :: (~>) Char Bool) (a6989586621679812501 :: (~>) Symbol Symbol) :: (~>) Symbol Symbol
  where
    ProtectEscSym2KindInference :: SameKind (Apply (ProtectEscSym2 a6989586621679812500 a6989586621679812501) arg_a3mOT) (ProtectEscSym3 a6989586621679812500 a6989586621679812501 arg_a3mOT) =>
                                    ProtectEscSym2 a6989586621679812500 a6989586621679812501 a6989586621679812502
type instance Apply @Symbol @Symbol (ProtectEscSym2 a6989586621679812500 a6989586621679812501) a6989586621679812502 = ProtectEsc a6989586621679812500 a6989586621679812501 a6989586621679812502
instance SuppressUnusedWarnings (ProtectEscSym2 a6989586621679812500 a6989586621679812501) where
  suppressUnusedWarnings = snd ((,) ProtectEscSym2KindInference ())
type ProtectEscSym3 :: (~>) Char Bool
                        -> (~>) Symbol Symbol -> Symbol -> Symbol
type family ProtectEscSym3 (a6989586621679812500 :: (~>) Char Bool) (a6989586621679812501 :: (~>) Symbol Symbol) (a6989586621679812502 :: Symbol) :: Symbol where
  ProtectEscSym3 a6989586621679812500 a6989586621679812501 a6989586621679812502 = ProtectEsc a6989586621679812500 a6989586621679812501 a6989586621679812502
type IsDecSym0 :: (~>) Char Bool
data IsDecSym0 :: (~>) Char Bool
  where
    IsDecSym0KindInference :: SameKind (Apply IsDecSym0 arg_a3mPr) (IsDecSym1 arg_a3mPr) =>
                              IsDecSym0 a6989586621679812534
type instance Apply @Char @Bool IsDecSym0 a6989586621679812534 = IsDec a6989586621679812534
instance SuppressUnusedWarnings IsDecSym0 where
  suppressUnusedWarnings = snd ((,) IsDecSym0KindInference ())
type IsDecSym1 :: Char -> Bool
type family IsDecSym1 (a6989586621679812534 :: Char) :: Bool where
  IsDecSym1 a6989586621679812534 = IsDec a6989586621679812534
type ShowLitSymbolSym0 :: (~>) Symbol ((~>) Symbol Symbol)
data ShowLitSymbolSym0 :: (~>) Symbol ((~>) Symbol Symbol)
  where
    ShowLitSymbolSym0KindInference :: SameKind (Apply ShowLitSymbolSym0 arg_a3mPw) (ShowLitSymbolSym1 arg_a3mPw) =>
                                      ShowLitSymbolSym0 a6989586621679812539
type instance Apply @Symbol @((~>) Symbol Symbol) ShowLitSymbolSym0 a6989586621679812539 = ShowLitSymbolSym1 a6989586621679812539
instance SuppressUnusedWarnings ShowLitSymbolSym0 where
  suppressUnusedWarnings
    = snd ((,) ShowLitSymbolSym0KindInference ())
type ShowLitSymbolSym1 :: Symbol -> (~>) Symbol Symbol
data ShowLitSymbolSym1 (a6989586621679812539 :: Symbol) :: (~>) Symbol Symbol
  where
    ShowLitSymbolSym1KindInference :: SameKind (Apply (ShowLitSymbolSym1 a6989586621679812539) arg_a3mPw) (ShowLitSymbolSym2 a6989586621679812539 arg_a3mPw) =>
                                      ShowLitSymbolSym1 a6989586621679812539 a6989586621679812540
type instance Apply @Symbol @Symbol (ShowLitSymbolSym1 a6989586621679812539) a6989586621679812540 = ShowLitSymbol a6989586621679812539 a6989586621679812540
instance SuppressUnusedWarnings (ShowLitSymbolSym1 a6989586621679812539) where
  suppressUnusedWarnings
    = snd ((,) ShowLitSymbolSym1KindInference ())
type ShowLitSymbolSym2 :: Symbol -> Symbol -> Symbol
type family ShowLitSymbolSym2 (a6989586621679812539 :: Symbol) (a6989586621679812540 :: Symbol) :: Symbol where
  ShowLitSymbolSym2 a6989586621679812539 a6989586621679812540 = ShowLitSymbol a6989586621679812539 a6989586621679812540
type ShowLitStringSym0 :: (~>) [Char] ((~>) Symbol Symbol)
data ShowLitStringSym0 :: (~>) [Char] ((~>) Symbol Symbol)
  where
    ShowLitStringSym0KindInference :: SameKind (Apply ShowLitStringSym0 arg_a3mPL) (ShowLitStringSym1 arg_a3mPL) =>
                                      ShowLitStringSym0 a6989586621679812554
type instance Apply @[Char] @((~>) Symbol Symbol) ShowLitStringSym0 a6989586621679812554 = ShowLitStringSym1 a6989586621679812554
instance SuppressUnusedWarnings ShowLitStringSym0 where
  suppressUnusedWarnings
    = snd ((,) ShowLitStringSym0KindInference ())
type ShowLitStringSym1 :: [Char] -> (~>) Symbol Symbol
data ShowLitStringSym1 (a6989586621679812554 :: [Char]) :: (~>) Symbol Symbol
  where
    ShowLitStringSym1KindInference :: SameKind (Apply (ShowLitStringSym1 a6989586621679812554) arg_a3mPL) (ShowLitStringSym2 a6989586621679812554 arg_a3mPL) =>
                                      ShowLitStringSym1 a6989586621679812554 a6989586621679812555
type instance Apply @Symbol @Symbol (ShowLitStringSym1 a6989586621679812554) a6989586621679812555 = ShowLitString a6989586621679812554 a6989586621679812555
instance SuppressUnusedWarnings (ShowLitStringSym1 a6989586621679812554) where
  suppressUnusedWarnings
    = snd ((,) ShowLitStringSym1KindInference ())
type ShowLitStringSym2 :: [Char] -> Symbol -> Symbol
type family ShowLitStringSym2 (a6989586621679812554 :: [Char]) (a6989586621679812555 :: Symbol) :: Symbol where
  ShowLitStringSym2 a6989586621679812554 a6989586621679812555 = ShowLitString a6989586621679812554 a6989586621679812555
type ShowLitCharSym0 :: (~>) Char ((~>) Symbol Symbol)
data ShowLitCharSym0 :: (~>) Char ((~>) Symbol Symbol)
  where
    ShowLitCharSym0KindInference :: SameKind (Apply ShowLitCharSym0 arg_a3mPW) (ShowLitCharSym1 arg_a3mPW) =>
                                    ShowLitCharSym0 a6989586621679812565
type instance Apply @Char @((~>) Symbol Symbol) ShowLitCharSym0 a6989586621679812565 = ShowLitCharSym1 a6989586621679812565
instance SuppressUnusedWarnings ShowLitCharSym0 where
  suppressUnusedWarnings = snd ((,) ShowLitCharSym0KindInference ())
type ShowLitCharSym1 :: Char -> (~>) Symbol Symbol
data ShowLitCharSym1 (a6989586621679812565 :: Char) :: (~>) Symbol Symbol
  where
    ShowLitCharSym1KindInference :: SameKind (Apply (ShowLitCharSym1 a6989586621679812565) arg_a3mPW) (ShowLitCharSym2 a6989586621679812565 arg_a3mPW) =>
                                    ShowLitCharSym1 a6989586621679812565 a6989586621679812566
type instance Apply @Symbol @Symbol (ShowLitCharSym1 a6989586621679812565) a6989586621679812566 = ShowLitChar a6989586621679812565 a6989586621679812566
instance SuppressUnusedWarnings (ShowLitCharSym1 a6989586621679812565) where
  suppressUnusedWarnings = snd ((,) ShowLitCharSym1KindInference ())
type ShowLitCharSym2 :: Char -> Symbol -> Symbol
type family ShowLitCharSym2 (a6989586621679812565 :: Char) (a6989586621679812566 :: Symbol) :: Symbol where
  ShowLitCharSym2 a6989586621679812565 a6989586621679812566 = ShowLitChar a6989586621679812565 a6989586621679812566
type ShowSymbolSym0 :: (~>) Symbol ((~>) Symbol Symbol)
data ShowSymbolSym0 :: (~>) Symbol ((~>) Symbol Symbol)
  where
    ShowSymbolSym0KindInference :: SameKind (Apply ShowSymbolSym0 arg_a3mQW) (ShowSymbolSym1 arg_a3mQW) =>
                                    ShowSymbolSym0 a6989586621679812627
type instance Apply @Symbol @((~>) Symbol Symbol) ShowSymbolSym0 a6989586621679812627 = ShowSymbolSym1 a6989586621679812627
instance SuppressUnusedWarnings ShowSymbolSym0 where
  suppressUnusedWarnings = snd ((,) ShowSymbolSym0KindInference ())
type ShowSymbolSym1 :: Symbol -> (~>) Symbol Symbol
data ShowSymbolSym1 (a6989586621679812627 :: Symbol) :: (~>) Symbol Symbol
  where
    ShowSymbolSym1KindInference :: SameKind (Apply (ShowSymbolSym1 a6989586621679812627) arg_a3mQW) (ShowSymbolSym2 a6989586621679812627 arg_a3mQW) =>
                                    ShowSymbolSym1 a6989586621679812627 a6989586621679812628
type instance Apply @Symbol @Symbol (ShowSymbolSym1 a6989586621679812627) a6989586621679812628 = ShowSymbol a6989586621679812627 a6989586621679812628
instance SuppressUnusedWarnings (ShowSymbolSym1 a6989586621679812627) where
  suppressUnusedWarnings = snd ((,) ShowSymbolSym1KindInference ())
type ShowSymbolSym2 :: Symbol -> Symbol -> Symbol
type family ShowSymbolSym2 (a6989586621679812627 :: Symbol) (a6989586621679812628 :: Symbol) :: Symbol where
  ShowSymbolSym2 a6989586621679812627 a6989586621679812628 = ShowSymbol a6989586621679812627 a6989586621679812628
type ShowCharListSym0 :: (~>) [Char] ((~>) Symbol Symbol)
data ShowCharListSym0 :: (~>) [Char] ((~>) Symbol Symbol)
  where
    ShowCharListSym0KindInference :: SameKind (Apply ShowCharListSym0 arg_a3mR5) (ShowCharListSym1 arg_a3mR5) =>
                                      ShowCharListSym0 a6989586621679812636
type instance Apply @[Char] @((~>) Symbol Symbol) ShowCharListSym0 a6989586621679812636 = ShowCharListSym1 a6989586621679812636
instance SuppressUnusedWarnings ShowCharListSym0 where
  suppressUnusedWarnings = snd ((,) ShowCharListSym0KindInference ())
type ShowCharListSym1 :: [Char] -> (~>) Symbol Symbol
data ShowCharListSym1 (a6989586621679812636 :: [Char]) :: (~>) Symbol Symbol
  where
    ShowCharListSym1KindInference :: SameKind (Apply (ShowCharListSym1 a6989586621679812636) arg_a3mR5) (ShowCharListSym2 a6989586621679812636 arg_a3mR5) =>
                                      ShowCharListSym1 a6989586621679812636 a6989586621679812637
type instance Apply @Symbol @Symbol (ShowCharListSym1 a6989586621679812636) a6989586621679812637 = ShowCharList a6989586621679812636 a6989586621679812637
instance SuppressUnusedWarnings (ShowCharListSym1 a6989586621679812636) where
  suppressUnusedWarnings = snd ((,) ShowCharListSym1KindInference ())
type ShowCharListSym2 :: [Char] -> Symbol -> Symbol
type family ShowCharListSym2 (a6989586621679812636 :: [Char]) (a6989586621679812637 :: Symbol) :: Symbol where
  ShowCharListSym2 a6989586621679812636 a6989586621679812637 = ShowCharList a6989586621679812636 a6989586621679812637
type ShowsCharPrecSym0 :: (~>) Natural ((~>) Char ((~>) Symbol Symbol))
data ShowsCharPrecSym0 :: (~>) Natural ((~>) Char ((~>) Symbol Symbol))
  where
    ShowsCharPrecSym0KindInference :: SameKind (Apply ShowsCharPrecSym0 arg_a3mRh) (ShowsCharPrecSym1 arg_a3mRh) =>
                                      ShowsCharPrecSym0 a6989586621679812648
type instance Apply @Natural @((~>) Char ((~>) Symbol Symbol)) ShowsCharPrecSym0 a6989586621679812648 = ShowsCharPrecSym1 a6989586621679812648
instance SuppressUnusedWarnings ShowsCharPrecSym0 where
  suppressUnusedWarnings
    = snd ((,) ShowsCharPrecSym0KindInference ())
type ShowsCharPrecSym1 :: Natural -> (~>) Char ((~>) Symbol Symbol)
data ShowsCharPrecSym1 (a6989586621679812648 :: Natural) :: (~>) Char ((~>) Symbol Symbol)
  where
    ShowsCharPrecSym1KindInference :: SameKind (Apply (ShowsCharPrecSym1 a6989586621679812648) arg_a3mRh) (ShowsCharPrecSym2 a6989586621679812648 arg_a3mRh) =>
                                      ShowsCharPrecSym1 a6989586621679812648 a6989586621679812649
type instance Apply @Char @((~>) Symbol Symbol) (ShowsCharPrecSym1 a6989586621679812648) a6989586621679812649 = ShowsCharPrecSym2 a6989586621679812648 a6989586621679812649
instance SuppressUnusedWarnings (ShowsCharPrecSym1 a6989586621679812648) where
  suppressUnusedWarnings
    = snd ((,) ShowsCharPrecSym1KindInference ())
type ShowsCharPrecSym2 :: Natural -> Char -> (~>) Symbol Symbol
data ShowsCharPrecSym2 (a6989586621679812648 :: Natural) (a6989586621679812649 :: Char) :: (~>) Symbol Symbol
  where
    ShowsCharPrecSym2KindInference :: SameKind (Apply (ShowsCharPrecSym2 a6989586621679812648 a6989586621679812649) arg_a3mRh) (ShowsCharPrecSym3 a6989586621679812648 a6989586621679812649 arg_a3mRh) =>
                                      ShowsCharPrecSym2 a6989586621679812648 a6989586621679812649 a6989586621679812650
type instance Apply @Symbol @Symbol (ShowsCharPrecSym2 a6989586621679812648 a6989586621679812649) a6989586621679812650 = ShowsCharPrec a6989586621679812648 a6989586621679812649 a6989586621679812650
instance SuppressUnusedWarnings (ShowsCharPrecSym2 a6989586621679812648 a6989586621679812649) where
  suppressUnusedWarnings
    = snd ((,) ShowsCharPrecSym2KindInference ())
type ShowsCharPrecSym3 :: Natural -> Char -> Symbol -> Symbol
type family ShowsCharPrecSym3 (a6989586621679812648 :: Natural) (a6989586621679812649 :: Char) (a6989586621679812650 :: Symbol) :: Symbol where
  ShowsCharPrecSym3 a6989586621679812648 a6989586621679812649 a6989586621679812650 = ShowsCharPrec a6989586621679812648 a6989586621679812649 a6989586621679812650
type AsciiTab :: [Symbol]
type family AsciiTab :: [Symbol] where
  AsciiTab = Apply (Apply (:@#@$) "NUL") (Apply (Apply (:@#@$) "SOH") (Apply (Apply (:@#@$) "STX") (Apply (Apply (:@#@$) "ETX") (Apply (Apply (:@#@$) "EOT") (Apply (Apply (:@#@$) "ENQ") (Apply (Apply (:@#@$) "ACK") (Apply (Apply (:@#@$) "BEL") (Apply (Apply (:@#@$) "BS") (Apply (Apply (:@#@$) "HT") (Apply (Apply (:@#@$) "LF") (Apply (Apply (:@#@$) "VT") (Apply (Apply (:@#@$) "FF") (Apply (Apply (:@#@$) "CR") (Apply (Apply (:@#@$) "SO") (Apply (Apply (:@#@$) "SI") (Apply (Apply (:@#@$) "DLE") (Apply (Apply (:@#@$) "DC1") (Apply (Apply (:@#@$) "DC2") (Apply (Apply (:@#@$) "DC3") (Apply (Apply (:@#@$) "DC4") (Apply (Apply (:@#@$) "NAK") (Apply (Apply (:@#@$) "SYN") (Apply (Apply (:@#@$) "ETB") (Apply (Apply (:@#@$) "CAN") (Apply (Apply (:@#@$) "EM") (Apply (Apply (:@#@$) "SUB") (Apply (Apply (:@#@$) "ESC") (Apply (Apply (:@#@$) "FS") (Apply (Apply (:@#@$) "GS") (Apply (Apply (:@#@$) "RS") (Apply (Apply (:@#@$) "US") (Apply (Apply (:@#@$) "SP") NilSym0))))))))))))))))))))))))))))))))
type ProtectEsc :: (~>) Char Bool
                    -> (~>) Symbol Symbol -> Symbol -> Symbol
type family ProtectEsc (a_a3mOQ :: (~>) Char Bool) (a_a3mOR :: (~>) Symbol Symbol) (a_a3mOS :: Symbol) :: Symbol where
  ProtectEsc p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ = Apply (Apply (Apply (.@#@$) f_a3mOY) (Let6989586621679812506ContSym0 p_a3mOX f_a3mOY a_6989586621679812494_a3mOZ)) a_6989586621679812494_a3mOZ
type IsDec :: Char -> Bool
type family IsDec (a_a3mPq :: Char) :: Bool where
  IsDec c_a3mPt = Apply (Apply (&&@#@$) (Apply (Apply (>=@#@$) c_a3mPt) '0')) (Apply (Apply (<=@#@$) c_a3mPt) '9')
type ShowLitSymbol :: Symbol -> Symbol -> Symbol
type family ShowLitSymbol (a_a3mPu :: Symbol) (a_a3mPv :: Symbol) :: Symbol where
  ShowLitSymbol sym_a3mPz s_a3mPA = Apply (LamCases_6989586621679812543Sym0 sym_a3mPz s_a3mPA) (Apply UnconsSymbolSym0 sym_a3mPz)
type ShowLitString :: [Char] -> Symbol -> Symbol
type family ShowLitString (a_a3mPJ :: [Char]) (a_a3mPK :: Symbol) :: Symbol where
  ShowLitString '[] s_a3mPO = s_a3mPO
  ShowLitString ('(:) '"' cs_a3mPP) s_a3mPQ = Apply (Apply ShowStringSym0 "\\\"") (Apply (Apply ShowLitStringSym0 cs_a3mPP) s_a3mPQ)
  ShowLitString ('(:) c_a3mPR cs_a3mPS) s_a3mPT = Apply (Apply ShowLitCharSym0 c_a3mPR) (Apply (Apply ShowLitStringSym0 cs_a3mPS) s_a3mPT)
type ShowLitChar :: Char -> Symbol -> Symbol
type family ShowLitChar (a_a3mPU :: Char) (a_a3mPV :: Symbol) :: Symbol where
  ShowLitChar arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0 = Apply (Apply (LamCases_6989586621679812569Sym0 arg_6989586621679812463_a3mPZ arg_6989586621679812465_a3mQ0) arg_6989586621679812463_a3mPZ) arg_6989586621679812465_a3mQ0
type ShowSymbol :: Symbol -> Symbol -> Symbol
type family ShowSymbol (a_a3mQU :: Symbol) (a_a3mQV :: Symbol) :: Symbol where
  ShowSymbol sym_a3mQZ a_6989586621679812622_a3mR0 = Apply (Apply (Apply (.@#@$) (Apply ShowCharSym0 '"')) (Apply (Apply (.@#@$) (Apply ShowLitSymbolSym0 sym_a3mQZ)) (Apply ShowCharSym0 '"'))) a_6989586621679812622_a3mR0
type ShowCharList :: [Char] -> Symbol -> Symbol
type family ShowCharList (a_a3mR3 :: [Char]) (a_a3mR4 :: Symbol) :: Symbol where
  ShowCharList cs_a3mR8 a_6989586621679812631_a3mR9 = Apply (Apply (Apply (.@#@$) (Apply ShowCharSym0 '"')) (Apply (Apply (.@#@$) (Apply ShowLitStringSym0 cs_a3mR8)) (Apply ShowCharSym0 '"'))) a_6989586621679812631_a3mR9
type ShowsCharPrec :: Natural -> Char -> Symbol -> Symbol
type family ShowsCharPrec (a_a3mRe :: Natural) (a_a3mRf :: Char) (a_a3mRg :: Symbol) :: Symbol where
  ShowsCharPrec _ '\'' a_6989586621679812640_a3mRl = Apply (Apply ShowStringSym0 "'\\''") a_6989586621679812640_a3mRl
  ShowsCharPrec _ c_a3mRm a_6989586621679812642_a3mRn = Apply (Apply (Apply (.@#@$) (Apply ShowCharSym0 '\'')) (Apply (Apply (.@#@$) (Apply ShowLitCharSym0 c_a3mRm)) (Apply ShowCharSym0 '\''))) a_6989586621679812642_a3mRn

instance PShow Char where
  type ShowsPrec p c x = ShowsCharPrec p c x
  type ShowList cs x = ShowCharList cs x

instance SShow Char where
  sShowsPrec sp sc sx =
    let p  = fromSing sp
        c  = fromSing sc
        x  = fromSing sx
    in withSomeSSymbol (P.showsPrec (fromIntegral p) c (T.unpack x)) unsafeCoerce

  sShowList scs sx =
    let cs = fromSing scs
        x  = fromSing sx
    in withSomeSSymbol (P.showList cs (T.unpack x)) unsafeCoerce

instance PShow Symbol where
  type ShowsPrec _ s x = ShowSymbol s x

instance SShow Symbol where
  sShowsPrec _ ss sx =
    let s  = fromSing ss
        x  = fromSing sx
    in withSomeSSymbol (P.show s ++ T.unpack x) unsafeCoerce

-- | 'P.show', but with an extra underscore so that its promoted counterpart
-- ('Show_') will not clash with the 'Show' class.
show_ :: P.Show a => a -> String
show_ = P.show

type ShowsPrec_6989586621679819840 :: Natural
                                          -> () -> Symbol -> Symbol
type family ShowsPrec_6989586621679819840 (a_a3oJm :: Natural) (a_a3oJn :: ()) (a_a3oJo :: Symbol) :: Symbol where
  ShowsPrec_6989586621679819840 _ '() a_6989586621679819842_a3oJt = Apply (Apply ShowStringSym0 "()") a_6989586621679819842_a3oJt
instance PShow () where
  type ShowsPrec a_a3oJf a_a3oJg a_a3oJh = ShowsPrec_6989586621679819840 a_a3oJf a_a3oJg a_a3oJh
instance SShow () where
  sShowsPrec
    _
    STuple0
    (sA_6989586621679819842 :: Sing a_6989586621679819842_a3oJt)
    = applySing
        (applySing
            (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "()"))
        sA_6989586621679819842
type ShowsPrec_6989586621679819869 :: forall a_11. Natural
                                                    -> Maybe a_11 -> Symbol -> Symbol
type family ShowsPrec_6989586621679819869 @a_11 (a_a3oJR :: Natural) (a_a3oJS :: Maybe a_11) (a_a3oJT :: Symbol) :: Symbol where
  ShowsPrec_6989586621679819869 @a_11 (_ :: Natural) ('Nothing :: Maybe a_11) (a_6989586621679819871_a3oJY :: Symbol) = Apply (Apply ShowStringSym0 "Nothing") a_6989586621679819871_a3oJY
  ShowsPrec_6989586621679819869 @a_11 (p_6989586621679819854_a3oJZ :: Natural) ('Just arg_6989586621679819856_a3oK0 :: Maybe a_11) (a_6989586621679819873_a3oK1 :: Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679819854_a3oJZ) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Just ")) (Apply (Apply ShowsPrecSym0 (FromInteger 11)) arg_6989586621679819856_a3oK0))) a_6989586621679819873_a3oK1
instance PShow (Maybe a_11) where
  type ShowsPrec a_a3oJI a_a3oJJ a_a3oJK = ShowsPrec_6989586621679819869 a_a3oJI a_a3oJJ a_a3oJK
instance SShow a_11 => SShow (Maybe a_11) where
  sShowsPrec
    _
    SNothing
    (sA_6989586621679819871 :: Sing a_6989586621679819871_a3oJY)
    = applySing
        (applySing
            (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Nothing"))
        sA_6989586621679819871
  sShowsPrec
    (sP_6989586621679819854 :: Sing p_6989586621679819854_a3oJZ)
    (SJust (sArg_6989586621679819856 :: Sing arg_6989586621679819856_a3oK0))
    (sA_6989586621679819873 :: Sing a_6989586621679819873_a3oK1)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679819854)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Just ")))
              (applySing
                  (applySing
                    (singFun3 @ShowsPrecSym0 sShowsPrec)
                    (sFromInteger (sing :: Sing 11)))
                  sArg_6989586621679819856)))
        sA_6989586621679819873
type ShowsPrec_6989586621679819915 :: forall a_a8ep b_a8eq. Natural
                                                            -> Either a_a8ep b_a8eq
                                                                -> Symbol -> Symbol
type family ShowsPrec_6989586621679819915 @a_a8ep @b_a8eq (a_a3oKB :: Natural) (a_a3oKC :: Either a_a8ep b_a8eq) (a_a3oKD :: Symbol) :: Symbol where
  ShowsPrec_6989586621679819915 @a_a8ep @b_a8eq (p_6989586621679819890_a3oKI :: Natural) ('Left arg_6989586621679819892_a3oKJ :: Either a_a8ep b_a8eq) (a_6989586621679819917_a3oKK :: Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679819890_a3oKI) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Left ")) (Apply (Apply ShowsPrecSym0 (FromInteger 11)) arg_6989586621679819892_a3oKJ))) a_6989586621679819917_a3oKK
  ShowsPrec_6989586621679819915 @a_a8ep @b_a8eq (p_6989586621679819890_a3oKL :: Natural) ('Right arg_6989586621679819894_a3oKM :: Either a_a8ep b_a8eq) (a_6989586621679819919_a3oKN :: Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679819890_a3oKL) (FromInteger 10))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Right ")) (Apply (Apply ShowsPrecSym0 (FromInteger 11)) arg_6989586621679819894_a3oKM))) a_6989586621679819919_a3oKN
instance PShow (Either a_a8ep b_a8eq) where
  type ShowsPrec a_a3oKs a_a3oKt a_a3oKu = ShowsPrec_6989586621679819915 a_a3oKs a_a3oKt a_a3oKu
instance (SShow a_a8ep, SShow b_a8eq) =>
          SShow (Either a_a8ep b_a8eq) where
  sShowsPrec
    (sP_6989586621679819890 :: Sing p_6989586621679819890_a3oKI)
    (SLeft (sArg_6989586621679819892 :: Sing arg_6989586621679819892_a3oKJ))
    (sA_6989586621679819917 :: Sing a_6989586621679819917_a3oKK)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679819890)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Left ")))
              (applySing
                  (applySing
                    (singFun3 @ShowsPrecSym0 sShowsPrec)
                    (sFromInteger (sing :: Sing 11)))
                  sArg_6989586621679819892)))
        sA_6989586621679819917
  sShowsPrec
    (sP_6989586621679819890 :: Sing p_6989586621679819890_a3oKL)
    (SRight (sArg_6989586621679819894 :: Sing arg_6989586621679819894_a3oKM))
    (sA_6989586621679819919 :: Sing a_6989586621679819919_a3oKN)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679819890)
                  (sFromInteger (sing :: Sing 10))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Right ")))
              (applySing
                  (applySing
                    (singFun3 @ShowsPrecSym0 sShowsPrec)
                    (sFromInteger (sing :: Sing 11)))
                  sArg_6989586621679819894)))
        sA_6989586621679819919
type ShowsPrec_6989586621679819946 :: forall a_a8fb. Natural
                                                      -> NonEmpty a_a8fb -> Symbol -> Symbol
type family ShowsPrec_6989586621679819946 @a_a8fb (a_a3oL4 :: Natural) (a_a3oL5 :: NonEmpty a_a8fb) (a_a3oL6 :: Symbol) :: Symbol where
  ShowsPrec_6989586621679819946 @a_a8fb (p_6989586621679819935_a3oLb :: Natural) ('(GHC.Base.:|) argL_6989586621679819937_a3oLc argR_6989586621679819939_a3oLd :: NonEmpty a_a8fb) (a_6989586621679819948_a3oLe :: Symbol) = Apply (Apply (Apply ShowParenSym0 (Apply (Apply (>@#@$) p_6989586621679819935_a3oLb) (FromInteger 5))) (Apply (Apply (.@#@$) (Apply (Apply ShowsPrecSym0 (FromInteger 6)) argL_6989586621679819937_a3oLc)) (Apply (Apply (.@#@$) (Apply ShowStringSym0 " :| ")) (Apply (Apply ShowsPrecSym0 (FromInteger 6)) argR_6989586621679819939_a3oLd)))) a_6989586621679819948_a3oLe
instance PShow (NonEmpty a_a8fb) where
  type ShowsPrec a_a3oKX a_a3oKY a_a3oKZ = ShowsPrec_6989586621679819946 a_a3oKX a_a3oKY a_a3oKZ
instance (SShow a_a8fb, SShow [a_a8fb]) =>
          SShow (NonEmpty a_a8fb) where
  sShowsPrec
    (sP_6989586621679819935 :: Sing p_6989586621679819935_a3oLb)
    ((:%|) (sArgL_6989586621679819937 :: Sing argL_6989586621679819937_a3oLc)
            (sArgR_6989586621679819939 :: Sing argR_6989586621679819939_a3oLd))
    (sA_6989586621679819948 :: Sing a_6989586621679819948_a3oLe)
    = applySing
        (applySing
            (applySing
              (singFun3 @ShowParenSym0 sShowParen)
              (applySing
                  (applySing (singFun2 @(>@#@$) (%>)) sP_6989586621679819935)
                  (sFromInteger (sing :: Sing 5))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (applySing
                        (singFun3 @ShowsPrecSym0 sShowsPrec)
                        (sFromInteger (sing :: Sing 6)))
                    sArgL_6989586621679819937))
              (applySing
                  (applySing
                    (singFun3 @(.@#@$) (%.))
                    (applySing
                        (singFun2 @ShowStringSym0 sShowString) (sing :: Sing " :| ")))
                  (applySing
                    (applySing
                        (singFun3 @ShowsPrecSym0 sShowsPrec)
                        (sFromInteger (sing :: Sing 6)))
                    sArgR_6989586621679819939))))
        sA_6989586621679819948
type ShowsPrec_6989586621679819966 :: Natural
                                      -> Bool -> Symbol -> Symbol
type family ShowsPrec_6989586621679819966 (a_a3oLq :: Natural) (a_a3oLr :: Bool) (a_a3oLs :: Symbol) :: Symbol where
  ShowsPrec_6989586621679819966 _ 'False a_6989586621679819968_a3oLx = Apply (Apply ShowStringSym0 "False") a_6989586621679819968_a3oLx
  ShowsPrec_6989586621679819966 _ 'True a_6989586621679819970_a3oLy = Apply (Apply ShowStringSym0 "True") a_6989586621679819970_a3oLy
instance PShow Bool where
  type ShowsPrec a_a3oLh a_a3oLi a_a3oLj = ShowsPrec_6989586621679819966 a_a3oLh a_a3oLi a_a3oLj
instance SShow Bool where
  sShowsPrec
    _
    SFalse
    (sA_6989586621679819968 :: Sing a_6989586621679819968_a3oLx)
    = applySing
        (applySing
            (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "False"))
        sA_6989586621679819968
  sShowsPrec
    _
    STrue
    (sA_6989586621679819970 :: Sing a_6989586621679819970_a3oLy)
    = applySing
        (applySing
            (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "True"))
        sA_6989586621679819970
type ShowsPrec_6989586621679819986 :: Natural
                                      -> Ordering -> Symbol -> Symbol
type family ShowsPrec_6989586621679819986 (a_a3oLM :: Natural) (a_a3oLN :: Ordering) (a_a3oLO :: Symbol) :: Symbol where
  ShowsPrec_6989586621679819986 _ 'LT a_6989586621679819988_a3oLT = Apply (Apply ShowStringSym0 "LT") a_6989586621679819988_a3oLT
  ShowsPrec_6989586621679819986 _ 'EQ a_6989586621679819990_a3oLU = Apply (Apply ShowStringSym0 "EQ") a_6989586621679819990_a3oLU
  ShowsPrec_6989586621679819986 _ 'GT a_6989586621679819992_a3oLV = Apply (Apply ShowStringSym0 "GT") a_6989586621679819992_a3oLV
instance PShow Ordering where
  type ShowsPrec a_a3oLB a_a3oLC a_a3oLD = ShowsPrec_6989586621679819986 a_a3oLB a_a3oLC a_a3oLD
instance SShow Ordering where
  sShowsPrec
    _
    SLT
    (sA_6989586621679819988 :: Sing a_6989586621679819988_a3oLT)
    = applySing
        (applySing
            (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "LT"))
        sA_6989586621679819988
  sShowsPrec
    _
    SEQ
    (sA_6989586621679819990 :: Sing a_6989586621679819990_a3oLU)
    = applySing
        (applySing
            (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "EQ"))
        sA_6989586621679819990
  sShowsPrec
    _
    SGT
    (sA_6989586621679819992 :: Sing a_6989586621679819992_a3oLV)
    = applySing
        (applySing
            (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "GT"))
        sA_6989586621679819992
type family LamCases_6989586621679820024_a3oMh (v_69895866216798200066989586621679820022 :: Void) (a_69895866216798200136989586621679820023 :: Symbol) a_6989586621679820026_a3oMj where
data LamCases_6989586621679820024Sym0 (v_69895866216798200066989586621679820022 :: Void) (a_69895866216798200136989586621679820023 :: Symbol) a_69895866216798200266989586621679820027
  where
    LamCases_6989586621679820024Sym0KindInference :: SameKind (Apply (LamCases_6989586621679820024Sym0 v_69895866216798200066989586621679820022 a_69895866216798200136989586621679820023) arg_a3oMk) (LamCases_6989586621679820024Sym1 v_69895866216798200066989586621679820022 a_69895866216798200136989586621679820023 arg_a3oMk) =>
                                                      LamCases_6989586621679820024Sym0 v_69895866216798200066989586621679820022 a_69895866216798200136989586621679820023 a_69895866216798200266989586621679820027
type instance Apply @_ @_ (LamCases_6989586621679820024Sym0 v_69895866216798200066989586621679820022 a_69895866216798200136989586621679820023) a_69895866216798200266989586621679820027 = LamCases_6989586621679820024_a3oMh v_69895866216798200066989586621679820022 a_69895866216798200136989586621679820023 a_69895866216798200266989586621679820027
instance SuppressUnusedWarnings (LamCases_6989586621679820024Sym0 v_69895866216798200066989586621679820022 a_69895866216798200136989586621679820023) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679820024Sym0KindInference ())
type family LamCases_6989586621679820024Sym1 (v_69895866216798200066989586621679820022 :: Void) (a_69895866216798200136989586621679820023 :: Symbol) a_69895866216798200266989586621679820027 where
  LamCases_6989586621679820024Sym1 v_69895866216798200066989586621679820022 a_69895866216798200136989586621679820023 a_69895866216798200266989586621679820027 = LamCases_6989586621679820024_a3oMh v_69895866216798200066989586621679820022 a_69895866216798200136989586621679820023 a_69895866216798200266989586621679820027
type ShowsPrec_6989586621679820011 :: Natural
                                      -> Void -> Symbol -> Symbol
type family ShowsPrec_6989586621679820011 (a_a3oM7 :: Natural) (a_a3oM8 :: Void) (a_a3oM9 :: Symbol) :: Symbol where
  ShowsPrec_6989586621679820011 _ v_6989586621679820006_a3oMe a_6989586621679820013_a3oMf = Apply (Apply (LamCases_6989586621679820024Sym0 v_6989586621679820006_a3oMe a_6989586621679820013_a3oMf) v_6989586621679820006_a3oMe) a_6989586621679820013_a3oMf
instance PShow Void where
  type ShowsPrec a_a3oM0 a_a3oM1 a_a3oM2 = ShowsPrec_6989586621679820011 a_a3oM0 a_a3oM1 a_a3oM2
instance SShow Void where
  sShowsPrec
    _
    (sV_6989586621679820006 :: Sing v_6989586621679820006_a3oMe)
    (sA_6989586621679820013 :: Sing a_6989586621679820013_a3oMf)
    = applySing
        (applySing
            (singFun1
              @(LamCases_6989586621679820024Sym0 v_6989586621679820006_a3oMe a_6989586621679820013_a3oMf)
              (\case))
            sV_6989586621679820006)
        sA_6989586621679820013

