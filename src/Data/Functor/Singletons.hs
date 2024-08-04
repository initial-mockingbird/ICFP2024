{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoNamedWildCards #-}

{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
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
-- Module      :  Data.Functor.Singletons
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines the promoted and singled versions of the 'Functor' type class.
--
----------------------------------------------------------------------------

module Data.Functor.Singletons (
  PFunctor(..), SFunctor(..),
  type ($>),  (%$>),
  type (<$>), (%<$>),
  type (<&>), (%<&>),
  Void, sVoid,

  -- * Defunctionalization symbols
  FmapSym0, FmapSym1, FmapSym2,
  type (<$@#@$),  type (<$@#@$$),  type (<$@#@$$$),
  type ($>@#@$),  type ($>@#@$$),  type ($>@#@$$$),
  type (<$>@#@$), type (<$>@#@$$), type (<$>@#@$$$),
  type (<&>@#@$), type (<&>@#@$$), type (<&>@#@$$$),
  VoidSym0, VoidSym1
  ) where

import Control.Monad.Singletons.Internal
import Data.Ord (Down(..))
import Data.Ord.Singletons
import Data.Singletons.Base.Instances
import Data.Singletons.TH hiding (Void)
import GHC.Base.Singletons
import Data.Kind (Type)

type VoidSym0 :: (~>) (f_a1vEy a_a1vEz) (f_a1vEy ())
data VoidSym0 :: (~>) (f_a1vEy a_a1vEz) (f_a1vEy ())
  where
    VoidSym0KindInference :: SameKind (Apply VoidSym0 arg_a1vFr) (VoidSym1 arg_a1vFr) =>
                              VoidSym0 a6989586621679369854
type instance Apply @(f_a1vEy a_a1vEz) @(f_a1vEy ()) VoidSym0 a6989586621679369854 = Void a6989586621679369854
instance SuppressUnusedWarnings VoidSym0 where
  suppressUnusedWarnings = snd ((,) VoidSym0KindInference ())
type VoidSym1 :: f_a1vEy a_a1vEz -> f_a1vEy ()
type family VoidSym1 @f_a1vEy @a_a1vEz (a6989586621679369854 :: f_a1vEy a_a1vEz) :: f_a1vEy () where
  VoidSym1 a6989586621679369854 = Void a6989586621679369854
type ($>@#@$) :: (~>) (f_a1vEA a_a1vEB) ((~>) b_a1vEC (f_a1vEA b_a1vEC))
data ($>@#@$) :: (~>) (f_a1vEA a_a1vEB) ((~>) b_a1vEC (f_a1vEA b_a1vEC))
  where
    (:$>@#@$###) :: SameKind (Apply ($>@#@$) arg_a1vFA) (($>@#@$$) arg_a1vFA) =>
                    ($>@#@$) a6989586621679369863
type instance Apply @(f_a1vEA a_a1vEB) @((~>) b_a1vEC (f_a1vEA b_a1vEC)) ($>@#@$) a6989586621679369863 = ($>@#@$$) a6989586621679369863
instance SuppressUnusedWarnings ($>@#@$) where
  suppressUnusedWarnings = snd ((,) (:$>@#@$###) ())
infixl 4 $>@#@$
type ($>@#@$$) :: f_a1vEA a_a1vEB -> (~>) b_a1vEC (f_a1vEA b_a1vEC)
data ($>@#@$$) (a6989586621679369863 :: f_a1vEA a_a1vEB) :: (~>) b_a1vEC (f_a1vEA b_a1vEC)
  where
    (:$>@#@$$###) :: SameKind (Apply (($>@#@$$) a6989586621679369863) arg_a1vFA) (($>@#@$$$) a6989586621679369863 arg_a1vFA) =>
                      ($>@#@$$) a6989586621679369863 a6989586621679369864
type instance Apply @b_a1vEC @(f_a1vEA b_a1vEC) (($>@#@$$) a6989586621679369863) a6989586621679369864 = ($>) a6989586621679369863 a6989586621679369864
instance SuppressUnusedWarnings (($>@#@$$) a6989586621679369863) where
  suppressUnusedWarnings = snd ((,) (:$>@#@$$###) ())
infixl 4 $>@#@$$
type ($>@#@$$$) :: f_a1vEA a_a1vEB -> b_a1vEC -> f_a1vEA b_a1vEC
type family ($>@#@$$$) @f_a1vEA @a_a1vEB @b_a1vEC (a6989586621679369863 :: f_a1vEA a_a1vEB) (a6989586621679369864 :: b_a1vEC) :: f_a1vEA b_a1vEC where
  ($>@#@$$$) a6989586621679369863 a6989586621679369864 = ($>) a6989586621679369863 a6989586621679369864
infixl 4 $>@#@$$$
type (<&>@#@$) :: (~>) (f_a1vED a_a1vEE) ((~>) ((~>) a_a1vEE b_a1vEF) (f_a1vED b_a1vEF))
data (<&>@#@$) :: (~>) (f_a1vED a_a1vEE) ((~>) ((~>) a_a1vEE b_a1vEF) (f_a1vED b_a1vEF))
  where
    (:<&>@#@$###) :: SameKind (Apply (<&>@#@$) arg_a1vFH) ((<&>@#@$$) arg_a1vFH) =>
                      (<&>@#@$) a6989586621679369870
type instance Apply @(f_a1vED a_a1vEE) @((~>) ((~>) a_a1vEE b_a1vEF) (f_a1vED b_a1vEF)) (<&>@#@$) a6989586621679369870 = (<&>@#@$$) a6989586621679369870
instance SuppressUnusedWarnings (<&>@#@$) where
  suppressUnusedWarnings = snd ((,) (:<&>@#@$###) ())
infixl 1 <&>@#@$
type (<&>@#@$$) :: f_a1vED a_a1vEE
                    -> (~>) ((~>) a_a1vEE b_a1vEF) (f_a1vED b_a1vEF)
data (<&>@#@$$) (a6989586621679369870 :: f_a1vED a_a1vEE) :: (~>) ((~>) a_a1vEE b_a1vEF) (f_a1vED b_a1vEF)
  where
    (:<&>@#@$$###) :: SameKind (Apply ((<&>@#@$$) a6989586621679369870) arg_a1vFH) ((<&>@#@$$$) a6989586621679369870 arg_a1vFH) =>
                      (<&>@#@$$) a6989586621679369870 a6989586621679369871
type instance Apply @((~>) a_a1vEE b_a1vEF) @(f_a1vED b_a1vEF) ((<&>@#@$$) a6989586621679369870) a6989586621679369871 = (<&>) a6989586621679369870 a6989586621679369871
instance SuppressUnusedWarnings ((<&>@#@$$) a6989586621679369870) where
  suppressUnusedWarnings = snd ((,) (:<&>@#@$$###) ())
infixl 1 <&>@#@$$
type (<&>@#@$$$) :: f_a1vED a_a1vEE
                    -> (~>) a_a1vEE b_a1vEF -> f_a1vED b_a1vEF
type family (<&>@#@$$$) @f_a1vED @a_a1vEE @b_a1vEF (a6989586621679369870 :: f_a1vED a_a1vEE) (a6989586621679369871 :: (~>) a_a1vEE b_a1vEF) :: f_a1vED b_a1vEF where
  (<&>@#@$$$) a6989586621679369870 a6989586621679369871 = (<&>) a6989586621679369870 a6989586621679369871
infixl 1 <&>@#@$$$
type (<$>@#@$) :: (~>) ((~>) a_a1vEH b_a1vEI) ((~>) (f_a1vEG a_a1vEH) (f_a1vEG b_a1vEI))
data (<$>@#@$) :: (~>) ((~>) a_a1vEH b_a1vEI) ((~>) (f_a1vEG a_a1vEH) (f_a1vEG b_a1vEI))
  where
    (:<$>@#@$###) :: SameKind (Apply (<$>@#@$) arg_a1vFS) ((<$>@#@$$) arg_a1vFS) =>
                      (<$>@#@$) a6989586621679369881
type instance Apply @((~>) a_a1vEH b_a1vEI) @((~>) (f_a1vEG a_a1vEH) (f_a1vEG b_a1vEI)) (<$>@#@$) a6989586621679369881 = (<$>@#@$$) a6989586621679369881
instance SuppressUnusedWarnings (<$>@#@$) where
  suppressUnusedWarnings = snd ((,) (:<$>@#@$###) ())
infixl 4 <$>@#@$
type (<$>@#@$$) :: (~>) a_a1vEH b_a1vEI
                    -> (~>) (f_a1vEG a_a1vEH) (f_a1vEG b_a1vEI)
data (<$>@#@$$) (a6989586621679369881 :: (~>) a_a1vEH b_a1vEI) :: (~>) (f_a1vEG a_a1vEH) (f_a1vEG b_a1vEI)
  where
    (:<$>@#@$$###) :: SameKind (Apply ((<$>@#@$$) a6989586621679369881) arg_a1vFS) ((<$>@#@$$$) a6989586621679369881 arg_a1vFS) =>
                      (<$>@#@$$) a6989586621679369881 a6989586621679369882
type instance Apply @(f_a1vEG a_a1vEH) @(f_a1vEG b_a1vEI) ((<$>@#@$$) a6989586621679369881) a6989586621679369882 = (<$>) a6989586621679369881 a6989586621679369882
instance SuppressUnusedWarnings ((<$>@#@$$) a6989586621679369881) where
  suppressUnusedWarnings = snd ((,) (:<$>@#@$$###) ())
infixl 4 <$>@#@$$
type (<$>@#@$$$) :: (~>) a_a1vEH b_a1vEI
                    -> f_a1vEG a_a1vEH -> f_a1vEG b_a1vEI
type family (<$>@#@$$$) @a_a1vEH @b_a1vEI @f_a1vEG (a6989586621679369881 :: (~>) a_a1vEH b_a1vEI) (a6989586621679369882 :: f_a1vEG a_a1vEH) :: f_a1vEG b_a1vEI where
  (<$>@#@$$$) a6989586621679369881 a6989586621679369882 = (<$>) a6989586621679369881 a6989586621679369882
infixl 4 <$>@#@$$$
type Void :: f_a1vEy a_a1vEz -> f_a1vEy ()
type family Void @f_a1vEy @a_a1vEz (a_a1vFq :: f_a1vEy a_a1vEz) :: f_a1vEy () where
  Void x_a1vFt = Apply (Apply (<$@#@$) Tuple0Sym0) x_a1vFt
type ($>) :: f_a1vEA a_a1vEB -> b_a1vEC -> f_a1vEA b_a1vEC
type family ($>) @f_a1vEA @a_a1vEB @b_a1vEC (a_a1vFy :: f_a1vEA a_a1vEB) (a_a1vFz :: b_a1vEC) :: f_a1vEA b_a1vEC where
  ($>) a_6989586621679369856_a1vFD a_6989586621679369858_a1vFE = Apply (Apply (Apply FlipSym0 (<$@#@$)) a_6989586621679369856_a1vFD) a_6989586621679369858_a1vFE
type (<&>) :: f_a1vED a_a1vEE
              -> (~>) a_a1vEE b_a1vEF -> f_a1vED b_a1vEF
type family (<&>) @f_a1vED @a_a1vEE @b_a1vEF (a_a1vFF :: f_a1vED a_a1vEE) (a_a1vFG :: (~>) a_a1vEE b_a1vEF) :: f_a1vED b_a1vEF where
  (<&>) as_a1vFK f_a1vFL = Apply (Apply (<$>@#@$) f_a1vFL) as_a1vFK
type (<$>) :: (~>) a_a1vEH b_a1vEI
              -> f_a1vEG a_a1vEH -> f_a1vEG b_a1vEI
type family (<$>) @a_a1vEH @b_a1vEI @f_a1vEG (a_a1vFQ :: (~>) a_a1vEH b_a1vEI) (a_a1vFR :: f_a1vEG a_a1vEH) :: f_a1vEG b_a1vEI where
  (<$>) a_6989586621679369874_a1vFV a_6989586621679369876_a1vFW = Apply (Apply FmapSym0 a_6989586621679369874_a1vFV) a_6989586621679369876_a1vFW
infixl 1 <&>
infixl 4 $>
infixl 4 <$>
type family LamCases_6989586621679369972_a1vHn a6989586621679369816 (_f_69895866216793698276989586621679369969 :: (~>) a7566047373982791004 b7566047373982791005) a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971 a_6989586621679369975_a1vHq where
  LamCases_6989586621679369972_a1vHn a_a1vEQ _f_6989586621679369827_a1vHj a_6989586621679369833_a1vHk a_6989586621679369835_a1vHl n_6989586621679369831_a1vHo = n_6989586621679369831_a1vHo
data LamCases_6989586621679369972Sym0 a6989586621679369816 (_f_69895866216793698276989586621679369969 :: (~>) a7566047373982791004 b7566047373982791005) a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971 a_69895866216793699756989586621679369976
  where
    LamCases_6989586621679369972Sym0KindInference :: SameKind (Apply (LamCases_6989586621679369972Sym0 a6989586621679369816 _f_69895866216793698276989586621679369969 a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971) arg_a1vHr) (LamCases_6989586621679369972Sym1 a6989586621679369816 _f_69895866216793698276989586621679369969 a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971 arg_a1vHr) =>
                                                      LamCases_6989586621679369972Sym0 a6989586621679369816 _f_69895866216793698276989586621679369969 a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971 a_69895866216793699756989586621679369976
type instance Apply @_ @_ (LamCases_6989586621679369972Sym0 a6989586621679369816 _f_69895866216793698276989586621679369969 a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971) a_69895866216793699756989586621679369976 = LamCases_6989586621679369972_a1vHn a6989586621679369816 _f_69895866216793698276989586621679369969 a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971 a_69895866216793699756989586621679369976
instance SuppressUnusedWarnings (LamCases_6989586621679369972Sym0 a6989586621679369816 _f_69895866216793698276989586621679369969 a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679369972Sym0KindInference ())
type family LamCases_6989586621679369972Sym1 a6989586621679369816 (_f_69895866216793698276989586621679369969 :: (~>) a7566047373982791004 b7566047373982791005) a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971 a_69895866216793699756989586621679369976 where
  LamCases_6989586621679369972Sym1 a6989586621679369816 _f_69895866216793698276989586621679369969 a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971 a_69895866216793699756989586621679369976 = LamCases_6989586621679369972_a1vHn a6989586621679369816 _f_69895866216793698276989586621679369969 a_69895866216793698336989586621679369970 a_69895866216793698356989586621679369971 a_69895866216793699756989586621679369976
type Fmap_6989586621679369962 :: forall a_a1vEQ
                                        a_i1v3K
                                        b_i1v3L. (~>) a_i1v3K b_i1v3L
                                                  -> (a_a1vEQ, a_i1v3K) -> (a_a1vEQ, b_i1v3L)
type family Fmap_6989586621679369962 @a_a1vEQ @a_i1v3K @b_i1v3L (a_a1vHe :: (~>) a_i1v3K b_i1v3L) (a_a1vHf :: (a_a1vEQ,
                                                                                                                a_i1v3K)) :: (a_a1vEQ,
                                                                                                                              b_i1v3L) where
  Fmap_6989586621679369962 @a_a1vEQ @a_i1v3K @b_i1v3L (_f_6989586621679369827_a1vHj :: (~>) a_i1v3K b_i1v3L) ('(a_6989586621679369833_a1vHk,
                                                                                                                a_6989586621679369835_a1vHl) :: (a_a1vEQ,
                                                                                                                                                  a_i1v3K)) = Apply (Apply Tuple2Sym0 (Apply (LamCases_6989586621679369972Sym0 a_a1vEQ _f_6989586621679369827_a1vHj a_6989586621679369833_a1vHk a_6989586621679369835_a1vHl) a_6989586621679369833_a1vHk)) (Apply _f_6989586621679369827_a1vHj a_6989586621679369835_a1vHl)
type family LamCases_6989586621679369990_a1vHF a6989586621679369816 (_z_69895866216793698296989586621679369987 :: a7566047373982791008) a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_6989586621679369993_a1vHI where
  LamCases_6989586621679369990_a1vHF a_a1vEQ _z_6989586621679369829_a1vHB a_6989586621679369839_a1vHC a_6989586621679369841_a1vHD n_6989586621679369837_a1vHG = n_6989586621679369837_a1vHG
data LamCases_6989586621679369990Sym0 a6989586621679369816 (_z_69895866216793698296989586621679369987 :: a7566047373982791008) a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699936989586621679369994
  where
    LamCases_6989586621679369990Sym0KindInference :: SameKind (Apply (LamCases_6989586621679369990Sym0 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989) arg_a1vHJ) (LamCases_6989586621679369990Sym1 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 arg_a1vHJ) =>
                                                      LamCases_6989586621679369990Sym0 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699936989586621679369994
type instance Apply @_ @_ (LamCases_6989586621679369990Sym0 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989) a_69895866216793699936989586621679369994 = LamCases_6989586621679369990_a1vHF a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699936989586621679369994
instance SuppressUnusedWarnings (LamCases_6989586621679369990Sym0 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679369990Sym0KindInference ())
type family LamCases_6989586621679369990Sym1 a6989586621679369816 (_z_69895866216793698296989586621679369987 :: a7566047373982791008) a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699936989586621679369994 where
  LamCases_6989586621679369990Sym1 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699936989586621679369994 = LamCases_6989586621679369990_a1vHF a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699936989586621679369994
type family LamCases_6989586621679369996_a1vHL a6989586621679369816 (_z_69895866216793698296989586621679369987 :: a7566047373982791008) a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_6989586621679369998_a1vHN where
  LamCases_6989586621679369996_a1vHL a_a1vEQ _z_6989586621679369829_a1vHB a_6989586621679369839_a1vHC a_6989586621679369841_a1vHD _ = _z_6989586621679369829_a1vHB
data LamCases_6989586621679369996Sym0 a6989586621679369816 (_z_69895866216793698296989586621679369987 :: a7566047373982791008) a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699986989586621679369999
  where
    LamCases_6989586621679369996Sym0KindInference :: SameKind (Apply (LamCases_6989586621679369996Sym0 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989) arg_a1vHO) (LamCases_6989586621679369996Sym1 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 arg_a1vHO) =>
                                                      LamCases_6989586621679369996Sym0 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699986989586621679369999
type instance Apply @_ @_ (LamCases_6989586621679369996Sym0 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989) a_69895866216793699986989586621679369999 = LamCases_6989586621679369996_a1vHL a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699986989586621679369999
instance SuppressUnusedWarnings (LamCases_6989586621679369996Sym0 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679369996Sym0KindInference ())
type family LamCases_6989586621679369996Sym1 a6989586621679369816 (_z_69895866216793698296989586621679369987 :: a7566047373982791008) a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699986989586621679369999 where
  LamCases_6989586621679369996Sym1 a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699986989586621679369999 = LamCases_6989586621679369996_a1vHL a6989586621679369816 _z_69895866216793698296989586621679369987 a_69895866216793698396989586621679369988 a_69895866216793698416989586621679369989 a_69895866216793699986989586621679369999
type TFHelper_6989586621679369980 :: forall a_a1vEQ
                                            a_i1v3O
                                            b_i1v3P. a_i1v3O
                                                      -> (a_a1vEQ, b_i1v3P) -> (a_a1vEQ, a_i1v3O)
type family TFHelper_6989586621679369980 @a_a1vEQ @a_i1v3O @b_i1v3P (a_a1vHw :: a_i1v3O) (a_a1vHx :: (a_a1vEQ,
                                                                                                      b_i1v3P)) :: (a_a1vEQ,
                                                                                                                    a_i1v3O) where
  TFHelper_6989586621679369980 @a_a1vEQ @a_i1v3O @b_i1v3P (_z_6989586621679369829_a1vHB :: a_i1v3O) ('(a_6989586621679369839_a1vHC,
                                                                                                        a_6989586621679369841_a1vHD) :: (a_a1vEQ,
                                                                                                                                        b_i1v3P)) = Apply (Apply Tuple2Sym0 (Apply (LamCases_6989586621679369990Sym0 a_a1vEQ _z_6989586621679369829_a1vHB a_6989586621679369839_a1vHC a_6989586621679369841_a1vHD) a_6989586621679369839_a1vHC)) (Apply (LamCases_6989586621679369996Sym0 a_a1vEQ _z_6989586621679369829_a1vHB a_6989586621679369839_a1vHC a_6989586621679369841_a1vHD) a_6989586621679369841_a1vHD)
instance PFunctor ((,) a_a1vEQ) where
  type Fmap a_a1vHa a_a1vHb = Fmap_6989586621679369962 a_a1vHa a_a1vHb
  type (<$) a_a1vHs a_a1vHt = TFHelper_6989586621679369980 a_a1vHs a_a1vHt
type Fmap_6989586621679370003 :: forall a_i1v3K
                                        b_i1v3L. (~>) a_i1v3K b_i1v3L
                                                  -> Down a_i1v3K -> Down b_i1v3L
type family Fmap_6989586621679370003 @a_i1v3K @b_i1v3L (a_a1vHT :: (~>) a_i1v3K b_i1v3L) (a_a1vHU :: Down a_i1v3K) :: Down b_i1v3L where
  Fmap_6989586621679370003 @a_i1v3K @b_i1v3L _f_6989586621679369844_a1vHY ('Down a_6989586621679369848_a1vHZ) = Apply DownSym0 (Apply _f_6989586621679369844_a1vHY a_6989586621679369848_a1vHZ)
type family LamCases_6989586621679370023_a1vIc (_z_69895866216793698466989586621679370021 :: a7566047373982791008) a_69895866216793698506989586621679370022 a_6989586621679370025_a1vIe where
  LamCases_6989586621679370023_a1vIc _z_6989586621679369846_a1vI9 a_6989586621679369850_a1vIa _ = _z_6989586621679369846_a1vI9
data LamCases_6989586621679370023Sym0 (_z_69895866216793698466989586621679370021 :: a7566047373982791008) a_69895866216793698506989586621679370022 a_69895866216793700256989586621679370026
  where
    LamCases_6989586621679370023Sym0KindInference :: SameKind (Apply (LamCases_6989586621679370023Sym0 _z_69895866216793698466989586621679370021 a_69895866216793698506989586621679370022) arg_a1vIf) (LamCases_6989586621679370023Sym1 _z_69895866216793698466989586621679370021 a_69895866216793698506989586621679370022 arg_a1vIf) =>
                                                      LamCases_6989586621679370023Sym0 _z_69895866216793698466989586621679370021 a_69895866216793698506989586621679370022 a_69895866216793700256989586621679370026
type instance Apply @_ @_ (LamCases_6989586621679370023Sym0 _z_69895866216793698466989586621679370021 a_69895866216793698506989586621679370022) a_69895866216793700256989586621679370026 = LamCases_6989586621679370023_a1vIc _z_69895866216793698466989586621679370021 a_69895866216793698506989586621679370022 a_69895866216793700256989586621679370026
instance SuppressUnusedWarnings (LamCases_6989586621679370023Sym0 _z_69895866216793698466989586621679370021 a_69895866216793698506989586621679370022) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679370023Sym0KindInference ())
type family LamCases_6989586621679370023Sym1 (_z_69895866216793698466989586621679370021 :: a7566047373982791008) a_69895866216793698506989586621679370022 a_69895866216793700256989586621679370026 where
  LamCases_6989586621679370023Sym1 _z_69895866216793698466989586621679370021 a_69895866216793698506989586621679370022 a_69895866216793700256989586621679370026 = LamCases_6989586621679370023_a1vIc _z_69895866216793698466989586621679370021 a_69895866216793698506989586621679370022 a_69895866216793700256989586621679370026
type TFHelper_6989586621679370014 :: forall a_i1v3O
                                            b_i1v3P. a_i1v3O -> Down b_i1v3P -> Down a_i1v3O
type family TFHelper_6989586621679370014 @a_i1v3O @b_i1v3P (a_a1vI4 :: a_i1v3O) (a_a1vI5 :: Down b_i1v3P) :: Down a_i1v3O where
  TFHelper_6989586621679370014 @a_i1v3O @b_i1v3P _z_6989586621679369846_a1vI9 ('Down a_6989586621679369850_a1vIa) = Apply DownSym0 (Apply (LamCases_6989586621679370023Sym0 _z_6989586621679369846_a1vI9 a_6989586621679369850_a1vIa) a_6989586621679369850_a1vIa)
instance PFunctor Down where
  type Fmap a_a1vHP a_a1vHQ = Fmap_6989586621679370003 a_a1vHP a_a1vHQ
  type (<$) a_a1vI0 a_a1vI1 = TFHelper_6989586621679370014 a_a1vI0 a_a1vI1
infixl 1 %<&>
infixl 4 %$>
infixl 4 %<$>
sVoid ::
  (forall (t_a1vIg :: f_a1vEy a_a1vEz).
    SFunctor f_a1vEy =>
    Sing t_a1vIg -> Sing (Void t_a1vIg :: f_a1vEy ()) :: Type)
(%$>) ::
  (forall (t_a1vIi :: f_a1vEA a_a1vEB) (t_a1vIj :: b_a1vEC).
    SFunctor f_a1vEA =>
    Sing t_a1vIi
    -> Sing t_a1vIj
      -> Sing (($>) t_a1vIi t_a1vIj :: f_a1vEA b_a1vEC) :: Type)
(%<&>) ::
  (forall (t_a1vIn :: f_a1vED a_a1vEE)
          (t_a1vIo :: (~>) a_a1vEE b_a1vEF).
    SFunctor f_a1vED =>
    Sing t_a1vIn
    -> Sing t_a1vIo
      -> Sing ((<&>) t_a1vIn t_a1vIo :: f_a1vED b_a1vEF) :: Type)
(%<$>) ::
  (forall (t_a1vIs :: (~>) a_a1vEH b_a1vEI)
          (t_a1vIt :: f_a1vEG a_a1vEH).
    SFunctor f_a1vEG =>
    Sing t_a1vIs
    -> Sing t_a1vIt
      -> Sing ((<$>) t_a1vIs t_a1vIt :: f_a1vEG b_a1vEI) :: Type)
sVoid (sX :: Sing x_a1vFt)
  = applySing (applySing (singFun2 @(<$@#@$) (%<$)) STuple0) sX
(%$>)
  (sA_6989586621679369856 :: Sing a_6989586621679369856_a1vFD)
  (sA_6989586621679369858 :: Sing a_6989586621679369858_a1vFE)
  = applySing
      (applySing
          (applySing (singFun3 @FlipSym0 sFlip) (singFun2 @(<$@#@$) (%<$)))
          sA_6989586621679369856)
      sA_6989586621679369858
(%<&>) (sAs :: Sing as_a1vFK) (sF :: Sing f_a1vFL)
  = applySing (applySing (singFun2 @(<$>@#@$) (%<$>)) sF) sAs
(%<$>)
  (sA_6989586621679369874 :: Sing a_6989586621679369874_a1vFV)
  (sA_6989586621679369876 :: Sing a_6989586621679369876_a1vFW)
  = applySing
      (applySing (singFun2 @FmapSym0 sFmap) sA_6989586621679369874)
      sA_6989586621679369876
instance SFunctor f_a1vEy =>
          SingI (VoidSym0 :: (~>) (f_a1vEy a_a1vEz) (f_a1vEy ())) where
  sing = singFun1 @VoidSym0 sVoid
instance SFunctor f_a1vEA =>
          SingI (($>@#@$) :: (~>) (f_a1vEA a_a1vEB) ((~>) b_a1vEC (f_a1vEA b_a1vEC))) where
  sing = singFun2 @($>@#@$) (%$>)
instance (SFunctor f_a1vEA, SingI d_a1vIk) =>
          SingI (($>@#@$$) (d_a1vIk :: f_a1vEA a_a1vEB) :: (~>) b_a1vEC (f_a1vEA b_a1vEC)) where
  sing
    = singFun1
        @(($>@#@$$) (d_a1vIk :: f_a1vEA a_a1vEB)) ((%$>) (sing @d_a1vIk))
instance SFunctor f_a1vEA =>
          SingI1 (($>@#@$$) :: f_a1vEA a_a1vEB
                              -> (~>) b_a1vEC (f_a1vEA b_a1vEC)) where
  liftSing (s_a1vIm :: Sing (d_a1vIk :: f_a1vEA a_a1vEB))
    = singFun1
        @(($>@#@$$) (d_a1vIk :: f_a1vEA a_a1vEB)) ((%$>) s_a1vIm)
instance SFunctor f_a1vED =>
          SingI ((<&>@#@$) :: (~>) (f_a1vED a_a1vEE) ((~>) ((~>) a_a1vEE b_a1vEF) (f_a1vED b_a1vEF))) where
  sing = singFun2 @(<&>@#@$) (%<&>)
instance (SFunctor f_a1vED, SingI d_a1vIp) =>
          SingI ((<&>@#@$$) (d_a1vIp :: f_a1vED a_a1vEE) :: (~>) ((~>) a_a1vEE b_a1vEF) (f_a1vED b_a1vEF)) where
  sing
    = singFun1
        @((<&>@#@$$) (d_a1vIp :: f_a1vED a_a1vEE)) ((%<&>) (sing @d_a1vIp))
instance SFunctor f_a1vED =>
          SingI1 ((<&>@#@$$) :: f_a1vED a_a1vEE
                                -> (~>) ((~>) a_a1vEE b_a1vEF) (f_a1vED b_a1vEF)) where
  liftSing (s_a1vIr :: Sing (d_a1vIp :: f_a1vED a_a1vEE))
    = singFun1
        @((<&>@#@$$) (d_a1vIp :: f_a1vED a_a1vEE)) ((%<&>) s_a1vIr)
instance SFunctor f_a1vEG =>
          SingI ((<$>@#@$) :: (~>) ((~>) a_a1vEH b_a1vEI) ((~>) (f_a1vEG a_a1vEH) (f_a1vEG b_a1vEI))) where
  sing = singFun2 @(<$>@#@$) (%<$>)
instance (SFunctor f_a1vEG, SingI d_a1vIu) =>
          SingI ((<$>@#@$$) (d_a1vIu :: (~>) a_a1vEH b_a1vEI) :: (~>) (f_a1vEG a_a1vEH) (f_a1vEG b_a1vEI)) where
  sing
    = singFun1
        @((<$>@#@$$) (d_a1vIu :: (~>) a_a1vEH b_a1vEI))
        ((%<$>) (sing @d_a1vIu))
instance SFunctor f_a1vEG =>
          SingI1 ((<$>@#@$$) :: (~>) a_a1vEH b_a1vEI
                                -> (~>) (f_a1vEG a_a1vEH) (f_a1vEG b_a1vEI)) where
  liftSing (s_a1vIw :: Sing (d_a1vIu :: (~>) a_a1vEH b_a1vEI))
    = singFun1
        @((<$>@#@$$) (d_a1vIu :: (~>) a_a1vEH b_a1vEI)) ((%<$>) s_a1vIw)
instance SFunctor ((,) a_a1vEQ) where
  sFmap
    (_sf_6989586621679369827 :: Sing _f_6989586621679369827_a1vHj)
    (STuple2 (sA_6989586621679369833 :: Sing a_6989586621679369833_a1vHk)
              (sA_6989586621679369835 :: Sing a_6989586621679369835_a1vHl))
    = applySing
        (applySing
            (singFun2 @Tuple2Sym0 STuple2)
            (applySing
              (singFun1
                  @(LamCases_6989586621679369972Sym0 a_a1vEQ _f_6989586621679369827_a1vHj a_6989586621679369833_a1vHk a_6989586621679369835_a1vHl)
                  (\cases
                    (sN_6989586621679369831 :: Sing n_6989586621679369831_a1vHo)
                      -> sN_6989586621679369831))
              sA_6989586621679369833))
        (applySing _sf_6989586621679369827 sA_6989586621679369835)
  (%<$)
    (_sz_6989586621679369829 :: Sing _z_6989586621679369829_a1vHB)
    (STuple2 (sA_6989586621679369839 :: Sing a_6989586621679369839_a1vHC)
              (sA_6989586621679369841 :: Sing a_6989586621679369841_a1vHD))
    = applySing
        (applySing
            (singFun2 @Tuple2Sym0 STuple2)
            (applySing
              (singFun1
                  @(LamCases_6989586621679369990Sym0 a_a1vEQ _z_6989586621679369829_a1vHB a_6989586621679369839_a1vHC a_6989586621679369841_a1vHD)
                  (\cases
                    (sN_6989586621679369837 :: Sing n_6989586621679369837_a1vHG)
                      -> sN_6989586621679369837))
              sA_6989586621679369839))
        (applySing
            (singFun1
              @(LamCases_6989586621679369996Sym0 a_a1vEQ _z_6989586621679369829_a1vHB a_6989586621679369839_a1vHC a_6989586621679369841_a1vHD)
              (\cases _ -> _sz_6989586621679369829))
            sA_6989586621679369841)
instance SFunctor Down where
  sFmap
    (_sf_6989586621679369844 :: Sing _f_6989586621679369844_a1vHY)
    (SDown (sA_6989586621679369848 :: Sing a_6989586621679369848_a1vHZ))
    = applySing
        (singFun1 @DownSym0 SDown)
        (applySing _sf_6989586621679369844 sA_6989586621679369848)
  (%<$)
    (_sz_6989586621679369846 :: Sing _z_6989586621679369846_a1vI9)
    (SDown (sA_6989586621679369850 :: Sing a_6989586621679369850_a1vIa))
    = applySing
        (singFun1 @DownSym0 SDown)
        (applySing
            (singFun1
              @(LamCases_6989586621679370023Sym0 _z_6989586621679369846_a1vI9 a_6989586621679369850_a1vIa)
              (\cases _ -> _sz_6989586621679369846))
            sA_6989586621679369850)
