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
-- Module      :  Data.Functor.Identity.Singletons
-- Copyright   :  (C) 2018 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Exports the promoted and singled versions of the 'Identity' data type.
--
-----------------------------------------------------------------------------

module Data.Functor.Identity.Singletons (
  -- * The 'Identity' singleton
  Sing, SIdentity(..), RunIdentity, sRunIdentity,

  -- * Defunctionalization symbols
  IdentitySym0, IdentitySym1,
  RunIdentitySym0, RunIdentitySym1
  ) where

import Control.Monad.Singletons.Internal
import Data.Eq.Singletons
import Data.Foldable (Foldable(..))
import Data.Foldable.Singletons
import Data.Functor.Identity
import Data.Monoid.Singletons
import Data.Ord.Singletons
import Data.Semigroup.Singletons.Internal.Classes
import Data.Singletons.Base.Instances hiding (Foldl, sFoldl)
import Data.Singletons.Base.Enum
import Data.Singletons.TH
import GHC.Base.Singletons hiding (Foldr, FoldrSym0, sFoldr)
import GHC.Num.Singletons
import Text.Show.Singletons
import qualified GHC.Num.Natural
import GHC.Exts
type Succ_6989586621679243108 :: forall a_aYcj. Identity a_aYcj
                                                    -> Identity a_aYcj
type family Succ_6989586621679243108 @a_aYcj (a_aYHc :: Identity a_aYcj) :: Identity a_aYcj where
  Succ_6989586621679243108 @a_aYcj ('Identity x_aYHf :: Identity a_aYcj) = Apply IdentitySym0 (Apply SuccSym0 x_aYHf)
type Pred_6989586621679243115 :: forall a_aYcj. Identity a_aYcj
                                                -> Identity a_aYcj
type family Pred_6989586621679243115 @a_aYcj (a_aYHj :: Identity a_aYcj) :: Identity a_aYcj where
  Pred_6989586621679243115 @a_aYcj ('Identity x_aYHm :: Identity a_aYcj) = Apply IdentitySym0 (Apply PredSym0 x_aYHm)
type ToEnum_6989586621679243122 :: forall a_aYcj. GHC.Num.Natural.Natural
                                                  -> Identity a_aYcj
type family ToEnum_6989586621679243122 @a_aYcj (a_aYHq :: GHC.Num.Natural.Natural) :: Identity a_aYcj where
  ToEnum_6989586621679243122 @a_aYcj (i_aYHt :: GHC.Num.Natural.Natural) = Apply IdentitySym0 (Apply ToEnumSym0 i_aYHt)
type FromEnum_6989586621679243129 :: forall a_aYcj. Identity a_aYcj
                                                    -> GHC.Num.Natural.Natural
type family FromEnum_6989586621679243129 @a_aYcj (a_aYHx :: Identity a_aYcj) :: GHC.Num.Natural.Natural where
  FromEnum_6989586621679243129 @a_aYcj ('Identity x_aYHA :: Identity a_aYcj) = Apply FromEnumSym0 x_aYHA
type EnumFromTo_6989586621679243137 :: forall a_aYcj. Identity a_aYcj
                                                      -> Identity a_aYcj -> [Identity a_aYcj]
type family EnumFromTo_6989586621679243137 @a_aYcj (a_aYHF :: Identity a_aYcj) (a_aYHG :: Identity a_aYcj) :: [Identity a_aYcj] where
  EnumFromTo_6989586621679243137 @a_aYcj ('Identity x_aYHK :: Identity a_aYcj) ('Identity y_aYHL :: Identity a_aYcj) = Apply (Apply MapSym0 IdentitySym0) (Apply (Apply EnumFromToSym0 x_aYHK) y_aYHL)
type EnumFromThenTo_6989586621679243149 :: forall a_aYcj. Identity a_aYcj
                                                          -> Identity a_aYcj
                                                              -> Identity a_aYcj
                                                                -> [Identity a_aYcj]
type family EnumFromThenTo_6989586621679243149 @a_aYcj (a_aYHR :: Identity a_aYcj) (a_aYHS :: Identity a_aYcj) (a_aYHT :: Identity a_aYcj) :: [Identity a_aYcj] where
  EnumFromThenTo_6989586621679243149 @a_aYcj ('Identity x_aYHY :: Identity a_aYcj) ('Identity y_aYHZ :: Identity a_aYcj) ('Identity z_aYI0 :: Identity a_aYcj) = Apply (Apply MapSym0 IdentitySym0) (Apply (Apply (Apply EnumFromThenToSym0 x_aYHY) y_aYHZ) z_aYI0)
instance PEnum (Identity a_aYcj) where
  type Succ a_aYH9 = Succ_6989586621679243108 a_aYH9
  type Pred a_aYHg = Pred_6989586621679243115 a_aYHg
  type ToEnum a_aYHn = ToEnum_6989586621679243122 a_aYHn
  type FromEnum a_aYHu = FromEnum_6989586621679243129 a_aYHu
  type EnumFromTo a_aYHB a_aYHC = EnumFromTo_6989586621679243137 a_aYHB a_aYHC
  type EnumFromThenTo a_aYHM a_aYHN a_aYHO = EnumFromThenTo_6989586621679243149 a_aYHM a_aYHN a_aYHO
type Mempty_6989586621679243191 :: forall a_aYct. Identity a_aYct
type family Mempty_6989586621679243191 @a_aYct :: Identity a_aYct where
  Mempty_6989586621679243191 @a_aYct = Apply IdentitySym0 MemptySym0
instance PMonoid (Identity a_aYct) where
  type Mempty = Mempty_6989586621679243191
type TFHelper_6989586621679243317 :: forall a_aYcu. Identity a_aYcu
                                                    -> Identity a_aYcu -> Identity a_aYcu
type family TFHelper_6989586621679243317 @a_aYcu (a_aYKz :: Identity a_aYcu) (a_aYKA :: Identity a_aYcu) :: Identity a_aYcu where
  TFHelper_6989586621679243317 @a_aYcu ('Identity x_aYKE :: Identity a_aYcu) ('Identity y_aYKF :: Identity a_aYcu) = Apply IdentitySym0 (Apply (Apply (+@#@$) x_aYKE) y_aYKF)
type TFHelper_6989586621679243328 :: forall a_aYcu. Identity a_aYcu
                                                    -> Identity a_aYcu -> Identity a_aYcu
type family TFHelper_6989586621679243328 @a_aYcu (a_aYKK :: Identity a_aYcu) (a_aYKL :: Identity a_aYcu) :: Identity a_aYcu where
  TFHelper_6989586621679243328 @a_aYcu ('Identity x_aYKP :: Identity a_aYcu) ('Identity y_aYKQ :: Identity a_aYcu) = Apply IdentitySym0 (Apply (Apply (-@#@$) x_aYKP) y_aYKQ)
type TFHelper_6989586621679243339 :: forall a_aYcu. Identity a_aYcu
                                                    -> Identity a_aYcu -> Identity a_aYcu
type family TFHelper_6989586621679243339 @a_aYcu (a_aYKV :: Identity a_aYcu) (a_aYKW :: Identity a_aYcu) :: Identity a_aYcu where
  TFHelper_6989586621679243339 @a_aYcu ('Identity x_aYL0 :: Identity a_aYcu) ('Identity y_aYL1 :: Identity a_aYcu) = Apply IdentitySym0 (Apply (Apply (*@#@$) x_aYL0) y_aYL1)
type Negate_6989586621679243349 :: forall a_aYcu. Identity a_aYcu
                                                  -> Identity a_aYcu
type family Negate_6989586621679243349 @a_aYcu (a_aYL5 :: Identity a_aYcu) :: Identity a_aYcu where
  Negate_6989586621679243349 @a_aYcu ('Identity x_aYL8 :: Identity a_aYcu) = Apply IdentitySym0 (Apply NegateSym0 x_aYL8)
type Abs_6989586621679243356 :: forall a_aYcu. Identity a_aYcu
                                                -> Identity a_aYcu
type family Abs_6989586621679243356 @a_aYcu (a_aYLc :: Identity a_aYcu) :: Identity a_aYcu where
  Abs_6989586621679243356 @a_aYcu ('Identity x_aYLf :: Identity a_aYcu) = Apply IdentitySym0 (Apply AbsSym0 x_aYLf)
type Signum_6989586621679243363 :: forall a_aYcu. Identity a_aYcu
                                                  -> Identity a_aYcu
type family Signum_6989586621679243363 @a_aYcu (a_aYLj :: Identity a_aYcu) :: Identity a_aYcu where
  Signum_6989586621679243363 @a_aYcu ('Identity x_aYLm :: Identity a_aYcu) = Apply IdentitySym0 (Apply SignumSym0 x_aYLm)
type FromInteger_6989586621679243370 :: forall a_aYcu. GHC.Num.Natural.Natural
                                                        -> Identity a_aYcu
type family FromInteger_6989586621679243370 @a_aYcu (a_aYLq :: GHC.Num.Natural.Natural) :: Identity a_aYcu where
  FromInteger_6989586621679243370 @a_aYcu (n_aYLt :: GHC.Num.Natural.Natural) = Apply IdentitySym0 (Apply FromIntegerSym0 n_aYLt)
instance PNum (Identity a_aYcu) where
  type (+) a_aYKv a_aYKw = TFHelper_6989586621679243317 a_aYKv a_aYKw
  type (-) a_aYKG a_aYKH = TFHelper_6989586621679243328 a_aYKG a_aYKH
  type (*) a_aYKR a_aYKS = TFHelper_6989586621679243339 a_aYKR a_aYKS
  type Negate a_aYL2 = Negate_6989586621679243349 a_aYL2
  type Abs a_aYL9 = Abs_6989586621679243356 a_aYL9
  type Signum a_aYLg = Signum_6989586621679243363 a_aYLg
  type FromInteger a_aYLn = FromInteger_6989586621679243370 a_aYLn
type TFHelper_6989586621679243408 :: forall a_aYcF. Identity a_aYcF
                                                    -> Identity a_aYcF -> Identity a_aYcF
type family TFHelper_6989586621679243408 @a_aYcF (a_aYM2 :: Identity a_aYcF) (a_aYM3 :: Identity a_aYcF) :: Identity a_aYcF where
  TFHelper_6989586621679243408 @a_aYcF ('Identity x_aYM7 :: Identity a_aYcF) ('Identity y_aYM8 :: Identity a_aYcF) = Apply IdentitySym0 (Apply (Apply (<>@#@$) x_aYM7) y_aYM8)
instance PSemigroup (Identity a_aYcF) where
  type (<>) a_aYLY a_aYLZ = TFHelper_6989586621679243408 a_aYLY a_aYLZ
type ShowsPrec_6989586621679243812 :: forall a_aYcI. GHC.Num.Natural.Natural
                                                      -> Identity a_aYcI
                                                        -> Symbol
                                                            -> Symbol
type family ShowsPrec_6989586621679243812 @a_aYcI (a_aYSA :: GHC.Num.Natural.Natural) (a_aYSB :: Identity a_aYcI) (a_aYSC :: Symbol) :: Symbol where
  ShowsPrec_6989586621679243812 @a_aYcI (d_aYSH :: GHC.Num.Natural.Natural) ('Identity x_aYSI :: Identity a_aYcI) (a_6989586621679243814_aYSJ :: Symbol) = Apply (Apply (Apply ($@#@$) (Apply ShowParenSym0 (Apply (Apply (>@#@$) d_aYSH) (FromInteger 10)))) (Apply (Apply (.@#@$) (Apply ShowStringSym0 "Identity ")) (Apply (Apply ShowsPrecSym0 (FromInteger 11)) x_aYSI))) a_6989586621679243814_aYSJ
instance PShow (Identity a_aYcI) where
  type ShowsPrec a_aYSt a_aYSu a_aYSv = ShowsPrec_6989586621679243812 a_aYSt a_aYSu a_aYSv
type Fmap_6989586621679243993 :: forall a_iYSL
                                        b_iYSM. (~>) a_iYSL b_iYSM
                                                -> Identity a_iYSL -> Identity b_iYSM
type family Fmap_6989586621679243993 @a_iYSL @b_iYSM (a_aYVt :: (~>) a_iYSL b_iYSM) (a_aYVu :: Identity a_iYSL) :: Identity b_iYSM where
  Fmap_6989586621679243993 @a_iYSL @b_iYSM _f_6989586621679243015_aYVy ('Identity a_6989586621679243019_aYVz) = Apply IdentitySym0 (Apply _f_6989586621679243015_aYVy a_6989586621679243019_aYVz)
type family LamCases_6989586621679244013_aYVM (_z_69895866216792430176989586621679244011 :: a7566047373982667319) a_69895866216792430216989586621679244012 a_6989586621679244015_aYVO where
  LamCases_6989586621679244013_aYVM _z_6989586621679243017_aYVJ a_6989586621679243021_aYVK _ = _z_6989586621679243017_aYVJ
data LamCases_6989586621679244013Sym0 (_z_69895866216792430176989586621679244011 :: a7566047373982667319) a_69895866216792430216989586621679244012 a_69895866216792440156989586621679244016
  where
    LamCases_6989586621679244013Sym0KindInference :: SameKind (Apply (LamCases_6989586621679244013Sym0 _z_69895866216792430176989586621679244011 a_69895866216792430216989586621679244012) arg_aYVP) (LamCases_6989586621679244013Sym1 _z_69895866216792430176989586621679244011 a_69895866216792430216989586621679244012 arg_aYVP) =>
                                                      LamCases_6989586621679244013Sym0 _z_69895866216792430176989586621679244011 a_69895866216792430216989586621679244012 a_69895866216792440156989586621679244016
type instance Apply @_ @_ (LamCases_6989586621679244013Sym0 _z_69895866216792430176989586621679244011 a_69895866216792430216989586621679244012) a_69895866216792440156989586621679244016 = LamCases_6989586621679244013_aYVM _z_69895866216792430176989586621679244011 a_69895866216792430216989586621679244012 a_69895866216792440156989586621679244016
instance SuppressUnusedWarnings (LamCases_6989586621679244013Sym0 _z_69895866216792430176989586621679244011 a_69895866216792430216989586621679244012) where
  suppressUnusedWarnings
    = snd ((,) LamCases_6989586621679244013Sym0KindInference ())
type family LamCases_6989586621679244013Sym1 (_z_69895866216792430176989586621679244011 :: a7566047373982667319) a_69895866216792430216989586621679244012 a_69895866216792440156989586621679244016 where
  LamCases_6989586621679244013Sym1 _z_69895866216792430176989586621679244011 a_69895866216792430216989586621679244012 a_69895866216792440156989586621679244016 = LamCases_6989586621679244013_aYVM _z_69895866216792430176989586621679244011 a_69895866216792430216989586621679244012 a_69895866216792440156989586621679244016
type TFHelper_6989586621679244004 :: forall a_iYSP b_iYSQ. a_iYSP
                                                            -> Identity b_iYSQ -> Identity a_iYSP
type family TFHelper_6989586621679244004 @a_iYSP @b_iYSQ (a_aYVE :: a_iYSP) (a_aYVF :: Identity b_iYSQ) :: Identity a_iYSP where
  TFHelper_6989586621679244004 @a_iYSP @b_iYSQ _z_6989586621679243017_aYVJ ('Identity a_6989586621679243021_aYVK) = Apply IdentitySym0 (Apply (LamCases_6989586621679244013Sym0 _z_6989586621679243017_aYVJ a_6989586621679243021_aYVK) a_6989586621679243021_aYVK)
instance PFunctor Identity where
  type Fmap a_aYVp a_aYVq = Fmap_6989586621679243993 a_aYVp a_aYVq
  type (<$) a_aYVA a_aYVB = TFHelper_6989586621679244004 a_aYVA a_aYVB
type FoldMap_6989586621679245006 :: forall a_iYVT
                                            m_iYVU. (~>) a_iYVT m_iYVU
                                                    -> Identity a_iYVT -> m_iYVU
type family FoldMap_6989586621679245006 @a_iYVT @m_iYVU (a_aZbO :: (~>) a_iYVT m_iYVU) (a_aZbP :: Identity a_iYVT) :: m_iYVU where
  FoldMap_6989586621679245006 @a_iYVT @m_iYVU f_aZbT ('Identity x_aZbU) = Apply f_aZbT x_aZbU
type Elem_6989586621679245017 :: forall a_iYWt. a_iYWt
                                                -> Identity a_iYWt -> Bool
type family Elem_6989586621679245017 @a_iYWt (a_aZbZ :: a_iYWt) (a_aZc0 :: Identity a_iYWt) :: Bool where
  Elem_6989586621679245017 @a_iYWt x_aZc4 ('Identity y_aZc5) = Apply (Apply (==@#@$) x_aZc4) y_aZc5
type Foldl_6989586621679245029 :: forall b_iYW7
                                          a_iYW8. (~>) b_iYW7 ((~>) a_iYW8 b_iYW7)
                                                  -> b_iYW7 -> Identity a_iYW8 -> b_iYW7
type family Foldl_6989586621679245029 @b_iYW7 @a_iYW8 (a_aZcb :: (~>) b_iYW7 ((~>) a_iYW8 b_iYW7)) (a_aZcc :: b_iYW7) (a_aZcd :: Identity a_iYW8) :: b_iYW7 where
  Foldl_6989586621679245029 @b_iYW7 @a_iYW8 f_aZci z_aZcj ('Identity x_aZck) = Apply (Apply f_aZci z_aZcj) x_aZck
type Foldl'_6989586621679245044 :: forall b_iYWc
                                          a_iYWd. (~>) b_iYWc ((~>) a_iYWd b_iYWc)
                                                  -> b_iYWc -> Identity a_iYWd -> b_iYWc
type family Foldl'_6989586621679245044 @b_iYWc @a_iYWd (a_aZcq :: (~>) b_iYWc ((~>) a_iYWd b_iYWc)) (a_aZcr :: b_iYWc) (a_aZcs :: Identity a_iYWd) :: b_iYWc where
  Foldl'_6989586621679245044 @b_iYWc @a_iYWd f_aZcx z_aZcy ('Identity x_aZcz) = Apply (Apply f_aZcx z_aZcy) x_aZcz
type Foldl1_6989586621679245058 :: forall a_iYWk. (~>) a_iYWk ((~>) a_iYWk a_iYWk)
                                                  -> Identity a_iYWk -> a_iYWk
type family Foldl1_6989586621679245058 @a_iYWk (a_aZcE :: (~>) a_iYWk ((~>) a_iYWk a_iYWk)) (a_aZcF :: Identity a_iYWk) :: a_iYWk where
  Foldl1_6989586621679245058 @a_iYWk _ ('Identity x_aZcJ) = x_aZcJ
type Foldr_6989586621679245069 :: forall a_iYVX
                                          b_iYVY. (~>) a_iYVX ((~>) b_iYVY b_iYVY)
                                                  -> b_iYVY -> Identity a_iYVX -> b_iYVY
type family Foldr_6989586621679245069 @a_iYVX @b_iYVY (a_aZcP :: (~>) a_iYVX ((~>) b_iYVY b_iYVY)) (a_aZcQ :: b_iYVY) (a_aZcR :: Identity a_iYVX) :: b_iYVY where
  Foldr_6989586621679245069 @a_iYVX @b_iYVY f_aZcW z_aZcX ('Identity x_aZcY) = Apply (Apply f_aZcW x_aZcY) z_aZcX
type Foldr'_6989586621679245084 :: forall a_iYW2
                                          b_iYW3. (~>) a_iYW2 ((~>) b_iYW3 b_iYW3)
                                                  -> b_iYW3 -> Identity a_iYW2 -> b_iYW3
type family Foldr'_6989586621679245084 @a_iYW2 @b_iYW3 (a_aZda :: (~>) a_iYW2 ((~>) b_iYW3 b_iYW3)) (a_aZdb :: b_iYW3) (a_aZdc :: Identity a_iYW2) :: b_iYW3 where
  Foldr'_6989586621679245084 @a_iYW2 @b_iYW3 a_6989586621679245086_aZdh a_6989586621679245088_aZdi a_6989586621679245090_aZdj = Apply (Apply (Apply FoldrSym0 a_6989586621679245086_aZdh) a_6989586621679245088_aZdi) a_6989586621679245090_aZdj
type Foldr1_6989586621679245104 :: forall a_iYWh. (~>) a_iYWh ((~>) a_iYWh a_iYWh)
                                                  -> Identity a_iYWh -> a_iYWh
type family Foldr1_6989586621679245104 @a_iYWh (a_aZdo :: (~>) a_iYWh ((~>) a_iYWh a_iYWh)) (a_aZdp :: Identity a_iYWh) :: a_iYWh where
  Foldr1_6989586621679245104 @a_iYWh _ ('Identity x_aZdt) = x_aZdt
type Length_6989586621679245113 :: forall a_iYWr. Identity a_iYWr
                                                  -> GHC.Num.Natural.Natural
type family Length_6989586621679245113 @a_iYWr (a_aZdx :: Identity a_iYWr) :: GHC.Num.Natural.Natural where
  Length_6989586621679245113 @a_iYWr _ = FromInteger 1
type Maximum_6989586621679245119 :: forall a_iYWw. Identity a_iYWw
                                                    -> a_iYWw
type family Maximum_6989586621679245119 @a_iYWw (a_aZdD :: Identity a_iYWw) :: a_iYWw where
  Maximum_6989586621679245119 @a_iYWw ('Identity x_aZdG) = x_aZdG
type Minimum_6989586621679245126 :: forall a_iYWy. Identity a_iYWy
                                                    -> a_iYWy
type family Minimum_6989586621679245126 @a_iYWy (a_aZdK :: Identity a_iYWy) :: a_iYWy where
  Minimum_6989586621679245126 @a_iYWy ('Identity x_aZdN) = x_aZdN
type Null_6989586621679245133 :: forall a_iYWp. Identity a_iYWp
                                                -> Bool
type family Null_6989586621679245133 @a_iYWp (a_aZdR :: Identity a_iYWp) :: Bool where
  Null_6989586621679245133 @a_iYWp _ = FalseSym0
type Product_6989586621679245139 :: forall a_iYWC. Identity a_iYWC
                                                    -> a_iYWC
type family Product_6989586621679245139 @a_iYWC (a_aZdX :: Identity a_iYWC) :: a_iYWC where
  Product_6989586621679245139 @a_iYWC ('Identity x_aZe0) = x_aZe0
type Sum_6989586621679245146 :: forall a_iYWA. Identity a_iYWA
                                                -> a_iYWA
type family Sum_6989586621679245146 @a_iYWA (a_aZe4 :: Identity a_iYWA) :: a_iYWA where
  Sum_6989586621679245146 @a_iYWA ('Identity x_aZe7) = x_aZe7
type ToList_6989586621679245153 :: forall a_iYWn. Identity a_iYWn
                                                  -> [a_iYWn]
type family ToList_6989586621679245153 @a_iYWn (a_aZeb :: Identity a_iYWn) :: [a_iYWn] where
  ToList_6989586621679245153 @a_iYWn ('Identity x_aZee) = Apply (Apply (:@#@$) x_aZee) NilSym0
instance PFoldable Identity where
  type FoldMap a_aZbK a_aZbL = FoldMap_6989586621679245006 a_aZbK a_aZbL
  type Elem a_aZbV a_aZbW = Elem_6989586621679245017 a_aZbV a_aZbW
  type Foldl a_aZc6 a_aZc7 a_aZc8 = Foldl_6989586621679245029 a_aZc6 a_aZc7 a_aZc8
  type Foldl' a_aZcl a_aZcm a_aZcn = Foldl'_6989586621679245044 a_aZcl a_aZcm a_aZcn
  type Foldl1 a_aZcA a_aZcB = Foldl1_6989586621679245058 a_aZcA a_aZcB
  type Foldr a_aZcK a_aZcL a_aZcM = Foldr_6989586621679245069 a_aZcK a_aZcL a_aZcM
  type Foldr' a_aZcZ a_aZd0 a_aZd1 = Foldr'_6989586621679245084 a_aZcZ a_aZd0 a_aZd1
  type Foldr1 a_aZdk a_aZdl = Foldr1_6989586621679245104 a_aZdk a_aZdl
  type Length a_aZdu = Length_6989586621679245113 a_aZdu
  type Maximum a_aZdA = Maximum_6989586621679245119 a_aZdA
  type Minimum a_aZdH = Minimum_6989586621679245126 a_aZdH
  type Null a_aZdO = Null_6989586621679245133 a_aZdO
  type Product a_aZdU = Product_6989586621679245139 a_aZdU
  type Sum a_aZe1 = Sum_6989586621679245146 a_aZe1
  type ToList a_aZe8 = ToList_6989586621679245153 a_aZe8
type Pure_6989586621679245451 :: forall a_iv9m. a_iv9m
                                                -> Identity a_iv9m
type family Pure_6989586621679245451 @a_iv9m (a_aZj1 :: a_iv9m) :: Identity a_iv9m where
  Pure_6989586621679245451 @a_iv9m a_6989586621679245453_aZj4 = Apply IdentitySym0 a_6989586621679245453_aZj4
type TFHelper_6989586621679245461 :: forall a_iv9o
                                            b_iv9p. Identity ((~>) a_iv9o b_iv9p)
                                                    -> Identity a_iv9o -> Identity b_iv9p
type family TFHelper_6989586621679245461 @a_iv9o @b_iv9p (a_aZj9 :: Identity ((~>) a_iv9o b_iv9p)) (a_aZja :: Identity a_iv9o) :: Identity b_iv9p where
  TFHelper_6989586621679245461 @a_iv9o @b_iv9p ('Identity f_aZje) ('Identity x_aZjf) = Apply IdentitySym0 (Apply f_aZje x_aZjf)
type LiftA2_6989586621679245473 :: forall a_iv9s
                                          b_iv9t
                                          c_iv9u. (~>) a_iv9s ((~>) b_iv9t c_iv9u)
                                                  -> Identity a_iv9s
                                                      -> Identity b_iv9t -> Identity c_iv9u
type family LiftA2_6989586621679245473 @a_iv9s @b_iv9t @c_iv9u (a_aZjl :: (~>) a_iv9s ((~>) b_iv9t c_iv9u)) (a_aZjm :: Identity a_iv9s) (a_aZjn :: Identity b_iv9t) :: Identity c_iv9u where
  LiftA2_6989586621679245473 @a_iv9s @b_iv9t @c_iv9u f_aZjs ('Identity x_aZjt) ('Identity y_aZju) = Apply IdentitySym0 (Apply (Apply f_aZjs x_aZjt) y_aZju)
instance PApplicative Identity where
  type Pure a_aZiW = Pure_6989586621679245451 a_aZiW
  type (<*>) a_aZj5 a_aZj6 = TFHelper_6989586621679245461 a_aZj5 a_aZj6
  type LiftA2 a_aZjg a_aZjh a_aZji = LiftA2_6989586621679245473 a_aZjg a_aZjh a_aZji
type TFHelper_6989586621679245631 :: forall a_iv94
                                            b_iv95. Identity a_iv94
                                                    -> (~>) a_iv94 (Identity b_iv95)
                                                        -> Identity b_iv95
type family TFHelper_6989586621679245631 @a_iv94 @b_iv95 (a_aZlT :: Identity a_iv94) (a_aZlU :: (~>) a_iv94 (Identity b_iv95)) :: Identity b_iv95 where
  TFHelper_6989586621679245631 @a_iv94 @b_iv95 ('Identity m_aZlY) k_aZlZ = Apply k_aZlZ m_aZlY
instance PMonad Identity where
  type (>>=) a_aZlP a_aZlQ = TFHelper_6989586621679245631 a_aZlP a_aZlQ
instance SEnum a_aYcj => SEnum (Identity a_aYcj) where
  sSucc (SIdentity (sX :: Sing x_aYHf))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (singFun1 @SuccSym0 sSucc) sX)
  sPred (SIdentity (sX :: Sing x_aYHm))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (singFun1 @PredSym0 sPred) sX)
  sToEnum (sI :: Sing i_aYHt)
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (singFun1 @ToEnumSym0 sToEnum) sI)
  sFromEnum (SIdentity (sX :: Sing x_aYHA))
    = applySing (singFun1 @FromEnumSym0 sFromEnum) sX
  sEnumFromTo
    (SIdentity (sX :: Sing x_aYHK))
    (SIdentity (sY :: Sing y_aYHL))
    = applySing
        (applySing
            (singFun2 @MapSym0 sMap) (singFun1 @IdentitySym0 SIdentity))
        (applySing
            (applySing (singFun2 @EnumFromToSym0 sEnumFromTo) sX) sY)
  sEnumFromThenTo
    (SIdentity (sX :: Sing x_aYHY))
    (SIdentity (sY :: Sing y_aYHZ))
    (SIdentity (sZ :: Sing z_aYI0))
    = applySing
        (applySing
            (singFun2 @MapSym0 sMap) (singFun1 @IdentitySym0 SIdentity))
        (applySing
            (applySing
              (applySing (singFun3 @EnumFromThenToSym0 sEnumFromThenTo) sX) sY)
            sZ)
instance SMonoid a_aYct => SMonoid (Identity a_aYct) where
  sMempty = applySing (singFun1 @IdentitySym0 SIdentity) sMempty
instance SNum a_aYcu => SNum (Identity a_aYcu) where
  (%+)
    (SIdentity (sX :: Sing x_aYKE))
    (SIdentity (sY :: Sing y_aYKF))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (applySing (singFun2 @(+@#@$) (%+)) sX) sY)
  (%-)
    (SIdentity (sX :: Sing x_aYKP))
    (SIdentity (sY :: Sing y_aYKQ))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (applySing (singFun2 @(-@#@$) (%-)) sX) sY)
  (%*)
    (SIdentity (sX :: Sing x_aYL0))
    (SIdentity (sY :: Sing y_aYL1))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (applySing (singFun2 @(*@#@$) (%*)) sX) sY)
  sNegate (SIdentity (sX :: Sing x_aYL8))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (singFun1 @NegateSym0 sNegate) sX)
  sAbs (SIdentity (sX :: Sing x_aYLf))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (singFun1 @AbsSym0 sAbs) sX)
  sSignum (SIdentity (sX :: Sing x_aYLm))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (singFun1 @SignumSym0 sSignum) sX)
  sFromInteger (sN :: Sing n_aYLt)
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (singFun1 @FromIntegerSym0 sFromInteger) sN)
instance SSemigroup a_aYcF => SSemigroup (Identity a_aYcF) where
  (%<>)
    (SIdentity (sX :: Sing x_aYM7))
    (SIdentity (sY :: Sing y_aYM8))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing (applySing (singFun2 @(<>@#@$) (%<>)) sX) sY)
instance SShow a_aYcI => SShow (Identity a_aYcI) where
  sShowsPrec
    (sD :: Sing d_aYSH)
    (SIdentity (sX :: Sing x_aYSI))
    (sA_6989586621679243814 :: Sing a_6989586621679243814_aYSJ)
    = applySing
        (applySing
            (applySing
              (singFun2 @($@#@$) (%$))
              (applySing
                  (singFun3 @ShowParenSym0 sShowParen)
                  (applySing
                    (applySing (singFun2 @(>@#@$) (%>)) sD)
                    (sFromInteger (sing :: Sing 10)))))
            (applySing
              (applySing
                  (singFun3 @(.@#@$) (%.))
                  (applySing
                    (singFun2 @ShowStringSym0 sShowString) (sing :: Sing "Identity ")))
              (applySing
                  (applySing
                    (singFun3 @ShowsPrecSym0 sShowsPrec)
                    (sFromInteger (sing :: Sing 11)))
                  sX)))
        sA_6989586621679243814
instance SFunctor Identity where
  sFmap
    (_sf_6989586621679243015 :: Sing _f_6989586621679243015_aYVy)
    (SIdentity (sA_6989586621679243019 :: Sing a_6989586621679243019_aYVz))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing _sf_6989586621679243015 sA_6989586621679243019)
  (%<$)
    (_sz_6989586621679243017 :: Sing _z_6989586621679243017_aYVJ)
    (SIdentity (sA_6989586621679243021 :: Sing a_6989586621679243021_aYVK))
    = applySing
        (singFun1 @IdentitySym0 SIdentity)
        (applySing
            (singFun1
              @(LamCases_6989586621679244013Sym0 _z_6989586621679243017_aYVJ a_6989586621679243021_aYVK)
              (\cases _ -> _sz_6989586621679243017))
            sA_6989586621679243021)
instance SFoldable Identity where
  sFoldMap (sF :: Sing f_aZbT) (SIdentity (sX :: Sing x_aZbU))
    = applySing sF sX
  sElem (sX :: Sing x_aZc4) (SIdentity (sY :: Sing y_aZc5))
    = applySing (applySing (singFun2 @(==@#@$) (%==)) sX) sY
  sFoldl
    (sF :: Sing f_aZci)
    (sZ :: Sing z_aZcj)
    (SIdentity (sX :: Sing x_aZck))
    = applySing (applySing sF sZ) sX
  sFoldl'
    (sF :: Sing f_aZcx)
    (sZ :: Sing z_aZcy)
    (SIdentity (sX :: Sing x_aZcz))
    = applySing (applySing sF sZ) sX
  sFoldl1 _ (SIdentity (sX :: Sing x_aZcJ)) = sX
  sFoldr
    (sF :: Sing f_aZcW)
    (sZ :: Sing z_aZcX)
    (SIdentity (sX :: Sing x_aZcY))
    = applySing (applySing sF sX) sZ
  sFoldr'
    (sA_6989586621679245086 :: Sing a_6989586621679245086_aZdh)
    (sA_6989586621679245088 :: Sing a_6989586621679245088_aZdi)
    (sA_6989586621679245090 :: Sing a_6989586621679245090_aZdj)
    = applySing
        (applySing
            (applySing (singFun3 @FoldrSym0 sFoldr) sA_6989586621679245086)
            sA_6989586621679245088)
        sA_6989586621679245090
  sFoldr1 _ (SIdentity (sX :: Sing x_aZdt)) = sX
  sLength _ = sFromInteger (sing :: Sing 1)
  sMaximum (SIdentity (sX :: Sing x_aZdG)) = sX
  sMinimum (SIdentity (sX :: Sing x_aZdN)) = sX
  sNull _ = SFalse
  sProduct (SIdentity (sX :: Sing x_aZe0)) = sX
  sSum (SIdentity (sX :: Sing x_aZe7)) = sX
  sToList (SIdentity (sX :: Sing x_aZee))
    = applySing (applySing (singFun2 @(:@#@$) SCons) sX) SNil
instance SApplicative Identity where
  sPure (sA_6989586621679245453 :: Sing a_6989586621679245453_aZj4)
    = applySing
        (singFun1 @IdentitySym0 SIdentity) sA_6989586621679245453
  (%<*>)
    (SIdentity (sF :: Sing f_aZje))
    (SIdentity (sX :: Sing x_aZjf))
    = applySing (singFun1 @IdentitySym0 SIdentity) (applySing sF sX)
  sLiftA2
    (sF :: Sing f_aZjs)
    (SIdentity (sX :: Sing x_aZjt))
    (SIdentity (sY :: Sing y_aZju))
    = applySing
        (singFun1 @IdentitySym0 SIdentity) (applySing (applySing sF sX) sY)
instance SMonad Identity where
  (%>>=) (SIdentity (sM :: Sing m_aZlY)) (sK :: Sing k_aZlZ)
    = applySing sK sM
