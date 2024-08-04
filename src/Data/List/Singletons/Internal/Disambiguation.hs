{-# LANGUAGE DataKinds #-}

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
-- Module      :  Data.List.Singletons.Internal.Disambiguation
-- Copyright   :  (C) 2016 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Renames a bunch of List functions because singletons can't support qualified
-- names. :(
--
----------------------------------------------------------------------------

module Data.List.Singletons.Internal.Disambiguation where

import Data.Eq.Singletons
import Data.List ( inits, insert, intersperse, isPrefixOf
                 , nubBy, partition, sort, sortBy, tails, transpose )
import Data.List.Singletons.Internal
import Data.Ord.Singletons
import Data.Singletons.Base.Instances
import Data.Singletons.TH
import GHC.Base.Singletons
import GHC.Num.Singletons
import GHC.TypeLits
import Data.Foldable (foldl')
import Data.Kind (Type)

listlast_a8vX :: [a_a8vo] -> a_a8vo
listlast_a8vX = last
listinit_a8vW :: [a_a8vn] -> [a_a8vn]
listinit_a8vW = init
listsort_a8vV :: Ord a_a8vm => [a_a8vm] -> [a_a8vm]
listsort_a8vV = sort
listinits_a8vU :: [a_a8vl] -> [[a_a8vl]]
listinits_a8vU = inits
listtails_a8vT :: [a_a8vk] -> [[a_a8vk]]
listtails_a8vT = tails
listinsert_a8vS :: Ord a_a8vj => a_a8vj -> [a_a8vj] -> [a_a8vj]
listinsert_a8vS = insert
listscanl_a8vR ::
  (b_a8vh -> a_a8vi -> b_a8vh) -> b_a8vh -> [a_a8vi] -> [b_a8vh]
listscanl_a8vR = scanl
listscanr_a8vQ ::
  (a_a8vf -> b_a8vg -> b_a8vg) -> b_a8vg -> [a_a8vf] -> [b_a8vg]
listscanr_a8vQ = scanr
listscanr1_a8vP ::
  (a_a8ve -> a_a8ve -> a_a8ve) -> [a_a8ve] -> [a_a8ve]
listscanr1_a8vP = scanr1
listintersperse_a8vO :: a_a8vd -> [a_a8vd] -> [a_a8vd]
listintersperse_a8vO = intersperse
listreverse_a8vN :: [a_a8vc] -> [a_a8vc]
listreverse_a8vN = reverse
listtakeWhile_a8vM :: (a_a8vb -> Bool) -> [a_a8vb] -> [a_a8vb]
listtakeWhile_a8vM = takeWhile
listdropWhile_a8vL :: (a_a8va -> Bool) -> [a_a8va] -> [a_a8va]
listdropWhile_a8vL = dropWhile
listspan_a8vK ::
  (a_a8v9 -> Bool) -> [a_a8v9] -> ([a_a8v9], [a_a8v9])
listspan_a8vK = span
listfilter_a8vJ :: (a_a8v8 -> Bool) -> [a_a8v8] -> [a_a8v8]
listfilter_a8vJ = filter
listpartition_a8vI ::
  (a_a8v7 -> Bool) -> [a_a8v7] -> ([a_a8v7], [a_a8v7])
listpartition_a8vI = partition
listsortBy_a8vH ::
  (a_a8v6 -> a_a8v6 -> Ordering) -> [a_a8v6] -> [a_a8v6]
listsortBy_a8vH = sortBy
listisPrefixOf_a8vG :: Eq a_a8v5 => [a_a8v5] -> [a_a8v5] -> Bool
listisPrefixOf_a8vG = isPrefixOf
listzip_a8vF :: [a_a8v3] -> [b_a8v4] -> [(a_a8v3, b_a8v4)]
listzip_a8vF = zip
listzipWith_a8vE ::
  (a_a8v0 -> b_a8v1 -> c_a8v2) -> [a_a8v0] -> [b_a8v1] -> [c_a8v2]
listzipWith_a8vE = zipWith
listnubBy_a8vD ::
  (a_a8uZ -> a_a8uZ -> Bool) -> [a_a8uZ] -> [a_a8uZ]
listnubBy_a8vD = nubBy
listtranspose_a8vC :: [[a_a8uY]] -> [[a_a8uY]]
listtranspose_a8vC = transpose
listunzip_a8vB :: [(a_a8uW, b_a8uX)] -> ([a_a8uW], [b_a8uX])
listunzip_a8vB = unzip
listmap_a8vA :: (a_a8uU -> b_a8uV) -> [a_a8uU] -> [b_a8uV]
listmap_a8vA = map
listelem_a8vz :: Eq a_a8uT => a_a8uT -> [a_a8uT] -> Bool
listelem_a8vz = elem
listfoldl_a8vy ::
  (b_a8uR -> a_a8uS -> b_a8uR) -> b_a8uR -> [a_a8uS] -> b_a8uR
listfoldl_a8vy = foldl
listfoldl'_a8vx ::
  (b_a8uP -> a_a8uQ -> b_a8uP) -> b_a8uP -> [a_a8uQ] -> b_a8uP
listfoldl'_a8vx = foldl'
listfoldl1_a8vw ::
  (a_a8uO -> a_a8uO -> a_a8uO) -> [a_a8uO] -> a_a8uO
listfoldl1_a8vw = foldl1
listfoldr_a8vv ::
  (a_a8uM -> b_a8uN -> b_a8uN) -> b_a8uN -> [a_a8uM] -> b_a8uN
listfoldr_a8vv = foldr
listfoldr1_a8vu ::
  (a_a8uL -> a_a8uL -> a_a8uL) -> [a_a8uL] -> a_a8uL
listfoldr1_a8vu = foldr1
listmaximum_a8vt :: Ord a_a8uK => [a_a8uK] -> a_a8uK
listmaximum_a8vt = maximum
listminimum_a8vs :: Ord a_a8uJ => [a_a8uJ] -> a_a8uJ
listminimum_a8vs = minimum
listnull_a8vr :: [a_a8uI] -> Bool
listnull_a8vr = null
listproduct_a8vq :: Num a_a8uH => [a_a8uH] -> a_a8uH
listproduct_a8vq = product
listsum_a8vp :: Num a_a8uG => [a_a8uG] -> a_a8uG
listsum_a8vp = sum
type ListsumSym0 :: (~>) [a_a8uG] a_a8uG
data ListsumSym0 :: (~>) [a_a8uG] a_a8uG
  where
    ListsumSym0KindInference :: SameKind (Apply ListsumSym0 arg_a9cQ) (ListsumSym1 arg_a9cQ) =>
                                ListsumSym0 a6989586621679045185
type instance Apply @[a_a8uG] @a_a8uG ListsumSym0 a6989586621679045185 = Listsum a6989586621679045185
instance SuppressUnusedWarnings ListsumSym0 where
  suppressUnusedWarnings = snd ((,) ListsumSym0KindInference ())
type ListsumSym1 :: [a_a8uG] -> a_a8uG
type family ListsumSym1 @a_a8uG (a6989586621679045185 :: [a_a8uG]) :: a_a8uG where
  ListsumSym1 a6989586621679045185 = Listsum a6989586621679045185
type ListproductSym0 :: (~>) [a_a8uH] a_a8uH
data ListproductSym0 :: (~>) [a_a8uH] a_a8uH
  where
    ListproductSym0KindInference :: SameKind (Apply ListproductSym0 arg_a9cW) (ListproductSym1 arg_a9cW) =>
                                    ListproductSym0 a6989586621679045191
type instance Apply @[a_a8uH] @a_a8uH ListproductSym0 a6989586621679045191 = Listproduct a6989586621679045191
instance SuppressUnusedWarnings ListproductSym0 where
  suppressUnusedWarnings = snd ((,) ListproductSym0KindInference ())
type ListproductSym1 :: [a_a8uH] -> a_a8uH
type family ListproductSym1 @a_a8uH (a6989586621679045191 :: [a_a8uH]) :: a_a8uH where
  ListproductSym1 a6989586621679045191 = Listproduct a6989586621679045191
type ListnullSym0 :: (~>) [a_a8uI] Bool
data ListnullSym0 :: (~>) [a_a8uI] Bool
  where
    ListnullSym0KindInference :: SameKind (Apply ListnullSym0 arg_a9d2) (ListnullSym1 arg_a9d2) =>
                                  ListnullSym0 a6989586621679045197
type instance Apply @[a_a8uI] @Bool ListnullSym0 a6989586621679045197 = Listnull a6989586621679045197
instance SuppressUnusedWarnings ListnullSym0 where
  suppressUnusedWarnings = snd ((,) ListnullSym0KindInference ())
type ListnullSym1 :: [a_a8uI] -> Bool
type family ListnullSym1 @a_a8uI (a6989586621679045197 :: [a_a8uI]) :: Bool where
  ListnullSym1 a6989586621679045197 = Listnull a6989586621679045197
type ListminimumSym0 :: (~>) [a_a8uJ] a_a8uJ
data ListminimumSym0 :: (~>) [a_a8uJ] a_a8uJ
  where
    ListminimumSym0KindInference :: SameKind (Apply ListminimumSym0 arg_a9d8) (ListminimumSym1 arg_a9d8) =>
                                    ListminimumSym0 a6989586621679045203
type instance Apply @[a_a8uJ] @a_a8uJ ListminimumSym0 a6989586621679045203 = Listminimum a6989586621679045203
instance SuppressUnusedWarnings ListminimumSym0 where
  suppressUnusedWarnings = snd ((,) ListminimumSym0KindInference ())
type ListminimumSym1 :: [a_a8uJ] -> a_a8uJ
type family ListminimumSym1 @a_a8uJ (a6989586621679045203 :: [a_a8uJ]) :: a_a8uJ where
  ListminimumSym1 a6989586621679045203 = Listminimum a6989586621679045203
type ListmaximumSym0 :: (~>) [a_a8uK] a_a8uK
data ListmaximumSym0 :: (~>) [a_a8uK] a_a8uK
  where
    ListmaximumSym0KindInference :: SameKind (Apply ListmaximumSym0 arg_a9de) (ListmaximumSym1 arg_a9de) =>
                                    ListmaximumSym0 a6989586621679045209
type instance Apply @[a_a8uK] @a_a8uK ListmaximumSym0 a6989586621679045209 = Listmaximum a6989586621679045209
instance SuppressUnusedWarnings ListmaximumSym0 where
  suppressUnusedWarnings = snd ((,) ListmaximumSym0KindInference ())
type ListmaximumSym1 :: [a_a8uK] -> a_a8uK
type family ListmaximumSym1 @a_a8uK (a6989586621679045209 :: [a_a8uK]) :: a_a8uK where
  ListmaximumSym1 a6989586621679045209 = Listmaximum a6989586621679045209
type Listfoldr1Sym0 :: (~>) ((~>) a_a8uL ((~>) a_a8uL a_a8uL)) ((~>) [a_a8uL] a_a8uL)
data Listfoldr1Sym0 :: (~>) ((~>) a_a8uL ((~>) a_a8uL a_a8uL)) ((~>) [a_a8uL] a_a8uL)
  where
    Listfoldr1Sym0KindInference :: SameKind (Apply Listfoldr1Sym0 arg_a9dn) (Listfoldr1Sym1 arg_a9dn) =>
                                    Listfoldr1Sym0 a6989586621679045218
type instance Apply @((~>) a_a8uL ((~>) a_a8uL a_a8uL)) @((~>) [a_a8uL] a_a8uL) Listfoldr1Sym0 a6989586621679045218 = Listfoldr1Sym1 a6989586621679045218
instance SuppressUnusedWarnings Listfoldr1Sym0 where
  suppressUnusedWarnings = snd ((,) Listfoldr1Sym0KindInference ())
type Listfoldr1Sym1 :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)
                        -> (~>) [a_a8uL] a_a8uL
data Listfoldr1Sym1 (a6989586621679045218 :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)) :: (~>) [a_a8uL] a_a8uL
  where
    Listfoldr1Sym1KindInference :: SameKind (Apply (Listfoldr1Sym1 a6989586621679045218) arg_a9dn) (Listfoldr1Sym2 a6989586621679045218 arg_a9dn) =>
                                    Listfoldr1Sym1 a6989586621679045218 a6989586621679045219
type instance Apply @[a_a8uL] @a_a8uL (Listfoldr1Sym1 a6989586621679045218) a6989586621679045219 = Listfoldr1 a6989586621679045218 a6989586621679045219
instance SuppressUnusedWarnings (Listfoldr1Sym1 a6989586621679045218) where
  suppressUnusedWarnings = snd ((,) Listfoldr1Sym1KindInference ())
type Listfoldr1Sym2 :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)
                        -> [a_a8uL] -> a_a8uL
type family Listfoldr1Sym2 @a_a8uL (a6989586621679045218 :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)) (a6989586621679045219 :: [a_a8uL]) :: a_a8uL where
  Listfoldr1Sym2 a6989586621679045218 a6989586621679045219 = Listfoldr1 a6989586621679045218 a6989586621679045219
type ListfoldrSym0 :: (~>) ((~>) a_a8uM ((~>) b_a8uN b_a8uN)) ((~>) b_a8uN ((~>) [a_a8uM] b_a8uN))
data ListfoldrSym0 :: (~>) ((~>) a_a8uM ((~>) b_a8uN b_a8uN)) ((~>) b_a8uN ((~>) [a_a8uM] b_a8uN))
  where
    ListfoldrSym0KindInference :: SameKind (Apply ListfoldrSym0 arg_a9dB) (ListfoldrSym1 arg_a9dB) =>
                                  ListfoldrSym0 a6989586621679045232
type instance Apply @((~>) a_a8uM ((~>) b_a8uN b_a8uN)) @((~>) b_a8uN ((~>) [a_a8uM] b_a8uN)) ListfoldrSym0 a6989586621679045232 = ListfoldrSym1 a6989586621679045232
instance SuppressUnusedWarnings ListfoldrSym0 where
  suppressUnusedWarnings = snd ((,) ListfoldrSym0KindInference ())
type ListfoldrSym1 :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)
                      -> (~>) b_a8uN ((~>) [a_a8uM] b_a8uN)
data ListfoldrSym1 (a6989586621679045232 :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) :: (~>) b_a8uN ((~>) [a_a8uM] b_a8uN)
  where
    ListfoldrSym1KindInference :: SameKind (Apply (ListfoldrSym1 a6989586621679045232) arg_a9dB) (ListfoldrSym2 a6989586621679045232 arg_a9dB) =>
                                  ListfoldrSym1 a6989586621679045232 a6989586621679045233
type instance Apply @b_a8uN @((~>) [a_a8uM] b_a8uN) (ListfoldrSym1 a6989586621679045232) a6989586621679045233 = ListfoldrSym2 a6989586621679045232 a6989586621679045233
instance SuppressUnusedWarnings (ListfoldrSym1 a6989586621679045232) where
  suppressUnusedWarnings = snd ((,) ListfoldrSym1KindInference ())
type ListfoldrSym2 :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)
                      -> b_a8uN -> (~>) [a_a8uM] b_a8uN
data ListfoldrSym2 (a6989586621679045232 :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) (a6989586621679045233 :: b_a8uN) :: (~>) [a_a8uM] b_a8uN
  where
    ListfoldrSym2KindInference :: SameKind (Apply (ListfoldrSym2 a6989586621679045232 a6989586621679045233) arg_a9dB) (ListfoldrSym3 a6989586621679045232 a6989586621679045233 arg_a9dB) =>
                                  ListfoldrSym2 a6989586621679045232 a6989586621679045233 a6989586621679045234
type instance Apply @[a_a8uM] @b_a8uN (ListfoldrSym2 a6989586621679045232 a6989586621679045233) a6989586621679045234 = Listfoldr a6989586621679045232 a6989586621679045233 a6989586621679045234
instance SuppressUnusedWarnings (ListfoldrSym2 a6989586621679045232 a6989586621679045233) where
  suppressUnusedWarnings = snd ((,) ListfoldrSym2KindInference ())
type ListfoldrSym3 :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)
                      -> b_a8uN -> [a_a8uM] -> b_a8uN
type family ListfoldrSym3 @a_a8uM @b_a8uN (a6989586621679045232 :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) (a6989586621679045233 :: b_a8uN) (a6989586621679045234 :: [a_a8uM]) :: b_a8uN where
  ListfoldrSym3 a6989586621679045232 a6989586621679045233 a6989586621679045234 = Listfoldr a6989586621679045232 a6989586621679045233 a6989586621679045234
type Listfoldl1Sym0 :: (~>) ((~>) a_a8uO ((~>) a_a8uO a_a8uO)) ((~>) [a_a8uO] a_a8uO)
data Listfoldl1Sym0 :: (~>) ((~>) a_a8uO ((~>) a_a8uO a_a8uO)) ((~>) [a_a8uO] a_a8uO)
  where
    Listfoldl1Sym0KindInference :: SameKind (Apply Listfoldl1Sym0 arg_a9dO) (Listfoldl1Sym1 arg_a9dO) =>
                                    Listfoldl1Sym0 a6989586621679045245
type instance Apply @((~>) a_a8uO ((~>) a_a8uO a_a8uO)) @((~>) [a_a8uO] a_a8uO) Listfoldl1Sym0 a6989586621679045245 = Listfoldl1Sym1 a6989586621679045245
instance SuppressUnusedWarnings Listfoldl1Sym0 where
  suppressUnusedWarnings = snd ((,) Listfoldl1Sym0KindInference ())
type Listfoldl1Sym1 :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)
                        -> (~>) [a_a8uO] a_a8uO
data Listfoldl1Sym1 (a6989586621679045245 :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)) :: (~>) [a_a8uO] a_a8uO
  where
    Listfoldl1Sym1KindInference :: SameKind (Apply (Listfoldl1Sym1 a6989586621679045245) arg_a9dO) (Listfoldl1Sym2 a6989586621679045245 arg_a9dO) =>
                                    Listfoldl1Sym1 a6989586621679045245 a6989586621679045246
type instance Apply @[a_a8uO] @a_a8uO (Listfoldl1Sym1 a6989586621679045245) a6989586621679045246 = Listfoldl1 a6989586621679045245 a6989586621679045246
instance SuppressUnusedWarnings (Listfoldl1Sym1 a6989586621679045245) where
  suppressUnusedWarnings = snd ((,) Listfoldl1Sym1KindInference ())
type Listfoldl1Sym2 :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)
                        -> [a_a8uO] -> a_a8uO
type family Listfoldl1Sym2 @a_a8uO (a6989586621679045245 :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)) (a6989586621679045246 :: [a_a8uO]) :: a_a8uO where
  Listfoldl1Sym2 a6989586621679045245 a6989586621679045246 = Listfoldl1 a6989586621679045245 a6989586621679045246
type Listfoldl'Sym0 :: (~>) ((~>) b_a8uP ((~>) a_a8uQ b_a8uP)) ((~>) b_a8uP ((~>) [a_a8uQ] b_a8uP))
data Listfoldl'Sym0 :: (~>) ((~>) b_a8uP ((~>) a_a8uQ b_a8uP)) ((~>) b_a8uP ((~>) [a_a8uQ] b_a8uP))
  where
    Listfoldl'Sym0KindInference :: SameKind (Apply Listfoldl'Sym0 arg_a9e2) (Listfoldl'Sym1 arg_a9e2) =>
                                    Listfoldl'Sym0 a6989586621679045259
type instance Apply @((~>) b_a8uP ((~>) a_a8uQ b_a8uP)) @((~>) b_a8uP ((~>) [a_a8uQ] b_a8uP)) Listfoldl'Sym0 a6989586621679045259 = Listfoldl'Sym1 a6989586621679045259
instance SuppressUnusedWarnings Listfoldl'Sym0 where
  suppressUnusedWarnings = snd ((,) Listfoldl'Sym0KindInference ())
type Listfoldl'Sym1 :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)
                        -> (~>) b_a8uP ((~>) [a_a8uQ] b_a8uP)
data Listfoldl'Sym1 (a6989586621679045259 :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) :: (~>) b_a8uP ((~>) [a_a8uQ] b_a8uP)
  where
    Listfoldl'Sym1KindInference :: SameKind (Apply (Listfoldl'Sym1 a6989586621679045259) arg_a9e2) (Listfoldl'Sym2 a6989586621679045259 arg_a9e2) =>
                                    Listfoldl'Sym1 a6989586621679045259 a6989586621679045260
type instance Apply @b_a8uP @((~>) [a_a8uQ] b_a8uP) (Listfoldl'Sym1 a6989586621679045259) a6989586621679045260 = Listfoldl'Sym2 a6989586621679045259 a6989586621679045260
instance SuppressUnusedWarnings (Listfoldl'Sym1 a6989586621679045259) where
  suppressUnusedWarnings = snd ((,) Listfoldl'Sym1KindInference ())
type Listfoldl'Sym2 :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)
                        -> b_a8uP -> (~>) [a_a8uQ] b_a8uP
data Listfoldl'Sym2 (a6989586621679045259 :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) (a6989586621679045260 :: b_a8uP) :: (~>) [a_a8uQ] b_a8uP
  where
    Listfoldl'Sym2KindInference :: SameKind (Apply (Listfoldl'Sym2 a6989586621679045259 a6989586621679045260) arg_a9e2) (Listfoldl'Sym3 a6989586621679045259 a6989586621679045260 arg_a9e2) =>
                                    Listfoldl'Sym2 a6989586621679045259 a6989586621679045260 a6989586621679045261
type instance Apply @[a_a8uQ] @b_a8uP (Listfoldl'Sym2 a6989586621679045259 a6989586621679045260) a6989586621679045261 = Listfoldl' a6989586621679045259 a6989586621679045260 a6989586621679045261
instance SuppressUnusedWarnings (Listfoldl'Sym2 a6989586621679045259 a6989586621679045260) where
  suppressUnusedWarnings = snd ((,) Listfoldl'Sym2KindInference ())
type Listfoldl'Sym3 :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)
                        -> b_a8uP -> [a_a8uQ] -> b_a8uP
type family Listfoldl'Sym3 @b_a8uP @a_a8uQ (a6989586621679045259 :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) (a6989586621679045260 :: b_a8uP) (a6989586621679045261 :: [a_a8uQ]) :: b_a8uP where
  Listfoldl'Sym3 a6989586621679045259 a6989586621679045260 a6989586621679045261 = Listfoldl' a6989586621679045259 a6989586621679045260 a6989586621679045261
type ListfoldlSym0 :: (~>) ((~>) b_a8uR ((~>) a_a8uS b_a8uR)) ((~>) b_a8uR ((~>) [a_a8uS] b_a8uR))
data ListfoldlSym0 :: (~>) ((~>) b_a8uR ((~>) a_a8uS b_a8uR)) ((~>) b_a8uR ((~>) [a_a8uS] b_a8uR))
  where
    ListfoldlSym0KindInference :: SameKind (Apply ListfoldlSym0 arg_a9ei) (ListfoldlSym1 arg_a9ei) =>
                                  ListfoldlSym0 a6989586621679045275
type instance Apply @((~>) b_a8uR ((~>) a_a8uS b_a8uR)) @((~>) b_a8uR ((~>) [a_a8uS] b_a8uR)) ListfoldlSym0 a6989586621679045275 = ListfoldlSym1 a6989586621679045275
instance SuppressUnusedWarnings ListfoldlSym0 where
  suppressUnusedWarnings = snd ((,) ListfoldlSym0KindInference ())
type ListfoldlSym1 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)
                      -> (~>) b_a8uR ((~>) [a_a8uS] b_a8uR)
data ListfoldlSym1 (a6989586621679045275 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) :: (~>) b_a8uR ((~>) [a_a8uS] b_a8uR)
  where
    ListfoldlSym1KindInference :: SameKind (Apply (ListfoldlSym1 a6989586621679045275) arg_a9ei) (ListfoldlSym2 a6989586621679045275 arg_a9ei) =>
                                  ListfoldlSym1 a6989586621679045275 a6989586621679045276
type instance Apply @b_a8uR @((~>) [a_a8uS] b_a8uR) (ListfoldlSym1 a6989586621679045275) a6989586621679045276 = ListfoldlSym2 a6989586621679045275 a6989586621679045276
instance SuppressUnusedWarnings (ListfoldlSym1 a6989586621679045275) where
  suppressUnusedWarnings = snd ((,) ListfoldlSym1KindInference ())
type ListfoldlSym2 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)
                      -> b_a8uR -> (~>) [a_a8uS] b_a8uR
data ListfoldlSym2 (a6989586621679045275 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) (a6989586621679045276 :: b_a8uR) :: (~>) [a_a8uS] b_a8uR
  where
    ListfoldlSym2KindInference :: SameKind (Apply (ListfoldlSym2 a6989586621679045275 a6989586621679045276) arg_a9ei) (ListfoldlSym3 a6989586621679045275 a6989586621679045276 arg_a9ei) =>
                                  ListfoldlSym2 a6989586621679045275 a6989586621679045276 a6989586621679045277
type instance Apply @[a_a8uS] @b_a8uR (ListfoldlSym2 a6989586621679045275 a6989586621679045276) a6989586621679045277 = Listfoldl a6989586621679045275 a6989586621679045276 a6989586621679045277
instance SuppressUnusedWarnings (ListfoldlSym2 a6989586621679045275 a6989586621679045276) where
  suppressUnusedWarnings = snd ((,) ListfoldlSym2KindInference ())
type ListfoldlSym3 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)
                      -> b_a8uR -> [a_a8uS] -> b_a8uR
type family ListfoldlSym3 @b_a8uR @a_a8uS (a6989586621679045275 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) (a6989586621679045276 :: b_a8uR) (a6989586621679045277 :: [a_a8uS]) :: b_a8uR where
  ListfoldlSym3 a6989586621679045275 a6989586621679045276 a6989586621679045277 = Listfoldl a6989586621679045275 a6989586621679045276 a6989586621679045277
type ListelemSym0 :: (~>) a_a8uT ((~>) [a_a8uT] Bool)
data ListelemSym0 :: (~>) a_a8uT ((~>) [a_a8uT] Bool)
  where
    ListelemSym0KindInference :: SameKind (Apply ListelemSym0 arg_a9ev) (ListelemSym1 arg_a9ev) =>
                                  ListelemSym0 a6989586621679045288
type instance Apply @a_a8uT @((~>) [a_a8uT] Bool) ListelemSym0 a6989586621679045288 = ListelemSym1 a6989586621679045288
instance SuppressUnusedWarnings ListelemSym0 where
  suppressUnusedWarnings = snd ((,) ListelemSym0KindInference ())
type ListelemSym1 :: a_a8uT -> (~>) [a_a8uT] Bool
data ListelemSym1 (a6989586621679045288 :: a_a8uT) :: (~>) [a_a8uT] Bool
  where
    ListelemSym1KindInference :: SameKind (Apply (ListelemSym1 a6989586621679045288) arg_a9ev) (ListelemSym2 a6989586621679045288 arg_a9ev) =>
                                  ListelemSym1 a6989586621679045288 a6989586621679045289
type instance Apply @[a_a8uT] @Bool (ListelemSym1 a6989586621679045288) a6989586621679045289 = Listelem a6989586621679045288 a6989586621679045289
instance SuppressUnusedWarnings (ListelemSym1 a6989586621679045288) where
  suppressUnusedWarnings = snd ((,) ListelemSym1KindInference ())
type ListelemSym2 :: a_a8uT -> [a_a8uT] -> Bool
type family ListelemSym2 @a_a8uT (a6989586621679045288 :: a_a8uT) (a6989586621679045289 :: [a_a8uT]) :: Bool where
  ListelemSym2 a6989586621679045288 a6989586621679045289 = Listelem a6989586621679045288 a6989586621679045289
type ListmapSym0 :: (~>) ((~>) a_a8uU b_a8uV) ((~>) [a_a8uU] [b_a8uV])
data ListmapSym0 :: (~>) ((~>) a_a8uU b_a8uV) ((~>) [a_a8uU] [b_a8uV])
  where
    ListmapSym0KindInference :: SameKind (Apply ListmapSym0 arg_a9eG) (ListmapSym1 arg_a9eG) =>
                                ListmapSym0 a6989586621679045299
type instance Apply @((~>) a_a8uU b_a8uV) @((~>) [a_a8uU] [b_a8uV]) ListmapSym0 a6989586621679045299 = ListmapSym1 a6989586621679045299
instance SuppressUnusedWarnings ListmapSym0 where
  suppressUnusedWarnings = snd ((,) ListmapSym0KindInference ())
type ListmapSym1 :: (~>) a_a8uU b_a8uV -> (~>) [a_a8uU] [b_a8uV]
data ListmapSym1 (a6989586621679045299 :: (~>) a_a8uU b_a8uV) :: (~>) [a_a8uU] [b_a8uV]
  where
    ListmapSym1KindInference :: SameKind (Apply (ListmapSym1 a6989586621679045299) arg_a9eG) (ListmapSym2 a6989586621679045299 arg_a9eG) =>
                                ListmapSym1 a6989586621679045299 a6989586621679045300
type instance Apply @[a_a8uU] @[b_a8uV] (ListmapSym1 a6989586621679045299) a6989586621679045300 = Listmap a6989586621679045299 a6989586621679045300
instance SuppressUnusedWarnings (ListmapSym1 a6989586621679045299) where
  suppressUnusedWarnings = snd ((,) ListmapSym1KindInference ())
type ListmapSym2 :: (~>) a_a8uU b_a8uV -> [a_a8uU] -> [b_a8uV]
type family ListmapSym2 @a_a8uU @b_a8uV (a6989586621679045299 :: (~>) a_a8uU b_a8uV) (a6989586621679045300 :: [a_a8uU]) :: [b_a8uV] where
  ListmapSym2 a6989586621679045299 a6989586621679045300 = Listmap a6989586621679045299 a6989586621679045300
type ListunzipSym0 :: (~>) [(a_a8uW, b_a8uX)] ([a_a8uW], [b_a8uX])
data ListunzipSym0 :: (~>) [(a_a8uW, b_a8uX)] ([a_a8uW], [b_a8uX])
  where
    ListunzipSym0KindInference :: SameKind (Apply ListunzipSym0 arg_a9eO) (ListunzipSym1 arg_a9eO) =>
                                  ListunzipSym0 a6989586621679045307
type instance Apply @[(a_a8uW, b_a8uX)] @([a_a8uW],
                                          [b_a8uX]) ListunzipSym0 a6989586621679045307 = Listunzip a6989586621679045307
instance SuppressUnusedWarnings ListunzipSym0 where
  suppressUnusedWarnings = snd ((,) ListunzipSym0KindInference ())
type ListunzipSym1 :: [(a_a8uW, b_a8uX)] -> ([a_a8uW], [b_a8uX])
type family ListunzipSym1 @a_a8uW @b_a8uX (a6989586621679045307 :: [(a_a8uW,
                                                                      b_a8uX)]) :: ([a_a8uW],
                                                                                    [b_a8uX]) where
  ListunzipSym1 a6989586621679045307 = Listunzip a6989586621679045307
type ListtransposeSym0 :: (~>) [[a_a8uY]] [[a_a8uY]]
data ListtransposeSym0 :: (~>) [[a_a8uY]] [[a_a8uY]]
  where
    ListtransposeSym0KindInference :: SameKind (Apply ListtransposeSym0 arg_a9eU) (ListtransposeSym1 arg_a9eU) =>
                                      ListtransposeSym0 a6989586621679045313
type instance Apply @[[a_a8uY]] @[[a_a8uY]] ListtransposeSym0 a6989586621679045313 = Listtranspose a6989586621679045313
instance SuppressUnusedWarnings ListtransposeSym0 where
  suppressUnusedWarnings
    = snd ((,) ListtransposeSym0KindInference ())
type ListtransposeSym1 :: [[a_a8uY]] -> [[a_a8uY]]
type family ListtransposeSym1 @a_a8uY (a6989586621679045313 :: [[a_a8uY]]) :: [[a_a8uY]] where
  ListtransposeSym1 a6989586621679045313 = Listtranspose a6989586621679045313
type ListnubBySym0 :: (~>) ((~>) a_a8uZ ((~>) a_a8uZ Bool)) ((~>) [a_a8uZ] [a_a8uZ])
data ListnubBySym0 :: (~>) ((~>) a_a8uZ ((~>) a_a8uZ Bool)) ((~>) [a_a8uZ] [a_a8uZ])
  where
    ListnubBySym0KindInference :: SameKind (Apply ListnubBySym0 arg_a9f3) (ListnubBySym1 arg_a9f3) =>
                                  ListnubBySym0 a6989586621679045322
type instance Apply @((~>) a_a8uZ ((~>) a_a8uZ Bool)) @((~>) [a_a8uZ] [a_a8uZ]) ListnubBySym0 a6989586621679045322 = ListnubBySym1 a6989586621679045322
instance SuppressUnusedWarnings ListnubBySym0 where
  suppressUnusedWarnings = snd ((,) ListnubBySym0KindInference ())
type ListnubBySym1 :: (~>) a_a8uZ ((~>) a_a8uZ Bool)
                      -> (~>) [a_a8uZ] [a_a8uZ]
data ListnubBySym1 (a6989586621679045322 :: (~>) a_a8uZ ((~>) a_a8uZ Bool)) :: (~>) [a_a8uZ] [a_a8uZ]
  where
    ListnubBySym1KindInference :: SameKind (Apply (ListnubBySym1 a6989586621679045322) arg_a9f3) (ListnubBySym2 a6989586621679045322 arg_a9f3) =>
                                  ListnubBySym1 a6989586621679045322 a6989586621679045323
type instance Apply @[a_a8uZ] @[a_a8uZ] (ListnubBySym1 a6989586621679045322) a6989586621679045323 = ListnubBy a6989586621679045322 a6989586621679045323
instance SuppressUnusedWarnings (ListnubBySym1 a6989586621679045322) where
  suppressUnusedWarnings = snd ((,) ListnubBySym1KindInference ())
type ListnubBySym2 :: (~>) a_a8uZ ((~>) a_a8uZ Bool)
                      -> [a_a8uZ] -> [a_a8uZ]
type family ListnubBySym2 @a_a8uZ (a6989586621679045322 :: (~>) a_a8uZ ((~>) a_a8uZ Bool)) (a6989586621679045323 :: [a_a8uZ]) :: [a_a8uZ] where
  ListnubBySym2 a6989586621679045322 a6989586621679045323 = ListnubBy a6989586621679045322 a6989586621679045323
type ListzipWithSym0 :: (~>) ((~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) ((~>) [a_a8v0] ((~>) [b_a8v1] [c_a8v2]))
data ListzipWithSym0 :: (~>) ((~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) ((~>) [a_a8v0] ((~>) [b_a8v1] [c_a8v2]))
  where
    ListzipWithSym0KindInference :: SameKind (Apply ListzipWithSym0 arg_a9fh) (ListzipWithSym1 arg_a9fh) =>
                                    ListzipWithSym0 a6989586621679045336
type instance Apply @((~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) @((~>) [a_a8v0] ((~>) [b_a8v1] [c_a8v2])) ListzipWithSym0 a6989586621679045336 = ListzipWithSym1 a6989586621679045336
instance SuppressUnusedWarnings ListzipWithSym0 where
  suppressUnusedWarnings = snd ((,) ListzipWithSym0KindInference ())
type ListzipWithSym1 :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)
                        -> (~>) [a_a8v0] ((~>) [b_a8v1] [c_a8v2])
data ListzipWithSym1 (a6989586621679045336 :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) :: (~>) [a_a8v0] ((~>) [b_a8v1] [c_a8v2])
  where
    ListzipWithSym1KindInference :: SameKind (Apply (ListzipWithSym1 a6989586621679045336) arg_a9fh) (ListzipWithSym2 a6989586621679045336 arg_a9fh) =>
                                    ListzipWithSym1 a6989586621679045336 a6989586621679045337
type instance Apply @[a_a8v0] @((~>) [b_a8v1] [c_a8v2]) (ListzipWithSym1 a6989586621679045336) a6989586621679045337 = ListzipWithSym2 a6989586621679045336 a6989586621679045337
instance SuppressUnusedWarnings (ListzipWithSym1 a6989586621679045336) where
  suppressUnusedWarnings = snd ((,) ListzipWithSym1KindInference ())
type ListzipWithSym2 :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)
                        -> [a_a8v0] -> (~>) [b_a8v1] [c_a8v2]
data ListzipWithSym2 (a6989586621679045336 :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) (a6989586621679045337 :: [a_a8v0]) :: (~>) [b_a8v1] [c_a8v2]
  where
    ListzipWithSym2KindInference :: SameKind (Apply (ListzipWithSym2 a6989586621679045336 a6989586621679045337) arg_a9fh) (ListzipWithSym3 a6989586621679045336 a6989586621679045337 arg_a9fh) =>
                                    ListzipWithSym2 a6989586621679045336 a6989586621679045337 a6989586621679045338
type instance Apply @[b_a8v1] @[c_a8v2] (ListzipWithSym2 a6989586621679045336 a6989586621679045337) a6989586621679045338 = ListzipWith a6989586621679045336 a6989586621679045337 a6989586621679045338
instance SuppressUnusedWarnings (ListzipWithSym2 a6989586621679045336 a6989586621679045337) where
  suppressUnusedWarnings = snd ((,) ListzipWithSym2KindInference ())
type ListzipWithSym3 :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)
                        -> [a_a8v0] -> [b_a8v1] -> [c_a8v2]
type family ListzipWithSym3 @a_a8v0 @b_a8v1 @c_a8v2 (a6989586621679045336 :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) (a6989586621679045337 :: [a_a8v0]) (a6989586621679045338 :: [b_a8v1]) :: [c_a8v2] where
  ListzipWithSym3 a6989586621679045336 a6989586621679045337 a6989586621679045338 = ListzipWith a6989586621679045336 a6989586621679045337 a6989586621679045338
type ListzipSym0 :: (~>) [a_a8v3] ((~>) [b_a8v4] [(a_a8v3,
                                                    b_a8v4)])
data ListzipSym0 :: (~>) [a_a8v3] ((~>) [b_a8v4] [(a_a8v3,
                                                    b_a8v4)])
  where
    ListzipSym0KindInference :: SameKind (Apply ListzipSym0 arg_a9fu) (ListzipSym1 arg_a9fu) =>
                                ListzipSym0 a6989586621679045349
type instance Apply @[a_a8v3] @((~>) [b_a8v4] [(a_a8v3,
                                                b_a8v4)]) ListzipSym0 a6989586621679045349 = ListzipSym1 a6989586621679045349
instance SuppressUnusedWarnings ListzipSym0 where
  suppressUnusedWarnings = snd ((,) ListzipSym0KindInference ())
type ListzipSym1 :: [a_a8v3] -> (~>) [b_a8v4] [(a_a8v3, b_a8v4)]
data ListzipSym1 (a6989586621679045349 :: [a_a8v3]) :: (~>) [b_a8v4] [(a_a8v3,
                                                                        b_a8v4)]
  where
    ListzipSym1KindInference :: SameKind (Apply (ListzipSym1 a6989586621679045349) arg_a9fu) (ListzipSym2 a6989586621679045349 arg_a9fu) =>
                                ListzipSym1 a6989586621679045349 a6989586621679045350
type instance Apply @[b_a8v4] @[(a_a8v3,
                                  b_a8v4)] (ListzipSym1 a6989586621679045349) a6989586621679045350 = Listzip a6989586621679045349 a6989586621679045350
instance SuppressUnusedWarnings (ListzipSym1 a6989586621679045349) where
  suppressUnusedWarnings = snd ((,) ListzipSym1KindInference ())
type ListzipSym2 :: [a_a8v3] -> [b_a8v4] -> [(a_a8v3, b_a8v4)]
type family ListzipSym2 @a_a8v3 @b_a8v4 (a6989586621679045349 :: [a_a8v3]) (a6989586621679045350 :: [b_a8v4]) :: [(a_a8v3,
                                                                                                                    b_a8v4)] where
  ListzipSym2 a6989586621679045349 a6989586621679045350 = Listzip a6989586621679045349 a6989586621679045350
type ListisPrefixOfSym0 :: (~>) [a_a8v5] ((~>) [a_a8v5] Bool)
data ListisPrefixOfSym0 :: (~>) [a_a8v5] ((~>) [a_a8v5] Bool)
  where
    ListisPrefixOfSym0KindInference :: SameKind (Apply ListisPrefixOfSym0 arg_a9fF) (ListisPrefixOfSym1 arg_a9fF) =>
                                        ListisPrefixOfSym0 a6989586621679045360
type instance Apply @[a_a8v5] @((~>) [a_a8v5] Bool) ListisPrefixOfSym0 a6989586621679045360 = ListisPrefixOfSym1 a6989586621679045360
instance SuppressUnusedWarnings ListisPrefixOfSym0 where
  suppressUnusedWarnings
    = snd ((,) ListisPrefixOfSym0KindInference ())
type ListisPrefixOfSym1 :: [a_a8v5] -> (~>) [a_a8v5] Bool
data ListisPrefixOfSym1 (a6989586621679045360 :: [a_a8v5]) :: (~>) [a_a8v5] Bool
  where
    ListisPrefixOfSym1KindInference :: SameKind (Apply (ListisPrefixOfSym1 a6989586621679045360) arg_a9fF) (ListisPrefixOfSym2 a6989586621679045360 arg_a9fF) =>
                                        ListisPrefixOfSym1 a6989586621679045360 a6989586621679045361
type instance Apply @[a_a8v5] @Bool (ListisPrefixOfSym1 a6989586621679045360) a6989586621679045361 = ListisPrefixOf a6989586621679045360 a6989586621679045361
instance SuppressUnusedWarnings (ListisPrefixOfSym1 a6989586621679045360) where
  suppressUnusedWarnings
    = snd ((,) ListisPrefixOfSym1KindInference ())
type ListisPrefixOfSym2 :: [a_a8v5] -> [a_a8v5] -> Bool
type family ListisPrefixOfSym2 @a_a8v5 (a6989586621679045360 :: [a_a8v5]) (a6989586621679045361 :: [a_a8v5]) :: Bool where
  ListisPrefixOfSym2 a6989586621679045360 a6989586621679045361 = ListisPrefixOf a6989586621679045360 a6989586621679045361
type ListsortBySym0 :: (~>) ((~>) a_a8v6 ((~>) a_a8v6 Ordering)) ((~>) [a_a8v6] [a_a8v6])
data ListsortBySym0 :: (~>) ((~>) a_a8v6 ((~>) a_a8v6 Ordering)) ((~>) [a_a8v6] [a_a8v6])
  where
    ListsortBySym0KindInference :: SameKind (Apply ListsortBySym0 arg_a9fQ) (ListsortBySym1 arg_a9fQ) =>
                                    ListsortBySym0 a6989586621679045371
type instance Apply @((~>) a_a8v6 ((~>) a_a8v6 Ordering)) @((~>) [a_a8v6] [a_a8v6]) ListsortBySym0 a6989586621679045371 = ListsortBySym1 a6989586621679045371
instance SuppressUnusedWarnings ListsortBySym0 where
  suppressUnusedWarnings = snd ((,) ListsortBySym0KindInference ())
type ListsortBySym1 :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)
                        -> (~>) [a_a8v6] [a_a8v6]
data ListsortBySym1 (a6989586621679045371 :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)) :: (~>) [a_a8v6] [a_a8v6]
  where
    ListsortBySym1KindInference :: SameKind (Apply (ListsortBySym1 a6989586621679045371) arg_a9fQ) (ListsortBySym2 a6989586621679045371 arg_a9fQ) =>
                                    ListsortBySym1 a6989586621679045371 a6989586621679045372
type instance Apply @[a_a8v6] @[a_a8v6] (ListsortBySym1 a6989586621679045371) a6989586621679045372 = ListsortBy a6989586621679045371 a6989586621679045372
instance SuppressUnusedWarnings (ListsortBySym1 a6989586621679045371) where
  suppressUnusedWarnings = snd ((,) ListsortBySym1KindInference ())
type ListsortBySym2 :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)
                        -> [a_a8v6] -> [a_a8v6]
type family ListsortBySym2 @a_a8v6 (a6989586621679045371 :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)) (a6989586621679045372 :: [a_a8v6]) :: [a_a8v6] where
  ListsortBySym2 a6989586621679045371 a6989586621679045372 = ListsortBy a6989586621679045371 a6989586621679045372
type ListpartitionSym0 :: (~>) ((~>) a_a8v7 Bool) ((~>) [a_a8v7] ([a_a8v7],
                                                                  [a_a8v7]))
data ListpartitionSym0 :: (~>) ((~>) a_a8v7 Bool) ((~>) [a_a8v7] ([a_a8v7],
                                                                  [a_a8v7]))
  where
    ListpartitionSym0KindInference :: SameKind (Apply ListpartitionSym0 arg_a9g1) (ListpartitionSym1 arg_a9g1) =>
                                      ListpartitionSym0 a6989586621679045382
type instance Apply @((~>) a_a8v7 Bool) @((~>) [a_a8v7] ([a_a8v7],
                                                          [a_a8v7])) ListpartitionSym0 a6989586621679045382 = ListpartitionSym1 a6989586621679045382
instance SuppressUnusedWarnings ListpartitionSym0 where
  suppressUnusedWarnings
    = snd ((,) ListpartitionSym0KindInference ())
type ListpartitionSym1 :: (~>) a_a8v7 Bool
                          -> (~>) [a_a8v7] ([a_a8v7], [a_a8v7])
data ListpartitionSym1 (a6989586621679045382 :: (~>) a_a8v7 Bool) :: (~>) [a_a8v7] ([a_a8v7],
                                                                                    [a_a8v7])
  where
    ListpartitionSym1KindInference :: SameKind (Apply (ListpartitionSym1 a6989586621679045382) arg_a9g1) (ListpartitionSym2 a6989586621679045382 arg_a9g1) =>
                                      ListpartitionSym1 a6989586621679045382 a6989586621679045383
type instance Apply @[a_a8v7] @([a_a8v7],
                                [a_a8v7]) (ListpartitionSym1 a6989586621679045382) a6989586621679045383 = Listpartition a6989586621679045382 a6989586621679045383
instance SuppressUnusedWarnings (ListpartitionSym1 a6989586621679045382) where
  suppressUnusedWarnings
    = snd ((,) ListpartitionSym1KindInference ())
type ListpartitionSym2 :: (~>) a_a8v7 Bool
                          -> [a_a8v7] -> ([a_a8v7], [a_a8v7])
type family ListpartitionSym2 @a_a8v7 (a6989586621679045382 :: (~>) a_a8v7 Bool) (a6989586621679045383 :: [a_a8v7]) :: ([a_a8v7],
                                                                                                                        [a_a8v7]) where
  ListpartitionSym2 a6989586621679045382 a6989586621679045383 = Listpartition a6989586621679045382 a6989586621679045383
type ListfilterSym0 :: (~>) ((~>) a_a8v8 Bool) ((~>) [a_a8v8] [a_a8v8])
data ListfilterSym0 :: (~>) ((~>) a_a8v8 Bool) ((~>) [a_a8v8] [a_a8v8])
  where
    ListfilterSym0KindInference :: SameKind (Apply ListfilterSym0 arg_a9gc) (ListfilterSym1 arg_a9gc) =>
                                    ListfilterSym0 a6989586621679045393
type instance Apply @((~>) a_a8v8 Bool) @((~>) [a_a8v8] [a_a8v8]) ListfilterSym0 a6989586621679045393 = ListfilterSym1 a6989586621679045393
instance SuppressUnusedWarnings ListfilterSym0 where
  suppressUnusedWarnings = snd ((,) ListfilterSym0KindInference ())
type ListfilterSym1 :: (~>) a_a8v8 Bool -> (~>) [a_a8v8] [a_a8v8]
data ListfilterSym1 (a6989586621679045393 :: (~>) a_a8v8 Bool) :: (~>) [a_a8v8] [a_a8v8]
  where
    ListfilterSym1KindInference :: SameKind (Apply (ListfilterSym1 a6989586621679045393) arg_a9gc) (ListfilterSym2 a6989586621679045393 arg_a9gc) =>
                                    ListfilterSym1 a6989586621679045393 a6989586621679045394
type instance Apply @[a_a8v8] @[a_a8v8] (ListfilterSym1 a6989586621679045393) a6989586621679045394 = Listfilter a6989586621679045393 a6989586621679045394
instance SuppressUnusedWarnings (ListfilterSym1 a6989586621679045393) where
  suppressUnusedWarnings = snd ((,) ListfilterSym1KindInference ())
type ListfilterSym2 :: (~>) a_a8v8 Bool -> [a_a8v8] -> [a_a8v8]
type family ListfilterSym2 @a_a8v8 (a6989586621679045393 :: (~>) a_a8v8 Bool) (a6989586621679045394 :: [a_a8v8]) :: [a_a8v8] where
  ListfilterSym2 a6989586621679045393 a6989586621679045394 = Listfilter a6989586621679045393 a6989586621679045394
type ListspanSym0 :: (~>) ((~>) a_a8v9 Bool) ((~>) [a_a8v9] ([a_a8v9],
                                                              [a_a8v9]))
data ListspanSym0 :: (~>) ((~>) a_a8v9 Bool) ((~>) [a_a8v9] ([a_a8v9],
                                                              [a_a8v9]))
  where
    ListspanSym0KindInference :: SameKind (Apply ListspanSym0 arg_a9gn) (ListspanSym1 arg_a9gn) =>
                                  ListspanSym0 a6989586621679045404
type instance Apply @((~>) a_a8v9 Bool) @((~>) [a_a8v9] ([a_a8v9],
                                                          [a_a8v9])) ListspanSym0 a6989586621679045404 = ListspanSym1 a6989586621679045404
instance SuppressUnusedWarnings ListspanSym0 where
  suppressUnusedWarnings = snd ((,) ListspanSym0KindInference ())
type ListspanSym1 :: (~>) a_a8v9 Bool
                      -> (~>) [a_a8v9] ([a_a8v9], [a_a8v9])
data ListspanSym1 (a6989586621679045404 :: (~>) a_a8v9 Bool) :: (~>) [a_a8v9] ([a_a8v9],
                                                                                [a_a8v9])
  where
    ListspanSym1KindInference :: SameKind (Apply (ListspanSym1 a6989586621679045404) arg_a9gn) (ListspanSym2 a6989586621679045404 arg_a9gn) =>
                                  ListspanSym1 a6989586621679045404 a6989586621679045405
type instance Apply @[a_a8v9] @([a_a8v9],
                                [a_a8v9]) (ListspanSym1 a6989586621679045404) a6989586621679045405 = Listspan a6989586621679045404 a6989586621679045405
instance SuppressUnusedWarnings (ListspanSym1 a6989586621679045404) where
  suppressUnusedWarnings = snd ((,) ListspanSym1KindInference ())
type ListspanSym2 :: (~>) a_a8v9 Bool
                      -> [a_a8v9] -> ([a_a8v9], [a_a8v9])
type family ListspanSym2 @a_a8v9 (a6989586621679045404 :: (~>) a_a8v9 Bool) (a6989586621679045405 :: [a_a8v9]) :: ([a_a8v9],
                                                                                                                    [a_a8v9]) where
  ListspanSym2 a6989586621679045404 a6989586621679045405 = Listspan a6989586621679045404 a6989586621679045405
type ListdropWhileSym0 :: (~>) ((~>) a_a8va Bool) ((~>) [a_a8va] [a_a8va])
data ListdropWhileSym0 :: (~>) ((~>) a_a8va Bool) ((~>) [a_a8va] [a_a8va])
  where
    ListdropWhileSym0KindInference :: SameKind (Apply ListdropWhileSym0 arg_a9gy) (ListdropWhileSym1 arg_a9gy) =>
                                      ListdropWhileSym0 a6989586621679045415
type instance Apply @((~>) a_a8va Bool) @((~>) [a_a8va] [a_a8va]) ListdropWhileSym0 a6989586621679045415 = ListdropWhileSym1 a6989586621679045415
instance SuppressUnusedWarnings ListdropWhileSym0 where
  suppressUnusedWarnings
    = snd ((,) ListdropWhileSym0KindInference ())
type ListdropWhileSym1 :: (~>) a_a8va Bool
                          -> (~>) [a_a8va] [a_a8va]
data ListdropWhileSym1 (a6989586621679045415 :: (~>) a_a8va Bool) :: (~>) [a_a8va] [a_a8va]
  where
    ListdropWhileSym1KindInference :: SameKind (Apply (ListdropWhileSym1 a6989586621679045415) arg_a9gy) (ListdropWhileSym2 a6989586621679045415 arg_a9gy) =>
                                      ListdropWhileSym1 a6989586621679045415 a6989586621679045416
type instance Apply @[a_a8va] @[a_a8va] (ListdropWhileSym1 a6989586621679045415) a6989586621679045416 = ListdropWhile a6989586621679045415 a6989586621679045416
instance SuppressUnusedWarnings (ListdropWhileSym1 a6989586621679045415) where
  suppressUnusedWarnings
    = snd ((,) ListdropWhileSym1KindInference ())
type ListdropWhileSym2 :: (~>) a_a8va Bool -> [a_a8va] -> [a_a8va]
type family ListdropWhileSym2 @a_a8va (a6989586621679045415 :: (~>) a_a8va Bool) (a6989586621679045416 :: [a_a8va]) :: [a_a8va] where
  ListdropWhileSym2 a6989586621679045415 a6989586621679045416 = ListdropWhile a6989586621679045415 a6989586621679045416
type ListtakeWhileSym0 :: (~>) ((~>) a_a8vb Bool) ((~>) [a_a8vb] [a_a8vb])
data ListtakeWhileSym0 :: (~>) ((~>) a_a8vb Bool) ((~>) [a_a8vb] [a_a8vb])
  where
    ListtakeWhileSym0KindInference :: SameKind (Apply ListtakeWhileSym0 arg_a9gJ) (ListtakeWhileSym1 arg_a9gJ) =>
                                      ListtakeWhileSym0 a6989586621679045426
type instance Apply @((~>) a_a8vb Bool) @((~>) [a_a8vb] [a_a8vb]) ListtakeWhileSym0 a6989586621679045426 = ListtakeWhileSym1 a6989586621679045426
instance SuppressUnusedWarnings ListtakeWhileSym0 where
  suppressUnusedWarnings
    = snd ((,) ListtakeWhileSym0KindInference ())
type ListtakeWhileSym1 :: (~>) a_a8vb Bool
                          -> (~>) [a_a8vb] [a_a8vb]
data ListtakeWhileSym1 (a6989586621679045426 :: (~>) a_a8vb Bool) :: (~>) [a_a8vb] [a_a8vb]
  where
    ListtakeWhileSym1KindInference :: SameKind (Apply (ListtakeWhileSym1 a6989586621679045426) arg_a9gJ) (ListtakeWhileSym2 a6989586621679045426 arg_a9gJ) =>
                                      ListtakeWhileSym1 a6989586621679045426 a6989586621679045427
type instance Apply @[a_a8vb] @[a_a8vb] (ListtakeWhileSym1 a6989586621679045426) a6989586621679045427 = ListtakeWhile a6989586621679045426 a6989586621679045427
instance SuppressUnusedWarnings (ListtakeWhileSym1 a6989586621679045426) where
  suppressUnusedWarnings
    = snd ((,) ListtakeWhileSym1KindInference ())
type ListtakeWhileSym2 :: (~>) a_a8vb Bool -> [a_a8vb] -> [a_a8vb]
type family ListtakeWhileSym2 @a_a8vb (a6989586621679045426 :: (~>) a_a8vb Bool) (a6989586621679045427 :: [a_a8vb]) :: [a_a8vb] where
  ListtakeWhileSym2 a6989586621679045426 a6989586621679045427 = ListtakeWhile a6989586621679045426 a6989586621679045427
type ListreverseSym0 :: (~>) [a_a8vc] [a_a8vc]
data ListreverseSym0 :: (~>) [a_a8vc] [a_a8vc]
  where
    ListreverseSym0KindInference :: SameKind (Apply ListreverseSym0 arg_a9gR) (ListreverseSym1 arg_a9gR) =>
                                    ListreverseSym0 a6989586621679045434
type instance Apply @[a_a8vc] @[a_a8vc] ListreverseSym0 a6989586621679045434 = Listreverse a6989586621679045434
instance SuppressUnusedWarnings ListreverseSym0 where
  suppressUnusedWarnings = snd ((,) ListreverseSym0KindInference ())
type ListreverseSym1 :: [a_a8vc] -> [a_a8vc]
type family ListreverseSym1 @a_a8vc (a6989586621679045434 :: [a_a8vc]) :: [a_a8vc] where
  ListreverseSym1 a6989586621679045434 = Listreverse a6989586621679045434
type ListintersperseSym0 :: (~>) a_a8vd ((~>) [a_a8vd] [a_a8vd])
data ListintersperseSym0 :: (~>) a_a8vd ((~>) [a_a8vd] [a_a8vd])
  where
    ListintersperseSym0KindInference :: SameKind (Apply ListintersperseSym0 arg_a9h0) (ListintersperseSym1 arg_a9h0) =>
                                        ListintersperseSym0 a6989586621679045443
type instance Apply @a_a8vd @((~>) [a_a8vd] [a_a8vd]) ListintersperseSym0 a6989586621679045443 = ListintersperseSym1 a6989586621679045443
instance SuppressUnusedWarnings ListintersperseSym0 where
  suppressUnusedWarnings
    = snd ((,) ListintersperseSym0KindInference ())
type ListintersperseSym1 :: a_a8vd -> (~>) [a_a8vd] [a_a8vd]
data ListintersperseSym1 (a6989586621679045443 :: a_a8vd) :: (~>) [a_a8vd] [a_a8vd]
  where
    ListintersperseSym1KindInference :: SameKind (Apply (ListintersperseSym1 a6989586621679045443) arg_a9h0) (ListintersperseSym2 a6989586621679045443 arg_a9h0) =>
                                        ListintersperseSym1 a6989586621679045443 a6989586621679045444
type instance Apply @[a_a8vd] @[a_a8vd] (ListintersperseSym1 a6989586621679045443) a6989586621679045444 = Listintersperse a6989586621679045443 a6989586621679045444
instance SuppressUnusedWarnings (ListintersperseSym1 a6989586621679045443) where
  suppressUnusedWarnings
    = snd ((,) ListintersperseSym1KindInference ())
type ListintersperseSym2 :: a_a8vd -> [a_a8vd] -> [a_a8vd]
type family ListintersperseSym2 @a_a8vd (a6989586621679045443 :: a_a8vd) (a6989586621679045444 :: [a_a8vd]) :: [a_a8vd] where
  ListintersperseSym2 a6989586621679045443 a6989586621679045444 = Listintersperse a6989586621679045443 a6989586621679045444
type Listscanr1Sym0 :: (~>) ((~>) a_a8ve ((~>) a_a8ve a_a8ve)) ((~>) [a_a8ve] [a_a8ve])
data Listscanr1Sym0 :: (~>) ((~>) a_a8ve ((~>) a_a8ve a_a8ve)) ((~>) [a_a8ve] [a_a8ve])
  where
    Listscanr1Sym0KindInference :: SameKind (Apply Listscanr1Sym0 arg_a9hb) (Listscanr1Sym1 arg_a9hb) =>
                                    Listscanr1Sym0 a6989586621679045454
type instance Apply @((~>) a_a8ve ((~>) a_a8ve a_a8ve)) @((~>) [a_a8ve] [a_a8ve]) Listscanr1Sym0 a6989586621679045454 = Listscanr1Sym1 a6989586621679045454
instance SuppressUnusedWarnings Listscanr1Sym0 where
  suppressUnusedWarnings = snd ((,) Listscanr1Sym0KindInference ())
type Listscanr1Sym1 :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)
                        -> (~>) [a_a8ve] [a_a8ve]
data Listscanr1Sym1 (a6989586621679045454 :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)) :: (~>) [a_a8ve] [a_a8ve]
  where
    Listscanr1Sym1KindInference :: SameKind (Apply (Listscanr1Sym1 a6989586621679045454) arg_a9hb) (Listscanr1Sym2 a6989586621679045454 arg_a9hb) =>
                                    Listscanr1Sym1 a6989586621679045454 a6989586621679045455
type instance Apply @[a_a8ve] @[a_a8ve] (Listscanr1Sym1 a6989586621679045454) a6989586621679045455 = Listscanr1 a6989586621679045454 a6989586621679045455
instance SuppressUnusedWarnings (Listscanr1Sym1 a6989586621679045454) where
  suppressUnusedWarnings = snd ((,) Listscanr1Sym1KindInference ())
type Listscanr1Sym2 :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)
                        -> [a_a8ve] -> [a_a8ve]
type family Listscanr1Sym2 @a_a8ve (a6989586621679045454 :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)) (a6989586621679045455 :: [a_a8ve]) :: [a_a8ve] where
  Listscanr1Sym2 a6989586621679045454 a6989586621679045455 = Listscanr1 a6989586621679045454 a6989586621679045455
type ListscanrSym0 :: (~>) ((~>) a_a8vf ((~>) b_a8vg b_a8vg)) ((~>) b_a8vg ((~>) [a_a8vf] [b_a8vg]))
data ListscanrSym0 :: (~>) ((~>) a_a8vf ((~>) b_a8vg b_a8vg)) ((~>) b_a8vg ((~>) [a_a8vf] [b_a8vg]))
  where
    ListscanrSym0KindInference :: SameKind (Apply ListscanrSym0 arg_a9hp) (ListscanrSym1 arg_a9hp) =>
                                  ListscanrSym0 a6989586621679045468
type instance Apply @((~>) a_a8vf ((~>) b_a8vg b_a8vg)) @((~>) b_a8vg ((~>) [a_a8vf] [b_a8vg])) ListscanrSym0 a6989586621679045468 = ListscanrSym1 a6989586621679045468
instance SuppressUnusedWarnings ListscanrSym0 where
  suppressUnusedWarnings = snd ((,) ListscanrSym0KindInference ())
type ListscanrSym1 :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)
                      -> (~>) b_a8vg ((~>) [a_a8vf] [b_a8vg])
data ListscanrSym1 (a6989586621679045468 :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) :: (~>) b_a8vg ((~>) [a_a8vf] [b_a8vg])
  where
    ListscanrSym1KindInference :: SameKind (Apply (ListscanrSym1 a6989586621679045468) arg_a9hp) (ListscanrSym2 a6989586621679045468 arg_a9hp) =>
                                  ListscanrSym1 a6989586621679045468 a6989586621679045469
type instance Apply @b_a8vg @((~>) [a_a8vf] [b_a8vg]) (ListscanrSym1 a6989586621679045468) a6989586621679045469 = ListscanrSym2 a6989586621679045468 a6989586621679045469
instance SuppressUnusedWarnings (ListscanrSym1 a6989586621679045468) where
  suppressUnusedWarnings = snd ((,) ListscanrSym1KindInference ())
type ListscanrSym2 :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)
                      -> b_a8vg -> (~>) [a_a8vf] [b_a8vg]
data ListscanrSym2 (a6989586621679045468 :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) (a6989586621679045469 :: b_a8vg) :: (~>) [a_a8vf] [b_a8vg]
  where
    ListscanrSym2KindInference :: SameKind (Apply (ListscanrSym2 a6989586621679045468 a6989586621679045469) arg_a9hp) (ListscanrSym3 a6989586621679045468 a6989586621679045469 arg_a9hp) =>
                                  ListscanrSym2 a6989586621679045468 a6989586621679045469 a6989586621679045470
type instance Apply @[a_a8vf] @[b_a8vg] (ListscanrSym2 a6989586621679045468 a6989586621679045469) a6989586621679045470 = Listscanr a6989586621679045468 a6989586621679045469 a6989586621679045470
instance SuppressUnusedWarnings (ListscanrSym2 a6989586621679045468 a6989586621679045469) where
  suppressUnusedWarnings = snd ((,) ListscanrSym2KindInference ())
type ListscanrSym3 :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)
                      -> b_a8vg -> [a_a8vf] -> [b_a8vg]
type family ListscanrSym3 @a_a8vf @b_a8vg (a6989586621679045468 :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) (a6989586621679045469 :: b_a8vg) (a6989586621679045470 :: [a_a8vf]) :: [b_a8vg] where
  ListscanrSym3 a6989586621679045468 a6989586621679045469 a6989586621679045470 = Listscanr a6989586621679045468 a6989586621679045469 a6989586621679045470
type ListscanlSym0 :: (~>) ((~>) b_a8vh ((~>) a_a8vi b_a8vh)) ((~>) b_a8vh ((~>) [a_a8vi] [b_a8vh]))
data ListscanlSym0 :: (~>) ((~>) b_a8vh ((~>) a_a8vi b_a8vh)) ((~>) b_a8vh ((~>) [a_a8vi] [b_a8vh]))
  where
    ListscanlSym0KindInference :: SameKind (Apply ListscanlSym0 arg_a9hF) (ListscanlSym1 arg_a9hF) =>
                                  ListscanlSym0 a6989586621679045484
type instance Apply @((~>) b_a8vh ((~>) a_a8vi b_a8vh)) @((~>) b_a8vh ((~>) [a_a8vi] [b_a8vh])) ListscanlSym0 a6989586621679045484 = ListscanlSym1 a6989586621679045484
instance SuppressUnusedWarnings ListscanlSym0 where
  suppressUnusedWarnings = snd ((,) ListscanlSym0KindInference ())
type ListscanlSym1 :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)
                      -> (~>) b_a8vh ((~>) [a_a8vi] [b_a8vh])
data ListscanlSym1 (a6989586621679045484 :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) :: (~>) b_a8vh ((~>) [a_a8vi] [b_a8vh])
  where
    ListscanlSym1KindInference :: SameKind (Apply (ListscanlSym1 a6989586621679045484) arg_a9hF) (ListscanlSym2 a6989586621679045484 arg_a9hF) =>
                                  ListscanlSym1 a6989586621679045484 a6989586621679045485
type instance Apply @b_a8vh @((~>) [a_a8vi] [b_a8vh]) (ListscanlSym1 a6989586621679045484) a6989586621679045485 = ListscanlSym2 a6989586621679045484 a6989586621679045485
instance SuppressUnusedWarnings (ListscanlSym1 a6989586621679045484) where
  suppressUnusedWarnings = snd ((,) ListscanlSym1KindInference ())
type ListscanlSym2 :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)
                      -> b_a8vh -> (~>) [a_a8vi] [b_a8vh]
data ListscanlSym2 (a6989586621679045484 :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) (a6989586621679045485 :: b_a8vh) :: (~>) [a_a8vi] [b_a8vh]
  where
    ListscanlSym2KindInference :: SameKind (Apply (ListscanlSym2 a6989586621679045484 a6989586621679045485) arg_a9hF) (ListscanlSym3 a6989586621679045484 a6989586621679045485 arg_a9hF) =>
                                  ListscanlSym2 a6989586621679045484 a6989586621679045485 a6989586621679045486
type instance Apply @[a_a8vi] @[b_a8vh] (ListscanlSym2 a6989586621679045484 a6989586621679045485) a6989586621679045486 = Listscanl a6989586621679045484 a6989586621679045485 a6989586621679045486
instance SuppressUnusedWarnings (ListscanlSym2 a6989586621679045484 a6989586621679045485) where
  suppressUnusedWarnings = snd ((,) ListscanlSym2KindInference ())
type ListscanlSym3 :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)
                      -> b_a8vh -> [a_a8vi] -> [b_a8vh]
type family ListscanlSym3 @b_a8vh @a_a8vi (a6989586621679045484 :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) (a6989586621679045485 :: b_a8vh) (a6989586621679045486 :: [a_a8vi]) :: [b_a8vh] where
  ListscanlSym3 a6989586621679045484 a6989586621679045485 a6989586621679045486 = Listscanl a6989586621679045484 a6989586621679045485 a6989586621679045486
type ListinsertSym0 :: (~>) a_a8vj ((~>) [a_a8vj] [a_a8vj])
data ListinsertSym0 :: (~>) a_a8vj ((~>) [a_a8vj] [a_a8vj])
  where
    ListinsertSym0KindInference :: SameKind (Apply ListinsertSym0 arg_a9hS) (ListinsertSym1 arg_a9hS) =>
                                    ListinsertSym0 a6989586621679045497
type instance Apply @a_a8vj @((~>) [a_a8vj] [a_a8vj]) ListinsertSym0 a6989586621679045497 = ListinsertSym1 a6989586621679045497
instance SuppressUnusedWarnings ListinsertSym0 where
  suppressUnusedWarnings = snd ((,) ListinsertSym0KindInference ())
type ListinsertSym1 :: a_a8vj -> (~>) [a_a8vj] [a_a8vj]
data ListinsertSym1 (a6989586621679045497 :: a_a8vj) :: (~>) [a_a8vj] [a_a8vj]
  where
    ListinsertSym1KindInference :: SameKind (Apply (ListinsertSym1 a6989586621679045497) arg_a9hS) (ListinsertSym2 a6989586621679045497 arg_a9hS) =>
                                    ListinsertSym1 a6989586621679045497 a6989586621679045498
type instance Apply @[a_a8vj] @[a_a8vj] (ListinsertSym1 a6989586621679045497) a6989586621679045498 = Listinsert a6989586621679045497 a6989586621679045498
instance SuppressUnusedWarnings (ListinsertSym1 a6989586621679045497) where
  suppressUnusedWarnings = snd ((,) ListinsertSym1KindInference ())
type ListinsertSym2 :: a_a8vj -> [a_a8vj] -> [a_a8vj]
type family ListinsertSym2 @a_a8vj (a6989586621679045497 :: a_a8vj) (a6989586621679045498 :: [a_a8vj]) :: [a_a8vj] where
  ListinsertSym2 a6989586621679045497 a6989586621679045498 = Listinsert a6989586621679045497 a6989586621679045498
type ListtailsSym0 :: (~>) [a_a8vk] [[a_a8vk]]
data ListtailsSym0 :: (~>) [a_a8vk] [[a_a8vk]]
  where
    ListtailsSym0KindInference :: SameKind (Apply ListtailsSym0 arg_a9i0) (ListtailsSym1 arg_a9i0) =>
                                  ListtailsSym0 a6989586621679045505
type instance Apply @[a_a8vk] @[[a_a8vk]] ListtailsSym0 a6989586621679045505 = Listtails a6989586621679045505
instance SuppressUnusedWarnings ListtailsSym0 where
  suppressUnusedWarnings = snd ((,) ListtailsSym0KindInference ())
type ListtailsSym1 :: [a_a8vk] -> [[a_a8vk]]
type family ListtailsSym1 @a_a8vk (a6989586621679045505 :: [a_a8vk]) :: [[a_a8vk]] where
  ListtailsSym1 a6989586621679045505 = Listtails a6989586621679045505
type ListinitsSym0 :: (~>) [a_a8vl] [[a_a8vl]]
data ListinitsSym0 :: (~>) [a_a8vl] [[a_a8vl]]
  where
    ListinitsSym0KindInference :: SameKind (Apply ListinitsSym0 arg_a9i6) (ListinitsSym1 arg_a9i6) =>
                                  ListinitsSym0 a6989586621679045511
type instance Apply @[a_a8vl] @[[a_a8vl]] ListinitsSym0 a6989586621679045511 = Listinits a6989586621679045511
instance SuppressUnusedWarnings ListinitsSym0 where
  suppressUnusedWarnings = snd ((,) ListinitsSym0KindInference ())
type ListinitsSym1 :: [a_a8vl] -> [[a_a8vl]]
type family ListinitsSym1 @a_a8vl (a6989586621679045511 :: [a_a8vl]) :: [[a_a8vl]] where
  ListinitsSym1 a6989586621679045511 = Listinits a6989586621679045511
type ListsortSym0 :: (~>) [a_a8vm] [a_a8vm]
data ListsortSym0 :: (~>) [a_a8vm] [a_a8vm]
  where
    ListsortSym0KindInference :: SameKind (Apply ListsortSym0 arg_a9ic) (ListsortSym1 arg_a9ic) =>
                                  ListsortSym0 a6989586621679045517
type instance Apply @[a_a8vm] @[a_a8vm] ListsortSym0 a6989586621679045517 = Listsort a6989586621679045517
instance SuppressUnusedWarnings ListsortSym0 where
  suppressUnusedWarnings = snd ((,) ListsortSym0KindInference ())
type ListsortSym1 :: [a_a8vm] -> [a_a8vm]
type family ListsortSym1 @a_a8vm (a6989586621679045517 :: [a_a8vm]) :: [a_a8vm] where
  ListsortSym1 a6989586621679045517 = Listsort a6989586621679045517
type ListinitSym0 :: (~>) [a_a8vn] [a_a8vn]
data ListinitSym0 :: (~>) [a_a8vn] [a_a8vn]
  where
    ListinitSym0KindInference :: SameKind (Apply ListinitSym0 arg_a9ii) (ListinitSym1 arg_a9ii) =>
                                  ListinitSym0 a6989586621679045523
type instance Apply @[a_a8vn] @[a_a8vn] ListinitSym0 a6989586621679045523 = Listinit a6989586621679045523
instance SuppressUnusedWarnings ListinitSym0 where
  suppressUnusedWarnings = snd ((,) ListinitSym0KindInference ())
type ListinitSym1 :: [a_a8vn] -> [a_a8vn]
type family ListinitSym1 @a_a8vn (a6989586621679045523 :: [a_a8vn]) :: [a_a8vn] where
  ListinitSym1 a6989586621679045523 = Listinit a6989586621679045523
type ListlastSym0 :: (~>) [a_a8vo] a_a8vo
data ListlastSym0 :: (~>) [a_a8vo] a_a8vo
  where
    ListlastSym0KindInference :: SameKind (Apply ListlastSym0 arg_a9io) (ListlastSym1 arg_a9io) =>
                                  ListlastSym0 a6989586621679045529
type instance Apply @[a_a8vo] @a_a8vo ListlastSym0 a6989586621679045529 = Listlast a6989586621679045529
instance SuppressUnusedWarnings ListlastSym0 where
  suppressUnusedWarnings = snd ((,) ListlastSym0KindInference ())
type ListlastSym1 :: [a_a8vo] -> a_a8vo
type family ListlastSym1 @a_a8vo (a6989586621679045529 :: [a_a8vo]) :: a_a8vo where
  ListlastSym1 a6989586621679045529 = Listlast a6989586621679045529
type Listsum :: [a_a8uG] -> a_a8uG
type family Listsum @a_a8uG (a_a9cP :: [a_a8uG]) :: a_a8uG where
  Listsum a_6989586621679045181_a9cS = Apply SumSym0 a_6989586621679045181_a9cS
type Listproduct :: [a_a8uH] -> a_a8uH
type family Listproduct @a_a8uH (a_a9cV :: [a_a8uH]) :: a_a8uH where
  Listproduct a_6989586621679045187_a9cY = Apply ProductSym0 a_6989586621679045187_a9cY
type Listnull :: [a_a8uI] -> Bool
type family Listnull @a_a8uI (a_a9d1 :: [a_a8uI]) :: Bool where
  Listnull a_6989586621679045193_a9d4 = Apply NullSym0 a_6989586621679045193_a9d4
type Listminimum :: [a_a8uJ] -> a_a8uJ
type family Listminimum @a_a8uJ (a_a9d7 :: [a_a8uJ]) :: a_a8uJ where
  Listminimum a_6989586621679045199_a9da = Apply MinimumSym0 a_6989586621679045199_a9da
type Listmaximum :: [a_a8uK] -> a_a8uK
type family Listmaximum @a_a8uK (a_a9dd :: [a_a8uK]) :: a_a8uK where
  Listmaximum a_6989586621679045205_a9dg = Apply MaximumSym0 a_6989586621679045205_a9dg
type Listfoldr1 :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)
                    -> [a_a8uL] -> a_a8uL
type family Listfoldr1 @a_a8uL (a_a9dl :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)) (a_a9dm :: [a_a8uL]) :: a_a8uL where
  Listfoldr1 a_6989586621679045211_a9dq a_6989586621679045213_a9dr = Apply (Apply Foldr1Sym0 a_6989586621679045211_a9dq) a_6989586621679045213_a9dr
type Listfoldr :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)
                  -> b_a8uN -> [a_a8uM] -> b_a8uN
type family Listfoldr @a_a8uM @b_a8uN (a_a9dy :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) (a_a9dz :: b_a8uN) (a_a9dA :: [a_a8uM]) :: b_a8uN where
  Listfoldr a_6989586621679045222_a9dF a_6989586621679045224_a9dG a_6989586621679045226_a9dH = Apply (Apply (Apply FoldrSym0 a_6989586621679045222_a9dF) a_6989586621679045224_a9dG) a_6989586621679045226_a9dH
type Listfoldl1 :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)
                    -> [a_a8uO] -> a_a8uO
type family Listfoldl1 @a_a8uO (a_a9dM :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)) (a_a9dN :: [a_a8uO]) :: a_a8uO where
  Listfoldl1 a_6989586621679045238_a9dR a_6989586621679045240_a9dS = Apply (Apply Foldl1Sym0 a_6989586621679045238_a9dR) a_6989586621679045240_a9dS
type Listfoldl' :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)
                    -> b_a8uP -> [a_a8uQ] -> b_a8uP
type family Listfoldl' @b_a8uP @a_a8uQ (a_a9dZ :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) (a_a9e0 :: b_a8uP) (a_a9e1 :: [a_a8uQ]) :: b_a8uP where
  Listfoldl' a_6989586621679045249_a9e6 a_6989586621679045251_a9e7 a_6989586621679045253_a9e8 = Apply (Apply (Apply Foldl'Sym0 a_6989586621679045249_a9e6) a_6989586621679045251_a9e7) a_6989586621679045253_a9e8
type Listfoldl :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)
                  -> b_a8uR -> [a_a8uS] -> b_a8uR
type family Listfoldl @b_a8uR @a_a8uS (a_a9ef :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) (a_a9eg :: b_a8uR) (a_a9eh :: [a_a8uS]) :: b_a8uR where
  Listfoldl a_6989586621679045265_a9em a_6989586621679045267_a9en a_6989586621679045269_a9eo = Apply (Apply (Apply FoldlSym0 a_6989586621679045265_a9em) a_6989586621679045267_a9en) a_6989586621679045269_a9eo
type Listelem :: a_a8uT -> [a_a8uT] -> Bool
type family Listelem @a_a8uT (a_a9et :: a_a8uT) (a_a9eu :: [a_a8uT]) :: Bool where
  Listelem a_6989586621679045281_a9ey a_6989586621679045283_a9ez = Apply (Apply ElemSym0 a_6989586621679045281_a9ey) a_6989586621679045283_a9ez
type Listmap :: (~>) a_a8uU b_a8uV -> [a_a8uU] -> [b_a8uV]
type family Listmap @a_a8uU @b_a8uV (a_a9eE :: (~>) a_a8uU b_a8uV) (a_a9eF :: [a_a8uU]) :: [b_a8uV] where
  Listmap a_6989586621679045292_a9eJ a_6989586621679045294_a9eK = Apply (Apply MapSym0 a_6989586621679045292_a9eJ) a_6989586621679045294_a9eK
type Listunzip :: [(a_a8uW, b_a8uX)] -> ([a_a8uW], [b_a8uX])
type family Listunzip @a_a8uW @b_a8uX (a_a9eN :: [(a_a8uW,
                                                    b_a8uX)]) :: ([a_a8uW], [b_a8uX]) where
  Listunzip a_6989586621679045303_a9eQ = Apply UnzipSym0 a_6989586621679045303_a9eQ
type Listtranspose :: [[a_a8uY]] -> [[a_a8uY]]
type family Listtranspose @a_a8uY (a_a9eT :: [[a_a8uY]]) :: [[a_a8uY]] where
  Listtranspose a_6989586621679045309_a9eW = Apply TransposeSym0 a_6989586621679045309_a9eW
type ListnubBy :: (~>) a_a8uZ ((~>) a_a8uZ Bool)
                  -> [a_a8uZ] -> [a_a8uZ]
type family ListnubBy @a_a8uZ (a_a9f1 :: (~>) a_a8uZ ((~>) a_a8uZ Bool)) (a_a9f2 :: [a_a8uZ]) :: [a_a8uZ] where
  ListnubBy a_6989586621679045315_a9f6 a_6989586621679045317_a9f7 = Apply (Apply NubBySym0 a_6989586621679045315_a9f6) a_6989586621679045317_a9f7
type ListzipWith :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)
                    -> [a_a8v0] -> [b_a8v1] -> [c_a8v2]
type family ListzipWith @a_a8v0 @b_a8v1 @c_a8v2 (a_a9fe :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) (a_a9ff :: [a_a8v0]) (a_a9fg :: [b_a8v1]) :: [c_a8v2] where
  ListzipWith a_6989586621679045326_a9fl a_6989586621679045328_a9fm a_6989586621679045330_a9fn = Apply (Apply (Apply ZipWithSym0 a_6989586621679045326_a9fl) a_6989586621679045328_a9fm) a_6989586621679045330_a9fn
type Listzip :: [a_a8v3] -> [b_a8v4] -> [(a_a8v3, b_a8v4)]
type family Listzip @a_a8v3 @b_a8v4 (a_a9fs :: [a_a8v3]) (a_a9ft :: [b_a8v4]) :: [(a_a8v3,
                                                                                    b_a8v4)] where
  Listzip a_6989586621679045342_a9fx a_6989586621679045344_a9fy = Apply (Apply ZipSym0 a_6989586621679045342_a9fx) a_6989586621679045344_a9fy
type ListisPrefixOf :: [a_a8v5] -> [a_a8v5] -> Bool
type family ListisPrefixOf @a_a8v5 (a_a9fD :: [a_a8v5]) (a_a9fE :: [a_a8v5]) :: Bool where
  ListisPrefixOf a_6989586621679045353_a9fI a_6989586621679045355_a9fJ = Apply (Apply IsPrefixOfSym0 a_6989586621679045353_a9fI) a_6989586621679045355_a9fJ
type ListsortBy :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)
                    -> [a_a8v6] -> [a_a8v6]
type family ListsortBy @a_a8v6 (a_a9fO :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)) (a_a9fP :: [a_a8v6]) :: [a_a8v6] where
  ListsortBy a_6989586621679045364_a9fT a_6989586621679045366_a9fU = Apply (Apply SortBySym0 a_6989586621679045364_a9fT) a_6989586621679045366_a9fU
type Listpartition :: (~>) a_a8v7 Bool
                      -> [a_a8v7] -> ([a_a8v7], [a_a8v7])
type family Listpartition @a_a8v7 (a_a9fZ :: (~>) a_a8v7 Bool) (a_a9g0 :: [a_a8v7]) :: ([a_a8v7],
                                                                                        [a_a8v7]) where
  Listpartition a_6989586621679045375_a9g4 a_6989586621679045377_a9g5 = Apply (Apply PartitionSym0 a_6989586621679045375_a9g4) a_6989586621679045377_a9g5
type Listfilter :: (~>) a_a8v8 Bool -> [a_a8v8] -> [a_a8v8]
type family Listfilter @a_a8v8 (a_a9ga :: (~>) a_a8v8 Bool) (a_a9gb :: [a_a8v8]) :: [a_a8v8] where
  Listfilter a_6989586621679045386_a9gf a_6989586621679045388_a9gg = Apply (Apply FilterSym0 a_6989586621679045386_a9gf) a_6989586621679045388_a9gg
type Listspan :: (~>) a_a8v9 Bool
                  -> [a_a8v9] -> ([a_a8v9], [a_a8v9])
type family Listspan @a_a8v9 (a_a9gl :: (~>) a_a8v9 Bool) (a_a9gm :: [a_a8v9]) :: ([a_a8v9],
                                                                                    [a_a8v9]) where
  Listspan a_6989586621679045397_a9gq a_6989586621679045399_a9gr = Apply (Apply SpanSym0 a_6989586621679045397_a9gq) a_6989586621679045399_a9gr
type ListdropWhile :: (~>) a_a8va Bool -> [a_a8va] -> [a_a8va]
type family ListdropWhile @a_a8va (a_a9gw :: (~>) a_a8va Bool) (a_a9gx :: [a_a8va]) :: [a_a8va] where
  ListdropWhile a_6989586621679045408_a9gB a_6989586621679045410_a9gC = Apply (Apply DropWhileSym0 a_6989586621679045408_a9gB) a_6989586621679045410_a9gC
type ListtakeWhile :: (~>) a_a8vb Bool -> [a_a8vb] -> [a_a8vb]
type family ListtakeWhile @a_a8vb (a_a9gH :: (~>) a_a8vb Bool) (a_a9gI :: [a_a8vb]) :: [a_a8vb] where
  ListtakeWhile a_6989586621679045419_a9gM a_6989586621679045421_a9gN = Apply (Apply TakeWhileSym0 a_6989586621679045419_a9gM) a_6989586621679045421_a9gN
type Listreverse :: [a_a8vc] -> [a_a8vc]
type family Listreverse @a_a8vc (a_a9gQ :: [a_a8vc]) :: [a_a8vc] where
  Listreverse a_6989586621679045430_a9gT = Apply ReverseSym0 a_6989586621679045430_a9gT
type Listintersperse :: a_a8vd -> [a_a8vd] -> [a_a8vd]
type family Listintersperse @a_a8vd (a_a9gY :: a_a8vd) (a_a9gZ :: [a_a8vd]) :: [a_a8vd] where
  Listintersperse a_6989586621679045436_a9h3 a_6989586621679045438_a9h4 = Apply (Apply IntersperseSym0 a_6989586621679045436_a9h3) a_6989586621679045438_a9h4
type Listscanr1 :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)
                    -> [a_a8ve] -> [a_a8ve]
type family Listscanr1 @a_a8ve (a_a9h9 :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)) (a_a9ha :: [a_a8ve]) :: [a_a8ve] where
  Listscanr1 a_6989586621679045447_a9he a_6989586621679045449_a9hf = Apply (Apply Scanr1Sym0 a_6989586621679045447_a9he) a_6989586621679045449_a9hf
type Listscanr :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)
                  -> b_a8vg -> [a_a8vf] -> [b_a8vg]
type family Listscanr @a_a8vf @b_a8vg (a_a9hm :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) (a_a9hn :: b_a8vg) (a_a9ho :: [a_a8vf]) :: [b_a8vg] where
  Listscanr a_6989586621679045458_a9ht a_6989586621679045460_a9hu a_6989586621679045462_a9hv = Apply (Apply (Apply ScanrSym0 a_6989586621679045458_a9ht) a_6989586621679045460_a9hu) a_6989586621679045462_a9hv
type Listscanl :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)
                  -> b_a8vh -> [a_a8vi] -> [b_a8vh]
type family Listscanl @b_a8vh @a_a8vi (a_a9hC :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) (a_a9hD :: b_a8vh) (a_a9hE :: [a_a8vi]) :: [b_a8vh] where
  Listscanl a_6989586621679045474_a9hJ a_6989586621679045476_a9hK a_6989586621679045478_a9hL = Apply (Apply (Apply ScanlSym0 a_6989586621679045474_a9hJ) a_6989586621679045476_a9hK) a_6989586621679045478_a9hL
type Listinsert :: a_a8vj -> [a_a8vj] -> [a_a8vj]
type family Listinsert @a_a8vj (a_a9hQ :: a_a8vj) (a_a9hR :: [a_a8vj]) :: [a_a8vj] where
  Listinsert a_6989586621679045490_a9hV a_6989586621679045492_a9hW = Apply (Apply InsertSym0 a_6989586621679045490_a9hV) a_6989586621679045492_a9hW
type Listtails :: [a_a8vk] -> [[a_a8vk]]
type family Listtails @a_a8vk (a_a9hZ :: [a_a8vk]) :: [[a_a8vk]] where
  Listtails a_6989586621679045501_a9i2 = Apply TailsSym0 a_6989586621679045501_a9i2
type Listinits :: [a_a8vl] -> [[a_a8vl]]
type family Listinits @a_a8vl (a_a9i5 :: [a_a8vl]) :: [[a_a8vl]] where
  Listinits a_6989586621679045507_a9i8 = Apply InitsSym0 a_6989586621679045507_a9i8
type Listsort :: [a_a8vm] -> [a_a8vm]
type family Listsort @a_a8vm (a_a9ib :: [a_a8vm]) :: [a_a8vm] where
  Listsort a_6989586621679045513_a9ie = Apply SortSym0 a_6989586621679045513_a9ie
type Listinit :: [a_a8vn] -> [a_a8vn]
type family Listinit @a_a8vn (a_a9ih :: [a_a8vn]) :: [a_a8vn] where
  Listinit a_6989586621679045519_a9ik = Apply InitSym0 a_6989586621679045519_a9ik
type Listlast :: [a_a8vo] -> a_a8vo
type family Listlast @a_a8vo (a_a9in :: [a_a8vo]) :: a_a8vo where
  Listlast a_6989586621679045525_a9iq = Apply LastSym0 a_6989586621679045525_a9iq
sListsum ::
  (forall (t_a9ir :: [a_a8uG]).
    SNum a_a8uG =>
    Sing t_a9ir -> Sing (Listsum t_a9ir :: a_a8uG) :: Type)
sListproduct ::
  (forall (t_a9it :: [a_a8uH]).
    SNum a_a8uH =>
    Sing t_a9it -> Sing (Listproduct t_a9it :: a_a8uH) :: Type)
sListnull ::
  (forall (t_a9iv :: [a_a8uI]).
    Sing t_a9iv -> Sing (Listnull t_a9iv :: Bool) :: Type)
sListminimum ::
  (forall (t_a9ix :: [a_a8uJ]).
    SOrd a_a8uJ =>
    Sing t_a9ix -> Sing (Listminimum t_a9ix :: a_a8uJ) :: Type)
sListmaximum ::
  (forall (t_a9iz :: [a_a8uK]).
    SOrd a_a8uK =>
    Sing t_a9iz -> Sing (Listmaximum t_a9iz :: a_a8uK) :: Type)
sListfoldr1 ::
  (forall (t_a9iB :: (~>) a_a8uL ((~>) a_a8uL a_a8uL))
          (t_a9iC :: [a_a8uL]).
    Sing t_a9iB
    -> Sing t_a9iC
      -> Sing (Listfoldr1 t_a9iB t_a9iC :: a_a8uL) :: Type)
sListfoldr ::
  (forall (t_a9iG :: (~>) a_a8uM ((~>) b_a8uN b_a8uN))
          (t_a9iH :: b_a8uN)
          (t_a9iI :: [a_a8uM]).
    Sing t_a9iG
    -> Sing t_a9iH
      -> Sing t_a9iI
          -> Sing (Listfoldr t_a9iG t_a9iH t_a9iI :: b_a8uN) :: Type)
sListfoldl1 ::
  (forall (t_a9iQ :: (~>) a_a8uO ((~>) a_a8uO a_a8uO))
          (t_a9iR :: [a_a8uO]).
    Sing t_a9iQ
    -> Sing t_a9iR
      -> Sing (Listfoldl1 t_a9iQ t_a9iR :: a_a8uO) :: Type)
sListfoldl' ::
  (forall (t_a9iV :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP))
          (t_a9iW :: b_a8uP)
          (t_a9iX :: [a_a8uQ]).
    Sing t_a9iV
    -> Sing t_a9iW
      -> Sing t_a9iX
          -> Sing (Listfoldl' t_a9iV t_a9iW t_a9iX :: b_a8uP) :: Type)
sListfoldl ::
  (forall (t_a9j5 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR))
          (t_a9j6 :: b_a8uR)
          (t_a9j7 :: [a_a8uS]).
    Sing t_a9j5
    -> Sing t_a9j6
      -> Sing t_a9j7
          -> Sing (Listfoldl t_a9j5 t_a9j6 t_a9j7 :: b_a8uR) :: Type)
sListelem ::
  (forall (t_a9jf :: a_a8uT) (t_a9jg :: [a_a8uT]).
    SEq a_a8uT =>
    Sing t_a9jf
    -> Sing t_a9jg -> Sing (Listelem t_a9jf t_a9jg :: Bool) :: Type)
sListmap ::
  (forall (t_a9jk :: (~>) a_a8uU b_a8uV) (t_a9jl :: [a_a8uU]).
    Sing t_a9jk
    -> Sing t_a9jl -> Sing (Listmap t_a9jk t_a9jl :: [b_a8uV]) :: Type)
sListunzip ::
  (forall (t_a9jp :: [(a_a8uW, b_a8uX)]).
    Sing t_a9jp
    -> Sing (Listunzip t_a9jp :: ([a_a8uW], [b_a8uX])) :: Type)
sListtranspose ::
  (forall (t_a9jr :: [[a_a8uY]]).
    Sing t_a9jr -> Sing (Listtranspose t_a9jr :: [[a_a8uY]]) :: Type)
sListnubBy ::
  (forall (t_a9jt :: (~>) a_a8uZ ((~>) a_a8uZ Bool))
          (t_a9ju :: [a_a8uZ]).
    Sing t_a9jt
    -> Sing t_a9ju
      -> Sing (ListnubBy t_a9jt t_a9ju :: [a_a8uZ]) :: Type)
sListzipWith ::
  (forall (t_a9jy :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2))
          (t_a9jz :: [a_a8v0])
          (t_a9jA :: [b_a8v1]).
    Sing t_a9jy
    -> Sing t_a9jz
      -> Sing t_a9jA
          -> Sing (ListzipWith t_a9jy t_a9jz t_a9jA :: [c_a8v2]) :: Type)
sListzip ::
  (forall (t_a9jI :: [a_a8v3]) (t_a9jJ :: [b_a8v4]).
    Sing t_a9jI
    -> Sing t_a9jJ
      -> Sing (Listzip t_a9jI t_a9jJ :: [(a_a8v3, b_a8v4)]) :: Type)
sListisPrefixOf ::
  (forall (t_a9jN :: [a_a8v5]) (t_a9jO :: [a_a8v5]).
    SEq a_a8v5 =>
    Sing t_a9jN
    -> Sing t_a9jO
      -> Sing (ListisPrefixOf t_a9jN t_a9jO :: Bool) :: Type)
sListsortBy ::
  (forall (t_a9jS :: (~>) a_a8v6 ((~>) a_a8v6 Ordering))
          (t_a9jT :: [a_a8v6]).
    Sing t_a9jS
    -> Sing t_a9jT
      -> Sing (ListsortBy t_a9jS t_a9jT :: [a_a8v6]) :: Type)
sListpartition ::
  (forall (t_a9jX :: (~>) a_a8v7 Bool) (t_a9jY :: [a_a8v7]).
    Sing t_a9jX
    -> Sing t_a9jY
      -> Sing (Listpartition t_a9jX t_a9jY :: ([a_a8v7],
                                                [a_a8v7])) :: Type)
sListfilter ::
  (forall (t_a9k2 :: (~>) a_a8v8 Bool) (t_a9k3 :: [a_a8v8]).
    Sing t_a9k2
    -> Sing t_a9k3
      -> Sing (Listfilter t_a9k2 t_a9k3 :: [a_a8v8]) :: Type)
sListspan ::
  (forall (t_a9k7 :: (~>) a_a8v9 Bool) (t_a9k8 :: [a_a8v9]).
    Sing t_a9k7
    -> Sing t_a9k8
      -> Sing (Listspan t_a9k7 t_a9k8 :: ([a_a8v9], [a_a8v9])) :: Type)
sListdropWhile ::
  (forall (t_a9kc :: (~>) a_a8va Bool) (t_a9kd :: [a_a8va]).
    Sing t_a9kc
    -> Sing t_a9kd
      -> Sing (ListdropWhile t_a9kc t_a9kd :: [a_a8va]) :: Type)
sListtakeWhile ::
  (forall (t_a9kh :: (~>) a_a8vb Bool) (t_a9ki :: [a_a8vb]).
    Sing t_a9kh
    -> Sing t_a9ki
      -> Sing (ListtakeWhile t_a9kh t_a9ki :: [a_a8vb]) :: Type)
sListreverse ::
  (forall (t_a9km :: [a_a8vc]).
    Sing t_a9km -> Sing (Listreverse t_a9km :: [a_a8vc]) :: Type)
sListintersperse ::
  (forall (t_a9ko :: a_a8vd) (t_a9kp :: [a_a8vd]).
    Sing t_a9ko
    -> Sing t_a9kp
      -> Sing (Listintersperse t_a9ko t_a9kp :: [a_a8vd]) :: Type)
sListscanr1 ::
  (forall (t_a9kt :: (~>) a_a8ve ((~>) a_a8ve a_a8ve))
          (t_a9ku :: [a_a8ve]).
    Sing t_a9kt
    -> Sing t_a9ku
      -> Sing (Listscanr1 t_a9kt t_a9ku :: [a_a8ve]) :: Type)
sListscanr ::
  (forall (t_a9ky :: (~>) a_a8vf ((~>) b_a8vg b_a8vg))
          (t_a9kz :: b_a8vg)
          (t_a9kA :: [a_a8vf]).
    Sing t_a9ky
    -> Sing t_a9kz
      -> Sing t_a9kA
          -> Sing (Listscanr t_a9ky t_a9kz t_a9kA :: [b_a8vg]) :: Type)
sListscanl ::
  (forall (t_a9kI :: (~>) b_a8vh ((~>) a_a8vi b_a8vh))
          (t_a9kJ :: b_a8vh)
          (t_a9kK :: [a_a8vi]).
    Sing t_a9kI
    -> Sing t_a9kJ
      -> Sing t_a9kK
          -> Sing (Listscanl t_a9kI t_a9kJ t_a9kK :: [b_a8vh]) :: Type)
sListinsert ::
  (forall (t_a9kS :: a_a8vj) (t_a9kT :: [a_a8vj]).
    SOrd a_a8vj =>
    Sing t_a9kS
    -> Sing t_a9kT
      -> Sing (Listinsert t_a9kS t_a9kT :: [a_a8vj]) :: Type)
sListtails ::
  (forall (t_a9kX :: [a_a8vk]).
    Sing t_a9kX -> Sing (Listtails t_a9kX :: [[a_a8vk]]) :: Type)
sListinits ::
  (forall (t_a9kZ :: [a_a8vl]).
    Sing t_a9kZ -> Sing (Listinits t_a9kZ :: [[a_a8vl]]) :: Type)
sListsort ::
  (forall (t_a9l1 :: [a_a8vm]).
    SOrd a_a8vm =>
    Sing t_a9l1 -> Sing (Listsort t_a9l1 :: [a_a8vm]) :: Type)
sListinit ::
  (forall (t_a9l3 :: [a_a8vn]).
    Sing t_a9l3 -> Sing (Listinit t_a9l3 :: [a_a8vn]) :: Type)
sListlast ::
  (forall (t_a9l5 :: [a_a8vo]).
    Sing t_a9l5 -> Sing (Listlast t_a9l5 :: a_a8vo) :: Type)
sListsum
  (sA_6989586621679045181 :: Sing a_6989586621679045181_a9cS)
  = applySing (singFun1 @SumSym0 sSum) sA_6989586621679045181
sListproduct
  (sA_6989586621679045187 :: Sing a_6989586621679045187_a9cY)
  = applySing (singFun1 @ProductSym0 sProduct) sA_6989586621679045187
sListnull
  (sA_6989586621679045193 :: Sing a_6989586621679045193_a9d4)
  = applySing (singFun1 @NullSym0 sNull) sA_6989586621679045193
sListminimum
  (sA_6989586621679045199 :: Sing a_6989586621679045199_a9da)
  = applySing (singFun1 @MinimumSym0 sMinimum) sA_6989586621679045199
sListmaximum
  (sA_6989586621679045205 :: Sing a_6989586621679045205_a9dg)
  = applySing (singFun1 @MaximumSym0 sMaximum) sA_6989586621679045205
sListfoldr1
  (sA_6989586621679045211 :: Sing a_6989586621679045211_a9dq)
  (sA_6989586621679045213 :: Sing a_6989586621679045213_a9dr)
  = applySing
      (applySing (singFun2 @Foldr1Sym0 sFoldr1) sA_6989586621679045211)
      sA_6989586621679045213
sListfoldr
  (sA_6989586621679045222 :: Sing a_6989586621679045222_a9dF)
  (sA_6989586621679045224 :: Sing a_6989586621679045224_a9dG)
  (sA_6989586621679045226 :: Sing a_6989586621679045226_a9dH)
  = applySing
      (applySing
          (applySing (singFun3 @FoldrSym0 sFoldr) sA_6989586621679045222)
          sA_6989586621679045224)
      sA_6989586621679045226
sListfoldl1
  (sA_6989586621679045238 :: Sing a_6989586621679045238_a9dR)
  (sA_6989586621679045240 :: Sing a_6989586621679045240_a9dS)
  = applySing
      (applySing (singFun2 @Foldl1Sym0 sFoldl1) sA_6989586621679045238)
      sA_6989586621679045240
sListfoldl'
  (sA_6989586621679045249 :: Sing a_6989586621679045249_a9e6)
  (sA_6989586621679045251 :: Sing a_6989586621679045251_a9e7)
  (sA_6989586621679045253 :: Sing a_6989586621679045253_a9e8)
  = applySing
      (applySing
          (applySing (singFun3 @Foldl'Sym0 sFoldl') sA_6989586621679045249)
          sA_6989586621679045251)
      sA_6989586621679045253
sListfoldl
  (sA_6989586621679045265 :: Sing a_6989586621679045265_a9em)
  (sA_6989586621679045267 :: Sing a_6989586621679045267_a9en)
  (sA_6989586621679045269 :: Sing a_6989586621679045269_a9eo)
  = applySing
      (applySing
          (applySing (singFun3 @FoldlSym0 sFoldl) sA_6989586621679045265)
          sA_6989586621679045267)
      sA_6989586621679045269
sListelem
  (sA_6989586621679045281 :: Sing a_6989586621679045281_a9ey)
  (sA_6989586621679045283 :: Sing a_6989586621679045283_a9ez)
  = applySing
      (applySing (singFun2 @ElemSym0 sElem) sA_6989586621679045281)
      sA_6989586621679045283
sListmap
  (sA_6989586621679045292 :: Sing a_6989586621679045292_a9eJ)
  (sA_6989586621679045294 :: Sing a_6989586621679045294_a9eK)
  = applySing
      (applySing (singFun2 @MapSym0 sMap) sA_6989586621679045292)
      sA_6989586621679045294
sListunzip
  (sA_6989586621679045303 :: Sing a_6989586621679045303_a9eQ)
  = applySing (singFun1 @UnzipSym0 sUnzip) sA_6989586621679045303
sListtranspose
  (sA_6989586621679045309 :: Sing a_6989586621679045309_a9eW)
  = applySing
      (singFun1 @TransposeSym0 sTranspose) sA_6989586621679045309
sListnubBy
  (sA_6989586621679045315 :: Sing a_6989586621679045315_a9f6)
  (sA_6989586621679045317 :: Sing a_6989586621679045317_a9f7)
  = applySing
      (applySing (singFun2 @NubBySym0 sNubBy) sA_6989586621679045315)
      sA_6989586621679045317
sListzipWith
  (sA_6989586621679045326 :: Sing a_6989586621679045326_a9fl)
  (sA_6989586621679045328 :: Sing a_6989586621679045328_a9fm)
  (sA_6989586621679045330 :: Sing a_6989586621679045330_a9fn)
  = applySing
      (applySing
          (applySing (singFun3 @ZipWithSym0 sZipWith) sA_6989586621679045326)
          sA_6989586621679045328)
      sA_6989586621679045330
sListzip
  (sA_6989586621679045342 :: Sing a_6989586621679045342_a9fx)
  (sA_6989586621679045344 :: Sing a_6989586621679045344_a9fy)
  = applySing
      (applySing (singFun2 @ZipSym0 sZip) sA_6989586621679045342)
      sA_6989586621679045344
sListisPrefixOf
  (sA_6989586621679045353 :: Sing a_6989586621679045353_a9fI)
  (sA_6989586621679045355 :: Sing a_6989586621679045355_a9fJ)
  = applySing
      (applySing
          (singFun2 @IsPrefixOfSym0 sIsPrefixOf) sA_6989586621679045353)
      sA_6989586621679045355
sListsortBy
  (sA_6989586621679045364 :: Sing a_6989586621679045364_a9fT)
  (sA_6989586621679045366 :: Sing a_6989586621679045366_a9fU)
  = applySing
      (applySing (singFun2 @SortBySym0 sSortBy) sA_6989586621679045364)
      sA_6989586621679045366
sListpartition
  (sA_6989586621679045375 :: Sing a_6989586621679045375_a9g4)
  (sA_6989586621679045377 :: Sing a_6989586621679045377_a9g5)
  = applySing
      (applySing
          (singFun2 @PartitionSym0 sPartition) sA_6989586621679045375)
      sA_6989586621679045377
sListfilter
  (sA_6989586621679045386 :: Sing a_6989586621679045386_a9gf)
  (sA_6989586621679045388 :: Sing a_6989586621679045388_a9gg)
  = applySing
      (applySing (singFun2 @FilterSym0 sFilter) sA_6989586621679045386)
      sA_6989586621679045388
sListspan
  (sA_6989586621679045397 :: Sing a_6989586621679045397_a9gq)
  (sA_6989586621679045399 :: Sing a_6989586621679045399_a9gr)
  = applySing
      (applySing (singFun2 @SpanSym0 sSpan) sA_6989586621679045397)
      sA_6989586621679045399
sListdropWhile
  (sA_6989586621679045408 :: Sing a_6989586621679045408_a9gB)
  (sA_6989586621679045410 :: Sing a_6989586621679045410_a9gC)
  = applySing
      (applySing
          (singFun2 @DropWhileSym0 sDropWhile) sA_6989586621679045408)
      sA_6989586621679045410
sListtakeWhile
  (sA_6989586621679045419 :: Sing a_6989586621679045419_a9gM)
  (sA_6989586621679045421 :: Sing a_6989586621679045421_a9gN)
  = applySing
      (applySing
          (singFun2 @TakeWhileSym0 sTakeWhile) sA_6989586621679045419)
      sA_6989586621679045421
sListreverse
  (sA_6989586621679045430 :: Sing a_6989586621679045430_a9gT)
  = applySing (singFun1 @ReverseSym0 sReverse) sA_6989586621679045430
sListintersperse
  (sA_6989586621679045436 :: Sing a_6989586621679045436_a9h3)
  (sA_6989586621679045438 :: Sing a_6989586621679045438_a9h4)
  = applySing
      (applySing
          (singFun2 @IntersperseSym0 sIntersperse) sA_6989586621679045436)
      sA_6989586621679045438
sListscanr1
  (sA_6989586621679045447 :: Sing a_6989586621679045447_a9he)
  (sA_6989586621679045449 :: Sing a_6989586621679045449_a9hf)
  = applySing
      (applySing (singFun2 @Scanr1Sym0 sScanr1) sA_6989586621679045447)
      sA_6989586621679045449
sListscanr
  (sA_6989586621679045458 :: Sing a_6989586621679045458_a9ht)
  (sA_6989586621679045460 :: Sing a_6989586621679045460_a9hu)
  (sA_6989586621679045462 :: Sing a_6989586621679045462_a9hv)
  = applySing
      (applySing
          (applySing (singFun3 @ScanrSym0 sScanr) sA_6989586621679045458)
          sA_6989586621679045460)
      sA_6989586621679045462
sListscanl
  (sA_6989586621679045474 :: Sing a_6989586621679045474_a9hJ)
  (sA_6989586621679045476 :: Sing a_6989586621679045476_a9hK)
  (sA_6989586621679045478 :: Sing a_6989586621679045478_a9hL)
  = applySing
      (applySing
          (applySing (singFun3 @ScanlSym0 sScanl) sA_6989586621679045474)
          sA_6989586621679045476)
      sA_6989586621679045478
sListinsert
  (sA_6989586621679045490 :: Sing a_6989586621679045490_a9hV)
  (sA_6989586621679045492 :: Sing a_6989586621679045492_a9hW)
  = applySing
      (applySing (singFun2 @InsertSym0 sInsert) sA_6989586621679045490)
      sA_6989586621679045492
sListtails
  (sA_6989586621679045501 :: Sing a_6989586621679045501_a9i2)
  = applySing (singFun1 @TailsSym0 sTails) sA_6989586621679045501
sListinits
  (sA_6989586621679045507 :: Sing a_6989586621679045507_a9i8)
  = applySing (singFun1 @InitsSym0 sInits) sA_6989586621679045507
sListsort
  (sA_6989586621679045513 :: Sing a_6989586621679045513_a9ie)
  = applySing (singFun1 @SortSym0 sSort) sA_6989586621679045513
sListinit
  (sA_6989586621679045519 :: Sing a_6989586621679045519_a9ik)
  = applySing (singFun1 @InitSym0 sInit) sA_6989586621679045519
sListlast
  (sA_6989586621679045525 :: Sing a_6989586621679045525_a9iq)
  = applySing (singFun1 @LastSym0 sLast) sA_6989586621679045525
instance SNum a_a8uG =>
          SingI (ListsumSym0 :: (~>) [a_a8uG] a_a8uG) where
  sing = singFun1 @ListsumSym0 sListsum
instance SNum a_a8uH =>
          SingI (ListproductSym0 :: (~>) [a_a8uH] a_a8uH) where
  sing = singFun1 @ListproductSym0 sListproduct
instance SingI (ListnullSym0 :: (~>) [a_a8uI] Bool) where
  sing = singFun1 @ListnullSym0 sListnull
instance SOrd a_a8uJ =>
          SingI (ListminimumSym0 :: (~>) [a_a8uJ] a_a8uJ) where
  sing = singFun1 @ListminimumSym0 sListminimum
instance SOrd a_a8uK =>
          SingI (ListmaximumSym0 :: (~>) [a_a8uK] a_a8uK) where
  sing = singFun1 @ListmaximumSym0 sListmaximum
instance SingI (Listfoldr1Sym0 :: (~>) ((~>) a_a8uL ((~>) a_a8uL a_a8uL)) ((~>) [a_a8uL] a_a8uL)) where
  sing = singFun2 @Listfoldr1Sym0 sListfoldr1
instance SingI d_a9iD =>
          SingI (Listfoldr1Sym1 (d_a9iD :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)) :: (~>) [a_a8uL] a_a8uL) where
  sing
    = singFun1
        @(Listfoldr1Sym1 (d_a9iD :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)))
        (sListfoldr1 (sing @d_a9iD))
instance SingI1 (Listfoldr1Sym1 :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)
                                    -> (~>) [a_a8uL] a_a8uL) where
  liftSing
    (s_a9iF :: Sing (d_a9iD :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)))
    = singFun1
        @(Listfoldr1Sym1 (d_a9iD :: (~>) a_a8uL ((~>) a_a8uL a_a8uL)))
        (sListfoldr1 s_a9iF)
instance SingI (ListfoldrSym0 :: (~>) ((~>) a_a8uM ((~>) b_a8uN b_a8uN)) ((~>) b_a8uN ((~>) [a_a8uM] b_a8uN))) where
  sing = singFun3 @ListfoldrSym0 sListfoldr
instance SingI d_a9iJ =>
          SingI (ListfoldrSym1 (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) :: (~>) b_a8uN ((~>) [a_a8uM] b_a8uN)) where
  sing
    = singFun2
        @(ListfoldrSym1 (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)))
        (sListfoldr (sing @d_a9iJ))
instance SingI1 (ListfoldrSym1 :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)
                                  -> (~>) b_a8uN ((~>) [a_a8uM] b_a8uN)) where
  liftSing
    (s_a9iP :: Sing (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)))
    = singFun2
        @(ListfoldrSym1 (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)))
        (sListfoldr s_a9iP)
instance (SingI d_a9iJ, SingI d_a9iK) =>
          SingI (ListfoldrSym2 (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) (d_a9iK :: b_a8uN) :: (~>) [a_a8uM] b_a8uN) where
  sing
    = singFun1
        @(ListfoldrSym2 (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) (d_a9iK :: b_a8uN))
        (sListfoldr (sing @d_a9iJ) (sing @d_a9iK))
instance SingI d_a9iJ =>
          SingI1 (ListfoldrSym2 (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) :: b_a8uN
                                                                                -> (~>) [a_a8uM] b_a8uN) where
  liftSing (s_a9iM :: Sing (d_a9iK :: b_a8uN))
    = singFun1
        @(ListfoldrSym2 (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) (d_a9iK :: b_a8uN))
        (sListfoldr (sing @d_a9iJ) s_a9iM)
instance SingI2 (ListfoldrSym2 :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)
                                  -> b_a8uN -> (~>) [a_a8uM] b_a8uN) where
  liftSing2
    (s_a9iN :: Sing (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)))
    (s_a9iO :: Sing (d_a9iK :: b_a8uN))
    = singFun1
        @(ListfoldrSym2 (d_a9iJ :: (~>) a_a8uM ((~>) b_a8uN b_a8uN)) (d_a9iK :: b_a8uN))
        (sListfoldr s_a9iN s_a9iO)
instance SingI (Listfoldl1Sym0 :: (~>) ((~>) a_a8uO ((~>) a_a8uO a_a8uO)) ((~>) [a_a8uO] a_a8uO)) where
  sing = singFun2 @Listfoldl1Sym0 sListfoldl1
instance SingI d_a9iS =>
          SingI (Listfoldl1Sym1 (d_a9iS :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)) :: (~>) [a_a8uO] a_a8uO) where
  sing
    = singFun1
        @(Listfoldl1Sym1 (d_a9iS :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)))
        (sListfoldl1 (sing @d_a9iS))
instance SingI1 (Listfoldl1Sym1 :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)
                                    -> (~>) [a_a8uO] a_a8uO) where
  liftSing
    (s_a9iU :: Sing (d_a9iS :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)))
    = singFun1
        @(Listfoldl1Sym1 (d_a9iS :: (~>) a_a8uO ((~>) a_a8uO a_a8uO)))
        (sListfoldl1 s_a9iU)
instance SingI (Listfoldl'Sym0 :: (~>) ((~>) b_a8uP ((~>) a_a8uQ b_a8uP)) ((~>) b_a8uP ((~>) [a_a8uQ] b_a8uP))) where
  sing = singFun3 @Listfoldl'Sym0 sListfoldl'
instance SingI d_a9iY =>
          SingI (Listfoldl'Sym1 (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) :: (~>) b_a8uP ((~>) [a_a8uQ] b_a8uP)) where
  sing
    = singFun2
        @(Listfoldl'Sym1 (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)))
        (sListfoldl' (sing @d_a9iY))
instance SingI1 (Listfoldl'Sym1 :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)
                                    -> (~>) b_a8uP ((~>) [a_a8uQ] b_a8uP)) where
  liftSing
    (s_a9j4 :: Sing (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)))
    = singFun2
        @(Listfoldl'Sym1 (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)))
        (sListfoldl' s_a9j4)
instance (SingI d_a9iY, SingI d_a9iZ) =>
          SingI (Listfoldl'Sym2 (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) (d_a9iZ :: b_a8uP) :: (~>) [a_a8uQ] b_a8uP) where
  sing
    = singFun1
        @(Listfoldl'Sym2 (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) (d_a9iZ :: b_a8uP))
        (sListfoldl' (sing @d_a9iY) (sing @d_a9iZ))
instance SingI d_a9iY =>
          SingI1 (Listfoldl'Sym2 (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) :: b_a8uP
                                                                                -> (~>) [a_a8uQ] b_a8uP) where
  liftSing (s_a9j1 :: Sing (d_a9iZ :: b_a8uP))
    = singFun1
        @(Listfoldl'Sym2 (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) (d_a9iZ :: b_a8uP))
        (sListfoldl' (sing @d_a9iY) s_a9j1)
instance SingI2 (Listfoldl'Sym2 :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)
                                    -> b_a8uP -> (~>) [a_a8uQ] b_a8uP) where
  liftSing2
    (s_a9j2 :: Sing (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)))
    (s_a9j3 :: Sing (d_a9iZ :: b_a8uP))
    = singFun1
        @(Listfoldl'Sym2 (d_a9iY :: (~>) b_a8uP ((~>) a_a8uQ b_a8uP)) (d_a9iZ :: b_a8uP))
        (sListfoldl' s_a9j2 s_a9j3)
instance SingI (ListfoldlSym0 :: (~>) ((~>) b_a8uR ((~>) a_a8uS b_a8uR)) ((~>) b_a8uR ((~>) [a_a8uS] b_a8uR))) where
  sing = singFun3 @ListfoldlSym0 sListfoldl
instance SingI d_a9j8 =>
          SingI (ListfoldlSym1 (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) :: (~>) b_a8uR ((~>) [a_a8uS] b_a8uR)) where
  sing
    = singFun2
        @(ListfoldlSym1 (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)))
        (sListfoldl (sing @d_a9j8))
instance SingI1 (ListfoldlSym1 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)
                                  -> (~>) b_a8uR ((~>) [a_a8uS] b_a8uR)) where
  liftSing
    (s_a9je :: Sing (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)))
    = singFun2
        @(ListfoldlSym1 (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)))
        (sListfoldl s_a9je)
instance (SingI d_a9j8, SingI d_a9j9) =>
          SingI (ListfoldlSym2 (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) (d_a9j9 :: b_a8uR) :: (~>) [a_a8uS] b_a8uR) where
  sing
    = singFun1
        @(ListfoldlSym2 (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) (d_a9j9 :: b_a8uR))
        (sListfoldl (sing @d_a9j8) (sing @d_a9j9))
instance SingI d_a9j8 =>
          SingI1 (ListfoldlSym2 (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) :: b_a8uR
                                                                                -> (~>) [a_a8uS] b_a8uR) where
  liftSing (s_a9jb :: Sing (d_a9j9 :: b_a8uR))
    = singFun1
        @(ListfoldlSym2 (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) (d_a9j9 :: b_a8uR))
        (sListfoldl (sing @d_a9j8) s_a9jb)
instance SingI2 (ListfoldlSym2 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)
                                  -> b_a8uR -> (~>) [a_a8uS] b_a8uR) where
  liftSing2
    (s_a9jc :: Sing (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)))
    (s_a9jd :: Sing (d_a9j9 :: b_a8uR))
    = singFun1
        @(ListfoldlSym2 (d_a9j8 :: (~>) b_a8uR ((~>) a_a8uS b_a8uR)) (d_a9j9 :: b_a8uR))
        (sListfoldl s_a9jc s_a9jd)
instance SEq a_a8uT =>
          SingI (ListelemSym0 :: (~>) a_a8uT ((~>) [a_a8uT] Bool)) where
  sing = singFun2 @ListelemSym0 sListelem
instance (SEq a_a8uT, SingI d_a9jh) =>
          SingI (ListelemSym1 (d_a9jh :: a_a8uT) :: (~>) [a_a8uT] Bool) where
  sing
    = singFun1
        @(ListelemSym1 (d_a9jh :: a_a8uT)) (sListelem (sing @d_a9jh))
instance SEq a_a8uT =>
          SingI1 (ListelemSym1 :: a_a8uT -> (~>) [a_a8uT] Bool) where
  liftSing (s_a9jj :: Sing (d_a9jh :: a_a8uT))
    = singFun1 @(ListelemSym1 (d_a9jh :: a_a8uT)) (sListelem s_a9jj)
instance SingI (ListmapSym0 :: (~>) ((~>) a_a8uU b_a8uV) ((~>) [a_a8uU] [b_a8uV])) where
  sing = singFun2 @ListmapSym0 sListmap
instance SingI d_a9jm =>
          SingI (ListmapSym1 (d_a9jm :: (~>) a_a8uU b_a8uV) :: (~>) [a_a8uU] [b_a8uV]) where
  sing
    = singFun1
        @(ListmapSym1 (d_a9jm :: (~>) a_a8uU b_a8uV))
        (sListmap (sing @d_a9jm))
instance SingI1 (ListmapSym1 :: (~>) a_a8uU b_a8uV
                                -> (~>) [a_a8uU] [b_a8uV]) where
  liftSing (s_a9jo :: Sing (d_a9jm :: (~>) a_a8uU b_a8uV))
    = singFun1
        @(ListmapSym1 (d_a9jm :: (~>) a_a8uU b_a8uV)) (sListmap s_a9jo)
instance SingI (ListunzipSym0 :: (~>) [(a_a8uW, b_a8uX)] ([a_a8uW],
                                                          [b_a8uX])) where
  sing = singFun1 @ListunzipSym0 sListunzip
instance SingI (ListtransposeSym0 :: (~>) [[a_a8uY]] [[a_a8uY]]) where
  sing = singFun1 @ListtransposeSym0 sListtranspose
instance SingI (ListnubBySym0 :: (~>) ((~>) a_a8uZ ((~>) a_a8uZ Bool)) ((~>) [a_a8uZ] [a_a8uZ])) where
  sing = singFun2 @ListnubBySym0 sListnubBy
instance SingI d_a9jv =>
          SingI (ListnubBySym1 (d_a9jv :: (~>) a_a8uZ ((~>) a_a8uZ Bool)) :: (~>) [a_a8uZ] [a_a8uZ]) where
  sing
    = singFun1
        @(ListnubBySym1 (d_a9jv :: (~>) a_a8uZ ((~>) a_a8uZ Bool)))
        (sListnubBy (sing @d_a9jv))
instance SingI1 (ListnubBySym1 :: (~>) a_a8uZ ((~>) a_a8uZ Bool)
                                  -> (~>) [a_a8uZ] [a_a8uZ]) where
  liftSing
    (s_a9jx :: Sing (d_a9jv :: (~>) a_a8uZ ((~>) a_a8uZ Bool)))
    = singFun1
        @(ListnubBySym1 (d_a9jv :: (~>) a_a8uZ ((~>) a_a8uZ Bool)))
        (sListnubBy s_a9jx)
instance SingI (ListzipWithSym0 :: (~>) ((~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) ((~>) [a_a8v0] ((~>) [b_a8v1] [c_a8v2]))) where
  sing = singFun3 @ListzipWithSym0 sListzipWith
instance SingI d_a9jB =>
          SingI (ListzipWithSym1 (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) :: (~>) [a_a8v0] ((~>) [b_a8v1] [c_a8v2])) where
  sing
    = singFun2
        @(ListzipWithSym1 (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)))
        (sListzipWith (sing @d_a9jB))
instance SingI1 (ListzipWithSym1 :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)
                                    -> (~>) [a_a8v0] ((~>) [b_a8v1] [c_a8v2])) where
  liftSing
    (s_a9jH :: Sing (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)))
    = singFun2
        @(ListzipWithSym1 (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)))
        (sListzipWith s_a9jH)
instance (SingI d_a9jB, SingI d_a9jC) =>
          SingI (ListzipWithSym2 (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) (d_a9jC :: [a_a8v0]) :: (~>) [b_a8v1] [c_a8v2]) where
  sing
    = singFun1
        @(ListzipWithSym2 (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) (d_a9jC :: [a_a8v0]))
        (sListzipWith (sing @d_a9jB) (sing @d_a9jC))
instance SingI d_a9jB =>
          SingI1 (ListzipWithSym2 (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) :: [a_a8v0]
                                                                                  -> (~>) [b_a8v1] [c_a8v2]) where
  liftSing (s_a9jE :: Sing (d_a9jC :: [a_a8v0]))
    = singFun1
        @(ListzipWithSym2 (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) (d_a9jC :: [a_a8v0]))
        (sListzipWith (sing @d_a9jB) s_a9jE)
instance SingI2 (ListzipWithSym2 :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)
                                    -> [a_a8v0] -> (~>) [b_a8v1] [c_a8v2]) where
  liftSing2
    (s_a9jF :: Sing (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)))
    (s_a9jG :: Sing (d_a9jC :: [a_a8v0]))
    = singFun1
        @(ListzipWithSym2 (d_a9jB :: (~>) a_a8v0 ((~>) b_a8v1 c_a8v2)) (d_a9jC :: [a_a8v0]))
        (sListzipWith s_a9jF s_a9jG)
instance SingI (ListzipSym0 :: (~>) [a_a8v3] ((~>) [b_a8v4] [(a_a8v3,
                                                              b_a8v4)])) where
  sing = singFun2 @ListzipSym0 sListzip
instance SingI d_a9jK =>
          SingI (ListzipSym1 (d_a9jK :: [a_a8v3]) :: (~>) [b_a8v4] [(a_a8v3,
                                                                    b_a8v4)]) where
  sing
    = singFun1
        @(ListzipSym1 (d_a9jK :: [a_a8v3])) (sListzip (sing @d_a9jK))
instance SingI1 (ListzipSym1 :: [a_a8v3]
                                -> (~>) [b_a8v4] [(a_a8v3, b_a8v4)]) where
  liftSing (s_a9jM :: Sing (d_a9jK :: [a_a8v3]))
    = singFun1 @(ListzipSym1 (d_a9jK :: [a_a8v3])) (sListzip s_a9jM)
instance SEq a_a8v5 =>
          SingI (ListisPrefixOfSym0 :: (~>) [a_a8v5] ((~>) [a_a8v5] Bool)) where
  sing = singFun2 @ListisPrefixOfSym0 sListisPrefixOf
instance (SEq a_a8v5, SingI d_a9jP) =>
          SingI (ListisPrefixOfSym1 (d_a9jP :: [a_a8v5]) :: (~>) [a_a8v5] Bool) where
  sing
    = singFun1
        @(ListisPrefixOfSym1 (d_a9jP :: [a_a8v5]))
        (sListisPrefixOf (sing @d_a9jP))
instance SEq a_a8v5 =>
          SingI1 (ListisPrefixOfSym1 :: [a_a8v5] -> (~>) [a_a8v5] Bool) where
  liftSing (s_a9jR :: Sing (d_a9jP :: [a_a8v5]))
    = singFun1
        @(ListisPrefixOfSym1 (d_a9jP :: [a_a8v5])) (sListisPrefixOf s_a9jR)
instance SingI (ListsortBySym0 :: (~>) ((~>) a_a8v6 ((~>) a_a8v6 Ordering)) ((~>) [a_a8v6] [a_a8v6])) where
  sing = singFun2 @ListsortBySym0 sListsortBy
instance SingI d_a9jU =>
          SingI (ListsortBySym1 (d_a9jU :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)) :: (~>) [a_a8v6] [a_a8v6]) where
  sing
    = singFun1
        @(ListsortBySym1 (d_a9jU :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)))
        (sListsortBy (sing @d_a9jU))
instance SingI1 (ListsortBySym1 :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)
                                    -> (~>) [a_a8v6] [a_a8v6]) where
  liftSing
    (s_a9jW :: Sing (d_a9jU :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)))
    = singFun1
        @(ListsortBySym1 (d_a9jU :: (~>) a_a8v6 ((~>) a_a8v6 Ordering)))
        (sListsortBy s_a9jW)
instance SingI (ListpartitionSym0 :: (~>) ((~>) a_a8v7 Bool) ((~>) [a_a8v7] ([a_a8v7],
                                                                              [a_a8v7]))) where
  sing = singFun2 @ListpartitionSym0 sListpartition
instance SingI d_a9jZ =>
          SingI (ListpartitionSym1 (d_a9jZ :: (~>) a_a8v7 Bool) :: (~>) [a_a8v7] ([a_a8v7],
                                                                                  [a_a8v7])) where
  sing
    = singFun1
        @(ListpartitionSym1 (d_a9jZ :: (~>) a_a8v7 Bool))
        (sListpartition (sing @d_a9jZ))
instance SingI1 (ListpartitionSym1 :: (~>) a_a8v7 Bool
                                      -> (~>) [a_a8v7] ([a_a8v7], [a_a8v7])) where
  liftSing (s_a9k1 :: Sing (d_a9jZ :: (~>) a_a8v7 Bool))
    = singFun1
        @(ListpartitionSym1 (d_a9jZ :: (~>) a_a8v7 Bool))
        (sListpartition s_a9k1)
instance SingI (ListfilterSym0 :: (~>) ((~>) a_a8v8 Bool) ((~>) [a_a8v8] [a_a8v8])) where
  sing = singFun2 @ListfilterSym0 sListfilter
instance SingI d_a9k4 =>
          SingI (ListfilterSym1 (d_a9k4 :: (~>) a_a8v8 Bool) :: (~>) [a_a8v8] [a_a8v8]) where
  sing
    = singFun1
        @(ListfilterSym1 (d_a9k4 :: (~>) a_a8v8 Bool))
        (sListfilter (sing @d_a9k4))
instance SingI1 (ListfilterSym1 :: (~>) a_a8v8 Bool
                                    -> (~>) [a_a8v8] [a_a8v8]) where
  liftSing (s_a9k6 :: Sing (d_a9k4 :: (~>) a_a8v8 Bool))
    = singFun1
        @(ListfilterSym1 (d_a9k4 :: (~>) a_a8v8 Bool)) (sListfilter s_a9k6)
instance SingI (ListspanSym0 :: (~>) ((~>) a_a8v9 Bool) ((~>) [a_a8v9] ([a_a8v9],
                                                                        [a_a8v9]))) where
  sing = singFun2 @ListspanSym0 sListspan
instance SingI d_a9k9 =>
          SingI (ListspanSym1 (d_a9k9 :: (~>) a_a8v9 Bool) :: (~>) [a_a8v9] ([a_a8v9],
                                                                            [a_a8v9])) where
  sing
    = singFun1
        @(ListspanSym1 (d_a9k9 :: (~>) a_a8v9 Bool))
        (sListspan (sing @d_a9k9))
instance SingI1 (ListspanSym1 :: (~>) a_a8v9 Bool
                                  -> (~>) [a_a8v9] ([a_a8v9], [a_a8v9])) where
  liftSing (s_a9kb :: Sing (d_a9k9 :: (~>) a_a8v9 Bool))
    = singFun1
        @(ListspanSym1 (d_a9k9 :: (~>) a_a8v9 Bool)) (sListspan s_a9kb)
instance SingI (ListdropWhileSym0 :: (~>) ((~>) a_a8va Bool) ((~>) [a_a8va] [a_a8va])) where
  sing = singFun2 @ListdropWhileSym0 sListdropWhile
instance SingI d_a9ke =>
          SingI (ListdropWhileSym1 (d_a9ke :: (~>) a_a8va Bool) :: (~>) [a_a8va] [a_a8va]) where
  sing
    = singFun1
        @(ListdropWhileSym1 (d_a9ke :: (~>) a_a8va Bool))
        (sListdropWhile (sing @d_a9ke))
instance SingI1 (ListdropWhileSym1 :: (~>) a_a8va Bool
                                      -> (~>) [a_a8va] [a_a8va]) where
  liftSing (s_a9kg :: Sing (d_a9ke :: (~>) a_a8va Bool))
    = singFun1
        @(ListdropWhileSym1 (d_a9ke :: (~>) a_a8va Bool))
        (sListdropWhile s_a9kg)
instance SingI (ListtakeWhileSym0 :: (~>) ((~>) a_a8vb Bool) ((~>) [a_a8vb] [a_a8vb])) where
  sing = singFun2 @ListtakeWhileSym0 sListtakeWhile
instance SingI d_a9kj =>
          SingI (ListtakeWhileSym1 (d_a9kj :: (~>) a_a8vb Bool) :: (~>) [a_a8vb] [a_a8vb]) where
  sing
    = singFun1
        @(ListtakeWhileSym1 (d_a9kj :: (~>) a_a8vb Bool))
        (sListtakeWhile (sing @d_a9kj))
instance SingI1 (ListtakeWhileSym1 :: (~>) a_a8vb Bool
                                      -> (~>) [a_a8vb] [a_a8vb]) where
  liftSing (s_a9kl :: Sing (d_a9kj :: (~>) a_a8vb Bool))
    = singFun1
        @(ListtakeWhileSym1 (d_a9kj :: (~>) a_a8vb Bool))
        (sListtakeWhile s_a9kl)
instance SingI (ListreverseSym0 :: (~>) [a_a8vc] [a_a8vc]) where
  sing = singFun1 @ListreverseSym0 sListreverse
instance SingI (ListintersperseSym0 :: (~>) a_a8vd ((~>) [a_a8vd] [a_a8vd])) where
  sing = singFun2 @ListintersperseSym0 sListintersperse
instance SingI d_a9kq =>
          SingI (ListintersperseSym1 (d_a9kq :: a_a8vd) :: (~>) [a_a8vd] [a_a8vd]) where
  sing
    = singFun1
        @(ListintersperseSym1 (d_a9kq :: a_a8vd))
        (sListintersperse (sing @d_a9kq))
instance SingI1 (ListintersperseSym1 :: a_a8vd
                                        -> (~>) [a_a8vd] [a_a8vd]) where
  liftSing (s_a9ks :: Sing (d_a9kq :: a_a8vd))
    = singFun1
        @(ListintersperseSym1 (d_a9kq :: a_a8vd)) (sListintersperse s_a9ks)
instance SingI (Listscanr1Sym0 :: (~>) ((~>) a_a8ve ((~>) a_a8ve a_a8ve)) ((~>) [a_a8ve] [a_a8ve])) where
  sing = singFun2 @Listscanr1Sym0 sListscanr1
instance SingI d_a9kv =>
          SingI (Listscanr1Sym1 (d_a9kv :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)) :: (~>) [a_a8ve] [a_a8ve]) where
  sing
    = singFun1
        @(Listscanr1Sym1 (d_a9kv :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)))
        (sListscanr1 (sing @d_a9kv))
instance SingI1 (Listscanr1Sym1 :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)
                                    -> (~>) [a_a8ve] [a_a8ve]) where
  liftSing
    (s_a9kx :: Sing (d_a9kv :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)))
    = singFun1
        @(Listscanr1Sym1 (d_a9kv :: (~>) a_a8ve ((~>) a_a8ve a_a8ve)))
        (sListscanr1 s_a9kx)
instance SingI (ListscanrSym0 :: (~>) ((~>) a_a8vf ((~>) b_a8vg b_a8vg)) ((~>) b_a8vg ((~>) [a_a8vf] [b_a8vg]))) where
  sing = singFun3 @ListscanrSym0 sListscanr
instance SingI d_a9kB =>
          SingI (ListscanrSym1 (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) :: (~>) b_a8vg ((~>) [a_a8vf] [b_a8vg])) where
  sing
    = singFun2
        @(ListscanrSym1 (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)))
        (sListscanr (sing @d_a9kB))
instance SingI1 (ListscanrSym1 :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)
                                  -> (~>) b_a8vg ((~>) [a_a8vf] [b_a8vg])) where
  liftSing
    (s_a9kH :: Sing (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)))
    = singFun2
        @(ListscanrSym1 (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)))
        (sListscanr s_a9kH)
instance (SingI d_a9kB, SingI d_a9kC) =>
          SingI (ListscanrSym2 (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) (d_a9kC :: b_a8vg) :: (~>) [a_a8vf] [b_a8vg]) where
  sing
    = singFun1
        @(ListscanrSym2 (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) (d_a9kC :: b_a8vg))
        (sListscanr (sing @d_a9kB) (sing @d_a9kC))
instance SingI d_a9kB =>
          SingI1 (ListscanrSym2 (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) :: b_a8vg
                                                                                -> (~>) [a_a8vf] [b_a8vg]) where
  liftSing (s_a9kE :: Sing (d_a9kC :: b_a8vg))
    = singFun1
        @(ListscanrSym2 (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) (d_a9kC :: b_a8vg))
        (sListscanr (sing @d_a9kB) s_a9kE)
instance SingI2 (ListscanrSym2 :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)
                                  -> b_a8vg -> (~>) [a_a8vf] [b_a8vg]) where
  liftSing2
    (s_a9kF :: Sing (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)))
    (s_a9kG :: Sing (d_a9kC :: b_a8vg))
    = singFun1
        @(ListscanrSym2 (d_a9kB :: (~>) a_a8vf ((~>) b_a8vg b_a8vg)) (d_a9kC :: b_a8vg))
        (sListscanr s_a9kF s_a9kG)
instance SingI (ListscanlSym0 :: (~>) ((~>) b_a8vh ((~>) a_a8vi b_a8vh)) ((~>) b_a8vh ((~>) [a_a8vi] [b_a8vh]))) where
  sing = singFun3 @ListscanlSym0 sListscanl
instance SingI d_a9kL =>
          SingI (ListscanlSym1 (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) :: (~>) b_a8vh ((~>) [a_a8vi] [b_a8vh])) where
  sing
    = singFun2
        @(ListscanlSym1 (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)))
        (sListscanl (sing @d_a9kL))
instance SingI1 (ListscanlSym1 :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)
                                  -> (~>) b_a8vh ((~>) [a_a8vi] [b_a8vh])) where
  liftSing
    (s_a9kR :: Sing (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)))
    = singFun2
        @(ListscanlSym1 (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)))
        (sListscanl s_a9kR)
instance (SingI d_a9kL, SingI d_a9kM) =>
          SingI (ListscanlSym2 (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) (d_a9kM :: b_a8vh) :: (~>) [a_a8vi] [b_a8vh]) where
  sing
    = singFun1
        @(ListscanlSym2 (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) (d_a9kM :: b_a8vh))
        (sListscanl (sing @d_a9kL) (sing @d_a9kM))
instance SingI d_a9kL =>
          SingI1 (ListscanlSym2 (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) :: b_a8vh
                                                                                -> (~>) [a_a8vi] [b_a8vh]) where
  liftSing (s_a9kO :: Sing (d_a9kM :: b_a8vh))
    = singFun1
        @(ListscanlSym2 (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) (d_a9kM :: b_a8vh))
        (sListscanl (sing @d_a9kL) s_a9kO)
instance SingI2 (ListscanlSym2 :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)
                                  -> b_a8vh -> (~>) [a_a8vi] [b_a8vh]) where
  liftSing2
    (s_a9kP :: Sing (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)))
    (s_a9kQ :: Sing (d_a9kM :: b_a8vh))
    = singFun1
        @(ListscanlSym2 (d_a9kL :: (~>) b_a8vh ((~>) a_a8vi b_a8vh)) (d_a9kM :: b_a8vh))
        (sListscanl s_a9kP s_a9kQ)
instance SOrd a_a8vj =>
          SingI (ListinsertSym0 :: (~>) a_a8vj ((~>) [a_a8vj] [a_a8vj])) where
  sing = singFun2 @ListinsertSym0 sListinsert
instance (SOrd a_a8vj, SingI d_a9kU) =>
          SingI (ListinsertSym1 (d_a9kU :: a_a8vj) :: (~>) [a_a8vj] [a_a8vj]) where
  sing
    = singFun1
        @(ListinsertSym1 (d_a9kU :: a_a8vj)) (sListinsert (sing @d_a9kU))
instance SOrd a_a8vj =>
          SingI1 (ListinsertSym1 :: a_a8vj -> (~>) [a_a8vj] [a_a8vj]) where
  liftSing (s_a9kW :: Sing (d_a9kU :: a_a8vj))
    = singFun1
        @(ListinsertSym1 (d_a9kU :: a_a8vj)) (sListinsert s_a9kW)
instance SingI (ListtailsSym0 :: (~>) [a_a8vk] [[a_a8vk]]) where
  sing = singFun1 @ListtailsSym0 sListtails
instance SingI (ListinitsSym0 :: (~>) [a_a8vl] [[a_a8vl]]) where
  sing = singFun1 @ListinitsSym0 sListinits
instance SOrd a_a8vm =>
          SingI (ListsortSym0 :: (~>) [a_a8vm] [a_a8vm]) where
  sing = singFun1 @ListsortSym0 sListsort
instance SingI (ListinitSym0 :: (~>) [a_a8vn] [a_a8vn]) where
  sing = singFun1 @ListinitSym0 sListinit
instance SingI (ListlastSym0 :: (~>) [a_a8vo] a_a8vo) where
  sing = singFun1 @ListlastSym0 sListlast

type ListlengthSym0 :: (~>) [a_akDQ] Natural
data ListlengthSym0 :: (~>) [a_akDQ] Natural
  where
    ListlengthSym0KindInference :: SameKind (Apply ListlengthSym0 arg_akFz) (ListlengthSym1 arg_akFz) =>
                                    ListlengthSym0 a6989586621679089250
type instance Apply @[a_akDQ] @Natural ListlengthSym0 a6989586621679089250 = Listlength a6989586621679089250
instance SuppressUnusedWarnings ListlengthSym0 where
  suppressUnusedWarnings = snd ((,) ListlengthSym0KindInference ())
type ListlengthSym1 :: [a_akDQ] -> Natural
type family ListlengthSym1 @a_akDQ (a6989586621679089250 :: [a_akDQ]) :: Natural where
  ListlengthSym1 a6989586621679089250 = Listlength a6989586621679089250
type ListindexSym0 :: (~>) [a_akDR] ((~>) Natural a_akDR)
data ListindexSym0 :: (~>) [a_akDR] ((~>) Natural a_akDR)
  where
    ListindexSym0KindInference :: SameKind (Apply ListindexSym0 arg_akFI) (ListindexSym1 arg_akFI) =>
                                  ListindexSym0 a6989586621679089259
type instance Apply @[a_akDR] @((~>) Natural a_akDR) ListindexSym0 a6989586621679089259 = ListindexSym1 a6989586621679089259
instance SuppressUnusedWarnings ListindexSym0 where
  suppressUnusedWarnings = snd ((,) ListindexSym0KindInference ())
type ListindexSym1 :: [a_akDR] -> (~>) Natural a_akDR
data ListindexSym1 (a6989586621679089259 :: [a_akDR]) :: (~>) Natural a_akDR
  where
    ListindexSym1KindInference :: SameKind (Apply (ListindexSym1 a6989586621679089259) arg_akFI) (ListindexSym2 a6989586621679089259 arg_akFI) =>
                                  ListindexSym1 a6989586621679089259 a6989586621679089260
type instance Apply @Natural @a_akDR (ListindexSym1 a6989586621679089259) a6989586621679089260 = Listindex a6989586621679089259 a6989586621679089260
instance SuppressUnusedWarnings (ListindexSym1 a6989586621679089259) where
  suppressUnusedWarnings = snd ((,) ListindexSym1KindInference ())
type ListindexSym2 :: [a_akDR] -> Natural -> a_akDR
type family ListindexSym2 @a_akDR (a6989586621679089259 :: [a_akDR]) (a6989586621679089260 :: Natural) :: a_akDR where
  ListindexSym2 a6989586621679089259 a6989586621679089260 = Listindex a6989586621679089259 a6989586621679089260
type ListsplitAtSym0 :: (~>) Natural ((~>) [a_akDS] ([a_akDS],
                                                      [a_akDS]))
data ListsplitAtSym0 :: (~>) Natural ((~>) [a_akDS] ([a_akDS],
                                                      [a_akDS]))
  where
    ListsplitAtSym0KindInference :: SameKind (Apply ListsplitAtSym0 arg_akFT) (ListsplitAtSym1 arg_akFT) =>
                                    ListsplitAtSym0 a6989586621679089270
type instance Apply @Natural @((~>) [a_akDS] ([a_akDS],
                                              [a_akDS])) ListsplitAtSym0 a6989586621679089270 = ListsplitAtSym1 a6989586621679089270
instance SuppressUnusedWarnings ListsplitAtSym0 where
  suppressUnusedWarnings = snd ((,) ListsplitAtSym0KindInference ())
type ListsplitAtSym1 :: Natural
                        -> (~>) [a_akDS] ([a_akDS], [a_akDS])
data ListsplitAtSym1 (a6989586621679089270 :: Natural) :: (~>) [a_akDS] ([a_akDS],
                                                                          [a_akDS])
  where
    ListsplitAtSym1KindInference :: SameKind (Apply (ListsplitAtSym1 a6989586621679089270) arg_akFT) (ListsplitAtSym2 a6989586621679089270 arg_akFT) =>
                                    ListsplitAtSym1 a6989586621679089270 a6989586621679089271
type instance Apply @[a_akDS] @([a_akDS],
                                [a_akDS]) (ListsplitAtSym1 a6989586621679089270) a6989586621679089271 = ListsplitAt a6989586621679089270 a6989586621679089271
instance SuppressUnusedWarnings (ListsplitAtSym1 a6989586621679089270) where
  suppressUnusedWarnings = snd ((,) ListsplitAtSym1KindInference ())
type ListsplitAtSym2 :: Natural -> [a_akDS] -> ([a_akDS], [a_akDS])
type family ListsplitAtSym2 @a_akDS (a6989586621679089270 :: Natural) (a6989586621679089271 :: [a_akDS]) :: ([a_akDS],
                                                                                                              [a_akDS]) where
  ListsplitAtSym2 a6989586621679089270 a6989586621679089271 = ListsplitAt a6989586621679089270 a6989586621679089271
type ListdropSym0 :: (~>) Natural ((~>) [a_akDT] [a_akDT])
data ListdropSym0 :: (~>) Natural ((~>) [a_akDT] [a_akDT])
  where
    ListdropSym0KindInference :: SameKind (Apply ListdropSym0 arg_akG4) (ListdropSym1 arg_akG4) =>
                                  ListdropSym0 a6989586621679089281
type instance Apply @Natural @((~>) [a_akDT] [a_akDT]) ListdropSym0 a6989586621679089281 = ListdropSym1 a6989586621679089281
instance SuppressUnusedWarnings ListdropSym0 where
  suppressUnusedWarnings = snd ((,) ListdropSym0KindInference ())
type ListdropSym1 :: Natural -> (~>) [a_akDT] [a_akDT]
data ListdropSym1 (a6989586621679089281 :: Natural) :: (~>) [a_akDT] [a_akDT]
  where
    ListdropSym1KindInference :: SameKind (Apply (ListdropSym1 a6989586621679089281) arg_akG4) (ListdropSym2 a6989586621679089281 arg_akG4) =>
                                  ListdropSym1 a6989586621679089281 a6989586621679089282
type instance Apply @[a_akDT] @[a_akDT] (ListdropSym1 a6989586621679089281) a6989586621679089282 = Listdrop a6989586621679089281 a6989586621679089282
instance SuppressUnusedWarnings (ListdropSym1 a6989586621679089281) where
  suppressUnusedWarnings = snd ((,) ListdropSym1KindInference ())
type ListdropSym2 :: Natural -> [a_akDT] -> [a_akDT]
type family ListdropSym2 @a_akDT (a6989586621679089281 :: Natural) (a6989586621679089282 :: [a_akDT]) :: [a_akDT] where
  ListdropSym2 a6989586621679089281 a6989586621679089282 = Listdrop a6989586621679089281 a6989586621679089282
type ListtakeSym0 :: (~>) Natural ((~>) [a_akDU] [a_akDU])
data ListtakeSym0 :: (~>) Natural ((~>) [a_akDU] [a_akDU])
  where
    ListtakeSym0KindInference :: SameKind (Apply ListtakeSym0 arg_akGf) (ListtakeSym1 arg_akGf) =>
                                  ListtakeSym0 a6989586621679089292
type instance Apply @Natural @((~>) [a_akDU] [a_akDU]) ListtakeSym0 a6989586621679089292 = ListtakeSym1 a6989586621679089292
instance SuppressUnusedWarnings ListtakeSym0 where
  suppressUnusedWarnings = snd ((,) ListtakeSym0KindInference ())
type ListtakeSym1 :: Natural -> (~>) [a_akDU] [a_akDU]
data ListtakeSym1 (a6989586621679089292 :: Natural) :: (~>) [a_akDU] [a_akDU]
  where
    ListtakeSym1KindInference :: SameKind (Apply (ListtakeSym1 a6989586621679089292) arg_akGf) (ListtakeSym2 a6989586621679089292 arg_akGf) =>
                                  ListtakeSym1 a6989586621679089292 a6989586621679089293
type instance Apply @[a_akDU] @[a_akDU] (ListtakeSym1 a6989586621679089292) a6989586621679089293 = Listtake a6989586621679089292 a6989586621679089293
instance SuppressUnusedWarnings (ListtakeSym1 a6989586621679089292) where
  suppressUnusedWarnings = snd ((,) ListtakeSym1KindInference ())
type ListtakeSym2 :: Natural -> [a_akDU] -> [a_akDU]
type family ListtakeSym2 @a_akDU (a6989586621679089292 :: Natural) (a6989586621679089293 :: [a_akDU]) :: [a_akDU] where
  ListtakeSym2 a6989586621679089292 a6989586621679089293 = Listtake a6989586621679089292 a6989586621679089293
type Listlength :: [a_akDQ] -> Natural
type family Listlength @a_akDQ (a_akFy :: [a_akDQ]) :: Natural where
  Listlength a_6989586621679089246_akFB = Apply LengthSym0 a_6989586621679089246_akFB
type Listindex :: [a_akDR] -> Natural -> a_akDR
type family Listindex @a_akDR (a_akFG :: [a_akDR]) (a_akFH :: Natural) :: a_akDR where
  Listindex a_6989586621679089252_akFL a_6989586621679089254_akFM = Apply (Apply (!!@#@$) a_6989586621679089252_akFL) a_6989586621679089254_akFM
type ListsplitAt :: Natural -> [a_akDS] -> ([a_akDS], [a_akDS])
type family ListsplitAt @a_akDS (a_akFR :: Natural) (a_akFS :: [a_akDS]) :: ([a_akDS],
                                                                              [a_akDS]) where
  ListsplitAt a_6989586621679089263_akFW a_6989586621679089265_akFX = Apply (Apply SplitAtSym0 a_6989586621679089263_akFW) a_6989586621679089265_akFX
type Listdrop :: Natural -> [a_akDT] -> [a_akDT]
type family Listdrop @a_akDT (a_akG2 :: Natural) (a_akG3 :: [a_akDT]) :: [a_akDT] where
  Listdrop a_6989586621679089274_akG7 a_6989586621679089276_akG8 = Apply (Apply DropSym0 a_6989586621679089274_akG7) a_6989586621679089276_akG8
type Listtake :: Natural -> [a_akDU] -> [a_akDU]
type family Listtake @a_akDU (a_akGd :: Natural) (a_akGe :: [a_akDU]) :: [a_akDU] where
  Listtake a_6989586621679089285_akGi a_6989586621679089287_akGj = Apply (Apply TakeSym0 a_6989586621679089285_akGi) a_6989586621679089287_akGj
sListlength ::
  (forall (t_akGk :: [a_akDQ]).
    Sing t_akGk -> Sing (Listlength t_akGk :: Natural) :: Type)
sListindex ::
  (forall (t_akGm :: [a_akDR]) (t_akGn :: Natural).
    Sing t_akGm
    -> Sing t_akGn -> Sing (Listindex t_akGm t_akGn :: a_akDR) :: Type)
sListsplitAt ::
  (forall (t_akGr :: Natural) (t_akGs :: [a_akDS]).
    Sing t_akGr
    -> Sing t_akGs
      -> Sing (ListsplitAt t_akGr t_akGs :: ([a_akDS],
                                              [a_akDS])) :: Type)
sListdrop ::
  (forall (t_akGw :: Natural) (t_akGx :: [a_akDT]).
    Sing t_akGw
    -> Sing t_akGx
      -> Sing (Listdrop t_akGw t_akGx :: [a_akDT]) :: Type)
sListtake ::
  (forall (t_akGB :: Natural) (t_akGC :: [a_akDU]).
    Sing t_akGB
    -> Sing t_akGC
      -> Sing (Listtake t_akGB t_akGC :: [a_akDU]) :: Type)
sListlength
  (sA_6989586621679089246 :: Sing a_6989586621679089246_akFB)
  = applySing (singFun1 @LengthSym0 sLength) sA_6989586621679089246
sListindex
  (sA_6989586621679089252 :: Sing a_6989586621679089252_akFL)
  (sA_6989586621679089254 :: Sing a_6989586621679089254_akFM)
  = applySing
      (applySing (singFun2 @(!!@#@$) (%!!)) sA_6989586621679089252)
      sA_6989586621679089254
sListsplitAt
  (sA_6989586621679089263 :: Sing a_6989586621679089263_akFW)
  (sA_6989586621679089265 :: Sing a_6989586621679089265_akFX)
  = applySing
      (applySing (singFun2 @SplitAtSym0 sSplitAt) sA_6989586621679089263)
      sA_6989586621679089265
sListdrop
  (sA_6989586621679089274 :: Sing a_6989586621679089274_akG7)
  (sA_6989586621679089276 :: Sing a_6989586621679089276_akG8)
  = applySing
      (applySing (singFun2 @DropSym0 sDrop) sA_6989586621679089274)
      sA_6989586621679089276
sListtake
  (sA_6989586621679089285 :: Sing a_6989586621679089285_akGi)
  (sA_6989586621679089287 :: Sing a_6989586621679089287_akGj)
  = applySing
      (applySing (singFun2 @TakeSym0 sTake) sA_6989586621679089285)
      sA_6989586621679089287
instance SingI (ListlengthSym0 :: (~>) [a_akDQ] Natural) where
  sing = singFun1 @ListlengthSym0 sListlength
instance SingI (ListindexSym0 :: (~>) [a_akDR] ((~>) Natural a_akDR)) where
  sing = singFun2 @ListindexSym0 sListindex
instance SingI d_akGo =>
          SingI (ListindexSym1 (d_akGo :: [a_akDR]) :: (~>) Natural a_akDR) where
  sing
    = singFun1
        @(ListindexSym1 (d_akGo :: [a_akDR])) (sListindex (sing @d_akGo))
instance SingI1 (ListindexSym1 :: [a_akDR]
                                  -> (~>) Natural a_akDR) where
  liftSing (s_akGq :: Sing (d_akGo :: [a_akDR]))
    = singFun1
        @(ListindexSym1 (d_akGo :: [a_akDR])) (sListindex s_akGq)
instance SingI (ListsplitAtSym0 :: (~>) Natural ((~>) [a_akDS] ([a_akDS],
                                                                [a_akDS]))) where
  sing = singFun2 @ListsplitAtSym0 sListsplitAt
instance SingI d_akGt =>
          SingI (ListsplitAtSym1 (d_akGt :: Natural) :: (~>) [a_akDS] ([a_akDS],
                                                                      [a_akDS])) where
  sing
    = singFun1
        @(ListsplitAtSym1 (d_akGt :: Natural))
        (sListsplitAt (sing @d_akGt))
instance SingI1 (ListsplitAtSym1 :: Natural
                                    -> (~>) [a_akDS] ([a_akDS], [a_akDS])) where
  liftSing (s_akGv :: Sing (d_akGt :: Natural))
    = singFun1
        @(ListsplitAtSym1 (d_akGt :: Natural)) (sListsplitAt s_akGv)
instance SingI (ListdropSym0 :: (~>) Natural ((~>) [a_akDT] [a_akDT])) where
  sing = singFun2 @ListdropSym0 sListdrop
instance SingI d_akGy =>
          SingI (ListdropSym1 (d_akGy :: Natural) :: (~>) [a_akDT] [a_akDT]) where
  sing
    = singFun1
        @(ListdropSym1 (d_akGy :: Natural)) (sListdrop (sing @d_akGy))
instance SingI1 (ListdropSym1 :: Natural
                                  -> (~>) [a_akDT] [a_akDT]) where
  liftSing (s_akGA :: Sing (d_akGy :: Natural))
    = singFun1 @(ListdropSym1 (d_akGy :: Natural)) (sListdrop s_akGA)
instance SingI (ListtakeSym0 :: (~>) Natural ((~>) [a_akDU] [a_akDU])) where
  sing = singFun2 @ListtakeSym0 sListtake
instance SingI d_akGD =>
          SingI (ListtakeSym1 (d_akGD :: Natural) :: (~>) [a_akDU] [a_akDU]) where
  sing
    = singFun1
        @(ListtakeSym1 (d_akGD :: Natural)) (sListtake (sing @d_akGD))
instance SingI1 (ListtakeSym1 :: Natural
                                  -> (~>) [a_akDU] [a_akDU]) where
  liftSing (s_akGF :: Sing (d_akGD :: Natural))
    = singFun1 @(ListtakeSym1 (d_akGD :: Natural)) (sListtake s_akGF)


listtake :: Natural -> [a] -> [a]
listtake = undefined

listdrop :: Natural -> [a] -> [a]
listdrop = undefined

listsplitAt :: Natural -> [a] -> ([a], [a])
listsplitAt = undefined

listindex :: [a] -> Natural -> a
listindex = undefined

listlength :: [a] -> Nat
listlength = undefined
