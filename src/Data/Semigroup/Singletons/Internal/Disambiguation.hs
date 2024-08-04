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
-- Module      :  Data.Semigroup.Singletons.Internal.Disambiguation
-- Copyright   :  (C) 2019 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Provides aliases for 'All', 'Any', 'Sum', and 'Product' that do not clash
-- with the promoted functions of the same names in
-- Data.Foldable.Singletons.
--
----------------------------------------------------------------------------

module Data.Semigroup.Singletons.Internal.Disambiguation where

import Data.Semigroup
import Data.Semigroup.Singletons.Internal.Wrappers
import Data.Singletons.TH
import Data.Kind (Type)

-- We need these in Data.Foldable.Singletons, as we need to promote
-- code that simultaneously uses the All/Any/Sum/Product constructors and the
-- all/any/sum/product functions, which have clashing defunctionalization
-- symbol names. Our workaround is to simply define synonyms for
-- all/any/sum/product and use those instead.
all_ :: Bool -> All
all_ = All
any_ :: Bool -> Any
any_ = Any
sum_ :: a_a2ehW -> Sum a_a2ehW
sum_ = Sum
product_ :: a_a2ehV -> Product a_a2ehV
product_ = Product
type Product_Sym0 :: (~>) a_a2ehV (Product a_a2ehV)
data Product_Sym0 :: (~>) a_a2ehV (Product a_a2ehV)
  where
    Product_Sym0KindInference :: SameKind (Apply Product_Sym0 arg_a2eia) (Product_Sym1 arg_a2eia) =>
                                  Product_Sym0 a6989586621679541391
type instance Apply @a_a2ehV @(Product a_a2ehV) Product_Sym0 a6989586621679541391 = Product_ a6989586621679541391
instance SuppressUnusedWarnings Product_Sym0 where
  suppressUnusedWarnings = snd ((,) Product_Sym0KindInference ())
type Product_Sym1 :: a_a2ehV -> Product a_a2ehV
type family Product_Sym1 @a_a2ehV (a6989586621679541391 :: a_a2ehV) :: Product a_a2ehV where
  Product_Sym1 a6989586621679541391 = Product_ a6989586621679541391
type Sum_Sym0 :: (~>) a_a2ehW (Sum a_a2ehW)
data Sum_Sym0 :: (~>) a_a2ehW (Sum a_a2ehW)
  where
    Sum_Sym0KindInference :: SameKind (Apply Sum_Sym0 arg_a2eig) (Sum_Sym1 arg_a2eig) =>
                              Sum_Sym0 a6989586621679541397
type instance Apply @a_a2ehW @(Sum a_a2ehW) Sum_Sym0 a6989586621679541397 = Sum_ a6989586621679541397
instance SuppressUnusedWarnings Sum_Sym0 where
  suppressUnusedWarnings = snd ((,) Sum_Sym0KindInference ())
type Sum_Sym1 :: a_a2ehW -> Sum a_a2ehW
type family Sum_Sym1 @a_a2ehW (a6989586621679541397 :: a_a2ehW) :: Sum a_a2ehW where
  Sum_Sym1 a6989586621679541397 = Sum_ a6989586621679541397
type Any_Sym0 :: (~>) Bool Any
data Any_Sym0 :: (~>) Bool Any
  where
    Any_Sym0KindInference :: SameKind (Apply Any_Sym0 arg_a2eim) (Any_Sym1 arg_a2eim) =>
                              Any_Sym0 a6989586621679541403
type instance Apply @Bool @Any Any_Sym0 a6989586621679541403 = Any_ a6989586621679541403
instance SuppressUnusedWarnings Any_Sym0 where
  suppressUnusedWarnings = snd ((,) Any_Sym0KindInference ())
type Any_Sym1 :: Bool -> Any
type family Any_Sym1 (a6989586621679541403 :: Bool) :: Any where
  Any_Sym1 a6989586621679541403 = Any_ a6989586621679541403
type All_Sym0 :: (~>) Bool All
data All_Sym0 :: (~>) Bool All
  where
    All_Sym0KindInference :: SameKind (Apply All_Sym0 arg_a2eis) (All_Sym1 arg_a2eis) =>
                              All_Sym0 a6989586621679541409
type instance Apply @Bool @All All_Sym0 a6989586621679541409 = All_ a6989586621679541409
instance SuppressUnusedWarnings All_Sym0 where
  suppressUnusedWarnings = snd ((,) All_Sym0KindInference ())
type All_Sym1 :: Bool -> All
type family All_Sym1 (a6989586621679541409 :: Bool) :: All where
  All_Sym1 a6989586621679541409 = All_ a6989586621679541409
type Product_ :: a_a2ehV -> Product a_a2ehV
type family Product_ @a_a2ehV (a_a2ei9 :: a_a2ehV) :: Product a_a2ehV where
  Product_ a_6989586621679541387_a2eic = Apply ProductSym0 a_6989586621679541387_a2eic
type Sum_ :: a_a2ehW -> Sum a_a2ehW
type family Sum_ @a_a2ehW (a_a2eif :: a_a2ehW) :: Sum a_a2ehW where
  Sum_ a_6989586621679541393_a2eii = Apply SumSym0 a_6989586621679541393_a2eii
type Any_ :: Bool -> Any
type family Any_ (a_a2eil :: Bool) :: Any where
  Any_ a_6989586621679541399_a2eio = Apply AnySym0 a_6989586621679541399_a2eio
type All_ :: Bool -> All
type family All_ (a_a2eir :: Bool) :: All where
  All_ a_6989586621679541405_a2eiu = Apply AllSym0 a_6989586621679541405_a2eiu
sProduct_ ::
  (forall (t_a2eiv :: a_a2ehV).
    Sing t_a2eiv -> Sing (Product_ t_a2eiv :: Product a_a2ehV) :: Type)
sSum_ ::
  (forall (t_a2eix :: a_a2ehW).
    Sing t_a2eix -> Sing (Sum_ t_a2eix :: Sum a_a2ehW) :: Type)
sAny_ ::
  (forall (t_a2eiz :: Bool).
    Sing t_a2eiz -> Sing (Any_ t_a2eiz :: Any) :: Type)
sAll_ ::
  (forall (t_a2eiB :: Bool).
    Sing t_a2eiB -> Sing (All_ t_a2eiB :: All) :: Type)
sProduct_
  (sA_6989586621679541387 :: Sing a_6989586621679541387_a2eic)
  = applySing (singFun1 @ProductSym0 SProduct) sA_6989586621679541387
sSum_ (sA_6989586621679541393 :: Sing a_6989586621679541393_a2eii)
  = applySing (singFun1 @SumSym0 SSum) sA_6989586621679541393
sAny_ (sA_6989586621679541399 :: Sing a_6989586621679541399_a2eio)
  = applySing (singFun1 @AnySym0 SAny) sA_6989586621679541399
sAll_ (sA_6989586621679541405 :: Sing a_6989586621679541405_a2eiu)
  = applySing (singFun1 @AllSym0 SAll) sA_6989586621679541405
instance SingI (Product_Sym0 :: (~>) a_a2ehV (Product a_a2ehV)) where
  sing = singFun1 @Product_Sym0 sProduct_
instance SingI (Sum_Sym0 :: (~>) a_a2ehW (Sum a_a2ehW)) where
  sing = singFun1 @Sum_Sym0 sSum_
instance SingI (Any_Sym0 :: (~>) Bool Any) where
  sing = singFun1 @Any_Sym0 sAny_
instance SingI (All_Sym0 :: (~>) Bool All) where
  sing = singFun1 @All_Sym0 sAll_

