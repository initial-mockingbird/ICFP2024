{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FunctionalDependencies #-}

{-|
Module      : Zilly.RValue
Description : Definition of RValue and evidence injection for Zilly.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Defines the RValue class, provides a way to inject them RValue types into a continuation..
-}
module Zilly.RValue where 

import Zilly.Types
import Data.Singletons.TH  hiding (Const)

import Data.Singletons.Decide
import Data.Kind (Type)

{- |
Class that yields the rvalue of a given type. 
-}
class RValue (f :: Types -> Type) (a :: Types) m where
  type RValueT f a :: Types
  rvalue :: f a -> m (f (RValueT f a))

{- -- same issue, illegal type family declaration....
type RTypeAxioms f =
  ( forall (a :: Types0) (b :: Types). RValueT f (Value a) ~ RValueT f (Value a)
  , forall (a :: Types). RValue f a
  ) -}

-- | Whenever we know a type, we know its rvalue-dict
withRVType :: forall (f :: Types -> Type) (m :: Type -> Type) (z :: Types)  r.
  ( forall (a :: Types). RValue f (Lazy (Lazy a)) m
  , forall (a :: Types0). RValue f (Lazy (Value a)) m
  , forall (a :: Types0). RValue f (Value a) m
  ) => Sing z -> (RValue f z m => r) -> r
withRVType (SValue v) f = case v of
  (SZ :: Sing (x :: Types0)) -> f
  (z1 :%-> z2) -> withRVType @f @m z1 $ withRVType @f @m z2 f
withRVType (SLazy  (SLazy s)) f = withRVType @f @m s f
withRVType (SLazy (SValue s)) f = withSingI s $ withRVType @f @m (SValue s) f
withRVType _ _ = error "Lazy* not supported"

-- | Whenever we know a type, we know its rtype
withSingIRType :: forall (z :: Types) f cont. SingI z => (SingI  (RValueT f z) => cont) -> cont
withSingIRType f 
  = withSingIRType @z @f 
  $ case sing @z of
  (SValue @n _) -> case decideEquality' @_ @(Value n) @(RValueT f z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT f z) @n of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT f z) @n of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented"

-- | Whenever we know two types, whe know their meet.
rvaluePreservesST :: forall {r0 :: Types} a b f cont. 
  ( SingI a
  , SingI b
  , SingI r0
  , UpperBound a b ~ Just r0
  ) 
  => (UpperBound (RValueT f a) (RValueT f b) ~ Just (RValueT f r0) => cont) -> cont
rvaluePreservesST f
  = withSingIRType @a @f 
  $ withSingIRType @b @f 
  $ withSingIRType @r0 @f
  $ withSingIUBType @(RValueT f a) @(RValueT f b)
  $ case decideEquality' @_ @(UpperBound (RValueT f a) (RValueT f b)) @(Just (RValueT f r0))of
    Just Refl -> f
    Nothing -> error "impossible case"

{-| Whenever we know a type \(a\), we know that:

  \[a \vee rtype(a) = a\]

-}
rvalueIsPred :: forall (a :: Types) f cont.
  ( SingI a
  )
  => (UpperBound (RValueT f a) a ~ Just a => cont) -> cont
rvalueIsPred !f 
  = withSingIRType @a @f
  $ withSingIUBType @(RValueT f a) @a 
  $ case  decideEquality (sing @(UpperBound (RValueT f a) a )) (sing @(Just a)) of
  Just Refl -> f
  Nothing -> error "impossible case"

-- | An easy way of constructing the subtyped context.
subtyped'CTX :: forall {r :: Types} (a :: Types) (b :: Types) (f :: Types -> Type) (m :: Type -> Type) cont.
  ( SingI a
  , SingI b
  , SingI r
  , UpperBound a b ~ 'Just r
  , forall (a :: Types). RValue f (Lazy (Lazy a)) m
  , forall (a :: Types0). RValue f (Lazy (Value a)) m
  , forall (a :: Types0). RValue f (Value a) m
  ) => ((UpperBound (RValueT f a) r ~ 'Just r, RValue f a m, RValue f b m) => cont) -> cont
subtyped'CTX f 
  = withSingIRType @a @f 
  $ withSingIRType @b @f
  $ withRVType @f @m (sing @a)  
  $ withRVType @f @m (sing @b) 
  $ rvalueIsPred @a @f
  $ ubIsUb @a @b
  $ ubIsTransitive' @(RValueT f a) @a @r
  $ f

{- 
upcastable :: forall (a :: Types) (b :: Types). 
  ( SingI a
  , SingI b
  ) => UpperBoundResults (Const ()) a b
upcastable 
  = withSingIUBType @a @b 
  $ case decideEquality (sing @a) (sing @b) of
    Just Refl -> ubIsIdempotent @a $ SameTypeUBN
    Nothing -> case sing @(UpperBound a b) of
      SJust sub -> case decideEquality (sing @a) sub of
        Just Refl -> LeftUBN
        Nothing   -> case decideEquality (sing @b) sub of
          Just Refl -> RightUBN
          Nothing   
            -> withRVType (sing @a)
            $  rvalueIsPred @a
            $  withSingI sub 
            $  SomethingElseUBN @a @b
      SNothing  -> NonExistentUB

data UpperBoundResults (f :: Types -> Type) (a :: Types) (b :: Types)where
  NonExistentUB   :: (UpperBound a b ~ Nothing) => UpperBoundResults f a b 
  SameTypeUB      :: (a ~ b, UpperBound a b ~ Just a) => f a -> UpperBoundResults f a b 
  LeftUB          :: (UpperBound a b ~ Just a)  => f a -> UpperBoundResults f a b 
  RightUB         :: (UpperBound a b ~ Just b)  => f b -> UpperBoundResults f a b 
  SomethingElseUB :: forall {r :: Types} f (a :: Types) (b :: Types) . 
    ( UpperBound a b ~ Just r
    , SingI r
    ) => f r -> UpperBoundResults f a b 

pattern SameTypeUBN ::  (a ~ b, UpperBound a b ~ Just a) => UpperBoundResults (Const ()) a b 
pattern SameTypeUBN = SameTypeUB (Const ())
  

pattern LeftUBN ::  (UpperBound a b ~ Just a) => UpperBoundResults (Const ()) a b 
pattern LeftUBN = LeftUB (Const ())

pattern RightUBN ::  (UpperBound a b ~ Just b) => UpperBoundResults (Const ()) a b 
pattern RightUBN = RightUB (Const ())

pattern SomethingElseUBN :: 
  ( UpperBound a b ~ Just r
  , SingI r
  ) => UpperBoundResults (Const ()) a b 
pattern SomethingElseUBN = SomethingElseUB (Const ())


lazyRT :: forall a f cont. 
  (SingI a
  , forall (b :: Types). RValue f b
  ) 
  => (RValueT f (Lazy a) ~ a => cont) -> cont
lazyRT f = case sing @a of
  sl@(SLazy @n _)  -> f
  sv@(SValue @n _) -> f
  sls@(SLazyS _) -> error "Lazy* not implemented"

 -}