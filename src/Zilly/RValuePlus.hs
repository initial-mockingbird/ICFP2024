
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE UndecidableSuperClasses  #-}
#ifndef WASM
{-# LANGUAGE TemplateHaskell          #-}
#endif

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
module Zilly.RValuePlus where 

import Zilly.Types
import Zilly.ADT.ExpressionPlus

import Data.Proof

import Data.Singletons
import Data.Singletons.Decide
import Data.Kind (Type,Constraint)


#ifndef WASM
import Data.Singletons.TH  hiding (Const)
$(singletons [d| 
  rValueT :: Types -> Types
  rValueT (Value a) = Value a
  rValueT (Array a) = Array (rValueT a)
  rValueT (Lazy a)  = a
  rValueT (LazyS a) = LazyS a
  |])
#else
import qualified Data.Type.Coercion
import Data.Singletons
import Data.Singletons.TH
import Data.Kind (Type)
import qualified Data.Type.Equality
rValueT :: Types -> Types
rValueT (Value a_aui4) = Value a_aui4
rValueT (Lazy a_aui5)  = a_aui5
rValueT (LazyS a_aui6) = a_aui6
type RValueTSym0 :: (Data.Singletons.~>) Types Types
data RValueTSym0 :: (Data.Singletons.~>) Types Types
  where
    RValueTSym0KindInference :: SameKind (Apply RValueTSym0 arg_aui8) (RValueTSym1 arg_aui8) =>
                                RValueTSym0 a6989586621679126237
type instance Apply RValueTSym0 a6989586621679126237 = RValueT a6989586621679126237
instance SuppressUnusedWarnings RValueTSym0 where
  suppressUnusedWarnings = snd ((,) RValueTSym0KindInference ())
type RValueTSym1 :: Types -> Types
type family RValueTSym1 (a6989586621679126237 :: Types) :: Types where
  RValueTSym1 a6989586621679126237 = RValueT a6989586621679126237
type RValueT :: Types -> Types
type family RValueT (a_aui7 :: Types) :: Types where
  RValueT ('Value a_auia) = Apply ValueSym0 a_auia
  RValueT ('Lazy a_auib) = a_auib
  RValueT ('LazyS a_auic) = a_auic
sRValueT ::
  (forall (t_auid :: Types).
    Sing t_auid -> Sing (Apply RValueTSym0 t_auid :: Types) :: Type)
sRValueT (SValue (sA :: Sing a_auia))
  = applySing (singFun1 @ValueSym0 SValue) sA
sRValueT (SLazy (sA :: Sing a_auib)) = sA
sRValueT (SLazyS (sA :: Sing a_auic)) = sA
instance SingI (RValueTSym0 :: (Data.Singletons.~>) Types Types) where
  sing = singFun1 @RValueTSym0 sRValueT
#endif



{- |
Class that yields the rvalue of a given type. 
-}
class RValue (f :: Types -> Type)  (a :: Types)  where
  type RVCtx f :: Type 
  rvalue :: f a -> (AssocCtxMonad (RVCtx f)) (f (RValueT a))

{- -- same issue, illegal type family declaration....
type RTypeAxioms f =
  ( forall (a :: Types0) (b :: Types). RValueT f (Value a) ~ RValueT f (Value a)
  , forall (a :: Types). RValue f a
  ) -}

-- | Whenever we know a type, we know its rvalue-dict
withRVType :: forall (f :: Types -> Type) (z :: Types)  r.
  ( TypesCaseAnalysis (RValue f)
  ) => Sing z -> (RValue f z  => r) -> r
withRVType (SValue v) f = case v of
  (SZ :: Sing (x :: Types0)) -> f
  SF -> f
  (z1 :%-> z2) -> withRVType @f   z1 $ withRVType @f z2 f
withRVType (SLazy  (SLazy s)) f = withRVType @f  s f
withRVType (SLazy (SValue s)) f = withSingI s $ withRVType @f  (SValue s) f
withRVType (SLazy  (SLazyS s)) f = withRVType @f  s f
withRVType (SLazy (SArray s)) f = withRVType @f  s f

withRVType _ _ = error "Lazy* not supported"




-- | Whenever we know a type, we know its rtype
withSingIRType :: forall (z :: Types) cont. SingI z => (SingI  (RValueT z) => cont) -> cont
withSingIRType f 
  = case sing @z of
  (SValue @n _) -> case decideEquality' @_ @(Value n) @(RValueT z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT z) @n of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT z) @n of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented"

-- | Whenever we know two types, whe know their meet.
rvaluePreservesST :: forall {r0 :: Types} a b cont. 
  ( SingI a
  , SingI b
  , SingI r0
  , UpperBound a b ~ Just r0
  ) 
  => (UpperBound (RValueT a) (RValueT b) ~ Just (RValueT r0) => cont) -> cont
rvaluePreservesST f
  = withSingIRType @a 
  $ withSingIRType @b 
  $ withSingIRType @r0
  $ withSingIUBType @(RValueT a) @(RValueT b)
  $ case decideEquality' @_ @(UpperBound (RValueT a) (RValueT b)) @(Just (RValueT r0))of
    Just Refl -> f
    Nothing -> error "impossible case"

{-| Whenever we know a type \(a\), we know that:

  \[a \vee rtype(a) = a\]

-}
rvalueIsPred :: forall (a :: Types) cont.
  ( SingI a
  )
  => (UpperBound (RValueT a) a ~ Just a => cont) -> cont
rvalueIsPred !f 
  = withSingIRType @a
  $ withSingIUBType @(RValueT a) @a 
  $ case  decideEquality (sing @(UpperBound (RValueT a) a )) (sing @(Just a)) of
  Just Refl -> f
  Nothing -> error "impossible case"
{- rvalueIsPred !f 
  = case sing @a of
    (SValue @n SZ) -> case sing @(RValueT (Value n)) of 
      SValue @m SZ -> f
    (SValue @n (a :%-> b)) -> case sing @(RValueT (Value n)) of 
      SValue @m (a' :%-> b') -> f
      
    (SLazy @n sa@(SLazy _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT a) @n of
      Just Refl -> undefined
      Nothing -> error "Type mismatch"
    (SLazy @n sa@(SValue _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT a) @n of
      Just Refl -> undefined
      Nothing -> error "Type mismatch"
    (SLazyS @n sa)   -> error "Lazy* not implemented"
    SLazy (SLazyS _) -> error "Lazy* not implemented" -}

-- | An easy way of constructing the subtyped context.
subtyped'CTX :: forall {r :: Types} (f :: Types -> Type) (a :: Types) (b :: Types) cont.
  ( SingI a
  , SingI b
  , SingI r
  , UpperBound a b ~ 'Just r
  , TypesCaseAnalysis (RValue f)
  ) => ((UpperBound (RValueT a) r ~ 'Just r, RValue f a, RValue f b) => cont) -> cont
subtyped'CTX f 
  = withSingIRType @a  
  $ withSingIRType @b 
  $ withRVType @f  (sing @a)  
  $ withRVType @f  (sing @b) 
  $ rvalueIsPred @a
  $ ubIsUb @a @b
  $ ubIsTransitive' @(RValueT a) @a @r
  $ f


rvalueValue :: forall {r :: Types0} (x :: Types) cont. 
  ( SingI x
  , x ~ Value r
  ) => (RValueT x ~ x => cont) -> cont 
rvalueValue f = case sing @x of 
  SValue SF -> f
  SValue SZ -> f 
  SValue (_ :%-> _) -> f 

typesCaseAnalysisRV :: forall (f :: Types -> Type) (x :: Types).
  ( TypesCaseAnalysis (RValue f)
  , SingI x 
  ) => Dict (RValue f x)
typesCaseAnalysisRV = typesCaseAnalysis @(RValue f) @x


