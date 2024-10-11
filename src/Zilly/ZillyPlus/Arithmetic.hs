{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE TypeAbstractions           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
#ifndef WASM
{-# LANGUAGE TemplateHaskell            #-}
#endif

{-|
Module      : Zilly.Classic.Expression
Description : Defines the contexts of expressions and its rvalue rules for classic zilly.
Copyright   : (c) Daniel Dictinto, 2024
                  Enzo Alda, 2024
License     : GDictL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Dictortability : DictOSIX

-}
module Zilly.ZillyPlus.Arithmetic where

import Data.Proof
import Utilities.LensM
import Utilities.TypedMapPlus
import Zilly.Types
import Zilly.ADT.ExpressionPlus
import Zilly.ADT.Arithmetic
import Zilly.RValuePlus
import Zilly.UpcastPlus
import Zilly.ZillyPlus.Interpreter
import Zilly.ZillyPlus.Expression
import InequalityFamily 
import Data.Foldable
import Control.Monad 

import Control.Applicative

import Utilities.ShowM
import Prelude hiding (LT,GT,EQ)
import Prelude.Singletons (SingI(..),Sing,SMaybe(..),withSingI, type (<$>), ApplySym1)
import Data.Maybe.Singletons (IsJust)
import Data.Sequence 
import Data.Kind (Type)

#ifndef WASM 
import Data.Singletons.TH


#endif

--------------------------
-- Util functions 
--------------------------


------------------------
-- Types and instances- 
------------------------


data ArithmeticTag

class
  ( ArithBaseType a
  , ArithBaseType b
  ) =>
  BinOp (tag :: Type)  (a :: Types) (b :: Types) where 
    type BinOpReturn (tag :: Type) (a :: Types) (b :: Types) :: Types

    (***) :: (ArithBaseType (BinOpReturn tag a b))
      => ArithNumType a 
      -> ArithNumType b
      -> (AssocCtxMonad ArithmeticTag) (ArithNumType (BinOpReturn tag a b))

class ArithBaseType a => Biject (f :: Types -> Type) (a :: Types) where 

    project :: f a -> (AssocCtxMonad ArithmeticTag) (ArithNumType a)
    inject  :: ArithNumType a -> (AssocCtxMonad ArithmeticTag) (f a)

class ArithBaseType (a :: Types) where 
  type ArithNumType (a :: Types) :: Type

data PlusTag

type instance AssocCtxMonad ArithmeticTag = TaggedInterpreter ExprTag


type family PlusX' (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type

type instance PlusX sup sub ArithmeticTag a b c =
  ( Dict (SingI a)
  , Dict (SingI b)
  , Dict (SingI c)
  , Dict (ArithBaseType (RValueT a))
  , Dict (ArithBaseType (RValueT b))
  , Dict (BinOp PlusTag (RValueT a) (RValueT b))
  , Dict (Biject sup (RValueT a))
  , Dict (Biject sup (RValueT b))
  , Dict (Biject sub  (RValueT a))
  , Dict (Biject sub (RValueT b))
  , Dict (ArithBaseType (RValueT c))
  , Dict (Biject sub (RValueT c))
  , Dict (Biject sup (RValueT c))
  , Dict (BinOpReturn PlusTag (RValueT a) (RValueT b) ~ RValueT c )
  , Dict (TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag)))
  , Dict (SingI a)
  , Dict (SingI b)
  , Dict (SingI c)
  )

type instance ArithExpX sup sub ArithmeticTag a = 
  ( sub a 
  , Dict (SingI a)
  , Dict (TypesCaseAnalysis (RValue sup))
  , Dict (TypesCaseAnalysis (RValue sub))
  )
pattern ArithExpE :: forall sup sub a . 
  ( SingI a 
  , TypesCaseAnalysis (RValue sup)
  , TypesCaseAnalysis (RValue sub)
  ) => sub a
    -> Arithmetic sup sub ArithmeticTag a
pattern ArithExpE a <- ArithExp (a,Dict,Dict,Dict)
  where ArithExpE a  = ArithExp (a,Dict,Dict,Dict)


type instance ArithInhX sup sub ArithmeticTag a = 
  ( sup a 
  , Dict (SingI a)
  , Dict (TypesCaseAnalysis (RValue sup))
  , Dict (TypesCaseAnalysis (RValue sub))

  )
pattern ArithInhE :: forall sup sub a . 
  ( SingI a 
  , TypesCaseAnalysis (RValue sup)
  , TypesCaseAnalysis (RValue sub)
  ) => sup a 
    -> Arithmetic sup sub ArithmeticTag a
pattern ArithInhE a <- ArithInh (a,Dict,Dict,Dict)
  where ArithInhE a  = ArithInh (a,Dict,Dict,Dict)


type instance ArithUpcastedX sup sub ArithmeticTag a b =
  ( Dict (UpperBound a b ~ Just b)
  , Dict (SingI a)
  , Dict (SingI b)
  , Dict (TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag)))
  , Dict (Upcast sup)
  , Dict (Upcast sub)
  , UpcastX sup (RValueT a)
  , UpcastX sub (RValueT a)
  )

instance 
  ( AssocCtxMonad (RVCtx sup) ~ AssocCtxMonad ArithmeticTag
  , AssocCtxMonad (RVCtx sub) ~ AssocCtxMonad ArithmeticTag
  ) => RValue (Arithmetic sup sub ArithmeticTag) (Value r) where 

  type RVCtx (Arithmetic sup sub ArithmeticTag) = ArithmeticTag  
  rvalue (Plus @_ @_ @_ @a @b @c 
    ( Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    ) a b) = case (tcarv @a, tcarv @b, tcarv @c ) of
      (Dict,Dict,Dict) -> (,) <$> rvalue a <*> rvalue b >>= \case 
        (ArithExp @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithExp @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do
          ea <- project @sub @a' a'
          eb <- project @sub @b' b'
          ec <- (***) @PlusTag @a' @b' ea  eb 
          c' <-  inject @sub @(RValueT c) ec
          withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict) 
        (ArithExp @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithInh @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do  
          ea <- project @sub @a' a'
          eb <- project @sup @b' b'
          ec <- (***) @PlusTag @a' @b' ea  eb 
          c' <-  inject @sub @(RValueT c) ec
          withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict) 
        (ArithInh @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithExp @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do  
          ea <- project a'
          eb <- project b'
          ec <- (***) @PlusTag @a' @b' ea  eb 
          c' <-  inject  ec
          withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict) 
        (ArithInh @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithInh @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do  
          ea <- project a'
          eb <- project b'
          ec <- (***) @PlusTag @a' @b' ea  eb 
          c' <-  inject  ec
          withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict)
        _ -> error "impossible case"
    where  
      tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
      tcarv = typesCaseAnalysisRV

  rvalue (ArithUpcasted @_ @_ @_ @a @b (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a) 
    = rvaluePreservesST @a @b
    $ withSingIRType @a
    $ withSingIRType @b
    $ case (tcarv @a, tcarv @b) of
      (Dict,Dict) -> rvalue a >>= \case 
        (ArithExp (ae,Dict,Dict,Dict)) -> case upcast @sub @(RValueT a) @(RValueT b) sub ae of 
          SameTypeUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
        (ArithInh (ae,Dict,Dict,Dict)) -> case upcast @sup @(RValueT a) @(RValueT b) sup ae of 
          SameTypeUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
        _ -> error "imposible case"
    where  
      tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
      tcarv = typesCaseAnalysisRV

  rvalue (ArithExp @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithExpE <$> rvalue a 
  rvalue (ArithInh @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithInhE <$> rvalue a 

  rvalue _ = error "impossible case"



instance 
  ( AssocCtxMonad (RVCtx sup) ~ AssocCtxMonad ArithmeticTag
  , AssocCtxMonad (RVCtx sub) ~ AssocCtxMonad ArithmeticTag
  ) => RValue (Arithmetic sup sub ArithmeticTag) (LazyS r) where 

  type RVCtx (Arithmetic sup sub ArithmeticTag) = ArithmeticTag  
  rvalue (ArithExp @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithExpE <$> rvalue a 
  rvalue (ArithInh @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithInhE <$> rvalue a 


  rvalue (ArithUpcasted @_ @_ @_ @a @b (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a) 
    = rvaluePreservesST @a @b
    $ withSingIRType @a
    $ withSingIRType @b
    $ case (tcarv @a, tcarv @b) of
      (Dict,Dict) -> rvalue a >>= \case 
        (ArithExp (ae,Dict,Dict,Dict)) -> case upcast @sub @(RValueT a) @(RValueT b) sub ae of 
          SameTypeUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
        (ArithInh (ae,Dict,Dict,Dict)) -> case upcast @sup @(RValueT a) @(RValueT b) sup ae of 
          SameTypeUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
        _ -> error "imposible case"
    where  
      tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
      tcarv = typesCaseAnalysisRV

  rvalue _ = error "impossible case"


instance 
  ( AssocCtxMonad (RVCtx sup) ~ AssocCtxMonad ArithmeticTag
  , AssocCtxMonad (RVCtx sub) ~ AssocCtxMonad ArithmeticTag
  ) => RValue (Arithmetic sup sub ArithmeticTag) (Lazy r) where 
  
  type RVCtx (Arithmetic sup sub ArithmeticTag) = ArithmeticTag  

  rvalue (ArithExp @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithExpE <$> rvalue a 
  rvalue (ArithInh @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithInhE <$> rvalue a 


  rvalue (ArithUpcasted @_ @_ @_ @a @b (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a) 
    = rvaluePreservesST @a @b
    $ withSingIRType @a
    $ withSingIRType @b
    $ case (tcarv @a, tcarv @b) of
      (Dict,Dict) -> rvalue a >>= \case 
        (ArithExp (ae,Dict,Dict,Dict)) -> case upcast @sub @(RValueT a) @(RValueT b) sub ae of 
          SameTypeUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
        (ArithInh (ae,Dict,Dict,Dict)) -> case upcast @sup @(RValueT a) @(RValueT b) sup ae of 
          SameTypeUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
        _ -> error "imposible case"
    where  
      tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
      tcarv = typesCaseAnalysisRV

  rvalue _ = error "impossible case"

instance 
  ( AssocCtxMonad (RVCtx sup) ~ AssocCtxMonad ArithmeticTag
  , AssocCtxMonad (RVCtx sub) ~ AssocCtxMonad ArithmeticTag
  ) => RValue (Arithmetic sup sub ArithmeticTag) (Array r) where 
  
  type RVCtx (Arithmetic sup sub ArithmeticTag) = ArithmeticTag  

  rvalue (Plus @_ @_ @_ @a @b @c 
    ( Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict 
    ) a b) = case (tcarv @a, tcarv @b, tcarv @c ) of
    (Dict,Dict,Dict) -> (,) <$> rvalue a <*> rvalue b >>= \case 
        (ArithExp @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithExp @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do
          ea <- project @sub @a' a'
          eb <- project @sub @b' b'
          ec <- (***) @PlusTag @a' @b' ea  eb 
          c' <-  inject @sub @(RValueT c) ec
          withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict) 
        (ArithExp @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithInh @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do  
          ea <- project @sub @a' a'
          eb <- project @sup @b' b'
          ec <- (***)  @PlusTag @a' @b' ea  eb 
          c' <-  inject @sub @(RValueT c) ec
          withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict) 
        (ArithInh @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithExp @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do  
          ea <- project a'
          eb <- project b'
          ec <- (***) @PlusTag @a' @b' ea  eb 
          c' <-  inject  ec
          withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict) 
        (ArithInh @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithInh @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do  
          ea <- project a'
          eb <- project b'
          ec <- (***) @PlusTag @a' @b' ea  eb 
          c' <-  inject  ec
          withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict)
        _ -> error "impossible case"
    where  
      tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
      tcarv = typesCaseAnalysisRV

  rvalue (ArithExp @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithExpE <$> rvalue a 
  rvalue (ArithInh @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithInhE <$> rvalue a 
  rvalue _ = error "impossible case"




data Exists f where
  MkExists ::  (forall x. Sing x -> UpcastX f x)  -> Exists f

type instance UpcastX (Arithmetic sup sub ArithmeticTag) a  =
  ( UpcastX sup (RValueT a) 
  , UpcastX sub (RValueT a)
  , UpcastX sup a 
  , UpcastX sub a
  , Dict (Upcast sup)
  , Dict (Upcast sub)
  , Dict (SingI a)
  , Dict (TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag)))
  , Dict (TypesCaseAnalysis (RValue sup))
  , Dict (TypesCaseAnalysis (RValue sub))
  , Dict (ArithBaseType (RValueT a))
  , Dict (Biject sub (Array (RValueT a)))
  , Dict (Biject sup (Array (RValueT a)))

    )



instance Upcast (Arithmetic sup sub ArithmeticTag) where
  upcast :: forall (a :: Types) (b :: Types)  
    . SingI b 
    => UpcastX (Arithmetic sup sub ArithmeticTag) a  
    ->  Arithmetic sup sub ArithmeticTag a  
    -> UpperBoundResults (Arithmetic sup sub ArithmeticTag) a b
  upcast 
    (supX,subX,_,_, Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict)
    (Plus ds l r) = case upcastable @a @b @Arithmetic @sup @sub @ArithmeticTag of
            NonExistentUB -> NonExistentUB
            SameTypeUB _  -> SameTypeUB $ Plus ds l r
            LeftUB _      -> LeftUB  $ Plus ds l r
            RightUB _     -> RightUB 
              $ ArithUpcasted (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) (Plus ds l r)
            SomethingElseUB _     -> case sing @(UpperBound a b) of
              SJust @_ @r _ -> ubIsUb @a @b $ SomethingElseUB 
                $ ArithUpcasted 
                  @sup 
                  @sub 
                  @ArithmeticTag 
                  @a 
                  @r 
                  (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) 
                  (Plus ds l r)


  upcast 
    (_,_,supX,subX, Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict)
    (ArithExp (a,Dict,Dict,Dict)) = case upcast @_ @a @b subX a of
      NonExistentUB      -> NonExistentUB
      SameTypeUB a'      -> SameTypeUB $ ArithExp (a',Dict,Dict,Dict)
      LeftUB a'          -> LeftUB  $ ArithExp (a',Dict,Dict,Dict)
      RightUB a'         -> RightUB $ ArithExp (a',Dict,Dict,Dict)
      SomethingElseUB a' -> SomethingElseUB $ ArithExp (a',Dict,Dict,Dict)
  upcast 
    (_,_,supX,subX, Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict)
    (ArithInh (a,Dict,Dict,Dict)) = case upcast @_ @a @b supX a of
      NonExistentUB      -> NonExistentUB
      SameTypeUB a'      -> SameTypeUB $ ArithInh (a',Dict,Dict,Dict)
      LeftUB a'          -> LeftUB  $ ArithInh (a',Dict,Dict,Dict)
      RightUB a'         -> RightUB $ ArithInh (a',Dict,Dict,Dict)
      SomethingElseUB a' -> SomethingElseUB $ ArithInh (a',Dict,Dict,Dict)

  upcast _ _ = undefined
--
--

instance 
  ( Monad m
  , C (ShowM m) sup
  , C (ShowM m) sub
  ) => ShowM m (Arithmetic sup sub ArithmeticTag a) where 
  showsPrecM p = \case 
    Plus _ l r -> showParenM (p > 6) $ showsPrecM 6 l <=< showStringM " + " <=< showsPrecM 7 r
    ArithExp (a,_,_,_) -> showsPrecM p a 
    ArithInh (a,_,_,_) -> showsPrecM p a
    ArithUpcasted _ a -> showsPrecM p a


