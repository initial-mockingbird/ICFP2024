

{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
--{-# LANGUAGE TypeAbstractions #-}

{-|
Module      : Zilly Expression
Description : Defines the contexts of expressions and its rvalue rules.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Zilly.Expressions where

import Utilities.LensM
import Utilities.ShowM
import Zilly.Types
import Zilly.ADT
import Zilly.Contexts
import Zilly.RValue
import Control.Monad.IO.Class
import Data.Kind (Type)
import Data.Typeable hiding (cast)
import Control.Monad.Reader 
import Control.Monad
import Unsafe.Coerce (unsafeCoerce)

import Control.Applicative
import Data.Singletons.TH (genSingletons, promote, singletons, promoteEqInstances, singEqInstances, singDecideInstances)
import Prelude.Singletons (fromSing, withSomeSing, Sing, SingI(sing), singByProxy, withSing, demote, SomeSing (SomeSing), withSingI)
import Data.Maybe.Singletons hiding (MapMaybe)
import Control.Applicative.Singletons
import Data.Eq.Singletons
import Data.Tuple.Singletons
import Data.Bool.Singletons
import Debug.Trace (trace)
import Data.Functor.Identity
import Data.Singletons.Decide
import Data.Either (fromRight)




--------------------------
-- Aux Functions
--------------------------

connector :: Int -> Bool
connector = (> 0)

rConnector :: Bool -> Int
rConnector = \case
  True -> 1
  False -> -1

cTrue :: (ShowM m env, MonadIO m, MonadReader env m, Alternative m) => E ExprTag env m (Value Z)
cTrue = ValE  (rConnector True)

cFalse :: (ShowM m env, MonadIO m, MonadReader env m, Alternative m) => E ExprTag env m (Value Z)
cFalse = ValE (rConnector False)

cvalue :: forall a (env :: Type) (m :: Type -> Type). 
  (MonadReader env m, Alternative m) => LensM m env a -> m a
cvalue l = ask >>= viewM l
  
--------------------------
-- Expression language
--------------------------

data ExprTag

type ShowMContextE m env = ShowMContext (E ExprTag) m env

bottom :: Void
bottom = error "Attempt to evaluate void"

absurd :: Void -> a
absurd m = case m of {}

type instance ValX ExprTag env m = 
  ( Proof2' ShowM m env
  , Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  )
pattern ValE :: (ShowM m env, MonadIO m, MonadReader env m, Alternative m) => Int -> E ExprTag env m (Value Z) 
pattern ValE n <- Val _ n
  where ValE n = Val (P2',P',PMR,P') n

type instance ValueCX ExprTag env m a =
  ( Proof2' ShowM m env 
  , Proof2' ShowM m (E ExprTag env m (Value a))
  , Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  ) 
pattern ValueCE :: 
  ( ShowM m env
  , ShowM m (E ExprTag env m (Value a))
  , MonadIO m
  , MonadReader env m
  , Alternative m
  ) 
  => (E ExprTag env m (Value a), env) -> E ExprTag env m (Value a)
pattern ValueCE n <- ValueC _ n
  where ValueCE n = ValueC (P2',P2',P',PMR,P') n

type instance ClosureX ExprTag env m a =
  ( Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  , Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  ) 
pattern ClosureE :: 
  ( ShowM m env
  , forall a. ShowM m (E ExprTag env m a)
  , MonadIO m
  , MonadReader env m
  , Alternative m
  ) 
  => (E ExprTag env m a,env) -> E ExprTag env m a 
pattern ClosureE n <- Closure _ n
  where ClosureE n = Closure (P2',PFA,P',PMR,P') n


type instance VarX ExprTag env m a =
  ( Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  , Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  ) 
pattern VarE :: 
  ( ShowM m env
  , forall a. ShowM m (E ExprTag env m a)
  , MonadIO m
  , MonadReader env m
  , Alternative m
  ) 
  => LensM m env (E ExprTag env m a) -> E ExprTag env m a 
pattern VarE n <- Var _ n
  where VarE n = Var (P2',PFA,P',PMR,P') n

type instance DeferX ExprTag env m a =
  ( Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  , ProofRV RValue (E ExprTag env m) a m
  , ProofS SingI a
  , ProofS SingI (RValueT (E ExprTag env m) a)
  , Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  )
pattern DeferE :: 
  ( MonadIO m
  , MonadReader env m
  , Alternative m
  , RValue (E ExprTag env m) a m
  , SingI a
  , SingI (RValueT (E ExprTag env m) a)
  , ShowM m env
  , forall a. ShowM m (E ExprTag env m a)
  ) 
  => E ExprTag env m a -> E ExprTag env m (Lazy a) 
pattern DeferE n <- Defer _ n
  where DeferE n = Defer (P',PMR,P',PRV,PS,PS,P2',PFA) n

type instance FormulaX ExprTag env m a = 
  ( Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  , Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  )
pattern FormulaE ::
  ( MonadIO m
  , MonadReader env m
  , Alternative m
  , ShowM m env
  , forall a. ShowM m (E ExprTag env m a)
  ) 
  => LensM m env (E ExprTag env m a)-> E ExprTag env m (Lazy a) 
pattern FormulaE n <- Formula _ n
  where FormulaE n = Formula (P',PMR,P',P2',PFA) n

type instance ExpX ExprTag env m a = Void
pattern ExpE :: Void -> E ExprTag env m a
pattern ExpE v <- Exp v
  where ExpE v = absurd v

type instance LambdaCX ExprTag env m a b =
  ( Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  , ProofRV RValue (E ExprTag env m) b m
  , Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  )
pattern LambdaCE :: 
  ( MonadIO m
  , MonadReader env m
  , Alternative m
  , RValue (E ExprTag env m) b m
  , ShowM m env
  , forall a. ShowM m (E ExprTag env m a)
  )
  => (env, LensM m env (E ExprTag env m a), E ExprTag env m b) -> E ExprTag env m (a ~> b)
pattern LambdaCE n <- LambdaC _ n
  where LambdaCE n = LambdaC (P',PMR,P',PRV,P2',PFA) n

type instance SubtypedX ExprTag env m a b =
  ( ProofUB (RValueT (E ExprTag env m) a) b b
  , ProofS SingI a
  , ProofS SingI b
  , Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  , ProofRV RValue (E ExprTag env m) a m
  , ProofRV RValue (E ExprTag env m) b m
  )
{- pattern SubtypedE :: 
  ( UpperBound (RValueT (E ExprTag env m) a) b ~ Just b
  , SingI a
  , SingI b
  , RValue (E ExprTag env m) a
  , RValue (E ExprTag env m) b
  )
  => E ExprTag env m a -> E ExprTag env m b
pattern SubtypedE n <- Subtyped _ n
  where SubtypedE n = Subtyped (PUB,PS,PS,PRV,PRV) n -}

type instance MinusX ExprTag env m a b = 
  ( Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  , ProofRV RValue (E ExprTag env m) a m
  , ProofRV RValue (E ExprTag env m) b m
  , ProofEQ (~) (RValueT (E ExprTag env m) a) (Value Z)
  , ProofEQ (~) (RValueT (E ExprTag env m) b) (Value Z)
  , Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  )
{- pattern MinusE ::
  ( RValue (E ExprTag env m) a
  , RValue (E ExprTag env m) b
  , RValueT (E ExprTag env m) a ~ Value Z
  , RValueT (E ExprTag env m) b ~ Value Z
  , ShowM m env
  , forall a. ShowM m (E ExprTag env m a)
  ) 
  => E ExprTag env m a -> E ExprTag env m b -> E ExprTag env m (Value Z)
pattern MinusE a b <- Minus _ a b
  where MinusE a b = Minus (PRV,PRV,PEQ,PEQ,P2',PFA) a b -}

type instance LessX ExprTag env m a b =
  ( ProofRV RValue (E ExprTag env m) a m
  , ProofRV RValue (E ExprTag env m) b m
  , ProofEQ (~) (RValueT (E ExprTag env m) a) (Value Z)
  , ProofEQ (~) (RValueT (E ExprTag env m) b) (Value Z)
  , Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  , Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  )

type instance LambdaX ExprTag env m a b =
  ( ProofRV RValue (E ExprTag env m) b m
  , ProofS SingI a
  , ProofS SingI b
  , Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  , Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m 
  )
pattern LambdaE :: 
  ( RValue (E ExprTag env m) b m
  , SingI a
  , SingI b
  , ShowM m env
  , forall a. ShowM m (E ExprTag env m a)
  , MonadIO m
  , MonadReader env m
  , Alternative m 
  )
  => LensM m env (E ExprTag env m a) -> E ExprTag env m b -> E ExprTag env m (a ~> b)
pattern LambdaE n m <- Lambda _ n m
  where LambdaE n m = Lambda (PRV,PS,PS,P2',PFA,P',PMR,P') n m

type instance AppX ExprTag env m f x arg b = 
  ( ProofRV RValue (E ExprTag env m) f m
  , ProofRV RValue (E ExprTag env m) x m
  , ProofEQ (~) (RValueT (E ExprTag env m) f) (arg ~> b)
  , ProofUB (RValueT (E ExprTag env m) x) arg arg
  , ProofS SingI f
  , ProofS SingI x
  , ProofS SingI arg
  , ProofS SingI b
  , Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  , Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  )

type instance IfX ExprTag env m x0 x1 x2 x3 = 
  ( ProofRV RValue (E ExprTag env m) x0 m
  , ProofRV RValue (E ExprTag env m) x1 m
  , ProofRV RValue (E ExprTag env m) x2 m
  , ProofEQ (~) (RValueT (E ExprTag env m) x0) (Value Z)
  , ProofUB (RValueT (E ExprTag env m) x1) (RValueT (E ExprTag env m) x2) x3
  , Proof2' ShowM m env
  , ProofFA ShowM m (E ExprTag env m)
  , Proof' MonadIO m
  , ProofMR MonadReader env m
  , Proof' Alternative m
  , ProofS SingI x1
  , ProofS SingI x2
  , ProofS SingI x3
  )

instance (ShowM m env,MonadIO m, Alternative m, MonadReader env m) => RValue (E ExprTag env m) (Value a) m where
  type RValueT (E ExprTag env m) (Value a) = Value a
  rvalue (ValE n) = pure (ValE n)
  rvalue (ValueC (P2',P2',P',PMR,P') (e,gamma)) = localM (pure . const gamma) $ rvalue e
  rvalue (Minus (P',PMR,P',PRV,PRV,PEQ,PEQ,P2',x@PFA) a b) = (,) <$> rvalue a <*> rvalue b >>= \case
    (ValE a', ValE b') -> pure $ ValE (a' - b')
    (a',b') ->  liftA2 (Minus (P',PMR,P',PRV,PRV,PEQ,PEQ,P2',x))  (rvalue a') (rvalue b') >>= rvalue
  rvalue (Less (PRV,PRV,PEQ,PEQ,P2',x@PFA,P',PMR,P') a b) = (,) <$> rvalue a <*> rvalue b >>= \case
    (ValE a', ValE b') -> pure $ ValE (rConnector $ a' < b')
    (a',b') -> liftA2 (Less (PRV,PRV,PEQ,PEQ,P2',x,P',PMR,P'))  (rvalue a') (rvalue b') >>= rvalue
  rvalue (App @_ @f @x @b @arg (PRV,PRV,PEQ,PUB,p0@PS,PS,PS,PS,P2',p@PFA,P',PMR,P') f a) = rvalue f >>= \case
    LambdaC _ (gamma, x, t) -> withSingIRType @x @(E ExprTag env m) $ do
      arg <- rvalue a >>= \rva -> case upcast @_ @arg rva of
        SameTypeUB rva'   -> pure rva'
        RightUB rva'      -> pure rva'
        LeftUB _       -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
      t'  <- localM (setMF x arg . const gamma) $ rvalue t
      gamma' <- setMF x arg gamma
      pure $ Closure (P2',p,P',PMR,P')  (t',gamma')
    f' ->   rvalue $ App (PRV,PRV,PEQ,PUB,PS,PS,PS,PS,P2',p,P',PMR,P') f' a
  rvalue (Var (P2',PFA,P',PMR,P') x) = rvalue <=< cvalue $ x
  rvalue e@(If (PRV,PRV,PRV,PEQ,PUB,P2',PFA,P',PMR,P',PS,PS,PS) _ _ _)  = genRVIf e
  rvalue (LambdaC c@(P',PMR,P',PRV,P2',PFA) gamma) = pure $ LambdaC c gamma
  rvalue (Lambda c@(PRV,PS,PS,P2',p@PFA,P',PMR,P') x t) = do
    gamma <- ask
    pure $ LambdaC (P',PMR,P',PRV,P2',p) (gamma,x,t)
  rvalue (Closure (P2',PFA,P',PMR,P') (e,gamma)) = localM (pure . const gamma) $ rvalue e
  rvalue (Subtyped @_ @_ @_ @e1 @e2 (PUB,PS,PS,P',PMR,P',PRV,PRV) e1) = do
    --trace "rvaluing a subtyped" pure ()
    e1' :: E ExprTag env m (RValueT (E ExprTag env m) e1)  <- withSingIRType @e1 @(E ExprTag env m) $ rvalue e1
    let e1'' :: E ExprTag env m (RValueT (E ExprTag env m) e2) 
          = withRVType @(E ExprTag env m) @m (sing @e1) 
          $ withSingIRType @e1 @(E ExprTag env m)
          $ withSingIRType @e2 @(E ExprTag env m)
          $ withRVType @(E ExprTag env m) @m (sing @(RValueT (E ExprTag env m) e1)) 
          $ withRVType @(E ExprTag env m) @m (sing @(RValueT (E ExprTag env m) e2)) 
          $ rvaluePreservesST @(RValueT (E ExprTag env m) e1) @e2 @(E ExprTag env m)
          $ Subtyped @_ @_ @_ @(RValueT (E ExprTag env m) e1) @(RValueT (E ExprTag env m)  e2) (PUB,PS,PS,P',PMR,P',PRV,PRV) e1'
    pure e1''
  rvalue (Exp v) = absurd v 

instance  (ShowM m env,MonadIO m, Alternative m, MonadReader env m) =>  RValue  (E ExprTag env m) (Lazy (Value a)) m where
  type RValueT (E ExprTag env m) (Lazy (Value a)) = Value a
  rvalue (Defer (P',PMR,P',PRV,PS,PS,P2',p@PFA) v) = do
    gamma <- ask 
    pure $ Closure (P2',p,P',PMR,P') (v,gamma)
  rvalue (App @_ @f @x @b @arg (PRV,PRV,PEQ,PUB,PS,PS,PS,PS,P2',p@PFA,P',PMR,P') f a) = rvalue f >>= \case
    LambdaC _ (gamma, x, t) -> withSingIRType @x @(E ExprTag env m) $ do
      arg <- rvalue a >>= \rva -> case upcast @_ @arg rva of
        SameTypeUB rva'   -> pure rva'
        RightUB rva'      -> pure rva'
        LeftUB _       -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
      t'  <- localM (setMF x arg . const gamma) $ rvalue t
      gamma' <- setMF x arg gamma
      pure $ Closure (P2',p,P',PMR,P')  (t',gamma')
    f' -> rvalue $ App (PRV,PRV,PEQ,PUB,PS,PS,PS,PS,P2',p,P',PMR,P') f' a
  rvalue (Closure (P2',PFA,P',PMR,P') (e,gamma)) = localM (pure . const gamma) $ rvalue e
  rvalue (Var (P2',PFA,P',PMR,P') x) = rvalue <=< cvalue $ x
  rvalue e@(If (PRV,PRV,PRV,PEQ,PUB,P2',PFA,P',PMR,P',PS,PS,PS) _ _ _)  = genRVIf e
  rvalue (Formula (P',PMR,P',P2',PFA) v) = cvalue v
  rvalue (Subtyped @_ @_ @_ @e1 @e2 (PUB,PS,PS,P',PMR,P',PRV,PRV) e1) = do
    --trace "rvaluing a subtyped" pure ()
    e1' :: E ExprTag env m (RValueT (E ExprTag env m) e1)  <- withSingIRType @e1 @(E ExprTag env m) $ rvalue e1
    let e1'' :: E ExprTag env m (RValueT (E ExprTag env m) e2) 
          = withRVType @(E ExprTag env m) @m (sing @e1) 
          $ withSingIRType @e1 @(E ExprTag env m)
          $ withSingIRType @e2 @(E ExprTag env m)
          $ withRVType @(E ExprTag env m) @m (sing @(RValueT (E ExprTag env m) e1)) 
          $ withRVType @(E ExprTag env m) @m (sing @(RValueT (E ExprTag env m) e2)) 
          $ rvaluePreservesST @(RValueT (E ExprTag env m) e1) @e2 @(E ExprTag env m)
          $ Subtyped @_ @_ @_ @(RValueT (E ExprTag env m) e1) @(RValueT (E ExprTag env m) e2) (PUB,PS,PS,P',PMR,P',PRV,PRV) e1'
    pure e1''
  rvalue (Exp v) = absurd v 


instance  (ShowM m env,MonadIO m, Alternative m, MonadReader env m) =>  RValue (E ExprTag env m) (Lazy (Lazy a)) m where 
  type RValueT (E ExprTag env m) (Lazy (Lazy a)) = Lazy a
  rvalue (Defer (P',PMR,P',PRV,PS,PS,P2',p@PFA) v) = do
    gamma <- ask 
    pure $ Closure (P2',p,P',PMR,P') (v,gamma)
  rvalue (App @_ @f @x @b @arg (PRV,PRV,PEQ,PUB,PS,PS,PS,PS,P2',p@PFA,P',PMR,P') f a) = rvalue f >>= \case
    LambdaC _ (gamma, x, t) -> withSingIRType @x @(E ExprTag env m) $ do
      arg <- rvalue a >>= \rva -> case upcast @_ @arg rva of
        SameTypeUB rva'   -> pure rva'
        RightUB rva'      -> pure rva'
        LeftUB _       -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
      t'  <- localM (setMF x arg . const gamma) $ rvalue t
      gamma' <- setMF x arg gamma
      pure $ Closure (P2',p,P',PMR,P')  (t',gamma')
    f' -> rvalue $ App (PRV,PRV,PEQ,PUB,PS,PS,PS,PS,P2',p,P',PMR,P') f' a
  rvalue (Closure (P2',PFA,P',PMR,P') (e,gamma)) = localM (pure . const gamma) $ rvalue e
  rvalue (Var (P2',PFA,P',PMR,P') x) = rvalue <=< cvalue $ x
  rvalue e@(If (PRV,PRV,PRV,PEQ,PUB,P2',PFA,P',PMR,P',PS,PS,PS) _ _ _)  = genRVIf e
  rvalue (Formula (P',PMR,P',P2',PFA) v) = cvalue v
  rvalue (Subtyped @_ @_ @_ @e1 @e2 (PUB,PS,PS,P',PMR,P',PRV,PRV) e1) = do
    --trace "rvaluing a subtyped" pure ()
    e1' :: E ExprTag env m (RValueT (E ExprTag env m) e1)  <- withSingIRType @e1 @(E ExprTag env m) $ rvalue e1
    let e1'' :: E ExprTag env m (RValueT (E ExprTag env m) e2) 
          = withRVType @(E ExprTag env m) @m (sing @e1) 
          $ withSingIRType @e1 @(E ExprTag env m)
          $ withSingIRType @e2 @(E ExprTag env m)
          $ withRVType @(E ExprTag env m) @m (sing @(RValueT (E ExprTag env m) e1)) 
          $ withRVType @(E ExprTag env m) @m (sing @(RValueT (E ExprTag env m) e2)) 
          $ rvaluePreservesST @(RValueT (E ExprTag env m) e1) @e2 @(E ExprTag env m)
          $ Subtyped @_ @_ @_ @(RValueT (E ExprTag env m) e1) @(RValueT (E ExprTag env m) e2) (PUB,PS,PS,P',PMR,P',PRV,PRV) e1'
    pure e1''
  rvalue (Exp v) = absurd v 

------------------------------
-- Generic R-Value Functions
------------------------------

genRVar :: 
  ( MonadIO m
  , MonadReader env m
  , Alternative m 
  , ShowM m env
  , forall a. ShowM m (E ExprTag env m a)
  , RValue (E ExprTag env m) a m
  , RValueT (E ExprTag env m) a ~ c
  , SingI c
  ) => E ExprTag env m a -> m (E ExprTag env m c)
genRVar (Var (P2',PFA,P',PMR,P') x) = rvalue <=< cvalue $ x
genRVar _ = undefined

genRVIf ::forall {x4 :: Types} (m :: Type -> Type) env (x3 :: Types) .
  ( MonadIO m
  , MonadReader env m
  , Alternative m 
  , ShowM m env
  , SingI x3
  , RValue (E ExprTag env m) x3 m
  , RValueT (E ExprTag env m) x3 ~ x4
  )
  => E ExprTag env m x3 -> m (E ExprTag env m x4)
genRVIf (If @_ @_ @_ @(x0 :: Types) @(x1 :: Types) @(x2 :: Types) (PRV,PRV,PRV,PEQ,PUB,P2',x@PFA,P',PMR,P',PS,PS,PS) cond t f) 
  = withSingIRType @x1 @(E ExprTag env m)
  $ withSingIRType @x2 @(E ExprTag env m)
  $ rvalue cond >>= \case
    ValE (connector -> True) -> do 
      t' <- rvalue t
      withSingIRType @x3 @(E ExprTag env m) $ case upcast @_ @x4 t' of
        SameTypeUB t'' -> pure t''
        RightUB t'' -> pure t''
        LeftUB _ -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
        NonExistentUB -> error "impossible case"
    ValE (connector -> False) -> do 
      f' :: E ExprTag env m c1 <- rvalue f
      withSingIRType @x3 @(E ExprTag env m) $ case upcast @_ @x4 f' of
        SameTypeUB f'' -> pure f''
        RightUB f'' -> pure f''
        LeftUB _ -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
        NonExistentUB -> error "impossible case"
    c' -> rvalue (If @ExprTag @env @m @(Value Z) @x1 @x2 (PRV,PRV,PRV,PEQ,PUB,P2',x,P',PMR,P',PS,PS,PS) c' t f)
genRVIf _ = undefined

---------------------
-- Upcasting
---------------------

data UpperBoundResults f a b where
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

upcastable :: forall (a :: Types) (b :: Types) (env :: Type) (m :: Type -> Type). 
  ( SingI a
  , SingI b
  , (ShowM m env,MonadIO m, Alternative m, MonadReader env m)
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
            -> withRVType @(E ExprTag env m) @m  (sing @a)
            $  rvalueIsPred @a
            $  withSingI sub 
            $  SomethingElseUBN @a @b
      SNothing  -> NonExistentUB

upcast :: forall (a :: Types) (b :: Types) env m. 
  ( SingI a
  , SingI b
  , MonadIO m
  , MonadReader env m
  , Alternative m 
  , ShowM m env
  ) => E ExprTag env m a  
  -> UpperBoundResults (E ExprTag env m) a b
upcast f
  = withSingIUBType @a @b 
  $ case decideEquality (sing @a) (sing @b) of
    Just Refl -> ubIsIdempotent @a $ SameTypeUB f
    Nothing -> case sing @(UpperBound a b) of
      SJust @_ @n sub -> case decideEquality (sing @a) sub of
        Just Refl -> LeftUB f
        Nothing   -> case decideEquality (sing @b) sub of
          Just Refl 
            -> rvalueIsPred @a @(E ExprTag env m) 
            $ withSingIRType @a @(E ExprTag env m)
            $ ubIsTransitive' @(RValueT (E ExprTag env m) a) @a @b 
            $ withRVType @(E ExprTag env m) @m (sing @a) 
            $ withRVType @(E ExprTag env m) @m (sing @b) 
            $ RightUB (Subtyped (PUB,PS,PS,P',PMR,P',PRV,PRV) f)
          Nothing   
            -> withRVType @(E ExprTag env m) @m (sing @a) 
            $ withSingI sub
            $ withRVType @(E ExprTag env m) @m (sing @n) 
            $ subtyped'CTX @a @b @(E ExprTag env m) @m
            $ SomethingElseUB (Subtyped (PUB,PS,PS,P',PMR,P',PRV,PRV) f)
      SNothing  -> NonExistentUB
