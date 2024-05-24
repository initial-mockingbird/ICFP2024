module Typecheck where
  
{- {-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Typecheck where


import qualified Parser as P
import qualified ADT as A
import Control.Monad.Reader
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Error.Class
import Data.Functor.Identity
import Type.Reflection 
import Data.Kind (Type)
import Data.Typeable (heqT,eqT)
import ADT (ADTContext)
import ShowM
import Data.String (IsString(..))
import Lensy 
import Action (ShowMContext)

type Gamma  = Map A.Symbol P.Type
type Gamma' = Map A.Symbol SomeTypeRep
data Errors 
  = UnboundVariable A.Symbol
  | TypeMismatch P.Type P.Type

newtype Actions t = Actions { runActions :: [P.A0 t] }

class TypeVars f where
  typeVars :: 
    (MonadError Errors m, MonadReader Gamma m) => f P.NoVarInfo -> m (f P.VarInfo)

instance TypeVars P.Atom where
  typeVars (P.Var x _) = asks (M.lookup x) >>= \case
    Just t -> pure $ P.Var x (Identity t) 
    Nothing -> throwError $ UnboundVariable x
  typeVars (P.Val x) = pure $ P.Val x
  typeVars (P.Parens x) = P.Parens <$> typeVars x
  typeVars (P.Defer x) = P.Defer <$> typeVars x
  typeVars (P.IfThenElse c t f) = P.IfThenElse <$> typeVars c <*> typeVars t <*> typeVars f
  typeVars (P.Formula e) = P.Formula <$> typeVars e
  typeVars (P.Lambda s t e) = P.Lambda s t <$> local (M.insert s t) (typeVars e)

instance TypeVars P.Term where
  typeVars (P.OfAtom a) = P.OfAtom <$> typeVars a
  typeVars (P.App f x) = P.App <$> typeVars f <*> typeVars x

instance TypeVars P.Expr where
  typeVars (P.Minus e t) = P.Minus  <$> typeVars e <*> typeVars t
  typeVars (P.Less e t)  = P.Less   <$> typeVars e <*> typeVars t
  typeVars (P.OfTerm t)  = P.OfTerm <$> typeVars t

instance TypeVars P.A0 where
  typeVars (P.Decl t s e) = P.Decl t s <$> local (M.insert s t) (typeVars e)
  typeVars (P.Assign x _ e) = liftA2 (\x (y,z) -> P.Assign y z x) (typeVars e) $ asks (M.lookup x) >>= \case
    Just t -> pure (x, Identity t)
    Nothing -> throwError $ UnboundVariable x
  typeVars (P.Print e) = P.Print <$> typeVars e

instance TypeVars Actions where
  typeVars (Actions (x:xs)) = typeVars x >>= \case
    (P.Decl t s e) -> do
      Actions xs' <- local (M.insert s t) (typeVars (Actions xs))
      pure $ Actions (P.Decl t s e : xs')
    x' -> do
      Actions xs' <- typeVars (Actions xs)
      pure $ Actions (x' : xs')
  typeVars (Actions []) = pure $ Actions []

typeMap :: P.Type -> SomeTypeRep
typeMap (P.OfType0 P.Int') = SomeTypeRep $ typeRep @(A.Value Int)
typeMap (P.OfType0 (P.Lazy t)) = case typeMap t of
  SomeTypeRep @k @a tr -> case typeRepKind tr of
    tr' -> withTypeable tr' $ SomeTypeRep $ typeRep @(A.Lazy k)
typeMap (P.OfType0 (P.LazyS t)) = case typeMap t of
  SomeTypeRep @k @a tr -> case typeRepKind tr of
    tr' -> withTypeable tr' $ SomeTypeRep $ typeRep @(A.Lazy k)
typeMap (P.Arrow t0 t) = case (typeMap (P.OfType0 t0), typeMap t) of
  (SomeTypeRep @k0 tr0,SomeTypeRep @k1 tr1) -> case (typeRepKind tr0, typeRepKind tr1) of
    (tr0', tr1') -> withTypeable tr0' 
      $ withTypeable tr1' $ SomeTypeRep $ typeRep @(A.Value (k0 -> k1))

class Subtype a b where
  upcast :: a -> b

instance Subtype 
  (A.E env m  (A.Value a)) 
  (A.E env m  (A.Value a)) 
  where
  upcast = id

instance 
  ( ADTContext m env
  , ShowM m (A.E env m (A.Value Int))
  ) => Subtype
  (A.E env m  (A.Value a))
  (A.E env m  (A.Lazy (A.Value a))) 
  where
    upcast n@(A.Val     {}) = A.Defer n
    upcast x@(A.Var     {}) = A.Defer x
    upcast e@(A.Minus   {}) = A.Defer e
    upcast e@(A.Less    {}) = A.Defer e
    upcast e@(A.If      {}) = A.Defer e
    upcast e@(A.Lambda  {}) = A.Defer e
    upcast e@(A.LambdaC {}) = A.Defer e
    upcast e@(A.App     {}) = A.Defer e
    upcast e@(A.Closure {}) = A.Defer e
    upcast e@(A.ValueC  {}) = A.Defer e
    -- Add wildcard patterns for other unmatched cases

instance 
  ( ADTContext m env
  , ShowM m (A.E env m (A.Value Int))
  , Subtype a b
  ) => Subtype
  (A.E env m  (A.Lazy a))
  (A.E env m  (A.Lazy b)) 
  where
    upcast = undefined
    {- upcast x@(A.Var     {}) = A.Defer x
    upcast e@(A.If      {}) = A.Defer e
    upcast e@(A.App     {}) = A.Defer e
    upcast e@(A.Closure {}) = A.Defer e
    upcast e@(A.Defer   {}) = A.Defer e -}

class TypeOfP f where
  typeOfP :: 
    (MonadError Errors m) => f P.VarInfo -> m [SomeTypeRep]

instance TypeOfP P.Expr where
  typeOfP (P.Minus _ _)= pure 
    [ SomeTypeRep $ TypeRep @(A.Value Int)
    , SomeTypeRep $ TypeRep @(A.Value Int)
    , SomeTypeRep $ TypeRep @(A.Value Int)
    ]
  typeOfP (P.Less _ _)= pure 
    [ SomeTypeRep $ TypeRep @(A.Value Int)
    , SomeTypeRep $ TypeRep @(A.Value Int)
    , SomeTypeRep $ TypeRep @(A.Value Int)
    ]
  typeOfP (P.OfTerm t) = typeOfP t

instance TypeOfP P.Term where
  typeOfP (P.App f x) = do
    f' <- typeOfP f
    x' <- typeOfP x
    pure $ f' ++ x'
  typeOfP (P.OfAtom x) = typeOfP x

instance TypeOfP P.Atom where
  typeOfP (P.Val {}) = pure [SomeTypeRep $ TypeRep @(A.Value Int)]
  typeOfP (P.Var _ (Identity tr)) =  pure [typeMap tr]
  typeOfP (P.Parens e) = typeOfP e
  typeOfP (P.Defer e) = typeOfP e
  typeOfP _ = undefined

class TypecheckE f where
  typecheckE :: forall m' a env m.
    ( MonadError Errors m
    , MonadReader Gamma' m
    , ADTContext m' env
    , Typeable a
    , ShowMContext m' env
    , forall x. IsString (LensyM' m' env (A.E env m' x))
    ) => TypeRep a -> f P.VarInfo -> m (A.E env m' a)

instance TypecheckE P.Expr where
  typecheckE :: forall m' a env m.
    ( MonadError Errors m
    , MonadReader Gamma' m
    , ADTContext m' env
    , Typeable a
    , ShowMContext m' env
    , forall x. IsString (LensyM' m' env (A.E env m' x))
    ) => TypeRep a -> P.Expr P.VarInfo -> m (A.E env m' a)
  typecheckE _ (P.Minus el er) = do 
    el' <- typecheckE @_ @m' (typeRep @(A.Value Int)) el
    er' <- typecheckE @_ @m' (typeRep @(A.Value Int)) er
    case eqT @a @(A.Value Int) of
      Just Refl -> pure $ A.Minus el' er'
      Nothing -> error "Type mismatch"
    
  typecheckE _ (P.Less el er) = do 
    el' <- typecheckE @_ @m' (typeRep @(A.Value Int)) el
    er' <- typecheckE @_ @m' (typeRep @(A.Value Int)) er
    case eqT @a @(A.Value Int) of
      Just Refl -> pure $ A.Minus el' er'
      Nothing -> error "Type mismatch"
  typecheckE tr (P.OfTerm t) = typecheckE tr t

instance TypecheckE P.Term where
  typecheckE :: forall m' a env m.
    ( MonadError Errors m
    , MonadReader Gamma' m
    , ADTContext m' env
    , Typeable a
    , ShowMContext m' env
    , forall x. IsString (LensyM' m' env (A.E env m' x))
    ) => TypeRep a -> P.Term P.VarInfo -> m (A.E env m' a)
  typecheckE _ (P.App f x) = do
    
    undefined
  typecheckE tr (P.OfAtom a) = typecheckE tr a

instance TypecheckE P.Atom where
  typecheckE = undefined

type family RValuable (a :: Type) :: Type where
  RValuable (A.Value a) = A.Value a
  RValuable (A.Lazy (A.Value a)) = A.Lazy (A.Value a)
  RValuable (A.Lazy (A.Lazy a)) = A.Lazy a


 -}