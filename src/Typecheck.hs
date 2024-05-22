{-# LANGUAGE FlexibleContexts #-}
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

type Gamma  = Map A.Symbol P.Type
type Gamma' = Map A.Symbol SomeTypeRep
data Errors 
  = UnboundVariable A.Symbol
  | TypeMismatch P.Type P.Type

newtype Actions t = Actions { runActions :: [P.A0 t] }

class TypeVars f where
  typeVars :: (MonadError Errors m, MonadReader Gamma m) => f P.NoVarInfo -> m (f P.VarInfo)

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

class TypecheckE f where
  typecheckE :: 
    ( MonadError Errors m
    , MonadReader Gamma' m
    ) => f P.VarInfo -> m (A.E env m a)




instance TypecheckE P.Atom where
  typecheckE ::  forall m env a.
    ( MonadError Errors m, MonadReader Gamma' m
    )
    => P.Atom P.VarInfo -> m (A.E env m a)
  typecheckE (P.Val x) = case eqT @a @(A.Value Int) of
    Just Refl -> pure $ A.Val x
    Nothing   -> undefined
  typecheckE (P.Var x (Identity t)) = asks (M.lookup x) >>= \case
    Just (SomeTypeRep @k _) -> case typeMap t of
      SomeTypeRep @k' _ -> case (eqT @k @k', eqT @k @a) of
        (Just Refl, Just Refl) -> pure $ A.Var @k (fromString x)
        _ -> throwError $ TypeMismatch t undefined
    Nothing -> throwError $ UnboundVariable x
  typecheckE (P.Parens x) = typecheckE x
  typecheckE (P.Defer x) = do 
    te :: A.E env m (A.Lazy a') <- A.Defer <$> typecheckE x 
    case eqT @a @(A.Lazy a') of
      Just Refl -> pure te
      Nothing -> undefined
  typecheckE (P.IfThenElse c t f) = do
    tc :: A.E env m x0 <- typecheckE c
    tt :: A.E env m x1 <- typecheckE t
    tf :: A.E env m x2 <- typecheckE f
    let te = A.If @(RValuable x1) @(RValuable x2) @x1 @x2 @x0 @_ @env @m tc tt tf
    undefined
    {- case eqT @a @(A.Lazy a) of
      Just Refl -> pure te
      Nothing -> undefined -}
  typecheckE (P.Formula e) = P.Formula <$> typecheckE e
  typecheckE (P.Lambda s t e) = P.Lambda s t <$> local (M.insert s t) (typecheckE e)

type family RValuable (a :: Type) :: Type where
  RValuable (A.Value a) = A.Value a
  RValuable (A.Lazy (A.Value a)) = A.Lazy (A.Value a)
  RValuable (A.Lazy (A.Lazy a)) = A.Lazy a


