

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
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Zilly.Classic.TypeCheck where


import Parser.Classic.ZillyParser qualified as P
import Utilities.LensM
import Utilities.TypedMap hiding (empty)
import Utilities.ShowM
import Zilly.ADT.Expression
import Zilly.ADT.Action
import Zilly.Classic.Action
import Zilly.Classic.Expression
import Zilly.Classic.Interpreter hiding (Env)
import Zilly.RValue
import Zilly.Types
import Zilly.Upcast
import Control.Monad.Reader


import Data.Kind (Type)
import Data.Singletons
import Control.Monad.IO.Class (MonadIO)
import Control.Applicative (Alternative(..))
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Writer.CPS
import Control.Monad.Error.Class
import Control.Monad.Trans.Maybe
import Parser.Classic.ZillyParser qualified as P
import Control.Monad (MonadPlus(mzero))
import Text.Parsec (SourcePos)
import Data.Singletons.Decide
import Data.Traversable

type Some :: forall k. (k -> Type) -> Type 
data Some (f :: k -> Type) where
    MkSome :: forall {k} f (a :: k). SingI a => f a -> Some f

type TypeCheckEnv = Map Symbol Types
type ErrorLog = [TypeCheckErrors]

data TypeCheckErrors 
  = SymbolNotDefined Symbol SourcePos
  | NeedsLValue P.Expr SourcePos
  | TypeMismatch Types Types SourcePos
  | NonUnifiableTypes (P.Expr,Types,SourcePos) (P.Expr,Types,SourcePos)

instance Show TypeCheckErrors where
  show (SymbolNotDefined s pos) = "Symbol " <> show s <> " not defined " <> show pos
  show (NeedsLValue e pos) = "Needs lvalue " <> show e <> " " <> show pos 
  show (TypeMismatch t1 t2 pos) = "Type mismatch " <> show pos
  show (NonUnifiableTypes (e1,t1,pos1) (e2,t2,pos2)) 
    = "Non unifiable types " <> show t1 <> "(" <> show pos1 <> ") " 
      <> show t2 <> "(" <> show pos2 <> ") "

newtype TCM a = TCM { unTCM :: ReaderT TypeCheckEnv (MaybeT (Writer ErrorLog) ) a }
  deriving newtype 
    ( Functor
    , Applicative
    , Monad
    , MonadReader TypeCheckEnv
    , MonadWriter ErrorLog
    , Alternative
    , MonadFail
    )



class TypeCheck actx e ret | e -> ret where
  type TCC actx ret :: ret -> Type
  typeCheck :: forall {f} {ctx}.
    ( AssocActionTag actx ~ ctx
    , TCC actx ret ~ f
    ) => e -> TCM (Some f,TypeCheckEnv)

instance TypeCheck ActionTag P.Atom Types where
  type TCC ActionTag  Types = E ExprTag
  typeCheck (P.Val s _) = do
    env <- ask
    pure (MkSome $  ValE s,env)
  typeCheck (P.Var s pos) = do
    env <- ask
    case M.lookup s env of
      Just t -> case toSing  t of
        SomeSing @_ @t st -> withSingI st 
          $ pure (MkSome $ VarE (mkVar @t @ExprTag s) ,env)
      Nothing -> 
        tell [SymbolNotDefined s pos] >> empty
  typeCheck (P.Parens e _) = typeCheck @ActionTag e
  typeCheck (P.Defer e _) = do
    (MkSome @_ @a a,env) <- typeCheck @ActionTag e
    withSingIRType @a
      $ withRVType @ExprTag (sing @a)
      $ pure (MkSome $ DeferE a,env)
  typeCheck (P.Formula (P.OfTerm (P.OfAtom (P.Var s varPos))) _) = do
    env <- ask
    case M.lookup s env of
      Just t -> case toSing  t of
        SomeSing @_ @t st -> withSingI st 
          $ pure (MkSome $ VarE (mkVar @t @ExprTag s) ,env)
      Nothing -> 
        tell [SymbolNotDefined s varPos] >> empty
  typeCheck (P.Formula e pos) = do
    (MkSome @_ @e' e',env) <- typeCheck @ActionTag e
    case e' of
      VarE v -> pure (MkSome $ FormulaE v,env)
      _ -> tell [NeedsLValue e pos] >> empty
  typeCheck (P.IfThenElse e1 e2 e3 pos) = do
    env <- ask
    (MkSome @_ @x0 x0,_) <- typeCheck @ActionTag e1
    (MkSome @_ @x1 x1,_) <- typeCheck @ActionTag e2
    (MkSome @_ @x2 x2,_) <- typeCheck @ActionTag e3
    withSingIRType @x0 
      $ withSingIRType @x1
      $ withSingIRType @x2
      $ withRVType @ExprTag (sing @x0)
      $ withRVType @ExprTag (sing @x1)
      $ withRVType @ExprTag (sing @x2)
      $ case decideEquality (sing @(RValueT x0)) (sing @(Value Z)) of
        Nothing -> tell [TypeMismatch (demote @x0) (Value Z) pos] >> empty
        Just Refl -> case upcastable @(RValueT x1) @(RValueT x2) @ExprTag of
          NonExistentUB     ->  tell [undefined] >> empty
          SameTypeUB _      -> pure (MkSome $ IfE x0 x1 x2,env)
          LeftUB _          -> pure (MkSome $ IfE x0 x1 x2,env)
          RightUB _         -> pure (MkSome $ IfE x0 x1 x2,env)
          SomethingElseUB _ -> pure (MkSome $ IfE x0 x1 x2,env)
  typeCheck (P.Lambda s t e pos) = do
    env <- ask
    let env' = M.insert s (P.parserT2AdtT t) env
    (MkSome @_ @body body,_) <- local (const env') $ typeCheck @ActionTag e
    -- never fails
    (MkSome @_ @var (Var _ var),_) <- local (const env') $ typeCheck @ActionTag (P.Var s pos)
    withRVType @ExprTag (sing @body)
      $ pure (MkSome $ LambdaE var body,env)


instance TypeCheck ActionTag P.Term Types where
  type TCC ActionTag Types = E ExprTag

  typeCheck (P.OfAtom a) = typeCheck @ActionTag a
  typeCheck (P.App f x pos) = do
    (MkSome @_ @f' f',_) <- typeCheck @ActionTag f
    (MkSome @_ @x' x',_) <- typeCheck @ActionTag x
    withRVType @ExprTag (sing @f')
      $ withRVType @ExprTag (sing @x')
      $ withSingIRType @f'
      $ withSingIRType @x'
      $ case sing @f' of
        SValue ((sarg :: Sing arg) :%-> (sb :: Sing b)) 
          -> withSingI sarg 
          $ withSingI sb
            $ case upcastable @(RValueT x') @arg  @ExprTag of
            NonExistentUB     -> tell [undefined] >> empty
            SomethingElseUB _ -> tell [undefined] >> empty
            LeftUB _          -> tell [undefined] >> empty
            SameTypeUB _      -> pure (MkSome $ AppE f' x',M.empty)
            RightUB _         -> pure (MkSome $ AppE f' x',M.empty)
            
        _ -> tell [undefined] >> empty
      

instance TypeCheck ActionTag P.Expr Types where
  type TCC ActionTag  Types = E ExprTag
  typeCheck (P.OfTerm t) = typeCheck @ActionTag t
  typeCheck (P.Minus e t pos) = do
    env <- ask
    (MkSome @_ @e' e',_) <- typeCheck @ActionTag e
    (MkSome @_ @t' t',_) <- typeCheck @ActionTag t
    withRVType @ExprTag (sing @e')
      $ withRVType @ExprTag (sing @t')
      $ withSingIRType @e'
      $ withSingIRType @t'
      $ case (decideEquality' @_ @(RValueT e') @(Value Z),decideEquality' @_ @(RValueT t') @(Value Z)) of
        (Just Refl,Just Refl) -> pure (MkSome $ MinusE e' t',env)
        (Nothing,Nothing) -> tell [undefined] >> empty
        (Just Refl,Nothing) -> tell [undefined] >> empty
        (Nothing,Just Refl) -> tell [undefined] >> empty
  typeCheck (P.Less e t pos) = do
    env <- ask
    (MkSome @_ @e' e',_) <- typeCheck @ActionTag e
    (MkSome @_ @t' t',_) <- typeCheck @ActionTag t
    withRVType @ExprTag (sing @e')
      $ withRVType @ExprTag (sing @t')
      $ withSingIRType @e'
      $ withSingIRType @t'
      $ case (decideEquality' @_ @(RValueT e') @(Value Z),decideEquality' @_ @(RValueT t') @(Value Z)) of
        (Just Refl,Just Refl) -> pure (MkSome $ LessE e' t',env)
        (Nothing,Nothing) -> tell [undefined] >> empty
        (Just Refl,Nothing) -> tell [undefined] >> empty
        (Nothing,Just Refl) -> tell [undefined] >> empty

instance TypeCheck ActionTag P.A0 () where
  type TCC ActionTag () = A ActionTag
  typeCheck (P.Decl t s e pos) = do
    env <- ask
    let env' = M.insert s (rValueT $ P.parserT2AdtT t) env
    (MkSome @_ @e' e',_) <- local (const env') $ typeCheck @ActionTag e
    -- never fails
    (MkSome @_ @var (Var _ var),_) <- local (const env') $ typeCheck @ActionTag (P.Var s pos)
    withSingIRType @e'
      $ withSingIRType @var
      $ withRVType @ExprTag (sing @e')
      $ withRVType @ExprTag (sing @var)
      $ case upcastable @(RValueT  var)  @(RValueT  e') @ExprTag of
        SameTypeUB  _     -> pure (MkSome (var := e'),env')
        LeftUB      _     -> pure (MkSome (var := e'),env')
        RightUB     _     -> undefined
        SomethingElseUB _ -> undefined
        NonExistentUB        -> undefined

  typeCheck (P.Assign s e pos) = do
    env <- ask
    (MkSome @_ @e' e',_) <- typeCheck @ActionTag e
    -- never fails
    (MkSome @_ @var (Var _ var),_) <- typeCheck @ActionTag (P.Var s pos)
    withSingIRType @e'
      $ withSingIRType @var
      $ withRVType @ExprTag (sing @e')
      $ withRVType @ExprTag (sing @var)
      $ case upcastable @(RValueT  var)  @(RValueT  e') @ExprTag of
        SameTypeUB  _     -> pure (MkSome (var := e'),env)
        LeftUB      _     -> pure (MkSome (var := e'),env)
        RightUB     _     -> undefined
        SomethingElseUB _ -> undefined
        NonExistentUB        -> undefined
  typeCheck (P.Print e pos) = do
    env <- ask
    (MkSome @_ @e' e',_) <- typeCheck @ActionTag e
    withRVType @ExprTag (sing @e')
      $ pure (MkSome $ Print e',env)

typeCheckProgram ::P.A1 -> TCM [A ActionTag '()]
typeCheckProgram as = fmap snd  . forAccumM M.empty (f as) $ \env a -> do
  (MkSome @_ @a' a',env') <- local (const env) $  typeCheck @ActionTag a
  case decideEquality (sing @a') (sing @'()) of
    Just Refl -> pure (env',a')
    _ -> tell [undefined] >> empty
  
  where 
    f (P.OfA0 a) = [a]
    f (P.Seq a as) = a : as

typeCheckProgram' ::P.A1 ->  (Maybe [A ActionTag '()],ErrorLog)
typeCheckProgram' as 
  = runWriter . runMaybeT . runReaderT (unTCM $ typeCheckProgram as) $ M.empty