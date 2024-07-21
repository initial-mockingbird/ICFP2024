

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

module Zilly.TypeCheck where


import Parser.ZillyParser qualified as P
import Utilities.LensM
import Utilities.TypedMap hiding (empty)
import Utilities.ShowM
import Zilly.ADT
import Zilly.Action
import Zilly.Expressions
import Zilly.Interpreter hiding (Env)
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
import Parser.ZillyParser qualified as P
import Control.Monad (MonadPlus(mzero))
import Text.Parsec (SourcePos)
import Data.Singletons.Decide

data Some f = forall  (a :: Types). SingI a => MkSome (f a)

type TypeCheckEnv = Map Symbol Types
type ErrorLog = [TypeCheckErrors]

data TypeCheckErrors 
  = SymbolNotDefined Symbol SourcePos
  | NeedsLValue P.Expr SourcePos
  | TypeMismatch Types Types SourcePos
  | NonUnifiableTypes (P.Expr,Types,SourcePos) (P.Expr,Types,SourcePos)

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



class TypeCheck actx e where
  type TCC actx :: Types -> Type
  typeCheck :: forall {f} {ctx}.
    ( AssocActionTag actx ~ ctx
    , TCC actx ~ f
    ) => e -> TCM (Some f,TypeCheckEnv)

instance TypeCheck ActionTag P.Atom where
  type TCC ActionTag  = E ExprTag
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
    (MkSome @m @a a,env) <- typeCheck @ActionTag e
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
    _ <- typeCheck @ActionTag e
    tell [NeedsLValue e pos] >> empty
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


instance TypeCheck ActionTag P.Term where
  type TCC ActionTag  = E ExprTag

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
      

instance TypeCheck ActionTag P.Expr where


{- type Env m = TypeRepMap m ExprTag
instance TypeCheckE P.Expr where
  
  typeCheck (P.Minus a b) = do
    (MkSome @m @a a',_) <- typeCheck a
    (MkSome @_ @b b',_) <- typeCheck b

    undefined 
  typeCheck _ = undefined

instance TypeCheckE P.Term
instance TypeCheckE P.Atom -}
