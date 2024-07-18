

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

module Zilly.Typecheck where


import Parser.ZillyParser qualified as P
import Utilities.LensM
import Utilities.TypedMap
import Utilities.ShowM
import Zilly.ADT
import Zilly.Action
import Zilly.Expressions
import Zilly.Interpreter hiding (Env)
import Zilly.RValue
import Zilly.Types
import Control.Monad.Reader


import Data.Kind (Type)
import Data.Singletons
import Control.Monad.IO.Class (MonadIO)
import Control.Applicative (Alternative)

data Some m = forall a. SingI a => MkSome (E ExprTag (TypeRepMap m ExprTag) m a)

class TypeCheckE e where
  typeCheck :: 
    (MonadIO m
    , MonadReader (TypeRepMap m ExprTag) m
    , Alternative m
    , ShowM m (TypeRepMap m ExprTag)
    ) => e -> m (Some m,TypeRepMap m ExprTag)


type Env m = TypeRepMap m ExprTag
instance TypeCheckE P.Expr where
  
  typeCheck (P.Minus a b) = do
    (MkSome @m @a a',_) <- typeCheck a
    (MkSome @_ @b b',_) <- typeCheck b
    _ <- withSingIRType @a @(E ExprTag (Env m) m) 
      $ withSingI (SValue SZ)
      $ case (upcastable @(RValueT (E ExprTag (Env m) m) a) @(Value Z) @(Env m) @m, upcastable @(RValueT (E ExprTag (Env m) m) b) @(Value Z) @(Env m) @m) of
      (NonExistentUB,_) -> error "type mismatch"
      _ -> undefined

    undefined 
  typeCheck _ = undefined

instance TypeCheckE P.Term
instance TypeCheckE P.Atom
