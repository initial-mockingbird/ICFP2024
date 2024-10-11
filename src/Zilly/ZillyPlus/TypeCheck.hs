
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
{-# LANGUAGE ImportQualifiedPost        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeAbstractions           #-}

module Zilly.ZillyPlus.TypeCheck where


import Parser.ClassicPlus.ZillyPlusParser qualified as P
import Utilities.LensM
import Utilities.TypedMapPlus hiding (empty)
import Utilities.ShowM
import Zilly.ADT.ExpressionPlus
import Zilly.ADT.ActionPlus
import Zilly.ZillyPlus.Expression
import Zilly.ADT.Error 
import Zilly.ZillyPlus.Error 
import Zilly.ADT.Array 
import Zilly.ZillyPlus.Array  
import Zilly.ADT.Arithmetic 
import Zilly.ZillyPlus.Arithmetic
import Zilly.ZillyPlus.Tower
import Zilly.ZillyPlus.Interpreter hiding (Env)
import Zilly.RValuePlus
import Zilly.Types
import Zilly.UpcastPlus
import Control.Monad.Reader
import Data.Proof

import Data.Kind (Type)
import Data.Singletons
import Control.Monad.IO.Class (MonadIO)
import Control.Applicative (Alternative(..))
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Writer.CPS
import Control.Monad.Error.Class
import Control.Monad.Trans.Maybe
import Parser.ClassicPlus.ZillyPlusParser qualified as P
import Control.Monad (MonadPlus(mzero))
import Text.Parsec (SourcePos)
import Data.Singletons.Decide
import Data.Traversable


type Some :: forall k. (k -> Type) -> Type 
data Some (f :: k -> Type) where
    MkSome :: forall {k} f (a :: k). SingI a => f a -> Some f

type TypeCheckEnv = Map Symbol Types
type ErrorLog = [TypeCheckErrors]

newtype ExpectedType = ExpectedType Types deriving newtype Show
newtype GotType      = GotType      Types deriving newtype Show

data TypeCheckErrors 
  = SymbolNotDefined Symbol SourcePos
  | FormulaNeedsLValue P.Expr SourcePos
  | TypeMismatch ExpectedType GotType SourcePos
  | NonUnifiableTypes (Types,SourcePos) (Types,SourcePos)
  | ArgNotSubtype    (Types,SourcePos) Types
  | ArgIsNotStrictSubtype   (Types,SourcePos) Types
  | AppNotAFun Types SourcePos
  | RHSNotSubtype    (Types,SourcePos) Types
  | RHSIsNotStrictSubtype   (Types,SourcePos) Types

instance Show TypeCheckErrors where
  show (SymbolNotDefined s pos) = "Symbol " <> show s <> " not defined " <> show pos
  -- show (FormulaNeedsLValue e pos) = "Needs lvalue " <> show e <> " " <> show pos 
  show (TypeMismatch t1 t2 pos) = "Type mismatch " <> show pos
  show (NonUnifiableTypes (t1,pos1) (t2,pos2) ) 
    = "Non unifiable types:\n" 
      <> show t1 <> "(" <> show pos1 <> ")\n" 
      <> show t2 <> "(" <> show pos2 <> ")\n" 
  show (ArgNotSubtype (t,s) expected) 
    = "Value passed as argument is not a subtype of the argument.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s
  show (ArgIsNotStrictSubtype (t,s) expected) 
    = "Value passed as argument is not a strict subtype of the argument.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s
  show (AppNotAFun t s) 
    = "Left argument of function application is not a function. Expected type: " <> show t <> " " <> show s
  show (RHSNotSubtype (t,s) expected) 
    = "Right hand side of assignment is not a subtype of the left hand side.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s
  show (RHSIsNotStrictSubtype (t,s) expected) 
    = "Right hand side of assignment is not a strict subtype of the left hand side.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s


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

data TcGen  = TcGen
  { tcGenEnv :: TypeCheckEnv
  , tcGenPos :: SourcePos
  }


class TypeCheck actx e ret | e -> ret where
  type TCC actx ret :: ret -> Type
  type TCReturn actx e :: Type 
  typeCheck :: forall {f} .
    ( TCC actx ret ~ f
    ) => e -> TCM (Some f,TCReturn actx e)

instance TypeCheck ActionTag (P.EPrec P.Atom) Types where 
  type TCC ActionTag Types = ET 
  type TCReturn ActionTag  (P.EPrec P.Atom) = TcGen

  typeCheck (P.PInt p n) = ask >>= \env -> pure 
    ( MkSome . ETower 
      $ Val  
        @ErrorT  
        @ExprTag 
        @(Value Z)
        ( Dict
        , n
        , Dict
        )
    , TcGen env (P.tokenPos p) 
    )

  typeCheck (P.PDouble p n) = ask >>= \env -> pure 
    ( MkSome . ETower 
      $ Val  
        @ErrorT  
        @ExprTag 
        @(Value F)
        ( Dict
        , n
        , Dict
        )
    , TcGen env (P.tokenPos p)
    )

  typeCheck (P.PVar p s) =  do
    env <- ask
    case M.lookup s env of
      Just t -> case toSing  t of
        SomeSing @_ @t st -> withSingI st 
          $ pure (MkSome . ETower $ VarE (mkVar @t @ExprTag s) ,TcGen env (P.tokenPos p))
      Nothing -> 
        tell [SymbolNotDefined s (P.tokenPos p)] >> empty
  
  typeCheck (P.PArray _ s) = undefined 

  typeCheck (P.PParen _ e) = typeCheck @ActionTag e

  typeCheck (P.PDefer _ n) = undefined 

  typeCheck (P.PLambda _ args t body) = undefined

  typeCheck (P.PUniform _) = error "uniform not yet implemented"

  typeCheck (P.PFormula _ e) = undefined 

  typeCheck (P.PIf _ (cond,a,b)) = undefined

  typeCheck (P.PBool _ n) = error "Bool not yet defined"

instance TypeCheck ActionTag (P.EPrec P.PrefixPrec) Types where 
  type TCC ActionTag Types = ET 
  type TCReturn ActionTag  (P.EPrec P.PrefixPrec) = TcGen

instance TypeCheck ActionTag (P.EPrec P.PostfixPrec) Types where 
  type TCC ActionTag Types = ET 
  type TCReturn ActionTag  (P.EPrec P.PostfixPrec) = TcGen

instance TypeCheck ActionTag (P.EPrec 8) Types where 
  type TCC ActionTag Types = ET 
  type TCReturn ActionTag  (P.EPrec 8) = TcGen


instance TypeCheck ActionTag (P.EPrec 7) Types where 
  type TCC ActionTag Types = ET 
  type TCReturn ActionTag  (P.EPrec 7) = TcGen


instance TypeCheck ActionTag (P.EPrec 6) Types where 
  type TCC ActionTag Types = ET 
  type TCReturn ActionTag  (P.EPrec 6) = TcGen


instance TypeCheck ActionTag (P.EPrec 4) Types where 
  type TCC ActionTag Types = ET 
  type TCReturn ActionTag  (P.EPrec 4) = TcGen
