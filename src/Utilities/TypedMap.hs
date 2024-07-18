{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BangPatterns #-}
module Utilities.TypedMap where


import Data.Map (Map)
import qualified Data.Map as M

import Unsafe.Coerce
import Type.Reflection 
import Control.Lens.Lens
import Utilities.LensM
import Utilities.ShowM
import Zilly.ADT 
import Zilly.Types

import Debug.Trace
import Data.List.NonEmpty ( NonEmpty((:|)) )
import Data.Foldable1 (foldl1')
import Control.Concurrent hiding (yield)
import Control.Monad.IO.Class
import Control.Monad
import Control.Applicative hiding (yield)
import Prelude.Singletons hiding (Map,Any,Symbol)
import Data.String (IsString(..))
import Data.Singletons.Decide 
import Control.Monad.Reader


data Any m ctx where
  MkAny :: forall (a :: Types) m ctx.  SingI a => MVar (E ctx (TypeRepMap m ctx) m a) -> Any m ctx 

newtype TypeRepMap m ctx= TypeRepMap (Map Symbol (Any m ctx))

empty :: TypeRepMap m ctx
empty = TypeRepMap M.empty 

insert :: forall a m ctx.  (SingI a, MonadIO m) => Symbol -> E ctx (TypeRepMap m ctx) m a -> TypeRepMap m ctx -> m (TypeRepMap m ctx)
insert var val (TypeRepMap m) = case M.lookup var m of
  Just (MkAny @a' @_ mv ) -> case decideEquality (sing @a') (sing @a) of 
    Just Refl -> do
      liftIO $ tryTakeMVar mv >> putMVar mv val
      pure . TypeRepMap $ m
    Nothing -> error 
      $ "Type mismatch for variable: " 
      <> show var <> ", expected: " 
      <> show (fromSing $ sing @a) 
      <> " got: " 
      <> show (fromSing $ sing @a') 
  Nothing -> do
    mv  <- liftIO $ newMVar val
    pure . TypeRepMap $ M.insert var (MkAny @a mv) m

insertFresh :: forall a m ctx. (SingI a, MonadIO m) => Symbol -> E ctx (TypeRepMap m ctx) m a -> TypeRepMap m ctx -> m (TypeRepMap m ctx )
insertFresh var val (TypeRepMap m) = do
    mv <- liftIO $ newMVar val
    pure . TypeRepMap $ M.insert var (MkAny mv) m

declare :: forall (a :: Types) m ctx. (SingI a, MonadIO m) =>  Symbol -> TypeRepMap m ctx -> m (TypeRepMap m ctx)
declare  var (TypeRepMap m) = case M.lookup var m of
  Just _ -> error $ "Variable: " <> show var <> " already declared"
  Nothing -> do
    mv :: MVar (E ctx (TypeRepMap m ctx) m a) <- liftIO newEmptyMVar 
    !x <- pure . TypeRepMap $ M.insert var (MkAny mv) m

    pure x


yield :: forall (a :: Types) m env ctx. (SingI a,  MonadIO m) => Symbol -> TypeRepMap m ctx  -> m (E ctx env m a)
yield var (TypeRepMap m) = 
  case M.lookup var m of
    Just (MkAny @a' mv ) -> case decideEquality (sing @a') (sing @a)  of
      Just Refl -> unsafeCoerce . maybe (error $ "Var " <> show var <> " not inizialited" ) id <$> liftIO (tryReadMVar  mv )
      Nothing -> error 
        $ "Type mismatch for symbol: " 
        <> show var <> ", expected: " 
        <> show (fromSing $ sing @a) 
        <> " got: " 
        <> show (fromSing $ sing @a') 
    Nothing -> error $ "Variable: " <> show var <> " not found"


instance forall (a :: Types) m ctx. (SingI a, MonadIO m) 
  => IsString (LensM m (TypeRepMap m ctx) (E ctx (TypeRepMap m ctx) m a)) where
  fromString var =  LensM (yield var) (flip $ insert var) (flip $ insertFresh var) var 

mkVar :: forall (a :: Types) m ctx. 
  ( SingI a
  , MonadIO m
  ) => String -> LensM m (TypeRepMap m ctx) (E ctx (TypeRepMap m ctx) m a)
mkVar = fromString

--IsString (LensyM' m TypeRepMap (m a))
--IsString (LensyM' m TypeRepMap (E TypeRepMap m (Value Int)))


{- instance {-# OVERLAPPABLE #-} (Typeable a, Typeable m, MonadIO m) 
  => IsString (Lensy TypeRepMap (m a)) where
  fromString var = Lensy { getLens = lens (yield var) (flip $ insert var), varName = var } -}


{- 
instance MonadIO m => ShowM m  TypeRepMap where
  showM (TypeRepMap m) =  do
    m' <-  (fmap . fmap) (\(a,(b,_)) -> a <> " -> " <> show b ) 
      . liftIO . (traverse . traverse . traverse) (fmap (maybe undefined id) .  tryReadMVar) . filter (\(a,_) -> a /= "sum") .  M.toList $ m
    let s = case  m' of
          (x:xs) -> foldl1' (\a b -> a <> ", " <> b) $ x :| xs
          [] -> ""
    
    pure $ "{ " <> s <> " }" -}

instance MonadIO m => ShowM m  (TypeRepMap m ctx) where
  showM (TypeRepMap m) =  -- pure "env"
    pure . show . M.keys $ m 



