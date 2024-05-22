{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module TypedMap where


import Data.Map (Map)
import qualified Data.Map as M
import GHC.Exts


import qualified ADT  as Z
import Unsafe.Coerce
import Type.Reflection 
import Control.Lens.Lens

import Lensy
import Debug.Trace

import Data.List.NonEmpty ( NonEmpty((:|)) )
import Data.Foldable1 (foldl1')
import ShowM
import Control.Concurrent hiding (yield)
import Control.Monad.IO.Class
import Control.Monad
import Control.Applicative hiding (yield)
-- Should have another version too:
-- Map Z.Symbol Any
-- so yield doesnt check for equality
-- not needed in GADT stage
newtype TypeRepMap = TypeRepMap (Map Z.Symbol (SomeTypeRep,MVar Any))

empty :: TypeRepMap
empty = TypeRepMap M.empty 

insert :: forall a m.  (Typeable a, MonadIO m) => Z.Symbol -> a -> TypeRepMap -> m TypeRepMap
insert var val (TypeRepMap m) = case M.lookup var m of
  Just (SomeTypeRep tr,mv) -> case eqTypeRep tr (typeRep @a) of 
    Just HRefl -> do
      liftIO $ tryTakeMVar mv >> putMVar mv (unsafeCoerce val)
      pure . TypeRepMap $ m
    Nothing -> error $ "Type mismatch for variable: " <> show var <> ", expected: " <> show (typeRep @a) <> " got: " <> show tr
  Nothing -> do
    mv <- liftIO $ newMVar (unsafeCoerce val)
    pure . TypeRepMap $ M.insert var (SomeTypeRep  $ typeRep @a,mv) m

insertFresh :: forall a m.  (Typeable a, MonadIO m) => Z.Symbol -> a -> TypeRepMap -> m TypeRepMap
insertFresh var val (TypeRepMap m) = do
    mv <- liftIO $ newMVar (unsafeCoerce val)
    pure . TypeRepMap $ M.insert var (SomeTypeRep  $ typeRep @a,mv) m

declare :: forall a m.  (Typeable a, MonadIO m) => Z.Symbol -> TypeRepMap -> m TypeRepMap
declare var (TypeRepMap m) = case M.lookup var m of
  Just _ -> error $ "Variable: " <> show var <> " already declared"
  Nothing -> do
    mv <- liftIO newEmptyMVar
    pure . TypeRepMap $ M.insert var (SomeTypeRep  $ typeRep @a,mv) m


yield :: forall a m. (Typeable a, MonadIO m)=> Z.Symbol -> TypeRepMap -> m a
yield var (TypeRepMap m) = 
  case M.lookup var m of
    Just (SomeTypeRep tr,mv) -> case eqTypeRep tr (typeRep @a) of
      -- Just HRefl -> unsafeCoerce <$> liftIO (readMVar mv )
      Just HRefl -> unsafeCoerce . maybe (error $ "Var " <> show var <> " not inizialited" ) id <$> liftIO (tryReadMVar  mv )
      
      Nothing -> error $ "Type mismatch for symbol: " <> show var <> ", expected: " <> show (typeRep @a) <> " got: " <> show tr
    Nothing -> error $ "Variable: " <> show var <> " not found"

{- instance IsString (Lens' TypeRepMap a) where
  fromString var = lens (yield var) (insert var)
 -}

instance (Typeable a,  MonadIO m, Typeable m) 
  => IsString (LensyM' m TypeRepMap a) where
  fromString var =  LensyM' (yield var) (flip $ insert var) (flip $ insertFresh var) var

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

instance MonadIO m => ShowM m  TypeRepMap where
  showM (TypeRepMap m) =  -- pure "env"
    pure . show . M.keys $ m 




