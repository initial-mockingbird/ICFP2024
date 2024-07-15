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
module TypedMap2 where


import Data.Map (Map)
import qualified Data.Map as M

import Unsafe.Coerce
import Type.Reflection 
import Control.Lens.Lens
import Lensy2
import Debug.Trace
import Data.List.NonEmpty ( NonEmpty((:|)) )
import Data.Foldable1 (foldl1')
import ShowM
import Control.Concurrent hiding (yield)
import Control.Monad.IO.Class
import Control.Monad
import Control.Applicative hiding (yield)
import ADT2 
import Prelude.Singletons hiding (Map,Any)
import Data.String (IsString(..))
import Data.Singletons.Decide 
import Control.Monad.Reader


data Any m where
  MkAny :: forall (a :: Types) m.  SingI a => MVar (E (TypeRepMap m) m a) -> Any m  

newtype TypeRepMap m = TypeRepMap (Map Symbol (Any m ))

empty :: TypeRepMap m 
empty = TypeRepMap M.empty 

insert :: forall a m.  (SingI a, MonadIO m) => Symbol -> E (TypeRepMap m) m a -> TypeRepMap m -> m (TypeRepMap m)
insert var val (TypeRepMap m) = case M.lookup var m of
  Just (MkAny @a' mv ) -> case decideEquality (sing @a') (sing @a)  of 
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

insertFresh :: forall a m . (SingI a, MonadIO m) => Symbol -> E (TypeRepMap m) m a -> TypeRepMap m -> m (TypeRepMap m )
insertFresh var val (TypeRepMap m) = do
    mv <- liftIO $ newMVar val
    pure . TypeRepMap $ M.insert var (MkAny mv) m

declare :: forall (a :: Types) m. (SingI a, MonadIO m) =>  Symbol -> TypeRepMap m -> m (TypeRepMap m)
declare  var (TypeRepMap m) = case M.lookup var m of
  Just _ -> error $ "Variable: " <> show var <> " already declared"
  Nothing -> do
    mv :: MVar (E (TypeRepMap m) m a) <- liftIO newEmptyMVar 
    !x <- pure . TypeRepMap $ M.insert var (MkAny mv) m

    pure x


yield :: forall (a :: Types) m env. (SingI a,  MonadIO m) => Symbol -> TypeRepMap m  -> m (E env m a)
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


instance forall (a :: Types) m. (SingI a, MonadIO m) 
  => IsString (LensyM' m (TypeRepMap m ) (E (TypeRepMap m ) m a)) where
  fromString var =  LensyM' (yield var) (flip $ insert var) (flip $ insertFresh var) var 

mkVar :: forall (a :: Types) m. 
  ( SingI a
  , MonadIO m
  ) => String -> LensyM' m (TypeRepMap m) (E (TypeRepMap m) m a)
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

instance MonadIO m => ShowM m  (TypeRepMap m ) where
  showM (TypeRepMap m) =  -- pure "env"
    pure . show . M.keys $ m 



