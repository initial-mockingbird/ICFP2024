{-# LANGUAGE ImportQualifiedPost        #-}
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
{-# LANGUAGE ImpredicativeTypes         #-}
module Zilly.Classic.Runner where

import Zilly.RValue
import Zilly.Types
import Zilly.Upcast
import Zilly.ADT.Expression
import Zilly.ADT.Action
import Zilly.Classic.Expression
import Zilly.Classic.Action
import Zilly.Classic.TypeCheck
import Zilly.Classic.Interpreter
import Utilities.ShowM
import Parser.Classic.ZillyParser qualified as P
import Control.Monad.Reader
import Text.Parsec

data Err 
    = PErr ParseError 
    | TCErr ErrorLog
    deriving Show

parseAndTypecheck :: FilePath -> IO (Either Err [A ActionTag '()])
parseAndTypecheck fp = P.parseFile' fp >>= \case
  Left e  -> pure $ Left (PErr e)
  Right as -> case typeCheckProgram' as of
    (Nothing,elog) -> pure $ Left (TCErr elog)
    (Just as',elog)  -> pure $ Right as'

parseAndTypecheck' :: FilePath -> IO ()
parseAndTypecheck' fp = parseAndTypecheck fp >>= \case
  Left e -> putStrLn $ show e
  Right as -> traverse showM as >>= putStrLn . unlines

