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
import Utilities.TypedMap
import Utilities.Codes
import Parser.Classic.ZillyParser qualified as P
import Parser.ParserZ
import Control.Monad.Reader
import Text.Parsec
import Data.Functor.Identity
data Err 
    = PErr ParseError 
    | TCErr ErrorLog

instance Show Err where
  show (PErr e)  = "Parser Error!\n" <> show e
  show (TCErr e) = "Typing Error!\n" <> concatMap (\x -> show x <> "\n\n") e

parseAndTypecheck :: FilePath -> IO (Either Err [A ActionTag '()])
parseAndTypecheck fp = P.parseFile' fp >>= \case
  Left e  -> pure $ Left (PErr e)
  Right as -> case typeCheckProgram' as of
    (Nothing,elog) -> pure $ Left (TCErr elog)
    (Just as',[])  -> pure $ Right as'
    (_,elog)       -> pure $ Left (TCErr elog)

parseAndTypecheck' :: FilePath -> IO ()
parseAndTypecheck' fp = parseAndTypecheck fp >>= \case
  Left e -> putStrLn $ show e
  Right as -> traverse showM as >>= putStrLn . unlines

parseAndRun :: FilePath -> IO (Either Err [A ActionTag '()])
parseAndRun fp = parseAndTypecheck fp >>= \case
  e@(Left _)  -> pure  e
  Right as -> Right . snd <$> runReaderT (runTI  (execProgram as )) empty


parseAndRun' :: FilePath -> IO ()
parseAndRun' fp = parseAndRun fp >>= \case
  Left e -> putStrLn $ show e
  Right as -> traverse showM as >>= putStrLn . unlines

parseAndResponse :: Monad m => Symbol -> IO [Some (ServerResponse m)]
parseAndResponse s =  case P.parsePacket s of
  (Left e) -> pure [MkSome $ ERRORR $ show  (PErr e)]
  (Right (Packet c s t (Payload p) eot)) -> case typeCheckProgram' p of
    (_,elog@(_:_)) -> pure [MkSome $ ERRORR $ show (TCErr elog)]
    (Nothing,elog) -> pure [MkSome $ ERRORR $ show (TCErr elog)]
    (Just as,_)  -> do
      (env',as') <- runReaderT (runTI  (execProgram as )) empty
      pure $ MkSome . ACKR <$> as'

parseAndResponse' :: Symbol -> IO [Symbol]
parseAndResponse' s = do
  rs <- parseAndResponse @Identity s
  let 
    f :: [Some (ServerResponse Identity)] -> [String]
    f = \case
        [] -> []
        (MkSome (ACKR a):s) -> runIdentity (showM a) : f s
        (MkSome (ERRORR e):s) -> e : f s
  pure $ f rs 
    


