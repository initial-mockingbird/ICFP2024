{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}


{-|
Module      : Parser.Classic.ZillyPlusParser
Description : A Parser for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX
-}
module Parser.ClassicPlus.ZillyPlusParser
  ( 
  ) where

import Parser.Utilities
import Parser.ParserZ (deserializePacket,Packet',Payload'(..))

import Text.Parsec hiding (token)
import Text.Parsec.String

import Data.String (IsString(..))
import Control.Monad

import Data.Functor.Identity
import Control.Applicative hiding (Alternative(..),optional)
import Data.Coerce
import GHC.TypeLits.Singletons
import Data.Kind (Type)

keywords :: [String]
keywords =
  [ "ifx"
  , "Lazy"
  , "int"
  , "formula"
  , "feval"
  , "Lazy*"
  , "print"
  , "Z"
  , "bool"
  , "boolean"
  , "double"
  , "float"
  , "random"
  ]


-------------------------------
-- Useful Orphans
-------------------------------

instance u ~ () => IsString (Parser u ) where
  fromString str
    | str `elem` keywords = keyword str
    | otherwise           = void $ token (string str)


-------------------------------
-- Main combinators
-------------------------------

anyKeyword :: Parser ()
anyKeyword = choice $ fmap keyword keywords

-------------------------------
-- Useful functions
-------------------------------

flip2 :: (t1 -> t2 -> t3 -> t4) -> (t3 -> t1 -> t2 -> t4)
flip2 f x3 x1 x2 = f x1 x2 x3

-----------------------------------------
-- Expression Grammar / Untyped AST
-----------------------------------------

type family Precedence (x :: Type) :: Natural where
  




-----------------------------------------
-- Type Parsers
-----------------------------------------




-----------------------------------------
-- Expression Parsers
-----------------------------------------



-----------------------------------------
-- Action Grammar
-----------------------------------------


-----------------------------------------
-- File Parsing
-----------------------------------------



-----------------------------------------
-- Type Mapping
-----------------------------------------


 

-----------------------------------------
-- Run parser
-----------------------------------------


-----------------------------------------
-- Show instances
-----------------------------------------

-----------------------------------------
-- Eq instances
-----------------------------------------

