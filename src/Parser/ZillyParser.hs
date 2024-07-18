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

{-|
Module      : Parser.ZillyParser
Description : A Parser for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX
-}
module Parser.ZillyParser
  ( Expr (..)
  , Term (..)
  , Atom (..)
  , A1 (..)
  , A0 (..)
  , parseAction
  , parseFile
  , parseExpr
  ) where

import Parser.Utilities
import Zilly.Types qualified as ZT
import Zilly.Types (Symbol )
--import Zilly.ADT
import Text.Parsec hiding (token)
import Text.Parsec.String

import Data.String (IsString(..))
import Control.Monad

import Data.Functor.Identity


keywords :: [Symbol]
keywords = 
  [ "if"
  , "then"
  , "else"
  , "Lazy"
  , "Int"
  , "formula"
  , "feval"
  , "Lazy*"
  , "print"
  , "Z"
  ]


-------------------------------
-- Useful Orphans
-------------------------------

instance IsString (Parser () ) where
  fromString str
    | str `elem` keywords = keyword str
    | otherwise           = void $ token (string str)


-------------------------------
-- Main combinators
-------------------------------

anyKeyword :: Parser ()
anyKeyword = choice $ map keyword keywords

-----------------------------------------
-- Expression Grammar / Untyped AST
-----------------------------------------

data Expr
  = Minus Expr Term 
  | Less Expr Term
  | OfTerm Term
  deriving (Show,Eq)

data Term
  = App Term Expr
  | OfAtom Atom
  deriving (Show,Eq)

data Atom
  = Val Int 
  | Var Symbol
  | Parens Expr
  | Defer Expr 
  | IfThenElse Expr Expr Expr
  | Formula Expr
  | Lambda Symbol Types Expr
  deriving (Show,Eq)

data Types
  = Arrow Types0 Types
  | OfTypes0 Types0
  deriving (Show, Eq)

data Types0 
  = Z
  | Lazy Types
  | LazyS Types
  deriving (Show, Eq)

instance Atom < Term where
  upcast = OfAtom

instance Term < Expr where
  upcast = OfTerm

instance Types0 < Types where
  upcast = OfTypes0


-----------------------------------------
-- Type Parsers
-----------------------------------------

    
pType0 :: Parser Types0
pType0 
  = Z <$ token (string "Int")
  <|> Lazy  <$> (token (string "Lazy")  *> bracketed pType) 
  <|> LazyS <$> (token (string "Lazy*") *> bracketed pType)

pType :: Parser Types
pType = precedence $ 
  sops InfixR [Arrow <$ token (string "->")] |-<
  Atom pType0



-----------------------------------------
-- Expression Parsers
-----------------------------------------

ident :: Parser Symbol
ident 
  =  notFollowedBy anyKeyword *> mzero
  <|> lexeme (f <$> letter <*> many (letter <|> digit <|> char '_'))
  where f c cs = c:cs


atom :: Parser Atom
atom 
  =   Val    <$> number  
  <|> Parens <$> parens expr
  <|> IfThenElse <$ keyword "if" <*> expr <* keyword "then" <*> expr <* keyword "else" <*> expr
  <|> Formula <$> (keyword "formula" *> expr)
  <|> Lambda <$> (token (string "/.") *> ident) <*> (token (string ":") *> pType) <*> (token (string "=>") *> expr)
  <|> Var <$> ident
  <|> Defer  <$> quoted expr


expr :: Parser Expr
expr = precedence $
  sops InfixL [Minus <$ lexeme (char '-'), Less <$ lexeme (char '<')] |-<
  --sops Postfix [flip App <$> parens atom] |-<
  sops Postfix [flip App <$> parens expr] |-<
  Atom atom


-----------------------------------------
-- Action Grammar
-----------------------------------------

data A1
  = Seq A1 A0
  | OfA0 A0
  deriving (Show,Eq)

data A0
  = Decl Types Symbol Expr
  | Assign Symbol Expr
  | Print Expr
  deriving (Show,Eq)

instance A0 < A1 where
  upcast = OfA0


a0 :: Parser A0
a0 
  =   Print <$> (keyword "print" *> expr)
  <|> Decl <$> pType <*> ident <* token (string ":=") <*> expr
  <|> Assign <$> ident <* token (string ":=") <*> expr


action :: ParsecT Symbol () Identity A0 
action =  a0 <* optional (lexeme (string ";"))

-----------------------------------------
-- File Parsing
-----------------------------------------

skipLines :: ParsecT Symbol () Identity ()
skipLines = void $ many (void endOfLine <|> spaces)

skipComments :: ParsecT Symbol () Identity ()
skipComments = void $ token (string "--") *> space *> manyTill anyChar (eot <|> void endOfLine) 

skipLinesAndComments :: ParsecT Symbol () Identity ()
skipLinesAndComments = void $ many (skipLines <|> skipComments)

eot :: ParsecT Symbol () Identity ()
eot  = void (char '\EOT') <?> "end of packet"

actions :: ParsecT Symbol () Identity [A0]
actions = manyTill (action <* skipLinesAndComments) (eot <|> eof)

-----------------------------------------
-- Type Mapping
-----------------------------------------


parserT2AdtT :: Types -> ZT.Types
parserT2AdtT = \case
  OfTypes0 Z         -> ZT.Value ZT.Z
  OfTypes0 (Lazy t)  -> ZT.Lazy (parserT2AdtT t)
  OfTypes0 (LazyS t) -> ZT.LazyS (parserT2AdtT t)
  Arrow t1 t2 -> ZT.Value (parserT2AdtT (OfTypes0 t1) ZT.:-> parserT2AdtT t2)
  
-----------------------------------------
-- Run parser
-----------------------------------------

parseAction :: Symbol -> Either ParseError A0
parseAction = parse (fully action) ""

parseFile :: FilePath -> IO (Either ParseError [A0])
parseFile = fmap (traverse parseAction . lines) . readFile


parseExpr :: Symbol -> Either ParseError Expr
parseExpr = parse (fully expr) ""