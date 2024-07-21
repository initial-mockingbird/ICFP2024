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
  , parserT2AdtT
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
import Control.Applicative hiding (Alternative(..),optional)

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

-------------------------------
-- Useful functions
-------------------------------


flip2 f x3 = \x1 x2 -> f x1 x2 x3


flip3 f x4 = \x1 x2 x3 -> f x1 x2 x3 x4

-----------------------------------------
-- Expression Grammar / Untyped AST
-----------------------------------------

data Expr
  = Minus Expr Term SourcePos
  | Less Expr Term  SourcePos
  | OfTerm Term     
  deriving (Show,Eq)

data Term
  = App Term Expr SourcePos
  | OfAtom Atom   
  deriving (Show,Eq)

data Atom
  = Val Int      SourcePos
  | Var Symbol   SourcePos
  | Parens  Expr SourcePos
  | Defer   Expr SourcePos
  | Formula Expr SourcePos
  | IfThenElse Expr Expr Expr SourcePos
  | Lambda Symbol Types Expr  SourcePos
  deriving (Show,Eq)

data Types
  = Arrow Types0 Types SourcePos
  | OfTypes0 Types0    
  deriving (Show, Eq)

data Types0 
  = Z           SourcePos
  | Lazy Types  SourcePos
  | LazyS Types SourcePos
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
  = Z <$> getPosition <*  (token (string "Int") <|> token (string "Z"))
  <|> flip Lazy  <$> getPosition <*> (token (string "Lazy")  *> bracketed pType) 
  <|> flip LazyS <$> getPosition <*> (token (string "Lazy*") *> bracketed pType)

pType :: Parser Types
pType = precedence $ 
  sops InfixR [flip2 Arrow <$> getPosition <* token (string "->")] |-<
  Atom pType0



-----------------------------------------
-- Expression Parsers
-----------------------------------------

ident :: Parser Symbol
ident 
  =  notFollowedBy anyKeyword *> mzero
  <|> lexeme (f <$> letter <*> many (letter <|> digit <|> char '_'))
  where f c cs = c:cs

mkVal :: Parser Int -> Parser Atom
mkVal p = getPosition <**> (Val <$> p)

mkParens :: Parser Expr -> Parser Atom
mkParens p = getPosition <**> (Parens <$> parens p)

mkIfThenElse :: Parser Expr -> Parser Expr -> Parser Expr -> Parser Atom
mkIfThenElse p1 p2 p3 = getPosition <**> 
  (IfThenElse <$> (keyword "if" *> p1 <* keyword "then") <*> p2 <* keyword "else" <*> p3)

mkFormula :: Parser Expr -> Parser Atom
mkFormula p = getPosition <**> (Formula <$> (keyword "formula" *> parens p))

mkLambda :: Parser Symbol -> Parser Types -> Parser Expr -> Parser Atom
mkLambda p1 p2 p3 = getPosition <**> 
  ( Lambda 
  <$> (token (string "/.") *> p1) 
  <*> (token (string ":") *> p2) 
  <*> (token (string "=>") *> p3)
  )

mkVar :: Parser Symbol -> Parser Atom
mkVar p = getPosition <**> (Var <$> p)

mkDefer :: Parser Expr -> Parser Atom
mkDefer p = getPosition <**> (Defer <$> quoted p)



atom :: Parser Atom
atom 
  =   mkVal number  
  <|> mkParens expr
  <|> mkIfThenElse expr expr expr
  <|> mkFormula expr
  <|> mkLambda ident pType expr
  <|> mkVar ident
  <|> mkDefer expr

    
{- mkMinus :: Parser Expr -> Parser Term -> Parser Expr
mkMinus p t = getPosition <**> 
  (Minus <$> p <* lexeme (char '-') <*> t) -}




mkMinus :: Parser (Expr-> Term -> Expr)
mkMinus = (\p x y -> Minus x y p) <$> getPosition

mkLess :: Parser (Expr-> Term -> Expr)
mkLess = (\p x y -> Less x y p) <$> getPosition

mkApp :: Parser Expr -> Parser (Term -> Term)
mkApp p = (\p x y -> App y x p) <$> getPosition <*> parens p

expr :: Parser Expr
expr = precedence $
  sops InfixL [mkMinus , mkLess] |-<
  --sops Postfix [flip App <$> parens atom] |-<
  sops Postfix [mkApp expr] |-<
  Atom atom


-----------------------------------------
-- Action Grammar
-----------------------------------------

data A1
  = Seq A1 A0
  | OfA0 A0
  deriving (Show,Eq)

data A0
  = Decl Types Symbol Expr SourcePos
  | Assign Symbol Expr     SourcePos
  | Print Expr             SourcePos
  deriving (Show,Eq)

instance A0 < A1 where
  upcast = OfA0


mkPrint :: Parser Expr -> Parser A0
mkPrint arg = getPosition <**> (Print <$> (keyword "print" *> parens arg))

mkDecl :: Parser Types -> Parser Symbol -> Parser Expr -> Parser A0
mkDecl pType ident expr = getPosition <**> (Decl <$> pType <*> ident <* token (string ":=") <*> expr)

mkAssign :: Parser Symbol -> Parser Expr -> Parser A0
mkAssign ident expr = getPosition <**> (Assign <$> ident <* token (string ":=") <*> expr)

a0 :: Parser A0
a0 
  =   mkPrint expr
  <|> mkDecl pType ident expr
  <|> mkAssign ident expr


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
  OfTypes0 (Z _)       -> ZT.Value ZT.Z
  OfTypes0 (Lazy t _)  -> ZT.Lazy (parserT2AdtT t)
  OfTypes0 (LazyS t _) -> ZT.LazyS (parserT2AdtT t)
  Arrow t1 t2 _ -> ZT.Value (parserT2AdtT (OfTypes0 t1) ZT.:-> parserT2AdtT t2)
   
-----------------------------------------
-- Run parser
-----------------------------------------

parseAction :: Symbol -> Either ParseError A0
parseAction = parse (fully action) ""

parseFile :: FilePath -> IO (Either ParseError [A0])
parseFile = fmap (traverse parseAction . lines) . readFile


parseExpr :: Symbol -> Either ParseError Expr
parseExpr = parse (fully expr) ""