{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}

{-|
Module      : Parser
Description : A Parser for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

A Parser for Zilly
-}
module Parser 
  ( Type (..)
  , Type0 (..)
  , Expr (..)
  , Term (..)
  , Atom (..)
  , A1 (..)
  , A0 (..)
  , Phantom(..)
  , NoVarInfo
  , VarInfo
  , parseAction
  , parseFile
  , parseExpr
  ) where



import Text.Parsec hiding (token)
import Text.Parsec.String
import Text.Parsec.Combinator
import Data.String (IsString(..))
import Control.Monad
import Control.Applicative ((<**>))
import Data.Functor.Const

import Data.Functor
import Data.Functor.Identity


keywords :: [String]
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
  ]


-------------------------------
-- Useful Orphans
-------------------------------

instance IsString (Parser () ) where
  fromString str
    | str `elem` keywords = keyword str
    | otherwise           = void $ token (string str)

-------------------------------
-- Useful Types
-------------------------------

data Phantom (a :: k) = Phantom

type NoVarInfo = Const ()
--type VarInfo   = Phantom 
type VarInfo   = Identity

noVarInfo :: NoVarInfo b
noVarInfo = Const ()

mkNoVarInfo :: String -> Atom NoVarInfo
mkNoVarInfo = flip Var noVarInfo

mkVarInfoA :: String -> Expr NoVarInfo -> A0 NoVarInfo
mkVarInfoA = flip Assign noVarInfo

-------------------------------
-- Main combinators
-------------------------------

lexeme :: Parser a -> Parser a
lexeme p = p <* spaces

fully :: Parser a -> Parser a
fully p = spaces *> p <* eof

token :: Parser a -> Parser a
token = lexeme . try

keyword :: String -> Parser ()
keyword k = token (string k *> notFollowedBy alphaNum)

anyKeyword :: Parser ()
anyKeyword = choice $ map keyword keywords

infixl1 :: (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
infixl1 wrap p op = (wrap <$> p) <**> rest
  where rest = flip (.) <$> (flip <$> op <*> p) <*> rest <|> pure id

infixr1 :: (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
infixr1 wrap p op =
  p <**> (flip <$> op <*> infixr1 wrap p op <|> pure wrap)

postfix :: (a -> b) -> Parser a -> Parser (b -> b) -> Parser b
postfix wrap p op = (wrap <$> p) <**> rest
  where rest = flip (.) <$> op <*> rest <|> pure id

prefix :: (a -> b) -> Parser (b -> b) -> Parser a -> Parser b
prefix wrap op p = op <*> prefix wrap op p <|> wrap <$> p

parens :: Parser a -> Parser a
parens = lexeme . between (token $ string "(") (token $ string ")")
    
quoted :: Parser a -> Parser a
quoted = lexeme . between (token $ string "'") (token $ string "'")

bracketed :: Parser a -> Parser a
bracketed = lexeme . between (char '<') (char '>')

---------------------------------------------
-- Fixity, Associativity and Precedence
---------------------------------------------

data Fixity a b sig where
  InfixL  :: Fixity a b (b -> a -> b) 
  InfixR  :: Fixity a b (a -> b -> b) 
  InfixN  :: Fixity a b (a -> a -> b) 
  Prefix  :: Fixity a b (b -> b) 
  Postfix :: Fixity a b (b -> b)

data Op a b where
  Op :: Fixity a b sig -> (a -> b) -> Parser sig -> Op a b

data Prec a where
  Level :: Prec a   -> Op a b -> Prec b
  Atom  :: Parser a -> Prec a

infixl 5 >-|
infixr 5 |-<
(>-|) :: Prec a -> Op a b -> Prec b
(>-|) = Level 

(|-<) :: Op a b -> Prec a -> Prec b
(|-<) = flip (>-|)

class sub < sup where
  upcast :: sub -> sup
  --downcast :: sup -> Maybe sub

-----------------------------------------
-- Precedence and Associativity
-----------------------------------------

precedence :: Prec a -> Parser a
precedence (Atom atom') = atom'
precedence (Level lvls ops') = con (precedence lvls) ops'
  where 
    con :: Parser a -> Op a b -> Parser b
    con p (Op InfixL wrap op)  = infixl1 wrap p op
    con p (Op InfixR wrap op)  = infixr1 wrap p op
    con p (Op InfixN wrap op)  = p <**> (flip <$> op <*> p <|> pure wrap)
    con p (Op Prefix wrap op)  = prefix wrap op p
    con p (Op Postfix wrap op) = postfix wrap p op

precHomo :: Parser a -> [Op a a] -> Parser a
precHomo atom' = precedence . foldl (>-|) (Atom atom')


gops :: Fixity a b sig -> (a -> b) -> [Parser sig] -> Op a b
gops fixity wrap = Op fixity wrap . choice

ops :: Fixity a a sig -> [Parser sig] -> Op a a
ops fixity = gops fixity id

sops :: a < b => Fixity a b sig -> [Parser sig] -> Op a b
sops fixity = gops fixity upcast

-----------------------------------------
-- Expression Grammar / Untyped AST
-----------------------------------------

data Type 
  = Arrow Type0 Type
  | OfType0 Type0
  deriving (Show, Eq)

data Type0 
  = Int' 
  | Lazy Type
  | LazyS Type
  deriving (Show, Eq)

data Expr t
  = Minus (Expr t) (Term t) 
  | Less (Expr t) (Term t)
  | OfTerm (Term t)
deriving instance Show (t Type) => Show (Expr t)
deriving instance Eq (t Type) => Eq (Expr t)

data Term t
  -- = App (Term t) (Atom t)
  = App (Term t) (Expr t)
  | OfAtom (Atom t)
deriving instance Show (t Type) => Show (Term t)
deriving instance Eq (t Type) => Eq (Term t)

data Atom t
  = Val Int 
  | Var String (t Type)
  | Parens (Expr t) 
  | Defer (Expr t)
  | IfThenElse (Expr t) (Expr t) (Expr t)
  | Formula (Expr t)
  | Lambda String Type (Expr t)
deriving instance Show (t Type) => Show (Atom t)
deriving instance Eq (t Type) => Eq (Atom t)
  

instance Atom t < Term t where
  upcast = OfAtom

instance Term t < Expr t where
  upcast = OfTerm

instance Type0 < Type where
  upcast = OfType0


-----------------------------------------
-- Type Parsers
-----------------------------------------

    
pType0 :: Parser Type0
pType0 
  = Int' <$ token (string "Int")
  <|> Lazy  <$> (token (string "Lazy")  *> bracketed pType) 
  <|> LazyS <$> (token (string "Lazy*") *> bracketed pType)

pType :: Parser Type
pType = precedence $ 
  sops InfixR [Arrow <$ token (string "->")] |-<
  Atom pType0

-----------------------------------------
-- Expression Parsers
-----------------------------------------

number :: Parser Int
number = f <$> option "" (token $ string "-" ) <*> lexeme (many1 digit)
  where f "-" ds = read ('-':ds)
        f _   ds = read ds

ident :: Parser String
ident 
  =  notFollowedBy anyKeyword *> mzero
  <|> lexeme (f <$> letter <*> many (letter <|> digit <|> char '_'))
  where f c cs = c:cs


atom :: Parser (Atom NoVarInfo)
atom 
  =   Val    <$> number  
  <|> Parens <$> parens expr
  <|> IfThenElse <$ keyword "if" <*> expr <* keyword "then" <*> expr <* keyword "else" <*> expr
  <|> Formula <$> (keyword "formula" *> expr)
  <|> Lambda <$> (token (string "/.") *> ident) <*> (token (string ":") *> pType) <*> (token (string "=>") *> expr)
  <|> mkNoVarInfo <$> ident
  <|> Defer  <$> quoted expr


expr :: Parser (Expr NoVarInfo)
expr = precedence $
  sops InfixL [Minus <$ lexeme (char '-'), Less <$ lexeme (char '<')] |-<
  --sops Postfix [flip App <$> parens atom] |-<
  sops Postfix [flip App <$> parens expr] |-<
  Atom atom


-----------------------------------------
-- Action Grammar
-----------------------------------------

data A1 t
  = Seq (A1 t) (A0 t)
  | OfA0 (A0 t)
deriving instance Show (t Type) => Show (A1 t)
deriving instance Eq (t Type) => Eq (A1 t)

data A0 t 
  = Decl Type String (Expr t)
  | Assign String (t Type) (Expr t)
  | Print (Expr t)
deriving instance Show (t Type) => Show (A0 t)
deriving instance Eq (t Type) => Eq (A0 t)

instance A0 t < A1 t where
  upcast = OfA0


a0 :: Parser (A0 NoVarInfo)
a0 
  =   Print <$> (keyword "print" *> expr)
  <|> Decl <$> pType <*> ident <* token (string ":=") <*> expr
  <|> mkVarInfoA <$> ident <* token (string ":=") <*> expr


-- action :: Parser (A1 NoVarInfo)
action :: ParsecT String () Identity (A0 NoVarInfo)
action =  a0 <* optional (lexeme (string ";"))


-----------------------------------------
-- Run parser
-----------------------------------------

parseAction :: String -> Either ParseError (A0 NoVarInfo)
parseAction = parse (fully action) ""

parseFile :: FilePath -> IO (Either ParseError [A0 NoVarInfo])
parseFile = fmap (traverse parseAction . lines) . readFile


parseExpr :: String -> Either ParseError (Expr NoVarInfo)
parseExpr = parse (fully expr) ""