{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
module Parser.Utilities
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

{-
Based on 

Design Patterns for Parser Combinators (Functional Pearl)

ACM ISBN 978-1-4503-8615-9/21/08.
https://doi.org/10.1145/3471874.3472984
-}

import Text.Parsec hiding (token)
import Text.Parsec.String
import Text.Parsec.Combinator
import Data.String (IsString(..))
import Control.Monad
import Control.Applicative ((<**>))
import Data.Functor.Const

import Data.Functor
import Data.Functor.Identity


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

----------------
-- Misc Parsers
----------------

number :: Parser Int
number = f <$> option "" (token $ string "-" ) <*> lexeme (many1 digit)
  where f "-" ds = read ('-':ds)
        f _   ds = read ds
