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
Module      : Parser.Classic.ZillyParser
Description : A Parser for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX
-}
module Parser.Classic.ZillyParser
  ( Expr (..)
  , Term (..)
  , Atom (..)
  , A1 (..)
  , A0 (..)
  , Types (..)
  , Types0 (..)
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

instance u ~ () => IsString (Parser u ) where
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


flip2 :: (t1 -> t2 -> t3 -> t4) -> t3 -> t1 -> t2 -> t4
flip2 f x3 x1 x2 = f x1 x2 x3



-----------------------------------------
-- Expression Grammar / Untyped AST
-----------------------------------------

data Expr
  = Minus Expr Term SourcePos
  | Less Expr Term  SourcePos
  | OfTerm Term


data Term
  = App Term Expr SourcePos
  | OfAtom Atom


data Atom
  = Val Int      SourcePos
  | Var Symbol   SourcePos
  | Parens  Expr SourcePos
  | Defer   Expr SourcePos
  | Formula Expr SourcePos
  | IfThenElse Expr Expr Expr SourcePos
  | Lambda Symbol Types Expr  SourcePos


data Types
  = Arrow Types0 Types SourcePos
  | OfTypes0 Types0


data Types0
  = Z           SourcePos
  | Lazy Types  SourcePos
  | LazyS Types SourcePos
  | TParen Types SourcePos


instance Atom < Term where
  upcast = OfAtom

instance Term < Expr where
  upcast = OfTerm

instance Types0 < Types where
  upcast = OfTypes0


-----------------------------------------
-- Type Parsers
-----------------------------------------

mkTParens :: Parser Types -> Parser Types0
mkTParens p = getPosition <**> (TParen <$> parens p)

mkZ :: Parser Types0
mkZ = getPosition <**> (Z <$ (token (string "Z") <|> token (string "Int")))

mkLazy :: Parser Types -> Parser Types0
mkLazy p = getPosition <**> (Lazy <$> (token (string "Lazy") *> bracketed p))

mkLazyS :: Parser Types -> Parser Types0
mkLazyS p = getPosition <**> (LazyS <$> (token (string "Lazy*") *> bracketed p))

pType0 :: Parser Types0
pType0
  = mkZ
  <|> mkLazy pType
  <|> mkLazyS pType
  <|> mkTParens pType

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
  <|> lexeme (f <$> (char '_' <|> letter) <*> many (letter <|> digit <|> char '_'))
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
mkApp p = (\p' x y -> App y x p') <$> getPosition <*> parens p




expr :: Parser Expr
expr = precedence $
  
  sops InfixL [mkMinus <* "-" , mkLess <* "<"] |-<
  sops Postfix [mkApp expr] |-<
  Atom atom


-----------------------------------------
-- Action Grammar
-----------------------------------------

data A1
  = Seq A0 [A0]
  | OfA0 A0


data A0
  = Decl Types Symbol Expr SourcePos
  | Assign Symbol Expr     SourcePos
  | Print Expr             SourcePos


instance A0 < A1 where
  upcast = OfA0


mkPrint :: Parser Expr -> Parser A0
mkPrint arg = getPosition <**> (Print <$> (keyword "print" *> parens arg))

mkDecl :: Parser Types -> Parser Symbol -> Parser Expr -> Parser A0
mkDecl pType' ident' expr' = getPosition <**> (Decl <$> pType' <*> ident' <* token (string ":=") <*> expr')

mkAssign :: Parser Symbol -> Parser Expr -> Parser A0
mkAssign ident' expr' = getPosition <**> (Assign <$> ident' <* token (string ":=") <*> expr')

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

-- | Skips 0 or more lines with spaces on them.
skipLines :: ParsecT Symbol () Identity ()
--skipLines = void $ many (void endOfLine <|> space *> spaces)
skipLines = void $ many (void endOfLine <|> space *> spaces)

-- | Skips 0 or more comments with spaces on them.
skipComments :: ParsecT Symbol () Identity ()
skipComments = void . many $ token (string "--") *> space *> manyTill anyChar (eot <|> void endOfLine)

skipLinesAndComments :: ParsecT Symbol () Identity ()
skipLinesAndComments = void (skipLines <|> skipComments)


eot :: ParsecT Symbol () Identity ()
eot  = void (char '\EOT') <?> "end of packet"

actions :: ParsecT Symbol () Identity [A0]
actions = manyTill (action <* skipLinesAndComments) (eot <|> eof)

actions' :: ParsecT Symbol () Identity A1
actions' = actions >>= \case
  [] -> fail "empty file"
  (a:as) -> pure $ Seq a as

-----------------------------------------
-- Type Mapping
-----------------------------------------


parserT2AdtT :: Types -> ZT.Types
parserT2AdtT = \case
  OfTypes0 (Z _)        -> ZT.Value ZT.Z
  OfTypes0 (Lazy t _)   -> ZT.Lazy (parserT2AdtT t)
  OfTypes0 (LazyS t _)  -> ZT.LazyS (parserT2AdtT t)
  OfTypes0 (TParen t _) -> parserT2AdtT t
  Arrow t1 t2 _ -> ZT.Value (parserT2AdtT (OfTypes0 t1) ZT.:-> parserT2AdtT t2)
 

-----------------------------------------
-- Run parser
-----------------------------------------

parseAction :: Symbol -> Either ParseError A0
parseAction = parse (fully action) ""

parseFile :: FilePath -> IO (Either ParseError [A0])
parseFile = fmap (parse actions "") . readFile

parseFile' :: FilePath -> IO (Either ParseError A1)
parseFile' = fmap (parse actions' "") . readFile

parseExpr :: Symbol -> Either ParseError Expr
parseExpr = parse (fully expr) ""

-----------------------------------------
-- Show instances
-----------------------------------------

instance Show Expr where
  showsPrec p = \case
    -- minu
    Minus e1 e2 _ -> showParen (p > 6) $ showsPrec 6 e1 . showString " - " . showsPrec 7 e2
    Less e1 e2 _  -> showParen (p > 4) $ showsPrec 5 e1 . showString " < " . showsPrec 5 e2
    OfTerm t      -> showsPrec p t

instance Show Term where
  showsPrec p = \case
    App t e _ -> showParen (p > 10) $ showsPrec 10 t . showString " " . showParen True (shows e) --showsPrec 11 e
    OfAtom a  -> showsPrec p a

instance Show Atom where
  showsPrec p = \case
    Val n _ -> shows n
    Var s _ -> showString s
    Parens e _ -> showParen True $ shows e
    Defer e _ -> showChar '\'' . shows e . showChar '\''
    Formula e _ -> showString "formula " . showParen True (shows e)
    IfThenElse e1 e2 e3 _ -> showString "if " . shows e1 . showString " then " . shows e2 . showString " else " . shows e3
    Lambda s t e _ -> showParen (p > 1) $  showString "/. " . showString s . showString " : " . shows t . showString " => " . shows e

instance Show Types where
  showsPrec p = \case
    Arrow t1 t2 _ -> showParen (p > 1) $ showsPrec 2 t1 . showString " -> " . showsPrec 1 t2
    OfTypes0 t -> showsPrec p t

instance Show Types0 where
  showsPrec _ = \case
    Z _ -> showString "Z"
    Lazy t _ -> showString "Lazy<" .  shows t . showString ">"
    LazyS t _ -> showString "Lazy*<" . shows t . showString ">"
    TParen e _ -> showParen True $ shows e

instance Show A0 where
  showsPrec _ = \case
    Decl t s e _ -> shows t . showString " " . showString s . showString " := " . shows e
    Assign s e _ -> showString s . showString " := " . shows e
    Print e _ -> showString "print " . shows e

instance Show A1 where
  show (OfA0 a) = show a <> ";\n"
  show (Seq a as) = show a <> ";\n" <> concatMap (show . OfA0) as

-----------------------------------------
-- Eq instances
-----------------------------------------

instance Eq Expr where
  Minus e1 e2 _ == Minus e1' e2' _ = e1 == e1' && e2 == e2'
  Less e1 e2 _ == Less e1' e2' _ = e1 == e1' && e2 == e2'
  OfTerm t == OfTerm t' = t == t'
  _ == _ = False

instance Eq Term where 
  App t e _ == App t' e' _ = t == t' && e == e'
  OfAtom a == OfAtom a' = a == a'
  _ == _ = False

instance Eq Atom where 
  Val n _ == Val n' _ = n == n'
  Var s _ == Var s' _ = s == s'
  Parens e _ == Parens e' _ = e == e'
  Defer e _ == Defer e' _ = e == e'
  Formula e _ == Formula e' _ = e == e'
  IfThenElse e1 e2 e3 _ == IfThenElse e1' e2' e3' _ = e1 == e1' && e2 == e2' && e3 == e3'
  Lambda s t e _ == Lambda s' t' e' _ = s == s' && t == t' && e == e'
  _ == _ = False

instance Eq Types where 
  Arrow t1 t2 _ == Arrow t1' t2' _ = t1 == t1' && t2 == t2'
  OfTypes0 t == OfTypes0 t' = t == t'
  _ == _ = False

instance Eq Types0 where 
  Z _ == Z _ = True
  Lazy t _ == Lazy t' _ = t == t'
  LazyS t _ == LazyS t' _ = t == t'
  TParen e _ == TParen e' _ = e == e'
  _ == _ = False

instance Eq A1 where 
  Seq a as == Seq a' as' = a == a' && as == as'
  OfA0 a == OfA0 a' = a == a'
  _ == _ = False

instance Eq A0 where 
  Decl t s e _ == Decl t' s' e' _ = t == t' && s == s' && e == e'
  Assign s e _ == Assign s' e' _ = s == s' && e == e'
  Print e _ == Print e' _ = e == e'
  _ == _ = False