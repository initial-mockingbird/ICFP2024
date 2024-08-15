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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeAbstractions #-}

{-|
Module      : Parser.Classic.ZillyPlusParser
Description : A Parser for Lilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX
-}
module Parser.ClassicPlus.ZillyPlusParser
where

import Parser.Utilities hiding (type(<))
import Parser.Utilities qualified as PU
import Parser.Numbers
import Parser.ParserZ (deserializePacket,Packet',Payload'(..))

import Text.Parsec hiding (token)


import Data.String (IsString(..))
import Control.Monad

import Data.Functor.Identity
import Control.Applicative hiding (Alternative(..),optional)
import Data.Coerce
import GHC.TypeLits.Singletons
import Prelude.Singletons
import Data.Kind (Type,Constraint)
import Data.Functor
import Control.Applicative (Alternative(empty))

#ifndef WASM
import Data.Singletons.TH
import Data.Singletons.Decide (decideEquality)
import Unsafe.Coerce (unsafeCoerce)



$(singletons [d|
  data TupleCtx = LambdaCtx | NoCtx | AppCtx deriving Eq
  |])

#endif

------------------------
-- Reserved strings
------------------------

-- | Keywords for Lilly
keywords :: [String]
keywords = stdLib ++
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
  , "array"
  , "string"
  , "true"
  , "false"
  , "fn"
  , "fun"
  , "#DIV/0!"
  , "#NUM!"
  , "#NAME?"
  ] 

-- | standard library for Lilly
stdLib :: [String]
stdLib = 
  [ "log"
  , "sin"
  , "cos"
  , "tan"
  , "sqrt"
  , "append"
  , "at"
  ]

-- | Reserved (expression/type) operators
reservedOperators :: [String]
reservedOperators =
  [ "::"
  , "+"
  , "-"
  , "*"
  , "/"
  , "%"
  , "^"
  , "->"
  , "=>"
  , "<"
  , "<="
  , ">"
  , ">="
  , "<>"
  , "="
  ]

----------------------------
-- Parser definition
----------------------------

data ParserState = PST 
  { pstIdent      :: Natural
  , insideComment :: Bool
  }

initialPST :: ParserState 
initialPST = PST {pstIdent=0,insideComment=False}

type Parser a = ParsecT String ParserState Identity a

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
-- Useful Aux class
-------------------------------

class UpcastPrec (f :: Natural -> Type) (n :: Natural) where
  upcastPrec :: SingI n' => ((n' > n) ~ True) => f n'   -> f n
  genericUnwrap :: f n -> Maybe (Exists f)
---------------------------
-- Book-keeping.
---------------------------

data BookeepInfo = BI 
  { tokenPos   :: SourcePos
  , identLevel :: Natural 
  }

mkBookeepInfo :: Parser BookeepInfo
mkBookeepInfo = BI <$> getPosition <*> fmap pstIdent getState 

----------------------------
-- Aux structures
----------------------------

data Exists f where
  MkExists :: forall f (n :: Natural). SingI n => f n -> Exists f

-- | Sometimes we will need to have an array of parse trees. 
-- Since haskell doesn't support first class existentials. We do so like this. 
data TupleArg (f :: Natural -> Type) (upperBound :: Natural) (ctx :: TupleCtx) where
  MkTupleArg ::forall f upperBound ctx n
    . ((n < upperBound) ~ True) 
    => TupleArgX ctx -- ^ Some tuples may need extra info
    -> f n 
    -> TupleArg f upperBound ctx

-- | Extra info for `TupleArg`
type family TupleArgX ctx :: Type where 
  TupleArgX LambdaCtx = Maybe Types
  TupleArgX NoCtx     = Void
  TupleArgX AppCtx    = Void

mkTupleArg :: forall f ctx upperBound n. 
  (n < upperBound) ~ True 
  => Parser (TupleArgX ctx) 
  -> Parser (f n)
  -> Parser (TupleArg f upperBound ctx)
mkTupleArg = liftA2 MkTupleArg 

-----------------------------------------
-- Type Parsers
-----------------------------------------

-- | Parser tree for types. Indexed by the precedence
data family TPrec (n :: Natural)

type Inf     = 0xffffffffffffffff

-- | Precedence of atoms. Defined as Infinity since 
-- they have the highest precedence.
type Atom    = Inf

-- | One level bellow atom precedence. Needed to be defined as 
-- a constant due to restrictions on type family evaluation inside GADTs.
type PredInf = 0xfffffffffffffffe

type PrefixPrec = 0xfffffffffffffffd

type PostfixPrec = 0xfffffffffffffffe


-- | Expressions Have the lowest precedence.
type Expr    = EPrec 0

-- | A type in lilly, is a type of precedence 0.
type Types = TPrec 0

------------------------------
-- Precedence Inf Types
------------------------------

data instance TPrec Atom where
  -- | Integers: @Z@, @int@
  TZ         :: BookeepInfo -> TPrec Atom
  -- | Double: @double@
  TDouble    :: BookeepInfo -> TPrec Atom
  -- | Boolean: @bool@,@boolean@
  TBool      :: BookeepInfo -> TPrec Atom
  -- | Strings: @string@
  TString    :: BookeepInfo -> TPrec Atom
  -- | null: @null@
  TNull      :: BookeepInfo -> TPrec Atom
  -- | Lazy: @lazy@
  TLazy      :: BookeepInfo -> TPrec Atom
  -- | Lazy star: @lazy*@
  TLazyS     :: BookeepInfo -> TPrec Atom
  -- | Array: @array[]@. TODO: multiple dimension array
  TArray     :: BookeepInfo -> TPrec Atom
  -- | Infer type: @:optional_identifier:@
  TInfer     :: BookeepInfo -> Maybe String       -> TPrec Atom
  -- | Functions: @fn(t0 var0, t1 var1, ...)@
  TFun       :: BookeepInfo -> [(TPrec 0,Maybe String)] -> TPrec Atom
  -- | Variables: any valid identifier
  TVar       :: BookeepInfo -> String             -> TPrec Atom
  -- | Parentheses: @(type)@
  TParen     :: forall n. (n < Atom) ~ True
    => BookeepInfo -> TPrec n -> TPrec Atom

mkZT :: Parser (TPrec Inf)
mkZT = mkBookeepInfo <**> (TZ <$ "Z")

mkDoubleT :: Parser (TPrec Inf)
mkDoubleT = mkBookeepInfo <**> (TDouble <$ "double")

mkBoolT :: Parser (TPrec Inf)
mkBoolT = mkBookeepInfo <**> (TBool <$ ("bool" <|> "boolean"))

mkStringT :: Parser (TPrec Inf)
mkStringT = mkBookeepInfo <**> (TString <$ "string")

mkNullT :: Parser (TPrec Inf)
mkNullT = mkBookeepInfo <**> (TNull <$ "null")

mkLazyT :: Parser (TPrec Inf)
mkLazyT = mkBookeepInfo <**> (TLazy <$ "lazy")

mkLazyST :: Parser (TPrec Inf)
mkLazyST = mkBookeepInfo <**> (TLazyS <$ "lazy*")

mkArrayT :: Parser (TPrec Inf)
mkArrayT = mkBookeepInfo <**> (TArray <$ "array[]")

mkInferT :: Parser (TPrec Inf)
mkInferT = TInfer <$> mkBookeepInfo <*> (":" *> optionMaybe ident <* ":")


mkFunT :: Parser [(TPrec 0,Maybe String)] -> Parser (TPrec Inf)
mkFunT p = TFun <$> (mkBookeepInfo <* ("fn" <|> "fun")) <*> parens p

mkVarT ::  Parser (String -> TPrec Inf)
mkVarT = TVar <$> mkBookeepInfo

mkParenT :: forall {n0} n. (n0 ~ Inf, (n < n0) ~ True) 
  =>  Parser (TPrec n) -> Parser (TPrec n0) 
mkParenT p = parens $ TParen <$> mkBookeepInfo <*> p


pTypeAtom :: Parser (TPrec Atom)
pTypeAtom 
  =   mkZT
  <|> mkDoubleT
  <|> mkBoolT
  <|> mkStringT
  <|> mkNullT
  <|> mkLazyT
  <|> mkLazyST
  <|> mkArrayT
  <|> mkInferT
  <|> mkParenT pTypes
  <|> mkFunT (((,) <$> pTypes <*> optionMaybe ident) `sepBy` "," )
  <|> mkVarT <*> ident
  

------------------------------
-- Precedence Inf-1 Types
------------------------------

-- | (Invisible) Type Applications are 1 level bellow attoms
data instance TPrec PredInf where
  -- | Invisible Lazy type: @lazy@
  TLazySp      :: forall n. (n ~ PredInf)
    => BookeepInfo -> TPrec n -> TPrec PredInf
  -- | Invisible Lazy Star type: @lazy*@
  TLazySpS     :: forall n. (n ~ PredInf)
    => BookeepInfo -> TPrec n -> TPrec PredInf
  -- | Invisible Array type: @array[]@. TODO: multi dimensional array
  TArrayS :: forall n. (n ~ PredInf)
    => BookeepInfo -> TPrec n -> TPrec PredInf
  OfHigherTPrecPredInf :: forall n. (SingI n, (n > PredInf) ~ True )
    => TPrec n -> TPrec PredInf

instance UpcastPrec TPrec PredInf where
  upcastPrec = OfHigherTPrecPredInf
  genericUnwrap (OfHigherTPrecPredInf f) = Just $ MkExists f
  genericUnwrap _ = Nothing
  
mkLazySpT :: forall {n0}. (n0 ~ PredInf) 
  => Parser (TPrec n0 -> TPrec n0) 
mkLazySpT =  TLazySp <$> mkBookeepInfo 

mkLazySpST :: forall {n0}. (n0 ~ PredInf) 
  => Parser (TPrec n0 -> TPrec n0) 
mkLazySpST = TLazySpS <$> mkBookeepInfo 

mkArrayST :: forall {n0}. (n0 ~ PredInf) 
  => Parser (TPrec n0 -> TPrec n0) 
mkArrayST =  TArrayS <$> mkBookeepInfo 

instance (SingI n',(n' > n) ~ True, UpcastPrec TPrec n) => TPrec n' PU.< TPrec n where
  upcast = upcastPrec @TPrec

------------------------------
-- Precedence 0 Types
------------------------------

data instance TPrec 0 where
  -- | Lowest precedence type. Visible Type application
  TArrow :: forall n. (SingI n, (n > 0) ~ True )
    => BookeepInfo -> TPrec n -> TPrec 0 -> TPrec 0
  OfHigherTPrec0 :: forall n. (SingI n,(n > 0) ~ True )
    => TPrec n -> TPrec 0

instance UpcastPrec TPrec 0 where
  upcastPrec = OfHigherTPrec0
  genericUnwrap (OfHigherTPrec0 f) = Just $ MkExists f
  genericUnwrap _ = Nothing




mkArrowT :: forall {n0} n. (SingI n, n0 ~ 0, (n > n0) ~ True) 
  => Parser (TPrec n -> TPrec 0 -> TPrec 0)
mkArrowT = TArrow <$> mkBookeepInfo


pTypes :: Parser Types
pTypes = precedence $ 
  sops InfixR  [mkArrowT <* "=>"] |-<
  sops Prefix 
    [ try $ mkLazySpT  <* ("lazy"   <* notFollowedBy "=>" )
    , try $ mkLazySpST <* ("lazy*" <* notFollowedBy "=>") 
    , try $ mkArrayST  <* ("array" <* "[]" <* notFollowedBy "=>")
    ] |-<
  Atom pTypeAtom

-----------------------------------------
-- Expression Grammar / Untyped AST
-----------------------------------------

-- | Expression parse trees are types indexed by its precedence.
data family EPrec (n :: Natural)

instance (SingI n',(n' > n) ~ True, UpcastPrec EPrec n) => EPrec n' PU.< EPrec n where
  upcast = upcastPrec @EPrec

instance UpcastPrec EPrec PrefixPrec where
  upcastPrec = OfHigherPrefixPrec
  genericUnwrap (OfHigherPrefixPrec f) = Just $ MkExists f
  genericUnwrap _ = Nothing

instance UpcastPrec EPrec PostfixPrec where
  upcastPrec = OfHigherPostfixPrec
  genericUnwrap (OfHigherPostfixPrec f) = Just $ MkExists f
  genericUnwrap _ = Nothing

instance UpcastPrec EPrec 8 where
  upcastPrec = OfHigher8
  genericUnwrap (OfHigher8 f) = Just $ MkExists f
  genericUnwrap _ = Nothing

instance UpcastPrec EPrec 7 where
  upcastPrec = OfHigher7
  genericUnwrap (OfHigher7 f) = Just $ MkExists f
  genericUnwrap _ = Nothing

instance UpcastPrec EPrec 6 where
  upcastPrec = OfHigher6 
  genericUnwrap (OfHigher6 f) = Just $ MkExists f
  genericUnwrap _ = Nothing

instance UpcastPrec EPrec 0 where
  upcastPrec = OfHigher0
  genericUnwrap (OfHigher0 f) = Just $ MkExists f

instance UpcastPrec EPrec 4 where
  upcastPrec = OfHigher4
  genericUnwrap (OfHigher4 f) = Just $ MkExists f
  genericUnwrap _ = Nothing




class UnwrapUpcasting (f :: Natural -> Type) (n :: Natural) where
  unwrapUpcast :: forall n'. (SingI n', UpcastPrec f n', (n' < n) ~ True) => f n' -> Maybe (f n)


instance UnwrapUpcasting TPrec PredInf where
  unwrapUpcast :: forall n''. 
    (SingI n'', UpcastPrec TPrec n'', (n'' < PredInf) ~ True) =>
      TPrec n'' -> Maybe (TPrec PredInf)
  unwrapUpcast f = do
    MkExists @TPrec @n' f' <- genericUnwrap f
    {- case sing @(Compare PredInf n') of
      SEQ -> Just f'
      SLT -> unwrapUpcast f'
      SGT -> Nothing  -}
    undefined

instance UnwrapUpcasting TPrec Inf 


solveChain :: forall (n' :: Natural). (SingI n') 
  => TPrec n' -> Maybe (TPrec Inf)
solveChain f = do 
  MkExists @TPrec @n x <- case 
      ( decideEquality (sing @n') (SNat @0)
      , decideEquality (sing @n') (SNat @PredInf)
      , decideEquality (sing @n') (SNat @Inf)
      ) of
      (Just Refl,_,_)-> case f of
          OfHigherTPrec0 @n x -> Just $ MkExists x 
          _ -> Nothing
      (_,Just Refl,_)-> case f of
          OfHigherTPrecPredInf @n x -> Just $ MkExists x 
          _ -> Nothing
      (_,_,Just Refl)-> case f of
          x -> Just $ MkExists x 
      _ -> Nothing
  case decideEquality (sing @n %< sing @Inf ) (sing @True) of
        Just Refl -> solveChain x
        Nothing   -> Just $ unsafeCoerce x



------------------------------
-- Precedence Inf Expressions
------------------------------


-- | Expression trees for attoms
data instance EPrec Atom where
  -- | Integers @-1,2,3,-100,....@
  PInt     :: BookeepInfo  -> Int    -> EPrec Atom
  -- | IEEE doubles @1,0.5,1e5,1E5,1e-10,-5e-5,-5E-5@
  PDouble  :: BookeepInfo  -> Double -> EPrec Atom
  -- | Booleans: @true,false@
  PBool    :: BookeepInfo  -> Bool   -> EPrec Atom 
  -- | Variables: any identifier
  PVar     :: BookeepInfo  -> String -> EPrec Atom
  -- | Array literals: @[expr0,expr1,....]@
  PArray   :: BookeepInfo -> [TupleArg EPrec Atom NoCtx] -> EPrec Atom
  -- | parenthesis: @(expr)@
  PParen   :: forall n. (SingI n,(n < Atom) ~ True) => BookeepInfo -> EPrec n    -> EPrec Atom
  -- | Quoted expressions: @'expr'@
  PDefer   :: forall n. (SingI n,(n < Atom) ~ True) => BookeepInfo -> EPrec n    -> EPrec Atom
  -- | Lambda functions: 
  -- @
  --  fn(type0 var0, type1 var1,...) => return_type -> expr 
  --  fn(type0 var0, type1 var1,...) -> expr
  -- @
  PLambda  :: forall n. (SingI n,(n < Atom) ~ True )
    => BookeepInfo 
    -> [TupleArg EPrec Atom LambdaCtx]
    -> Maybe Types
    -> EPrec n
    -> EPrec Atom
  -- | Uniform random function: @uniform()@
  PUniform  :: BookeepInfo -> EPrec Atom
  -- | Formula function: @formula(expr)@
  PFormula  :: forall n. (SingI n,(n < Atom) ~ True)
    => BookeepInfo -> EPrec n ->  EPrec Atom
  -- | If function: @if(expr,expr,expr)@
  PIf :: forall n0 n1 n2. 
    ( (n0 < Atom) ~ True
    , (n1 < Atom) ~ True
    , (n2 < Atom) ~ True
    , SingI n0
    , SingI n1
    , SingI n2
    )
    => BookeepInfo 
    -> (EPrec n0, EPrec n1, EPrec n2) 
    -> EPrec Atom

mkUniform :: Parser (EPrec Atom)
mkUniform = "uniform" *> parens (PUniform <$> mkBookeepInfo)

mkFormula :: forall {n0} n. (SingI n,n0 ~ Atom, (n < n0) ~ True)
  => Parser (EPrec n ->  EPrec Atom)
mkFormula = "formula" *> parens (PFormula <$> mkBookeepInfo)

mkIf :: forall {n} n0 n1 n2. 
  ( n ~ Atom
  , SingI n0
  , SingI n1
  , SingI n2
  , (n0 < n) ~ True
  , (n1 < n) ~ True 
  , (n2 < n) ~ True 
  ) => Parser (EPrec n0, EPrec n1, EPrec n2) -> Parser ( EPrec Atom)
mkIf p = "if" *> parens (PIf <$> mkBookeepInfo <*> p)



ident :: Parser String
ident = mkIdent anyKeyword 


mkInt :: forall {n0}. (n0 ~ Atom) 
  =>  Parser (Int -> EPrec n0)
mkInt = PInt <$> mkBookeepInfo

mkDouble :: forall {n0}. (n0 ~ Atom) 
  =>  Parser (Double -> EPrec n0)
mkDouble = PDouble <$> mkBookeepInfo

mkBool :: forall {n0}. (n0 ~ Atom) 
  =>  Parser (Bool -> EPrec n0)
mkBool = PBool <$> mkBookeepInfo

mkVar :: forall {n0}. (n0 ~ Atom) 
  =>  Parser (String -> EPrec n0)
mkVar = PVar <$> mkBookeepInfo 

mkParen :: forall {n0} n. (SingI n,n0 ~ Atom, (n < n0) ~ True) 
  =>  Parser (EPrec n) -> Parser (EPrec n0) 
mkParen p = parens $ PParen <$> mkBookeepInfo <*> p

mkDefer :: forall {n0} n. (SingI n,n0 ~ Atom, (n < n0) ~ True) 
  =>  Parser (EPrec n) -> Parser (EPrec n0)
mkDefer p = quoted $ PDefer <$> mkBookeepInfo <*> p

mkArray :: forall {n0}. (n0 ~ Atom) 
  =>  Parser (TupleArg EPrec Atom NoCtx) -> Parser (EPrec n0)
mkArray  p = bracketed' $ PArray <$> mkBookeepInfo <*> p `sepBy` ","

mkLambda :: forall {n0} n. (SingI n,n0 ~ Atom, (n < n0) ~ True) 
  => Parser (EPrec n) -> Parser (TupleArg EPrec Atom LambdaCtx) -> Parser (EPrec n0)
mkLambda p t 
  = PLambda 
  <$> (mkBookeepInfo <* "fn" ) 
  <*> parens (t `sepBy` ",")
  <*> optionMaybe ("=>" *> pTypes) 
  <*> ("->" *> p)


atom :: Parser (EPrec Atom)
atom 
  = pNumber 
  <|> mkBool   <*> (True <$ "true" <|> False <$ "false")
  <|> mkArray (mkTupleArg (pure $ error "Attempt to evaluate void") expr)
  <|> mkDefer expr
  <|> mkUniform
  <|> mkFormula <*> expr
  <|> mkIf ((,,) <$> (expr <* ",")  <*> (expr <* ",") <*> expr)
  <|> mkLambda expr contextualLambda
  <|> mkParen expr
  <|> mkVar    <*> ident
  where 
    pNumber' 
      = try (mkDouble <*> floating) 
      <|> mkInt <*> (read <$> many1 digit)
      <?> "malformed number literal"
    
    pNumber = pNumber' <* spaces

    contextualLambda :: Parser (TupleArg EPrec Atom LambdaCtx)
    contextualLambda = optionMaybe pTypes >>= \case
      var@(Just (OfHigherTPrec0 f)) -> case solveChain f of  
        Just (TVar bi x) ->  MkTupleArg @EPrec @Atom @LambdaCtx var <$> expr 
          <|> pure (MkTupleArg @_ @_ @LambdaCtx Nothing (OfHigher0 (PVar bi x)))
        _ -> MkTupleArg @EPrec @Atom @LambdaCtx var <$> expr
      t -> MkTupleArg @EPrec @Atom @LambdaCtx t <$> expr



-----------------------------------
-- Precedence AppPrec Expressions
-----------------------------------

data instance EPrec PrefixPrec where
  PUMinus :: BookeepInfo -> EPrec PrefixPrec -> EPrec PrefixPrec
  OfHigherPrefixPrec :: forall n. (SingI n,(n > PrefixPrec) ~ True) => EPrec n -> EPrec PrefixPrec
-- | Precedence of applications
data instance EPrec PostfixPrec where
  -- Function applications: @expr(expr00,expr01,....)(expr10,expr11,...)...@
  PApp    :: BookeepInfo -> EPrec PostfixPrec -> [TupleArg EPrec PostfixPrec AppCtx] -> EPrec PostfixPrec
  PAppArr :: BookeepInfo -> EPrec PostfixPrec -> [TupleArg EPrec PostfixPrec AppCtx] -> EPrec PostfixPrec
  OfHigherPostfixPrec :: forall n. (SingI n,(n > PostfixPrec) ~ True) => EPrec n -> EPrec PostfixPrec

mkApp :: Parser (TupleArg EPrec PostfixPrec AppCtx) -> Parser (EPrec PostfixPrec -> EPrec PostfixPrec)
mkApp p =  (\p' x y -> PApp p' y x ) <$> mkBookeepInfo <*> parens (p `sepBy` ",")

mkAppArr :: Parser (TupleArg EPrec PostfixPrec AppCtx) -> Parser (EPrec PostfixPrec -> EPrec PostfixPrec)
mkAppArr p =  (\p' x y -> PAppArr p' y x ) <$> mkBookeepInfo <*> bracketed' (p `sepBy` ",")


mkUMinus :: Parser (EPrec PrefixPrec -> EPrec PrefixPrec)
mkUMinus = PUMinus <$> mkBookeepInfo

------------------------------
-- Precedence 8 Expressions
------------------------------

-- | Precedence 8 operators.
data instance EPrec 8 where
  -- | Power operator: @expr^expr@, right associative.
  PPower    :: forall n. (SingI n,(n > 8) ~ True) => BookeepInfo -> EPrec n -> EPrec 8 -> EPrec 8
  OfHigher8 :: forall n. (SingI n,(n > 8) ~ True) =>                EPrec n            -> EPrec 8

mkPower :: forall {n0} n. (SingI n,n0 ~ 8, (n > n0) ~ True) => Parser (EPrec n -> EPrec n0 -> EPrec n0)
mkPower = PPower <$> mkBookeepInfo

------------------------------
-- Precedence 7 Expressions
------------------------------

-- | Precedence 7 operators.
data instance EPrec 7 where
  -- | Multiplication operator: @expr * expr@, left associative.
  PMul      :: forall n. (SingI n,(n > 7) ~ True) => BookeepInfo -> EPrec 7 -> EPrec n -> EPrec 7
  -- | Division operator: @expr / expr@, left associative.
  PDiv      :: forall n. (SingI n,(n > 7) ~ True) => BookeepInfo -> EPrec 7 -> EPrec n -> EPrec 7
  -- | Mod operator: @expr % expr@, left associative.
  PMod      :: forall n. (SingI n,(n > 7) ~ True) => BookeepInfo -> EPrec 7 -> EPrec n -> EPrec 7
  OfHigher7 :: forall n. (SingI n,(n > 7) ~ True) =>                           EPrec n -> EPrec 7

mkMul :: forall {n0} n. (SingI n,n0 ~ 7, (n > n0) ~ True) => Parser (EPrec n0 -> EPrec n -> EPrec n0)
mkMul = PMul <$> mkBookeepInfo

mkDiv :: forall {n0} n. (SingI n,n0 ~ 7, (n > n0) ~ True) => Parser (EPrec n0 -> EPrec n -> EPrec n0)
mkDiv = PDiv <$> mkBookeepInfo

mkMod :: forall {n0} n. (SingI n,n0 ~ 7, (n > n0) ~ True) => Parser (EPrec n0 -> EPrec n -> EPrec n0)
mkMod = PMod <$> mkBookeepInfo


------------------------------
-- Precedence 6 Expressions
------------------------------

-- | Precedence 6 operators.
data instance EPrec 6 where
  -- | Plus operator: @expr + expr@, left associative.
  PPlus     :: forall n. (SingI n,(n > 6) ~ True) => BookeepInfo -> EPrec 6 ->  EPrec n -> EPrec 6
  -- | Minus operator: @expr - expr@, left associative.
  PMinus    :: forall n. (SingI n,(n > 6) ~ True) => BookeepInfo -> EPrec 6 ->  EPrec n -> EPrec 6
  OfHigher6 :: forall n. (SingI n,(n > 6) ~ True) =>                            EPrec n -> EPrec 6

mkMinus :: forall {n0} n. (SingI n,n0 ~ 6, (n > n0) ~ True) => Parser (EPrec n0 -> EPrec n -> EPrec n0)
mkMinus = PMinus <$> mkBookeepInfo

mkPlus :: forall {n0} n. (SingI n,n0 ~ 6, (n > n0) ~ True) => Parser (EPrec n0 -> EPrec n -> EPrec n0)
mkPlus = PPlus <$> mkBookeepInfo

------------------------------
-- Precedence 4 Expressions
------------------------------

-- | Precedence 4 operators.
data instance EPrec 4 where
  -- | Less Than operator: @expr < expr@, non assoc associative.
  PLT       :: forall n. (SingI n,(n > 4) ~ True) => BookeepInfo -> EPrec n ->  EPrec n -> EPrec 4
  -- | Less Than or Equal operator: @expr <= expr@, non assoc associative.
  PLTEQ     :: forall n. (SingI n,(n > 4) ~ True) => BookeepInfo -> EPrec n ->  EPrec n -> EPrec 4
  -- | Greater Than operator: @expr > expr@, non assoc associative.
  PGT       :: forall n. (SingI n,(n > 4) ~ True) => BookeepInfo -> EPrec n ->  EPrec n -> EPrec 4
  -- | Greater Than or Equal operator: @expr >= expr@, non assoc associative.
  PGTEQ     :: forall n. (SingI n,(n > 4) ~ True) => BookeepInfo -> EPrec n ->  EPrec n -> EPrec 4
  -- | Equal operator: @expr = expr@, non assoc associative.
  PEQ       :: forall n. (SingI n,(n > 4) ~ True) => BookeepInfo -> EPrec n ->  EPrec n -> EPrec 4
  -- | Different operator : @expr <> expr@, non assoc associative.
  PNEQ      :: forall n. (SingI n,(n > 4) ~ True) => BookeepInfo -> EPrec n ->  EPrec n -> EPrec 4
  OfHigher4 :: forall n. (SingI n,(n > 4) ~ True) =>                            EPrec n -> EPrec 4

mkPLT :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec n -> EPrec n -> EPrec n0)
mkPLT = PLT <$>  mkBookeepInfo

mkPLTEQ :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec n -> EPrec n -> EPrec n0)
mkPLTEQ = PLTEQ <$>  mkBookeepInfo

mkPGT :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec n -> EPrec n -> EPrec n0)
mkPGT  = PGT <$>  mkBookeepInfo

mkPGTEQ :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec n -> EPrec n -> EPrec n0)
mkPGTEQ = PGTEQ <$>  mkBookeepInfo

mkPEQ :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec n -> EPrec n -> EPrec n0)
mkPEQ  = PEQ <$>  mkBookeepInfo

mkPNEQ :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec n -> EPrec n -> EPrec n0)
mkPNEQ = PNEQ <$>  mkBookeepInfo

------------------------------
-- Precedence 0 Expressions
------------------------------

-- | Expressions.
data instance EPrec 0 where
  OfHigher0 :: forall n. (SingI n, (n > 0) ~ True) => EPrec n -> EPrec 0

expr :: Parser (EPrec 0)
expr = fmap OfHigher0 . precedence $
  sops InfixN 
    [ mkPLT   <* "<" 
    , mkPLTEQ <* "<="
    , mkPGT   <* ">"
    , mkPGTEQ <* ">="
    , mkPEQ   <* "="
    , mkPNEQ  <* "<>"
    ] |-<
  sops InfixL 
    [ mkMinus <* "-"
    , mkPlus  <* "+"
    ] |-<
  sops InfixL 
    [ mkMul <* "*"
    , mkDiv <* "/"
    , mkMod <* "%"
    ] |-<
  sops InfixR  [ mkPower  <* "^"] |-<
  sops Prefix  [ mkUMinus <* "-"] |-<
  sops Postfix 
    [ mkApp    $ mkTupleArg (pure $ error "Attempt to evaluate void") expr
    , mkAppArr $ mkTupleArg (pure $ error "Attempt to evaluate void") expr
    ] |-<
  
  Atom atom




-----------------------------------------
-- Action Grammar
-----------------------------------------

data A1
  = Seq A0 [A0]
  | OfA0 A0


data A0
  = Decl Types String Expr BookeepInfo
  | Assign String Expr     BookeepInfo
  | Print Expr             BookeepInfo


instance A0 PU.< A1 where
  upcast = OfA0


mkPrint :: Parser A0
mkPrint = mkBookeepInfo <**> (Print <$> (keyword "print" *> parens expr))

mkDecl :: Parser Types -> Parser String -> Parser Expr -> Parser A0
mkDecl pType' ident' expr' = mkBookeepInfo <**> (Decl <$> pType' <*> ident' <* token (string ":=") <*> expr')

mkAssign :: Parser String -> Parser Expr -> Parser A0
mkAssign ident' expr' = mkBookeepInfo <**> (Assign <$> ident' <* token (string ":=") <*> expr')

a0 :: Parser A0
a0
  =   mkPrint
  <|> mkDecl pTypes ident expr
  <|> mkAssign ident expr


action :: Parser A0
action =  a0 <* optional (lexeme (string ";"))

-----------------------------------------
-- File Parsing
-----------------------------------------



-----------------------------------------
-- Type Mapping
-----------------------------------------


 

-----------------------------------------
-- Run parser
-----------------------------------------

parseExpr :: String -> String
parseExpr s = case runParser (spaces *> fully expr) initialPST "" s of
  Left e -> show e
  Right _ -> "success!"

parseTypes :: String -> String
parseTypes s = case runParser (spaces *> fully pTypes) initialPST "" s of
  Left e -> show e
  Right _ -> "success!"

parseAction :: String -> String
parseAction s = case runParser (spaces *> fully action) initialPST "" s of
  Left e -> show e
  Right _ -> "success!"


tests :: [String]
tests =
  [ "array[] => lazy var vec := ['0 + uniform()', '1 + uniform()', '2 + uniform()', '3 + uniform()', '4 + uniform()', '5 + uniform()'];"
  , ":: vec := ['0 + uniform()', '1 + uniform()', '2 + uniform()', '3 + uniform()', '4 + uniform()', '5 + uniform()'];"
  , "array[] => :: vec := ['0 + uniform()', '1 + uniform()', '2 + uniform()', '3 + uniform()', '4 + uniform()', '5 + uniform()'];"
  , "array[] => lazy double vec := ['0 + uniform()', '1 + uniform()', '2 + uniform()', '3 + uniform()', '4 + uniform()', '5 + uniform()'];"
  , ":: f := fn(n) -> if(n < 2, n, f(n-1) + f(n-2));"
  , ":: f := fn(n) => var -> if(n < 2, n, f(n-1) + f(n-2));"
  , ":: f := fn(n) => lazy var -> if(n < 2, n, f(n-1) + f(n-2));"
  , ":: f := fn(var n) -> if(n < 2, n, f(n-1) + f(n-2));"
  , ":: f := fn(var n) => var -> if(n < 2, n, f(n-1) + f(n-2));"
  , ":: f := fn(var n) => lazy var -> if(n < 2, n, f(n-1) + f(n-2));"
  , ":: f := fn(lazy var n) -> if(n < 2, n, f(n-1) + f(n-2));"
  , ":: f := fn(lazy var n) => var -> if(n < 2, n, f(n-1) + f(n-2));"
  , ":: f := fn(lazy var n) => lazy var -> if(n < 2, n, f(n-1) + f(n-2));"
  , ":: f := fn(int n) => int -> if(n < 2, n, f(n-1) + f(n-2));"
  , "fun(int k) => int f := fn(int n) => int -> if(n < 2, n, f(n-1) + f(n-2));"
  , "fun(int n) => int f := fn(int n) => int -> if(n < 2, n, f(n-1) + f(n-2));"
  , "array[] => array[] => lazy double xs := [[1.0, 1.0 + uniform()],[2.0, 2.0 + uniform()] ]"
  , "array[] => array[] => lazy double xs := [[1.0, xs[0][0] + uniform()],[2.0, xs[1][0] + uniform()] ]"
  , ":: xs := [['1.0', 'xs[0][0] + uniform()'],['2.0', 'xs[1][0] + uniform()'] ]"
  ]

runTests :: IO ()
runTests = forM_ (zip [1..] tests) $ \(i,s) -> do
  putStrLn $ show i <> ". " <> s
  putStrLn $ parseAction s
  putStrLn ""


-----------------------------------------
-- Show instances
-----------------------------------------

-----------------------------------------
-- Eq instances
-----------------------------------------

