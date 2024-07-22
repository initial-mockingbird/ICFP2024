{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}

module Parser.Classic.QuickCheck where

import Debug.Trace (trace)
import Parser.Classic.ZillyParser
import Test.Framework.QuickCheckWrapper
import Text.Parsec.Pos
import Data.Coerce (coerce)

newtype IdentifierGen = IdentifierGen String deriving newtype Show

newtype ExprGen = ExprGen Expr deriving newtype Show
newtype TermGen = TermGen Term deriving newtype Show
newtype AtomGen = AtomGen Atom deriving newtype Show

newtype TypesGen = TypesGen Types deriving newtype Show
newtype Types0Gen = Types0Gen Types0 deriving newtype Show

newtype A0Gen = A0Gen A0 deriving newtype Show
newtype A1Gen = A1Gen A1 deriving newtype Show

arbitraryExpr :: Gen Expr
arbitraryExpr = fmap (coerce @ExprGen) arbitrary

arbitraryTerm :: Gen Term
arbitraryTerm = fmap (coerce @TermGen) arbitrary

arbitraryAtom :: Gen Atom
arbitraryAtom = fmap (coerce @AtomGen) arbitrary

arbitraryTypes :: Gen Types
arbitraryTypes = fmap (coerce @TypesGen) arbitrary

arbitraryTypes0 :: Gen Types0
arbitraryTypes0 = fmap (coerce @Types0Gen) arbitrary

arbitraryA0 :: Gen A0
arbitraryA0 = fmap (coerce @A0Gen) arbitrary

arbitraryA1 :: Gen A1
arbitraryA1 = fmap (coerce @A1Gen) arbitrary

arbitraryIdentifier :: Gen String
arbitraryIdentifier = fmap (coerce @IdentifierGen) arbitrary

arbitrarySourcePos :: Gen SourcePos
{- arbitrarySourcePos = do
  l <- arbitrary
  c <- arbitrary
  return $ newPos "" l c -}
arbitrarySourcePos = pure $ initialPos ""

instance Arbitrary IdentifierGen where
  arbitrary = IdentifierGen <$> sized (\n -> take (abs n + 1) <$> identifier)
    where
      firstChar = elements  $ '_' : ['a'..'z']
      rest = listOf . elements $ '_' : ['a'..'z'] <> ['0'..'9']
      identifier = liftA2 (:) firstChar rest

instance Arbitrary ExprGen where
  arbitrary = fmap ExprGen . frequency $ zip [1,1,4]
    [ Minus <$> arbitraryExpr<*> arbitraryTerm <*> arbitrarySourcePos
    , Less <$> arbitraryExpr<*> arbitraryTerm <*> arbitrarySourcePos
    , OfTerm <$> arbitraryTerm
    ]

instance Arbitrary TermGen where
  arbitrary = fmap TermGen . frequency $ zip [1,4]
    [ App <$> arbitraryTerm <*> arbitraryExpr <*> arbitrarySourcePos
    , OfAtom <$> arbitraryAtom
    ]
    --[OfAtom <$> arbitraryAtom]

instance Arbitrary AtomGen where
  arbitrary = fmap AtomGen . frequency $ zip [4,4,1,1,1,1,2]
    [ Val <$> arbitrary <*> arbitrarySourcePos
    , Var <$> arbitraryIdentifier <*> arbitrarySourcePos
    , Parens <$> arbitraryExpr <*> arbitrarySourcePos
    , Defer <$> arbitraryExpr <*> arbitrarySourcePos
    , Formula <$> arbitraryExpr <*> arbitrarySourcePos
    , IfThenElse <$> arbitraryExpr <*> arbitraryExpr <*> arbitraryExpr <*> arbitrarySourcePos
    --, Lambda <$> arbitraryIdentifier <*> arbitraryTypes <*> arbitraryExpr <*> arbitrarySourcePos 
    , Lambda <$> arbitraryIdentifier <*> pure (OfTypes0 . Z $ initialPos "") <*> arbitraryExpr <*> arbitrarySourcePos
    ]


instance Arbitrary TypesGen where
    arbitrary = fmap TypesGen . frequency $ zip [1,5]
      [ Arrow <$> arbitraryTypes0 <*> arbitraryTypes <*> arbitrarySourcePos
      , OfTypes0 <$> arbitraryTypes0
      ]


instance Arbitrary Types0Gen where
  arbitrary = fmap Types0Gen . frequency $ zip [4,1,1]
    [ Z <$> arbitrarySourcePos
    , Lazy <$> arbitraryTypes <*> arbitrarySourcePos
    , TParen <$> arbitraryTypes <*> arbitrarySourcePos
    ]

instance Arbitrary A0Gen where
  arbitrary = A0Gen <$> oneof
    [ Decl   <$> arbitraryTypes <*> arbitraryIdentifier     <*> arbitraryExpr <*> arbitrarySourcePos
    , Assign <$> arbitraryIdentifier      <*> arbitraryExpr <*> arbitrarySourcePos
    , Print  <$> arbitraryExpr  <*> arbitrarySourcePos
    ]

instance Arbitrary A1Gen where
  arbitrary = fmap A1Gen . frequency $ zip [1,4]
    [ Seq  <$> arbitraryA0 <*> listOf arbitraryA0
    , OfA0 <$> arbitraryA0
    ]

testExprParser :: Property
testExprParser = forAll arbitraryExpr $ \e ->
  case parseExpr (show e) of
    Left _ -> counterexample ("Can't Parse:\n" <> show e) False
    Right e' -> counterexample 
      "Showing and parsing aren't inverses" 
      (e == e')

props :: [Property]
props =
  [testExprParser]