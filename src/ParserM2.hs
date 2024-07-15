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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant <$>" #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}

module ParserM2 where




import Parser (Type0(..),Type(..),Expr(..),Term(..),Atom(..),A1(..),A0(..),Phantom(..),NoVarInfo,VarInfo,parseAction,parseFile, parseExpr)
import Control.Monad.Reader
import Data.Map (Map)
import Data.Map qualified as M
import ADT2 qualified as A
import Prelude.Singletons hiding (Map)
import ADT2 ( type (~>), STypes0((:%->)),Types0((:->)) ) 
import Interpreter2
import Data.Type.Equality
import TypedMap2
import Action2
import Debug.Trace (trace)
import Data.Functor.Identity (Identity(..))
import Data.Singletons.Decide 
import Control.Monad (foldM)
import Interpreter2
import ShowM
import GHC.IO (unsafePerformIO)

type Gamma = Map String A.Types

varType :: MonadReader Gamma m => String -> m A.Types
varType s = asks (M.! s)

data Some f where
  MkSome :: SingI a => f a -> Some f

class BuildAST a where
  buildAST ::  
    (MonadReader Gamma m
    )
    => a -> m (Some (A.E Env BaseInterpreter))

instance BuildAST (Expr NoVarInfo) where
  buildAST (OfTerm t) = buildAST t
  buildAST (Minus e1 t2) = do
    MkSome @se1' e1' <- buildAST e1
    MkSome @st2' t2' <- buildAST t2
    case (sing @se1', sing @st2') of
      (A.SValue A.SZ, A.SValue A.SZ) -> pure . MkSome $ A.Minus e1' t2'
      _ -> error "type mismatch"

  buildAST (Less e1 t2) = do
    MkSome @se1' e1' <- buildAST e1
    MkSome @st2' t2' <- buildAST t2
    case (sing @se1', sing @st2') of
      (A.SValue A.SZ, A.SValue A.SZ) -> pure . MkSome $ A.Less e1' t2'
      _ -> error "type mismatch"


instance BuildAST (Term NoVarInfo) where
  buildAST :: forall m. MonadReader Gamma m => Term NoVarInfo -> m (Some (A.E Env BaseInterpreter))
  buildAST (OfAtom t) = buildAST t
  buildAST (App f t) = do
    MkSome @sf' f' <- buildAST f
    MkSome @st' t' <- buildAST t
    case (sing @sf') of
      (A.SValue ((arg :: Sing arg) :%-> (ret :: Sing ret))) 
        -> A.withSingIRType @st' 
        $ A.withSingIType arg
        $ A.withSingIType ret
        $ A.withRVType (sing @st')
        $ case A.upcastable @(A.RValueT st') @arg @Env @BaseInterpreter of
          A.NonExistentUB' -> error "type mismatch"
          A.SameTypeUB'
            -> pure 
            $ MkSome @ret
            $ A.withRVType (A.SLazy arg)
            $ A.lazyRT @arg 
            $ A.App @(A.Value (arg :-> ret)) @st' @ret @arg f' t'
          A.RightUB' 
            -> pure 
            $ MkSome @ret
            $ A.withRVType (A.SLazy arg)
            $ A.lazyRT @arg 
            $ A.App @(A.Value (arg :-> ret)) @st' @ret @arg f' t'
          A.LeftUB' -> error "type mismatch"
          A.SomethingElseUB' -> error "type mismatch" 
      s -> error $ "type mismatch, got: " <> show (fromSing s)
      -- _ -> error "type mismatch" 


instance BuildAST (Atom NoVarInfo) where
  buildAST (Val n) = pure . MkSome . A.Val $ n
  buildAST (Parens t) = buildAST t
  buildAST (Var s _) = toSing <$> varType s >>= \case
    SomeSing @_ @sv sv -> A.withSingIType sv $ pure . MkSome . A.Var $ mkVar @sv @BaseInterpreter s
  buildAST (Defer t) = do
    MkSome @st' t' <- buildAST t
    pure . MkSome $ A.withRVType (sing @st') $ A.withSingIRType @st' $ A.Defer t'
  buildAST (IfThenElse e1 e2 e3) = do
    MkSome @se1' e1' <- buildAST e1
    MkSome @se2' e2' <- buildAST e2
    MkSome @se3' e3' <- buildAST e3
    A.withSingIUBType @se2' @se3'
      $ A.withRVType (sing @se1')
      $ A.withRVType (sing @se2')
      $ A.withRVType (sing @se3')
      $ A.withSingIRType @se1'
      $ case (A.upcast' @se2' @se3' (A.AB e2' e3'), decideEquality (sing @(A.RValueT se1'))  (sing @(A.Value A.Z))) of
        (_,Nothing)     -> error "type mismatch"
        (Left Refl,_)   -> error "type mismatch"
        (Right (A.MkSome2 (A.AB l r)), Just Refl) 
          -> pure . MkSome $ A.If e1' l r
        _ -> error "impossible case"
  buildAST (Formula t) = buildAST t >>= \case 
    MkSome (A.Var t') -> pure . MkSome $  A.Formula t'
    _ -> error "type mismatch"
  buildAST (Lambda s t e) = local (M.insert s $ f t) $ do
    MkSome @st' e' <-  buildAST e
    toSing <$> varType s >>= \case
      SomeSing @_ @sv sv -> A.withSingIType sv 
        $ A.withSingIRType @st'
        $ pure . MkSome 
        $ A.withRVType (sing @st') 
        $ A.Lambda (mkVar @sv @BaseInterpreter s) e'
    

f :: Type -> A.Types
f (Arrow t0 t1) = A.Value $ g t0 :-> f t1
f (OfType0 t0) = g t0

g :: Type0 -> A.Types
g Int'       = A.Value A.Z
g (Lazy t1)  = A.Lazy (f t1)
g (LazyS t1) = A.LazyS (f t1)





class TypeCheck a where
  tc ::  
    ( MonadReader Gamma m
    --, forall (x :: A.Types). SingI x
    --, forall (x :: A.Types). A.RValue x
    )
    => a -> m (A Env BaseInterpreter '(),Gamma) 

{- instance SingI () where
  sing = S() --sing @'() -}

instance TypeCheck (A1 NoVarInfo) where
  tc (OfA0 t)    = tc t
  tc (Seq t1 t0) = undefined

instance TypeCheck (A0 NoVarInfo) where
  tc (Decl t var e) = do
    let t' = f t
        rt = A.rvalueT t'
    gamma' <- asks (M.insert var rt)
    MkSome @se' e' <- local (const gamma') $ buildAST e
    trace ("se': " <> (show $ fromSing $ sing @se')) pure ()
    
    case toSing t' of
      SomeSing @_ @st st 
        -> A.withSingIType st 
        $ A.withRVType (sing @se')
        $ A.withSingIRType @se'
        $ A.withRVType (sing @st)
        $ A.withSingIRType @st
        $ A.withRVType (sing @(A.RValueT st))
        $ A.withSingIRType @(A.RValueT st)
        -- (Ltype e = st) <=> (e ^ st = st)
        $ case A.upcast'' @se' @st e' of -- change se' to RValueT se' and change assumptions
          A.NonExistentUB -> error "type mismatch"
          A.SameTypeUB x' -> A.rvaluePreservesST @se' @st $ pure (mkVar @st @BaseInterpreter var :=  x',gamma')
          A.LeftUB x'     -> error "type mismatch"
          A.RightUB !x'   
            -> A.rvaluePreservesST @se' @st 
            $  A.upperBoundIsCommutative @(A.RValueT se') @(A.RValueT st)
            $ do
              !(x'',gamma'') <- pure (mkVar @st @BaseInterpreter var := e',gamma')
              {- let x = runReaderT (runBI (showM x')) empty >>= putStrLn
                  !y = unsafePerformIO (putStrLn "printing x">>x) -}
              pure (x'',gamma'')
          A.SomethingElseUB x' -> error "type mismatch"
  tc (Assign var _ e) = do 
    gamma' <- ask
    t' <- varType var
    MkSome @se' e' <- local (M.insert var t') $ buildAST e
    case toSing t' of
      SomeSing @_ @st st 
        -> A.withSingIType st 
        $ A.withRVType (sing @se')
        $ A.withSingIRType @se'
        $ A.withRVType (sing @st)
        $ A.withSingIRType @st
        $ case A.upcast'' @se' @st e' of
          A.NonExistentUB -> error "type mismatch"
          A.SameTypeUB x' -> pure (mkVar @st @BaseInterpreter var :=. x',gamma')
          A.LeftUB x'     -> error "type mismatch"
          A.RightUB x'    -> A.ubIsReflexive @st $ pure (mkVar @st @BaseInterpreter var :=. x',gamma')
          A.SomethingElseUB x' -> error "type mismatch"
  tc (Parser.Print e) = do
    gamma' <- ask
    MkSome @se' e' <-  buildAST e
    A.withRVType (sing @se')
      $ A.withSingIRType @se'
      $ pure (Action2.Print e',gamma')

transformAndPrint' :: Expr NoVarInfo -> IO ()
transformAndPrint' t = runReaderT (buildAST t) M.empty >>= \case
  MkSome @st e -> A.withSingIRType @st 
    $  A.withRVType (sing @st) 
    $  runReaderT (runBI $ A.rvalue e) empty 
    >>= printProgram

transformAndPrint :: Expr NoVarInfo -> IO ()
transformAndPrint t = runReaderT (buildAST t) M.empty >>= \case
  MkSome e -> printProgram e

interpretProgram :: FilePath -> IO ()
interpretProgram fp = do
  contents <- lines <$> readFile fp
  (_,as) <- case traverse parseAction contents of
    Left e -> error $ show e
    Right actions -> flip (`foldM` (M.empty,[])) actions $ \(gamma,as) a -> do 
      (r, gamma') <- runReaderT (tc a) gamma
      pure (gamma',r:as)
  putStrLn "finished typechecking"
  printAndExec $ reverse as
  pure ()
ex1 :: String
ex1 = "1 - 2 "

ex2 :: String
ex2 = "1 - 2 - 3"

ex3 :: String
ex3 = "((1 - 2) - 3)"

ex4 :: String
ex4 = "1 - (2 - 3)"

ex5 :: String
ex5 = "(/. x : Int => x - 1)(5)"

ex6 :: String
ex6 = "'5'"

ex7 :: String
ex7 = "1 - ''5''"

ex8 :: String
ex8 = "1 - '5'"

ex9 :: String
ex9 = "(/. x : Lazy<Int> => x)(5)"

ex10 :: String
ex10 = "(/. x : Lazy<Lazy<Int>> => x)(5)"

ex11 :: String
ex11 = "(/. x : Lazy<Lazy<Lazy<Int>>> => x)(5)"

ex12 :: String
ex12 = "(/. x : Lazy<Lazy<Lazy<Int>>> => x)('5')"

pex1 :: IO ()
pex1 = case parseExpr ex1 of
  Left e -> error $ show e
  Right e -> transformAndPrint e

pex1' :: IO ()
pex1' = case parseExpr ex1 of 
  Left e -> error $ show e
  Right e -> transformAndPrint e

pex2 :: IO ()
pex2 = case parseExpr ex2 of
  Left e -> error $ show e
  Right e -> transformAndPrint e

pex3 :: IO ()
pex3 = case parseExpr ex3 of
  Left e -> error $ show e
  Right e -> transformAndPrint e

pex4 :: IO ()
pex4 = case parseExpr ex4 of
  Left e -> error $ show e
  Right e -> transformAndPrint e

pex5 :: IO ()
pex5 = case parseExpr ex5 of
  Left e -> error $ show e
  Right e -> transformAndPrint e 

pex6 :: IO ()
pex6 = case parseExpr ex6 of
  Left e -> error $ show e
  Right e -> transformAndPrint e 

pex7 :: IO ()
pex7 = case parseExpr ex7 of
  Left e -> error $ show e
  Right e -> transformAndPrint e 

pex8 :: IO ()
pex8 = case parseExpr ex8 of
  Left e -> error $ show e
  Right e -> transformAndPrint e 

pex9 :: IO ()
pex9 = case parseExpr ex9 of
  Left e -> error $ show e
  Right e -> transformAndPrint e

pex10 :: IO ()
pex10 = case parseExpr ex10 of
  Left e -> error $ show e
  Right e -> transformAndPrint e 

pex11 :: IO ()
pex11 = case parseExpr ex11 of
  Left e -> error $ show e
  Right e -> transformAndPrint e 

pex12 :: IO ()
pex12 = case parseExpr ex12 of
  Left e -> error $ show e
  Right e -> transformAndPrint e 