

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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NoCUSKs #-}
{-# LANGUAGE NoNamedWildCards #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE BangPatterns #-}
--{-# LANGUAGE TypeAbstractions #-}


module ADT2 where

import Lensy2
import Control.Monad.IO.Class
import Data.Kind (Type)
import Data.Typeable hiding (cast)
import Control.Monad.Reader 
import Control.Monad
import Unsafe.Coerce (unsafeCoerce)
import ShowM
import Control.Applicative
import Data.Singletons.TH (genSingletons, promote, singletons, promoteEqInstances, singEqInstances, singDecideInstances)
import Prelude.Singletons (fromSing, withSomeSing, Sing, SingI(sing), singByProxy, withSing, demote, SomeSing (SomeSing))
import Data.Maybe.Singletons hiding (MapMaybe)
import Control.Applicative.Singletons
import Data.Eq.Singletons
import Data.Tuple.Singletons
import Data.Bool.Singletons
import Debug.Trace (trace)
import Data.Functor.Identity
import Data.Singletons.Decide
import Data.Either (fromRight)

$(singletons [d|
  infixr 0 :->
  data Types 
      = Value Types0
      | Lazy Types 
      | LazyS Types 
    deriving (Eq)

  data Types0 
    = Z
    | (:->) Types Types
    deriving (Eq)

  lowerBound' :: Types -> Types -> Maybe Types
  lowerBound' (Lazy a) (Lazy b) =  Lazy <$> lowerBound' a b
  lowerBound' (Value (a :-> b)) (Value (c :-> d)) =  Value <$> liftA2 (:->) (upperBound' a c ) (lowerBound' b d)
  lowerBound' (Value a) (Lazy b)  = lowerBound' (Value a) b
  lowerBound' (Lazy a)  (Value b) = lowerBound' a (Value b)
  lowerBound' (Value Z) (Value Z) = Just (Value Z)
  lowerBound' (Value Z) (Value (_ :-> _)) = Nothing
  lowerBound' (Value (_ :-> _)) (Value Z) = Nothing

  upperBound' :: Types -> Types -> Maybe Types
  upperBound' (Value (a :-> b)) (Value (c :-> d))  =  Value <$> liftA2 (:->) (lowerBound' a c) (upperBound' b d)
  upperBound' (Lazy a) (Lazy b)   =  Lazy <$> upperBound' a b
  upperBound' (Value a) (Lazy b)  =  Lazy <$> upperBound' (Value a) b
  upperBound' (Lazy a)  (Value b) =  Lazy <$> upperBound' a (Value b)
  upperBound' (Value Z) (Value Z) = Just (Value Z)
  upperBound' (Value Z) (Value (_ :-> _)) = Nothing
  upperBound' (Value (_ :-> _)) (Value Z) = Nothing

  |])

instance Show Types where
  showsPrec p = \case
    (Value a) -> showsPrec p a
    (Lazy a)  -> showString "Lazy <" . showsPrec p a . showString ">"
    (LazyS a) -> showString "Lazy* <" . showsPrec p a . showString ">"

instance Show Types0 where
  showsPrec p = \case
    Z -> showString "Z"
    (a :-> b) -> showParen (p > 0) $ showsPrec 1 a . showString " :-> " . showsPrec 0 b

{- deriving instance Show Types
deriving instance Show Types0 -}


{- type family (<:) (a :: Types) (b :: Types) :: Bool where
  a <: a = True
  Lazy a  <: Lazy b  = a <: b
  LazyS a <: LazyS b = a <: b
  Value Z <: Lazy b  = Value Z <: Lazy b
  Value (a :-> b) <: Value (c :-> d) = (c <: a) && (b <: d)
  a <: b = False -}

{-
(a :-> b) <: (c :-> d) 
= c <: a && b <: d

(c :-> d) <: (e :-> f)
= e <: c && d <: f

(a :-> b) <: (e :-> f)?
= e <: a && b <: f?

-}

infixr 0 ~>
type (~>) a b = Value (a :-> b)
--------------------------
-- Aux Functions
--------------------------



connector :: Int -> Bool
connector = (> 0)

rConnector :: Bool -> Int
rConnector = \case
  True -> 1
  False -> -1

cTrue :: (ShowM m env) => E env m (Value Z)
cTrue = Val (rConnector True)

cFalse :: (ShowM m env) => E env m (Value Z)
cFalse = Val (rConnector False)

cvalue :: (MonadReader env m, Alternative m) => LensyM' m env a -> m a
cvalue l = ask >>= viewyM' l
  

--------------------------
-- Types
--------------------------

type ADTContext m env =
  ( MonadIO m
  --, Interpreter m env
  , MonadReader env m
  , Alternative m
  )

type ShowMContextE m env =
  ( ShowM m env
  , forall a. ShowM m (E env m a)
  )

type Symbol = String


--------------------------
-- Classes
--------------------------

class SingI a => RValue (a :: Types) where
  type RValueT a :: Types
  rvalue :: 
    ( ADTContext m env
    , ShowMContextE m env
    , RValueT a ~ b
    , SingI b
    ) 
    => E env m a -> m (E env m b)


--------------------------
-- Expression language
--------------------------

{-| Zilly expression Language. |-}
data  E (env :: Type) (m :: Type -> Type) (a :: Types) where
  Val   :: ShowM m env
    => Int -> E env m (Value Z)
  Var   :: forall a m env. 
    ( ShowMContextE m env
    )
    => LensyM' m env (E env m a) -> E env m a
  Minus :: forall m (a :: Types) (b :: Types) env.
    ( RValue a
    , RValue b
    , RValueT a ~ Value Z
    , RValueT b ~ Value Z
    , ShowMContextE m env
    )
    => E env m a -> E env m b -> E env m (Value Z)
  Less ::
    ( RValue a 
    , RValue b
    , RValueT a ~ Value Z
    , RValueT b ~ Value Z
    , ShowMContextE m env
    )
    => E env m a -> E env m b -> E env m (Value Z)
  If    :: forall {c0 :: Types} {c1 :: Types} {x3 :: Types} (x1 :: Types) (x2 :: Types) (x0 :: Types) env m.
    ( RValue x0
    , RValue x1
    , RValue x2
    , RValueT x0 ~ Value Z
    , RValueT x1 ~ c0
    , RValueT x2 ~ c1
    , UpperBound' x1 x2 ~ Just x3
    , ShowMContextE m env
    )
    => E env m x0 -> E env m x1 -> E env m x2 -> E env m x3
  Subtyped :: forall a b m env. 
    ( UpperBound' a b ~ Just b
    , SingI a
    , SingI b
    , RValue a
    , RValue b
    ) 
    => E env m a -> E env m b
  Subtyped' :: forall (a :: Types) (b :: Types) m env. 
    ( UpperBound' (RValueT a) b ~ Just b
    , SingI a
    , SingI b
    , RValue a
    , RValue b
    ) 
    => E env m a -> E env m b
  Lambda  :: forall a b m env.
    ( RValue b
    , ShowMContextE m env
    , SingI b
    , SingI a
    )
    => LensyM' m env (E env m a) 
    -> E env m b 
    -> E env m (a ~> b)
  LambdaC ::
    ( RValue b
    , ShowM m (E env m b)
    , ShowM m env
    )
    => (env, LensyM' m env (E env m a), E env m b) 
    -> E env m (a ~> b)
  App :: forall f x b arg m env.
    ( RValue f
    , RValue x
    , RValueT f ~ (arg ~> b)
    , UpperBound' (RValueT x) arg ~ Just arg
    , SingI f
    , SingI x
    , SingI arg
    , SingI b
    , ShowMContextE m env
    )
    => E env m f -> E env m x -> E env m b

  Defer :: forall (a :: Types) env m (b :: Types).
    ( RValue a
    , RValueT a ~ b
    , SingI a
    , SingI b
    , ShowMContextE m env
    )
    => E env m a -> E env m (Lazy a)
  Formula :: 
    (

    ) => LensyM' m env (E env m a) -> E env m (Lazy a)
  FEval ::
    ( BaseType a ~ Value b
    , RValue a 
    , RValueT a ~ c
    --, ForceEvaluation a
    --, ForceEvaluation (Value b)
    ) => E env m a -> E env m (Value b) 
  Closure ::
    ( ShowMContextE m env
    )
    => (E env m a,env) -> E env m a
  ValueC :: 
    ( ShowM m env
    , ShowM m (E env m (Value a))
    ) 
    => (E env m (Value a), env) -> E env m (Value a)
  DeferS :: forall a c env m b.
    ( RValue a
    , RValue a ~ c
    , BaseType a ~ b
    , ShowMContextE m env
    --, ForceEvaluation c
    )
    => E env m a -> E env m (LazyS b) 

deriving instance Typeable (E env m a)




--------------------------
-- Aux type families
--------------------------

type family BaseType (x :: Types) :: Types where
  BaseType (Value a)  = (Value a)
  BaseType (Lazy a)   = BaseType a
  BaseType (LazyS a)  = BaseType a

type family LowerBound  (x :: Types) (y :: Types) :: Types where
  LowerBound (Lazy a) (Lazy b) = Lazy (LowerBound a b)
  LowerBound (Value (a :-> b)) (Value (c :-> d)) = Value ( UpperBound a c :-> LowerBound b d)
  LowerBound (Value a) (Lazy b)  = LowerBound (Value a) b
  LowerBound (Lazy a)  (Value b) = LowerBound a (Value b)
  LowerBound (Value a) (Value a) = Value a

type family UpperBound (x :: Types) (y :: Types) :: Types where
  UpperBound (Value (a :-> b)) (Value (c :-> d))  = Value ( LowerBound a c :-> UpperBound b d)
  UpperBound (Lazy a) (Lazy b)   = Lazy (UpperBound a b)
  UpperBound (Value a) (Lazy b)  = Lazy (UpperBound (Value a) b)
  UpperBound (Lazy a)  (Value b) = Lazy (UpperBound a (Value b))
  UpperBound (Value a) (Value a) = Value a



{- type family MapMaybe (f :: a -> b) (ma :: Maybe a) :: Maybe b where
  MapMaybe f (Just a) = Just (f a)
  MapMaybe f Nothing  = Nothing

type family AppMaybe (f :: a -> b -> c) (ma :: Maybe a) (mb :: Maybe b) :: Maybe c where
  AppMaybe f (Just a) (Just b) = Just (f a b)
  AppMaybe f _ _  = Nothing

type family LowerBound' (x :: Types) (y :: Types) :: Maybe Types where
  LowerBound' (Lazy a) (Lazy b) = MapMaybe Lazy (LowerBound' a b)
  LowerBound' (Value (a :-> b)) (Value (c :-> d)) = MapMaybe Value ( AppMaybe (:->) (UpperBound' a c)  (LowerBound' b d))
  LowerBound' (Value a) (Lazy b)  = LowerBound' (Value a) b
  LowerBound' (Lazy a)  (Value b) = LowerBound' a (Value b)
  LowerBound' (Value a) (Value a) = Just (Value a)
  LowerBound' _ _ = Nothing

type family UpperBound' (x :: Types) (y :: Types) :: Maybe Types where
  UpperBound' (Value (a :-> b)) (Value (c :-> d))  = MapMaybe Value ( AppMaybe (:->) (LowerBound' a c)  (UpperBound' b d))
  UpperBound' (Lazy a) (Lazy b)   = MapMaybe Lazy (UpperBound' a b)
  UpperBound' (Value a) (Lazy b)  = MapMaybe Lazy (UpperBound' (Value a) b)
  UpperBound' (Lazy a)  (Value b) = MapMaybe Lazy (UpperBound' a (Value b))
  UpperBound' (Value a) (Value a) = Just (Value a)
  UpperBound' _ _                 = Nothing -}

------------------------------------
-- Proofs regarding type families
------------------------------------

safeCoerce :: forall a b. (a ~ b) => a -> b
safeCoerce = unsafeCoerce

commute :: forall c0 c1 r x. (UpperBound c0 c1 ~ x) => (UpperBound c1 c0 ~ x => r) -> r
commute = unsafeCoerce

idempotency :: forall c0 r. (UpperBound c0 c0 ~ c0 => r) -> r
idempotency = unsafeCoerce

reflexivity :: forall c0 r. r -> (UpperBound c0 c0 ~ c0 => r)
reflexivity = unsafeCoerce

leftAssociate :: forall c0 c1 c2 r x. (UpperBound  c0 (UpperBound  c1 c2) ~ x) =>  (UpperBound  (UpperBound  c0 c1) c2 ~ x => r) -> r
leftAssociate = unsafeCoerce

lSubstitution :: forall a0 a1 b r x. (a0 ~ a1,UpperBound  a0 b ~ x) =>  (UpperBound a1 b ~ x => r) -> r
lSubstitution = unsafeCoerce

rSubstitution :: forall a0 a1 b r x. (a0 ~ a1,UpperBound  b a0 ~ x) =>  (UpperBound b a1 ~ x => r) -> r
rSubstitution = unsafeCoerce


labsortion :: forall  c0 c1 r x. (UpperBound  c0 (UpperBound  c0 c1) ~ x) => (UpperBound  c0 c1 ~ x => r) -> r
labsortion f = f' $ f'' f 
  where
    f' ::  (UpperBound  c0 (UpperBound  c0 c1) ~ x) => (UpperBound (UpperBound c0 c0) c1 ~ x => r) -> r
    f' = leftAssociate @c0 @c0 @c1 

    f'' :: UpperBound (UpperBound c0 c0) c1 ~ x => (UpperBound c0 c1 ~ x => r) -> r
    f'' = idempotency @c0 lSubstitution 

labsortion' :: forall c0 c1 r x. (UpperBound  c1 (UpperBound  c0 c1) ~ x) => (UpperBound  c0 c1 ~ x => r) -> r
labsortion' = f' . labsortion @c1 @c0 . commute @c1 @c0 
  where
    f' :: (UpperBound  c1 (UpperBound  c0 c1) ~ x) => (UpperBound  c1 (UpperBound  c1 c0) ~ x => r) -> r
    f' = commute @c1 @c0 rSubstitution

--------------------------
-- R-Value Instances
--------------------------



instance SingI a => RValue (Value a) where
  type RValueT (Value a) = Value a
  rvalue (Val n) = pure (Val n)
  rvalue (ValueC (e,gamma)) = localM (pure . const gamma) $ rvalue e
  rvalue (Minus a b) = (,) <$> rvalue a <*> rvalue b >>= \case
    (Val a', Val b') -> pure $ Val (a' - b')
    (a',b') ->  liftA2 Minus  (rvalue a') (rvalue b') >>= rvalue
  rvalue (Less a b) = (,) <$> rvalue a <*> rvalue b >>= \case
    (Val a', Val b') -> pure $ Val (rConnector $ a' < b')
    (a',b') -> liftA2 Less  (rvalue a') (rvalue b') >>= rvalue
  rvalue (App @f @x @b @arg f a) = rvalue f >>= \case
    LambdaC (gamma, x, t) -> withSingIRType @x $ do
      arg <- rvalue a >>= \rva -> case upcast'' @_ @arg rva of
        SameTypeUB rva'   -> pure rva'
        RightUB rva'      -> pure rva'
        LeftUB _       -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
      t'  <- localM (setyMF' x arg . const gamma) $ rvalue t
      gamma' <- setyMF' x arg gamma
      pure $ Closure (t',gamma')
      
    f' ->  rvalue $ App f' a
  rvalue x@(Var {}) = genRVar x
  rvalue e@(If {}) = genRVIf e
  rvalue (LambdaC gamma) = do 
    pure $ LambdaC gamma
  rvalue (Lambda x t) = do
    gamma <- ask
    pure $ LambdaC (gamma,x,t)
  rvalue (Closure (e,gamma)) = localM (pure . const gamma) $ rvalue e
  rvalue (FEval e) = undefined -- forceEvaluation e
  rvalue (Subtyped @e1 @e2 e1) = do
    
    e1' :: E env m (RValueT e1)  <- withSingIRType @e1 $ rvalue e1
    let e1'' :: E env m (RValueT e2) 
          = withRVType (sing @e1) 
          $ withSingIRType @e1
          $ withRVType (sing @(RValueT e1)) 
          $ rvaluePreservesST @e1 @e2 
          $ Subtyped @(RValueT e1) @(RValueT e2)  e1'
    pure e1''
  rvalue (Subtyped' @e1 @e2 e1) = do
    --trace "rvaluing a subtyped" pure ()
    e1' :: E env m (RValueT e1)  <- withSingIRType @e1 $ rvalue e1
    let e1'' :: E env m (RValueT e2) 
          = withRVType (sing @e1) 
          $ withSingIRType @e1
          $ withRVType (sing @(RValueT e1)) 
          $ rvaluePreservesST @(RValueT e1) @e2 
          $ Subtyped' @(RValueT e1) @(RValueT e2)  e1'
    pure e1''
  

-- | Lazy <a> are reduced to a
instance SingI a => RValue (Lazy (Value a)) where
  type RValueT (Lazy (Value a)) = Value a
  rvalue (Defer v) = do
    gamma <- ask 
    pure $ Closure (v,gamma)
  rvalue (App @f @x @b @arg f a) = rvalue f >>= \case
    LambdaC (gamma, x, t) -> withSingIRType @x $ do
      arg <- rvalue a >>= \rva -> case upcast'' @_ @arg rva of
        SameTypeUB rva'   -> pure rva'
        RightUB rva'      -> pure rva'
        LeftUB _       -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
      t'  <- localM (setyMF' x arg . const gamma) $ rvalue t
      gamma' <- setyMF' x arg gamma
      pure $ Closure (t',gamma')
      
      {- rvalue f >>= \case
    LambdaC _ (gamma, x, t) -> do
      arg <-  rvalue a
      t'  <- localM (setyMF' x arg . const gamma) $ rvalue t
      gamma' <- setyMF' x arg gamma
      rvalue $ Closure (t',gamma') -}
    f' ->  rvalue $ App f' a
  rvalue (Closure (e,gamma)) = localM (pure . const gamma) $ rvalue e
  rvalue x@(Var {}) = genRVar x
  rvalue e@(If {})  = genRVIf e
  rvalue (Formula v) = cvalue v
  rvalue (Subtyped @e1 @e2 e1) = do
    
    e1' :: E env m (RValueT e1)  <- withSingIRType @e1 $ rvalue e1
    let e1'' :: E env m (RValueT e2) 
          = withRVType (sing @e1) 
          $ withSingIRType @e1
          $ withRVType (sing @(RValueT e1)) 
          $ rvaluePreservesST @e1 @e2 
          $ Subtyped @(RValueT e1) @(RValueT e2)  e1'
    pure e1''
  rvalue (Subtyped' @e1 @e2 e1) = do
    
    e1' :: E env m (RValueT e1)  <- withSingIRType @e1 $ rvalue e1
    let e1'' :: E env m (RValueT e2) 
          = withRVType (sing @e1) 
          $ withSingIRType @e1
          $ withRVType (sing @(RValueT e1)) 
          $ rvaluePreservesST @(RValueT e1) @e2 
          $ Subtyped' @(RValueT e1) @(RValueT e2)  e1'
    pure e1''


instance SingI a => RValue (Lazy (Lazy a)) where
  type RValueT (Lazy (Lazy a)) = Lazy a
  rvalue (Defer v) = do
    gamma <- ask 
    pure $ Closure (v,gamma)
  rvalue (Var x) = rvalue <=< cvalue $ x
  rvalue (If cond t f) = genRVIf (If cond t f)
  rvalue (App f a) = rvalue (App f a)
  rvalue (Closure (e :: E env m (Lazy (Lazy a)), gamma)) = do 
    e' <- localM (pure . const gamma) $ rvalue e
    pure $ Closure (e',gamma)
  rvalue (Formula v) = cvalue v
  rvalue (Subtyped @e1 @e2 e1) = do
    e1' :: E env m (RValueT e1)  <- withSingIRType @e1 $ rvalue e1
    let e1'' :: E env m (RValueT e2) 
          = withRVType (sing @(Lazy a)) 
          $ withRVType (sing @e1) 
          $ withSingIRType @e1
          $ withRVType (sing @(RValueT e1)) 
          $ rvaluePreservesST @e1 @e2 
          $ Subtyped @(RValueT e1) @(RValueT e2)  e1'
    pure e1''
  rvalue (Subtyped' @e1 @e2 e1) = do
    
    e1' :: E env m (RValueT e1)  <- withSingIRType @e1 $ rvalue e1
    let e1'' :: E env m (RValueT e2) 
          = withRVType (sing @(Lazy a)) 
          $ withSingIRType @e1
          $ withRVType (sing @(RValueT e1)) 
          $ rvaluePreservesST @(RValueT e1) @(Lazy (Lazy a)) 
          $ Subtyped' @(RValueT e1) @(RValueT e2)  e1'
    pure e1''

instance SingI a => RValue (LazyS a) where 
  type RValueT (LazyS a) = LazyS a
  rvalue = undefined
  {- rvalue (DeferS @a' @c @_ @_ @b v) = rvaluePreservesBT @m @(E env m a') 
    $ DeferS <$> rvalue v
  rvalue (Var x) = rvalue <=< cvalue $ x
  rvalue _ = undefined -}







------------------------------
-- Generic R-Value Functions
------------------------------

genRVar :: (ADTContext m env, RValue a, RValueT a ~ c, SingI c) => E env m a -> m (E env m c)
genRVar (Var x) = rvalue <=< cvalue $ x
genRVar _ = undefined


genRVIf ::forall {x4 :: Types} m env (x3 :: Types) .
  ( ADTContext m env
  , ShowMContextE m env
  , SingI x4
  , RValue  x3
  , RValueT x3 ~ x4
  )
  => E env m x3 -> m (E env m x4)
genRVIf (If @x1 @x2 cond t f) 
  = withSingIRType @x1 
  $ withSingIRType @x2
  $ rvalue cond >>= \case
    Val (connector -> True) -> do 
      t' <- rvalue t
      case upcast'' @_ @x4 t' of
        SameTypeUB t'' -> pure t''
        RightUB t'' -> pure t''
        LeftUB _ -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
        NonExistentUB -> error "impossible case"
    Val (connector -> False) -> do 
      f' :: E env m c1 <- rvalue f
      case upcast'' @_ @x4 f' of
        SameTypeUB f'' -> pure f''
        RightUB f'' -> pure f''
        LeftUB _ -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
        NonExistentUB -> error "impossible case"
    c' -> rvalue (If @x1 @x2 @(Value Z) c' t f)
genRVIf _ = undefined




--------------------------
-- FEval 
--------------------------

class ForceEvaluation (a :: Types) where
  forceEvaluation :: 
    ( ADTContext m env
    , ShowMContextE m env
    , BaseType a ~ b
    ) => E env m a -> m (E env m b)

instance ForceEvaluation (Value Z) where
  forceEvaluation (Val n)        = pure $ Val n
  forceEvaluation (Var x)        = forceEvaluation <=< cvalue $ x
  forceEvaluation e@(Minus {})   = pure e
  forceEvaluation e@(Less {})    = pure e
  forceEvaluation e@(If {})      = forceEvaluation <=< genRVIf $ e
  forceEvaluation e@(App {})     = forceEvaluation <=< rvalue $ e
  forceEvaluation e@(FEval _)    = forceEvaluation <=< rvalue $ e
  forceEvaluation e@(Closure {}) = forceEvaluation <=< rvalue $ e
  forceEvaluation e@(ValueC {})  = forceEvaluation <=< rvalue $ e

instance ForceEvaluation (Lazy (Value Z)) where

  forceEvaluation (Formula v)    = forceEvaluation <=< cvalue $ v
  forceEvaluation (Var x)        = forceEvaluation <=< cvalue $ x
  forceEvaluation e@(If {})      = forceEvaluation <=< genRVIf $ e
  forceEvaluation e@(App {})     = forceEvaluation <=< rvalue $ e
  forceEvaluation e@(Closure {}) = forceEvaluation <=< rvalue $ e
  forceEvaluation (Defer v)      = forceEvaluation v
  

instance (SingI a, ForceEvaluation (Lazy a)) => ForceEvaluation (Lazy (Lazy a)) where
  forceEvaluation (Formula v)    = forceEvaluation <=< cvalue $ v
  forceEvaluation (Var x)        = forceEvaluation <=< cvalue $ x
  forceEvaluation e@(If {})      = forceEvaluation <=< genRVIf $ e
  forceEvaluation e@(App {})     = forceEvaluation <=< rvalue $ e
  forceEvaluation e@(Closure {}) = forceEvaluation <=< rvalue $ e
  forceEvaluation (Defer v)      = forceEvaluation v


instance SingI a => ForceEvaluation (LazyS a) where
  {- forceEvaluation (DeferS @_ @c @_ @_ @b v)     = do
    v' <- rvalue v
    case eqT @(BaseType c) @b of
      Nothing -> undefined
      Just Refl -> forceEvaluation  v' -}
  forceEvaluation (Var x)        = forceEvaluation <=< cvalue $ x
  forceEvaluation e@(If {})      = forceEvaluation <=< genRVIf $ e
  forceEvaluation e@(App {})     = forceEvaluation <=< rvalue $ e
  forceEvaluation e@(Closure {}) = forceEvaluation <=< rvalue $ e
 






--------------------------
-- Singletons
--------------------------

rvalueT :: Types -> Types
rvalueT t = case t of
  (Value a) -> Value a
  (Lazy a)  -> a
  (LazyS a) -> LazyS a


withTypeableType0 :: forall (z :: Types0) r.  Sing z -> (Typeable  z => r) -> r
withTypeableType0 SZ  f = f
withTypeableType0 (z1 :%-> z2) f = withTypeableType z1 $ withTypeableType z2 f

withTypeableType :: forall (z :: Types) r. Sing z -> (Typeable  z => r) -> r
withTypeableType (SValue v) f = case v of
  (SZ :: Sing (x :: Types0)) -> f
  (z1 :%-> z2) -> withTypeableType z1 $ withTypeableType z2 f
withTypeableType (SLazy t) f = withTypeableType t f
withTypeableType _ _ = error "Lazy* not supported"

withShow :: forall (z :: Types). SingI z => String
withShow = show $ fromSing (sing @z) 


withSingIType :: forall (z :: Types) r. Sing z -> (SingI  z => r) -> r
withSingIType (SValue v) f = case v of
  (SZ :: Sing (x :: Types0)) -> f
  (z1 :%-> z2) -> withSingIType z1 $ withSingIType z2 f
withSingIType (SLazy t) f = withSingIType t f
withSingIType _ _ = error "Lazy* not supported"

withSingIType0 :: forall (z :: Types0) r. Sing z -> (SingI  z => r) -> r
withSingIType0  v f = case v of
  (SZ :: Sing (x :: Types0)) -> f
  (z1 :%-> z2) -> withSingIType z1 $ withSingIType z2 f


withRVType :: forall (z :: Types) r. Sing z -> (RValue z => r) -> r
withRVType (SValue v) f = case v of
  (SZ :: Sing (x :: Types0)) -> f
  (z1 :%-> z2) -> withRVType z1 $ withRVType z2 f
withRVType (SLazy  (SLazy s)) f = withRVType s f
withRVType (SLazy (SValue s)) f = withSingIType0 s $ withRVType (SValue s) f
withRVType _ _ = error "Lazy* not supported"


withBVType :: forall (z :: Types) r. SingI z => (SingI  (BaseType z) => r) -> r
withBVType f = case sing @z of
  (SValue @n _) -> case decideEquality' @_ @(Value n) @(BaseType z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) -> withSingIType @n sa $ withBVType @n $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) -> withSingIType @n sa $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented"

withSingIRType :: forall (z :: Types) r. SingI z => (SingI  (RValueT z) => r) -> r
withSingIRType f = case sing @z of
  (SValue @n _) -> case decideEquality' @_ @(Value n) @(RValueT z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) -> withSingIType @n sa $ case decideEquality' @_ @(RValueT z) @n of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) -> withSingIType @n sa $ case decideEquality' @_ @(RValueT z) @n of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented"

withSingIUBType :: forall (z0 :: Types) (z1 :: Types) r. 
  ( SingI z0
  , SingI z1
  ) => (SingI  (UpperBound' z0 z1) => r) -> r
withSingIUBType f = case sUpperBound' (sing @z0) (sing @z1) of
  SJust ub -> withSingIType ub f
  SNothing -> f

withSingILBType :: forall (z0 :: Types) (z1 :: Types) r. 
  ( SingI z0
  , SingI z1
  ) => (SingI  (LowerBound' z0 z1) => r) -> r
withSingILBType f = undefined 



withBVType' :: forall (z :: Types) r. Sing z -> (SingI  (BaseType z) => r) -> r
withBVType' z f= case z of
  (SValue @n _) -> withSingIType z $ case decideEquality' @_ @(Value n) @(BaseType z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) -> withSingIType @n sa $ withBVType @n $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl ->  f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) -> withSingIType @n sa $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented"

{- withKnownUpcast :: forall (a :: Types) (b :: Types) (c :: Types) env m.
  ( SingI a 
  , SingI b
  , SingI c
  , UpperBound' a b ~ Just c
  ) 
  => E env m a 
  -> E env m c
withKnownUpcast f = case upcast @a @b f of
  Left Refl -> error "Type mismatch"
  Right (MkSome f') -> f' -}
  

upcast :: forall (a :: Types) (b :: Types) env m. 
  ( SingI a
  , SingI b
  ) => E env m a 
  -> Either 
    ( UpperBound' a b :~: Nothing )
    (Some (E env m) a b)
upcast f 
  = withSingIUBType @a @b 
  $ case sing @(UpperBound' a b) of
    SJust sub -> case decideEquality (sing @a) sub of
      (Just Refl) ->  Right 
        $ MkSome @a @b f
      Nothing ->  Right 
        $ withRVType (sing @a)
        $ rvalueIsPred @a
        $ withSingIType sub
        $ MkSome @a @b
        $ Subtyped' f
    SNothing  -> Left Refl

data UpperBoundResults a b env m where
  NonExistentUB   :: (UpperBound' a b ~ Nothing) => UpperBoundResults a b env m
  SameTypeUB      :: (a ~ b, UpperBound' a b ~ Just a) => E env m a -> UpperBoundResults a b env m
  LeftUB          :: (UpperBound' a b ~ Just a)  => E env m a  -> UpperBoundResults a b env m
  RightUB         :: (UpperBound' a b ~ Just b)  => E env m b  -> UpperBoundResults a b env m
  SomethingElseUB :: forall {r :: Types} (a :: Types) (b :: Types) env m. 
    ( UpperBound' a b ~ Just r
    , SingI r
    ) => E env m r -> UpperBoundResults a b env m

data UpperBoundResults' a b env m where
  NonExistentUB'   :: (UpperBound' a b ~ Nothing) => UpperBoundResults' a b env m
  SameTypeUB'      :: (a ~ b, UpperBound' a b ~ Just a) => UpperBoundResults' a b env m
  LeftUB'          :: (UpperBound' a b ~ Just a)  => UpperBoundResults' a b env m
  RightUB'         :: (UpperBound' a b ~ Just b)  => UpperBoundResults' a b env m
  SomethingElseUB' :: forall {r :: Types} (a :: Types) (b :: Types) env m. 
    ( UpperBound' a b ~ Just r
    , SingI r
    ) => UpperBoundResults' a b env m


upcastable :: forall (a :: Types) (b :: Types) env m. 
  ( SingI a
  , SingI b
  ) => UpperBoundResults' a b env m
upcastable 
  = withSingIUBType @a @b 
  $ case decideEquality (sing @a) (sing @b) of
    Just Refl -> ubIsReflexive @a $ SameTypeUB'
    Nothing -> case sing @(UpperBound' a b) of
      SJust sub -> case decideEquality (sing @a) sub of
        Just Refl -> LeftUB'
        Nothing   -> case decideEquality (sing @b) sub of
          Just Refl -> RightUB'
          Nothing   
            -> withRVType (sing @a)
            $ rvalueIsPred @a
            $ withSingIType sub 
            $ SomethingElseUB' @a @b
      SNothing  -> NonExistentUB'

upcast'' :: forall (a :: Types) (b :: Types) env m. 
  ( SingI a
  , SingI b
  ) => E env m a 
  -> UpperBoundResults a b env m
upcast'' f 
  = withSingIUBType @a @b 
  $ either (\Refl -> NonExistentUB) id
  $ (upcast @a @b) f >>= \case
    MkSome !f' -> case sing @(UpperBound' a b) of
      SJust !r -> case  (decideEquality r (sing @a), decideEquality r (sing @b)) of
        (Nothing,Nothing) -> pure 
          $ SomethingElseUB @a @b @env @m 
          $ subtyped'CTX @a @b 
          $ withRVType r
          $ Subtyped'  f'
        (Just Refl,Just Refl) 
          ->  pure 
          $ SameTypeUB @a @b @env @m 
          $  f'
        (Just Refl,_)
          -> pure 
          $ LeftUB @a @b @env @m 
          $ f'
        (_,Just Refl)
          ->  pure 
          $ RightUB @a @b @env @m 
          $ subtyped'CTX @a @b 
          $ Subtyped' f'

data AtLeastOne f a b = AL (f a) | AR (f b) | AB (f a) (f b)

data Some (f :: Types -> Type) (a :: Types) (b :: Types) where
  MkSome :: forall {r :: Types} a b f. (SingI a,SingI b,SingI r, UpperBound' a b ~ Just r) => f a -> Some f a b

data Some2 (f :: Types -> Types -> Type) (a :: Types) (b :: Types) where
  MkSome2 :: forall {r :: Types} a b f. 
    ( SingI a
    , SingI b
    , SingI r
    , UpperBound' a b ~ Just r
    ) => f a b -> Some2 f a b

upcast' :: forall (a :: Types) (b :: Types) env m. 
  ( SingI a
  , SingI b
  --, UpperBound' a b ~ UpperBound' b a
  ) => AtLeastOne (E env m) a b
  -> Either 
    (UpperBound' a b :~: Nothing) 
    (Some2 (AtLeastOne (E env m)) a b)
upcast' (AL f) = upcast @a @b f >>= \case
  MkSome f' -> Right . MkSome2 @a @b . AL $ f'
upcast' (AR f) = upperBoundIsCommutative @a @b 
  $ upcast @b @a f >>= \case
  MkSome f' -> Right . MkSome2 @a @b . AR $ f'
upcast' (AB fl fr) = upperBoundIsCommutative @a @b $ do
  MkSome fl' <- upcast @a @b fl
  MkSome fr' <- upcast @b @a fr
  pure . MkSome2 @a @b $ AB fl' fr'

decideEquality' :: forall k (a :: k) (b :: k).  (SDecide k, SingI a, SingI b) => Maybe (a :~: b) 
decideEquality' = decideEquality (sing @a) (sing @b)
--------------------------
-- Subtyping
--------------------------

rvalueIsPred :: forall (a :: Types) c.
  ( SingI a --RValue a 
  )
  => (UpperBound' (RValueT a) a ~ Just a => c) -> c
rvalueIsPred !f = case withSingIRType @a $ withSingIUBType @(RValueT a) @a $ decideEquality (sing @(UpperBound' (RValueT a) a )) (sing @(Just a)) of
  Just Refl -> f
  Nothing -> error "impossible case"

upperBoundIsCommutative :: forall (a :: Types) (b :: Types) cont.
  ( SingI a
  , SingI b
  )
  => ((UpperBound' a b ~ UpperBound' b a) => cont) -> cont
upperBoundIsCommutative f 
  = withSingIUBType @a @b 
  $ withSingIUBType @b @a 
  $ case decideEquality (sing @(UpperBound' a b)) (sing @(UpperBound' b a)) of
  Just Refl -> f
  Nothing -> error "impossible case"

upperBoundIsTransitive 
  :: forall {r0 :: Types} {r1 :: Types} {r2 :: Types} a b c cont.
  ( UpperBound' a b ~ Just r0
  , UpperBound' b c ~ Just r1 
  )
  => (UpperBound' a c ~ Just r2 => cont) -> cont
upperBoundIsTransitive = unsafeCoerce


upperBoundIsTransitive'
  :: forall {r0 :: Types} a b c cont.
  ( UpperBound' a b ~ Just b
  , UpperBound' b c ~ Just r0
  , SingI r0
  , SingI a
  , SingI c
  )
  => (UpperBound' a c ~ Just r0 => cont) -> cont
upperBoundIsTransitive' !f = withSingIUBType @a @c $ case decideEquality (sing @(UpperBound' a c)) (sing @(Just r0)) of
  Just Refl -> f
  Nothing -> error "impossible case"

rvaluePreservesST :: forall {r0 :: Types} a b cont. 
  ( SingI a
  , SingI b
  , SingI r0
  , UpperBound' a b ~ Just r0) 
  => (UpperBound' (RValueT a) (RValueT b) ~ Just (RValueT r0) => cont) -> cont
rvaluePreservesST f
  = withSingIRType @a 
  $ withSingIRType @b 
  $ withSingIRType @r0 
  $ withSingIUBType @(RValueT a) @(RValueT b)
  $ case decideEquality (sing @(UpperBound' (RValueT a) (RValueT b))) (sing @(Just (RValueT r0)))of
    Just Refl -> f
    Nothing -> error "impossible case"

ubIsReflexive :: forall (a :: Types) cont.
  (SingI a)
  => (UpperBound' a a ~ Just a => cont) -> cont
ubIsReflexive !f = withSingIUBType @a @a $ case decideEquality (sing @(UpperBound' a a)) (sing @(Just a)) of
  Just Refl -> f
  Nothing -> error "impossible case"

ubIsIdempotent :: forall {r0 :: Types} (a :: Types) (b :: Types) cont.
  ( UpperBound' a b ~ Just r0 
  , SingI a
  , SingI b
  , SingI r0
  ) 
  => (UpperBound' a r0 ~ Just r0 => cont) -> cont
ubIsIdempotent !f =  withSingIUBType @a @r0 $  case decideEquality (sing @(UpperBound' a r0 )) (sing @(Just r0)) of
  Just Refl -> f
  Nothing -> error "impossible case"

subtyped'CTX :: forall {r :: Types} (a :: Types) (b :: Types) cont.
  ( SingI a
  , SingI b
  , SingI r
  , UpperBound' a b ~ 'Just r
  ) => ((UpperBound' (RValueT a) r ~ 'Just r, RValue a, RValue b) => cont) -> cont
subtyped'CTX f 
  = withSingIRType @a
  $ withSingIRType @b
  $ withRVType (sing @a)
  $ withRVType (sing @b)
  $ rvalueIsPred @a
  $ ubIsIdempotent @a @b
  $ upperBoundIsTransitive' @(RValueT a) @a @r
  $ f




{- rvaluePreservesST :: forall {r0 :: Types} a b r. 
  (UpperBound' a b ~ Just r) 
  => (RValueT a <: RValueT b ~ True => r) -> r
rvaluePreservesST = unsafeCoerce

rvaluePreservesST' :: forall a b r. 
  (a <: b ~ True) 
  => (RValueT a <: b ~ True => r) -> r
rvaluePreservesST' = unsafeCoerce


lazyPreservesST :: forall a b r. 
  (a <: b ~ True) 
  => (Lazy a <: Lazy b ~ True => r) -> r
lazyPreservesST = unsafeCoerce

lazySPreservesST :: forall a b r. 
  (a <: b ~ True) 
  => (LazyS a <: LazyS b ~ True => r) -> r
lazySPreservesST = unsafeCoerce

functionST :: forall a b c d r.
  ( c <: a ~ True
  , b <: d ~ True
  ) => ((a ~> b) <: (c ~> d) ~ True => r) -> r 
functionST = unsafeCoerce -}




lazyRT :: forall a r. SingI a => (RValueT (Lazy a) ~ a => r) -> r
lazyRT f = case sing @a of
  sl@(SLazy @n _)  -> f
  sv@(SValue @n _) -> f
  sls@(SLazyS _) -> error "Lazy* not implemented"
