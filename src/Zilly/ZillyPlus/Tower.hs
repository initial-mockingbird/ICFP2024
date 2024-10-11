{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleContexts      #-}

module Zilly.ZillyPlus.Tower where

import Zilly.ADT.ExpressionPlus
import Zilly.ADT.Error 
import Zilly.ADT.Array 
import Zilly.ADT.Arithmetic 

import Zilly.ZillyPlus.Expression
import Zilly.ZillyPlus.Error 
import Zilly.ZillyPlus.Array 
import Zilly.ZillyPlus.Arithmetic 
import Zilly.ZillyPlus.Interpreter
import Utilities.LensM
import Utilities.TypedMapPlus
import Data.Proof
import Zilly.RValuePlus
import Zilly.Types
import Utilities.ShowM
import Data.Singletons (SingI, sing, withSingI, Sing)
import Data.Coerce 

newtype ET a = ETower (E Void2 ErrorT  ExprTag a)

newtype ErrorT a = ErrorT (Error ET ArrayT ErrorTag a)

newtype ArrayT a = ArrayT (ArrayE ErrorT ArithmeticT ArrayTag a)

newtype ArithmeticT a = ArithmeticT (Arithmetic ArrayT Void2 ArithmeticTag a)

instance RValue Void2 a where
  type RVCtx Void2 = RVCtx (E Void2 ErrorT ExprTag)

instance Functor m => ShowM m (Void2 a)

type instance Gamma (TaggedInterpreter ExprTag)       = TypeRepMap ErrorT ExprTag
type instance Gamma (TaggedInterpreter ErrorTag)      = Gamma (TaggedInterpreter ExprTag) 
type instance Gamma (TaggedInterpreter ArrayTag)      = Gamma (TaggedInterpreter ExprTag) 
type instance Gamma (TaggedInterpreter ArithmeticTag) = Gamma (TaggedInterpreter ExprTag) 

--------------------------------------------------------------------

instance  RValue ET (Value a)  where 
  type RVCtx ET = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ETower a) = ETower <$> rvalue a

instance SingI (Array a) => RValue ET (Array a)  where 
  type RVCtx ET = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ETower a) = withSingIRType @(Array a) $ ETower <$> rvalue a 

instance SingI (Lazy a) => RValue ET (Lazy a)  where 
  type RVCtx ET = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ETower a) = case sing @(Lazy a) of 
    SLazy sa -> withSingI sa $ case sing @a of
      SValue _ -> ETower <$> rvalue a
      SArray _ -> ETower <$> rvalue a
      SLazy  _ -> ETower <$> rvalue a
      SLazyS _ -> ETower <$> rvalue a


instance  RValue ET (LazyS a)  where 
  type RVCtx ET = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ETower a) = ETower <$> rvalue a 

---------------------------------------------------------------------


instance  RValue ErrorT (Value a)  where 
  type RVCtx ErrorT = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ErrorT a) = ErrorT <$> rvalue a

instance SingI (Array a) => RValue ErrorT (Array a)  where 
  type RVCtx ErrorT = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ErrorT a) = withSingIRType @(Array a) $ ErrorT <$> rvalue a 

instance SingI (Lazy a) => RValue ErrorT (Lazy a)  where 
  type RVCtx ErrorT = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ErrorT a) = case sing @(Lazy a) of 
    SLazy sa -> withSingI sa $ case sing @a of
      SValue _ -> ErrorT <$> rvalue a
      SArray _ -> ErrorT <$> rvalue a
      SLazy  _ -> ErrorT <$> rvalue a
      SLazyS _ -> ErrorT <$> rvalue a

instance  RValue ErrorT (LazyS a)  where 
  type RVCtx ErrorT = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ErrorT a) = ErrorT <$> rvalue a 

---------------------------------------------------------------------


instance  RValue ArrayT (Value a)  where 
  type RVCtx ArrayT = RVCtx (E Void2 ArrayT ExprTag)
  rvalue (ArrayT a) = ArrayT <$> rvalue a

instance SingI (Array a) => RValue ArrayT (Array a)  where 
  type RVCtx ArrayT = RVCtx (E Void2 ArrayT ExprTag)
  rvalue (ArrayT a) = withSingIRType @(Array a) $ ArrayT <$> rvalue a 

instance SingI (Lazy a) => RValue ArrayT (Lazy a)  where 
  type RVCtx ArrayT = RVCtx (E Void2 ArrayT ExprTag)
  rvalue (ArrayT a) = case sing @(Lazy a) of 
    SLazy sa -> withSingI sa $ case sing @a of
      SValue _ -> ArrayT <$> rvalue a
      SArray _ -> ArrayT <$> rvalue a
      SLazy  _ -> ArrayT <$> rvalue a
      SLazyS _ -> ArrayT <$> rvalue a


instance  RValue ArrayT (LazyS a)  where 
  type RVCtx ArrayT = RVCtx (E Void2 ArrayT ExprTag)
  rvalue (ArrayT a) = ArrayT <$> rvalue a 




---------------------------------------------------------------------


instance  RValue ArithmeticT (Value a)  where 
  type RVCtx ArithmeticT = RVCtx (E Void2 ArithmeticT ExprTag)
  rvalue (ArithmeticT a) = ArithmeticT <$> rvalue a

instance SingI (Array a) => RValue ArithmeticT (Array a)  where 
  type RVCtx ArithmeticT = RVCtx (E Void2 ArithmeticT ExprTag)
  rvalue (ArithmeticT a) = withSingIRType @(Array a) $ ArithmeticT <$> rvalue a 

instance  RValue ArithmeticT (Lazy a)  where 
  type RVCtx ArithmeticT = RVCtx (E Void2 ArithmeticT ExprTag)
  rvalue (ArithmeticT a) = ArithmeticT <$> rvalue a 


instance  RValue ArithmeticT (LazyS a)  where 
  type RVCtx ArithmeticT = RVCtx (E Void2 ArithmeticT ExprTag)
  rvalue (ArithmeticT a) = ArithmeticT <$> rvalue a 



---------------------------------------------------------------------


voidShowProof :: forall m. Functor m => Dict (C (ShowM m) Void2)
voidShowProof = Dict

instance Monad m => ShowM m (ET a) where 
 showsPrecM p (ETower a) = showsPrecM p a

instance Monad m => ShowM m (ErrorT a) where 
   showsPrecM p (ErrorT a) = showsPrecM p a

instance Monad m => ShowM m (ArrayT a) where 
   showsPrecM p (ArrayT a) = showsPrecM p a

instance Monad m => ShowM m (ArithmeticT a) where 
   showsPrecM p (ArithmeticT a) = case voidShowProof @m of 
     Dict -> showsPrecM @m p a

