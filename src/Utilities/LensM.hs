{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE KindSignatures #-}
{-|
Module      : Utilities.LensM
Description : "Lenses" that perform monadic actions
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

We use "lens" very loosely here, since whenever you add arbitrary
monadic actions to lenses, it's very hard to keep the lens laws.

In our case, a LensM will eventually embody a means to
represent a variable in a context \(\Gamma\):

- We can read it using @getL@
- We can set it using @setL@, yielding an error for already defined variables
- We can set it fresh using @setFL@, ignoring if it's already defined or not.
- We can get the variable name by using @varNameM@

If we introduce algebraic effects into the mix, we can encode these
axioms (i.e: adding a @ReadOnly@ effect for @getL@). But for the
time being, this isn't a pressing issue.

-}
module Utilities.LensM where
import Data.Kind (Type)


data LensM (m :: Type -> Type) (s :: Type) (a :: Type) = LensM
  { getL  :: s -> m a
  , setL  :: s -> a -> m s
  , setFL :: s -> a -> m s
  , varNameM :: String
  }

viewM :: LensM m s a -> s -> m a
viewM  = getL

setM :: LensM m s a -> a -> s -> m s
setM = flip . setL

setMF :: LensM m s a -> a -> s -> m s
setMF = flip . setFL