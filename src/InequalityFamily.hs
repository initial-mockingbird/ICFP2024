{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}


-- https://stackoverflow.com/questions/6939043/is-it-possible-to-place-inequality-constraints-on-haskell-type-variables
module InequalityFamily  where


data Yes = Yes deriving (Show)
data No = No deriving (Show)

type family TypeEq x y where
  TypeEq x x  = Yes
  TypeEq x y  = No


class (No ~ TypeEq x y) => (:/~) x y
instance (No ~ TypeEq x y) => (:/~) x y
