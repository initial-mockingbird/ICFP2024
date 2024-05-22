{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module VarMap where


import Lensy
import qualified ADT  as Z
import Data.String


newtype PhatomVar a = PhatomVar Z.Symbol
  deriving newtype (Eq,Ord,Show,IsString, Semigroup, Monoid)

newtype VarMap = VarMap (Z.Symbol)
  deriving newtype (Eq,Ord,Show,IsString, Semigroup, Monoid)