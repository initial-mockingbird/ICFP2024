module Lensy2 where


data LensyM' m s a = LensyM'
  { getL  :: s -> m a
  , setL  :: s -> a -> m s
  , setFL :: s -> a -> m s
  , varNameM' :: String
  }


viewyM' :: LensyM' m s a -> s -> m a
viewyM'  = getL

setyM' :: LensyM' m s a -> a -> s -> m s
setyM' = flip . setL


setyMF' :: LensyM' m s a -> a -> s -> m s
setyMF' = flip . setFL
