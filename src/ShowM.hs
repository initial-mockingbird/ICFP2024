{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module ShowM where
import Control.Monad


newtype UnquotedText = UT String

instance Show UnquotedText where
  show (UT s) = s


type ShowSM m = String -> m String

class Functor f => ShowM f a where
  {-# MINIMAL showsPrecM | showM #-}
  showM :: a -> f String
  showsPrecM :: Int -> a -> ShowSM f

  showM        x   = showsM x ""
  showsPrecM _ x s = (<> s) <$> showM x 
  

-- | equivalent to 'showsPrec' with a precedence of 0.
showsM :: (ShowM f a) => a -> ShowSM f
showsM =  showsPrecM 0

showCharM :: Applicative f => Char -> ShowSM f
showCharM c = pure <$> (c :)


showParenM :: Monad m => Bool -> ShowSM m -> ShowSM m
showParenM b p =  if b then showCharM '(' <=< p <=< showCharM ')' else p 

showStringM :: Applicative m => String -> ShowSM m
showStringM x =  pure . (x ++)

instance Applicative f => ShowM f Int where
  showM = pure . show

instance Applicative f => ShowM f UnquotedText where
  showM (UT s) = pure s