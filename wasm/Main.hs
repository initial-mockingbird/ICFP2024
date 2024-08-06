{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Zilly.Classic.Runner
import GHC.Wasm.Prim
import Language.Javascript.JSaddle.Wasm qualified as JSaddle.Wasm
import GHCJS.Types
import Data.String (IsString(fromString))
import Data.Text (Text)
-- import GHC.Wasm.Prim 

main :: IO ()
main = pure ()

foreign export  javascript cmain :: JSString -> IO JSString 

cmain :: JSString -> IO JSString 
cmain _ = undefined -- head <$> parseAndResponse' packet >>= \s -> putStrLn s >> (pure . fromString @JSString ) s
  where
    packet = "0[0]\tZ x := 5;\EOT"



