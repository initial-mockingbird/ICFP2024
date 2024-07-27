{-# LANGUAGE ForeignFunctionInterface #-}

module Main where

import Zilly.Classic.Runner
import Foreign
import Foreign.C
import System.IO.Unsafe as Unsafe
-- import GHC.Wasm.Prim 

main :: IO ()
main = pure ()

cmain :: IO CString
cmain = head <$> parseAndResponse' "" >>= newCString 
  where
    packet = "0[0]\tZ x := 5;\EOT"


foreign export ccall cmain :: IO CString
