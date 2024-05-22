module Main (main) where

import Parser
import Control.Monad (forM_)



files :: [FilePath]
files = ["./programs/ex" <> show n <> ".z" | n <- [1..9]]

main :: IO ()
main = forM_ files $ \file -> do
  putStrLn $ "Parsing: " <> file
  print =<< parseFile file
  sep
  where
    sep = putStrLn "----------------------"
