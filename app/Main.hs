module Main where

import HiProlog.Interpreter

main :: IO ()
main = do
  program <- getContents
  print $ eval program
