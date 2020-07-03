module Main where

import Core
import Parser
import Control.Monad
import System.IO
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  if length args == 0 then fail "Need at least one file as an argument" else return ()
  let file = args !! 0
  contents <- readFile file
  case runFile file contents of
    Left err -> fail $ show err
    Right trms ->
      forM trms (\(nam, trm, typ) ->
                   putStrLn $ nam ++ ": " ++ if check trm typ then show typ else " type error.")
  return ()
