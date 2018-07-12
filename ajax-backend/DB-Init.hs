module Main where

import Database
import Database.SQLite.Simple

import Paths_ajax_backend

main :: IO ()
main = do
  putStrLn "Starting"
  con <- getDB >>= open
  initDB con
  putStrLn "Finished, shutting down"
  close con
