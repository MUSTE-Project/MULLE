module Main where

import Database
import Database.SQLite.Simple

main =
  do
    putStrLn "Starting"
    con <- open "muste.db"
    initDB con
--    (grammars,precs) <- initPrecomputed con
--    writeFile "/dev/null" (show precs)
    putStrLn "Finished, shutting down"
    close con
