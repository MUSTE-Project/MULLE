-- module Muste where
import PGF

import Data.Maybe
import Tree
type Weight = Int

-- precompute :: PGF -> Tree -> Path -> [(Path, Tree,Weight)]
-- precompute pgf tree [] = []
-- precompute pgf tree path =
--   let b = selectBranch tree (head path)
--   in
--     precompute pgf b (tail path)


     
       
main =
  do
    grammar <- readPGF "gf/ABCAbs.pgf"
    let lang = (head $ languages grammar)
    let scat = (startCat grammar)
    let parses1 = parse grammar lang scat "b d e f" -- "the wolf drinks the milk"
--    let foo = map (\p -> putStrLn $ show $ snd $ tree2utree p 0) parses1
--    let bar = map (\p -> putStrLn $ show $ p) parses1
    putStrLn $ show (head parses1)
    putStrLn $ show $ snd $ tree2utree ( head parses1 ) 0
    return ()
    
