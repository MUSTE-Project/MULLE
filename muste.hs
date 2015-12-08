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
    let parses1 = parse grammar lang scat "b e d f" -- "the wolf drinks the milk"
--    let foo = map (\p -> putStrLn $ show $ snd $ tree2utree p 0) parses1
--    let bar = map (\p -> putStrLn $ show $ p) parses1
    putStrLn $ show (head parses1)
    let uparse = tree2utree ( head parses1 )
    let gparse = tree2gtree ( head parses1 )
--     let ugparse = gtree2ugtree gparse
--     putStrLn $ show $ uparse
-- --    putStrLn $ show $ fromJust $ path2upath uparse [0,1,0,0]
--     putStrLn $ show $ gparse
--     putStrLn $ show $ ugparse
--     putStrLn $ show $ gtree2tree gparse
--     putStrLn $ show $ gtree2cgtree gparse grammar
--     putStrLn $ show $ cgsubtrees $ gtree2cgtree gparse grammar
--    augment grammar $ gtree2cgtree gparse grammar
    putStrLn $ show $ showfuntype $ getfuntype grammar (mkCId "g")
    putStrLn $ show $ functionsByCat grammar (mkCId "A")
    putStrLn $ show $ map (getfuntype grammar) (functionsByCat grammar (mkCId "A"))
    return ()
    
