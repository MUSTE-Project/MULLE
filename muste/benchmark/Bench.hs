module Bench (main) where

import qualified Criterion

main ∷ IO ()
main = putStrLn "Feeling very benchy!" -- Criterion.defaultMain _

-- setupEnv = do
--   let small = replicate 1000 (1 :: Int)
--   big <- map length . words <$> readFile "/usr/dict/words"
--   return (small, big)

-- main = defaultMain [
--    -- notice the lazy pattern match here!
--    env setupEnv $ \ ~(small,big) -> bgroup "main" [
--    bgroup "small" [
--      bench "length" $ whnf length small
--    , bench "length . filter" $ whnf (length . filter (==1)) small
--    ]
--  ,  bgroup "big" [
--      bench "length" $ whnf length big
--    , bench "length . filter" $ whnf (length . filter (==1)) big
--    ]
--  ] ]
