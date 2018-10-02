{-# Language TemplateHaskell, OverloadedStrings #-}
module Main (main) where

import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LB

import Criterion (Benchmark)
import qualified Criterion
import qualified Criterion.Main as Criterion

import Muste (Grammar, TTree, Context)
import qualified Muste.Util as Util
import qualified Muste.Grammar.Embed as Embed
import Muste.Grammar (Grammar)
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Menu.Internal as Menu

getGrammar :: IO LB.ByteString
getGrammar = pure $ LB.fromStrict $ snd grammar'
  where
  grammar' ∷ (String, ByteString)
  grammar' = $(Embed.grammar "exemplum/Exemplum")

-- theCtxt ∷ IO Context
-- theCtxt = pure $ Util.unsafeGetContext grammar "ExemplumSwe"

bench ∷ LB.ByteString → Benchmark
bench bs
  =   Criterion.bgroup "Menu.getMenuItems"
  $   go <$> sentences
  where
  c = Util.unsafeGetContext (Grammar.parseGrammar bs) "ExemplumSwe"
  go ∷ String → Benchmark
  go s = Criterion.bench s $ Criterion.nf (Menu.getMenuItems c) s
  sentences ∷ [String]
  sentences =
    [ "vinet är vist"
    , "ofta håller den stora kejsaren ett gott vin"
    , "Augustus felix est"
    , "flickan slår på en dator"
    , "flickan i Paris slår på många datorer i dåliga böcker"
    ]

main ∷ IO ()
-- main = putStrLn "Feeling very benchy!"
main = Criterion.defaultMain [Criterion.env getGrammar bench]

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
