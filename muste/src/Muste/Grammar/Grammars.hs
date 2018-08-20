{-# Language TemplateHaskell #-}
module Muste.Grammar.Grammars (grammars) where

import Data.ByteString (ByteString)

import qualified Muste.Grammar.Embed as Embed

-- Better yet it would be to complete the parsing of all this data.
-- However, I'm not strong enough in Template Haskell to figure out
-- how to make a gadget that does that.  The type would ideally be
-- @Map String Grammar@.  That way we can also know at compile time(!)
-- if there is an error in one of the compiled binaries.  That
-- situation might arise if the version of the pgf runtime is
-- different from the compiler used to generate the binaries.
grammars :: [(String, ByteString)]
grammars =
  [ $(Embed.grammar "novo_modo/Prima")
  , $(Embed.grammar "novo_modo/Secunda")
  ]
