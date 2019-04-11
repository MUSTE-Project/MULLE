{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 TemplateHaskell
#-}

module Muste.Prelude.Unsafe where

import qualified Development.GitRev as GitRev

gitDescription :: String
gitDescription = $(GitRev.gitDescribe)
