{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language UnicodeSyntax, NamedFieldPuns, OverloadedStrings,
  TypeApplications #-}

import qualified Distribution.Simple.Setup as Dist
import Distribution.Types.HookedBuildInfo (HookedBuildInfo)
import Distribution.Simple (UserHooks(..))
import qualified Distribution.Simple as Dist
import Turtle (Shell, Line)
import qualified Turtle as Turtle
import Data.Text (Text)
import Control.Monad.IO.Class (MonadIO)
import Control.Applicative (empty)

main ∷ IO ()
main
  = Dist.defaultMainWithHooks
  $ hooks

hooks ∷ UserHooks
hooks = Dist.simpleUserHooks { preBuild }
  where
  preBuild ∷ Dist.Args → Dist.BuildFlags → IO HookedBuildInfo
  preBuild args flags
    =  installGrammars
    *> Dist.preBuild Dist.simpleUserHooks args flags

installGrammars ∷ IO ()
installGrammars = make ["-C", "data/grammars", "install"]

-- | @make@ a single target.  Throws on error.
make ∷ MonadIO io ⇒ [Text] → io ()
make = echoed "make"

echoed ∷ MonadIO io ⇒ Text → [Text] → io ()
echoed c xs = Turtle.stdout $ inprocs c xs empty

-- | Like 'Turtle.inproc' but throws on non-zero exit codes.
inprocs ∷ Text → [Text] → Shell Line → Shell Line
inprocs cmd args s = either id id <$> Turtle.inprocWithErr cmd args s
