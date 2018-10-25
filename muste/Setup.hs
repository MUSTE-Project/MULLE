{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language UnicodeSyntax, NamedFieldPuns, OverloadedStrings,
  TypeApplications #-}

import qualified Distribution.Simple.Setup as Dist
import Distribution.Types.HookedBuildInfo (HookedBuildInfo)
import Distribution.Simple (UserHooks(..))
import qualified Distribution.Simple as Dist
import Turtle (Shell, Line, ExitCode(..), ProcFailed(..))
import qualified Turtle as Turtle
import Data.Text (Text)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Applicative (empty)
import Control.Exception (throwIO)

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
-- make xs = Turtle.procs "make" xs empty
make = echoed "make"

echoed ∷ MonadIO io ⇒ Text → [Text] → io ()
echoed c xs = Turtle.stdout $ Turtle.inproc c xs empty

-- | Like 'Turtle.inproc' but throws on non-zero exit codes.  Also,
-- returns whole output, not just a line.
inprocs ∷ Text → [Text] → Shell Line → Shell Text
inprocs cmd args s = do
  (exitCode, stdout, _) ← Turtle.procStrictWithErr cmd args s
  case exitCode of
    ExitSuccess → pure stdout
    _           → liftIO (throwIO (ProcFailed cmd args exitCode))

