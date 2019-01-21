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
hooks = Dist.simpleUserHooks { preConf }
  where
  preConf ∷ Dist.Args → Dist.ConfigFlags → IO HookedBuildInfo
  preConf args flags
    =  npmInstall
    *> Dist.preConf Dist.simpleUserHooks args flags

npmInstall ∷ IO ()
npmInstall = do
  Turtle.cd "static"
  npm ["install"]
  Turtle.cd ".."

-- | run @npm@ a single target.
--
--     TODO: npm does not set the correct status code if the build
--     fails, so errors are not reported correctly.
npm ∷ MonadIO io ⇒ [Text] → io ()
npm = echoed "npm"

-------------------------------------------------
-- Copied over from the setup script for muste --
-------------------------------------------------

echoed ∷ MonadIO io ⇒ Text → [Text] → io ()
echoed c xs = Turtle.stdout $ inprocs c xs empty

-- | Like 'Turtle.inproc' but throws on non-zero exit codes.
inprocs ∷ Text → [Text] → Shell Line → Shell Line
inprocs cmd args s = either id id <$> Turtle.inprocWithErr cmd args s
