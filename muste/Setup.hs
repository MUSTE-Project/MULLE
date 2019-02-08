{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language NamedFieldPuns, OverloadedStrings, TypeApplications #-}

import qualified Distribution.Simple.Setup as Dist
import Distribution.Types.HookedBuildInfo (HookedBuildInfo)
import Distribution.Simple (UserHooks(..))
import qualified Distribution.Simple as Dist

main :: IO ()
main
  = Dist.defaultMainWithHooks
  $ hooks

hooks :: UserHooks
hooks = Dist.simpleUserHooks { preBuild }
  where
  preBuild :: Dist.Args -> Dist.BuildFlags -> IO HookedBuildInfo
  preBuild args flags
    =  Dist.preBuild Dist.simpleUserHooks args flags
