-- | Beware this module does magic!
--
-- See e.g. http://neilmitchell.blogspot.com/2008/02/adding-data-files-using-cabal.html
-- for more information.
module Paths_muste_ajax where

getDataFileName :: FilePath -> IO FilePath
getDataFileName = pure
