{-# Language UnicodeSyntax, CPP #-}
module Options (getOptions, Options, initDb) where

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup((<>)))
#endif
import Options.Applicative (Parser, execParser, ParserInfo)
import qualified Options.Applicative as O
import Control.Applicative ((<**>))

data Options = Options
  { initDb ∷ Bool
  }

optionsParser ∷ Parser Options
optionsParser = Options
  <$> O.switch
    ( O.long "recreate-db"
    <> O.help
      (  "Recreates the database. "
      <> "WARNING: This deletes any existing data in the database."
      )
    )

getOptions ∷ IO Options
getOptions = execParser opts

opts ∷ ParserInfo Options
opts = O.info (optionsParser <**> O.helper)
  (  O.fullDesc
  <> O.progDesc descr
  <> O.header header
  )

header ∷ String
header = "muste-ajax - REST API for the Multi Semantic Text Editor (MUSTE)"

descr ∷ String
descr = "Runs a REST endpoint for the Multi Semantic Text Editor"
