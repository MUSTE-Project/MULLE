{-# OPTIONS_GHC -Wall #-}
{-# Language UnicodeSyntax, TemplateHaskell #-}
module Options (getOptions, Options, initDb) where

import Prelude ()
import Muste.Prelude
import Options.Applicative (Parser, execParser, ParserInfo)
import qualified Options.Applicative as O
import Control.Applicative ((<**>))
import qualified Development.GitRev as Dev

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
opts = O.info (optionsParser <**> O.helper <**> version)
  (  O.fullDesc
  <> O.progDesc descr
  <> O.header header
  )

version ∷ Parser (a → a)
version = O.infoOption gitDescription $ mconcat
  [ O.long "version"
  , O.help "Output version information and exit"
  , O.hidden
  ]

header ∷ String
header = "muste-ajax - REST API for the Multi Semantic Text Editor (MUSTE)"

descr ∷ String
descr = "Runs a REST endpoint for the Multi Semantic Text Editor"

gitDescription ∷ String
gitDescription = $(Dev.gitDescribe)
