{-# OPTIONS_GHC -Wall #-}

module Options (getOptions, Options, initDb) where

import Prelude ()
import Muste.Prelude
import qualified Muste.Prelude.Unsafe as Unsafe
import Options.Applicative (Parser, execParser, ParserInfo)
import qualified Options.Applicative as O
import Control.Applicative ((<**>))

newtype Options = Options
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
version = O.infoOption Unsafe.gitDescription $ mconcat
  [ O.long "version"
  , O.help "Output version information and exit"
  , O.hidden
  ]

header ∷ String
header = "muste-ajax - REST API for the Multi Semantic Text Editor (MUSTE)"

descr ∷ String
descr = "Runs a REST endpoint for the Multi Semantic Text Editor"
