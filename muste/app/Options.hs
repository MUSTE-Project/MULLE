{-# OPTIONS_GHC -Wall #-}
{-# Language UnicodeSyntax, TemplateHaskell #-}
module Options (getOptions, Options(..)) where

import Prelude ()
import Muste.Prelude
import Options.Applicative (Parser, execParser, ParserInfo)
import qualified Options.Applicative as O
import Control.Applicative ((<**>), optional)
import qualified Development.GitRev as Dev

data Options = Options
  { searchDepth     ∷ Maybe Int
  , interactiveMode ∷ Bool
  , sentences       ∷ [String]
  }

optionsParser ∷ Parser Options
optionsParser
  = Options
  <$> searchDepthParser
  <*> interactiveModeParser
  <*> sentencesParser
  where
  searchDepthParser ∷ Parser (Maybe Int)
  searchDepthParser
    = optional
    $ O.option O.auto
    $ (  O.short 'L'
      <> O.long "limit-search"
      <> O.help "Limit search depth when creating adjunction trees"
      <> O.metavar "DEPTH"
      )
  interactiveModeParser ∷ Parser Bool
  interactiveModeParser
    = O.switch
    $ (  O.long "interactive"
      <> O.help "Run in interactive mode"
      )
  sentencesParser ∷ Parser [String]
  sentencesParser
    = many (O.strArgument (O.metavar "SENTENCES"))

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
header = "muste-cli - CLI for the Multi Semantic Text Editor (MUSTE)"

descr ∷ String
descr = "Runs the CLI for the Multi Semantic Text Editor"

gitDescription ∷ String
gitDescription = $(Dev.gitDescribe)
