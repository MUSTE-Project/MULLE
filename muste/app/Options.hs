{-# OPTIONS_GHC -Wall #-}
{-# Language UnicodeSyntax, TemplateHaskell, OverloadedStrings,
  DuplicateRecordFields #-}
module Options
  ( getOptions
  , Command(Command)
  , SubCommand(..)
  , Options(..)
  , PreComputeOpts(..)
  ) where

import Prelude ()
import Muste.Prelude
import Options.Applicative (Parser, execParser, ParserInfo)
import qualified Options.Applicative as O
import Control.Applicative ((<**>), optional)
import qualified Development.GitRev as Dev

data Options = Options
  { searchDepth      ∷ Maybe Int
  , interactiveMode  ∷ Bool
  , sentences        ∷ [String]
  , grammar          ∷ Text   -- E.g. "novo_modo/Exemplum"
  , language         ∷ Text   -- E.g. "ExemplumSwe"
  , printNodes       ∷ Bool
  , printCompact     ∷ Bool
  , pruneSearchDepth ∷ Maybe Int
  }

data PreComputeOpts = PreComputeOpts
  { grammar ∷ Text
  , output  ∷ FilePath
  }

data Command = Command SubCommand

data SubCommand = Muste Options | PreCompute PreComputeOpts

optionsParser ∷ Parser Options
optionsParser
  = Options
  <$> searchDepthParser
  <*> interactiveModeParser
  <*> sentencesParser
  <*> grammarParser
  <*> languageParser
  <*> printNodesParser
  <*> printCompactParser
  <*> pruneSearchDepthParser
  where
  searchDepthParser ∷ Parser (Maybe Int)
  searchDepthParser
    = optional
    $ O.option O.auto
      (  O.long "limit-adjunctions"
      <> O.help "Limit search depth when creating adjunction trees"
      <> O.metavar "DEPTH"
      )
  interactiveModeParser ∷ Parser Bool
  interactiveModeParser
    = O.switch
      (  O.long "interactive"
      <> O.help "Run in interactive mode"
      )
  sentencesParser ∷ Parser [String]
  sentencesParser
    = many (O.strArgument (O.metavar "SENTENCES"))
  languageParser ∷ Parser Text
  languageParser
    = O.strOption
      (  O.short 'L'
      <> O.long "language"
      <> O.help "The language to use.  E.g. \"ExemplumSwe\""
      <> O.metavar "LANG"
      )
  printNodesParser ∷ Parser Bool
  printNodesParser
    = O.switch
      (  O.long "print-nodes"
      <> O.help "Show the internal representation of the sentences"
      )
  printCompactParser ∷ Parser Bool
  printCompactParser
    = O.switch
      (  O.long "print-compact"
      <> O.help "Print compact information about menus"
      )
  pruneSearchDepthParser ∷ Parser (Maybe Int)
  pruneSearchDepthParser
    = optional
    $ O.option O.auto
      (  O.long "limit-prune"
      <> O.help "Limit search depth when creating pruning trees"
      <> O.metavar "DEPTH"
      )

grammarParser ∷ Parser Text
grammarParser
  = O.strOption
    (  O.short 'G'
    <> O.long "grammar"
    <> O.help
      (  "The grammar to use.  E.g. \"novo_modo/Exemplum\".  "
      <> "Please note that this is not actually a path, "
      <> "but rather must be one of the built in grammars."
      )
    <> O.metavar "GRAMMAR"
    )

musteParserInfo ∷ ParserInfo Options
musteParserInfo = O.info (optionsParser <**> O.helper <**> version)
  (  O.fullDesc
  <> O.progDesc descr
  <> O.header header
  )

preComputeOptsParser ∷ Parser PreComputeOpts
preComputeOptsParser
  =   PreComputeOpts
  <$> grammarParser
  <*> outputParser
  where
  outputParser ∷ Parser FilePath
  outputParser = O.strOption
    (  O.short 'o'
    <> O.long "output"
    <> O.metavar "PATH"
    )

preComputeParserInfo ∷ ParserInfo PreComputeOpts
preComputeParserInfo
  = O.info preComputeOptsParser (O.progDesc "Precompute grammar")

commandParser ∷ Parser Command
commandParser = Command <$> O.subparser
  (  O.command "cli"        (Muste      <$> musteParserInfo)
  <> O.command "precompute" (PreCompute <$> preComputeParserInfo)
  )

getOptions ∷ IO Command
getOptions
  = execParser
  $ O.info (commandParser <**> O.helper <**> version) mempty

version ∷ Parser (a → a)
version = O.infoOption gitDescription $ mconcat
  [ O.long "version"
  , O.help "Output version information and exit"
  , O.hidden
  ]

header ∷ String
header = "muste cli - CLI for the Multi Semantic Text Editor (MUSTE)"

descr ∷ String
descr = "Runs the CLI for the Multi Semantic Text Editor"

gitDescription ∷ String
gitDescription = $(Dev.gitDescribe)
