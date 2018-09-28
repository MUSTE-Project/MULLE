{-# OPTIONS_GHC -Wall #-}
{-# Language UnicodeSyntax, TemplateHaskell, OverloadedStrings,
  DuplicateRecordFields #-}
module Options
  ( getOptions
  , Command(Command)
  , SubCommand(..)
  , Options(..)
  , PreComputeOpts(..)
  , SearchOptions(..)
  ) where

import Prelude ()
import Muste.Prelude
import Options.Applicative (Parser, execParser, ParserInfo)
import qualified Options.Applicative as O
import Control.Applicative ((<**>), optional)
import qualified Development.GitRev as Dev

data Options = Options
  { interactiveMode    ∷ Bool
  , sentences          ∷ [Text]
  , grammar            ∷ Text   -- E.g. "novo_modo/Exemplum"
  , language           ∷ Text   -- E.g. "ExemplumSwe"
  , printNodes         ∷ Bool
  , printCompact       ∷ Bool
  , searchOptions      ∷ SearchOptions
  , input              ∷ Maybe FilePath
  }

data PreComputeOpts = PreComputeOpts
  { grammar       ∷ Text
  , output        ∷ FilePath
  , searchOptions ∷ SearchOptions
  }

data SearchOptions = SearchOptions
  { adjTreeSearchDepth ∷ Maybe Int
  , adjTreeSearchSize  ∷ Maybe Int
  , pruneSearchDepth   ∷ Maybe Int
  , pruneSearchSize    ∷ Maybe Int
  }

data Command = Command SubCommand

data SubCommand = Muste Options | PreCompute PreComputeOpts

optionsParser ∷ Parser Options
optionsParser
  = Options
  <$> interactiveModeParser
  <*> sentencesParser
  <*> grammarParser
  <*> languageParser
  <*> printNodesParser
  <*> printCompactParser
  <*> searchOptionsParser
  <*> inputParser
  where
  interactiveModeParser ∷ Parser Bool
  interactiveModeParser
    = O.switch
      (  O.long "interactive"
      <> O.help "Run in interactive mode"
      )
  sentencesParser ∷ Parser [Text]
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
  inputParser ∷ Parser (Maybe FilePath)
  inputParser
    = optional
    $ O.strOption
      (  O.long "input"
      <> O.help "Load adjunction trees from cache"
      <> O.metavar "PATH"
      )

searchOptionsParser ∷ Parser SearchOptions
searchOptionsParser
  = SearchOptions
  <$> adjTreeSearchDepthParser
  <*> adjTreeSearchSizeParser
  <*> pruneSearchDepthParser
  <*> pruneSearchSizeParser
  where
  adjTreeSearchDepthParser ∷ Parser (Maybe Int)
  adjTreeSearchDepthParser
    = optional
    $ O.option O.auto
      (  O.long "max-adjtree-depth"
      <> O.help "Limit search depth when creating adjunction trees"
      <> O.metavar "DEPTH"
      )

  adjTreeSearchSizeParser ∷ Parser (Maybe Int)
  adjTreeSearchSizeParser
    = optional
    $ O.option O.auto
      (  O.long "max-adjtree-size"
      <> O.help
        (  "Limit search size when creating adjunction trees. "
        <> warnNotUsed
        )
      <> O.metavar "SIZE"
      )

  pruneSearchDepthParser ∷ Parser (Maybe Int)
  pruneSearchDepthParser
    = optional
    $ O.option O.auto
      (  O.long "max-prune-depth"
      <> O.help
        (  "Limit search depth when pruning trees. "
        <> warnNotUsed
        )
      <> O.metavar "DEPTH"
      )

  warnNotUsed
        =   "WARNING: This options is not currently being used. "
        <> "Please see the discussion at: "
        <> "https://github.com/MUSTE-Project/MULLE/issues/46"

  pruneSearchSizeParser ∷ Parser (Maybe Int)
  pruneSearchSizeParser
    = optional
    $ O.option O.auto
      (  O.long "max-prune-size"
      <> O.help "Limit search size when pruning trees"
      <> O.metavar "SIZE"
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
  <*> searchOptionsParser
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
