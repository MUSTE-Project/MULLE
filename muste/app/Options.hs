{-# OPTIONS_GHC -Wall #-}
{-# Language UnicodeSyntax, OverloadedStrings, 
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
import qualified Muste.Prelude.Unsafe as Unsafe
import qualified Options.Applicative as O
import Control.Applicative ((<**>), optional)

data Options = Options
  { interactiveMode    ∷ Bool
  , sentences          ∷ [Text]
  , grammar            ∷ Text   -- E.g. "exemplum/Exemplum" or "novo_modo/Prima"
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

newtype Command = Command SubCommand

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

dup ∷ a → (a, a)
dup a = (a, a)

searchOptionsParser ∷ Parser SearchOptions
searchOptionsParser
  = (\(d0, d1) (s0, s1) → SearchOptions d0 s0 d1 s1)
  <$> depths
  <*> sizes
  where
  depths = fmap dup searchDepthParser
    <|> (,) <$> adjTreeSearchDepthParser <*> pruneSearchDepthParser

  sizes = fmap dup searchSizeParser
    <|> (,) <$> adjTreeSearchSizeParser  <*> pruneSearchSizeParser

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
      <> O.help "Limit search size when creating adjunction trees. "
      <> O.metavar "SIZE"
      )

  pruneSearchDepthParser ∷ Parser (Maybe Int)
  pruneSearchDepthParser
    = optional
    $ O.option O.auto
      (  O.long "max-prune-depth"
      <> O.help "Limit search depth when pruning trees. "
      <> O.metavar "DEPTH"
      )

  pruneSearchSizeParser ∷ Parser (Maybe Int)
  pruneSearchSizeParser
    = optional
    $ O.option O.auto
      (  O.long "max-prune-size"
      <> O.help "Limit search size when pruning trees"
      <> O.metavar "SIZE"
      )

  searchDepthParser ∷ Parser (Maybe Int)
  searchDepthParser
    = optional
    $ O.option O.auto
      (  O.long "max-search-depth"
      <> O.help
        "Limit search depth when pruning trees and creating adjunction trees."
      <> O.metavar "DEPTH"
      )

  searchSizeParser ∷ Parser (Maybe Int)
  searchSizeParser
    = optional
    $ O.option O.auto
      (  O.long "max-search-size"
      <> O.help
        "Limit search size when pruning trees and creating adjunction trees."
      <> O.metavar "SIZE"
      )

grammarParser ∷ Parser Text
grammarParser
  = O.strOption
    (  O.short 'G'
    <> O.long "grammar"
    <> O.help
      (  "The grammar to use.  "
      <> "E.g. \"novo_modo/Prima\" or \"exemplum/Exemplum\".  "
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
version = O.infoOption Unsafe.gitDescription $ mconcat
  [ O.long "version"
  , O.help "Output version information and exit"
  , O.hidden
  ]

header ∷ String
header = "muste cli - CLI for the Multi Semantic Text Editor (MUSTE)"

descr ∷ String
descr = "Runs the CLI for the Multi Semantic Text Editor"
