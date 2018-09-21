{-# OPTIONS_GHC -Wall #-}
{-# Language UnicodeSyntax, TemplateHaskell, OverloadedStrings #-}
module Options (getOptions, Command(Command), SubCommand(..), Options(..)) where

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
  , grammarLang      ∷ Text   -- E.g. "ExemplumSwe"
  , language         ∷ String -- E.g. "Swe"
  , printNodes       ∷ Bool
  , printCompact     ∷ Bool
  , pruneSearchDepth ∷ Maybe Int
  }

data Command = Command SubCommand

data SubCommand = Muste Options | PreCompute

optionsParser ∷ Parser Options
optionsParser
  = Options
  <$> searchDepthParser
  <*> interactiveModeParser
  <*> sentencesParser
  <*> grammarParser
  <*> grammarLangParser
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
  grammarLangParser ∷ Parser Text
  grammarLangParser
    = O.strOption
      (  O.short 'L'
      <> O.long "grammar-lang"
      <> O.help "The grammar/lang to use.  E.g. \"ExemplumSwe\""
      <> O.metavar "GRAMMAR_LANG"
      )
  languageParser ∷ Parser String
  languageParser
    = O.strOption
      (  O.short 'l'
      <> O.long "language"
      <> O.help "The language to use.  E.g. \"Swe\""
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

musteParserInfo ∷ ParserInfo Options
musteParserInfo = O.info (optionsParser <**> O.helper <**> version)
  (  O.fullDesc
  <> O.progDesc descr
  <> O.header header
  )

preComputeParserInfo ∷ ParserInfo ()
preComputeParserInfo = O.info (pure ()) (O.progDesc "Precompute grammar")

commandParser ∷ Parser Command
commandParser = Command <$> O.subparser
  (  O.command "cli"        (Muste      <$> musteParserInfo)
  <> O.command "precompute" (PreCompute <$  preComputeParserInfo)
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
