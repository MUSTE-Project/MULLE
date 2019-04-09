{-# OPTIONS_GHC -Wall #-}
{-# Language
 OverloadedStrings
#-}

module Options
  ( getOptions
  , Options(..)
  , Command(..)
  , MusteOptions(..)
  , PrecomputeOptions(..)
  , SearchOptions(..)
  ) where

import Prelude ()
import Muste.Prelude
import qualified Muste.Prelude.Unsafe as Unsafe
import qualified Options.Applicative as O
import Options.Applicative (Parser)
import Control.Applicative ((<**>))


-- Options type hierarchy

data Options = Options
    { grammar       :: Text   -- E.g. "exemplum/Exemplum" 
    , searchOptions :: SearchOptions
    , command       :: Command
    }

data Command = Muste MusteOptions | Precompute PrecomputeOptions

data MusteOptions = MusteOptions
    { language           :: Text   -- E.g. "ExemplumSwe"
    , input              :: Maybe FilePath
    , printNodes         :: Bool
    , printCompact       :: Bool
    , sentences          :: [Text]
    }

data PrecomputeOptions = PrecomputeOptions
    { output        :: FilePath
    }

data SearchOptions = SearchOptions
    { adjTreeSearchDepth :: Maybe Int
    , adjTreeSearchSize  :: Maybe Int
    , pruneSearchDepth   :: Maybe Int
    , pruneSearchSize    :: Maybe Int
    }


-- Main procedure for getting options

getOptions :: IO Options
getOptions = O.execParser $
    O.info (optionsParser <**> O.helper <**> versionParser)
    (  O.fullDesc
    <> O.progDesc description
    <> O.header header
    )

versionParser :: Parser (a -> a)
versionParser = O.infoOption Unsafe.gitDescription 
    (  O.short 'v'
    <> O.long "version"
    <> O.help "Output version information and exit"
    <> O.hidden
    )

header :: String
header = "muste cli - CLI for the Multi Semantic Text Editor (MUSTE)"

description :: String
description = "Runs the CLI for the Multi Semantic Text Editor"


-- Top-level parsers

optionsParser :: Parser Options
optionsParser = Options
                <$> grammarParser
                <*> searchOptionsParser
                <*> commandParser

commandParser :: Parser Command
commandParser = Precompute <$> precomputeParser
                <|>
                Muste <$> musteOptionsParser

precomputeParser :: Parser PrecomputeOptions
precomputeParser = PrecomputeOptions <$> precomputeOutputParser

musteOptionsParser :: Parser MusteOptions
musteOptionsParser = MusteOptions
                     <$> languageParser
                     <*> inputParser
                     <*> printNodesParser
                     <*> printCompactParser
                     <*> (interactiveModeParser <|> sentencesParser)

searchOptionsParser :: Parser SearchOptions
searchOptionsParser = (\(d0, d1) (s0, s1) -> SearchOptions d0 s0 d1 s1)
                      <$> depths
                      <*> sizes
    where
      depths = fmap dup searchDepthParser
               <|> (,) <$> adjTreeSearchDepthParser <*> pruneSearchDepthParser
      sizes  = fmap dup searchSizeParser
               <|> (,) <$> adjTreeSearchSizeParser  <*> pruneSearchSizeParser
      dup a  = (a, a)


-- Basic option parsers

precomputeOutputParser :: Parser FilePath
precomputeOutputParser = O.strOption
    (  O.short 'o'
    <> O.long "precompute"
    <> O.help "Save the precomputed adjunction trees to a file"
    <> O.metavar "PATH"
    )

interactiveModeParser :: Parser [Text]
interactiveModeParser= O.flag' []
    (  O.short 'i'
    <> O.long "interactive"
    <> O.help "Run in interactive mode"
    )

sentencesParser :: Parser [Text]
sentencesParser = some (O.strArgument (O.metavar "SENTENCES"))


grammarParser :: Parser Text
grammarParser = O.strOption
    (  O.short 'G'
    <> O.long "grammar"
    <> O.help ("The grammar to use.  " <>
               "E.g. \"exemplum/Exemplum\".  " <>
               "Please note that this is not actually a path, " <>
               "but rather must be one of the built in grammars.")
    <> O.metavar "GRAMMAR"
    )

languageParser :: Parser Text
languageParser = O.strOption
    (  O.short 'L'
    <> O.long "language"
    <> O.help "The language to use.  E.g. \"ExemplumSwe\""
    <> O.metavar "LANG"
    )

inputParser :: Parser (Maybe FilePath)
inputParser = O.optional $ O.strOption
    (  O.short 'f'
    <> O.long "input"
    <> O.help "Load precomputed adjunction trees from a file"
    <> O.metavar "PATH"
    )

printNodesParser :: Parser Bool
printNodesParser = O.switch
    (  O.long "print-nodes"
    <> O.help "Show the internal representation of the sentences"
    )

printCompactParser :: Parser Bool
printCompactParser = O.switch
    (  O.long "print-compact"
    <> O.help "Print compact information about menus"
    )

adjTreeSearchDepthParser :: Parser (Maybe Int)
adjTreeSearchDepthParser = O.optional $ O.option O.auto
    (  O.long "max-adjtree-depth"
    <> O.help "Limit search depth when creating adjunction trees"
    <> O.metavar "DEPTH"
    )

adjTreeSearchSizeParser :: Parser (Maybe Int)
adjTreeSearchSizeParser = O.optional $ O.option O.auto
    (  O.long "max-adjtree-size"
    <> O.help "Limit search size when creating adjunction trees. "
    <> O.metavar "SIZE"
    )

pruneSearchDepthParser :: Parser (Maybe Int)
pruneSearchDepthParser = O.optional $ O.option O.auto
    (  O.long "max-prune-depth"
    <> O.help "Limit search depth when pruning trees. "
    <> O.metavar "DEPTH"
    )

pruneSearchSizeParser :: Parser (Maybe Int)
pruneSearchSizeParser = O.optional $ O.option O.auto
    (  O.long "max-prune-size"
    <> O.help "Limit search size when pruning trees"
    <> O.metavar "SIZE"
    )

searchDepthParser :: Parser (Maybe Int)
searchDepthParser = O.optional $ O.option O.auto
    (  O.short 'D'
    <> O.long "max-depth"
    <> O.help
      "Limit search depth when pruning trees and creating adjunction trees."
    <> O.metavar "DEPTH"
    )

searchSizeParser :: Parser (Maybe Int)
searchSizeParser = O.optional $ O.option O.auto
    (  O.short 'S'
    <> O.long "max-size"
    <> O.help
      "Limit search size when pruning trees and creating adjunction trees."
    <> O.metavar "SIZE"
    )
