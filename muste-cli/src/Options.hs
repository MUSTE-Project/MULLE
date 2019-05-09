{-# OPTIONS_GHC -Wall #-}
{-# Language
 OverloadedStrings,
 TemplateHaskell
#-}

module Options
  ( getOptions
  , Options(..)
  , Command(..)
  , MusteOptions(..)
  , PrecomputeOptions(..)
  , PrintOptions(..)
  ) where

import Development.GitRev (gitDescribe)

import qualified Options.Applicative as O
import Options.Applicative (Parser)
import Control.Applicative ((<**>), (<|>), some)
import Data.Text (Text)

import qualified Muste

-- Options type hierarchy

data Options = Options
    { grammar       :: FilePath   -- E.g. "exemplum/Exemplum.pgf" 
    , builderInfo   :: Muste.BuilderInfo
    , command       :: Command
    }

data Command = Muste MusteOptions | Precompute PrecomputeOptions

data MusteOptions = MusteOptions
    { language           :: Text   -- E.g. "ExemplumSwe"
    , input              :: Maybe FilePath
    , pruneOptions       :: Muste.PruneOpts
    , printOptions       :: PrintOptions
    , sentences          :: [Text]
    }

data PrintOptions = PrintOptions
    { printNodes    :: Bool
    , printCompact  :: Bool
    }

newtype PrecomputeOptions = PrecomputeOptions
    { output        :: FilePath
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
versionParser = O.infoOption $(gitDescribe)
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
                <*> builderInfoParser
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
                     <*> pruneOptionsParser
                     <*> printOptionsParser
                     <*> (interactiveModeParser <|> sentencesParser)

printOptionsParser :: Parser PrintOptions
printOptionsParser = PrintOptions
                     <$> printNodesParser
                     <*> printCompactParser

pruneOptionsParser :: Parser Muste.PruneOpts
pruneOptionsParser = Muste.PruneOpts
                     <$> (pruneSearchDepthParser <|> searchDepthParser)
                     <*> (pruneSearchSizeParser  <|> searchSizeParser)

builderInfoParser :: Parser Muste.BuilderInfo
builderInfoParser = Muste.BuilderInfo
                    <$> (adjTreeSearchDepthParser <|> searchDepthParser)
                    <*> (adjTreeSearchSizeParser  <|> searchSizeParser)
      
      
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


grammarParser :: Parser FilePath
grammarParser = O.strOption
    (  O.short 'G'
    <> O.long "grammar"
    <> O.help "The path to the PGF grammar to use (e.g., \"grammars/exemplum/Exemplum.pgf\")" 
    <> O.metavar "GRAMMAR"
    )

languageParser :: Parser Text
languageParser = O.strOption
    (  O.short 'L'
    <> O.long "language"
    <> O.help "The language to use, (e.g., \"ExemplumSwe\")"
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
    <> O.help "Limit search size when creating adjunction trees"
    <> O.metavar "SIZE"
    )

pruneSearchDepthParser :: Parser (Maybe Int)
pruneSearchDepthParser = O.optional $ O.option O.auto
    (  O.long "max-prune-depth"
    <> O.help "Limit search depth when pruning trees"
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
    <> O.help "Limit search depth when pruning trees and creating adjunction trees"
    <> O.metavar "DEPTH"
    )

searchSizeParser :: Parser (Maybe Int)
searchSizeParser = O.optional $ O.option O.auto
    (  O.short 'S'
    <> O.long "max-size"
    <> O.help "Limit search size when pruning trees and creating adjunction trees"
    <> O.metavar "SIZE"
    )
