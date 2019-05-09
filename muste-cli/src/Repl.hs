-- | A REPL (Read Eval Print Loop) for the MUSTE library.
--
-- This functionality is provided by the backend
-- "System.Control.Repline".

{-# OPTIONS_GHC -Wall #-}
{-# Language
 DerivingStrategies,
 GeneralizedNewtypeDeriving,
 MultiParamTypeClasses,
 OverloadedStrings,
 StandaloneDeriving
#-}

module Repl
  ( Muste
  , interactively
  , detachedly
  , updateMenu
  , Env(..)
  , grName
  ) where

import System.Console.Repline (HaskelineT, runHaskelineT)
import qualified System.Console.Haskeline as Repline
import qualified System.Console.Repline as Repline

import Control.Category ((>>>))
import Control.Monad.Reader (ask, ReaderT, runReaderT, MonadReader, MonadIO, liftIO)
import Data.Function ((&))

import Data.Text.Prettyprint.Doc (Doc, Pretty(pretty), (<+>))
import qualified Data.Text.Prettyprint.Doc as Doc
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Set as Set
import qualified Data.Containers as Mono
import qualified Data.List as List
import GHC.Exts (toList)

import qualified Muste
import qualified Options

grName :: Text
grName = "GRAMMAR"

-- | Data used during execution of the REPL.
data Env = Env
  { printOpts  :: Options.PrintOptions
  , pruneOpts  :: Muste.PruneOpts
  , muState :: Muste.MUState
  , muLang :: Text
  }

-- | The monad used for interacting with the MUSTE library.
newtype Muste a = Muste { unMuste :: (ReaderT Env IO) a }

deriving newtype instance Functor Muste
deriving newtype instance Applicative Muste
deriving newtype instance Monad Muste
deriving newtype instance MonadIO Muste
deriving newtype instance MonadReader Env Muste
deriving newtype instance Repline.MonadException Muste

type Repl = HaskelineT Muste 

detachedly :: Env -> Repl a -> IO a
detachedly env act
    = runHaskelineT Repline.defaultSettings act
    & runMuste env

runMuste :: Env -> Muste a -> IO a
runMuste env = unMuste >>> flip runReaderT env

interactively :: Env -> Repline.Command Repl -> IO ()
interactively env cmd
    = Repline.evalRepl (return "MULLE> ") cmd [] (Just ':') completer ini
    & runMuste env


updateMenu :: Text -> Repl ()
updateMenu sent = do
    env <- ask
    let menus = getMenuFor env sent
    let doc = if Options.printCompact (printOpts env) 
              then prettyCompact sent menus
              else prettyMenu env sent menus
    liftIO $ do
        Text.putStrLn $ "Sentence is now: " <> sent
        Muste.putDocLn doc


prettyCompact :: Text -> Muste.Menu -> Doc act
prettyCompact sent menus =
    Doc.vsep
        $  [ Doc.fill 60 "Selection" <+> "N:o menu items, total:"
             <+> pretty (sum (map (length . snd) menuList))
           ]
        <> (purdy <$> menuList)
 where
    menuList = Mono.mapToList menus
    purdy (sel, items)
      = Doc.fill 60
            (pretty sel <> ":" <+> prettyLin sel (Text.words s))
        <+> pretty (length items)


prettyMenu :: Env -> Text -> Muste.Menu -> Doc a
prettyMenu env sent menus
  = Doc.vsep
    [ Doc.vcat
      [ ""
      , maybeVerbose
        (pretty sel <> ":" <+> prettyLin sel (Text.words sent))
        (prettyLin sel annotated)
      , Doc.vcat
        [ maybeVerbose
          (prettyLin sel' (map getWord lin))
          (prettyLin sel' (map getNodes lin))
        | (sel', Muste.Linearization lin) <- Set.toList items ]
      ]
    | (sel, items) <- Mono.mapToList menus ]
 where
    annotated :: [Text]
    annotated = [ getNodes tok | tok <- lin ]
        where Muste.Linearization lin = foldl1 Muste.mergeL 
                    [ Muste.mkLinearization ctxt t
                    | let lin' = Muste.Linearization [Muste.Token (Text.pack w) mempty | w <- words (Text.unpack sent)],
                    t <- Muste.parseSentenceMU (muState env) grName (Muste.LangLin (muLang env) lin')
                    ]
    ctxt :: Muste.Context
    ctxt = Muste.getContextMU (muState env) grName (muLang env)
    getWord :: Muste.Token -> Text
    getWord (Muste.Token word _) = word
    getNodes :: Muste.Token -> Text
    getNodes (Muste.Token _ nodes) = Text.intercalate "+" (Set.toList nodes)
    maybeVerbose :: Doc a -> Doc a -> Doc a
    maybeVerbose docA docB
        | Options.printNodes (printOpts env) = Doc.fill 60 docA <+> docB
        | otherwise = docA


prettyLin :: Pretty tok => Muste.Selection -> [tok] -> Doc a
prettyLin sel tokens  = Doc.hsep tokens''
    where intervals   = [ Muste.runInterval int | int <- toList sel ]
          insertions  = [ pos  | (pos,pos') <- intervals, pos == pos' ]
          leftbraces  = [ pos  | (pos,pos') <- intervals, pos < pos' ]
          rightbraces = [ pos' | (pos,pos') <- intervals, pos < pos' ]
          count x     = length . filter (x==)
          tokens'     = [ Doc.hcat (List.replicate (count i leftbraces) "[") <> pretty tok <>
                          Doc.hcat (List.replicate (count (i+1) rightbraces) "]")
                        | (i, tok) <- zip [0..] tokens ]
          tokens''    = [ if i `elem` insertions then "[]" <+> tok' else tok'
                        | (i, tok') <- zip [0..] tokens' ] ++
                        [ "[]" | length tokens `elem` insertions ]


getMenuFor :: Env -> Text -> Muste.Menu
getMenuFor env sent = menus
 where 
    Muste.LinMenus _lin menus 
            = Muste.getMenusMU (muState env) (pruneOpts env) grName (Muste.LangLin (muLang env) lin')
    lin' = Muste.Linearization 
            [ Muste.Token (Text.pack w) mempty | w <- words (Text.unpack sent) ]


-- Currently no completion support.
completer :: Repline.CompleterStyle Muste 
completer = Repline.Word (const (pure mempty))

ini :: Repl ()
ini = liftIO $ putStrLn $ unlines
  [ "Type in a sentence to get the menu for that sentence."
  , ""
  , "Please note that sentences that cannot be parsed are silently ignored."
  , "An empty menu will be displayed (just newline) this is likely caused"
  , "by the sentence not being understood by the current grammar."
  , ""
  , "The grammar and language must be specified on the command line"
  , "(run with `--help` to see usage)."
  ]
