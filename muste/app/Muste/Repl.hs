-- | A REPL (Read Eval Print Loop) for the MUSTE library.
--
-- This functionality is provided by the backend
-- "System.Control.Repline".

{-# OPTIONS_GHC -Wall #-}
{-# Language
 DeriveAnyClass,
 DerivingStrategies,
 GeneralizedNewtypeDeriving,
 MultiParamTypeClasses,
 NamedFieldPuns,
 OverloadedStrings,
 RecordWildCards,
 ScopedTypeVariables,
 StandaloneDeriving,
 TypeApplications
#-}

module Muste.Repl
  -- * The repl monad
  ( Muste
  -- * Ways of running the repl
  , interactively
  , detachedly
  -- * The single repl command
  , updateMenu
  -- * Additional bits and bobs needed to make this run
  , Options(..)
  , Env(..)
  ) where

import System.Console.Repline (HaskelineT, runHaskelineT)
import qualified System.Console.Haskeline as Repl
import qualified System.Console.Repline as Repl

import Control.Category ((>>>))
import Control.Monad.State.Strict
import Control.Monad.Reader
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

import Muste.Prelude.Extra (putDocLn)

import qualified Muste.Grammar as Grammar
import Muste.Selection (Selection, runInterval)
import Muste.Menu (Menu)
import qualified Muste.Menu as Menu
import qualified Muste.Sentence.Annotated as Annotated
import qualified Muste.Linearization as Linearization
import Muste.Tree (TTree)


-- | Options for the REPL.
data Options = Options
  { printNodes :: Bool
  , compact    :: Bool
  , pruneOpts  :: Menu.PruneOpts
  }

-- | Data used during execution of the REPL.
data Env = Env
  { ctxt :: Linearization.Context
  }

-- | The monad used for interacting with the MUSTE library.
newtype Muste m a = Muste { unMuste :: (ReaderT Options (StateT Env m)) a }

deriving newtype instance Functor m             => Functor (Muste m)
deriving newtype instance Monad m               => Applicative (Muste m)
deriving newtype instance Monad m               => Monad (Muste m)
deriving newtype instance MonadIO m             => MonadIO (Muste m)
deriving newtype instance Monad m               => MonadReader Options (Muste m)
deriving newtype instance Monad m               => MonadState Env (Muste m)
deriving newtype instance Repl.MonadException m => Repl.MonadException (Muste m)

type Repl a = HaskelineT (Muste IO) a

detachedly :: Options -> Env -> Repl a -> IO a
detachedly opts env act
  = runHaskelineT Repl.defaultSettings act
  & runMuste opts env

runMuste
  :: Monad m
  => Options
  -> Env
  -> Muste m a
  -> m a
runMuste opts env
  =   unMuste
  >>> flip runReaderT opts
  >>> flip evalStateT env

evalRepl
  :: Repl.MonadException m
  => String                      -- ^ Banner
  -> Repl.Command (HaskelineT m) -- ^ Command
  -> Repl.Options (HaskelineT m) -- ^ Options
  -> Repl.CompleterStyle m       -- ^ Tab completion
  -> HaskelineT m a              -- ^ Initializer
  -> m ()
evalRepl b c o s i
  = Repl.evalRepl (pure b) c o (pure ':') s i

interactively :: Options -> Env -> Repl.Command (HaskelineT (Muste IO)) -> IO ()
interactively opts env cmd
  = evalRepl "MULLE> " cmd options completer ini
  & runMuste opts env

-- I think there's a bug in the instantiation of `MonadReader` for
-- `HaskelineT` meaning that we have to use `lift` here.
getPrintNodes :: Repl Bool
getPrintNodes = lift $ asks @Options printNodes

getCompact :: Repl Bool
getCompact = lift $ asks @Options compact

askPruneOpts :: Repl Menu.PruneOpts
-- TODO Actually be ready with an answer here.
askPruneOpts = lift $ asks @Options pruneOpts

updateMenu :: Text -> Repl ()
updateMenu s = do
  ctxt <- getContext
  m <- getMenuFor s
  verb <- getPrintNodes
  comp <- getCompact
  let menuList = Mono.mapToList m
  let compDoc = Doc.vsep
        $  [ Doc.fill 60 "Selection" <+> "N:o menu items, total:"
             <+> pretty (sum (map (length . snd) menuList))
           ]
        <> (purdy <$> menuList)
  let doc = if comp then compDoc
            else prettyMenu verb ctxt s m
  liftIO $ do
    Text.putStrLn $ "Sentence is now: " <> s
    putDocLn doc
    where
    purdy (sel, items)
      = Doc.fill 60
            (pretty sel <> ":" <+> prettyLin sel (Text.words s))
        <+> pretty (length items)

prettyMenu :: forall a . Bool -> Linearization.Context -> Text -> Menu -> Doc a
prettyMenu verbose ctxt s = Doc.vsep . fmap (uncurry go) . open
  where
  open = fmap @[] (fmap @((,) Selection) Set.toList)
    . Mono.mapToList
  go :: Selection
    -> [(Selection, Menu.Linearization Menu.Annotated)]
    -> Doc a
  go sel xs = Doc.vcat
    [ ""
    , maybeVerbose prettySel $ prettyLin sel annotated
    , Doc.vcat $ fmap gogo xs
    ]
    where
    prettySel = pretty sel <> ":" <+> prettyLin sel (Text.words s)
  gogo :: (Selection, Menu.Linearization Menu.Annotated) -> Doc a
  gogo (sel, lin)
    = maybeVerbose prettyMenuItems
    $ prettyLin sel (map getNodes (toList lin))
    where
    prettyMenuItems = prettyLin sel (map getWord (toList lin))
  annotated :: [Text]
  annotated
    = parse s
    & map (\t -> Annotated.mkLinearization ctxt t)
    & foldl1 Annotated.mergeL
    & toList
    & map getNodes
  parse :: Text -> [TTree]
  parse = Grammar.parseSentence
    (Linearization.ctxtGrammar ctxt) (Linearization.ctxtLang ctxt)
  getWord (Menu.Annotated word _) = word
  getNodes :: Menu.Annotated -> Text
  getNodes (Menu.Annotated _ nodes) = Text.intercalate "+" (Set.toList nodes)
  maybeVerbose docA docB
    | verbose   = Doc.fill 60 docA <+> docB
    | otherwise = docA

prettyLin :: Pretty tok => Selection -> [tok] -> Doc a
prettyLin sel tokens  = Doc.hsep tokens''
    where intervals   = [ runInterval int | int <- toList sel ]
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


-- | @'getMenu' s@ gets a menu for a sentence @s@.
getMenuFor
  :: Text -- ^ The sentence to parse
  -> Repl Menu
getMenuFor s = do
  c <- getContext
  opts <- askPruneOpts
  pure $ Menu.getMenuItems opts c s

getContext :: Repl Linearization.Context
getContext = gets $ \(Env { .. }) -> ctxt

options :: Repl.Options (HaskelineT (Muste IO))
options = mempty

-- Currently no completion support.
completer :: Repl.CompleterStyle (Muste IO)
completer = Repl.Word (const (pure mempty))

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
