-- | A REPL (Read Eval Print Loop) for the MUSTE library.
--
-- This functionality is provided by the backend
-- "System.Control.Repline".
{-# OPTIONS_GHC -Wall #-}
{-# Language RecordWildCards, NamedFieldPuns, TemplateHaskell,
  DeriveAnyClass, OverloadedStrings, MultiParamTypeClasses,
  DerivingStrategies #-}
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

import Prelude (Float)
import Muste.Prelude
import System.Console.Repline
  (HaskelineT, runHaskelineT)
import qualified System.Console.Haskeline     as Repl
import qualified System.Console.Repline       as Repl
import Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc    as Doc
import qualified Data.Set                     as Set
import qualified Data.Containers              as Mono
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.List (intercalate)
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

import Muste hiding (getMenu)
import Muste.Common
import qualified Muste.Grammar.Internal       as Grammar
import Muste.Menu (Menu)
import qualified Muste.Menu.Internal          as Menu
import qualified Muste.Sentence.Annotated     as Annotated
import qualified Muste.Linearization.Internal as Linearization

-- | Options for the REPL.
data Options = Options
  { printNodes ∷ Bool
  }

-- | Data used during execution of the REPL.
data Env = Env
  { lang ∷ String
  , ctxt ∷ Context
  }

-- | The monad used for interacting with the MUSTE library.
newtype Muste m a = Muste { unMuste ∷ (ReaderT Options (StateT Env m)) a }

deriving newtype instance Functor m             ⇒ Functor (Muste m)
deriving newtype instance Monad m               ⇒ Applicative (Muste m)
deriving newtype instance Monad m               ⇒ Monad (Muste m)
deriving newtype instance MonadIO m             ⇒ MonadIO (Muste m)
deriving newtype instance Monad m               ⇒ MonadReader Options (Muste m)
deriving newtype instance Monad m               ⇒ MonadState Env (Muste m)
deriving newtype instance Repl.MonadException m ⇒ Repl.MonadException (Muste m)

type Repl a = HaskelineT (Muste IO) a

detachedly :: Options → Env → Repl a → IO a
detachedly opts env act
  = runHaskelineT Repl.defaultSettings act
  & runMuste opts env

runMuste
  ∷ Monad m
  ⇒ Options
  → Env
  → Muste m a
  → m a
runMuste opts env
  =   unMuste
  >>> flip runReaderT opts
  >>> flip evalStateT env

interactively ∷ Options → Env → Repl.Command (HaskelineT (Muste IO)) → IO ()
interactively opts env cmd
  = Repl.evalRepl "§ " cmd options completer ini
  & runMuste opts env

-- I think there's a bug in the instantiation of `MonadReader` for
-- `HaskelineT` meaning that we have to use `lift` here.
getPrintNodes ∷ Repl Bool
getPrintNodes = lift $ asks @Options printNodes

updateMenu ∷ String → Repl ()
updateMenu s = do
  ctxt ← getContext
  liftIO $ timeCommand "Precalculate adjunction trees" $ do
    let adjtrees = Mono.mapToList $ Linearization.ctxtPrecomputed ctxt
    let adjsizes = [ (cat, length trees) | (cat, trees) <- adjtrees ]
    printf "\nN:o adjunction trees = %d\n" (sum (map snd adjsizes))
  m ← getMenuFor s
  verb ← getPrintNodes
  liftIO $ timeCommand "Update menu" $ do
    putStrLn $ "Sentence is now: " <> s
    putDocLn $ prettyMenu verb ctxt s m

timeCommand :: String -> IO a -> IO a
timeCommand title cmd = do
    time0 <- getCPUTime
    result <- cmd
    time1 <- getCPUTime
    let secs :: Float = fromInteger (time1-time0) * 1e-12
    printf "\n>>> %s: %.2f s <<<\n\n" title secs
    return result

prettyMenu ∷ ∀ a . Bool → Context → String → Menu → Doc a
prettyMenu verbose ctxt s = Doc.vsep . fmap (uncurry go) . open
  where
  open = fmap @[] (fmap @((,) Menu.Selection) Set.toList)
    . Mono.mapToList
  go ∷ Menu.Selection
    → [(Menu.Selection, Menu.Linearization Menu.Annotated)]
    → Doc a
  go sel xs = Doc.vcat
    [ ""
    , maybeVerbose prettySel $ prettyLin sel annotated
    , Doc.vcat $ fmap gogo xs
    ]
    where
    prettySel = pretty sel <> ":" <+> prettyLin sel (words s)
  gogo ∷ (Menu.Selection, Menu.Linearization Menu.Annotated) → Doc a
  gogo (sel, lin)
    = maybeVerbose prettyMenuItems
    $ prettyLin sel (map getNodes (toList lin))
    where
    prettyMenuItems = prettyLin sel (map getWord (toList lin))
  annotated = Grammar.parseSentence (Linearization.ctxtGrammar ctxt) (Linearization.ctxtLang ctxt) s
              & map (\t -> Annotated.mkLinearization ctxt t t t)
              & foldl1 Annotated.mergeL
              & toList
              & map getNodes
  getWord (Menu.Annotated word _) = word
  getNodes (Menu.Annotated _ nodes) = intercalate "+" (Set.toList nodes)
  maybeVerbose docA docB
    | verbose   = Doc.fill 60 docA <+> docB
    | otherwise = docA

prettyLin ∷ ∀ tok a . Pretty tok => Menu.Selection → [tok] → Doc a
prettyLin sel tokens = Doc.hsep $ map go $ highlight sel tokens
  where
  go ∷ Either Bool tok → Doc a
  go = \case
    Left a     → hl a
    Right tok  → pretty tok
  hl ∷ Bool → Doc a
  hl = bool "[" "]" >>> pretty @String

highlight ∷ Menu.Selection → [a] → [Either Bool a]
highlight (toList → xs) (zip [0..] . map pure → ys)
  = snd <$> closes `weave` opens `weave` ys
  where
  opens  ∷ [(Int, Either Bool a)]
  opens  = zip (map (pred . fst . Menu.runInterval) xs) (repeat (Left False))
  closes ∷ [(Int, Either Bool a)]
  closes  = zip (map (pred . snd . Menu.runInterval) xs) (repeat (Left True))

weave ∷ [(Int, a)] → [(Int, a)] → [(Int, a)]
weave [] ys = ys
weave xs [] = xs
weave xs@(x@(n, _):xss) ys@(y@(m, _):yss)
  | n < m     = x : weave xss ys
  | otherwise = y : weave xs  yss

-- | @'getMenu' s@ gets a menu for a sentence @s@.
getMenuFor
  ∷ String -- ^ The sentence to parse
  → Repl Menu
getMenuFor s = do
  c ← getContext
  pure $ Menu.getMenuItems c s

getContext ∷ Repl Context
getContext = gets $ \(Env { .. }) → ctxt

options ∷ Repl.Options (HaskelineT (Muste IO))
options =
  [ "lang" |> oneArg setLang
  ]
  where
  (|>) = (,)

oneArg ∷ MonadIO m ⇒ (a → m b) → [a] → m ()
oneArg a = \case
  [l] → void $ a l
  _   → throwOneArgErr

data AppException
  = SelectionNotFound
  | OneArgErr
  deriving (Exception)

instance Show AppException where
  show e = "ERROR: " <> case e of
    SelectionNotFound → "ERROR: Selection not found"
    OneArgErr → "One argument plz"

showErr ∷ MonadIO m ⇒ Exception e ⇒ e → m ()
showErr = liftIO . putStrLn . displayException

throwOneArgErr ∷ MonadIO m ⇒ m ()
throwOneArgErr = showErr OneArgErr

setLang ∷ MonadState Env m ⇒ String → m ()
setLang lang = modify $ \e → e { lang }

-- Currently no completion support.
completer ∷ Repl.CompleterStyle (Muste IO)
completer = Repl.Word (const (pure mempty))

ini ∷ Repl ()
ini = liftIO $ putStrLn $ unlines
  [ "Type in a sentence to get the menu for that sentence."
  , ""
  , "Please note that sentences that cannot be parsed are silently ignored."
  , "An empty menu will be displayed (just newline) this is likely caused"
  , "by the sentence not being understood by the current grammar."
  , ""
  , "Also the current grammar is hard-coded to be:"
  , ""
  , "    novo_modo/Exemplum"
  , ""
  , "The language can be specified on the command line (run with `--help`"
  , "to see usage)."
  ]
