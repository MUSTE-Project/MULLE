{-# OPTIONS_GHC -Wall #-}
{-# Language CPP, RecordWildCards, NamedFieldPuns, TemplateHaskell,
  DeriveAnyClass, OverloadedStrings
#-}
module Main (main) where

import Prelude hiding (fail)
import System.Console.Repline (HaskelineT)
import qualified System.Console.Repline as Repl
import Control.Exception (Exception, displayException)
import Control.Monad.State.Strict hiding (fail)
import Data.Function ((&))
#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup((<>)))
#endif
import Data.ByteString (ByteString)
import Data.String.Conversions (convertString)
import qualified Muste.Grammar.Embed as Embed
import Data.Text.Prettyprint.Doc (Doc, (<+>), pretty)
import qualified Data.Text.Prettyprint.Doc as Doc
import Text.Read
import Data.Text (Text)
import qualified Data.Set as Set
import qualified Data.Containers as Mono
import GHC.Exts (toList)

import Muste
import Muste.Common
import Muste.Util
import qualified Muste.Grammar.Internal as Grammar
import Muste.Menu.New (NewFancyMenu)
import qualified Muste.Menu.New      as Menu

grammar :: Grammar
grammar = Grammar.parseGrammar $ convertString $ snd grammar'
  where
  grammar' ∷ (Text, ByteString)
  grammar' = $(Embed.grammar "novo_modo/Exemplum")

defCtxt ∷ Context
defCtxt = unsafeGetContext grammar "ExemplumSwe"

data Env = Env
  { lang ∷ String
  , menu ∷ NewFancyMenu
  , ctxt ∷ Context
  }

defEnv ∷ Env
defEnv = Env defLang mempty defCtxt

defLang ∷ String
defLang = "Swe"

type Repl a = HaskelineT (StateT Env IO) a

main :: IO ()
main
  = Repl.evalRepl "§ " updateMenu options completer ini
  & flip evalStateT defEnv

updateMenu ∷ String → Repl ()
updateMenu s = do
  m ← getMenuFor s
  liftIO $ do
    putStrLn $ "Sentence is now: " <> s
    putDocLn $ prettyMenu s m
  setMenu m

prettyMenu ∷ String → NewFancyMenu → Doc a
prettyMenu s = Doc.vsep . fmap (uncurry go) . open
  where
  open = fmap @[] (fmap @((,) Menu.Selection) Set.toList)
    . Mono.mapToList
  go ∷ Menu.Selection
    → [(Menu.Selection, Menu.Linearization Menu.Unannotated)]
    → Doc a
  go sel xs = Doc.vcat
    [ Doc.brackets (pretty sel) <+> "<>" <+> pretty @String s
    , Doc.vcat $ fmap gogo xs
    ]

gogo ∷ (Menu.Selection, Menu.Linearization Menu.Unannotated) → Doc a
gogo (xs, lin) = Doc.hsep $ map go $ highlight xs (toList lin)
  where
  go ∷ (Bool, Menu.Unannotated) → Doc a
  go (b, tok)
    | b         = Doc.brackets $ pretty tok
    | otherwise = pretty tok

highlight ∷ Menu.Selection → [a] → [(Bool, a)]
highlight sel xs = map go $ zip [0..] xs
  where
  go ∷ (Int, a) → (Bool, a)
  go (n, a) = (selected n sel, a)
  selected ∷ Int → Menu.Selection → Bool
  selected n = \case
    [] → False
    (x:xss) → (n `within` x) || selected n xss
  within ∷ Int → (Int, Int) → Bool
  within x (a, b)
    | x < a = False
    | x > b = False
    | otherwise = True

-- | @'getMenu' s@ gets a menu for a sentence @s@.
getMenuFor
  ∷ String -- ^ The sentence to parse
  → Repl NewFancyMenu
getMenuFor s = do
  c ← getContext
  pure $ Menu.getMenuItems c s

setMenu ∷ NewFancyMenu → Repl ()
setMenu menu = modify $ \e → e { menu }

getContext ∷ Repl Context
getContext = gets $ \(Env { .. }) → ctxt

getMenu ∷ Repl NewFancyMenu
getMenu = gets $ \(Env { .. }) → menu

options ∷ Repl.Options (HaskelineT (StateT Env IO))
options =
  [ "lang" |> oneArg setLang
  , "sel"  |> oneArg setSel
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

setSel ∷ String → Repl ()
setSel str = do
  case readMaybe @Menu.Selection str of
    Nothing → liftIO $ putStrLn "readMaybe @Menu.Selection: No parse"
    Just sel → do
      m ← getMenu
      case lookupFail mempty sel m of
        Nothing → showErr SelectionNotFound
        Just ts → liftIO $ putDocLn $ pretty $ Set.toList ts

showErr ∷ MonadIO m ⇒ Exception e ⇒ e → m ()
showErr = liftIO . putStrLn . displayException

throwOneArgErr ∷ MonadIO m ⇒ m ()
throwOneArgErr = showErr OneArgErr

setLang ∷ MonadState Env m ⇒ String → m ()
setLang lang = modify $ \e → e { lang }

-- Currently no completion support.
completer ∷ Repl.CompleterStyle (StateT Env IO)
completer = Repl.Word (const (pure mempty))

ini ∷ Repl ()
ini = liftIO $ putStrLn $ unlines
  [ "Type in a sentence to get the menu for that sentence"
  , "This will set and display the \"active\" menu"
  , "You can select an entry in the active menu with e.g.:"
  , ""
  , "    :sel [(0,1)]"
  , ""
  , "Please note that sentences that cannot be parsed are silently ignored"
  , "An empty menu will be displayed (just newline) this is likely caused"
  , "by the sentence not being understood by the current grammar."
  , ""
  , "Also the current grammar is hard-coded to be:"
  , "    novo_modo/Exemplum"
  , "    ExemplumSwe"
  ]
