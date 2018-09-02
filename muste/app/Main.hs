{-# OPTIONS_GHC -Wall #-}
{-# Language CPP, RecordWildCards, NamedFieldPuns, TemplateHaskell,
  DeriveAnyClass, OverloadedStrings
#-}
module Main (main) where

import Prelude hiding (fail)
import System.Environment (getArgs)
import System.Console.Repline (HaskelineT, runHaskelineT)
import System.Console.Haskeline (Settings, defaultSettings)
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
import Data.List (intercalate)
import qualified Data.Set as Set
import qualified Data.Containers as Mono
import GHC.Exts (toList)

import Muste
import Muste.Common
import Muste.Util
import qualified Muste.Grammar.Internal as Grammar
import Muste.Menu.New (NewFancyMenu)
import qualified Muste.Menu.New      as Menu
import qualified Muste.Sentence.Annotated as Annotated
import qualified Muste.Linearization.Internal as Linearization

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
main = getArgs >>= gomain

gomain :: [String] -> IO ()
gomain [s]
  = runHaskelineT defaultSettings (updateMenu s)
  & flip evalStateT defEnv
gomain []
  = Repl.evalRepl "§ " updateMenu options completer ini
  & flip evalStateT defEnv

updateMenu ∷ String → Repl ()
updateMenu s = do
  ctxt ← getContext
  m ← getMenuFor s
  liftIO $ do
    putStrLn $ "Sentence is now: " <> s
    putDocLn $ prettyMenu ctxt s m
  setMenu m

prettyMenu ∷ Context → String → NewFancyMenu → Doc a
prettyMenu ctxt s = Doc.vsep . fmap (uncurry go) . open
  where
  open = fmap @[] (fmap @((,) Menu.Selection) Set.toList)
    . Mono.mapToList
  go ∷ Menu.Selection
    → [(Menu.Selection, Menu.Linearization Menu.Annotated)]
    → Doc a
  go sel xs = Doc.vcat
    [ ""
    , Doc.fill 60 (Menu.prettySelection sel <> ":" <+> prettyLin sel (words s))
      <+> prettyLin sel annotated
    , Doc.vcat $ fmap gogo xs
    ]
  gogo ∷ (Menu.Selection, Menu.Linearization Menu.Annotated) → Doc a
  gogo (sel, lin) = Doc.fill 60 (prettyLin sel (map getWord (toList lin)))
                    <+> prettyLin sel (map getNodes (toList lin))
  annotated = Grammar.parseSentence (Linearization.ctxtGrammar ctxt) (Linearization.ctxtLang ctxt) s
              & map (\t -> Annotated.mkLinearization ctxt t t t)
              & foldl1 Annotated.mergeL
              & toList
              & map getNodes
  getWord (Menu.Annotated word _) = word
  getNodes (Menu.Annotated _ nodes) = intercalate "+" (Set.toList nodes)

prettyLin ∷ Doc.Pretty tok => Menu.Selection → [tok] → Doc a
prettyLin sel tokens = Doc.hsep $ map go $ highlight sel tokens
  where
  go (b, tok)
    | b         = Doc.brackets $ pretty tok
    | otherwise = pretty tok

highlight ∷ Menu.Selection → [a] → [(Bool, Maybe a)]
highlight sel xs = go $ zip [0..] xs
  where
  go ∷ [(Int, a)] → [(Bool, Maybe a)]
  go [] = if (length xs, length xs) `elem` sel then [insertion] else []
  go ((n, a) : xs) = if (n, n) `elem` sel then insertion : ys else ys 
    where ys = (selected n sel, Just a) : go xs
  insertion = (True, Nothing)
  selected ∷ Int → Menu.Selection → Bool
  selected n = any (within n)
  within ∷ Int → (Int, Int) → Bool
  within x (a, b) = a <= x && x < b

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
