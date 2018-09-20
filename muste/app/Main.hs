{-# OPTIONS_GHC -Wall #-}
{-# Language RecordWildCards, NamedFieldPuns, TemplateHaskell,
  DeriveAnyClass, OverloadedStrings #-}
module Main (main) where

import Prelude (Float)
import Muste.Prelude
import System.Console.Repline
  (HaskelineT, runHaskelineT)
import qualified System.Console.Haskeline     as Repl
import qualified System.Console.Repline       as Repl
import Data.ByteString (ByteString)
import Data.String.Conversions (convertString)
import qualified Muste.Grammar.Embed          as Embed
import Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc    as Doc
import qualified Data.Set                     as Set
import qualified Data.Containers              as Mono
import Control.Monad.State.Strict
import Data.List (intercalate)
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

import Muste hiding (getMenu)
import Muste.Common
import Muste.Util
import qualified Muste.Grammar.Internal       as Grammar
import Muste.Menu (Menu)
import qualified Muste.Menu.Internal          as Menu
import qualified Muste.Sentence.Annotated     as Annotated
import qualified Muste.Linearization.Internal as Linearization

import Options (Options(Options))
import qualified Options

grammar :: Grammar
grammar = Grammar.parseGrammar $ convertString $ snd grammar'
  where
  grammar' ∷ (Text, ByteString)
  grammar' = $(Embed.grammar "novo_modo/Exemplum")

data Env = Env
  { lang ∷ String
  , menu ∷ Menu
  , ctxt ∷ Context
  }

makeEnv ∷ Options → Env
makeEnv opts@(Options{..}) = Env defLang mempty c
  where
  c ∷ Context
  c = unsafeGetContext (builderInfo opts) grammar language

defLang ∷ String
defLang = "Swe"

type Repl a = HaskelineT (StateT Env IO) a

builderInfo ∷ Options → BuilderInfo
builderInfo Options{..} = BuilderInfo { searchDepth }

main :: IO ()
main = do
  opts ← Options.getOptions
  let e ∷ Env
      e = makeEnv opts
  let sentences = Options.sentences opts
  -- If there are any sentences supplied on the command line, run them
  -- all.
  void $ traverse (nonInteractive e) sentences
  -- If we are also in interactive mode, start the interactive session.
  let interactive = Options.interactiveMode opts
  when interactive $ repl e    

nonInteractive :: Env → String -> IO ()
nonInteractive env s
  = runHaskelineT Repl.defaultSettings (updateMenu s)
  & flip evalStateT env

repl ∷ Env → IO ()
repl env
  = Repl.evalRepl "§ " updateMenu options completer ini
  & flip evalStateT env

updateMenu ∷ String → Repl ()
updateMenu s = do
  ctxt ← getContext
  liftIO $ timeCommand "Precalculate adjunction trees" $ do
    let adjtrees = Mono.mapToList $ Linearization.ctxtPrecomputed ctxt
    let adjsizes = [ (cat, length trees) | (cat, trees) <- adjtrees ]
    printf "\nN:o adjunction trees = %d\n" (sum (map snd adjsizes))
  m ← getMenuFor s
  liftIO $ timeCommand "Update menu" $ do
    putStrLn $ "Sentence is now: " <> s
    putDocLn $ prettyMenu ctxt s m
  setMenu m

timeCommand :: String -> IO a -> IO a
timeCommand title cmd = do
    time0 <- getCPUTime
    result <- cmd
    time1 <- getCPUTime
    let secs :: Float = fromInteger (time1-time0) * 1e-12
    printf "\n>>> %s: %.2f s <<<\n\n" title secs
    return result

prettyMenu ∷ Context → String → Menu → Doc a
prettyMenu ctxt s = Doc.vsep . fmap (uncurry go) . open
  where
  open = fmap @[] (fmap @((,) Menu.Selection) Set.toList)
    . Mono.mapToList
  go ∷ Menu.Selection
    → [(Menu.Selection, Menu.Linearization Menu.Annotated)]
    → Doc a
  go sel xs = Doc.vcat
    [ ""
    , Doc.fill 60 (pretty sel <> ":" <+> prettyLin sel (words s))
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

setMenu ∷ Menu → Repl ()
setMenu menu = modify $ \e → e { menu }

getContext ∷ Repl Context
getContext = gets $ \(Env { .. }) → ctxt

getMenu ∷ Repl Menu
getMenu = gets $ \(Env { .. }) → menu

options ∷ Repl.Options (HaskelineT (StateT Env IO))
options =
  [ "lang" |> oneArg setLang
  , "sel"  |> setSel
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

setSel ∷ [String] → Repl ()
setSel args = do
  -- case readMaybe @[(Int, Int)] str of
  case traverse (readMaybe @(Int, Int)) args of
    Nothing → liftIO $ putStrLn
      $  "Expecting a space-seperated list of pairs of numbers.  "
      <> "Like so: \"(0,1) (2,3)\""
    Just sel → do
      m ← getMenu
      case lookupFail mempty (fromL sel) m of
        Nothing → showErr SelectionNotFound
        Just ts → liftIO $ putDocLn $ pretty $ Set.toList ts
  where
  fromL ∷ [(Int, Int)] → Menu.Selection
  fromL = Menu.Selection . fmap Menu.Interval

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
