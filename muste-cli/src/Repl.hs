{-# OPTIONS_GHC -Wall #-}
{-# Language
 OverloadedStrings
#-}

module Repl
  ( interactively
  , detachedly
  , Env(..)
  , grName
  ) where

import qualified System.Console.Haskeline as H

import Control.Monad.IO.Class (liftIO)
import Data.Text.Prettyprint.Doc (Doc, Pretty(pretty), (<+>))
import qualified Data.Text.Prettyprint.Doc as Doc
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Set as Set
import qualified Data.Containers as Mono
import qualified Data.List as List

import qualified Muste
import qualified Options

grName :: Text
grName = "GRAMMAR"

-- | Data used during execution of the REPL.
data Env = Env
  { printOpts :: Options.PrintOptions
  , pruneOpts :: Muste.PruneOpts
  , muState   :: Muste.MUState
  , muLang    :: Text
  }


detachedly :: Env -> [Text] -> IO ()
detachedly env sentences = mapM_ (updateMenu env) sentences


interactively :: Env -> IO ()
interactively env = H.runInputT H.defaultSettings (liftIO initial_text >> loop)
  where
    loop = H.getInputLine "\nMULLE> " >>= handle
    handle Nothing = return ()
    handle (Just "") = H.outputStrLn "Ctrl-D to quit" >> loop
    handle (Just input) = liftIO (updateMenu env (Text.pack input)) >> loop


updateMenu :: Env -> Text -> IO ()
updateMenu env sent = putStrLn $ unlines
    [ ""
    , "+---------------------------------------------------------------------"
    , "+-- " ++ Text.unpack sent
    , show doc
    ]
  where 
    menus = getMenuFor env sent
    doc = if Options.printCompact (printOpts env) 
          then prettyCompact sent menus
          else prettyMenu env sent menus


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
            (pretty sel <> ":" <+> prettyLin sel (Text.words sent))
        <+> pretty (length items)


prettyMenu :: Env -> Text -> Muste.Menu -> Doc a
prettyMenu env sent menus
  = Doc.vsep
    [ Doc.vcat
      [ ""
      , maybeVerbose
        (pretty sel <> ":" <+> prettyLin sel (Text.words sent))
        (prettyLin sel (map getNodes sentLin))
      , Doc.vcat
        [ maybeVerbose
          (prettyLin sel' (map getWord lin))
          (prettyLin sel' (map getNodes lin))
        | (sel', Muste.Linearization lin) <- Set.toList items ]
      ]
    | (sel, items) <- Mono.mapToList menus ]
 where
    sentLin :: [Muste.Token]
    Muste.Linearization sentLin
        = maybe (error "Can't find linearization nodes in menu")
                (snd . head . Set.toList) 
                (Mono.lookup mempty menus)
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
    where intervals   = [ Muste.runInterval int | int <- Set.toList (Muste.runSelection sel) ]
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


initial_text :: IO ()
initial_text = putStrLn $ unlines
  [ "Type in a sentence to get the menu for that sentence."
  , ""
  , "Please note that sentences that cannot be parsed are silently ignored."
  , "An empty menu will be displayed (just newline) this is likely caused"
  , "by the sentence not being understood by the current grammar."
  , ""
  , "The grammar and language must be specified on the command line"
  , "(run with `--help` to see usage)."
  ]
