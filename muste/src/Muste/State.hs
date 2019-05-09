{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language
 OverloadedStrings
#-}

module Muste.State
  ( MUState
  , emptyMUState
  , lookupLessonMU
  , loadGrammarsMU
  , loadGrammarMU
  , getMenusMU
  , getContextMU
  , editDistanceMU
  , parseSentenceMU
  , LangLin(..)
  , LinMenus(..)
  ) where

import Control.Monad (foldM)
import System.FilePath ((</>))

import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import Data.Text (Text)

import Muste.Grammar (Grammar, readGrammar, parseSentence)
import Muste.AdjunctionTrees (BuilderInfo, getAdjunctionTrees, AdjunctionTrees)
import Muste.Tree (TTree, treeDiff) 
import Muste.Menu (Menu, getMenu, unMenu)
import Muste.Prune (PruneOpts)
import Muste.Selection (Selection(Selection))

import Muste.Sentence
  ( Context(Context, ctxtGrammar, ctxtLang, ctxtPrecomputed)
  , Linearization
  , textRep
  )

import qualified PGF


newtype MUState = MUState (Map Text (Grammar, AdjunctionTrees))

emptyMUState :: MUState
emptyMUState = MUState mempty

lookupLessonMU :: MUState -> Text -> (Grammar, AdjunctionTrees)
lookupLessonMU (MUState grammarsM) grname 
    = fromMaybe (error $ "Grammar not loaded: " ++ Text.unpack grname) 
    $ Map.lookup grname grammarsM 


loadGrammarsMU :: FilePath -> MUState -> [(Text, FilePath, BuilderInfo)] -> IO MUState
loadGrammarsMU grammardir = foldM (loadGrammarMU grammardir)


loadGrammarMU :: FilePath -> MUState -> (Text, FilePath, BuilderInfo) -> IO MUState
loadGrammarMU grammardir mustate@(MUState grammarsM) (grname, grpath, binfo)
  = if Map.member grname grammarsM then
      do putStrLn $ "Grammar already loaded: " ++ show grname
         return mustate
    else
      do putStrLn $ "Loading grammar " ++ show grname ++ ": " ++ grpath
         grammar <- readGrammar $ Text.pack $ grammardir </> grpath
         let adjtrees = getAdjunctionTrees binfo grammar
         let grammarsM' = Map.insert grname (grammar, adjtrees) grammarsM
         return $ MUState grammarsM'


getContextMU :: MUState -> Text -> Text -> Context
getContextMU mustate grname lang
    = Context { ctxtGrammar = grammar
                , ctxtLang    = PGF.mkCId (Text.unpack lang)
                , ctxtPrecomputed = adjtrees
                }
  where (grammar, adjtrees) = lookupLessonMU mustate grname


getMenusMU :: MUState -> PruneOpts -> Text -> LangLin -> LinMenus
getMenusMU mustate opts grname (LangLin lang lin) = LinMenus annotated menus
  where 
    ctxt = getContextMU mustate grname lang
    menus = getMenu opts ctxt lin
    emptySel = Selection mempty
    annotated = case Map.lookup emptySel (unMenu menus) of
                  Nothing -> lin
                  Just ms -> snd $ head $ Set.toList ms


editDistanceMU :: MUState -> Text -> LangLin -> LangLin -> Int
editDistanceMU mustate grname (LangLin lang1 lin1) (LangLin lang2 lin2)
  = minimum [ treeDiff t1 t2 |
              t1 <- parseSentence grammar pgflang1 (textRep lin1),
              t2 <- parseSentence grammar pgflang2 (textRep lin2) ]
  where
    (grammar, _) = lookupLessonMU mustate grname
    pgflang1 = PGF.mkCId (Text.unpack lang1)
    pgflang2 = PGF.mkCId (Text.unpack lang2)


parseSentenceMU :: MUState -> Text -> LangLin -> [TTree]
parseSentenceMU mustate grname (LangLin lang lin)
    = parseSentence grammar pgflang (textRep lin)
  where 
    (grammar, _) = lookupLessonMU mustate grname
    pgflang = PGF.mkCId (Text.unpack lang)


data LangLin = LangLin Text Linearization

instance ToJSON LangLin where
  toJSON (LangLin lang lin) = Aeson.object
    [ "lang" .= lang, "lin"  .= lin ]

instance FromJSON LangLin where
  parseJSON = Aeson.withObject "LangLin" $ \v ->
    LangLin <$> v .: "lang" <*> v .: "lin"


data LinMenus = LinMenus Linearization Menu

instance ToJSON LinMenus where
  toJSON (LinMenus lin menus) = Aeson.object
    [ "lin" .= lin, "menus" .= menus ]

instance FromJSON LinMenus where
  parseJSON = Aeson.withObject "LinMenus" $ \v ->
    LinMenus <$> v .: "lin" <*> v .: "menus"

