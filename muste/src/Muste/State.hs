{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language
 OverloadedStrings
#-}

module Muste.State
  ( MUState
  , emptyMUState
  , loadGrammarsMU
  , loadGrammarMU
  , getMenusMU
  , editDistanceMU
  , LangLin
  , LinMenus
  ) where

import Control.Monad (foldM)
import System.FilePath ((</>))

import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Text as Text
import Data.Text (Text)

import Muste.Grammar (Grammar, readGrammar, parseSentence)
import Muste.AdjunctionTrees (BuilderInfo, getAdjunctionTrees, AdjunctionTrees)
import Muste.Tree (treeDiff) ----TTree
import Muste.Menu (Menu, getMenu, unMenu)
import Muste.Prune (PruneOpts)
import Muste.Selection (Selection(Selection))

import Muste.Sentence
  ( Context(Context, ctxtGrammar, ctxtLang, ctxtPrecomputed)
  , Linearization
  , textRep
  )

import qualified PGF


data MUState = MUState (Map Text (Grammar, AdjunctionTrees))


emptyMUState :: MUState
emptyMUState = MUState mempty


lookupLessonMU :: MUState -> Text -> (Grammar, AdjunctionTrees)
lookupLessonMU (MUState grammarsM) grname
  = case Map.lookup grname grammarsM of
      Nothing -> error $ "Grammar not loaded: " ++ Text.unpack grname
      Just result -> result


loadGrammarsMU :: FilePath -> MUState -> [(Text, FilePath, BuilderInfo)] -> IO MUState
loadGrammarsMU grammardir = foldM (loadGrammarMU grammardir)


loadGrammarMU :: FilePath -> MUState -> (Text, FilePath, BuilderInfo) -> IO MUState
loadGrammarMU grammardir mustate@(MUState grammarsM) (grname, grpath, binfo)
  = if Map.member grname grammarsM then
      do putStrLn $ "Lesson already loaded: " ++ show grname
         return mustate
    else
      do putStrLn $ "Loading lesson grammar: " ++ show (grname, grpath)
         grammar <- readGrammar $ Text.pack $ grammardir </> grpath
         let adjtrees = getAdjunctionTrees binfo grammar
         let grammarsM' = Map.insert grname (grammar, adjtrees) grammarsM
         return $ MUState grammarsM'


getMenusMU :: MUState -> PruneOpts -> Text -> LangLin -> LinMenus
getMenusMU mustate opts lesson (LangLin lang lin) = LinMenus annotated menus
  where (grammar, adjtrees) = lookupLessonMU mustate lesson
        ctxt = Context { ctxtGrammar = grammar
                                , ctxtLang    = PGF.mkCId (Text.unpack lang)
                                , ctxtPrecomputed = adjtrees
                                }
        menus = getMenu opts ctxt lin
        emptySel = Selection mempty
        annotated = case Map.lookup emptySel (unMenu menus) of
                      Nothing -> lin
                      Just ms -> snd $ head $ Set.toList ms


editDistanceMU :: MUState -> Text -> LangLin -> LangLin -> Int
editDistanceMU mustate lesson (LangLin lang1 lin1) (LangLin lang2 lin2)
  = minimum [ treeDiff t1 t2 |
              t1 <- parseSentence grammar pgflang1 (textRep lin1),
              t2 <- parseSentence grammar pgflang2 (textRep lin2) ]
  where
    (grammar, _) = lookupLessonMU mustate lesson
    pgflang1 = PGF.mkCId (Text.unpack lang1)
    pgflang2 = PGF.mkCId (Text.unpack lang2)


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

