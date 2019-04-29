{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 OverloadedStrings
#-}

module Muste.Web.Handlers.Grammar
  ( getMenus
  , editDistance
  ) where

import Control.Monad.Reader (asks)
import Data.Text (Text)

import qualified Data.Aeson as Aeson
import Data.Aeson ((.=), (.:), FromJSON(parseJSON), ToJSON(toJSON))

import qualified Muste

import Muste.Web.Class (MULLE, muState)
import Muste.Web.Handlers.Session (verifySession, SessionToken(..))


getMenus :: SessionToken MenuRequest -> MULLE v MenuResponse
getMenus (SessionToken token (MenuRequest lesson src trg))
  = do verifySession token
       must <- asks muState
       let assemble = Muste.getMenusMU must Muste.emptyPruneOpts lesson
       return $ MenuResponse (assemble src) (assemble trg)


editDistance :: SessionToken MenuRequest -> MULLE v Aeson.Value
editDistance (SessionToken token (MenuRequest lesson src trg))
  = do verifySession token
       must <- asks muState
       let distance = Muste.editDistanceMU must lesson src trg
       return $ Aeson.object [ "distance" .= distance ]


data MenuRequest = MenuRequest Text Muste.LangLin Muste.LangLin

instance ToJSON MenuRequest where
  toJSON (MenuRequest grammar src trg) = Aeson.object
    [ "grammar" .= grammar, "src" .= src, "trg" .= trg ]

instance FromJSON MenuRequest where
  parseJSON = Aeson.withObject "MenuRequest" $ \v ->
    MenuRequest <$> v .: "grammar" <*> v .: "src" <*> v .: "trg"


data MenuResponse = MenuResponse Muste.LinMenus Muste.LinMenus

instance ToJSON MenuResponse where
  toJSON (MenuResponse src trg) = Aeson.object
    [ "src" .= src, "trg" .= trg ]

instance FromJSON MenuResponse where
  parseJSON = Aeson.withObject "MenuResponse" $ \v ->
    MenuResponse <$> v .: "src" <*> v .: "trg"
