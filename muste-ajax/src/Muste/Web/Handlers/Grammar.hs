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


getMenus :: SessionToken MenuRequest -> MULLE v Aeson.Value
getMenus (SessionToken token _course (MenuRequest grammar solution problem))
  = do verifySession token
       must <- asks muState
       let assemble = Muste.getMenusMU must Muste.emptyPruneOpts grammar
       return $ Aeson.object [ "solution" .= assemble solution, "problem" .= assemble problem ]


editDistance :: SessionToken MenuRequest -> MULLE v Aeson.Value
editDistance (SessionToken token _course (MenuRequest grammar solution problem))
  = do verifySession token
       must <- asks muState
       let distance = Muste.editDistanceMU must grammar solution problem
       return $ Aeson.object [ "distance" .= distance ]


data MenuRequest = MenuRequest Text Muste.LangLin Muste.LangLin

instance ToJSON MenuRequest where
  toJSON (MenuRequest grammar solution problem) = Aeson.object
    [ "grammar" .= grammar, "solution" .= solution, "problem" .= problem ]

instance FromJSON MenuRequest where
  parseJSON = Aeson.withObject "MenuRequest" $ \v ->
    MenuRequest <$> v .: "grammar" <*> v .: "solution" <*> v .: "problem"

