{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 OverloadedStrings,
 RecordWildCards
#-}

module Muste.Web.Config.Types
  ( User(..)
  ) where

import Data.Aeson (FromJSON(..), ToJSON(..), (.:), (.=))
import qualified Data.Aeson as Aeson

data User = User
  { name     :: String
  , password :: String
  , enabled  :: Bool
  }
  deriving (Show)

instance FromJSON User where
  parseJSON = Aeson.withObject "user" $ \v -> User
    <$> v .: "name"
    <*> v .: "password"
    <*> v .: "enabled"

instance ToJSON User where
  toJSON User{..} = Aeson.object
    [ "name"    .= name
    , "enabled" .= enabled
    ]
