{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language DeriveLift, RecordWildCards #-}
module Muste.Web.Config.Types
  ( User(..)
  ) where

import Data.Aeson (FromJSON(..), ToJSON(..), (.:), (.=))
import qualified Data.Aeson as Aeson
import Language.Haskell.TH.Syntax (Lift)

data User = User
  { name     :: String
  , password :: String
  , enabled  :: Bool
  }

deriving stock instance Show User
deriving stock instance Lift User

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
