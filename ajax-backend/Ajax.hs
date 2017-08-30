{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}

module Ajax where

import Data.Aeson
import Data.Text
import Data.Monoid
import Control.Exception
import qualified Data.ByteString.Lazy.Char8 as B
import Data.Either

data ClientTree = CT {
  cgrammar :: String,
  ctree :: String
  } deriving (Show) ;
  
data ClientMessage = Null | CM {
  cscore :: Int ,
  ca :: ClientTree ,
  cb :: ClientTree
  } deriving (Show) ;
  
instance FromJSON ClientTree where
  parseJSON = withObject "ClientTree" $ \v -> CT
    <$> v .: "grammar"
    <*> v .: "tree"
    
instance FromJSON ClientMessage where
  parseJSON = withObject "ClientMessage" $ \v ->
    CM
      <$> v .: "score"
      <*> v .: "a"
      <*> v .: "b"

instance ToJSON ClientTree where
    -- this generates a Value
    toJSON (CT tree grammar) =
      object ["tree" .= tree, "grammar" .= grammar]
    -- this encodes directly to a bytestring Builder
    toEncoding (CT tree grammar) =
      pairs ("tree" .= tree <> "grammar" .= grammar)

instance ToJSON ClientMessage where
    -- this generates a Value
    toJSON (CM score a b) =
      object ["score" .= score , "a" .= a , "b" .= b]
    -- this encodes directly to a bytestring Builder
    toEncoding (CM score a b) =
      pairs ("score" .= score <> "a" .= a <> "b" .= b)

data ServerTree = ST {
  grammar :: String ,
  lin :: [String] ,
  menu :: [((Int,Int),[ClientTree])]
  } deriving (Show) ;

data ServerMessage = SM {
  ssuccess :: Bool ,
  sscore :: Int ,
  sa :: ServerTree ,
  sb :: ServerTree
  } deriving (Show) ;

instance FromJSON ServerTree where
  parseJSON = withObject "ServerTree" $ \v -> ST
    <$> v .: "grammar"
    <*> v .: "lin"
    <*> v .: "menu"
    
instance FromJSON ServerMessage where
  parseJSON = withObject "ServerMessage" $ \v -> SM
    <$> v .: "success"
    <*> v .: "score"
    <*> v .: "a"
    <*> v .: "b"
    
instance ToJSON ServerTree where
    -- this generates a Value
    toJSON (ST grammar lin menu) =
      object ["grammar" .= grammar , "lin" .= lin , "menu" .= menu]
    -- this encodes directly to a bytestring Builder
    toEncoding (ST grammar lin menu) =
      pairs ("grammar" .= grammar <> "lin" .= lin <> "menu" .= menu)

instance ToJSON ServerMessage where
    -- this generates a Value
    toJSON (SM success score a b) =
      object ["success" .= success , "score" .= score , "a" .= a , "b" .= b]
    -- this encodes directly to a bytestring Builder
    toEncoding (SM success score a b) =
      pairs ("success" .= success <> "score" .= score <> "a" .= a <> "b" .= b)

data ClientMessageException = CME String deriving (Show)

instance Exception ClientMessageException

decodeClientMessage :: String -> ClientMessage
decodeClientMessage s =
  let rcm = eitherDecode (B.pack s) :: Either String ClientMessage
  in
    either (throw . CME) id rcm

encodeServerMessage :: ServerMessage -> String
encodeServerMessage sm =
  B.unpack $ encode sm
