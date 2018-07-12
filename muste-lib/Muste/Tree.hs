{- | This module provides implementations of different kinds of syntax trees and functions to manipulate them
-}
module Muste.Tree
  ( TTree(TNode,TMeta)
  , FunType(Fun, NoType)
  , LTree(..)
  , Path
  , Pos
  , getPath
  , ttreeToLTree
  , getPathes
  -- , maxDepth
  , getTreeCat
  -- , generateTrees
  , selectNode
  , replaceNode
  , isValid
  , countNodes
  -- , countMatchedNodes
  ) where

import Muste.Tree.Internal
