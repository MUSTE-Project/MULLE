{- | This module provides implementations of different kinds of syntax trees and functions to manipulate them
-}
module Muste.Tree (TTree(..),LTree(..),Path,Pos,getPath,ttreeToLTree,ttreeToGFAbsTree,getPathes,maxDepth,getTreeCat,generateTrees,selectNode,replaceNode,gfAbsTreeToTTree,isValid) where

import Muste.Tree.Internal
import Muste.Feat
