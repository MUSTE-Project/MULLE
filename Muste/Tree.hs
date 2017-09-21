{- | This module provides implementations of different kinds of syntax trees and functions to manipulate them
-}
module Muste.Tree (TTree(..),LTree(..),Path,Pos,ttreeToGFAbsTree,gfAbsTreeToTTreeWithGrammar,gfAbsTreeToTTreeWithPGF,ttreeToLTree,getPath,getPathes,maxDepth,generateList,selectNode,getTreeCat,hasMetas,isValid,replaceNode) where

import Muste.Tree.Internal
import Muste.Feat
