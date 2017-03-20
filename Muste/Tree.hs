{- | This module provides implementations of different kinds of syntax trees and functions to manipulate them
-}
module Muste.Tree (TTree(..),LTree(..),Path,Pos,ttreeToGFAbsTree,gfAbsTreeToTTree,ttreeToLTree,getPath,generateSet,generateList,selectNode,getTreeCat,hasMetas,replaceNode) where

import Muste.Tree.Internal

generateList = generateListPGF

combine = combineSet
