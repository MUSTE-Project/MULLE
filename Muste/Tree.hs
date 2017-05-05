{- | This module provides implementations of different kinds of syntax trees and functions to manipulate them
-}
module Muste.Tree (TTree(..),LTree(..),Path,Pos,ttreeToGFAbsTree,gfAbsTreeToTTree,ttreeToLTree,getPath,generateSet,generateListSimple,selectNode,getTreeCat,hasMetas,replaceNode) where

import Muste.Tree.Internal
