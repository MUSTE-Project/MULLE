{- | This module provides implementations of different kinds of syntax trees and functions to manipulate them
-}
module Muste.Tree (TTree(..),MetaTTree(..),LTree(..),Path,Pos,ttreeToGFAbsTree,gfAbsTreeToTTree,ttreeToLTree,generate,match,makeMeta,selectNode,getTreeCat) where

import Muste.Tree.Internal
