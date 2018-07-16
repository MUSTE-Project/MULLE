-- | This module provides a representation of gramatically structured
-- sentences from natural language called 'TTree's.  The
-- representation lends ideas from type theory (hence the name 'TTree'
-- @~@ /Typed Trees/).
module Muste.Tree
  ( TTree(TNode,TMeta)
  , FunType(Fun, NoType)
  , Path
  , Pos
  , getPath
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
