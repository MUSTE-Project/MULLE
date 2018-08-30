{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language TemplateHaskell #-}
module Muste.Menu.New (NewFancyMenu, getNewFancyMenu) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Array as Array
import Data.Aeson

import qualified Muste.Grammar.Internal as Grammar
import Muste.Linearization.Internal
  (Linearization(..), Context, ctxtGrammar, ctxtPrecomputed)
import qualified Muste.Linearization.Internal as Linearization
import Muste.Tree.Internal (TTree(..), Path)
import qualified Muste.Tree.Internal as Tree
import Muste.Prune ()
import qualified Muste.Prune as Prune
import Data.Function ((&))
import GHC.Exts (fromList)

import qualified Muste.Sentence as Sentence
import qualified Muste.Sentence.Linearization as Sentence (Linearization)
import qualified Muste.Sentence.Token as Token

type Tokn = String
type Node = String
type Selection = [(Int, Int)]


-- * First, some basic functions and types:

parseSentence :: Context -> String -> [TTree]
parseSentence ctxt sent = Grammar.parseSentence (ctxtGrammar ctxt) (Linearization.ctxtLang ctxt) sent

linTree :: Context -> TTree -> ([Tokn], [Node])
linTree ctxt tree = (map Linearization.ltlin lintokens, map (lookupNode tree . Linearization.ltpath) lintokens)
    where Linearization lintokens = Linearization.linearizeTree ctxt tree

lookupNode :: TTree -> Path -> Node
lookupNode tree path = case Tree.selectNode tree path of
                         Just (TNode node _ _) -> node
                         _ → error "Incomplete Pattern-Match"

similarTrees :: Context -> TTree -> [TTree]
similarTrees ctxt tree = [ tree' | (_path, simtrees) <- Map.toList simmap, (_, tree') <- Set.toList simtrees ]
    where simmap = Prune.replaceTrees (ctxtGrammar ctxt) (ctxtPrecomputed ctxt) tree


-- * Exported stuff

newtype NewFancyMenu
  = NewFancyMenu (Map Selection (Set (Selection, Sentence.Linearization Token.Unannotated)))

deriving instance Show NewFancyMenu
deriving instance Semigroup NewFancyMenu
deriving instance Monoid NewFancyMenu
deriving instance ToJSON NewFancyMenu
deriving instance FromJSON NewFancyMenu

-- | FIXME Change my name when we have moved the deprecated 'getMenu'.
getNewFancyMenu
  ∷ Sentence.IsToken a
  ⇒ Context
  → Sentence.Linearization a
  → NewFancyMenu
getNewFancyMenu c l
  = Sentence.stringRep l
  & getMenuItems c

getMenuItems :: Context -> String -> NewFancyMenu
getMenuItems ctxt sentence
  = NewFancyMenu
  $ Map.fromListWith Set.union
  $ do
    oldtree <- parseSentence ctxt sentence
    let (_oldwords, oldnodes) = linTree ctxt oldtree
    newtree <- similarTrees ctxt oldtree
    let (newwords, newnodes) = linTree ctxt newtree
    let edits = alignSequences oldnodes newnodes
    let (oldselection, newselection) = splitAlignments edits
    return
      ( oldselection
      , Set.singleton
        ( newselection
        , ambigLin newwords
        )
      )

ambigLin ∷ [Tokn] → Sentence.Linearization Token.Unannotated
ambigLin = fromList . map Token.unannotated


-- * LCS

type Edit a = (([a], Int, Int), ([a], Int, Int))

splitAlignments :: [Edit a] -> (Selection, Selection)
splitAlignments [] = ([], [])
splitAlignments (((_,i,j), (_,k,l)) : edits) = ((i,j):oldselection, (k,l):newselection)
    where (oldselection, newselection) = splitAlignments edits

alignSequences :: Eq a => [a] -> [a] -> [Edit a]
alignSequences xs ys = mergeEdits $ snd $ a Array.! (0,0)
    where n = length xs
          m = length ys
          a = Array.array ((0,0),(n,m)) $ l1 ++ l2 ++ l3
          -- l1 = [((i,m), (0, [])) | i <- [0..n]]
          l1 = [((i,m), (fromInteger @Int 0, [])) | i <- [0..n]]
          l2 = [((n,j), (0, [])) | j <- [0..m]]
          l3 = [((i,j), f x y i j) | (x,i) <- zip xs [0..], (y,j) <- zip ys [0..]]
          f x y i j
              | x == y     = (eqs+1, (([x],i,i+1), ([x],j,j+1)) : eqedits)
              | ins == del = (ins,   (([x],i,i+1), ([y],j,j+1)) : eqedits)
              | ins > del  = (ins,   (([],i,i), ([y],j,j+1)) : inedits)
              | otherwise  = (del,   (([x],i,i+1), ([],j,j)) : dledits)
              where (eqs, eqedits) = a Array.! (i+1,j+1)
                    (ins, inedits) = a Array.! (i,j+1)
                    (del, dledits) = a Array.! (i+1,j)

mergeEdits :: Eq a => [Edit a] -> [Edit a]
mergeEdits [] = []
mergeEdits (edit@((xs,_,_), (xs',_,_)) : edits)
    | xs == xs' = mergeEdits edits
    | otherwise = merge edit edits
    where merge edit [] = [edit]
          merge edit@((xs,i,_j), (xs',i',_j')) (((ys,_k,l), (ys',_k',l')) : edits)
              | ys == ys' = edit : mergeEdits edits
              | otherwise = merge ((xs++ys,i,l), (xs'++ys',i',l')) edits
