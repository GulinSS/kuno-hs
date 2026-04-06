module Kuno.Strategy
  ( StrategyNode(..)
  , Strategy(..)
  , expandStrategyNode
  , nodeToDialogue
  , winningStrategyForProponent
  , winningStrategyForOpponent
  , strategyLeaves
  , branchClosed
  , fullyExpanded
  ) where

import Data.Maybe (isJust, fromMaybe)

import Kuno.Expression
import Kuno.Move
import Kuno.Dialogue

-- | A node in a strategy tree
data StrategyNode = StrategyNode
  { snMove     :: Move
  , snRuleset  :: Ruleset
  , snParent   :: Maybe StrategyNode
  , snChildren :: Maybe [StrategyNode]  -- Nothing = unexpanded
  }

snExpanded :: StrategyNode -> Bool
snExpanded = isJust . snChildren

snChildList :: StrategyNode -> [StrategyNode]
snChildList = fromMaybe [] . snChildren

-- | A strategy tree
data Strategy = Strategy
  { strategyRoot    :: StrategyNode
  , strategyRuleset :: Ruleset
  }

-- | Convert a strategy node back to a dialogue by walking up to the root
nodeToDialogue :: StrategyNode -> Ruleset -> Dialogue
nodeToDialogue node rs = go node
  where
    go n = case snParent n of
      Nothing -> emptyDialogue (extractFormula (snMove n)) rs
      Just p  -> addMove (go p) (snMove n)

    extractFormula m = case moveStatement m of
      FormulaS f -> f
      _ -> Atomic "unknown" []  -- shouldn't happen for root

-- | Expand a strategy node by computing all continuations
expandStrategyNode :: StrategyNode -> StrategyNode
expandStrategyNode node =
  let dialogue = nodeToDialogue node (snRuleset node)
      m = snMove node
      nextMoves = if isProponentMove m
                  then nextOpponentMoves dialogue
                  else nextProponentMoves dialogue
      children = map (\mv -> StrategyNode
                        { snMove = mv
                        , snRuleset = snRuleset node
                        , snParent = Just node
                        , snChildren = Nothing
                        }) nextMoves
  in node { snChildren = Just children }

-- | Depth of a strategy node
snDepth :: StrategyNode -> Int
snDepth node = case snParent node of
  Nothing -> 0
  Just p  -> 1 + snDepth p

-- | All leaves reachable from a node (expanding as needed)
strategyLeaves :: StrategyNode -> [StrategyNode]
strategyLeaves node =
  let node' = if snExpanded node then node else expandStrategyNode node
  in case snChildList node' of
       [] -> [node']
       cs -> concatMap strategyLeaves cs

-- | All nodes reachable from a strategy node
allNodes :: StrategyNode -> [StrategyNode]
allNodes node = node : concatMap allNodes (snChildList node)

fullyExpanded :: Strategy -> Bool
fullyExpanded s = all snExpanded (allNodes (strategyRoot s))

branchClosed :: StrategyNode -> Bool
branchClosed node
  | not (snExpanded node) = False
  | null (snChildList node) = True
  | otherwise = all branchClosed (snChildList node)

-- | Check if this is a winning strategy for Proponent.
-- Even-depth nodes (Proponent) must have all opponent moves as children.
-- Odd-depth nodes (Opponent) must have exactly one child.
-- All leaves must be wins for Proponent.
winningStrategyForProponent :: Strategy -> Bool
winningStrategyForProponent strat =
  winningFormP (strategyRoot strat)
  && fullyExpanded strat
  && all (\leaf -> proponentWins (nodeToDialogue leaf (strategyRuleset strat)))
         (strategyLeaves (strategyRoot strat))
  where
    winningFormP node =
      case snChildList node of
        [] -> True
        cs | even (snDepth node) -> all winningFormO cs
        [c] -> winningFormP c
        _ -> False
    winningFormO node =
      case snChildList node of
        [] -> True
        cs | odd (snDepth node) -> case cs of
              [c] -> winningFormP c
              _ -> False
        cs -> all winningFormO cs

-- | Check if this is a winning strategy for Opponent.
winningStrategyForOpponent :: Strategy -> Bool
winningStrategyForOpponent strat =
  winningFormO (strategyRoot strat)
  && fullyExpanded strat
  && all (\leaf -> opponentWins (nodeToDialogue leaf (strategyRuleset strat)))
         (strategyLeaves (strategyRoot strat))
  where
    winningFormO node =
      case snChildList node of
        [] -> True
        cs | even (snDepth node) -> case cs of
              [c] -> winningFormP c
              _ -> False
        cs -> all winningFormO cs
    winningFormP node =
      case snChildList node of
        [] -> True
        cs | odd (snDepth node) -> all winningFormO cs
        [c] -> winningFormP c
        _ -> False
