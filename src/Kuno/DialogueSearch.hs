-- | Top-level proof search interface.
--
-- This module provides a generic 'validWith' function parameterized by a
-- 'Logic', and a convenience wrapper 'intuitionisticallyValid' for the
-- built-in intuitionistic logic.
module Kuno.DialogueSearch
  ( SearchResult(..)
  , Logic(..)
  , proponentHasWinningStrategy
  , validWith
  , intuitionisticallyValid
  , tptpToDialogue
  ) where

import Kuno.Expression
import Kuno.Logic
import Kuno.Logic.Intuitionistic (intuitionisticLogic)
import Kuno.TPTP

-- | Generic proof search parameterized by a logic.
validWith :: Logic -> Either Formula TPTPDb -> Int -> SearchResult
validWith logic (Left formula) depth = logicSearchFormula logic formula depth
validWith logic (Right db)     depth = logicSearchDb logic db depth

-- | Check intuitionistic validity (convenience wrapper).
intuitionisticallyValid :: Either Formula TPTPDb -> Int -> SearchResult
intuitionisticallyValid = validWith intuitionisticLogic
