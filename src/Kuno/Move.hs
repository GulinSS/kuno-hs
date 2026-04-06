module Kuno.Move
  ( Player(..)
  , Move(..)
  , otherPlayer
  , isProponent
  , isOpponent
  , isAttack
  , isDefense
  , isProponentMove
  , isOpponentMove
  , moveTermsIn
  , moveFreeVariables
  ) where

import Kuno.Expression

data Player = Proponent | Opponent
  deriving (Show, Eq, Ord)

data Move = Move
  { moveStatement :: Statement
  , moveReference :: Int
  , moveIsAttack  :: Bool
  , movePlayer    :: Player
  } deriving (Show, Eq, Ord)

otherPlayer :: Player -> Player
otherPlayer Proponent = Opponent
otherPlayer Opponent = Proponent

isProponent :: Player -> Bool
isProponent Proponent = True
isProponent _ = False

isOpponent :: Player -> Bool
isOpponent Opponent = True
isOpponent _ = False

isAttack :: Move -> Bool
isAttack = moveIsAttack

isDefense :: Move -> Bool
isDefense = not . moveIsAttack

isProponentMove :: Move -> Bool
isProponentMove m = movePlayer m == Proponent

isOpponentMove :: Move -> Bool
isOpponentMove m = movePlayer m == Opponent

moveTermsIn :: Move -> [Term]
moveTermsIn m = case moveStatement m of
  FormulaS f -> termsIn f
  AttackS (WhichInstance (Just t)) -> [t]
  _ -> []

moveFreeVariables :: Move -> [Term]
moveFreeVariables m = case moveStatement m of
  FormulaS f -> freeVariables f
  _ -> []
