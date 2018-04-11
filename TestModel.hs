{-# LANGUAGE KindSignatures #-}

module TestModel where

import TestBase

import qualified Data.Set as Set
import qualified Data.Map as Map

data Token = DAI | MKR
  deriving (Eq, Ord, Show, Enum)

allTokens :: [Token]
allTokens = enumFrom DAI

data Model (v :: * -> *) = Model
  { accounts :: Set Word160
  , balances :: Map (Token, Word160) Word256
  } deriving (Eq, Show)

zeroBalancesFor :: Word160 -> Map (Token, Word160) Word256
zeroBalancesFor x = Map.fromList [((g, x), 0) | g <- allTokens]

totalSupply :: Model v -> Word256
totalSupply = sum . Map.elems . balances

balanceOf :: Token -> Word160 -> Model v -> Word256
balanceOf g x s =
  case Map.lookup (g, x) (balances s) of
    Nothing -> 0
    Just n -> n

initialState :: Model v
initialState = Model
  { accounts = Set.fromList [root]
  , balances = zeroBalancesFor root
  }

supply :: Token -> Model v -> Word256
supply token s =
  sum [x | ((t, _), x) <- Map.assocs (balances s), t == token]
