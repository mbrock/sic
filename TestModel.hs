{-# LANGUAGE KindSignatures #-}

module TestModel where

import TestBase

import qualified Data.Set as Set
import qualified Data.Map as Map

data Gem = DAI | MKR
  deriving (Eq, Ord, Show, Enum)

allGems :: [Gem]
allGems = enumFrom DAI

data Model (v :: * -> *) = Model
  { accounts :: Set Word160
  , balances :: Map (Gem, Word160) Word256
  } deriving (Eq, Show)

zeroBalancesFor :: Word160 -> Map (Gem, Word160) Word256
zeroBalancesFor x = Map.fromList [((g, x), 0) | g <- allGems]

totalSupply :: Model v -> Word256
totalSupply = sum . Map.elems . balances

balanceOf :: Gem -> Word160 -> Model v -> Word256
balanceOf g x s =
  case Map.lookup (g, x) (balances s) of
    Nothing -> 0
    Just n -> n

initialState :: Model v
initialState = Model
  { accounts = Set.fromList [root]
  , balances = zeroBalancesFor root
  }

supply :: Gem -> Model v -> Word256
supply gem s =
  sum [x | ((g, _), x) <- Map.assocs (balances s), g == gem]
