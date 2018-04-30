{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StrictData #-}

module TestModel where

import TestBase

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Hedgehog.Gen as Gen

data Token = DAI | MKR | ETH | DGX | OMG
  deriving (Eq, Ord, Show, Enum)

allTokens :: [Token]
allTokens = enumFrom DAI

allGems :: [Token]
allGems = enumFrom ETH

data Ilk = Ilk
  { φ :: Ray
  , ψ :: Ray
  , ω :: Integer
  , σ :: Integer
  } deriving (Eq, Show)

emptyIlk :: Token -> Ilk
emptyIlk t = Ilk 0 1 0 0

data Urn = Urn
  { ink :: Integer
  , art :: Integer
  } deriving (Eq, Show)

newtype Id a = Id ByteString
  deriving (Ord, Eq, Show)

data Model (v :: * -> *) =
  Model
    { accounts  :: Set Word160
    , balances  :: Map (Token, Word160) Word256
    , approvals :: Set (Token, Word160, Word160)
    , ilks      :: Map (Id Ilk) Ilk
    , urns      :: Map (Id Ilk, Word160) Urn
    }

deriving instance Show1 v => Show (Model v)

initialState :: Model v
initialState = Model
  { accounts = Set.fromList [root]
  , balances = zeroBalancesFor root
  , approvals = Set.empty
  , ilks = Map.empty
  , urns = Map.empty
  }

someAccount :: Model v -> Gen Word160
someAccount = Gen.element . Set.toList . accounts

someToken :: Gen Token
someToken = Gen.element allTokens

someIlk :: Model v -> Gen (Id Ilk, Ilk)
someIlk = Gen.element . Map.toList . ilks

zeroBalancesFor :: Word160 -> Map (Token, Word160) Word256
zeroBalancesFor x = Map.fromList [((g, x), 0) | g <- allTokens]

balanceOf :: Token -> Word160 -> Model v -> Word256
balanceOf g x s =
  fromMaybe 0 (Map.lookup (g, x) (balances s))

totalSupply :: Token -> Model v -> Word256
totalSupply token s =
  sum [x | ((t, _), x) <- Map.assocs (balances s), t == token]
