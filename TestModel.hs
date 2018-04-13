{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}

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
  { spot :: !Ray
  , rate :: !Ray
  , line :: !Integer
  , arts :: !Integer
  , gem  :: !Token
  } deriving (Eq, Show)

emptyIlk :: Token -> Ilk
emptyIlk t = Ilk
  { spot = 0
  , rate = 0
  , line = 0
  , arts = 0
  , gem = t
  }

data Urn = Urn
  { ink :: !Integer
  , art :: !Integer
  } deriving (Eq, Show)

newtype Id a = Id ByteString
  deriving (Ord, Eq, Show)

data Model v =
  Model
    { accounts :: !(Set Word160)
    , balances :: !(Map (Token, Word160) Word256)
    , ilks     :: !(Map (Var (Id Ilk) v) Ilk)
    }

deriving instance Show1 v => Show (Model v)

initialState :: Model v
initialState = Model
  { accounts = Set.fromList [root]
  , balances = zeroBalancesFor root
  , ilks     = Map.empty
  }

someAccount :: Model v -> Gen Word160
someAccount = Gen.element . Set.toList . accounts

someToken :: Gen Token
someToken = Gen.element allTokens

zeroBalancesFor :: Word160 -> Map (Token, Word160) Word256
zeroBalancesFor x = Map.fromList [((g, x), 0) | g <- allTokens]

balanceOf :: Token -> Word160 -> Model v -> Word256
balanceOf g x s =
  fromMaybe 0 (Map.lookup (g, x) (balances s))

totalSupply :: Token -> Model v -> Word256
totalSupply token s =
  sum [x | ((t, _), x) <- Map.assocs (balances s), t == token]
