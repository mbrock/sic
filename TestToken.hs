{-# Language KindSignatures #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

module TestToken where

import TestBase
import TestLoad
import TestDebug
import TestModel

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

prop_token = withTests testCount . property $ do
  ref <- liftIO (newIORef initialVm)
  acts <-
    forAll $ Gen.sequential (Range.linear 0 100) initialState
      [ cmdSpawn
      , cmdMintGood ref
      , cmdMintUnauthorized ref
      , cmdTransferGood ref
      , cmdTransferTooMuch ref
      , cmdBalanceOf ref
      ]

  executeSequential initialState acts
  debugIfFailed

someAccount :: Model v -> Gen Word160
someAccount = Gen.element . Set.toList . accounts

someToken :: Gen Token
someToken = Gen.element allTokens

data Spawn (v :: * -> *) =
  Spawn Word160
  deriving (Eq, Show)

data Mint (v :: * -> *) =
  Mint Token Word160 Word160 Word256
  deriving (Eq, Show)

data Transfer (v :: * -> *) =
  Transfer Token Word160 Word160 Word256
  deriving (Eq, Show)

data BalanceOf (v :: * -> *) =
  BalanceOf Word160 Token Word160
  deriving (Eq, Show)

instance HTraversable Spawn where
  htraverse f (Spawn x) = pure (Spawn x)

instance HTraversable Mint where
  htraverse f (Mint a b c d) = pure (Mint a b c d)

instance HTraversable Transfer where
  htraverse f (Transfer a b c d) = pure (Transfer a b c d)

instance HTraversable BalanceOf where
  htraverse f (BalanceOf a b c) = pure (BalanceOf a b c)

class AsCall a where
  asCall :: a -> Call

instance AsCall (Transfer v) where
  asCall (Transfer token src dst wad) =
    Call "transfer(address,uint256)"
      src (tokenAddress token)
      (Just AbiBoolType)
      [AbiAddress (cast dst), AbiUInt 256 wad]

instance AsCall (Mint v) where
  asCall (Mint token src dst wad) =
    Call "mint(address,uint256)"
      src (tokenAddress token)
      Nothing
      [AbiAddress (cast dst), AbiUInt 256 wad]

instance AsCall (BalanceOf v) where
  asCall (BalanceOf src token guy) =
    Call "balanceOf(address)"
      src (tokenAddress token)
      (Just (AbiUIntType 256))
      [AbiAddress (cast guy)]

cmdSpawn :: Monad m => Command Gen m Model
cmdSpawn =
  Command
    (const (pure (Spawn . cast <$> anyInt)))
    (const (pure ()))
    [ Require $ \s (Spawn x) ->
        Set.notMember x (accounts s)
    , Update $ \s (Spawn x) _ ->
        s { accounts = Set.insert x (accounts s)
          , balances = Map.union (balances s) (zeroBalancesFor x)
          }
    ]

cmdMintGood :: IORef VM -> Command Gen (PropertyT IO) Model
cmdMintGood ref =
  let
    gen s =
      Just $ do
        token <- someToken
        dst <- someAccount s
        let dstWad = balanceOf token dst s
        wad <- someUpTo (min (maxBound - totalSupply s) (maxBound - dstWad))
        pure (Mint token root dst wad)

  in
    Command gen (send ref . asCall)
      [ Require $ \s _  -> do True
      , Update $ \s (Mint token src dst wad) _ ->
          s { balances =
                Map.adjust (+ wad) (token, dst) (balances s) }
      , ensureVoidSuccess
      ]

cmdMintUnauthorized :: IORef VM -> Command Gen (PropertyT IO) Model
cmdMintUnauthorized ref =
  let
    gen s =
      if Set.size (accounts s) < 2
      then Nothing
      else Just $ do
        token <- Gen.element [DAI, MKR]
        src <- Gen.filter (/= root) (someAccount s)
        dst <- someAccount s
        wad <- someUpTo maxBound
        pure (Mint token src dst wad)

  in
    Command gen (send ref . asCall)
      [ ensureRevert
      ]

cmdTransferGood :: IORef VM -> Command Gen (PropertyT IO) Model
cmdTransferGood ref =
  let
    gen s =
      Just $ do
        token <- someToken
        src <- someAccount s
        dst <- someAccount s
        let srcWad = balances s ! (token, src)
        wad <- someUpTo srcWad
        pure (Transfer token src dst wad)

  in Command gen (send ref . asCall)
      [ Require $ \s (Transfer token src dst wad) ->
          balanceOf token src s >= wad
      , Update $ \s (Transfer token src dst wad) _ ->
          s { balances =
                Map.adjust (subtract wad) (token, src) .
                Map.adjust (+ wad) (token, dst) $
                  balances s
            }
       , ensureSuccess (AbiBool True)
       ]

cmdTransferTooMuch ref =
  let
    gen s =
      Just $ do
        token <- someToken
        src <- someAccount s
        dst <- someAccount s
        let srcWad = balances s ! (token, src)
        wad <- Gen.integral (someAbove srcWad)
        pure (Transfer token src dst wad)

  in Command gen (send ref . asCall) [ ensureRevert ]

cmdBalanceOf :: IORef VM -> Command Gen (PropertyT IO) Model
cmdBalanceOf ref =
  let
    gen s =
      Just (BalanceOf <$> someAccount s <*> someToken <*> someAccount s)

  in
    Command gen (send ref . asCall)
      [ Ensure $ \s _ (BalanceOf _ token guy) (vm, out) -> do
          case out of
            Just (AbiUInt 256 x) ->
              x === balanceOf token guy s
            _ ->
              failure
      ]
