{-# Language KindSignatures #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

import TestBase
import TestLoad
import TestModel
import TestBasicMath
import TestDebug

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

main :: IO ()
main = do
  let
    check s ps = do
      good <- checkSequential $ Group s ps
      unless good exitFailure
      putStrLn ""

  check "Dependencies"
    [ ("DSToken", prop_token)
    ]
    
  check "Sic basic math"
    [ ("iadd", prop_iadd)
    , ("imul", prop_imul)
    , ("rmul", prop_rmul)
    , ("rpow", prop_rpow)
    ]

prop_token = withShrinks 100 . withTests 500 . property $ do
  ref <- liftIO (newIORef vm1)
  acts <-
    forAll $ Gen.sequential (Range.linear 0 25) initialState
      [ cmdSpawn
      , cmdMintGood ref
      , cmdMintUnauthorized ref
      , cmdTransferGood ref
      , cmdTransferOverflow ref
      , cmdBalanceOf ref
      ]
      
  executeSequential initialState acts
  debugIfFailed

someAccount :: Model v -> Gen Addr
someAccount = Gen.element . Set.toList . accounts

someGem :: Gen Gem
someGem = Gen.element allGems

data Spawn (v :: * -> *) =
  Spawn Addr
  deriving (Eq, Show)

data Mint (v :: * -> *) =
  Mint Gem Addr Addr Word256
  deriving (Eq, Show)

data Transfer (v :: * -> *) =
  Transfer Gem Addr Addr Word256
  deriving (Eq, Show)

data BalanceOf (v :: * -> *) =
  BalanceOf Addr Gem Addr
  deriving (Eq, Show)

instance HTraversable Spawn where
  htraverse f (Spawn x) = pure (Spawn x)

instance HTraversable Mint where
  htraverse f (Mint a b c d) = pure (Mint a b c d)

instance HTraversable Transfer where
  htraverse f (Transfer a b c d) = pure (Transfer a b c d)

instance HTraversable BalanceOf where
  htraverse f (BalanceOf a b c) = pure (BalanceOf a b c)

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
        gem <- someGem
        dst <- someAccount s
        let dstWad = balanceOf gem dst s
        wad <- someUpTo (min (maxBound - totalSupply s) (maxBound - dstWad))
        pure (Mint gem root dst wad)
      
    execute cmd@(Mint gem src dst wad) = do
      send ref $ Call
        src (gemAddress gem)
        "mint(address,uint256)"
        Nothing
        [AbiAddress (cast dst), AbiUInt 256 wad]

  in
    Command gen execute
      [ Require $ \s _  -> do True
      , Update $ \s (Mint gem src dst wad) _ ->
          s { balances =
                Map.adjust (+ wad) (gem, dst) (balances s) }
      , ensureVoidSuccess
      ]

cmdMintUnauthorized :: IORef VM -> Command Gen (PropertyT IO) Model
cmdMintUnauthorized ref =
  let
    gen s =
      if Set.size (accounts s) < 2
      then Nothing
      else Just $ do
        gem <- Gen.element [DAI, MKR]
        src <- Gen.element (Set.toList (Set.delete root (accounts s)))
        dst <- someAccount s
        wad <- someUpTo maxBound
        pure (Mint gem src dst wad)
      
    execute (Mint gem src dst wad) = do
      send ref $ Call
        src (gemAddress gem)
        "mint(address,uint256)"
        Nothing
        [AbiAddress (cast dst), AbiUInt 256 wad]

  in
    Command gen execute
      [ ensureRevert
      ]

cmdTransferGood ref =
  let
    gen s =
      Just $ do
        gem <- someGem
        src <- someAccount s
        dst <- someAccount s
        let srcWad = balances s ! (gem, src)
        let dstWad = balances s ! (gem, dst)
        wad <- someUpTo (min srcWad (maxWord - dstWad))
        pure (Transfer gem src dst wad)

    run cmd@(Transfer gem src dst wad) = do
      send ref $ Call
        src (gemAddress gem)
        "push(address,uint256)"
        Nothing
        [AbiAddress (cast dst), AbiUInt 256 wad]

  in Command gen run
      [ Require $ \s (Transfer gem src dst wad) ->
          balanceOf gem src s >= wad
      , Update $ \s (Transfer gem src dst wad) _ ->
             s { balances =
                   Map.adjust (subtract wad) (gem, src) .
                   Map.adjust (+ wad) (gem, dst) $
                     balances s
               }
       , ensureVoidSuccess
       ]

cmdTransferOverflow ref =
  let
    gen s =
      if Set.size (accounts s) < 2 then Nothing
      else Just $ do
        gem <- someGem
        src <- someAccount s
        dst <- Gen.filter (/= src) (someAccount s)
        let srcWad = balances s ! (gem, src)
        let dstWad = balances s ! (gem, dst)
        wad <- someGreaterThan (maxWord - dstWad)
        pure (Transfer gem src dst wad)

    run cmd@(Transfer gem src dst wad) = do
      send ref $
        Call src (gemAddress gem)
          "push(address,uint256)"
          Nothing
          [AbiAddress (cast dst), AbiUInt 256 wad]

  in Command gen run
      [ Require $ \s (Transfer gem src dst wad) ->
          balanceOf gem src s >= wad
            && addOverflow (balanceOf gem dst s) wad
      , ensureRevert
      ]

cmdBalanceOf ref =
  let
    gen s =
      Just (BalanceOf <$> someAccount s <*> someGem <*> someAccount s)
        
    run (BalanceOf src gem guy) =
      send ref $ Call src (gemAddress gem)
        "balanceOf(address)"
        (Just (AbiUIntType 256))
        [AbiAddress (cast guy)]
        
  in
    Command gen run
      [ Ensure $ \s _ (BalanceOf _ gem guy) (vm, out) -> do
          case out of
            Just (AbiUInt 256 x) ->
              x === balanceOf gem guy s
            _ ->
              failure
      ]
