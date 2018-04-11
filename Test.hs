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
    
  -- check "Sic basic math"
  --   [ ("iadd", prop_iadd (+))
  --   , ("imul", prop_imul (*))
  --   , ("rmul", prop_rmul (*))
  --   , ("rpow", prop_rpow (^) rpowMaxResult)
  --   ]

do_math x y name =
  case run (name <> "(int256,int256)") (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
    Right (AbiInt 256 z) ->
      Right z
    Left e ->
      Left e

do_iadd x y = do_math x y "iadd"
do_imul x y = do_math x y "imul"
do_rmul x y = fixed <$> do_math (unfixed x) (unfixed y) "rmul"
do_rpow x n = fixed <$> do_math (unfixed (ray x)) n "rpow"

debug_rpow x n =
  let
    c =
      Call root example "rpow(int256,int256)" (Just (AbiIntType 256))
        [AbiInt 256 (unfixed x), AbiInt 256 n]
  in
    runFromVM (execState (setupCall c) initialVm) "rpow"

prop_token = withTests testCount . property $ do
  ref <- liftIO (newIORef initialVm)
  acts <-
    forAll $ Gen.sequential (Range.linear 0 100) initialState
      [ cmdSpawn
      , cmdMintGood ref
      , cmdMintUnauthorized ref
      , cmdTransferGood ref
      , cmdBalanceOf ref
      ]
    
  executeSequential initialState acts
  debugIfFailed

someAccount :: Model v -> Gen Word160
someAccount = Gen.element . Set.toList . accounts

someGem :: Gen Gem
someGem = Gen.element allGems

data Spawn (v :: * -> *) =
  Spawn Word160
  deriving (Eq, Show)

data Mint (v :: * -> *) =
  Mint Gem Word160 Word160 Word256
  deriving (Eq, Show)

data Transfer (v :: * -> *) =
  Transfer Gem Word160 Word160 Word256
  deriving (Eq, Show)

data BalanceOf (v :: * -> *) =
  BalanceOf Word160 Gem Word160
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
        src <- Gen.filter (/= root) (someAccount s)
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
        wad <- someUpTo srcWad
        pure (Transfer gem src dst wad)

    run cmd@(Transfer gem src dst wad) = do
      debug ref cmd $ Call
        src (gemAddress gem)
        "transfer(address,uint256)"
        (Just AbiBoolType)
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
       , ensureSuccess (AbiBool True)
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
