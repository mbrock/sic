{-# Language StandaloneDeriving #-}
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
import qualified Data.Vector as Vector

allCommands ref =
  [ gen_spawn
  , good_mint ref
  , fail_mint_unauthorized ref
  , good_transfer ref
  , fail_transfer_tooMuch ref
  , check_balanceOf ref
  , good_form ref
  , good_getIlk ref
  , good_file_spot ref
  , good_file_rate ref
  , good_file_line ref
  ]

prop_allCommands :: PropertyT IO VM -> Property
prop_allCommands vm0 = withTests testCount . property $ do
  ref <- liftIO (newIORef undefined)
  acts <-
    forAll $
      Gen.sequential (Range.linear 1 100)
        initialState (allCommands ref)

  vm <- vm0

  -- It's important that we initialize the reference here, and not
  -- before selecting the acts, because of how shrinking works
  -- in the Property monad...
  liftIO (writeIORef ref vm)

  executeSequential initialState acts
  debugIfFailed

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

data Form (v :: * -> *) =
  Form Word160 Word160 Token
  deriving (Eq, Show)

data GetIlk (v :: * -> *) =
  GetIlk Word160 Word160 (Var (Id Ilk) v)
  deriving (Eq, Show)

data File (v :: * -> *) =
  File Word160 Word160 (Var (Id Ilk) v) ByteString Word256
  deriving (Eq, Show)

instance HTraversable Spawn where
  htraverse f (Spawn x) =
    pure (Spawn x)

instance HTraversable Mint where
  htraverse f (Mint a b c d) =
    pure (Mint a b c d)

instance HTraversable Transfer where
  htraverse f (Transfer a b c d) =
    pure (Transfer a b c d)

instance HTraversable BalanceOf where
  htraverse f (BalanceOf a b c) =
    pure (BalanceOf a b c)

instance HTraversable Form where
  htraverse f (Form a b c) =
    pure (Form a b c)

instance HTraversable GetIlk where
  htraverse f (GetIlk a b c) =
    GetIlk a b <$> htraverse f c

instance HTraversable File where
  htraverse f (File a b c d e) =
    File a b <$> htraverse f c <*> pure d <*> pure e

class AsCall a where
  asCall :: a Concrete -> Call

instance AsCall Transfer where
  asCall (Transfer token src dst wad) =
    Call "transfer(address,uint256)"
      src (tokenAddress token)
      (Just AbiBoolType)
      [AbiAddress (cast dst), AbiUInt 256 wad]

instance AsCall Mint where
  asCall (Mint token src dst wad) =
    Call "mint(address,uint256)"
      src (tokenAddress token)
      Nothing
      [AbiAddress (cast dst), AbiUInt 256 wad]

instance AsCall BalanceOf where
  asCall (BalanceOf src token guy) =
    Call "balanceOf(address)"
      src (tokenAddress token)
      (Just (AbiUIntType 256))
      [AbiAddress (cast guy)]

instance AsCall Form where
  asCall (Form src dst token) =
    Call "form(address)"
      src dst
      (Just (AbiBytesType 32))
      [AbiAddress (cast (tokenAddress token))]

instance AsCall GetIlk where
  asCall (GetIlk src dst (Var (Concrete (Id i)))) =
    Call "ilks(bytes32)"
      src dst
      (Just (AbiArrayType 6 (AbiUIntType 256)))
      [AbiBytes 32 i]

instance AsCall File where
  asCall (File src dst (Var (Concrete (Id i))) what risk) =
    Call "file(bytes32,bytes32,uint256)"
      src dst
      Nothing
      [AbiBytes 32 i, AbiBytes 32 what, AbiUInt 256 risk]

mkSendCommand ref g f = Command f (fmap g . send ref . asCall)

-- This command only affects the model.
--
-- It generates a random new account with zero balances.
-- In the EVM, all such accounts exist implicitly.
--
-- If we want to run these tests against a real node,
-- we might have to generate private/public keys here...
--
gen_spawn =
  Command
    (const (pure (Spawn . cast <$> someUpTo 100000)))
    (const (pure ()))
    [ Require $ \s (Spawn x) ->
        Set.notMember x (accounts s)
    , Update $ \s (Spawn x) _ ->
        s { accounts = Set.insert x (accounts s)
          , balances = Map.union (balances s) (zeroBalancesFor x)
          }
    ]

good_form ref = mkSendCommand ref
  (\(_, out) ->
     case out of
       Just (AbiBytes 32 x) -> Id x
       _ -> error "bad result of form(address)")

  (\s ->
     Just $ do
       token <- someToken
       pure (Form root vatAddress token))

  [ Update $ \s (Form _ _ gem) o ->
      s { ilks = Map.insert o (emptyIlk gem) (ilks s) }
  ]

tokenFromAddress :: Word160 -> Token
tokenFromAddress x =
  case find ((== x) . tokenAddress) allTokens of
    Just t -> t
    _ -> error "invalid token address"

ilkFromStruct :: Foldable v => v AbiValue -> Ilk
ilkFromStruct v =
  case toList v of
    [AbiUInt 256 a, AbiUInt 256 b, AbiUInt 256 c,
     AbiUInt 256 d, AbiUInt 256 e, AbiUInt 256 _] ->
      Ilk
        { spot = fixed a
        , rate = fixed b
        , line = cast c
        , arts = cast d
        , gem = tokenFromAddress (cast e)
        }
    _ ->
      error "invalid ilk struct"

-- This command runs the getter for an existing ilk ID
-- and verifies that the struct's data matches the model.
good_getIlk ref = mkSendCommand ref id
  (\model ->
     if Map.null (ilks model)
     then Nothing
     else Just $ do
       i <- Gen.element (Map.keys (ilks model))
       pure (GetIlk root vatAddress i))

  [ Require $ \model (GetIlk _ _ i) ->
      Map.member i (ilks model)

  , Ensure $ \model _ (GetIlk _ _ i) (vm, out) -> do
      case out of
        Just (AbiArray _ _ v) -> do
          Just (ilkFromStruct v) === Map.lookup i (ilks model)
        _ ->
          failure
  ]

-- Parameterized command for randomly altering an ilk parameter.
good_file what gen f ref = mkSendCommand ref id
  (\model ->
     if Map.null (ilks model)
     then Nothing
     else Just $ do
       i <- Gen.element (Map.keys (ilks model))
       x <- gen
       pure (File root vatAddress i (padRight 32 what) x))

  [ Require $ \model (File _ _ i _ _) ->
      Map.member i (ilks model)

  , ensureVoidSuccess

  , Update $ \model (File _ _ i _ x) _ ->
      model
        { ilks = Map.adjust (f x) i (ilks model) }
  ]

good_file_spot =
  good_file "spot"
    (unfixed <$> anyRay)
    (\x ilk -> ilk { spot = fixed x })

good_file_rate =
  good_file "rate"
    (unfixed <$> anyRay)
    (\x ilk -> ilk { rate = fixed x })

good_file_line =
  good_file "line"
    anyInt
    (\x ilk -> ilk { line = cast x })

good_mint ref = mkSendCommand ref id
  (\s ->
     Just $ do
       token <- someToken
       dst <- someAccount s
       let dstWad = balanceOf token dst s

       -- We can mint only up to maxing out the total supply
       -- or maxing out the destination's balance.
       wad <-
         someUpTo
           (min (maxBound - totalSupply token s)
                (maxBound - dstWad))

       pure (Mint token root dst wad))

  [ ensureVoidSuccess
  , Update $ \s (Mint token src dst wad) _ ->
      s { balances =
            Map.adjust (+ wad) (token, dst) (balances s) }
  ]

fail_mint_unauthorized ref = mkSendCommand ref id
  (\s ->
     if Set.size (accounts s) < 2
     then Nothing
     else Just $ do
       token <- Gen.element [DAI, MKR]
       src <- Gen.filter (/= root) (someAccount s)
       dst <- someAccount s
       wad <- someUpTo maxBound
       pure (Mint token src dst wad))
  [ensureRevert]

good_transfer ref = mkSendCommand ref id
  (\s ->
     Just $ do
       token <- someToken
       src <- someAccount s
       dst <- someAccount s
       let srcWad = balances s ! (token, src)
       wad <- someUpTo srcWad
       pure (Transfer token src dst wad))

  [ ensureSuccess (AbiBool True)
  , Require $ \s (Transfer token src dst wad) ->
      balanceOf token src s >= wad
  , Update $ \s (Transfer token src dst wad) _ ->
      s { balances =
            Map.adjust (subtract wad) (token, src) .
            Map.adjust (+ wad) (token, dst) $
              balances s
        }
  ]

fail_transfer_tooMuch ref = mkSendCommand ref id
  (\s ->
     Just $ do
       token <- someToken
       src <- someAccount s
       dst <- someAccount s
       let srcWad = balances s ! (token, src)
       wad <- Gen.integral (someAbove srcWad)
       pure (Transfer token src dst wad))
  [ensureRevert]

check_balanceOf ref = mkSendCommand ref id
  (\s ->
     Just (BalanceOf <$> someAccount s <*> someToken <*> someAccount s))
  [ Ensure $ \s _ (BalanceOf _ token guy) (vm, out) -> do
      case out of
        Just (AbiUInt 256 x) ->
          x === balanceOf token guy s
        _ ->
          failure
  ]
