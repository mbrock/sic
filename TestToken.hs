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

----------------------------------------------------------------------------

type ModelCommand =
  Command Gen (PropertyT IO) Model

goodCommands :: IORef VM -> [ModelCommand]
goodCommands ref =
  [ good_mint ref
  , good_transfer ref
  , good_form ref
  , good_file_spot ref
  , good_file_rate ref
  , good_file_line ref
  , good_frob ref
  ]

failCommands :: IORef VM -> [ModelCommand]
failCommands ref =
  [ fail_mint_unauthorized ref
  , fail_transfer_tooMuch ref
  ]

checkCommands :: IORef VM -> [ModelCommand]
checkCommands ref =
  [ check_balanceOf ref
  , check_getIlk ref
  ]

allCommands :: IORef VM -> [ModelCommand]
allCommands ref =
  gen_spawn : concat
    [goodCommands ref, failCommands ref, checkCommands ref]

----------------------------------------------------------------------------

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

----------------------------------------------------------------------------

data Target = Box Word160 | Token Token deriving (Eq, Show)
data C (c :: (* -> *) -> *) (v :: * -> *)
  = C Word160 Target (c v) deriving (Eq, Show)

instance HTraversable c => HTraversable (C c) where
  htraverse f (C x y c) = C <$> pure x <*> pure y <*> htraverse f c

----------------------------------------------------------------------------

data Spawn (v :: * -> *) = Spawn Word160               deriving (Eq, Show)
data Mint (v :: * -> *) = Mint Word160 Word256         deriving (Eq, Show)
data Transfer (v :: * -> *) = Transfer Word160 Word256 deriving (Eq, Show)
data BalanceOf (v :: * -> *) = BalanceOf Word160       deriving (Eq, Show)
data Form (v :: * -> *) = Form Token                   deriving (Eq, Show)
data GetIlk v = GetIlk (Var (Id Ilk) v)                deriving (Eq, Show)
data File v = File (Var (Id Ilk) v) ByteString Word256 deriving (Eq, Show)
data Frob v = Frob (Var (Id Ilk) v) Word256 Word256    deriving (Eq, Show)

instance HTraversable Spawn where
  htraverse f (Spawn x) = pure (Spawn x)
instance HTraversable Mint where
  htraverse f (Mint a b) = pure (Mint a b)
instance HTraversable Transfer where
  htraverse f (Transfer a b) = pure (Transfer a b)
instance HTraversable BalanceOf where
  htraverse f (BalanceOf a) = pure (BalanceOf a)
instance HTraversable Form where
  htraverse f (Form a) = pure (Form a)
instance HTraversable GetIlk where
  htraverse f (GetIlk a) = GetIlk <$> htraverse f a
instance HTraversable File where
  htraverse f (File a b c) = File <$> htraverse f a <*> pure b <*> pure c
instance HTraversable Frob where
  htraverse f (Frob a b c) = Frob <$> htraverse f a <*> pure b <*> pure c

----------------------------------------------------------------------------

class ToABI a where
  toABI :: a Concrete -> (Text, Maybe AbiType, [AbiValue])

toCall (C src target c) =
  let
    (sig, t, xs) = toABI c
    dst =
      case target of
        Box x -> x
        Token x -> tokenAddress x
  in
    Call sig src dst t xs

mkSendCommand ref g f =
  Command f (\c@(C _ _ x) -> fmap g (sendDebug ref x (toCall c)))

----------------------------------------------------------------------------

instance ToABI Transfer where
  toABI (Transfer dst wad) =
    ( "transfer(address,uint256)"
    , Just AbiBoolType
    , [AbiAddress (cast dst), AbiUInt 256 wad]
    )

instance ToABI Mint where
  toABI (Mint guy wad) =
    ( "mint(address,uint256)"
    , Nothing
    , [AbiAddress (cast guy), AbiUInt 256 wad]
    )

instance ToABI BalanceOf where
  toABI (BalanceOf guy) =
    ( "balanceOf(address)"
    , Just (AbiUIntType 256)
    , [AbiAddress (cast guy)]
    )

instance ToABI Form where
  toABI (Form token) =
    ( "form(address)"
    , Just (AbiUIntType 256)
    , [AbiAddress (cast (tokenAddress token))]
    )

instance ToABI GetIlk where
  toABI (GetIlk (Var (Concrete (Id i)))) =
    ( "ilks(bytes32)"
    , Just (AbiArrayType 6 (AbiUIntType 256))
    , [AbiUInt 256 (cast i)]
    )

instance ToABI File where
  toABI (File (Var (Concrete (Id i))) what risk) =
    ( "file(bytes32,bytes32,uint256)"
    , Nothing
    , [AbiUInt 256 (cast i), AbiBytes 32 what, AbiUInt 256 risk]
    )

instance ToABI Frob where
  toABI (Frob (Var (Concrete (Id i))) ink art) =
    ( "frob(bytes32,uint256,uint256)"
    , Nothing
    , [AbiUInt 256 (cast i), AbiUInt 256 ink, AbiUInt 256 art]
    )

----------------------------------------------------------------------------


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
       Just (AbiUInt 256 x) -> Id (cast x)
       _ -> error "bad result of form(address)")

  (\s ->
     Just $ do
       token <- someToken
       pure (C root (Box vatAddress) (Form token)))

  [ Update $ \s (C _ _ (Form gem)) o ->
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
check_getIlk ref = mkSendCommand ref id
  (\model ->
     if Map.null (ilks model)
     then Nothing
     else Just $ do
       i <- Gen.element (Map.keys (ilks model))
       pure (C root (Box vatAddress) (GetIlk i)))

  [ Require $ \model (C _ _ (GetIlk i)) ->
      Map.member i (ilks model)

  , Ensure $ \model _ (C _ _ (GetIlk i)) (vm, out) -> do
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
       pure (C root (Box vatAddress) (File i (padRight 32 what) x)))

  [ Require $ \model (C _ _ (File i _ _)) ->
      Map.member i (ilks model)

  , ensureVoidSuccess

  , Update $ \model (C _ _ (File i _ x)) _ ->
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

       pure (C root (Token token) (Mint dst wad)))

  [ ensureVoidSuccess
  , Update $ \s (C src (Token token) (Mint dst wad)) _ ->
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
       pure (C src (Token token) (Mint dst wad)))
  [ensureRevert]

good_transfer ref = mkSendCommand ref id
  (\s ->
     Just $ do
       token <- someToken
       src <- someAccount s
       dst <- someAccount s
       let srcWad = balances s ! (token, src)
       wad <- someUpTo srcWad
       pure (C src (Token token) (Transfer dst wad)))

  [ ensureSuccess (AbiBool True)
  , Require $ \s (C src (Token token) (Transfer dst wad)) ->
      balanceOf token src s >= wad
  , Update $ \s (C src (Token token) (Transfer dst wad)) _ ->
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
       pure (C src (Token token) (Transfer dst wad)))
  [ensureRevert]

check_balanceOf ref = mkSendCommand ref id
  (\s ->
     Just $ do
       src <- someAccount s
       guy <- someAccount s
       token <- someToken
       pure (C src (Token token) (BalanceOf guy)))
  [ Ensure $ \s _ (C _ (Token token) (BalanceOf guy)) (vm, out) -> do
      case out of
        Just (AbiUInt 256 x) ->
          x === balanceOf token guy s
        _ ->
          failure
  ]

good_frob ref = mkSendCommand ref id
  (\model -> do
      guard . not . empty $ ilks model
      Just $ do
        src <- someAccount model
        ilk <- someIlk model
        x <- anyInt

        pure (C src (Box vatAddress) (Frob ilk x 0)))
  [ensureVoidSuccess]
