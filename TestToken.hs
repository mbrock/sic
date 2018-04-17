{-# Language ConstraintKinds #-}
{-# Language KindSignatures #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language StandaloneDeriving #-}

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
  IORef VM -> Command Gen (PropertyT IO) Model

-- These commands have no effect on the real system;
-- they only affect the model in some preparatory way.
pseudoCommands :: [ModelCommand]
pseudoCommands =
  [ const gen_spawn
  ]

-- These commands should succeed and update the model.
goodCommands :: [ModelCommand]
goodCommands =
  [ good_mint
  , good_transfer
  , good_approve
  , good_form
  , good_file_spot
  , good_file_rate
  , good_file_line
  , good_frob
  ]

-- These commands exercise the system's error cases.
failCommands :: [ModelCommand]
failCommands =
  [ fail_mint_unauthorized
  , fail_transfer_tooMuch
  ]

-- These commands verify getters against the model's data.
checkCommands :: [ModelCommand]
checkCommands =
  [ check_balanceOf
  , check_getIlk
  ]

allCommands :: [ModelCommand]
allCommands =
  concat
    [ pseudoCommands
    , goodCommands
    , failCommands
    , checkCommands
    ]

----------------------------------------------------------------------------

prop_system :: PropertyT IO VM -> Property
prop_system generateInitialVm =
  withTests testCount . property $ do

    vmRef <- liftIO (newIORef undefined)
    acts <-
      forAll $
        Gen.sequential (Range.linear 1 100)
          initialState (map ($ vmRef) allCommands)

    -- It's important that we initialize the reference here, and not
    -- before selecting the acts, because of how shrinking works
    -- in the Property monad.
    generateInitialVm >>= liftIO . writeIORef vmRef
    executeSequential initialState acts

----------------------------------------------------------------------------

data Target = ToContract Word160 | ToToken Token
  deriving (Eq, Show)

data C (c :: (* -> *) -> *) v = C Word160 Target (c v)
  deriving (Eq, Show)

instance HTraversable c => HTraversable (C c) where
  htraverse f (C x y c) = C <$> pure x <*> pure y <*> htraverse f c

----------------------------------------------------------------------------

-- Action types that don't refer to ilk IDs need an explicit kind signature
-- because the type parameter is unused and so not inferrable.

data Spawn     (v :: * -> *) = Spawn Word160              deriving (Eq, Show)
data Mint      (v :: * -> *) = Mint Word160 Word256       deriving (Eq, Show)
data Transfer  (v :: * -> *) = Transfer Word160 Word256   deriving (Eq, Show)
data BalanceOf (v :: * -> *) = BalanceOf Word160          deriving (Eq, Show)
data Approve   (v :: * -> *) = Approve Word160            deriving (Eq, Show)
data Form      (v :: * -> *) = Form Token                 deriving (Eq, Show)

data GetIlk v = GetIlk (Var (Id Ilk) v)                   deriving (Eq, Show)
data File   v = File (Var (Id Ilk) v) ByteString Word256  deriving (Eq, Show)
data Frob   v = Frob (Var (Id Ilk) v) Word256 Word256     deriving (Eq, Show)

instance HTraversable Spawn where
  htraverse f (Spawn x) = pure (Spawn x)
instance HTraversable Mint where
  htraverse f (Mint a b) = pure (Mint a b)
instance HTraversable Transfer where
  htraverse f (Transfer a b) = pure (Transfer a b)
instance HTraversable BalanceOf where
  htraverse f (BalanceOf a) = pure (BalanceOf a)
instance HTraversable Approve where
  htraverse f (Approve a) = pure (Approve a)
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
        ToContract x -> x
        ToToken x -> tokenAddress x
  in
    Call sig src dst t xs

type AbiAction t =
  ( HTraversable t
  , Show (t Symbolic)
  , Show (t Concrete)
  , ToABI t
  )

mkSendCommand
  :: (AbiAction t, MonadIO m, Typeable output)
  => IORef VM
  -> ((VM, Maybe AbiValue) -> output)
  -> (state Symbolic -> Maybe (a (C t Symbolic)))
  -> [Callback (C t) output state]
  -> Command a m state
mkSendCommand ref g f =
  Command f $
    \c@(C _ _ x) ->
      fmap g (sendDebug ref x (toCall c))

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

instance ToABI Approve where
  toABI (Approve guy) =
    ( "approve(address)"
    , Just AbiBoolType
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
     pure $ do
       token <- someToken
       pure (C root (ToContract vatAddress) (Form token)))

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
  (\model -> do
     guard $ not (empty (ilks model))
     pure $ do
       i <- Gen.element (Map.keys (ilks model))
       pure (C root (ToContract vatAddress) (GetIlk i)))

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
       pure (C root (ToContract vatAddress) (File i (padRight 32 what) x)))

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

       pure (C root (ToToken token) (Mint dst wad)))

  [ ensureVoidSuccess
  , Update $ \s (C src (ToToken token) (Mint dst wad)) _ ->
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
       pure (C src (ToToken token) (Mint dst wad)))
  [ensureRevert]

good_transfer ref = mkSendCommand ref id
  (\s ->
     Just $ do
       token <- someToken
       src <- someAccount s
       dst <- someAccount s
       let srcWad = balances s ! (token, src)
       wad <- someUpTo srcWad
       pure (C src (ToToken token) (Transfer dst wad)))

  [ ensureSuccess (AbiBool True)
  , Require $ \s (C src (ToToken token) (Transfer dst wad)) ->
      balanceOf token src s >= wad
  , Update $ \s (C src (ToToken token) (Transfer dst wad)) _ ->
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
       pure (C src (ToToken token) (Transfer dst wad)))
  [ensureRevert]

check_balanceOf ref = mkSendCommand ref id
  (\s ->
     Just $ do
       src <- someAccount s
       guy <- someAccount s
       token <- someToken
       pure (C src (ToToken token) (BalanceOf guy)))
  [ Ensure $ \s _ (C _ (ToToken token) (BalanceOf guy)) (vm, out) -> do
      case out of
        Just (AbiUInt 256 x) ->
          x === balanceOf token guy s
        _ ->
          failure
  ]

good_approve ref = mkSendCommand ref id
  (\model -> do
      pure $ do
        src <- someAccount model
        guy <- pure vatAddress
        token <- someToken
        pure (C src (ToToken token) (Approve guy)))
  [ ensureSuccess (AbiBool True)
  , Require $
      \model (C src (ToToken token) (Approve guy)) ->
        and
          [ Set.member src (accounts model)
          ]
  , Update $
      \model (C src (ToToken token) (Approve guy)) _ ->
        model
          { approvals =
              Set.insert (token, src, guy) (approvals model)
          }
  ]

good_frob ref = mkSendCommand ref id
  (\model -> do
      guard . not . empty $ ilks model
      pure $ do
        src <- someAccount model
        (ilkId, ilk) <- someIlk model
        x <- someUpTo (balanceOf (gem ilk) src model)
        pure (C src (ToContract vatAddress) (Frob ilkId x 0)))

  [ ensureVoidSuccess

  , Require $
      \model (C src _ (Frob ilkId x _)) ->
        case
          Map.lookup ilkId (ilks model)
        of
          Just ilk ->
            and
              [ balanceOf (gem ilk) src model >= x
              , Set.member (gem ilk, src, vatAddress) (approvals model)
              ]
          _ ->
            False

  , Require $
      \model (C src _ (Frob ilkId x _)) ->
        let
          Just ilk = Map.lookup ilkId (ilks model)
        in
          spot ilk * cast x < cast maxInt

  , Update $
      \model
       (C src _ (Frob ilkId x _)) _ ->
        let
          Just ilk = Map.lookup ilkId (ilks model)
        in
          model
            { balances =
                Map.adjust (subtract x) (gem ilk, src)
                  (balances model)
            }
  ]
