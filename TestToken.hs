{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

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
-- We specify our system as Hedgehog-based stateful testing commands.
----------------------------------------------------------------------------

type VmCommand =
  IORef VM -> Command Gen (PropertyT IO) Model

-- These commands have no effect on the real system;
-- they only affect the model in some preparatory way.
pseudoCommands :: [VmCommand]
pseudoCommands =
  [ const gen_spawn
  ]

-- These commands should succeed and update the model.
goodCommands :: [VmCommand]
goodCommands =
  [ act good_mint
  , act good_transfer
  , act good_approve
  , act good_form
  , act good_file_spot
  , act good_file_rate
  , act good_file_line
  -- , act good_frob
  ]

-- These commands exercise the system's error cases.
failCommands :: [VmCommand]
failCommands =
  [ act fail_mint_unauthorized
  , act fail_transfer_tooMuch
  ]

-- These commands verify getters against the model's data.
checkCommands :: [VmCommand]
checkCommands =
  [ act check_balanceOf
  , act check_getIlk
  ]

-- This is all commands; other subsets might be interesting later.
allCommands :: [VmCommand]
allCommands =
  concat
    [ pseudoCommands
    , goodCommands
    , failCommands
    , checkCommands
    ]


----------------------------------------------------------------------------
-- Here's how we verify the spec using randomized testing.
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
-- We define data types to represent all the specified commands.
--
-- The type parameter v is related to Hedgehog's "symbolic results,"
-- which we currently only use for system-generated ilk IDs.
--
-- Action types that don't refer to ilk IDs need an explicit kind signature
-- because the type parameter is unused and so not inferrable.
----------------------------------------------------------------------------

data Spawn     (v :: * -> *) = Spawn Word160              deriving (Eq, Show)
data Mint      (v :: * -> *) = Mint Word160 Word256       deriving (Eq, Show)
data Transfer  (v :: * -> *) = Transfer Word160 Word256   deriving (Eq, Show)
data BalanceOf (v :: * -> *) = BalanceOf Word160          deriving (Eq, Show)
data Approve   (v :: * -> *) = Approve Word160            deriving (Eq, Show)
data Form      (v :: * -> *) = Form Token                 deriving (Eq, Show)

data GetIlk v = GetIlk (Var (Id Ilk) v)                   deriving (Eq, Show)
data File   v = File (Var (Id Ilk) v) ByteString Word256  deriving (Eq, Show)
data Frob   v = Frob (Var (Id Ilk) v) Word256 Word256     deriving (Eq, Show)

-- This type family gives the symbolic result type for each action type.
type family Outcome c where
  -- For ilk forming, the outcome is an ID.
  Outcome Form = Id Ilk
  -- For other actions, the outcome is a regular VM execution result.
  Outcome c    = Result


-- A command is sent either to some arbitrary contract or to a named token.
data Target = ToContract Word160 | ToToken Token
  deriving (Eq, Show)

-- This data type specifies a source, a target, and a command.
data Do (c :: (* -> *) -> *) v = Do Word160 Target (c v)
  deriving (Eq, Show)


----------------------------------------------------------------------------
-- We define how the various actions update the model.
----------------------------------------------------------------------------

class Change c where
  change :: Ord1 v => Model v -> Do c v -> Var (Outcome c) v -> Model v

instance Change Form where
  change model (Do _ _ (Form gem)) x =
    model
      { ilks =
          Map.insert x (emptyIlk gem) (ilks model)
      }

instance Change Mint where
  change model (Do src (ToToken token) (Mint dst wad)) _ =
    model
      { balances =
          Map.adjust (+ wad) (token, dst) (balances model)
      }

instance Change Transfer where
  change model (Do src (ToToken token) (Transfer dst wad)) _ =
    model
      { balances =
          ( Map.adjust (subtract wad) (token, src)
          . Map.adjust (+ wad) (token, dst)
          $ balances model
          )
      }

instance Change Approve where
  change model (Do src (ToToken token) (Approve guy)) _ =
    model
      { approvals =
          Set.insert (token, src, guy) (approvals model)
      }

instance Change File where
  change model (Do _ _ (File i what x)) _ =
    model { ilks = Map.adjust f i (ilks model) }
    where
      f ilk = if | what == padRight 32 "spot" -> ilk { spot = fixed x }
                 | what == padRight 32 "rate" -> ilk { rate = fixed x }
                 | what == padRight 32 "line" -> ilk { line = cast x }
                 | otherwise ->
                     error "erroneous file"


----------------------------------------------------------------------------
-- Boilerplate stuff would preferrably be automated away using generics.
----------------------------------------------------------------------------

instance HTraversable c => HTraversable (Do c) where
  htraverse f (Do x y c) =
    Do <$> pure x <*> pure y <*> htraverse f c

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
-- Some support stuff for integrating the EVM with Hedgehog.
----------------------------------------------------------------------------

class EvmCall a where
  toEvmCall :: a Concrete -> (Text, Maybe AbiType, [AbiValue])
  fromEvmResult :: a v -> Result -> Outcome a

toCall :: EvmCall t => Do t Concrete -> Call
toCall (Do src target c) =
  let
    (sig, t, xs) = toEvmCall c
    dst = case target of
            ToContract x -> x
            ToToken x -> tokenAddress x
  in
    Call sig src dst t xs

-- This name is very bad...
data Confirmand output action =
  Confirmand
    { prev :: Model Concrete
    , next :: Model Concrete
    , deed :: Do action Concrete
    , output :: output
    }

-- This is a variation on Hedgehog's `Command` record.
data Act action =
  Act
    { concoct :: -- How to invent a random instance of the act.
        Model Symbolic -> Maybe (Gen (Do action Symbolic))

    , confine :: -- How to decide whether the random instance is okay.
        Model Symbolic -> Do action Symbolic -> Bool

    , consume :: -- How to update the model according to the action.
        forall v. Ord1 v => Model v -> Do action v -> Var (Outcome action) v -> Model v

    , confirm :: -- How to verify the outcome of the action.
        Confirmand (Outcome action) action -> Test ()
    }

-- This instance lets us combine confirmation checks like `f <> g`.
instance (Monad f, Semigroup g) => Semigroup (TestT f g) where
  (<>) = liftA2 (<>)

-- Setting fields of this empty act is convenient.
emptyAct :: Act action
emptyAct = Act
  { concoct = const Nothing
  , confine = const (const True)
  , consume = const . const
  , confirm = const (pure ())
  }

-- This will be the basis for all acts that change the model.
changingAct :: (EvmCall c, Change c) => Act c
changingAct = emptyAct { consume = f }
  where
    f model x@(Do _ _ a) v = change model x v

-- Convert our Act to the Hedgehog Command structure.
act
  :: ( HTraversable t, EvmCall t
     , Show (t Symbolic), Show (t Concrete)
     , MonadIO m, Typeable (Outcome t) )
  => Act t -> IORef VM -> Command Gen m Model
act (Act {..}) ref =
  Command
    { commandGen = concoct
    , commandExecute =
        \c@(Do _ _ x) ->
          fmap (fromEvmResult x) (sendDebug ref x (toCall c))
    , commandCallbacks =
        [ Require confine
        , Update consume
        , Ensure (\a b c d -> confirm (Confirmand a b c d))
        ]
    }

confirmVoidSuccess :: Confirmand Result action -> Test ()
confirmVoidSuccess x =
  case view result (resultVm (output x)) of
    Just (VMSuccess (B "")) -> pure ()
    _ -> failure

confirmSuccess :: AbiValue -> Confirmand Result action -> Test ()
confirmSuccess x c =
  case (view result (resultVm (output c)), resultValue (output c)) of
    (Just (VMSuccess _), Just y) ->
      y === x
    _ -> failure

doesRevert
  :: Show (action Concrete)
  => Confirmand Result action
  -> Test ()
doesRevert x =
  case view result (resultVm (output x)) of
    Just (VMFailure Revert) -> pure ()
    _ -> annotate (show (deed x)) >> failure


----------------------------------------------------------------------------
-- Now we define the encoding/decoding specifics for our actions.
----------------------------------------------------------------------------

instance EvmCall Transfer where
  fromEvmResult = const id
  toEvmCall (Transfer dst wad) =
    ( "transfer(address,uint256)"
    , Just AbiBoolType
    , [AbiAddress (cast dst), AbiUInt 256 wad]
    )

instance EvmCall Mint where
  fromEvmResult = const id
  toEvmCall (Mint guy wad) =
    ( "mint(address,uint256)"
    , Nothing
    , [AbiAddress (cast guy), AbiUInt 256 wad]
    )

instance EvmCall BalanceOf where
  fromEvmResult = const id
  toEvmCall (BalanceOf guy) =
    ( "balanceOf(address)"
    , Just (AbiUIntType 256)
    , [AbiAddress (cast guy)]
    )

instance EvmCall Approve where
  fromEvmResult = const id
  toEvmCall (Approve guy) =
    ( "approve(address)"
    , Just AbiBoolType
    , [AbiAddress (cast guy)]
    )

instance EvmCall Form where
  fromEvmResult _ (Result _ out) =
    case out of
      Just (AbiUInt 256 x) -> Id (cast x)
      _ -> error "bad result of form(address)"

  toEvmCall (Form token) =
    ( "form(address)"
    , Just (AbiUIntType 256)
    , [AbiAddress (cast (tokenAddress token))]
    )

instance EvmCall GetIlk where
  fromEvmResult = const id
  toEvmCall (GetIlk (Var (Concrete (Id i)))) =
    ( "ilks(bytes32)"
    , Just (AbiArrayType 6 (AbiUIntType 256))
    , [AbiUInt 256 (cast i)]
    )

instance EvmCall File where
  fromEvmResult = const id
  toEvmCall (File (Var (Concrete (Id i))) what risk) =
    ( "file(bytes32,bytes32,uint256)"
    , Nothing
    , [AbiUInt 256 (cast i), AbiBytes 32 what, AbiUInt 256 risk]
    )

instance EvmCall Frob where
  fromEvmResult = const id
  toEvmCall (Frob (Var (Concrete (Id i))) ink art) =
    ( "frob(bytes32,uint256,uint256)"
    , Nothing
    , [AbiUInt 256 (cast i), AbiUInt 256 ink, AbiUInt 256 art]
    )


----------------------------------------------------------------------------
-- And finally, the specifications of all the command generators.
----------------------------------------------------------------------------

good_form :: Act Form
good_form = changingAct
  { concoct =
      const . pure $ do
        token <- someToken
        pure (Do root (ToContract vatAddress) (Form token))
  }

-- This command runs the getter for an existing ilk ID
-- and verifies that the struct's data matches the model.
check_getIlk :: Act GetIlk
check_getIlk = emptyAct
  { concoct =
      \model -> do
         guard $ not (empty (ilks model))
         pure $ do
           i <- Gen.element (Map.keys (ilks model))
           pure (Do root (ToContract vatAddress) (GetIlk i))

  , confine =
      \model (Do _ _ (GetIlk i)) ->
        Map.member i (ilks model)

  , confirm =
      \c -> do
        let Do _ _ (GetIlk i) = deed c
        case resultValue (output c) of
          Just (AbiArray _ _ v) -> do
            Just (ilkFromStruct v) === Map.lookup i (ilks (next c))
          _ ->
            failure
  }

-- Parameterized command for randomly altering an ilk parameter.
good_file
  :: ByteString
  -> Gen Word256
  -> Act File
good_file what gen = changingAct
  { concoct =
      \model -> do
        guard . not . empty $ ilks model
        pure $ do
          i <- Gen.element (Map.keys (ilks model))
          x <- gen
          pure $ Do root
            (ToContract vatAddress)
            (File i (padRight 32 what) x)

  , confine =
      \model (Do _ _ (File i _ _)) ->
        Map.member i (ilks model)

  , confirm =
      \c -> do
        let Result vm x = output c
        unless (successful vm) failure
        x === Nothing
  }

good_file_spot :: Act File
good_file_spot = good_file "spot" (unfixed <$> anyRay)

good_file_rate :: Act File
good_file_rate = good_file "rate" (unfixed <$> anyRay)

good_file_line :: Act File
good_file_line = good_file "line" anyInt

good_mint :: Act Mint
good_mint = changingAct
  { concoct =
      \s ->
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

          pure (Do root (ToToken token) (Mint dst wad))

  , confirm = confirmVoidSuccess
  }

fail_mint_unauthorized :: Act Mint
fail_mint_unauthorized = emptyAct
  { concoct =
      \model -> do
        guard $ Set.size (accounts model) >= 2
        pure $ do
          token <- Gen.element [DAI, MKR]
          src <- Gen.filter (/= root) (someAccount model)
          dst <- someAccount model
          wad <- someUpTo maxBound
          pure (Do src (ToToken token) (Mint dst wad))
  , confirm = doesRevert
  }

good_transfer :: Act Transfer
good_transfer = changingAct
  { concoct =
      \model ->
         pure $ do
           token <- someToken
           src <- someAccount model
           dst <- someAccount model
           let srcWad = balances model ! (token, src)
           wad <- someUpTo srcWad
           pure (Do src (ToToken token) (Transfer dst wad))
  , confine =
      \model (Do src (ToToken token) (Transfer dst wad)) ->
        balanceOf token src model >= wad
  , confirm = confirmSuccess (AbiBool True)
  }

fail_transfer_tooMuch :: Act Transfer
fail_transfer_tooMuch = emptyAct
  { concoct =
      \model ->
         pure $ do
           token <- someToken
           src <- someAccount model
           dst <- someAccount model
           let srcWad = balances model ! (token, src)
           wad <- Gen.integral (someAbove srcWad)
           pure (Do src (ToToken token) (Transfer dst wad))
  , confirm = doesRevert
  }

check_balanceOf :: Act BalanceOf
check_balanceOf = emptyAct
  { concoct =
      \model ->
        pure $ do
          src <- someAccount model
          guy <- someAccount model
          token <- someToken
          pure (Do src (ToToken token) (BalanceOf guy))
  , confirm =
      \c -> do
        let Do _ (ToToken token) (BalanceOf guy) = deed c
        resultValue (output c) ===
          Just (AbiUInt 256 (balanceOf token guy (next c)))
  }

good_approve :: Act Approve
good_approve = changingAct
  { concoct =
      \model -> do
        pure $ do
          src <- someAccount model
          guy <- pure vatAddress
          token <- someToken
          pure (Do src (ToToken token) (Approve guy))
  , confine =
      \model (Do src (ToToken token) (Approve guy)) ->
        Set.member src (accounts model)
  , confirm =
      confirmSuccess (AbiBool True)
  }

good_frob :: Act Frob
good_frob = emptyAct
  { concoct =
      \model -> do
        guard . not . empty $ ilks model
        pure $ do
          src <- someAccount model
          (ilkId, ilk) <- someIlk model
          x <- someUpTo (balanceOf (gem ilk) src model)
          pure (Do src (ToContract vatAddress) (Frob ilkId x 0))

  , confine =
      \model (Do src _ (Frob ilkId x _)) ->
        case Map.lookup ilkId (ilks model) of
          Nothing -> False
          Just ilk ->
            and
              [ balanceOf (gem ilk) src model >= x
              , Set.member (gem ilk, src, vatAddress) (approvals model)
              , rayMultiplicationSafe (spot ilk) (cast x)
              ]

  , consume =
      \model (Do src _ (Frob ilkId x _)) _ ->
        let
          Just ilk = Map.lookup ilkId (ilks model)
        in
          model
            { balances =
                Map.adjust (subtract x) (gem ilk, src)
                  (balances model)
            }

  , confirm = confirmVoidSuccess
  }

-- This command only affects the model.
--
-- It generates a random new account with zero balances.
-- In the EVM, all such accounts exist implicitly.
--
-- If we want to run these tests against a real node,
-- we might have to generate private/public keys here...
--
gen_spawn :: Command Gen (PropertyT IO) Model
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



----------------------------------------------------------------------------
-- Find better place for this stuff.
----------------------------------------------------------------------------

successful :: VM -> Bool
successful vm =
  case view result vm of
    Just (VMSuccess _) -> True
    _ -> False

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
