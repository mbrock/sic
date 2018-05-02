{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module TestD0 where

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
  [ act good_form
  ]

-- These commands exercise the system's error cases.
failCommands :: [VmCommand]
failCommands =
  []

-- These commands verify getters against the model's data.
checkCommands :: [VmCommand]
checkCommands =
  [ act check_feel
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

type Wad = Word256 -- XXX

data Spawn     (v :: * -> *) = Spawn Word160              deriving (Eq, Show)
data Mold      (v :: * -> *) = Mold (Id Ilk) Ray Ray Wad  deriving (Eq, Show)

data Feel (v :: * -> *) = Feel (Id Ilk)                   deriving (Eq, Show)

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
  change :: Ord1 v => Model v -> Do c v -> Var Result v -> Model v

instance Change Mold where
  change model (Do _ _ (Mold i φ ψ ω)) x =
    model
      { ilks =
          (ilks model)
      }


----------------------------------------------------------------------------
-- Boilerplate stuff would preferrably be automated away using generics.
----------------------------------------------------------------------------

instance HTraversable c => HTraversable (Do c) where
  htraverse f (Do x y c) =
    Do <$> pure x <*> pure y <*> htraverse f c

instance HTraversable Spawn where
  htraverse f (Spawn x) = pure (Spawn x)
instance HTraversable Mold where
  htraverse f (Mold a b c d) = pure (Mold a b c d)
instance HTraversable Feel where
  htraverse f (Feel i) = pure (Feel i)


----------------------------------------------------------------------------
-- Some support stuff for integrating the EVM with Hedgehog.
----------------------------------------------------------------------------

class EvmCall a where
  toEvmCall :: a Concrete -> (Text, Maybe AbiType, [AbiValue])
  fromEvmResult :: a v -> Result -> Result

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
        forall v. Ord1 v => Model v -> Do action v -> Var Result v -> Model v

    , confirm :: -- How to verify the outcome of the action.
        Confirmand Result action -> Test ()
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
     , MonadIO m, Typeable Result)
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

instance EvmCall Mold where
  fromEvmResult = const id
  toEvmCall (Mold (Id i) φ ψ ω) =
    ( "mold(uint256,int256,int256,int256)"
    , Nothing
    , [ AbiBytes 32 i
      , AbiInt 256 (unfixed φ)
      , AbiInt 256 (unfixed ψ)
      , AbiInt 256 (cast ω)
      ]
    )

instance EvmCall Feel where
  fromEvmResult = const id
  toEvmCall (Feel (Id i)) =
    ( "feel(uint256)"
    , Just (AbiArrayType 4 (AbiUIntType 256))
    , [AbiBytes 32 i]
    )

----------------------------------------------------------------------------
-- And finally, the specifications of all the command generators.
----------------------------------------------------------------------------

someId :: Gen (Id a)
someId =
  fmap (Id . padRight 32 . encodeUtf8 . pack)
    (Gen.list (Range.singleton 8) Gen.alphaNum)

good_form :: Act Mold
good_form = changingAct
  { concoct =
      const . pure $ do
        i <- someId
        pure (Do root (ToContract vatAddress) (Mold i 0 1 0))
  }

-- This command runs the getter for an existing ilk ID
-- and verifies that the struct's data matches the model.
check_feel :: Act Feel
check_feel = emptyAct
  { concoct =
      \model -> do
         guard $ not (empty (ilks model))
         pure $ do
           i <- Gen.element (Map.keys (ilks model))
           pure (Do root (ToContract vatAddress) (Feel i))

  , confine =
      \model (Do _ _ (Feel i)) ->
        Map.member i (ilks model)

  , confirm =
      \c -> do
        let Do _ _ (Feel i) = deed c
        case resultValue (output c) of
          Just (AbiArray _ _ v) -> do
            Just (ilkFromStruct v) === Map.lookup i (ilks (next c))
          _ ->
            failure
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
    [AbiUInt 256 a, AbiUInt 256 b, AbiUInt 256 c, AbiUInt 256 d] ->
      Ilk
        { phi = fixed a
        , psi = fixed b
        , omega = cast c
        , sigma = cast d
        }
    _ ->
      error "invalid ilk struct"
