{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RankNTypes #-}
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
  , act good_frob
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

allCommands :: [VmCommand]
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

----------------------------------------------------------------------------

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

data Target =
  ToContract Word160 | ToToken Token
  deriving (Eq, Show)

data Do (c :: (* -> *) -> *) v =
  Do Word160 Target (c v)
  deriving (Eq, Show)

instance HTraversable c => HTraversable (Do c) where
  htraverse f (Do x y c) =
    Do <$> pure x <*> pure y <*> htraverse f c

class ToABI a where
  toABI :: a Concrete -> (Text, Maybe AbiType, [AbiValue])

toCall :: ToABI t => Do t Concrete -> Call
toCall (Do src target c) =
  let
    (sig, t, xs) = toABI c
    dst =
      case target of
        ToContract x -> x
        ToToken x -> tokenAddress x
  in
    Call sig src dst t xs

-- This is a slight variant on Hedgehog's Command structure.

data Confirmand output action =
  Confirmand
    { prev :: Model Concrete
    , next :: Model Concrete
    , deed :: Do action Concrete
    , output :: output
    }

data Act output action =
  Act
    { concoct ::
        Model Symbolic
          -> Maybe (Gen (Do action Symbolic))
    , convert ::
        Result -> output
    , require ::
        Maybe
          (Model Symbolic
            -> Do action Symbolic
            -> Bool)
    , perform ::
        forall v. Ord1 v
          => Model v
          -> Do action v
          -> Var output v
          -> Model v
    , confirm ::
        Confirmand output action -> Test ()
    }

unchanged :: a -> b -> c -> a
unchanged x _ _ = x

-- Convert our Act to the Hedgehog Command structure.
act
  :: ( HTraversable t
     , ToABI t
     , Show (t Symbolic)
     , Show (t Concrete)
     , MonadIO m
     , Typeable output
     )
  => Act output t
  -> IORef VM
  -> Command Gen m Model
act (Act {..}) ref =
  Command
    { commandGen =
        concoct
    , commandExecute =
        \c@(Do _ _ x) ->
          fmap convert (sendDebug ref x (toCall c))
    , commandCallbacks =
        let
          singleton x = [x]
        in concat
          [ maybe [] (singleton . Require) require
          , [Update perform]
          , [Ensure $ \a b c d -> confirm (Confirmand a b c d)]
          ]
    }

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

good_form :: Act (Id Ilk) Form
good_form = Act
  { concoct =
      const . pure $ do
         token <- someToken
         pure (Do root (ToContract vatAddress) (Form token))
  , convert =
      \(Result _ out) ->
         case out of
           Just (AbiUInt 256 x) -> Id (cast x)
           _ -> error "bad result of form(address)"
  , perform =
      \model (Do _ _ (Form gem)) o ->
        model
          { ilks = Map.insert o (emptyIlk gem) (ilks model)
          }
  , require = Nothing
  , confirm = const (pure ())
  }

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
check_getIlk :: Act Result GetIlk
check_getIlk = Act
  { concoct =
      \model -> do
         guard $ not (empty (ilks model))
         pure $ do
           i <- Gen.element (Map.keys (ilks model))
           pure (Do root (ToContract vatAddress) (GetIlk i))
  , require = Just $
      \model (Do _ _ (GetIlk i)) ->
        Map.member i (ilks model)
  , convert = id
  , perform = unchanged
  , confirm =
      \c -> do
        let Do _ _ (GetIlk i) = deed c
        case resultValue (output c) of
          Just (AbiArray _ _ v) -> do
            Just (ilkFromStruct v) === Map.lookup i (ilks (next c))
          _ ->
            failure
  }

successful :: VM -> Bool
successful vm =
  case view result vm of
    Just (VMSuccess _) -> True
    _ -> False

-- Parameterized command for randomly altering an ilk parameter.
good_file
  :: ByteString
  -> Gen Word256
  -> (Word256 -> Ilk -> Ilk)
  -> Act Result File
good_file what gen f = Act
  { concoct =
      \model -> do
        guard . not . empty $ ilks model
        pure $ do
          i <- Gen.element (Map.keys (ilks model))
          x <- gen
          pure $ Do root
            (ToContract vatAddress)
            (File i (padRight 32 what) x)

  , require = Just $
      \model (Do _ _ (File i _ _)) ->
        Map.member i (ilks model)
  , convert = id
  , perform =
      \model (Do _ _ (File i _ x)) _ ->
         model
           { ilks = Map.adjust (f x) i (ilks model) }
  , confirm =
      \c -> do
        let Result vm x = output c
        unless (successful vm) failure
        x === Nothing
  }

good_file_spot :: Act Result File
good_file_spot =
  good_file "spot"
    (unfixed <$> anyRay)
    (\x ilk -> ilk { spot = fixed x })

good_file_rate :: Act Result File
good_file_rate =
  good_file "rate"
    (unfixed <$> anyRay)
    (\x ilk -> ilk { rate = fixed x })

good_file_line :: Act Result File
good_file_line =
  good_file "line"
    anyInt
    (\x ilk -> ilk { line = cast x })

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

confirmReversion
  :: Show (action Concrete)
  => Confirmand Result action
  -> Test ()
confirmReversion x =
  case view result (resultVm (output x)) of
    Just (VMFailure Revert) -> pure ()
    _ -> annotate (show (deed x)) >> failure

good_mint :: Act Result Mint
good_mint = Act
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

  , require = Nothing
  , convert = id
  , confirm = confirmVoidSuccess
  , perform =
      \s (Do src (ToToken token) (Mint dst wad)) _ ->
           s { balances =
                 Map.adjust (+ wad) (token, dst) (balances s) }
  }

fail_mint_unauthorized :: Act Result Mint
fail_mint_unauthorized = Act
  { concoct =
      \model -> do
        guard $ Set.size (accounts model) >= 2
        pure $ do
          token <- Gen.element [DAI, MKR]
          src <- Gen.filter (/= root) (someAccount model)
          dst <- someAccount model
          wad <- someUpTo maxBound
          pure (Do src (ToToken token) (Mint dst wad))
  , require = Nothing
  , convert = id
  , confirm = confirmReversion
  , perform = unchanged
  }

good_transfer :: Act Result Transfer
good_transfer = Act
  { concoct =
      \model ->
         pure $ do
           token <- someToken
           src <- someAccount model
           dst <- someAccount model
           let srcWad = balances model ! (token, src)
           wad <- someUpTo srcWad
           pure (Do src (ToToken token) (Transfer dst wad))
  , require =
      Just $
        \model (Do src (ToToken token) (Transfer dst wad)) ->
          balanceOf token src model >= wad
  , convert = id
  , confirm = confirmSuccess (AbiBool True)
  , perform =
      \model (Do src (ToToken token) (Transfer dst wad)) _ ->
        model
          { balances =
              Map.adjust (subtract wad) (token, src) .
              Map.adjust (+ wad) (token, dst) $
                balances model
          }
  }

fail_transfer_tooMuch :: Act Result Transfer
fail_transfer_tooMuch = Act
  { concoct =
      \model ->
         pure $ do
           token <- someToken
           src <- someAccount model
           dst <- someAccount model
           let srcWad = balances model ! (token, src)
           wad <- Gen.integral (someAbove srcWad)
           pure (Do src (ToToken token) (Transfer dst wad))
  , require = Nothing
  , convert = id
  , confirm = confirmReversion
  , perform = unchanged
  }

check_balanceOf :: Act Result BalanceOf
check_balanceOf = Act
  { concoct =
      \model ->
        pure $ do
          src <- someAccount model
          guy <- someAccount model
          token <- someToken
          pure (Do src (ToToken token) (BalanceOf guy))
  , require = Nothing
  , convert = id
  , confirm =
      \c -> do
        let Do _ (ToToken token) (BalanceOf guy) = deed c
        resultValue (output c) ===
          Just (AbiUInt 256 (balanceOf token guy (next c)))
  , perform = unchanged
  }

good_approve :: Act Result Approve
good_approve = Act
  { concoct =
      \model -> do
        pure $ do
          src <- someAccount model
          guy <- pure vatAddress
          token <- someToken
          pure (Do src (ToToken token) (Approve guy))
  , require =
      Just $
        \model (Do src (ToToken token) (Approve guy)) ->
          Set.member src (accounts model)
  , convert = id
  , confirm = confirmSuccess (AbiBool True)
  , perform =
      \model (Do src (ToToken token) (Approve guy)) _ ->
        model
          { approvals =
              Set.insert (token, src, guy) (approvals model)
          }
  }

good_frob :: Act Result Frob
good_frob = Act
  { concoct =
      \model -> do
        guard . not . empty $ ilks model
        pure $ do
          src <- someAccount model
          (ilkId, ilk) <- someIlk model
          x <- someUpTo (balanceOf (gem ilk) src model)
          pure (Do src (ToContract vatAddress) (Frob ilkId x 0))
  , require =
      Just $
        \model (Do src _ (Frob ilkId x _)) ->
          case Map.lookup ilkId (ilks model) of
            Nothing -> False
            Just ilk ->
              and
                [ balanceOf (gem ilk) src model >= x
                , Set.member (gem ilk, src, vatAddress) (approvals model)
                , let Just ilk = Map.lookup ilkId (ilks model)
                  in spot ilk * cast x < cast maxInt
                ]
  , convert = id
  , confirm = confirmVoidSuccess
  , perform =
      \model (Do src _ (Frob ilkId x _)) _ ->
        let
          Just ilk = Map.lookup ilkId (ilks model)
        in
          model
            { balances =
                Map.adjust (subtract x) (gem ilk, src)
                  (balances model)
            }
  }
