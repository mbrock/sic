{-# Language LambdaCase #-}
{-# Language NamedFieldPuns #-}
{-# Language OverloadedStrings #-}

module TestLoad where

import TestBase
import TestModel

import qualified Data.Vector as Vector
import qualified Data.ByteString as BS

data Global = Global
  { globalExample :: !Word160
  , globalVatAddress :: !Word160
  , globalTokenAddress :: !(Token -> Word160)
  , globalD0Address :: !Word160
  , globalInitialVm  :: !VM
  }

-- Top-level global I/O!
{-# NOINLINE global #-}
global = unsafePerformIO (load (vmForEthrunCreation ""))

-- Rebind some names...
Global
  { globalExample = example
  , globalVatAddress = vatAddress
  , globalTokenAddress = tokenAddress
  , globalD0Address = d0Address
  , globalInitialVm = initialVm
  } = global

load :: VM -> IO Global
load vm = do

  let
    loadFromEnv x =
      hexByteString "code" . encodeUtf8 . pack <$> getEnv x

  exampleCode <-
    loadFromEnv "T0_CODE"
  tokenCode <-
    loadFromEnv "PIE_CODE"
  binCode <-
    loadFromEnv "BIN_CODE"
  d0Code <-
    loadFromEnv "D0_CODE"

  pure . flip evalState vm $ do
    example <-
      create exampleCode []

    let
      makeToken symbol =
        create tokenCode
          [ AbiBytes 32 (padRight 32 symbol)
          , AbiBytes 32 (padRight 32 (symbol <> " token"))
          ]

    dai <- makeToken "DAI"
    mkr <- makeToken "MKR"
    eth <- makeToken "ETH"
    dgx <- makeToken "DGX"
    omg <- makeToken "OMG"

    vat <-
      create binCode
        [AbiAddress dai, AbiAddress 0, AbiAddress 0]

    d0 <-
      create d0Code []

    vm' <- get
    return Global
      { globalExample = cast example
      , globalVatAddress = cast vat
      , globalD0Address = cast d0
      , globalTokenAddress =
          cast .
            \case DAI -> dai; MKR -> mkr; ETH -> eth; DGX -> dgx; OMG -> omg
      , globalInitialVm = vm'
      }

create :: Num t => ByteString -> [AbiValue] -> EVM t
create x args = do
  resetState
  assign (state . gas) 0xffffffffffffff
  assign (state . caller) root
  Just i <- preuse (env . contracts . ix ethrunAddress . nonce)
  let a = newContractAddress ethrunAddress (cast i)
  env . contracts . ix ethrunAddress . nonce += 1

  let
    calldata =
      BS.drop 4 (abiCalldata "foo()" (Vector.fromList args))

  env . contracts . at a .=
    Just (initialContract (x <> calldata))
  loadContract a
  exec >>= \case
    VMFailure e -> error (show e)
    VMSuccess (B runtime) -> do
      replaceCodeOfSelf runtime
      return (cast a)

data CallResult
  = Returned AbiValue
  | Stopped
  | Failed Error
  deriving (Show)

data Call = Call
  { callSig :: Text
  , callSrc :: Word160
  , callDst :: Word160
  , callRet :: Maybe AbiType
  , callArg :: [AbiValue]
  } deriving (Eq, Show)

setupCall :: Call -> EVM ()
setupCall (Call sig src dst ret xs) = do
  resetState
  loadContract (Addr dst)
  assign (state . caller) (Addr src)
  assign (state . gas) 100000
  assign (state . calldata) (B (abiCalldata sig (Vector.fromList xs)))

call :: Call -> EVM CallResult
call info@(Call sig src dst ret xs) = do
  setupCall info
  exec >>= \case
    VMSuccess (B out) ->
      case ret of
        Nothing -> pure Stopped
        Just retType ->
          case runGetOrFail (getAbi retType) (fromStrict out) of
            Right ("", _, x) -> pure (Returned x)
            _ -> error ("return value decoding error in " ++ unpack sig)
    VMFailure problem ->
      pure (Failed problem)

-- Some ugly code to run an ABI method and decode its return value.
run :: Text -> AbiType -> [AbiValue] -> Either Error AbiValue
run sig ret args = do
  let
    continue = do
      setupCall $ Call sig root example (Just ret) args
      exec
  case runState continue initialVm of
    (VMSuccess (B out), _) ->
      case runGetOrFail (getAbi ret) (fromStrict out) of
        Right ("", _, x) -> Right x
        _ -> error "ABI return value decoding error"
    (VMFailure problem, _) ->
      Left problem

performReversion :: VM -> VM -> VM
performReversion vm0 vm1 =
  case view result vm1 of
    Just (VMFailure _) ->
      vm1 & env . contracts .~ view (env . contracts) vm0
    _ ->
      vm1

data Result = Result
  { resultVm :: !VM
  , resultValue :: !(Maybe AbiValue)
  }

send :: MonadIO m => IORef VM -> Call -> m Result
send ref c@(Call sig src dst ret xs) = do
  vm <- liftIO (readIORef ref)
  let vm' = performReversion vm (execState (call c) vm)
  liftIO (writeIORef ref vm')

  pure $ case (ret, view result vm') of

    (Just t, Just (VMSuccess (B out))) ->
      case runGetOrFail (getAbi t) (fromStrict out) of
        Right ("", _, x) ->
          Result vm' (Just x)
        _ ->
          error "ABI return value decoding error"

    (Nothing, Just (VMSuccess (B ""))) ->
      Result vm' Nothing

    (Nothing, Just (VMSuccess _)) ->
      error "unexpected return value"

    (_, Just (VMFailure _)) ->
      Result vm' Nothing

    (_, Nothing) ->
      error "weird VM state"
