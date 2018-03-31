{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}

module TestLoad where

import TestBase
import TestModel

import qualified Data.Vector as Vector

-- Top-level global I/O!
{-# NOINLINE global #-}
global = unsafePerformIO (load emptyVm)

((example, gemAddress), vm1) = global

emptyVm :: VM
emptyVm = vmForEthrunCreation ""

load :: VM -> IO ((Addr, Gem -> Addr), VM)
load vm = do
  exampleCode <-
    hexByteString "code" . encodeUtf8 . pack <$> getEnv "EXAMPLE_CODE"
  factoryCode <-
    hexByteString "code" . encodeUtf8 . pack <$> getEnv "TOKEN_FACTORY_CODE"
  pure . flip runState vm $ do
    example <- create exampleCode
    factory <- create factoryCode
    Returned (AbiAddress dai) <-
      call (Call root factory "make(bytes32,bytes32)" (Just AbiAddressType)
        [AbiBytes 32 (padRight 32 "DAI"), AbiBytes 32 (padRight 32 "Dai")])
    Returned (AbiAddress mkr) <-
      call (Call root factory "make(bytes32,bytes32)" (Just AbiAddressType)
        [AbiBytes 32 (padRight 32 "MKR"), AbiBytes 32 (padRight 32 "Maker")])
    return
      ( cast example
      , cast . \case DAI -> dai; MKR -> mkr
      )

create :: Num t => ByteString -> EVM t
create x = do
  resetState
  assign (state . gas) 0xffffffffffffff
  assign (state . caller) root
  Just i <- preuse (env . contracts . ix ethrunAddress . nonce)
  let a = newContractAddress ethrunAddress (cast i)
  env . contracts . ix ethrunAddress . nonce += 1
  env . contracts . at a .= Just (initialContract x)
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
  { callSrc :: Addr
  , callDst :: Addr
  , callSig :: Text
  , callRet :: Maybe AbiType
  , callArg :: [AbiValue]
  } deriving (Eq, Show)

setupCall :: Call -> EVM ()
setupCall (Call src dst sig ret xs) = do
  resetState
  loadContract dst
  assign (state . caller) src
  assign (state . gas) 0xffffffffffffff
  assign (state . calldata) (B (abiCalldata sig (Vector.fromList xs)))

call :: Call -> EVM CallResult
call info@(Call src dst sig ret xs) = do
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
      setupCall $ Call root example sig (Just ret) args
      exec
  case runState continue vm1 of
    (VMSuccess (B out), _) ->
      case runGetOrFail (getAbi ret) (fromStrict out) of
        Right ("", _, x) -> Right x
        _ -> error "ABI return value decoding error"
    (VMFailure problem, _) ->
      Left problem

performReversion vm0 vm1 =
  case view result vm1 of
    Just (VMFailure _) ->
      vm1 & env . contracts .~ view (env . contracts) vm0
    _ ->
      vm1

send ref c@(Call src dst sig ret xs) = do
  vm <- liftIO (readIORef ref)
  let vm' = performReversion vm (execState (call c) vm)
  liftIO (writeIORef ref vm')
  pure $ case (ret, view result vm') of
    (Just t, Just (VMSuccess (B out))) ->
      case runGetOrFail (getAbi t) (fromStrict out) of
        Right ("", _, x) -> (vm', Just x)
        _ -> error "ABI return value decoding error"
    (Nothing, Just (VMSuccess (B ""))) -> (vm', Nothing)
    (Nothing, Just (VMSuccess _)) -> error "unexpected return value"
    (_, Just (VMFailure _)) -> (vm', Nothing)
    (_, Nothing) -> error "weird VM state"
