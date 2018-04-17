{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}

module TestDebug where

import TestBase
import TestLoad

import qualified Brick
import qualified EVM.Fetch as Fetch
import qualified EVM.Stepper as Stepper

failedVm :: IORef (Maybe (VM, Text))
{-# NOINLINE failedVm #-}
failedVm = unsafePerformIO (newIORef Nothing)

resetDebug :: IO ()
resetDebug = writeIORef failedVm Nothing

sendDebug
  :: (MonadIO m, Show a) => IORef VM -> a -> Call
  -> m (VM, Maybe AbiValue)
sendDebug ref cmd c = do
  vm0 <- liftIO (readIORef ref)
  (vm1, x) <- send ref c
  case view result vm1 of
    Just (VMFailure Revert) -> do
      let
        vm' = flip execState vm0 $ do
          setupCall c
          pushTrace (EntryTrace (pack (show cmd)))
      liftIO (writeIORef failedVm (Just (vm', pack (show cmd))))
    _ ->
      pure ()
  pure (vm1, x)

runFromVM :: VM -> Text -> IO VM
runFromVM vm msg = do
  dappRoot <- getEnv "DAPP_ROOT"
  dappFile <- getEnv "DAPP_FILE"
  dapp <- loadDappInfo dappRoot dappFile
  let
    ui0 = UiVmState
           { _uiVm = vm
           , _uiVmNextStep =
               void Stepper.execFully >> Stepper.evm finalize
           , _uiVmStackList = undefined
           , _uiVmBytecodeList = undefined
           , _uiVmTraceList = undefined
           , _uiVmSolidityList = undefined
           , _uiVmSolc = Nothing
           , _uiVmDapp = Just dapp
           , _uiVmStepCount = 0
           , _uiVmFirstState = undefined
           , _uiVmMessage = Just (unpack msg)
           , _uiVmNotes = []
           }
    ui1 = updateUiVmState ui0 vm & set uiVmFirstState ui1

    testOpts = UnitTestOptions
      { oracle            = Fetch.zero
      , verbose           = False
      , match             = ""
      , vmModifier        = id
      , testParams        = error "irrelevant"
      }

  ui2 <- Brick.customMain mkVty Nothing (app testOpts) (UiVmScreen ui1)
  case ui2 of
    UiVmScreen ui -> return (view uiVm ui)
    _ -> error "internal error: customMain returned prematurely"

debug :: MonadIO m => m ()
debug = do
  liftIO (readIORef failedVm) >>=
    \case
      Nothing -> pure ()
      Just (vm', msg) -> liftIO $ do
        void (runFromVM vm' msg)
