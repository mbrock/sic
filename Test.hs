{-# Language OverloadedStrings #-}

import TestBase
import TestLoad
import TestModel
import TestBasicMath
import TestDebug
import TestToken

import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import System.IO.Silently (hSilence)
import System.IO (stdout, stderr)
import System.Random
import System.Environment (getArgs)

import qualified Data.ByteString as BS
import Data.Word (Word8)

checkGood :: GroupName -> [(PropertyName, Property)] -> IO ()
checkGood s ps =  do
  good <- checkSequential $ Group s ps
  unless good exitFailure

checkFail :: String -> [(PropertyName, Property)] -> IO ()
checkFail s ps = do
  putStrLn ("Verifying failure of " <> s <> "... ")
  good <-
    checkSequential
      (Group "" [(x, withShrinks 0 y) | (x, y) <- ps])
  if good
    then do
      putStrLn "unfortunately, all tests passed!"
      exitFailure
    else do
      putStrLn "tests failed as expected."

mainGood :: IO ()
mainGood = do
  resetDebug
  checkGood "System"
    [("Full test suite", prop_system (pure initialVm))]

  -- check "Sic basic math"
  --   [ ("iadd", prop_iadd (+))
  --   , ("imul", prop_imul (*))
  --   , ("rmul", prop_rmul (*))
  --   , ("rpow", prop_rpow (^) rpowMaxResult)
  --   ]

mainFail :: IO ()
mainFail = do
  resetDebug
  forM_ [1..5] $ \i ->
    checkFail ("system mutation " <> show i)
      [("Full test suite", prop_system (mutate initialVm))]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--mutation"] -> mainFail
    [] -> mainGood
    _ -> do
      putStrLn "nope"
      exitFailure

-- This bytecode mutation testing code is very prototype.
-- Right now it just alters one random opcode according to
-- a stupid scheme given below.

mutate :: MonadIO m => VM -> m VM
mutate vm = do
  let
    code = vm ^. env . contracts . ix (cast vatAddress) . bytecode
  i <- liftIO (randomRIO (0, BS.length code))
  pure $
    vm & env . contracts . ix (cast vatAddress) . bytecode . ix i %~ mutateOp

mutateOp :: Word8 -> Word8
mutateOp x =
  case x of
    1 -> 3
    2 -> 4
    3 -> 1
    4 -> 2
    5 -> 7
    6 -> 4
    7 -> 5
    0x10 -> 0x12
    0x11 -> 0x13
    0x12 -> 0x10
    0x13 -> 0x11
    _ -> 0x00

do_math x y name =
  case
    run (name <> "(int256,int256)") (AbiIntType 256)
      [AbiInt 256 x, AbiInt 256 y]
  of
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
      Call "rpow(int256,int256)" root example (Just (AbiIntType 256))
        [AbiInt 256 (unfixed x), AbiInt 256 n]
  in
    runFromVM (execState (setupCall c) initialVm) "rpow"
