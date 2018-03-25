{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import System.IO.Unsafe

import EVM
import EVM.ABI
import EVM.Concrete (Blob (B))
import EVM.Exec
import EVM.Types
import EVM.UnitTest

import Data.Binary.Get (runGetOrFail)

import Control.Monad (unless, when)
import Control.Monad.State.Strict (execState, runState)
import System.Exit (exitFailure)

import Data.ByteString (ByteString)
import Data.ByteString.Lazy (fromStrict)
import qualified Data.ByteString as BS

import Data.Text (Text)
import qualified Data.Text as Text

import qualified Data.Vector as Vector

import Control.Lens

(runtime, vm1) =
  case (unsafePerformIO $
          runState exec . vmForEthrunCreation <$>
            hexByteString "code" <$> BS.getContents) of
    (VMFailure problem, _) -> error (show problem)
    (VMSuccess (B runtime), vm) -> (runtime, vm)

run :: Text -> AbiType -> [AbiValue] -> Either Error AbiValue
run sig tret args = do
  let
    target = view (state . contract) vm1
    vm2 = execState (replaceCodeOfSelf runtime) vm1
    continue = do
      resetState
      assign (state . gas) 0xffffffffffffff
      loadContract target
      assign (state . calldata) (B (abiCalldata sig (Vector.fromList args)))
      exec
  case runState continue vm2 of
    (VMSuccess (B out), _) ->
      case runGetOrFail (getAbi tret) (fromStrict out) of
        Right ("", _, x) -> Right x
        _ -> error "ABI return value decoding error"
    (VMFailure problem, _) ->
      Left problem

maxint = 2 ^ 255 - 1

integer :: Integral a => a -> Integer
integer x = fromIntegral x

prop_add :: Property
prop_add =
  withTests 200 . property $ do
    x <- forAll $ Gen.integral (Range.linear (-maxint) maxint)
    y <- forAll $ Gen.integral (Range.linear (-maxint) maxint)
    case run "add(int128,int128)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Right (AbiInt 256 z) -> do
        z === x + y
      Left Revert ->
        if (x > 0 && y > 0)
          then assert (x + y < x)     -- Overflow
          else
            if (x < 0 && y < 0)
              then assert (x + y > x) -- Underflow
              else failure

main :: IO ()
main = do
  good <- checkParallel $$(discover)
  unless good exitFailure
