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

import Control.Monad (unless)
import Control.Monad.State.Strict (execState, runState)
import System.Exit (exitFailure)

import Data.ByteString (ByteString)
import Data.ByteString.Lazy (fromStrict)
import qualified Data.ByteString as BS

import Data.Text (Text)
import qualified Data.Text as Text

import qualified Data.Vector as Vector

import Control.Lens

foo :: ByteString -> Text -> AbiType -> [AbiValue] -> Maybe AbiValue
foo code sig tret args = do
  case runState exec (vmForEthrunCreation code) of
    (VMSuccess (B runtime), vm1) -> do
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
            Right ("", _, x) -> Just x
            _ -> Nothing
        (VMFailure problem, _) ->
          Nothing
    _ -> Nothing

program :: ByteString
program = unsafePerformIO (hexByteString "code" <$> BS.getContents)

maxint = 2 ^ 255 - 1

prop_add :: Property
prop_add =
  property $ do
    x <- forAll $ Gen.integral (Range.linear (-maxint) maxint)
    y <- forAll $ Gen.integral (Range.linear (-maxint) maxint)
    case foo program "add(int128,int128)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Just (AbiInt 256 z) ->
        z === x + y
      Nothing ->
        failure

main :: IO ()
main = do
  good <- checkParallel $$(discover)
  unless good exitFailure
