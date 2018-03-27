{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language ScopedTypeVariables #-}

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

import Data.DoubleWord

import Control.Lens
import Control.Monad (unless, when)
import Control.Monad.State.Strict (execState, runState)
import Data.Binary.Get (runGetOrFail)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy (fromStrict)
import Data.Fixed
import Data.Ratio
import Data.Text (Text)
import System.Exit (exitFailure)
import qualified Data.ByteString as BS
import qualified Data.Text as Text
import qualified Data.Vector as Vector

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

maxint :: Integral a => a
maxint = 2 ^ 255 - 1

minint :: Integral a => a
minint = - (2 ^ 255)

smallRange = Range.linear (-100) 100
maxRange = Range.linear 0 maxint
anyInt = forAll (Gen.integral maxRange)

type Ray = Decimal E27

ray x = x :: Ray
rayRange x = (Range.linear (unfixed (ray x)) (- (unfixed (ray x))))

anyRay :: PropertyT IO (Ray)
anyRay = forAll $
  fixed <$>
    (Gen.choice $
      Gen.integral maxRange :
        map (Gen.integral . rayRange)
          [10^n | n <- [0, 6 .. 36]])

integer :: Integral a => a -> Integer
integer x = fromIntegral x

prop_iadd :: Property
prop_iadd =
  withTests 100 . property $ do
    x <- anyInt
    y <- anyInt
    case run "iadd(int256,int256)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Right (AbiInt 256 z) -> do
        z === x + y
      Left Revert -> do
        let z = integer x + integer y
        annotate (show z)
        assert (z > maxint || z <= minint)

unfixed :: Num a => Decimal b -> a
unfixed (D (MkFixed i)) = fromIntegral i

fixed :: Integral a => a -> Ray
fixed x = fromRational (fromIntegral (fromIntegral x :: Int256) % 10^27)

prop_imul :: Property
prop_imul =
  withTests 100 . property $ do
    x <- anyInt
    annotate (show x)
    y <- anyInt
    annotate (show y)
    case run "imul(int256,int256)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Right (AbiInt 256 z) -> do
        z === x * y
      Left Revert -> do
        assert (x * y `div` y /= x)
      Left e -> do
        annotate (show e)
        failure
        
prop_rmul :: Property
prop_rmul =
  withShrinks 10 . withTests 100 . property $ do
    x <- unfixed <$> anyRay
    annotate (show (fixed x))
    y <- unfixed <$> anyRay
    annotate (show (fixed y))
    case run "rmul(int256,int256)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Right (AbiInt 256 z) -> do
        annotate (show (fixed z))
        annotate (show (abs (fixed z - fixed x * fixed y)))
        fixed z === fixed x * fixed y
      Left Revert -> do
        if signum x * signum y > 0
          then assert (integer x * integer y + (10^27 `div` 2) > maxint)
          else assert (integer x * integer y + (10^27 `div` 2) < minint)
      Left e -> do
        annotate (show e)
        failure 

prop_rpow :: Property
prop_rpow =
  withTests 500 . withShrinks 10 . property $ do
    x <- anyRay
    n <- anyInt
    case run "rpow(int256,int256)" (AbiIntType 256) [AbiInt 256 (unfixed x), AbiInt 256 n] of
      Right (AbiInt 256 z) -> do
        if n == 0
          then do
            assert (not (x == 0))
            fixed z === 1.0
          else fixed z === x ^ fromIntegral n
      Left Revert -> do
        assert $
          -- x too big to multiply?
             (x > fixed maxint / 10^27) || (x == 0 && n == 0)
          -- x^n would overflow?
          || fromIntegral n >
               (log (realToFrac (fixed maxint)) / log (abs (realToFrac x)))
      Left e -> do
        annotate (show e)
        failure 

main :: IO ()
main = do
  good <- checkParallel $$(discover)
  unless good exitFailure






newtype Decimal e = D (Fixed e)
  deriving (Ord, Eq, Real, RealFrac)

instance HasResolution e => Read (Decimal e) where
  readsPrec n s = fmap (\(x, y) -> (D x, y)) (readsPrec n s)
instance HasResolution e => Show (Decimal e) where
  show (D x)  = show x

instance HasResolution e => Num (Decimal e) where
  x@(D (MkFixed a)) * D (MkFixed b) =
    D (MkFixed (quot (a * b + div (resolution x) 2)
                     (resolution x)))

  D a + D b      = D (a + b)
  D a - D b      = D (a - b)
  negate  (D a)  = D (negate a)
  abs     (D a)  = D (abs a)
  signum  (D a)  = D (signum a)
  fromInteger i  = D (fromInteger i)

instance HasResolution e => Fractional (Decimal e) where
  x@(D (MkFixed a)) / D (MkFixed b) =
    D (MkFixed (div (a * resolution x + div b 2) b))

  recip (D a)     = D (recip a)
  fromRational r  = D (fromRational r)

data E27

instance HasResolution E27 where
  resolution _ = 10^(27 :: Integer)

epsilon = 1 / 10^27

