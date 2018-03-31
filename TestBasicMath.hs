{-# Language OverloadedStrings #-}

module TestBasicMath where

import TestBase
import TestLoad

import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

prop_iadd :: Property
prop_iadd =
  withTests 100 . property $ do
    x <- forAll anyInt
    y <- forAll anyInt
    case run "iadd(int256,int256)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Right (AbiInt 256 z) -> do
        z === x + y
      Left Revert -> do
        let z = integer x + integer y
        annotate (show z)
        assert (z > maxInt || z <= minInt)

prop_imul :: Property
prop_imul =
  withTests 100 . property $ do
    x <- forAll anyInt
    annotate (show x)
    y <- forAll anyInt
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
    x <- unfixed <$> forAll anyRay
    annotate (show (fixed x))
    y <- unfixed <$> forAll anyRay
    annotate (show (fixed y))
    case run "rmul(int256,int256)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Right (AbiInt 256 z) -> do
        annotate (show (fixed z))
        annotate (show (abs (fixed z - fixed x * fixed y)))

        -- Note that our Haskell fixed points don't overflow,
        -- so this tests that the result is actually correct.
        fixed z === fixed x * fixed y

      Left Revert -> do
        -- Verify the failure mode: overflow or underflow.
        if signum x * signum y > 0
          then assert (integer x * integer y + (10^27 `div` 2) > maxInt)
          else assert (integer x * integer y + (10^27 `div` 2) < minInt)

      Left e -> do
        annotate (show e)
        failure

prop_rpow :: Property
prop_rpow =
  withTests 100 . withShrinks 1 . property $ do
    x <- forAll anyRay
    n <- forAll (Gen.filter (> 0) anyInt)
    case run "rpow(int256,int256)" (AbiIntType 256) [AbiInt 256 (unfixed x), AbiInt 256 n] of
      Right (AbiInt 256 z) -> do
        if n == 0
          then do
            assert (not (x == 0))
            fixed z === 1.0
          else fixed z === x ^ cast n
      Left Revert -> do
        assert $
          -- x too big to multiply?
             (x > fixed maxInt / 10^27) || (x == 0 && n == 0)
          -- x^n would overflow?
          || cast n >
               (log (realToFrac (fixed maxInt)) / log (abs (realToFrac x)))
      Left e -> do
        annotate (show e)
        failure
