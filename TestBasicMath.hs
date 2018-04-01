{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}

module TestBasicMath where

import TestBase
import TestLoad

import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Data.Vector as Vector

prop_iadd (+) =
  withTests testCount . property $ do
    x <- forAll anyInt
    y <- forAll anyInt
    case run "iadd(int256,int256)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Right (AbiInt 256 z) -> do
        integer z === integer x + integer y
      Left Revert -> do
        let z = integer x + integer y
        annotate (show z)
        assert (z > maxInt || z <= minInt)

prop_imul (*) =
  withTests testCount . property $ do
    x <- forAll anyInt
    y <- forAll anyInt
    case run "imul(int256,int256)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Right (AbiInt 256 z) -> do
        integer z === integer x * integer y
      Left Revert -> do
        assert $
          (x == minInt && y < 0) ||
          (x Prelude.* y `div` y /= x)
      Left e -> do
        annotate (show e)
        failure

prop_rmul :: (forall a. Num a => a -> a -> a) -> Property
prop_rmul (*) =
  withShrinks 10 . withTests testCount . property $ do
    x <- forAll anyRay
    y <- forAll anyRay
    case run "rmul(int256,int256)" (AbiIntType 256) [AbiInt 256 (unfixed x), AbiInt 256 (unfixed y)] of
      Right (AbiInt 256 z) -> do
        -- Note that our Haskell fixed points don't overflow,
        -- so this tests that the result is actually correct.
        fixed z === x * y

      Left Revert -> do
        -- Verify the failure mode: overflow or underflow.
        annotate (showByteStringWith0x (abiCalldata "rmul(int256,int256)" (Vector.fromList [AbiInt 256 (unfixed x), AbiInt 256 (unfixed y)])))
        let z = integer (unfixed x * unfixed y + unfixed (ray 0.5))
        if signum x * signum y > 0
          then
            assert (z > maxInt)
          else
            assert (z < minInt)

      Left e -> do
        annotate (show e)
        failure

prop_rpow (^) =
  withTests testCount . withShrinks 1 . property $ do
    x <- forAll anyRay
    n <- forAll anyInt
    case run "rpow(int256,int256)" (AbiIntType 256) [AbiInt 256 (unfixed x), AbiInt 256 n] of
      Right (AbiInt 256 z) -> do
        annotate (show (x, n, fixed z))
        if n == 0
          then do
            assert (not (x == 0))
            fixed z === 1.0
          else do
            assert $ (x == 0 && z == 0) ||
              fixed z == 1 * (x ^ cast n)
      Left Revert -> do
        annotate (show (x, n))
        assert $ or
          [ x == 0 && n == 0
          , n < 0
          , unfixed x Prelude.^ 2 > (maxInt :: Integer)
          , cast n > (log (realToFrac (fixed maxInt)) / log (abs (realToFrac x)))
          ]
      Left e -> do
        annotate (show e)
        failure
