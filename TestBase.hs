{-# Language OverloadedStrings #-}
{-# Language GeneralizedNewtypeDeriving #-}

module TestBase (module TestBase, module X) where

import Data.Fixed as X
import Control.Lens as X hiding (below, Indexed)
import Control.Monad as X (unless, when, void)
import Control.Monad.IO.Class as X
import Control.Monad.State.Class as X (MonadState, get, modify)
import Control.Monad.State.Strict as X (execState, runState)
import Data.Monoid as X
import Data.Binary.Get as X (runGetOrFail)
import Data.ByteString as X (ByteString)
import Data.ByteString.Lazy as X (fromStrict)
import Data.DoubleWord as X
import Data.IORef as X
import Data.Map as X (Map, (!))
import Data.Ratio as X
import Data.Set as X (Set)
import Data.String as X (fromString)
import Data.Text as X (Text, pack, unpack)
import Data.Text.Encoding as X (encodeUtf8)
import EVM as X
import EVM.ABI as X
import EVM.Concrete as X (Blob (B))
import EVM.Dev as X (loadDappInfo)
import EVM.Exec as X
import EVM.Keccak as X (newContractAddress)
import EVM.TTY as X hiding (interpret, Returned, runFromVM, main)
import EVM.Types as X
import EVM.UnitTest as X hiding (interpret, setupCall)
import Hedgehog as X
import System.Environment as X (getEnv)
import System.Exit as X (exitFailure)
import System.IO.Unsafe as X

import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

performIO = unsafePerformIO

root :: Integral a => a
root = cast ethrunAddress

cast :: (Integral a, Num b) => a -> b
cast = fromIntegral

maxInt :: Integral a => a
maxInt = 2 ^ 255 - 1

maxWord :: Integral a => a
maxWord = 2 ^ 256 - 1

minInt :: Integral a => a
minInt = - (2 ^ 255)

maxRange :: Integral a => Range a
maxRange = Range.linear 0 maxInt

anyInt :: Integral a => Gen a
anyInt = Gen.frequency
  [ (1, pure 0)
  , (1, pure 1)
  , (1, pure (-1))
  , (1, pure maxInt)
  , (1, pure minInt)
  , (3, Gen.integral (Range.exponential 0 maxInt))
  , (3, Gen.integral (Range.exponential 0 minInt))
  ]

ray x = x :: Ray

someBelow 0 = error "too big"
someBelow x = Range.linear 0 (x - 1)

someAbove x | x == maxBound = error "too big"
someAbove x = Range.linear (x + 1) maxBound

someUpTo x = Gen.integral (Range.linear 0 x)

someGreaterThan x | x == maxBound = error "too big"
someGreaterThan x = Gen.integral (Range.linear (x + 1) maxBound)

addOverflow :: Word256 -> Word256 -> Bool
addOverflow x y = x + y < x

unfixed :: Num a => Decimal b -> a
unfixed (D (MkFixed i)) = cast i

fixed :: Integral a => a -> Ray
fixed x = fromRational (cast (cast x :: Int256) % 10^27)

anyRay :: Gen Ray
anyRay = Gen.frequency
  [ (1, fixed <$> anyInt)
  , (1, fixed <$> Gen.integral (Range.linear (10^27) (10^30)))
  ]

integer :: Integral a => a -> Integer
integer x = cast x

ensureRevert :: Show (c Concrete) => Callback a (VM, t) c
ensureRevert =
  Ensure $ \_ i _ (vm, _) -> do
    case view result vm of
      Just (VMFailure Revert) -> pure ()
      _ -> annotate (show i) >> failure

ensureVoidSuccess :: Callback a (VM, t) c
ensureVoidSuccess =
  Ensure $ \_ _ _ (vm, _) -> do
    case view result vm of
      Just (VMSuccess (B "")) -> pure ()
      _ -> failure

ensureSuccess :: AbiValue -> Callback a (VM, Maybe AbiValue) c
ensureSuccess x =
  Ensure $ \_ _ _ (vm, _) -> do
    case view result vm of
      Just (VMSuccess (B out)) -> do
        case runGetOrFail (getAbi (abiValueType x)) (fromStrict out) of
          Right ("", _, x) -> pure ()
          _ -> error ("return value decoding error")
      _ -> failure

-- Fixed point number support

newtype Decimal e = D (Fixed e)
  deriving (Ord, Eq, Real, RealFrac)

data E27
instance HasResolution E27 where
  resolution _ = 10^(27 :: Integer)

type Ray = Decimal E27

instance HasResolution e => Read (Decimal e) where
  readsPrec n s = fmap (\(x, y) -> (D x, y)) (readsPrec n s)
instance HasResolution e => Show (Decimal e) where
  show (D x)  = show x

instance HasResolution e => Num (Decimal e) where
  x@(D (MkFixed a)) * D (MkFixed b) =
    -- Using quot here instead of div is necessary for compatibility
    -- with the EVM's SDIV opcode, which negatives towards zero.
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

{-# NOINLINE testCount #-}
testCount :: TestLimit
testCount = cast (read (performIO (getEnv "count")))
