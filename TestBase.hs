{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language GeneralizedNewtypeDeriving #-}

module TestBase (module TestBase, module X) where

import Data.Fixed as X
import Data.Typeable as X (Typeable)
import Control.Lens as X hiding (below, Indexed)
import Control.Monad as X
import Control.Monad.IO.Class as X
import Control.Monad.State.Class as X (MonadState, get, modify)
import Control.Monad.State.Strict as X (execState, evalState, runState)
import Data.Foldable as X (Foldable, toList, find)
import Data.Maybe as X
import Data.Semigroup as X
import Data.Monoid as X (mempty)
import Control.Applicative as X (liftA2)
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
import Data.Vector as X (Vector)
import EVM as X hiding (next)
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

empty :: Foldable t => t a -> Bool
empty = null . toList








data X
  = XMega !Int | XMax
  | XRange !X !X
  | XSum !X !X | XProduct !X !X | XNegate !X
  | XSqrt !X
  | XConst !Integer
  deriving (Eq, Show)

rangeX :: MonadGen m => X -> m Integer
rangeX x =
  case x of
    XConst i -> pure i
    XMega n -> rangeX (reduce x)
    XMax -> rangeX (reduce x)
    XRange a b ->
      (Range.linear <$> rangeX a <*> rangeX b) >>= Gen.integral_
    XSum a b ->
      liftM2 (+) (rangeX a) (rangeX b)
    XProduct a b ->
      (`div` 10^27) <$> liftM2 (*) (rangeX a) (rangeX b)
    XNegate a ->
      liftM negate (rangeX a)
    XSqrt a ->
      fixedSqrt <$> rangeX a

fixedSqrt :: Integer -> Integer
fixedSqrt = unfixed . f . fixed
  where f :: Ray -> Ray
        f = realToFrac . sqrt . realToFrac

px :: X -> Text
px = \case
  XConst i -> pack (show i)
  XMega n -> "10^(9*" <> pack (show n) <> ")"
  XMax -> "2^255-1"
  XRange a b -> "(" <> px a <> ".." <> px b <> ")"
  XSum a b -> "(" <> px a <> " + " <> px b <> ")"
  XProduct a b -> "(" <> px a <> " * " <> px b <> ")"
  XNegate a -> "-(" <> px a <> ")"
  XSqrt a -> "sqrt(" <> px a <> ")"

reduce :: X -> X
reduce = \case
  XConst i -> XConst i
  XMega n -> XConst (10 ^ (9 * n))
  XMax -> XConst (2^255 - 1)
  XSum a b ->
    case (reduce a, reduce b) of
      (XConst a', XConst b') -> XConst (a' + b')
      (a', b') -> XSum a' b'
  XProduct a b ->
    case (reduce a, reduce b) of
      (XConst a', XConst b') -> XConst (a' * b')
      (a', b') -> XProduct a' b'
  XNegate a ->
    case reduce a of
      XConst a' -> XConst (-a')
      a' -> a'
  XRange a b ->
    XRange (reduce a) (reduce b)

isRange (XRange _ _) = True
isRange _ = False

foo = do
  x <- Gen.sample (Gen.resize 100 genX)
  putStrLn (unpack (px x))
  y <- Gen.sample (Gen.resize 100 (rangeX x))
  print (fixed y)

recursive :: MonadGen m => ([(Int, m a)] -> m a) -> [(Int, m a)] -> [(Int, m a)] -> m a
recursive f nonrec rec =
  Gen.sized $ \n ->
    if n <= 1 then
      f nonrec
    else
      f $ nonrec ++ fmap (\(i, x) -> (i, Gen.small x)) rec

genX :: MonadGen m => m X
genX = recursive Gen.frequency simple complex
  where
    simple =
      [ (1, pure (XConst 0))
      , (3, pure (XConst 1))
      , (5, pure (XConst 10))
      , (5, pure (XConst (10^27)))
      , (1, pure XMax)
      , (5, XMega <$> Gen.integral_ (Range.linear 1 5))
      ]
    complex =
      [ (2, Gen.subterm2 genX genX XSum)
      , (2, Gen.subterm2 genX genX XProduct)
      , (4, Gen.subterm2 genX genX XRange)
      , (2, Gen.subterm       genX XNegate)
      , (2, Gen.subterm       genX XSqrt)
      ]

anyInt :: Integral a => Gen a
anyInt = fromIntegral <$> (genX >>= rangeX)

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
anyRay = fixed <$> anyInt

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
    -- with the EVM's SDIV opcode, which rounds negatives towards zero.
    D (MkFixed (quot (a * b + div (resolution x) 2 * signum (a * b))
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



rayMultiplicationSafe :: Integral a => Ray -> a -> Bool
rayMultiplicationSafe r x =
  ((unfixed r * cast x) :: Integer) + (10^27 `div` 2) < maxWord
