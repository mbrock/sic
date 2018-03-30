{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# Language TemplateHaskell #-}
{-# Language LambdaCase #-}
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
import EVM.Keccak (newContractAddress)

import Control.Lens
import Control.Monad (unless, when)
import Control.Monad.State.Class (MonadState, get, modify)
import qualified Control.Monad.State.Class as State
import Control.Monad.State.Strict (execState, runState)
import Control.Monad.IO.Class
import Data.Binary.Get (runGetOrFail)
import Data.ByteString (ByteString)
import Data.IORef
import Data.ByteString.Lazy (fromStrict)
import Data.DoubleWord
import Data.Fixed
import Data.Ratio
import Data.Text (Text, pack, unpack)
import System.Environment (getEnv)
import System.Exit (exitFailure)
import qualified Data.ByteString as BS
import qualified Data.Text as Text
import Data.Text.Encoding (encodeUtf8)
import qualified Data.Vector as Vector

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

create x = do
  resetState
  assign (state . gas) 0xffffffffffffff
  Just i <- preuse (env . contracts . ix ethrunAddress . nonce)
  let a = newContractAddress ethrunAddress (fromIntegral i)
  env . contracts . ix ethrunAddress . nonce += 1
  env . contracts . at a .= Just (initialContract x)
  loadContract a
  exec >>= \case
    VMFailure e -> error (show e)
    VMSuccess (B runtime) -> do
      replaceCodeOfSelf runtime
      return (fromIntegral a)

call src dst sig ret xs = do
  resetState
  loadContract (fromIntegral dst)
  assign (state . caller) src
  assign (state . gas) 0xffffffffffffff
  assign (state . calldata) (B (abiCalldata sig (Vector.fromList xs)))
  exec >>= \case
    VMSuccess (B out) ->
      case ret of
        Nothing -> pure Nothing
        Just retType ->
          case runGetOrFail (getAbi retType) (fromStrict out) of
            Right ("", _, x) -> pure (Just x)
            _ -> error ("ABI return value decoding error: " ++ unpack sig ++ " " ++ show (out))
    VMFailure problem ->
      error (show problem)

load :: VM -> IO ((Word160, Word160, Word160), VM)
load vm = do
  exampleCode <-
    hexByteString "code" <$> BS.getContents
  factoryCode <-
    hexByteString "code" . encodeUtf8 . pack <$> getEnv "TOKEN_FACTORY_CODE"
  pure . flip runState vm $ do
    example <- create exampleCode
    factory <- create factoryCode
    Just (AbiAddress dai) <- call root factory "make(bytes32,bytes32)" (Just AbiAddressType)
      [AbiBytes 32 (padRight 32 "DAI"), AbiBytes 32 (padRight 32 "Dai")]
    Just (AbiAddress mkr) <- call root factory "make(bytes32,bytes32)" (Just AbiAddressType)
      [AbiBytes 32 (padRight 32 "MKR"), AbiBytes 32 (padRight 32 "Maker")]
    return (example, dai, mkr)

-- Top-level unsafe I/O to read bytecode from stdin.
-- Forgive me; it's nice to have it globally available
-- for all the Hedgehog properties.
((example, daiToken, mkrToken), vm1) =
  unsafePerformIO (load emptyVm)

emptyVm = vmForEthrunCreation ""

-- Some ugly code to run an ABI method and decode its return value.
run :: Text -> AbiType -> [AbiValue] -> Either Error AbiValue
run sig ret args = do
  let
    continue = do
      resetState
      assign (state . gas) 0xffffffffffffff
      loadContract (fromIntegral example)
      assign (state . calldata) (B (abiCalldata sig (Vector.fromList args)))
      exec
  case runState continue vm1 of
    (VMSuccess (B out), _) ->
      case runGetOrFail (getAbi ret) (fromStrict out) of
        Right ("", _, x) -> Right x
        _ -> error "ABI return value decoding error"
    (VMFailure problem, _) ->
      Left problem

maxInt :: Integral a => a
maxInt = 2 ^ 255 - 1

minInt :: Integral a => a
minInt = - (2 ^ 255)

maxRange :: Integral a => Range a
maxRange = Range.linear 0 maxInt

anyInt :: Integral a => Gen a
anyInt = Gen.integral maxRange

ray x = x :: Ray
rayRange x = (Range.linear (unfixed (ray x)) (- (unfixed (ray x))))

-- This generates ray fixed point numbers in a variety of magnitudes,
-- to ensure good test coverage.
anyRay =
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
    x <- forAll anyInt
    y <- forAll anyInt
    case run "iadd(int256,int256)" (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
      Right (AbiInt 256 z) -> do
        z === x + y
      Left Revert -> do
        let z = integer x + integer y
        annotate (show z)
        assert (z > maxInt || z <= minInt)

unfixed :: Num a => Decimal b -> a
unfixed (D (MkFixed i)) = fromIntegral i

fixed :: Integral a => a -> Ray
fixed x = fromRational (fromIntegral (fromIntegral x :: Int256) % 10^27)

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
          else fixed z === x ^ fromIntegral n
      Left Revert -> do
        assert $
          -- x too big to multiply?
             (x > fixed maxInt / 10^27) || (x == 0 && n == 0)
          -- x^n would overflow?
          || fromIntegral n >
               (log (realToFrac (fixed maxInt)) / log (abs (realToFrac x)))
      Left e -> do
        annotate (show e)
        failure 

main :: IO ()
main = do
  good <- checkSequential $$(discover)
  unless good exitFailure

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



newtype Account = Account Word160
  deriving (Eq, Ord, Show, Num, Integral, Real, Enum)

data Gem = DAI | MKR
  deriving (Eq, Ord, Show)

gemAddress = \case
  DAI -> daiToken
  MKR -> mkrToken

data Model (v :: * -> *) = Model
  { accounts :: Set Account
  , balances :: Map (Gem, Account) Word256
  } deriving (Eq, Show)

initialState :: Model v
initialState = Model
  { accounts = Set.fromList [root]
  , balances = Map.fromList [((MKR, root), 0), ((DAI, root), 0)]
  }

data Spawn (v :: * -> *) = Spawn Account
  deriving (Eq, Show)

data Mint (v :: * -> *) = Mint Gem Account Account Word256
  deriving (Eq, Show)

instance HTraversable Spawn where
  htraverse f (Spawn x) = pure (Spawn x)

instance HTraversable Mint where
  htraverse f (Mint a b c d) = pure (Mint a b c d)

spawn :: Monad m => Command Gen m Model
spawn =
  let
    gen s = pure (Spawn . fromIntegral <$> anyInt)
    execute (Spawn x) = pure ()

  in
    Command gen execute
      [ Require $ \s (Spawn x) ->
          Set.notMember x (accounts s)
      , Update $ \s (Spawn x) _ ->
          s { accounts = Set.insert x (accounts s)
            , balances = Map.union (balances s) (Map.fromList [((DAI, x), 0), ((MKR, x), 0)])
            }
      ]

root :: Integral a => a
root = fromIntegral ethrunAddress

mint1 :: IORef VM -> Command Gen (PropertyT IO) Model
mint1 ref =
  let
    gen s =
      if Set.null (accounts s)
      then Nothing
      else Just $ do
        gem <- Gen.element [DAI, MKR]
        dst <- Gen.element (Set.toList (accounts s))
        wad <- anyInt
        pure (Mint gem root dst wad)
      
    execute (Mint gem src dst wad) = do
      vm <- liftIO (readIORef ref)
      let vm' = execState (call (fromIntegral src) (gemAddress gem) "mint(address,uint256)" Nothing [AbiAddress (fromIntegral dst), AbiUInt 256 wad]) vm
      liftIO (writeIORef ref vm')
      pure vm'

  in
    Command gen execute
      [ Update $ \s (Mint gem src dst wad) _ ->
          if addOverflow (balances s Map.! (gem, dst)) wad
          then s
          else
            s { balances =
                  Map.adjust (+ wad) (gem, dst) (balances s) }
      -- , Ensure $ \s s' (Mint gem src dst wad) vm ->
      --     if addOverflow (balances s Map.! (gem, dst)) wad
      --     then
      --       case view result vm of
      --         Just (VMFailure Revert) -> pure ()
      --         _ -> failure
      --     else
      --       case view result vm of
      --         Just (VMSuccess "") -> pure ()
      --         _ -> failure
      ]

addOverflow :: Word256 -> Word256 -> Bool
addOverflow x y = x + y < x

prop_spawn = property $ do
  acts <-
    forAll $ Gen.sequential (Range.linear 0 100) initialState
      [ spawn ]
  executeSequential initialState acts

prop_mint1 = property $ do
  ref <- liftIO (newIORef vm1)
  acts <-
    forAll $ Gen.sequential (Range.linear 0 100) initialState
      [ spawn, mint1 ref ]
  executeSequential initialState acts
  
