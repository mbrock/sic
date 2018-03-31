{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# Language TemplateHaskell #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language ScopedTypeVariables #-}

import           Control.Lens hiding (below)
import           Control.Monad (unless, when, void)
import           Control.Monad.Catch
import           Control.Monad.IO.Class
import           Control.Monad.State.Class (MonadState, get, modify)
import qualified Control.Monad.State.Class as State
import           Control.Monad.State.Strict (execState, runState)
import           Data.Binary.Get (runGetOrFail)
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import           Data.ByteString.Lazy (fromStrict)
import           Data.DoubleWord
import           Data.Fixed
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Ratio
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text, pack, unpack)
import qualified Data.Text as Text
import           Data.Text.Encoding (encodeUtf8)
import qualified Data.Vector as Vector
import           EVM
import           EVM.TTY hiding (StepOutcome (..), main, runFromVM)
import qualified Brick
import qualified EVM.TTY
import qualified EVM.Fetch as Fetch
import qualified EVM.Stepper as Stepper
import           EVM.Dev (loadDappInfo)
import           EVM.ABI
import           EVM.Concrete (Blob (B))
import           EVM.Exec
import           EVM.Keccak (newContractAddress)
import           EVM.Types
import           EVM.UnitTest hiding (setupCall)
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           System.Environment (getEnv)
import           System.Exit (exitFailure)
import           System.IO.Unsafe

main :: IO ()
main = do
  good <- checkSequential $ Group "Tokens"
    [ ("token", prop_token)
    ]
  unless good exitFailure

cast :: (Integral a, Num b) => a -> b
cast = fromIntegral

-- Top-level global I/O!
{-# NOINLINE global #-}
global = unsafePerformIO (load emptyVm)

((example, gemAddress), vm1) = global

emptyVm :: VM
emptyVm = vmForEthrunCreation ""

root :: Integral a => a
root = cast ethrunAddress

data Gem = DAI | MKR
  deriving (Eq, Ord, Show, Enum)

allGems :: [Gem]
allGems = enumFrom DAI

load :: VM -> IO ((Word160, Gem -> Word160), VM)
load vm = do
  exampleCode <-
    hexByteString "code" . encodeUtf8 . pack <$> getEnv "EXAMPLE_CODE"
  factoryCode <-
    hexByteString "code" . encodeUtf8 . pack <$> getEnv "TOKEN_FACTORY_CODE"
  pure . flip runState vm $ do
    example <- create exampleCode
    factory <- create factoryCode
    Returned (AbiAddress dai) <-
      call (Call root factory "make(bytes32,bytes32)" (Just AbiAddressType)
        [AbiBytes 32 (padRight 32 "DAI"), AbiBytes 32 (padRight 32 "Dai")])
    Returned (AbiAddress mkr) <-
      call (Call root factory "make(bytes32,bytes32)" (Just AbiAddressType)
        [AbiBytes 32 (padRight 32 "MKR"), AbiBytes 32 (padRight 32 "Maker")])
    return
      ( example
      , \case DAI -> dai; MKR -> mkr
      )

create :: Num t => ByteString -> EVM t
create x = do
  resetState
  assign (state . gas) 0xffffffffffffff
  assign (state . caller) root
  Just i <- preuse (env . contracts . ix ethrunAddress . nonce)
  let a = newContractAddress ethrunAddress (cast i)
  env . contracts . ix ethrunAddress . nonce += 1
  env . contracts . at a .= Just (initialContract x)
  loadContract a
  exec >>= \case
    VMFailure e -> error (show e)
    VMSuccess (B runtime) -> do
      replaceCodeOfSelf runtime
      return (cast a)

data CallResult
  = Returned AbiValue
  | Stopped
  | Failed Error
  deriving (Show)

data Call = Call
  { callSrc :: Addr
  , callDst :: Addr
  , callSig :: Text
  , callRet :: Maybe AbiType
  , callArg :: [AbiValue]
  } deriving (Eq, Show)

setupCall :: Call -> EVM ()
setupCall (Call src dst sig ret xs) = do
  resetState
  loadContract dst
  assign (state . caller) src
  assign (state . gas) 0xffffffffffffff
  assign (state . calldata) (B (abiCalldata sig (Vector.fromList xs)))

call :: Call -> EVM CallResult
call info@(Call src dst sig ret xs) = do
  setupCall info
  exec >>= \case
    VMSuccess (B out) ->
      case ret of
        Nothing -> pure Stopped
        Just retType ->
          case runGetOrFail (getAbi retType) (fromStrict out) of
            Right ("", _, x) -> pure (Returned x)
            _ -> error ("return value decoding error in " ++ unpack sig)
    VMFailure problem ->
      pure (Failed problem)

-- Some ugly code to run an ABI method and decode its return value.
run :: Text -> AbiType -> [AbiValue] -> Either Error AbiValue
run sig ret args = do
  let
    continue = do
      resetState
      assign (state . gas) 0xffffffffffffff
      loadContract (cast example)
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

maxWord :: Integral a => a
maxWord = 2 ^ 256 - 1

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
integer x = cast x

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
unfixed (D (MkFixed i)) = cast i

fixed :: Integral a => a -> Ray
fixed x = fromRational (cast (cast x :: Int256) % 10^27)

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




------------------------------------------------------------------------
-- Smart contract model testing ----------------------------------------
------------------------------------------------------------------------

newtype Account = Account Word160
  deriving (Eq, Ord, Show, Num, Integral, Real, Enum)

data Model (v :: * -> *) = Model
  { accounts :: Set Account
  , balances :: Map (Gem, Account) Word256
  } deriving (Eq, Show)

zeroBalancesFor :: Account -> Map (Gem, Account) Word256
zeroBalancesFor x = Map.fromList [((g, x), 0) | g <- allGems]

totalSupply :: Model v -> Word256
totalSupply = sum . Map.elems . balances

balanceOf :: Gem -> Account -> Model v -> Word256
balanceOf g x s =
  case Map.lookup (g, x) (balances s) of
    Nothing -> 0
    Just n -> n

initialState :: Model v
initialState = Model
  { accounts = Set.fromList [root]
  , balances = zeroBalancesFor root
  }

performReversion vm0 vm1 =
  case view result vm1 of
    Just (VMFailure _) ->
      vm1 & env . contracts .~ view (env . contracts) vm0
    _ ->
      vm1

send ref c@(Call src dst sig _ xs) = do 
  vm <- liftIO (readIORef ref)
  let vm' = performReversion vm (execState (call c) vm)
  liftIO (writeIORef ref vm')
  pure vm'

data Spawn (v :: * -> *) =
  Spawn Account
  deriving (Eq, Show)

data Mint (v :: * -> *) =
  Mint Gem Account Account Word256
  deriving (Eq, Show)

data Transfer (v :: * -> *) =
  Transfer Gem Account Account Word256
  deriving (Eq, Show)

instance HTraversable Spawn where
  htraverse f (Spawn x) = pure (Spawn x)

instance HTraversable Mint where
  htraverse f (Mint a b c d) = pure (Mint a b c d)

instance HTraversable Transfer where
  htraverse f (Transfer a b c d) = pure (Transfer a b c d)

spawn :: Monad m => Command Gen m Model
spawn =
  Command
    (const (pure (Spawn . cast <$> anyInt)))
    (const (pure ()))
    [ Require $ \s (Spawn x) ->
        Set.notMember x (accounts s)
    , Update $ \s (Spawn x) _ ->
        s { accounts = Set.insert x (accounts s)
          , balances = Map.union (balances s) (zeroBalancesFor x)
          }
    ]

failedVm :: IORef (Maybe (VM, Text))
{-# NOINLINE failedVm #-}
failedVm = unsafePerformIO (newIORef Nothing)

failedVmStop :: IORef Bool
{-# NOINLINE failedVmStop #-}
failedVmStop = unsafePerformIO (newIORef True)

debug :: (MonadIO m, Show a) => IORef VM -> a -> Call -> m VM
debug ref cmd c = do
  vm0 <- liftIO (readIORef ref)
  vm1 <- send ref c
  case view result vm1 of
    Just (VMFailure Revert) -> do
      stop <- liftIO (readIORef failedVmStop)
      when stop $ do
        let
          vm' = flip execState vm0 $ do
            setupCall c
            pushTrace (EntryTrace (pack (show cmd)))
        liftIO (writeIORef failedVm (Just (vm', pack (show cmd))))
        liftIO (writeIORef failedVmStop False)
    _ ->
      pure ()
  pure vm1

below x = Range.linear 0 (if x == 0 then 0 else x - 1)
above x = Range.linear (if x == maxBound then maxBound else x + 1) maxBound

mintGood :: IORef VM -> Command Gen (PropertyT IO) Model
mintGood ref =
  let
    gen s =
      if Set.null (accounts s)
      then Nothing
      else Just $ do
        gem <- Gen.element [DAI, MKR]
        dst <- Gen.element (Set.toList (accounts s))
        let dstWad = balanceOf gem dst s
        wad <- Gen.integral (below (min (maxBound - totalSupply s) (maxBound - dstWad)))
        pure (Mint gem root dst wad)
      
    execute cmd@(Mint gem src dst wad) = do
      send ref $ Call
        (cast src) (cast (gemAddress gem))
        "mint(address,uint256)"
        Nothing
        [AbiAddress (cast dst), AbiUInt 256 wad]

  in
    Command gen execute
      [ Require $ \s _  -> do True
      , Update $ \s (Mint gem src dst wad) _ ->
          s { balances =
                Map.adjust (+ wad) (gem, dst) (balances s) }
      , ensureVoidSuccess
      ]

mintUnauthorized :: IORef VM -> Command Gen (PropertyT IO) Model
mintUnauthorized ref =
  let
    gen s =
      if Set.size (accounts s) < 2
      then Nothing
      else Just $ do
        gem <- Gen.element [DAI, MKR]
        src <- Gen.element (Set.toList (Set.delete root (accounts s)))
        dst <- Gen.element (Set.toList (accounts s))
        wad <- anyInt
        pure (Mint gem src dst wad)
      
    execute (Mint gem src dst wad) = do
      send ref $ Call
        (cast src) (cast (gemAddress gem))
        "mint(address,uint256)"
        Nothing
        [AbiAddress (cast dst), AbiUInt 256 wad]

  in
    Command gen execute
      [ ensureRevert
      ]

ensureRevert =
  Ensure $ \_ i _ vm -> do
    case view result vm of
      Just (VMFailure Revert) -> pure ()
      _ -> annotate (show i) >> failure

ensureVoidSuccess :: Callback i VM s
ensureVoidSuccess =
  Ensure $ \_ _ _ vm -> do
    case view result vm of
      Just (VMSuccess (B "")) -> pure ()
      _ -> failure

transferGood ref =
  let
    gen s =
      Just $ do
        gem <- Gen.element allGems
        src <- Gen.element (Set.toList (accounts s))
        dst <- Gen.element (Set.toList (accounts s))
        let srcWad = balances s Map.! (gem, src)
        let dstWad = balances s Map.! (gem, dst)
        wad <- Gen.integral (below (min srcWad (maxWord - dstWad)))
        pure (Transfer gem src dst wad)

    run cmd@(Transfer gem src dst wad) = do
      send ref $ Call
        (cast src) (cast (gemAddress gem))
        "push(address,uint256)"
        Nothing
        [AbiAddress (cast dst), AbiUInt 256 wad]

  in Command gen run
      [ Require $ \s (Transfer gem src dst wad) ->
          balanceOf gem src s >= wad
      , Update $ \s (Transfer gem src dst wad) _ ->
             s { balances =
                   Map.adjust (subtract wad) (gem, src) .
                   Map.adjust (+ wad) (gem, dst) $
                     balances s
               }
       , ensureVoidSuccess
       ]

transferOverflow ref =
  let
    gen s =
      Just $ do
        gem <- Gen.element allGems
        src <- Gen.element (Set.toList (accounts s))
        dst <- Gen.element (Set.toList (accounts s))
        let srcWad = balances s Map.! (gem, src)
        let dstWad = balances s Map.! (gem, dst)
        wad <- 
          Gen.integral
            (above (max srcWad (maxWord - dstWad)))
        pure (Transfer gem src dst wad)

    run cmd@(Transfer gem src dst wad) = do
      send ref $
        Call (cast src) (cast (gemAddress gem))
          "push(address,uint256)"
          Nothing
          [AbiAddress (cast dst), AbiUInt 256 wad]

  in Command gen run
       [ 
         ensureRevert
       ]

addOverflow :: Word256 -> Word256 -> Bool
addOverflow x y = x + y < x

supply gem s =
  sum [x | ((g, _), x) <- Map.assocs (balances s), g == gem]

prop_token = withShrinks 0 . withTests 500 . property $ do
  ref <- liftIO (newIORef vm1)
  acts <-
    forAll $ Gen.sequential (Range.linear 0 10) initialState
      [ spawn
      , mintGood ref
      , mintUnauthorized ref
      , transferGood ref
      , transferOverflow ref
      ]
  executeSequential initialState acts
  liftIO (writeIORef ref vm1)
  liftIO (readIORef failedVm) >>=
    \case
      Nothing -> pure ()
      Just (vm', msg) -> liftIO $ do
        void (runFromVM vm' msg)
        writeIORef failedVm Nothing
       
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
