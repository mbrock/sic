{-# Language OverloadedStrings #-}

import TestBase
import TestLoad
import TestModel
import TestBasicMath
import TestDebug
import TestToken

main :: IO ()
main = do
  let
    check s ps = do
      good <- checkSequential $ Group s ps
      unless good exitFailure
      putStrLn ""

  check "Dependencies"
    [ ("Full test suite", prop_allCommands)
    ]
    
  -- check "Sic basic math"
  --   [ ("iadd", prop_iadd (+))
  --   , ("imul", prop_imul (*))
  --   , ("rmul", prop_rmul (*))
  --   , ("rpow", prop_rpow (^) rpowMaxResult)
  --   ]

do_math x y name =
  case run (name <> "(int256,int256)") (AbiIntType 256) [AbiInt 256 x, AbiInt 256 y] of
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
