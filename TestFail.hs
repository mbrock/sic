{-# Language OverloadedStrings #-}

module TestFail where

import TestBase
import TestLoad
import TestBasicMath

import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

main :: IO ()
main = do
  let
    check s ps = do
      good <- checkSequential $ Group s ps
      unless good exitFailure
      putStrLn ""

  check "Sic basic math"
    [ ("iadd *", prop_iadd (*))
    , ("iadd -", prop_iadd (-))
    , ("imul +", prop_imul (+))
    , ("imul -", prop_imul (-))
    , ("imul x+1", prop_imul (\x _ -> x + 1))
    , ("rmul +", prop_rmul (+))
    , ("rmul -", prop_rmul (-))
    , ("rmul x+1", prop_rmul (\x _ -> x + 1))
    , ("rpow *", prop_rpow (*))
    , ("rpow +", prop_rpow (+))
    , ("rpow ^+1", prop_rpow (\x y -> x ^ y + 1))
    ]
