module Example where

open import Sic
open Dappsys
open Solidity

pow =
  act "cool" :: ⟨ # 0 , u ⟩ ← # 1 │ iff (# 0 ≡ # 1) //
  act "frob" :: ⟨ # 0 , u ⟩ ← # 1 │ fyi₂ u t
