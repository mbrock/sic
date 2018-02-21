module Example where

open import Sic
open Dappsys

pow =
  act "cool" :: ⟨ 0 , u ⟩ ← 1 │ iff (0 ≡ 1) //
  act "frob" :: iff root │ ⟨ 0 , u ⟩ ← 1 │ fyi₂ u t
