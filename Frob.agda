module Frob where

open import Sic
open Dappsys

data Guy : Set where
  gov rat bat : Guy

data Act : Set where
  mold cage poke frob : Act

frobcore : S² Guy Act easy
frobcore =
  let
    -- &⬙   = 0
    -- ΣΣ⬙$ = 1
    -- ΣΣ○$ = 2
    χ  = λ ι → ⟨ 0 , ι ⟩
    ρ  = λ ι → ⟨ 1 , ι ⟩
    Ψ  = λ ι → ⟨ 2 , ι ⟩
    Σ◇ = λ ι → ⟨ 3 , ι ⟩
  in
       anybody can frob :: ⟨ u ⟩ ← arg 0
    // the gov can mold :: χ (arg 0) ← arg 1
