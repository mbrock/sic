module Example where

open import Sic
open Dappsys
open Solidity

pow =
  act "cool" :: ⟨ 0 , u ⟩ ← 1 │ iff (0 ≡ 1) //
  act "frob" :: iff root │ ⟨ 0 , u ⟩ ← 1 │ fyi₂ u t

simple =
  act "mem" :: fyi₁ 1 //
  act "str" :: fyi₁ (get 0)

hello =
  act "poke" :: 0 ← 1 //
  act "frob" :: iff (get 0) │ 1 ← 2 //
  act "look" :: fyi₂ (get 0) (get 1) //
  act "feel" :: fyi₁ (get 0) //
  act "test" :: fyi₁ 1

fyi&ext =
  act "foo" :: 0 ≜ (ref 1) │ fyi₂ (get 0) (get 1) │ ext₂ "quit" u (get 0) (get 1)

caller =
  act "good" :: ext₀ "poke" u //
  act "evil" :: ext₀ "quit" u

callee =
  act "gaze" :: fyi₁ (get 0) //
  act "poke" :: 0 ← 1 //
  act "fail" :: iff 0

-- TODO: test `caller` with ds-test
-- TODO: add `this` as resource, maybe as `&`
