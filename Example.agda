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
  act "poke()" :: 0 ← 1 //
  act "frob()" :: iff (get 0) │ 1 ← 2 //
  act "look()" :: fyi₂ (get 0) (get 1) //
  act "feel()" :: fyi₁ (get 0) //
  act "test()" :: fyi₁ 1

simple&hello = simple ⊗ hello

fyi&ext =
  act "foo()" ::
      0 ≜ (ref 1)
    │ fyi₂ (get 0) (get 1)
    │ ext₂ "quit()" u (get 0) (get 1)

caller =
  act "good()" :: ext₀ "poke()" u //
  act "evil()" :: ext₀ "quit()" u //
  act "push()" :: ext₁ "push(uint256)" u 1 //
  act "punt()" :: ext₂ "punt(uint256,uint256)" u 1 2

callee =
  act "gaze()" :: fyi₁ (get 0) //
  act "poke()" :: 0 ← 1 //
  act "fail()" :: iff 0

stoppable =
  let stopped = 0 ; counter = 1
  in case (get stopped)
       then act "poke()" :: counter ← 1 + get counter
         // act "stop()" :: stopped ← 1
       else act "peek()" :: fyi₁ (get counter)

-- TODO: add `this` as resource, maybe as `&`
