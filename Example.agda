module Example where

open import Sic
open Dappsys

pow =
  the "lad" may "cool" :: ⟨ 0 , u ⟩ ← 1 │ iff (0 ≡ 1) //
  the "gal" may "frob" :: iff root │ ⟨ 0 , u ⟩ ← 1 │ fyi₂ u t

simple : S² ⊥ String
simple =
  anybody may "mem" :: fyi₁ 1 //
  anybody may "str" :: fyi₁ (get 0)

hello : S² ⊥ String
hello =
  anybody may "poke()" :: 0 ← 1 //
  anybody may "frob()" :: iff (get 0) │ 1 ← 2 //
  anybody may "look()" :: fyi₂ (get 0) (get 1) //
  anybody may "feel()" :: fyi₁ (get 0) //
  anybody may "test()" :: fyi₁ 1

simple&hello = simple ⊗ hello

fyi&ext : S² ⊥ String
fyi&ext =
  anybody may "foo()" ::
      0 ≜ (ref 1)
    │ fyi₂ (get 0) (get 1)
    │ ext₂ "quit()" u (get 0) (get 1)

caller =
  the "lad" may "good()" :: ext₀ "poke()" u //
  the "bad" may "evil()" :: ext₀ "quit()" u //
  anybody may "push()" :: ext₁ "push(uint256)" u 1 //
  anybody may "punt()" :: ext₂ "punt(uint256,uint256)" u 1 2

callee =
  anybody may "gaze()" :: fyi₁ (get 0) //
  the "mom" may "poke()" :: 0 ← 1 //
  anybody may "fail()" :: iff 0

stoppable =
  let stopped = 0 ; counter = 1
  in case (get stopped)
       then anybody may "poke()" :: counter ← 1 + get counter
         // the "dad" may "stop()" :: stopped ← 1
       else anybody may "peek()" :: fyi₁ (get counter)

-- TODO: add `this` as resource, maybe as `&`

open import IO
open import Coinduction

main = run
  (♯ lift (ask "HELLO") >>=
     λ x → ♯ (♯ putStrLn x >>
              ♯ putStrLn (compile-and-assemble stoppable)))
