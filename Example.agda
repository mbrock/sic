module Example where

open import Sic
open Dappsys

pow =
  the "lad" may "cool" :: ⟨ 0 , u ⟩ ← 1 │ iff (0 ≡ 1) //
  the "gal" may "frob" :: iff root │ ⟨ 0 , u ⟩ ← 1 │ fyi₂ u t

simple : S² ⊥ String easy
simple =
  anybody may "mem" :: fyi₁ 1 //
  anybody may "str" :: fyi₁ (get 0)

hello : S² ⊥ String easy
hello =
  anybody may "poke()" :: 0 ← 1 //
  anybody may "frob()" :: iff (get 0) │ 1 ← 2 //
  anybody may "look()" :: fyi₂ (get 0) (get 1) //
  anybody may "feel()" :: fyi₁ (get 0) //
  anybody may "test()" :: fyi₁ 1

simple&hello = simple ⊗ hello

fyi&ext : S² ⊥ String hard
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


------------------------------------------------------------------------

data Guy : Set where dad pal : Guy
data Act : Set where peek! poke! shut! open! : Act

counter =
  let
    p = 0 ; i = 1
  in
    case get p
      then the dad may open! :: p ← 0 //
           anybody may peek! :: fyi₁ (get i)
      else the dad may shut! :: p ← 1 //
           the pal may poke! :: i ← 1 + get i

counter-main =
  link counter
    with-guys
      (λ { dad → parameter "DAD_ADDRESS"
         ; pal → parameter "PAL_ADDRESS" })
    with-acts
      (λ { peek! → "peek()"
         ; poke! → "poke()"
         ; shut! → "shut()"
         ; open! → "open()" })

-----

data MathAct : Set where
  add! sub! mul! pow! : MathAct

main =
  link
    anybody may add! :: fyi₁ (x₁ + x₂) //
    anybody may sub! :: fyi₁ (x₁ − x₂) //
    anybody may mul! :: fyi₁ (x₁ ∙ x₂) //
    anybody may pow! :: fyi₁ (x₁ ^ x₂)
  with-guys (λ z → z)
  with-acts λ { add! → "add(int128,int128)"
              ; sub! → "sub(int128,int128)"
              ; mul! → "mul(int128,int128)"
              ; pow! → "pow(int128,int128)" }
