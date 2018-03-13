module Example where

open import Sic
open Dappsys

pow =
  the "lad" can "cool" :: ⟨ 0 , u ⟩ ← 1 │ iff (0 ≡ 1) //
  the "gal" can "frob" :: iff root │ ⟨ 0 , u ⟩ ← 1 │ fyi₂ u t

simple : S² ⊥ String easy
simple =
  anybody can "mem" :: fyi₁ 1 //
  anybody can "str" :: fyi₁ (get 0)

hello : S² ⊥ String easy
hello =
  anybody can "poke()" :: 0 ← 1 //
  anybody can "frob()" :: iff (get 0) │ 1 ← 2 //
  anybody can "look()" :: fyi₂ (get 0) (get 1) //
  anybody can "feel()" :: fyi₁ (get 0) //
  anybody can "test()" :: fyi₁ 1

fyi&ext : S² ⊥ String hard
fyi&ext =
  anybody can "foo()" ::
      0 ≜ (ref 1)
    │ fyi₂ (get 0) (get 1)
    │ ext₂ "quit()" u (get 0) (get 1)

caller =
  the "lad" can "good()" :: ext₀ "poke()" u //
  the "bad" can "evil()" :: ext₀ "quit()" u //
  anybody can "push()" :: ext₁ "push(uint256)" u 1 //
  anybody can "punt()" :: ext₂ "punt(uint256,uint256)" u 1 2

callee =
  anybody can "gaze()" :: fyi₁ (get 0) //
  the "mom" can "poke()" :: 0 ← 1 //
  anybody can "fail()" :: iff 0


------------------------------------------------------------------------

data Guy : Set where dad pal : Guy
data Act : Set where peek! poke! shut! open! : Act

counter =
  let
    p = 0 ; i = 1
  in
    case get p
      then the dad can open! :: p ← 0 //
           anybody can peek! :: fyi₁ (get i)
      else the dad can shut! :: p ← 1 //
           the pal can poke! :: i ← 1 + get i

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
    anybody can add! :: fyi₁ (x₁ + x₂) //
    anybody can sub! :: fyi₁ (x₁ − x₂) //
    anybody can mul! :: fyi₁ (x₁ ∙ x₂) //
    anybody can pow! :: fyi₁ (x₁ ^ x₂)
  with-guys (λ z → z)
  with-acts λ { add! → "add(int128,int128)"
              ; sub! → "sub(int128,int128)"
              ; mul! → "mul(int128,int128)"
              ; pow! → "pow(int128,int128)" }
