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

multi-owner =
  CALLER ⟫ PUSH 1 ⟫ SSTORE ⟫
  PUSH 13 ⟫ CODESIZE ⟫ SUB ⟫ DUP 1 ⟫
  PUSH 13 ⟫ PUSH 0 ⟫ CODECOPY ⟫ PUSH 0 ⟫ RETURN

counter-main =
  link counter
    with-guys
      (λ { dad → parameter "DAD"
         ; pal → parameter "PAL" })
    with-acts
      (λ { peek! → "peek()"
         ; poke! → "poke()"
         ; shut! → "shut()"
         ; open! → "open()" })

-----

data MathAct : Set where
  iadd! isub! imul! rmul! rpow! : MathAct

main =
  link
    anybody can iadd! :: fyi₁ (x₁ + x₂) //
    anybody can isub! :: fyi₁ (x₁ − x₂) //
    anybody can imul! :: fyi₁ (x₁ × x₂) //
    anybody can rmul! :: fyi₁ (x₁ ∙ x₂) //
    anybody can rpow! :: fyi₁ (x₁ ^ x₂)
  with-guys (λ z → z)
  with-acts λ { iadd! → "iadd(int256,int256)"
              ; isub! → "isub(int256,int256)"
              ; imul! → "imul(int256,int256)"
              ; rmul! → "rmul(int256,int256)"
              ; rpow! → "rpow(int256,int256)" }
