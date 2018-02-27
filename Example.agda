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


------------------------------------------------------------------------

data Guy : Set where
  dad : Guy

data Act : Set where
  peek! poke! shut! open! : Act

sig : Act → String
sig peek! = "peek()"
sig poke! = "poke()"
sig shut! = "shut()"
sig open! = "open()"

pausable-counter =
  let p = 0 ; i = 1
  in case get p
     then
       the dad may open! :: p ← 0 //
       anybody may peek! :: fyi₁ (get i)
     else
       the dad may shut! :: p ← 1 //
       anybody may poke! :: i ← 1 + get i

------------------------------------------------------------------------

open Naturals
open Vectors
open Lists
open EVM

open import IO
open import Coinduction
open import Data.Maybe

fixed-width : (A : Set) → (n : ℕ) → List A → Maybe (Vec A n)
fixed-width _ ℕ.zero [] = just []ᵛ
fixed-width _ ℕ.zero (x ∷ xs) = nothing
fixed-width _ (suc n) [] = nothing
fixed-width A (suc n) (x ∷ xs) with fixed-width A n xs
... | nothing = nothing
... | just xs′ = just (x ∷ᵛ xs′)

addr : String → Maybe Addrᴱ
addr s = fixed-width Char 20 (Data.String.toList s)
  where import Data.String

compile-it : Maybe (Vec Char 20) → IO ⊤
compile-it nothing = IO.return ⊤.tt
compile-it (just a) =
  putStrLn (compile-and-assemble (λ { dad → a }) sig pausable-counter)

main = run
  (♯ lift (ask "DAD_ADDRESS") >>=
     λ x → ♯ compile-it (addr x))
