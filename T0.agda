module T0 where

open import Sic
open Dappsys

data ⊥ : Set where
data Math : Set where
  IADD ISUB IMUL RMUL RPOW : Math

T⁰ : S² ⊥ Math
T⁰ = ¶ IADD 2 (λ x y → fyi₁ (x + y))
   & ¶ ISUB 2 (λ x y → fyi₁ (x − y))
   & ¶ IMUL 2 (λ x y → fyi₁ (x × y))
   & ¶ RMUL 2 (λ x y → fyi₁ (x ∙ y))
   & ¶ RPOW 2 (λ x y → fyi₁ (x ^ y))

main = link T⁰ (λ ())
  (λ { IADD → "iadd(int256,int256)"
     ; ISUB → "isub(int256,int256)"
     ; IMUL → "imul(int256,int256)"
     ; RMUL → "rmul(int256,int256)"
     ; RPOW → "rpow(int256,int256)"
     })
