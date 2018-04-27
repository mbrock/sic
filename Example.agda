module Example where

open import Sic
open Dappsys

multi-owner =
  CALLER ⟫ PUSH 1 ⟫ SSTORE ⟫
  PUSH 13 ⟫ CODESIZE ⟫ SUB ⟫ DUP 1 ⟫
  PUSH 13 ⟫ PUSH 0 ⟫ CODECOPY ⟫ PUSH 0 ⟫ RETURN

data Math : Set where
  IADD ISUB IMUL RMUL RPOW : Math

data X : Set where ⊤ : X

main =
  link
    ( ¶ IADD ⊤ 2 (λ x y → fyi₁ (x + y))
    & ¶ ISUB ⊤ 2 (λ x y → fyi₁ (x − y))
    & ¶ IMUL ⊤ 2 (λ x y → fyi₁ (x × y))
    & ¶ RMUL ⊤ 2 (λ x y → fyi₁ (x ∙ y))
    & ¶ RPOW ⊤ 2 (λ x y → fyi₁ (x ^ y)))
  (λ { ⊤ → anybody })
  (λ { IADD → "iadd(int256,int256)"
     ; ISUB → "isub(int256,int256)"
     ; IMUL → "imul(int256,int256)"
     ; RMUL → "rmul(int256,int256)"
     ; RPOW → "rpow(int256,int256)"
     })
