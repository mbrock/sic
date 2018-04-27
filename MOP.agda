module MOP where

open import Sic

mop =
  CALLER ⟫ PUSH 1 ⟫ SSTORE ⟫
  PUSH 13 ⟫ CODESIZE ⟫ SUB ⟫ DUP 1 ⟫
  PUSH 13 ⟫ PUSH 0 ⟫ CODECOPY ⟫ PUSH 0 ⟫ RETURN
