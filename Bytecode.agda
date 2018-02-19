open import Data.Nat
open import SIC11 using (module Oᴱ; sig; S²; S²→Oᴱ)
open import Data.Product
open import Agda.Builtin.String

open Oᴱ

data Opcode : ℕ → Set where
  B1   : ℕ      → Opcode 1
  B2   : ℕ      → Opcode 2
  BSig : String → Opcode 4

data Bytes : ℕ → Set where
  op_ : ∀ {m} → Opcode m → Bytes m
  Δ   : ℕ     → Bytes 2
  _⦂_ : ∀ {m n} → Bytes m → Bytes n → Bytes (m + n)

size : ∀ {m} → Bytes m → ℕ
size {m} _ = m

data Opcode⋆ : Set where
  _⟩_ : ∀ {m} → Opcode m → Opcode⋆ → Opcode⋆
  fin : Opcode⋆

infixr 1 _⟩_

append : Opcode⋆ → Opcode⋆ → Opcode⋆
append (x ⟩ o₁) o₂ = x ⟩ append o₁ o₂
append fin o₂ = o₂

⋆ : ∀ {n} → ℕ → Bytes n → Opcode⋆
⋆ i (op x) = x ⟩ fin
⋆ i (Δ x) = B2 i ⟩ fin
⋆ i (b₁ ⦂ b₂) = append (⋆ i b₁) (⋆ (i + size b₁) b₂)

infixr 10 _⦂_

code : Oᴱ → Σ ℕ Bytes
code (fyi o¹ oᴱ) = code oᴱ
code (x₁ ⟫ x₂) with code x₁
code (x₁ ⟫ x₂) | (i , x₁ᴱ) with code x₂
code (x₁ ⟫ x₂) | (i , x₁ᴱ) | (j , x₂ᴱ) = , (x₁ᴱ ⦂ x₂ᴱ)
code ADD = , op B1 0x01
code ADDRESS = , op B1 0x30
code AND = , op B1 0x16
code CALLDATALOAD = , op B1 0x35
code CALLER = , op B1 0x33
code EQ = , op B1 0x14
code JUMPDEST = , op B1 0x5b
code (JUMP x)  = , op B1 0x61 ⦂ op B2 x ⦂ op B1 0x56
code (JUMPI x) = , op B1 0x61 ⦂ op B2 x ⦂ op B1 0x57
code (ΔJUMPI x) with code x
code (ΔJUMPI x) | i , bs = , op B1 0x61 ⦂ Δ i ⦂ bs
code KECCAK256 = , op B1 0x20
code MLOAD = , op B1 0x51
code MSTORE = , op B1 0x52
code MUL = , op B1 0x02
code EXP = , op B1 0x0a
code OR = , op B1 0x17
code (PUSH x) = , op B1 0x60 ⦂ op B1 x
code (PUSHSIG (sig x _ _)) = , op BSig x
code DIV = , op B1 0x04
code SDIV = , op B1 0x05
code SGT = , op B1 0x13
code SLOAD = , op B1 0x54
code SLT = , op B1 0x12
code NOT = , op B1 0x19
code ISZERO = , op B1 0x15
code SSTORE = , op B1 0x55
code STOP = , op B1 0x00
code SUB = , op B1 0x03
code TIMESTAMP = , op B1 0x42
code (DUP x) = , op B1 (0x7f + x)
code (SWAP x) = , op B1 (0x8f + x)
code REVERT = , op B1 0xfd
code REVERTIF = , op B1 0x60 ⦂ op B1 0x03 ⦂ op B1 0x57
code RETURN = , op B1 0xf3

compile : S² → Opcode⋆
compile s² with code (S²→Oᴱ s²)
... | _ , b = ⋆ 0 b
