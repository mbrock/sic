------------------------------------------------------------------------
-- ✿ SIC: Symbolic Instruction Code
--

module SIC12 where

open import Data.String using (String; _++_) renaming (_==_ to _string==_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Show using (showInBase)

open import Data.Bool.Base using (Bool)
open import Data.List.NonEmpty using (List⁺; [_]; foldr₁) renaming (map to map⁺; _∷_ to _∷⁺_)
open import Data.List using (List; _∷_; []; map)
open import Data.Nat using (ℕ; _⊔_; suc) renaming (_≟_ to _≟ℕ_; _+_ to _+ℕ_; _*_ to _×ℕ_)

open import Data.Integer using (ℤ; -_; +_) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_)
open import Data.Product using (Σ; ,_) renaming (_,_ to _Σ,_)

------------------------------------------------------------------------
-- ✿ Section 1
--     SIC syntax data types
--

mutual
  data S⁰ : Set where
    #  : ℕ → S⁰
    Uₐ : S⁰
    &ₐ : S⁰
    t  : S⁰

    _+_ : S⁰ → S⁰ → S⁰
    _−_ : S⁰ → S⁰ → S⁰
    _×_ : S⁰ → S⁰ → S⁰
    _^_ : S⁰ → S⁰ → S⁰
    _∨_ : S⁰ → S⁰ → S⁰
    _∧_ : S⁰ → S⁰ → S⁰
    _≥_ : S⁰ → S⁰ → S⁰
    _≤_ : S⁰ → S⁰ → S⁰
    _≡_ : S⁰ → S⁰ → S⁰

    get_  : ℕ → S⁰
    ref_  : ℕ → S⁰
    arg_  : ℕ → S⁰
    getₖ_ : ⟨S⁰⟩ → S⁰
    sha_  : ⟨S⁰⟩ → S⁰

  data ⟨S⁰⟩ : Set where
    ⟨⟩_  : S⁰ → ⟨S⁰⟩
    _,_  : S⁰ → ⟨S⁰⟩ → ⟨S⁰⟩

$ : ℕ → S⁰
$ i = arg i

⟨_ : ⟨S⁰⟩ → ⟨S⁰⟩
⟨ x = x

_⟩ : S⁰ → ⟨S⁰⟩
x ⟩ = ⟨⟩ x

data Sig : Set where
  sig : String → ℕ → ℕ → Sig

_is_ : Sig → Sig → Bool
sig s₁ x₁ y₁ is sig s₂ x₂ y₂ = s₁ string== s₂

data S¹ : Set where
  iff_    : S⁰ → S¹
  def_≜_  : ℕ → S⁰ → S¹
  set_←_  : ℕ → S⁰ → S¹
  setₖ_←_ : ⟨S⁰⟩ → S⁰ → S¹
  out_    : ⟨S⁰⟩ → S¹
  _│_     : S¹ → S¹ → S¹

data S² : Set where
  _┌_  : Sig → S¹ → S²
  _└_  : S² → S² → S²

------------------------------------------------------------------------
-- ✿ Section 2
--     SIC operator precedence and fixity
--

infixr 2 _┌_
infixr 3 _│_
infixl 1 _└_

infix  10 iff_
infix  10 def_≜_
infix  10 set_←_
infix  10 setₖ_←_

infixl 31 _∨_
infixl 32 _∧_

infixl 35 _≡_
infixl 36 _≥_

infixl 40 _+_ _−_
infixl 41 _×_

infix  50 getₖ_
infix  50 get_
infix  50 ref_
infix  50 arg_
infix  50 sha_

infixr 60 ⟨_
infixr 61 _,_
infixr 62 _⟩

------------------------------------------------------------------------
-- ✿ Section 4
--     EV²M, the "Ethereum Virtual Virtual Machine"
--

data O⁰ : ℕ → ℕ → Set where
  _┆_     : ∀ {i j k} → O⁰ i j → O⁰ j k → O⁰ i k
  #ₒ      : ∀ {i} → ℕ → O⁰ i (suc i)
  callerₒ : ∀ {i} → O⁰ i (suc i)
  calleeₒ : ∀ {i} → O⁰ i (suc i)
  timeₒ   : ∀ {i} → O⁰ i (suc i)
  getₖₒ   : ∀ {i} → O⁰ (suc i) (suc i)
  H¹ₒ     : ∀ {i} → O⁰ (suc i) (suc i)
  H²ₒ     : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  +ₒ      : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  −ₒ      : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  ×ₒ      : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  ^ₒ      : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  ≡ₒ      : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  ≥ₒ      : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  ≤ₒ      : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  ∧ₒ      : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  ∨ₒ      : ∀ {i} → O⁰ (suc (suc i)) (suc i)
  refₒ    : ∀ {i} → ℕ → O⁰ i (suc i)
  getₒ    : ∀ {i} → ℕ → O⁰ i (suc i)
  argₒ    : ∀ {i} → ℕ → O⁰ i (suc i)

data O¹ : Set where
  _∥_   : O¹ → O¹ → O¹
  iffₒ  : O⁰ 0 1 → O¹
  setₖₒ : O⁰ 0 1 → O⁰ 0 1 → O¹
  defₒ  : ℕ → O⁰ 0 1 → O¹
  setₒ  : ℕ → O⁰ 0 1 → O¹
  outₒ  : List⁺ (O⁰ 0 1) → O¹

data O² : Set where
  sigₒ : Sig → O¹ → O²
  seqₒ : O² → O² → O²

infixr  5 _┆_
infixr 10 _∥_

example-O⁰ : O⁰ 0 1
example-O⁰ = #ₒ 1 ┆ #ₒ 1 ┆ +ₒ

------------------------------------------------------------------------
-- ✿ Section 5
--     “Compilers for the Sⁿ languages to EV²M assembly”
--

mutual
  -- Compiling left-associative hashing of expression sequences
  ⟨comp⁰⟩ʰ : ∀ {i} → ⟨S⁰⟩ → O⁰ i (suc i)
  ⟨comp⁰⟩ʰ (⟨⟩ x)   = comp⁰ x ┆ H¹ₒ
  ⟨comp⁰⟩ʰ (x , xs) = comp⁰ x ┆ ⟨comp⁰⟩ʰ xs ┆ H²ₒ

  -- Compiling left-associative expression sequences
  ⟨comp⁰⟩ᵒ : ⟨S⁰⟩ → List⁺ (O⁰ 0 1)
  ⟨comp⁰⟩ᵒ x = map⁺ comp⁰ (⟨S⁰⟩→List⁺ x)

  ⟨S⁰⟩→List⁺ : ⟨S⁰⟩ → List⁺ S⁰
  ⟨S⁰⟩→List⁺ (⟨⟩ x)    = [ x ]
  ⟨S⁰⟩→List⁺ (x₁ , x₂) = x₁ ∷⁺ Data.List.NonEmpty.toList (⟨S⁰⟩→List⁺ x₂)

  -- Compiling expressions
  comp⁰ : ∀ {i} → S⁰ → O⁰ i (suc i)
  comp⁰ (# n)     = #ₒ n
  comp⁰ Uₐ        = callerₒ
  comp⁰ &ₐ        = calleeₒ
  comp⁰ (get x)   = getₒ x
  comp⁰ (ref x)   = refₒ x
  comp⁰ (arg x)   = argₒ x
  comp⁰ (getₖ k)  = ⟨comp⁰⟩ʰ k ┆ getₖₒ
  comp⁰ (sha k)   = ⟨comp⁰⟩ʰ k
  comp⁰ (x + y)   = comp⁰ x ┆ comp⁰ y ┆ +ₒ
  comp⁰ (x − y)   = comp⁰ x ┆ comp⁰ y ┆ −ₒ
  comp⁰ (x × y)   = comp⁰ x ┆ comp⁰ y ┆ ×ₒ
  comp⁰ (x ^ y)   = comp⁰ x ┆ comp⁰ y ┆ ^ₒ
  comp⁰ (x ∨ y)   = comp⁰ x ┆ comp⁰ y ┆ ∨ₒ
  comp⁰ (x ∧ y)   = comp⁰ x ┆ comp⁰ y ┆ ∧ₒ
  comp⁰ (x ≥ y)   = comp⁰ x ┆ comp⁰ y ┆ ≥ₒ
  comp⁰ (x ≤ y)   = comp⁰ x ┆ comp⁰ y ┆ ≤ₒ
  comp⁰ (x ≡ y)   = comp⁰ x ┆ comp⁰ y ┆ ≡ₒ
  comp⁰ t         = timeₒ

-- Compiling statement sequences
comp¹ : S¹ → O¹
comp¹ (iff x)      = iffₒ (comp⁰ x)
comp¹ (def i ≜ x)  = defₒ i (comp⁰ x)
comp¹ (set i ← x)  = setₒ i (comp⁰ x)
comp¹ (setₖ k ← x) = setₖₒ (comp⁰ x) (⟨comp⁰⟩ʰ k)
comp¹ (out x)      = outₒ (⟨comp⁰⟩ᵒ x)
comp¹ (x │ s)      = comp¹ x ∥ comp¹ s

-- Compiling signature dispatch sequences
comp² : S² → O²
comp² (s ┌ k) = sigₒ s (comp¹ k)
comp² (a └ b) = seqₒ (comp² a) (comp² b)


------------------------------------------------------------------------
-- ✿ Section 6
--     “Compiling EV²M to EVM assembly”
--

module Oᴱ where

  data Oᴱ : Set where
    fyi          : O¹ → Oᴱ → Oᴱ
    ADD          : Oᴱ
    ADDRESS      : Oᴱ
    AND          : Oᴱ
    CALLDATALOAD : Oᴱ
    CALLER       : Oᴱ
    DIV          : Oᴱ
    DUP          : ℕ → Oᴱ
    EQ           : Oᴱ
    EXP          : Oᴱ
    ISZERO       : Oᴱ
    JUMP         : ℕ → Oᴱ
    JUMPDEST     : Oᴱ
    JUMPI        : ℕ → Oᴱ
    KECCAK256    : Oᴱ
    LOOP         : Oᴱ → Oᴱ → Oᴱ
    MLOAD        : Oᴱ
    MOD          : Oᴱ
    MSTORE       : Oᴱ
    MUL          : Oᴱ
    NOT          : Oᴱ
    OR           : Oᴱ
    POP          : Oᴱ
    PUSH         : ℕ → Oᴱ
    PUSHSIG      : Sig → Oᴱ
    RETURN       : Oᴱ
    REVERT       : Oᴱ
    REVERTIF     : Oᴱ
    SDIV         : Oᴱ
    SGT          : Oᴱ
    SLOAD        : Oᴱ
    SLT          : Oᴱ
    SSTORE       : Oᴱ
    STOP         : Oᴱ
    SUB          : Oᴱ
    SWAP         : ℕ → Oᴱ
    THEN         : Oᴱ → Oᴱ
    TIMESTAMP    : Oᴱ
    XOR          : Oᴱ
    _⟫_          : Oᴱ → Oᴱ → Oᴱ

  infixr 10 _⟫_

open Oᴱ

prelude = JUMP 6 ⟫ JUMPDEST ⟫ REVERT ⟫ JUMPDEST

XADD = DUP 2 ⟫ DUP 2 ⟫ XOR ⟫ NOT ⟫ SWAP 2 ⟫ DUP 2 ⟫ ADD ⟫ DUP 1 ⟫ SWAP 2 ⟫
  XOR ⟫ SWAP 1 ⟫ SWAP 2 ⟫ AND ⟫ PUSH 255 ⟫ PUSH 2 ⟫ EXP ⟫ AND ⟫ REVERTIF

XMUL = DUP 2 ⟫ DUP 2 ⟫ MUL ⟫ DUP 2 ⟫ DUP 2 ⟫ DIV ⟫ SWAP 2 ⟫ SWAP 3 ⟫
  SWAP 1 ⟫ SWAP 2 ⟫ EQ ⟫ SWAP 2 ⟫ ISZERO ⟫ SWAP 1 ⟫ SWAP 2 ⟫ OR ⟫
  ISZERO ⟫ REVERTIF

RAY = PUSH 27 ⟫ PUSH 10 ⟫ EXP
RMUL = RAY ⟫ XMUL ⟫ PUSH 2 ⟫ RAY ⟫ DIV ⟫ XADD ⟫ DIV

RPOW = PUSH 2 ⟫ DUP 3 ⟫ MOD ⟫ ISZERO ⟫
  DUP 1 ⟫ RAY ⟫ MUL ⟫ SWAP 1 ⟫ ISZERO ⟫ DUP 3 ⟫ MUL ⟫ ADD ⟫
  SWAP 1 ⟫ SWAP 2 ⟫ PUSH 2 ⟫ SWAP 1 ⟫ DIV ⟫
  LOOP (DUP 1) (
    SWAP 2 ⟫ DUP 1 ⟫ RMUL ⟫ SWAP 1 ⟫ SWAP 2 ⟫ SWAP 1 ⟫ SWAP 2 ⟫
    PUSH 2 ⟫ DUP 2 ⟫ MOD ⟫ ISZERO ⟫
    THEN (SWAP 2 ⟫ SWAP 1 ⟫ DUP 2 ⟫ RMUL ⟫ SWAP 1 ⟫ SWAP 2) ⟫
    PUSH 2 ⟫ SWAP 2 ⟫ DIV
  ) ⟫ SWAP 2 ⟫ POP ⟫ POP

XEXP = PUSH 2 ⟫ DUP 3 ⟫ MOD ⟫ ISZERO ⟫
  DUP 1 ⟫ PUSH 1 ⟫ MUL ⟫ SWAP 1 ⟫ ISZERO ⟫ DUP 3 ⟫ MUL ⟫ ADD ⟫
  SWAP 1 ⟫ SWAP 2 ⟫ PUSH 2 ⟫ SWAP 1 ⟫ DIV ⟫
  LOOP (DUP 1) (
    SWAP 2 ⟫ DUP 1 ⟫ MUL ⟫ SWAP 2 ⟫
    PUSH 2 ⟫ DUP 2 ⟫ MOD ⟫ ISZERO ⟫
    THEN (SWAP 2 ⟫ SWAP 1 ⟫ DUP 2 ⟫ MUL ⟫ SWAP 1 ⟫ SWAP 2) ⟫
    PUSH 2 ⟫ SWAP 2 ⟫ DIV
  ) ⟫ SWAP 2 ⟫ POP ⟫ POP

|Oᴱ| : Oᴱ → ℕ
|Oᴱ| (x ⟫ y) = |Oᴱ| x +ℕ |Oᴱ| y
|Oᴱ| _ = 1

O⁰→Oᴱ : ∀ {i j} → O⁰ i j → Oᴱ
O⁰→Oᴱ (#ₒ n)    = PUSH n
O⁰→Oᴱ timeₒ     = TIMESTAMP
O⁰→Oᴱ (x₁ ┆ x₂) = O⁰→Oᴱ x₁ ⟫ O⁰→Oᴱ x₂
O⁰→Oᴱ (callerₒ) = CALLER
O⁰→Oᴱ (calleeₒ) = ADDRESS
O⁰→Oᴱ (refₒ x)  = PUSH (x +ℕ 64) ⟫ MLOAD
O⁰→Oᴱ (getₒ x)  = PUSH x ⟫ SLOAD
O⁰→Oᴱ (argₒ x)  = PUSH (x ×ℕ 32) ⟫ CALLDATALOAD
O⁰→Oᴱ (getₖₒ)   = SLOAD
O⁰→Oᴱ (H¹ₒ)     = PUSH 0  ⟫ MSTORE ⟫
                  PUSH 32 ⟫ PUSH 0 ⟫ KECCAK256
O⁰→Oᴱ (+ₒ)      = XADD
O⁰→Oᴱ (−ₒ)      = PUSH 0 ⟫ SUB ⟫ XADD
O⁰→Oᴱ (×ₒ)      = MUL
O⁰→Oᴱ  ^ₒ       = EXP
O⁰→Oᴱ (≡ₒ)      = EQ
O⁰→Oᴱ (≥ₒ)      = SGT ⟫ ISZERO
O⁰→Oᴱ (≤ₒ)      = SLT ⟫ ISZERO
O⁰→Oᴱ (∧ₒ)      = AND
O⁰→Oᴱ (∨ₒ)      = OR
O⁰→Oᴱ (H²ₒ)     = PUSH 0  ⟫ MSTORE ⟫
                  PUSH 32 ⟫ MSTORE ⟫
                  PUSH 64 ⟫ PUSH 0 ⟫ KECCAK256

record Index a : Set where
  constructor _at_
  field
    thing : a
    index : ℕ

index : ∀ {t} → ℕ → List t → List (Index t)
index i [] = []
index i (x ∷ xs) = x at i ∷ index (suc i) xs

index⁺ : ∀ {t} → ℕ → List⁺ t → List⁺ (Index t)
index⁺ i (x ∷⁺ []) = [ x at i ]
index⁺ i (x ∷⁺ xs) = x at i ∷⁺ index (suc i) xs

O⁰#→Oᴱ : Index (O⁰ 0 1) → Oᴱ
O⁰#→Oᴱ (x at i) = O⁰→Oᴱ x ⟫ PUSH i ⟫ MSTORE

outₒ→Oᴱ : ℕ → List⁺ (O⁰ 0 1) → Oᴱ
outₒ→Oᴱ i xs = foldr₁ _⟫_ (map⁺ O⁰#→Oᴱ (index⁺ i xs))

mutual
  O¹→Oᴱ′ : O¹ → Oᴱ
  O¹→Oᴱ′ (iffₒ o)     = O⁰→Oᴱ o ⟫ ISZERO ⟫ JUMPI 3
  O¹→Oᴱ′ (defₒ i x)   = O⁰→Oᴱ x ⟫ PUSH (i +ℕ 64) ⟫ MSTORE
  O¹→Oᴱ′ (setₒ i x)   = O⁰→Oᴱ x ⟫ PUSH i         ⟫ SSTORE
  O¹→Oᴱ′ (setₖₒ k x)  = O⁰→Oᴱ x ⟫ O⁰→Oᴱ k ⟫ SSTORE
  O¹→Oᴱ′ (outₒ xs)    = outₒ→Oᴱ 1024 xs
  O¹→Oᴱ′ (o₁ ∥ o₂)    = O¹→Oᴱ o₁ ⟫ O¹→Oᴱ o₂

  O¹→Oᴱ : O¹ → Oᴱ
  O¹→Oᴱ o@(_ ∥ _) = O¹→Oᴱ′ o
  O¹→Oᴱ o = fyi o (O¹→Oᴱ′ o)

O²→Oᴱ : O² → Oᴱ
O²→Oᴱ (sigₒ s k) =
  PUSH 224 ⟫ PUSH 2 ⟫ EXP ⟫ PUSH 0 ⟫ CALLDATALOAD ⟫ DIV ⟫
  PUSHSIG s ⟫ EQ ⟫ ISZERO ⟫ THEN (O¹→Oᴱ k)
O²→Oᴱ (seqₒ a b) =
  O²→Oᴱ a ⟫ O²→Oᴱ b

S¹→Oᴱ : S¹ → Oᴱ
S¹→Oᴱ s = prelude ⟫ O¹→Oᴱ (comp¹ s)

S²→Oᴱ : S² → Oᴱ
S²→Oᴱ s = prelude ⟫ O²→Oᴱ (comp² s) ⟫ REVERT

------------------------------------------------------------------------
-- ✿ Section 7
--     “Assembling EVM assembly”
--

data Opcode : ℕ → Set where
  B1   : ℕ      → Opcode 1
  B2   : ℤ      → Opcode 2
  BSig : String → Opcode 4

data Bytes : ℕ → Set where
  op_ : ∀ {m} → Opcode m → Bytes m
  Δ   : ℤ     → Bytes 2
  _⦂_ : ∀ {m n} → Bytes m → Bytes n → Bytes (m +ℕ n)

size : ∀ {m} → Bytes m → ℕ
size {m} _ = m

data Opcode⋆ : Set where
  _⟩_ : ∀ {m} → Opcode m → Opcode⋆ → Opcode⋆
  fin : Opcode⋆

infixr 1 _⟩_

append : Opcode⋆ → Opcode⋆ → Opcode⋆
append (x ⟩ o₁) o₂ = x ⟩ append o₁ o₂
append fin o₂ = o₂

⋆ : ∀ {n} → ℤ → Bytes n → Opcode⋆
⋆ i (op x) = x ⟩ fin
⋆ i (Δ x) = B2 (i +ℤ x) ⟩ fin
⋆ i (b₁ ⦂ b₂) = append (⋆ i b₁) (⋆ (i +ℤ (+ size b₁)) b₂)

infixr 10 _⦂_

code : Oᴱ → Σ ℕ Bytes
code (fyi o¹ oᴱ) = code oᴱ
code (x₁ ⟫ x₂) with code x₁
... | (i Σ, x₁ᴱ) with code x₂
... | (j Σ, x₂ᴱ) = , (x₁ᴱ ⦂ x₂ᴱ)
code ADD = , op B1 0x01
code ADDRESS = , op B1 0x30
code AND = , op B1 0x16
code CALLDATALOAD = , op B1 0x35
code CALLER = , op B1 0x33
code EQ = , op B1 0x14
code JUMPDEST = , op B1 0x5b
code (JUMP x)  = , op B1 0x61 ⦂ op B2 (+ x) ⦂ op B1 0x56
code (JUMPI x) = , op B1 0x61 ⦂ op B2 (+ x) ⦂ op B1 0x57
code (THEN x) with code x
... | i Σ, bs = , op B1 0x61 ⦂ Δ (+ (i +ℕ 2)) ⦂ op B1 0x57 ⦂ bs ⦂ op B1 0x5b

code (LOOP p k) with code p
... | iₚ Σ, bsₚ   with code k
... | iₖ Σ, bsₖ =
  , op B1 0x5b ⦂ bsₚ ⦂ op B1 0x15 ⦂ op B1 0x61 ⦂ Δ (+ (3 +ℕ iₖ +ℕ 4))
    ⦂ op B1 0x57 ⦂ bsₖ
    ⦂ op B1 0x61 ⦂ Δ (- (+ (1 +ℕ iₖ +ℕ 5 +ℕ iₚ +ℕ 1))) ⦂ op B1 0x56
    ⦂ op B1 0x5b

code KECCAK256 = , op B1 0x20
code MLOAD = , op B1 0x51
code MSTORE = , op B1 0x52
code MUL = , op B1 0x02
code MOD = , op B1 0x06
code EXP = , op B1 0x0a
code OR = , op B1 0x17
code (PUSH x) = , op B1 0x60 ⦂ op B1 x
code (PUSHSIG (sig x _ _)) = , op B1 0x63 ⦂ op BSig x
code DIV = , op B1 0x04
code SDIV = , op B1 0x05
code SGT = , op B1 0x13
code SLOAD = , op B1 0x54
code SLT = , op B1 0x12
code NOT = , op B1 0x19
code ISZERO = , op B1 0x15
code POP = , op B1 0x50
code SSTORE = , op B1 0x55
code STOP = , op B1 0x00
code SUB = , op B1 0x03
code TIMESTAMP = , op B1 0x42
code (DUP x) = , op B1 (0x7f +ℕ x)
code (SWAP x) = , op B1 (0x8f +ℕ x)
code REVERT = , op B1 0xfd
code REVERTIF = , op B1 0x60 ⦂ op B1 0x04 ⦂ op B1 0x57
code RETURN = , op B1 0xf3
code XOR = , op B1 0x18

compile : S² → Opcode⋆
compile s² with code (prelude ⟫ S²→Oᴱ s² ⟫ STOP)
... | _ Σ, b = ⋆ (+ 0) b

assemble : Oᴱ → Opcode⋆
assemble oᴱ with code (prelude ⟫ oᴱ ⟫ STOP)
... | _ Σ, b = ⋆ (+ 0) b

hexpad : ℤ → String
hexpad (+_ n) = showInBase 16 n ++ " "
hexpad (ℤ.negsuc n) = "{erroneously-negative}"

Opcode⋆→String : Opcode⋆ → String
Opcode⋆→String (B1   x ⟩ x₁) = "B1 " ++ hexpad (+ x) ++ Opcode⋆→String x₁
Opcode⋆→String (B2   x ⟩ x₁) = "B2 " ++ hexpad x ++ Opcode⋆→String x₁
Opcode⋆→String (BSig x ⟩ x₁) = "B1 63 [" ++ x ++ "] " ++ Opcode⋆→String x₁
Opcode⋆→String fin = ""

------------------------------------------------------------------------
-- ✿ Section 8
--     “Dai Credit System”
--

#0 = # 0; #1 = # 1; #2 = # 2; #3 = # 3
x₁ = $ 0; x₂ = $ 1; x₃ = $ 2; x₄ = $ 3; x₅ = $ 4
tmp₁ = 0; tmp₂ = 1
Φ = 0; Ψ = 1; Ω = 2; t₀ = 3; χ = 4; Σd = 5; Θ = 6

Cᵘ = λ u → ⟨ u , #0 ⟩
Dᵘ = λ u → ⟨ u , #1 ⟩
cᵘ = λ u → ⟨ u , #2 ⟩
dᵘ = λ u → ⟨ u , #3 ⟩

Cₓ₁ = Cᵘ x₁
Dₓ₁ = Dᵘ x₁
cₓ₁ = cᵘ x₁
dₓ₁ = dᵘ x₁

Cᵥ = Cᵘ Uₐ
Dᵥ = Dᵘ Uₐ
cᵥ = cᵘ Uₐ
dᵥ = dᵘ Uₐ

is-root = getₖ ⟨ #0 , Uₐ ⟩ ≡ #1

setₖ_↧_↥_ = λ k₁ k₂ Δ → iff (Δ + getₖ k₁ ≥ #0) │ iff (Δ + getₖ k₂ ≥ #0) -- XXX
setₖ_↧_ = λ k Δ → iff (getₖ k ≥ #0) − Δ -- XXX
setₖ_↥_ = λ k Δ → iff (getₖ k ≥ #0) + Δ -- XXX
set_↑_ = λ k Δ → set k ← get k + Δ

moldᵣ = sig "mold" 3 0
slipᵣ = sig "slip" 3 0
gazeᵤ = sig "gaze" 1 0
dripᵣ = sig "drip" 1 0
giveᵤ = sig "give" 5 0


-- ilk-code = S²→Oᴱ ilk

RPOW-example = PUSH 3 ⟫ PUSH 5 ⟫ RAY ⟫ MUL ⟫ RPOW ⟫ PUSHSIG giveᵤ
XEXP-example = PUSH 10 ⟫ PUSH 5 ⟫ XEXP
XMUL-example = PUSH 3 ⟫ PUSH 5 ⟫ XMUL
XADD-example = PUSH 3 ⟫ PUSH 8 ⟫ XADD

main = "⟨" ++ Opcode⋆→String (assemble RPOW-example) ++ "⟩"
