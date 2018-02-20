------------------------------------------------------------------------
-- ✿ Sic: Symbolic Instruction Code
--

module Sic where

open import Data.String using (String; _++_)
  renaming (_==_ to _string==_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Show using (showInBase)
open import Data.Bool.Base using (Bool)
open import Data.List.NonEmpty using (List⁺; [_]; foldr₁)
  renaming (map to map⁺; _∷_ to _∷⁺_)
open import Data.List using (List; _∷_; []; map)
open import Data.Nat using (ℕ; _⊔_; suc)
  renaming (_≟_ to _≟ℕ_; _+_ to _+ℕ_; _*_ to _×ℕ_)
open import Data.Integer using (ℤ; +_)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; -_ to -ℤ_)
open import Data.Product using (Σ; ,_; proj₁; proj₂)
  renaming (_,_ to _Σ,_)
open import Relation.Binary.PropositionalEquality
  using (refl) renaming (_≡_ to _≣_)

------------------------------------------------------------------------
-- ✿ Section 1
--     SIC syntax data types
--

mutual
  data S⁰ : Set where
    # : ℕ → S⁰
    u : S⁰
    t : S⁰

    -_  : S⁰ → S⁰
    _+_ : S⁰ → S⁰ → S⁰
    _−_ : S⁰ → S⁰ → S⁰
    _×_ : S⁰ → S⁰ → S⁰
    _^_ : S⁰ → S⁰ → S⁰
    ¬_  : S⁰ → S⁰
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

data S¹ : Set where
  iff_ : S⁰ → S¹
  _≜_  : ℕ → S⁰ → S¹
  _←_  : ℕ → S⁰ → S¹
  _←ₖ_ : ⟨S⁰⟩ → S⁰ → S¹
  fyi_ : ⟨S⁰⟩ → S¹
  _│_  : S¹ → S¹ → S¹

data S² : Set where
  act : String → S¹ → S²
  _//_  : S² → S² → S²

------------------------------------------------------------------------
-- ✿ Section 2
--     SIC operator precedence and fixity
--

infixr 1 _//_
infixr 2 _│_

infix  10 iff_
infix  10 _≜_
infix  10 _←_
infix  10 _←ₖ_

infix  19 _↧ₖ_↥ₖ_

infixl 31 _∨_
infixl 32 _∧_
infixl 33 ¬_

infixl 35 _≡_
infixl 36 _≥_

infixl 40 _+_ _−_
infixl 41 _×_
infixl 42 -_

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
  ¬ₒ      : ∀ {i} → O⁰ (suc i) (suc i)
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
  sigₒ : String → O¹ → O²
  seqₒ : O² → O² → O²

infixr  5 _┆_
infixr 10 _∥_

-- In order to allocate memory (say, for EVM return values),
-- we need to compute the memory requirements of operations.

O⁰-memory : ∀ {m n} → O⁰ m n → ℕ
O⁰-memory (refₒ i) = suc i
O⁰-memory (o₁ ┆ o₂) = O⁰-memory o₁ ⊔ O⁰-memory o₂
O⁰-memory _ = 0

O¹-memory : O¹ → ℕ
O¹-memory (defₒ i x) = suc i ⊔ O⁰-memory x
O¹-memory (outₒ xs) = foldr₁ _⊔_ (map⁺ O⁰-memory xs)
O¹-memory (iffₒ x) = O⁰-memory x
O¹-memory (setₖₒ k x) = O⁰-memory x
O¹-memory (setₒ i x) = O⁰-memory x
O¹-memory (o₁ ∥ o₂) = O¹-memory o₁ ⊔ O¹-memory o₂

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
  comp⁰ u         = callerₒ
  comp⁰ (get x)   = getₒ x
  comp⁰ (ref x)   = refₒ x
  comp⁰ (arg x)   = argₒ x
  comp⁰ (getₖ k)  = ⟨comp⁰⟩ʰ k ┆ getₖₒ
  comp⁰ (sha k)   = ⟨comp⁰⟩ʰ k
  comp⁰ (x + y)   = comp⁰ x ┆ comp⁰ y ┆ +ₒ
  comp⁰ (x − y)   = comp⁰ x ┆ comp⁰ y ┆ −ₒ
  comp⁰ (- x)     = comp⁰ x ┆ #ₒ 0    ┆ −ₒ
  comp⁰ (x × y)   = comp⁰ x ┆ comp⁰ y ┆ ×ₒ
  comp⁰ (x ^ y)   = comp⁰ x ┆ comp⁰ y ┆ ^ₒ
  comp⁰ (¬ x)     = comp⁰ x ┆ ¬ₒ
  comp⁰ (x ∨ y)   = comp⁰ x ┆ comp⁰ y ┆ ∨ₒ
  comp⁰ (x ∧ y)   = comp⁰ x ┆ comp⁰ y ┆ ∧ₒ
  comp⁰ (x ≥ y)   = comp⁰ x ┆ comp⁰ y ┆ ≥ₒ
  comp⁰ (x ≤ y)   = comp⁰ x ┆ comp⁰ y ┆ ≤ₒ
  comp⁰ (x ≡ y)   = comp⁰ x ┆ comp⁰ y ┆ ≡ₒ
  comp⁰ t         = timeₒ

-- Compiling statement sequences
comp¹ : S¹ → O¹
comp¹ (iff x)  = iffₒ (comp⁰ x)
comp¹ (i ≜ x)  = defₒ i (comp⁰ x)
comp¹ (i ← x)  = setₒ i (comp⁰ x)
comp¹ (k ←ₖ x) = setₖₒ (comp⁰ x) (⟨comp⁰⟩ʰ k)
comp¹ (fyi x)  = outₒ (⟨comp⁰⟩ᵒ x)
comp¹ (x │ s)  = comp¹ x ∥ comp¹ s

-- Compiling signature dispatch sequences
comp² : S² → O²
comp² (act s k) = sigₒ s (comp¹ k)
comp² (a // b) = seqₒ (comp² a) (comp² b)

private
  module Memory-Size-Examples where
    S¹-memory : S¹ → ℕ
    S¹-memory s = O¹-memory (comp¹ s)

    example-1 : S¹-memory (0 ← # 0) ≣ 0
    example-1 = refl

    example-2 : S¹-memory (0 ≜ # 0) ≣ 1
    example-2 = refl

    example-3 : S¹-memory (0 ≜ ref 1 + ref 2) ≣ 3
    example-3 = refl

------------------------------------------------------------------------
-- ✿ Section 6
--     “Compiling EV²M to EVM assembly”
--

module Oᴱ where

  data Oᴱ : Set where
    tag          : O¹ → Oᴱ → Oᴱ
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
    PUSHSIG      : String → Oᴱ
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

XADD = DUP 2 ⟫ DUP 2 ⟫ XOR ⟫ NOT ⟫ SWAP 2 ⟫ DUP 2 ⟫ ADD ⟫ DUP 1 ⟫ SWAP 2 ⟫
  XOR ⟫ SWAP 1 ⟫ SWAP 2 ⟫ AND ⟫ PUSH 255 ⟫ PUSH 2 ⟫ EXP ⟫ AND ⟫ REVERTIF
XSUB = PUSH 0 ⟫ SUB ⟫ XADD
XMUL = DUP 2 ⟫ DUP 2 ⟫ MUL ⟫ DUP 2 ⟫ DUP 2 ⟫ DIV ⟫ SWAP 2 ⟫ SWAP 3 ⟫
  SWAP 1 ⟫ SWAP 2 ⟫ EQ ⟫ SWAP 2 ⟫ ISZERO ⟫ SWAP 1 ⟫ SWAP 2 ⟫ OR ⟫
  ISZERO ⟫ REVERTIF
RONE = PUSH 27 ⟫ PUSH 10 ⟫ EXP
RMUL = RONE ⟫ XMUL ⟫ PUSH 2 ⟫ RONE ⟫ DIV ⟫ XADD ⟫ DIV
RPOW = PUSH 2 ⟫ DUP 3 ⟫ MOD ⟫ ISZERO ⟫
  DUP 1 ⟫ RONE ⟫ MUL ⟫ SWAP 1 ⟫ ISZERO ⟫ DUP 3 ⟫ MUL ⟫ ADD ⟫
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
O⁰→Oᴱ (refₒ x)  = PUSH (x +ℕ 64) ⟫ MLOAD
O⁰→Oᴱ (getₒ x)  = PUSH x ⟫ SLOAD
O⁰→Oᴱ (argₒ x)  = PUSH (x ×ℕ 32) ⟫ CALLDATALOAD
O⁰→Oᴱ (getₖₒ)   = SLOAD
O⁰→Oᴱ (H¹ₒ)     = PUSH 0  ⟫ MSTORE ⟫
                  PUSH 32 ⟫ PUSH 0 ⟫ KECCAK256
O⁰→Oᴱ +ₒ      = XADD
O⁰→Oᴱ −ₒ      = XSUB
O⁰→Oᴱ ×ₒ      = RMUL
O⁰→Oᴱ ^ₒ      = RPOW
O⁰→Oᴱ ≡ₒ      = EQ
O⁰→Oᴱ ≥ₒ      = SGT ⟫ ISZERO
O⁰→Oᴱ ≤ₒ      = SLT ⟫ ISZERO
O⁰→Oᴱ ¬ₒ      = ISZERO
O⁰→Oᴱ ∧ₒ      = AND
O⁰→Oᴱ ∨ₒ      = OR
O⁰→Oᴱ H²ₒ     = PUSH 0  ⟫ MSTORE ⟫
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
  O¹→Oᴱ′ : ℕ → O¹ → Oᴱ
  O¹→Oᴱ′ n (iffₒ o)     = O⁰→Oᴱ o ⟫ ISZERO ⟫ JUMPI 3
  O¹→Oᴱ′ n (defₒ i x)   = O⁰→Oᴱ x ⟫ PUSH (i ×ℕ 32 +ℕ 64) ⟫ MSTORE
  O¹→Oᴱ′ n (setₒ i x)   = O⁰→Oᴱ x ⟫ PUSH i         ⟫ SSTORE
  O¹→Oᴱ′ n (setₖₒ k x)  = O⁰→Oᴱ x ⟫ O⁰→Oᴱ k ⟫ SSTORE
  O¹→Oᴱ′ n (outₒ xs)    = outₒ→Oᴱ (suc n ×ℕ 32 +ℕ 64) xs
  O¹→Oᴱ′ n (o₁ ∥ o₂)    = O¹→Oᴱ n o₁ ⟫ O¹→Oᴱ n o₂

  O¹→Oᴱ : ℕ → O¹ → Oᴱ
  O¹→Oᴱ n o@(_ ∥ _) = O¹→Oᴱ′ n o
  O¹→Oᴱ n o = tag o (O¹→Oᴱ′ n o)

O²→Oᴱ : O² → Oᴱ
O²→Oᴱ (sigₒ s k) =
  PUSH 224 ⟫ PUSH 2 ⟫ EXP ⟫ PUSH 0 ⟫ CALLDATALOAD ⟫ DIV ⟫
  PUSHSIG s ⟫ EQ ⟫ ISZERO ⟫ THEN (O¹→Oᴱ (O¹-memory k) k)
O²→Oᴱ (seqₒ a b) =
  O²→Oᴱ a ⟫ O²→Oᴱ b

prelude = JUMP 6 ⟫ JUMPDEST ⟫ REVERT ⟫ JUMPDEST

S²→Oᴱ : S² → Oᴱ
S²→Oᴱ s = prelude ⟫ O²→Oᴱ (comp² s) ⟫ REVERT

------------------------------------------------------------------------
-- ✿ Section 7
--     “Assembling EVM assembly”
--

-- Concrete bytes indexed by size
data B⁰ : ℕ → Set where
  B1   : ℕ      → B⁰ 1
  B2   : ℤ      → B⁰ 2
  BSig : String → B⁰ 4

-- Byte sequences with unresolved deltas
data B¹ : ℕ → Set where
  op_ : ∀ {m} → B⁰ m → B¹ m
  Δ   : ℤ → B¹ 2
  _⦂_ : ∀ {m n} → B¹ m → B¹ n → B¹ (m +ℕ n)

size : ∀ {m} → B¹ m → ℕ
size {m} _ = m

bytes : (p : Σ ℕ B¹) → B¹ (proj₁ p)
bytes = proj₂

data B⁰⋆ : Set where
  _⟩_ : ∀ {m} → B⁰ m → B⁰⋆ → B⁰⋆
  fin : B⁰⋆

infixr 1 _⟩_

append : B⁰⋆ → B⁰⋆ → B⁰⋆
append (x ⟩ o₁) o₂ = x ⟩ append o₁ o₂
append fin o₂ = o₂

⋆ : ∀ {n} → ℤ → B¹ n → B⁰⋆
⋆ i (op x) = x ⟩ fin
⋆ i (Δ x) = B2 (i +ℤ x) ⟩ fin
⋆ i (b₁ ⦂ b₂) = append (⋆ i b₁) (⋆ (i +ℤ (+ size b₁)) b₂)

infixr 10 _⦂_

code : Oᴱ → Σ ℕ B¹
code (tag o¹ oᴱ) = code oᴱ
code (x₁ ⟫ x₂) = , (bytes (code x₁) ⦂ bytes (code x₂))
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
    ⦂ op B1 0x61 ⦂ Δ (-ℤ (+ (1 +ℕ iₖ +ℕ 5 +ℕ iₚ +ℕ 1))) ⦂ op B1 0x56
    ⦂ op B1 0x5b

code KECCAK256 = , op B1 0x20
code MLOAD = , op B1 0x51
code MSTORE = , op B1 0x52
code MUL = , op B1 0x02
code MOD = , op B1 0x06
code EXP = , op B1 0x0a
code OR = , op B1 0x17
code (PUSH x) = , op B1 0x60 ⦂ op B1 x
code (PUSHSIG x) = , op B1 0x63 ⦂ op BSig x
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

compile : S² → B⁰⋆
compile s² = ⋆ (+ 0) (bytes (code (S²→Oᴱ s²)))

assemble : Oᴱ → B⁰⋆
assemble oᴱ with code (prelude ⟫ oᴱ ⟫ STOP)
... | _ Σ, b = ⋆ (+ 0) b

hexpad : ℤ → String
hexpad (+_ n) = showInBase 16 n ++ " "
hexpad (ℤ.negsuc n) = "{erroneously-negative}"

B⁰⋆→String : B⁰⋆ → String
B⁰⋆→String (B1   x ⟩ x₁) = "B1 " ++ hexpad (+ x) ++ B⁰⋆→String x₁
B⁰⋆→String (B2   x ⟩ x₁) = "B2 " ++ hexpad x ++ B⁰⋆→String x₁
B⁰⋆→String (BSig x ⟩ x₁) = "B1 63 [" ++ x ++ "] " ++ B⁰⋆→String x₁
B⁰⋆→String fin = ""

------------------------------------------------------------------------
-- ✿ Section 8
--     “Free Dapp Tools”
--

⓪ = # 0; ① = # 1; ② = # 2; ③ = # 3; ④ = # 4
x₁ = $ 0; x₂ = $ 1; x₃ = $ 2; x₄ = $ 3; x₅ = $ 4

v = x₁
root = getₖ ⟨ ⓪ , u ⟩ ≡ ①

_↑_ : ℕ → S⁰ → S¹
_↓_ : ℕ → S⁰ → S¹
_↥_ : ℕ → S⁰ → S¹
_↧_ : ℕ → S⁰ → S¹
_↥ₖ_ : ⟨S⁰⟩ → S⁰ → S¹
_↧ₖ_ : ⟨S⁰⟩ → S⁰ → S¹

n ↑  v = n ← get n + v
n ↥  v = n ←  get  n + v │ iff get  n ≥ ⓪
k ↥ₖ v = k ←ₖ getₖ k + v │ iff getₖ k ≥ ⓪
n ↓  v = n ↑  (- v)
n ↧  v = n ↥  (- v)
k ↧ₖ v = k ↥ₖ (- v)

_↧ₖ_↥ₖ_ : ⟨S⁰⟩ → ⟨S⁰⟩ → S⁰ → S¹
k₁ ↧ₖ k₂ ↥ₖ v = (k₁ ↧ₖ v) │ (k₂ ↥ₖ v)
