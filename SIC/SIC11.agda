------------------------------------------------------------------------
-- ✿ SIC: Symbolic Instruction Code
--

module SIC.SIC11 where

open import Data.String using (String) renaming (_==_ to _string==_)
open import Agda.Builtin.String using (String)

open import Data.Bool.Base using (Bool)
open import Data.List.NonEmpty using (List⁺; [_]; foldr₁) renaming (map to map⁺; _∷_ to _∷⁺_)
open import Data.List using (List; _∷_; []; map)
open import Data.Nat using (ℕ; _⊔_; suc) renaming (_≟_ to _≟ℕ_; _+_ to _+ℕ_; _*_ to _×ℕ_)

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
    DUP          : ℕ → Oᴱ
    EQ           : Oᴱ
    EXP          : Oᴱ
    ISZERO       : Oᴱ
    REVERTIF     : Oᴱ
    JUMP         : ℕ → Oᴱ
    JUMPDEST     : Oᴱ
    JUMPI        : ℕ → Oᴱ
    KECCAK256    : Oᴱ
    MLOAD        : Oᴱ
    MSTORE       : Oᴱ
    MUL          : Oᴱ
    NOT          : Oᴱ
    OR           : Oᴱ
    PUSH         : ℕ → Oᴱ
    PUSHSIG      : Sig → Oᴱ
    RETURN       : Oᴱ
    REVERT       : Oᴱ
    DIV          : Oᴱ
    SDIV         : Oᴱ
    SGT          : Oᴱ
    SLOAD        : Oᴱ
    SLT          : Oᴱ
    SSTORE       : Oᴱ
    STOP         : Oᴱ
    SUB          : Oᴱ
    SWAP         : ℕ → Oᴱ
    TIMESTAMP    : Oᴱ
    _⟫_          : Oᴱ → Oᴱ → Oᴱ
    ΔJUMPI       : Oᴱ → Oᴱ

  infixr 10 _⟫_

open Oᴱ

ADD-safe =
  PUSH 0 ⟫ DUP  2 ⟫ SLT ⟫ DUP  3 ⟫ DUP 3 ⟫ ADD    ⟫ DUP 4 ⟫ SLT ⟫ AND ⟫
  DUP  2 ⟫ PUSH 0 ⟫ SLT ⟫ SWAP 3 ⟫ DUP 1 ⟫ SWAP 4 ⟫ ADD   ⟫ SLT ⟫ AND ⟫
  OR ⟫ REVERTIF

prelude = JUMP 5 ⟫ JUMPDEST ⟫ REVERT ⟫ JUMPDEST

ADD-safe-example =
  prelude ⟫ PUSH 0 ⟫ SLOAD ⟫ PUSH 1 ⟫ SLOAD ⟫ ADD-safe

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
O⁰→Oᴱ (+ₒ)      = ADD-safe
O⁰→Oᴱ (−ₒ)      = PUSH 0 ⟫ SUB ⟫ ADD-safe
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
  PUSHSIG s ⟫ EQ ⟫ ISZERO ⟫ ΔJUMPI (O¹→Oᴱ k)
O²→Oᴱ (seqₒ a b) =
  O²→Oᴱ a ⟫ O²→Oᴱ b

S¹→Oᴱ : S¹ → Oᴱ
S¹→Oᴱ s = prelude ⟫ O¹→Oᴱ (comp¹ s)

S²→Oᴱ : S² → Oᴱ
S²→Oᴱ s = prelude ⟫ O²→Oᴱ (comp² s) ⟫ REVERT


------------------------------------------------------------------------
-- ✿ Section 7
--     “Dai Credit System”
--

#0 = # 0; #1 = # 1; #2 = # 2; #3 = # 3
x₁ = $ 0; x₂ = $ 1; x₃ = $ 2; x₄ = $ 3; x₅ = $ 4
tmp₁ = 0; tmp₂ = 1
Φ = 0; Ψ = 1; Ω = 2; t₀ = 3; χ = 4; Σd = 5

Cᵘ = λ u → ⟨ u , #0 ⟩
Dᵘ = λ u → ⟨ u , #1 ⟩
cᵘ = λ u → ⟨ u , #2 ⟩
dᵘ = λ u → ⟨ u , #3 ⟩

Cₓ₁ = Cᵘ x₁
Dₓ₁ = Dᵘ x₁
cₓ₁ = cᵘ x₁
dₓ₁ = dᵘ x₁

Cᵤ = Cᵘ Uₐ
Dᵤ = Dᵘ Uₐ
cᵤ = cᵘ Uₐ
dᵤ = dᵘ Uₐ

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

ilk =
   moldᵣ
   ┌ set Φ ← x₁
   │ set Ψ ← x₂
   │ set Ω ← x₃
   └

   slipᵣ
   ┌ iff is-root
   │ setₖ Cₓ₁ ↥ x₂
   │ setₖ Dₓ₁ ↥ x₃
   └

   gazeᵤ
   ┌ out ⟨ (getₖ Cₓ₁) , (getₖ Dₓ₁) , (getₖ cₓ₁) , (getₖ dₓ₁) ⟩
   └

   let Δχ = tmp₁ in
   dripᵣ
   ┌ def Δχ ≜ (get Φ ^ (t − get t₀) − #1) × get χ
   │ set χ ↑ ref Δχ
   │ set t₀ ← t
   │ out ⟨ (ref Δχ × get Σd) ⟩
   └

   let
     safe = λ Δc Δd →
       let safe₁ = (get χ × get Ψ × getₖ dᵤ ≤ getₖ cᵤ) ∨ Δd ≤ #0 ∧ Δc ≥ #0
           safe₂ = (get χ × get Σd ≤ get Ω) ∨ Δd ≤ #0 in
         safe₁ ∧ safe₂ in
   giveᵤ
   ┌ iff x₂ ≥ #0 ∧ x₃ ≥ #0 ∧ x₄ ≥ #0 ∧ x₅ ≥ #0
   │ setₖ Cᵤ ↧ Cₓ₁ ↥ x₂
   │ setₖ Dᵤ ↧ Dₓ₁ ↥ x₃
   │ setₖ cᵤ ↧ cₓ₁ ↥ x₄
   │ setₖ dₓ₁ ↧ dᵤ ↥ x₅
   │ iff safe x₂ x₃

ilk-code = S²→Oᴱ ilk
