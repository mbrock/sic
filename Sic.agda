{-
                  ┌────────────────────────────────┐
                  │ Sic: Symbolic Instruction Code │
                  └────────────────────────────────┘

 We define Sic, a smart contract definition language, and a compiler.

 Sic has no loops and its only conditional statement is assertion.
 It is blockchain-agnostic; Sic programs do not depend on EVM details.

 We also define an “abstract contract machine” inspired by the EVM.
 It is agnostic about hashing functions, memory layouts, ABI, etc.

 Sic is compiled via abstract machine code into EVM code.

╔══════════════════════════════════════════════════════════════════════╗
║ Copyright © 2018  Mikael Brockman, Daniel Brockman, Rain             ║
║                                                                      ║
║ This program is free software: you can redistribute it and/or modify ║
║ it under the terms of the GNU Affero General Public License as       ║
║ published by the Free Software Foundation, either version 3 of the   ║
║ License, or (at your option) any later version.                      ║
║                                                                      ║
║ This program is distributed in the hope that it will be useful,      ║
║ but WITHOUT ANY WARRANTY; without even the implied warranty of       ║
║ MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the        ║
║ GNU Affero General Public License for more details.                  ║
╚══════════════════════════════════════════════════════════════════════╝

-}

module Sic where

-- Section 1: Sic syntax data types
--
-- We define a hierarchy of syntax data types:
--
--   ● S⁰, the expressions (pure formulas);
--   ● S¹, the actions (decisions and updates); and
--   ● S², the contracts (combinations of named actions).

open import Data.Unit  using (⊤)
open import Data.Empty using (⊥)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc; _⊔_)
  renaming (_+_ to _+ℕ_; _*_ to _*_)

module Sⁿ where
  data Arg : Set where $ : ℕ → Arg
  data Ref : Set where # : ℕ → Ref

  mutual
    data S⁰ : Set where
      _+_ _−_ _×_ _^_ _∨_ _∧_ _≥_ _≤_ _≡_ : S⁰ → S⁰ → S⁰
      -_ ¬_ : S⁰ → S⁰
      u t   : S⁰
      nat_  : ℕ → S⁰
      get_  : S⁰ → S⁰
      ref_  : Ref → S⁰
      arg_  : Arg → S⁰
      ⟨_    : ⟨S⁰⟩ → S⁰

    data ⟨S⁰⟩ : Set where
      ⟨⟩_  : S⁰ → ⟨S⁰⟩
      _,_  : S⁰ → ⟨S⁰⟩ → ⟨S⁰⟩

    _⟩ : S⁰ → ⟨S⁰⟩
    x ⟩ = ⟨⟩ x

  -- We define a “type class” for overloading number literals.
  record IsNumber {a} (A : Set a) : Set a where
    field
      from-ℕ : ℕ → A

  open IsNumber {{...}} public

  instance
    ℕ-IsNumber   : IsNumber ℕ
    S⁰-IsNumber  : IsNumber S⁰
    Ref-IsNumber : IsNumber Ref
    Arg-IsNumber : IsNumber Arg
    from-ℕ {{ℕ-IsNumber}}   n = n
    from-ℕ {{S⁰-IsNumber}}  n = nat n
    from-ℕ {{Ref-IsNumber}} n = # n
    from-ℕ {{Arg-IsNumber}} n = $ n

  {-# BUILTIN FROMNAT from-ℕ #-}

  open import Data.List.NonEmpty using (List⁺; [_]; _∷⁺_; length)

  fyi-ok : ℕ → ℕ → Set
  fyi-ok 0       _       = ⊤
  fyi-ok (suc _) 0       = ⊤
  fyi-ok (suc _) (suc _) = ⊥

  data S¹ : ℕ → Set where
    iff_ : S⁰ → S¹ 0
    _≜_  : ℕ → S⁰ → S¹ 0
    _←_  : S⁰ → S⁰ → S¹ 0
    fyi  : (xs : List⁺ S⁰) → S¹ (length xs)
    _│_  : ∀ {m n} → S¹ m → S¹ n → {_ : fyi-ok m n} → S¹ (m ⊔ n)

  S¹-fyi-size : ∀ {n} → S¹ n → ℕ
  S¹-fyi-size {n} _ = n

  fyi₁ : S⁰ → S¹ 1
  fyi₁ a = fyi [ a ]

  fyi₂ : S⁰ → S⁰ → S¹ 2
  fyi₂ a b = fyi (a ∷⁺ [ b ])

  fyi₃ : S⁰ → S⁰ → S⁰ → S¹ 3
  fyi₃ a b c = fyi (a ∷⁺ b ∷⁺ [ c ])

  fyi₄ : S⁰ → S⁰ → S⁰ → S⁰ → S¹ 4
  fyi₄ a b c d = fyi (a ∷⁺ b ∷⁺ c ∷⁺ [ d ])

  data S² : Set where
    act_::_ : ∀ {n} → (sig : String) → S¹ n → S²
    _//_ : S² → S² → S²

  infixr 1 _//_
  infixr 2 act_::_
  infixr 3 _│_

  infix  10 iff_ _≜_ _←_

  infixl 31 _∨_
  infixl 32 _∧_
  infixl 33 ¬_

  infixl 35 _≡_
  infixl 36 _≥_

  infixl 40 _+_ _−_
  infixl 41 _×_
  infixl 42 -_

  infix  50 get_ ref_ arg_

  infixr 60 ⟨_
  infixr 61 _,_
  infixr 62 _⟩


-- Section 3: Oⁿ, the “Abstract Contract Machine”
--
-- We define a stack machine that is more general than the EVM.
-- This instruction set can be compiled to other virtual machines.
-- Like the Sⁿ syntax types, the Oⁿ code types form a hierarchy:
--
--   ● O⁰, the target of S⁰, stack computations;
--   ● O¹, the target of S¹, effect sequences; and
--   ● O², the target of S², contracts with named actions.
--

module Oⁿ where

  -- The O⁰ operations have stack effects, which we encode in the types.
  -- For example, the type of +ₒ denotes taking two items and leaving one.
  -- Sequences like a ┆ b ┆ c must be “well-formed.”

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

  open import Data.List.NonEmpty using (List⁺)

  data O¹ : Set where
    _∥_   : O¹ → O¹ → O¹
    iffₒ  : O⁰ 0 1 → O¹
    setₖₒ : O⁰ 0 1 → O⁰ 0 1 → O¹
    defₒ  : ℕ → O⁰ 0 1 → O¹
    setₒ  : ℕ → O⁰ 0 1 → O¹
    fyiₒ  : List⁺ (O⁰ 0 1) → O¹

  data O² : Set where
    sigₒ : String → ℕ → O¹ → O²
    seqₒ : O² → O² → O²

  infixr  5 _┆_
  infixr 10 _∥_

  -- In order to allocate memory (say, for EVM return values),
  -- we need to compute the memory requirements of operations.

  open Data.Nat using (_⊔_)

  O⁰-memory : ∀ {m n} → O⁰ m n → ℕ
  O⁰-memory (refₒ i) = suc i
  O⁰-memory (o₁ ┆ o₂) = O⁰-memory o₁ ⊔ O⁰-memory o₂
  O⁰-memory x = 0

  O¹-memory : O¹ → ℕ
  O¹-memory (defₒ i x) = suc i ⊔ O⁰-memory x
  O¹-memory (fyiₒ xs) = foldr₁ _⊔_ (map⁺ O⁰-memory xs)
    where
      open import Data.List.NonEmpty using (foldr₁)
             renaming (map to map⁺)
  O¹-memory (iffₒ x) = O⁰-memory x
  O¹-memory (setₖₒ k x) = O⁰-memory x
  O¹-memory (setₒ i x) = O⁰-memory x
  O¹-memory (o₁ ∥ o₂) = O¹-memory o₁ ⊔ O¹-memory o₂

-- Section 4: Compiling Sic to abstract machine code
--
-- This transformation is mostly a simple linearization,
-- since our abstract machine is based on Sic semantics.
--

module Sⁿ→Oⁿ where
  open Sⁿ
  open Oⁿ

  open import Data.List.NonEmpty using (List⁺; [_]; _∷⁺_)
    renaming (map to map⁺)

  mutual
    ⟨S⁰⟩→O⁰ : ∀ {i} → ⟨S⁰⟩ → O⁰ i (suc i)
    ⟨S⁰⟩→O⁰ (⟨⟩ x)   =              S⁰→O⁰ x ┆ H¹ₒ
    ⟨S⁰⟩→O⁰ (x , xs) = ⟨S⁰⟩→O⁰ xs ┆ S⁰→O⁰ x ┆ H²ₒ

    -- Compiling expressions
    S⁰→O⁰ : ∀ {i} → S⁰ → O⁰ i (suc i)
    S⁰→O⁰ (⟨ xs)    = ⟨S⁰⟩→O⁰ xs
    S⁰→O⁰ (nat n)     = #ₒ n
    S⁰→O⁰ u         = callerₒ
    S⁰→O⁰ (get x)   = S⁰→O⁰ x ┆ getₖₒ
    S⁰→O⁰ (ref (# x)) = refₒ x
    S⁰→O⁰ (arg ($ x)) = argₒ x
    S⁰→O⁰ (x + y)   = S⁰→O⁰ y ┆ S⁰→O⁰ x ┆ +ₒ
    S⁰→O⁰ (x − y)   = S⁰→O⁰ y ┆ S⁰→O⁰ x ┆ −ₒ
    S⁰→O⁰ (- x)     = #ₒ 0    ┆ S⁰→O⁰ x ┆ −ₒ
    S⁰→O⁰ (x × y)   = S⁰→O⁰ y ┆ S⁰→O⁰ x ┆ ×ₒ
    S⁰→O⁰ (x ^ y)   = S⁰→O⁰ y ┆ S⁰→O⁰ x ┆ ^ₒ
    S⁰→O⁰ (¬ x)     = S⁰→O⁰ x ┆ ¬ₒ
    S⁰→O⁰ (x ∨ y)   = S⁰→O⁰ y ┆ S⁰→O⁰ x ┆ ∨ₒ
    S⁰→O⁰ (x ∧ y)   = S⁰→O⁰ y ┆ S⁰→O⁰ x ┆ ∧ₒ
    S⁰→O⁰ (x ≥ y)   = S⁰→O⁰ y ┆ S⁰→O⁰ x ┆ ≥ₒ
    S⁰→O⁰ (x ≤ y)   = S⁰→O⁰ y ┆ S⁰→O⁰ x ┆ ≤ₒ
    S⁰→O⁰ (x ≡ y)   = S⁰→O⁰ y ┆ S⁰→O⁰ x ┆ ≡ₒ
    S⁰→O⁰ t         = timeₒ

  -- Compiling statement sequences
  S¹→O¹ : ∀ {n} → S¹ n → O¹
  S¹→O¹ (iff x)  = iffₒ (S⁰→O⁰ x)
  S¹→O¹ (i ≜ x)  = defₒ i (S⁰→O⁰ x)
  S¹→O¹ (k ← x)  = setₖₒ (S⁰→O⁰ k) (S⁰→O⁰ x)
  S¹→O¹ (x │ s)  = S¹→O¹ x ∥ S¹→O¹ s
  S¹→O¹ (fyi x)  = fyiₒ (map⁺ S⁰→O⁰ x)

  -- Compiling signature dispatch sequences
  S²→O² : S² → O²
  S²→O² (act s :: k) = sigₒ s (S¹-fyi-size k) (S¹→O¹ k)
  S²→O² (a // b) = seqₒ (S²→O² a) (S²→O² b)

  -- Some compile-time assertions
  private
    open Sⁿ
    open import Relation.Binary.PropositionalEquality
      using (refl) renaming (_≡_ to _≣_)

    S¹-memory : ∀ {n} → S¹ n → ℕ
    S¹-memory s = O¹-memory (S¹→O¹ s)

    example-1 : S¹-memory {0} (nat 0 ← nat 0) ≣ 0
    example-1 = refl

    example-2 : S¹-memory {0} (0 ≜ nat 0) ≣ 1
    example-2 = refl

    example-3 : S¹-memory {0} (0 ≜ ref 1 + ref 2) ≣ 3
    example-3 = refl


-- Section 5: EVM assembly
--
-- We now introduce a data type denoting EVM assembly.
--
-- Our EVM assembly type has the control flow structures LOOP and ELSE
-- which are taken care of later by the bytecode assembler.
--

module EVM where
  open Oⁿ

  data Oᴱ : Set where
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
    ELSE         : Oᴱ → Oᴱ
    TIMESTAMP    : Oᴱ
    XOR          : Oᴱ
    _⟫_          : Oᴱ → Oᴱ → Oᴱ
    tag          : O¹ → Oᴱ → Oᴱ

  infixr 10 _⟫_

  |Oᴱ| : Oᴱ → ℕ
  |Oᴱ| (x ⟫ y) = |Oᴱ| x +ℕ |Oᴱ| y
  |Oᴱ| _ = 1


-- Section 6: EVM safe math and exponentiation
--
-- For the EVM, we define our own overflow safe arithmetic.
--
-- We also define multiplication, division, and exponentiation
-- on decimal fixed point numbers.
--

module EVM-Math where
  open EVM

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
      ELSE (SWAP 2 ⟫ SWAP 1 ⟫ DUP 2 ⟫ RMUL ⟫ SWAP 1 ⟫ SWAP 2) ⟫
      PUSH 2 ⟫ SWAP 2 ⟫ DIV
    ) ⟫ SWAP 2 ⟫ POP ⟫ POP

    -- rpow(x, n) => z
    --   z = n % 2 ? x : 1
    --   for (n /= 2; n != 0; n /= 2)
    --     x = x * x
    --     if (n % 2)
    --       z = z * x

    -- f(1) = x; f(0) = 1
    -- f(a) = !a + a * x
    -- f(0) = 1 + 0 * x; f(1) = 0 + 1 * x

  RPOW′ =
    let z = 2 * 32 in
    DUP 2 ⟫ PUSH 2 ⟫ SWAP 1 ⟫ MOD ⟫ DUP 1 ⟫ ISZERO ⟫
    SWAP 1 ⟫ DUP 3 ⟫ MUL ⟫ ADD ⟫ PUSH z ⟫ MSTORE ⟫
    SWAP 1 ⟫ PUSH 2 ⟫ SWAP 1 ⟫ DIV ⟫ LOOP (DUP 1) (
      SWAP 1 ⟫ DUP 1 ⟫ MUL ⟫ PUSH 2 ⟫ DUP 3 ⟫ MOD ⟫ ISZERO ⟫
      ELSE (PUSH z ⟫ MLOAD ⟫ DUP 2 ⟫ MUL ⟫ PUSH z ⟫ MSTORE) ⟫
      SWAP 1 ⟫ PUSH 2 ⟫ SWAP 1 ⟫ DIV
    ) ⟫ POP ⟫ POP ⟫ PUSH z ⟫ MLOAD

-- Section 7: Compiling Sic machine code to EVM assembly
--

module Sic→EVM where

  open Oⁿ
  open EVM
  open EVM-Math

  wordsize : ℕ
  wordsize = 32

  -- We use three reserved variables: two for hashing, one for RPOW.
  m₀ = 2 * wordsize

  O⁰→Oᴱ : ∀ {i j} → O⁰ i j → Oᴱ
  O⁰→Oᴱ (#ₒ n)    = PUSH n
  O⁰→Oᴱ timeₒ     = TIMESTAMP
  O⁰→Oᴱ (x₁ ┆ x₂) = O⁰→Oᴱ x₁ ⟫ O⁰→Oᴱ x₂
  O⁰→Oᴱ (callerₒ) = CALLER
  O⁰→Oᴱ (refₒ x)  = PUSH (x +ℕ m₀) ⟫ MLOAD
  O⁰→Oᴱ (getₒ x)  = PUSH x ⟫ SLOAD
  O⁰→Oᴱ (argₒ x)  = PUSH (x * wordsize) ⟫ CALLDATALOAD
  O⁰→Oᴱ (getₖₒ)   = SLOAD
  O⁰→Oᴱ (H¹ₒ)     = PUSH 0  ⟫ MSTORE ⟫
                    PUSH wordsize ⟫ PUSH 0 ⟫ KECCAK256
  O⁰→Oᴱ +ₒ      = XADD
  O⁰→Oᴱ −ₒ      = XSUB
  O⁰→Oᴱ ×ₒ      = RMUL
  O⁰→Oᴱ ^ₒ      = RPOW′
  O⁰→Oᴱ ≡ₒ      = EQ
  O⁰→Oᴱ ≥ₒ      = SGT ⟫ ISZERO
  O⁰→Oᴱ ≤ₒ      = SLT ⟫ ISZERO
  O⁰→Oᴱ ¬ₒ      = ISZERO
  O⁰→Oᴱ ∧ₒ      = AND
  O⁰→Oᴱ ∨ₒ      = OR
  O⁰→Oᴱ H²ₒ     = PUSH 0  ⟫ MSTORE ⟫
                  PUSH wordsize ⟫ MSTORE ⟫
                  PUSH 64 ⟫ PUSH 0 ⟫ KECCAK256

  record Index a : Set where
    constructor _at_from_
    field
      thing : a
      index : ℕ
      base  : ℕ

  open import Data.List using (List; _∷_; [])
  open import Data.List.NonEmpty using (List⁺; [_]) renaming (_∷_ to _∷⁺_)

  index : ∀ {t} → ℕ → ℕ → List t → List (Index t)
  index j i [] = []
  index j i (x ∷ xs) = x at j from i ∷ index (suc j) i xs

  index⁺ : ∀ {t} → ℕ → List⁺ t → List⁺ (Index t)
  index⁺ i (x ∷⁺ []) = [ x at 0 from i ]
  index⁺ i (x ∷⁺ xs) = x at 0 from i ∷⁺ index 1 i xs

  O⁰#→Oᴱ : Index (O⁰ 0 1) → Oᴱ
  O⁰#→Oᴱ (x at j from i) = O⁰→Oᴱ x ⟫ PUSH (i +ℕ j * wordsize) ⟫ MSTORE

  fyiₒ→Oᴱ : ℕ → List⁺ (O⁰ 0 1) → Oᴱ
  fyiₒ→Oᴱ i xs = foldr₁ _⟫_ (map O⁰#→Oᴱ (index⁺ i xs)) ⟫ return
    where
      open import Data.List.NonEmpty using (foldr₁; map; length)
      return = PUSH (wordsize * length xs) ⟫ PUSH i ⟫ RETURN

  mutual
    O¹→Oᴱ′ : ℕ → O¹ → Oᴱ
    O¹→Oᴱ′ n (iffₒ o)     = O⁰→Oᴱ o ⟫ ISZERO ⟫ JUMPI 3
    O¹→Oᴱ′ n (defₒ i x)   = O⁰→Oᴱ x ⟫ PUSH (i * wordsize +ℕ m₀) ⟫ MSTORE
    O¹→Oᴱ′ n (setₒ i x)   = O⁰→Oᴱ x ⟫ PUSH i ⟫ SSTORE
    O¹→Oᴱ′ n (setₖₒ k x)  = O⁰→Oᴱ x ⟫ O⁰→Oᴱ k ⟫ SSTORE
    O¹→Oᴱ′ n (fyiₒ xs)    = fyiₒ→Oᴱ offset xs
      where offset = suc n * wordsize +ℕ m₀
    O¹→Oᴱ′ n (o₁ ∥ o₂)    = O¹→Oᴱ n o₁ ⟫ O¹→Oᴱ n o₂

    O¹→Oᴱ : ℕ → O¹ → Oᴱ
    O¹→Oᴱ n o@(_ ∥ _) = O¹→Oᴱ′ n o
    O¹→Oᴱ n o = tag o (O¹→Oᴱ′ n o)

  prelude = JUMP 6 ⟫ JUMPDEST ⟫ REVERT ⟫ JUMPDEST

  return : ℕ → ℕ → Oᴱ
  return offset n =
    PUSH (n * wordsize) ⟫
    PUSH (m₀ +ℕ offset * wordsize) ⟫
    RETURN

  O²→Oᴱ : O² → Oᴱ
  O²→Oᴱ (sigₒ s n k) =
    PUSH 224 ⟫ PUSH 2 ⟫ EXP ⟫ PUSH 0 ⟫ CALLDATALOAD ⟫ DIV ⟫
    PUSHSIG s ⟫ EQ ⟫ ISZERO ⟫ ELSE (O¹→Oᴱ (O¹-memory k) k ⟫
    return (O¹-memory k) n)
  O²→Oᴱ (seqₒ a b) =
    O²→Oᴱ a ⟫ O²→Oᴱ b

  open Sⁿ    using (S²)
  open Sⁿ→Oⁿ using (S²→O²)

  S²→Oᴱ : S² → Oᴱ
  S²→Oᴱ s = prelude ⟫ O²→Oᴱ (S²→O² s) ⟫ REVERT

  compile : S² → Oᴱ
  compile = S²→Oᴱ


-- Section 8: Assembling EVM assembly
--
-- We define the concrete output format of the Agda program.
--
-- This is mostly uninteresting except for the “delta encoding,”
-- which is how we deal with assembling relative jumps:
--
--   We define Δ i where i ∈ ℤ as “the PC i steps from here”.
--   These deltas are resolved at the last stage of assembly.
--

module EVM-Assembly where

  open import Data.Integer using (ℤ; +_)
    renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; -_ to -ℤ_)

  data B⁰ : ℕ → Set where
    B1   : ℕ      → B⁰ 1
    B2   : ℤ      → B⁰ 2
    BSig : String → B⁰ 4

  data B¹ : ℕ → Set where
    op_ : ∀ {m} → B⁰ m → B¹ m
    Δ   : ℤ → B¹ 2
    _⦂_ : ∀ {m n} → B¹ m → B¹ n → B¹ (m +ℕ n)

  infixr 10 _⦂_

  bytesize : ∀ {m} → B¹ m → ℕ
  bytesize {m} _ = m

  open import Data.Product using (Σ; ,_; proj₁; proj₂)
    renaming (_,_ to _Σ,_)

  data B⁰⋆ : Set where
    _⟩_ : ∀ {m} → B⁰ m → B⁰⋆ → B⁰⋆
    fin : B⁰⋆

  infixr 1 _⟩_

  append : B⁰⋆ → B⁰⋆ → B⁰⋆
  append (x ⟩ o₁) o₂ = x ⟩ append o₁ o₂
  append fin o₂ = o₂

  ⋆′ : ∀ {n} → ℤ → B¹ n → B⁰⋆
  ⋆′ i (op x) = x ⟩ fin
  ⋆′ i (Δ x) = B2 (i +ℤ x) ⟩ fin
  ⋆′ i (b₁ ⦂ b₂) = append (⋆′ i b₁) (⋆′ (i +ℤ (+ bytesize b₁)) b₂)

  ⋆ : ∀ {n} → B¹ n → B⁰⋆
  ⋆ b = ⋆′ (+ 0) b

  open EVM

  code′ : Oᴱ → Σ ℕ B¹
  code′ (tag o¹ oᴱ) = code′ oᴱ
  code′ (x₁ ⟫ x₂) = , (proj₂ (code′ x₁) ⦂ proj₂ (code′ x₂))
  code′ ADD = , op B1 0x01
  code′ ADDRESS = , op B1 0x30
  code′ AND = , op B1 0x16
  code′ CALLDATALOAD = , op B1 0x35
  code′ CALLER = , op B1 0x33
  code′ EQ = , op B1 0x14
  code′ JUMPDEST = , op B1 0x5b
  code′ (JUMP x)  = , op B1 0x61 ⦂ op B2 (+ x) ⦂ op B1 0x56
  code′ (JUMPI x) = , op B1 0x61 ⦂ op B2 (+ x) ⦂ op B1 0x57
  code′ (ELSE x) with code′ x
  ... | i Σ, bs = , op B1 0x61 ⦂ Δ (+ (i +ℕ skip)) ⦂ op B1 0x57 ⦂ bs ⦂ op B1 0x5b
    where skip = 3
  code′ (LOOP p k) with code′ p
  ... | iₚ Σ, bsₚ   with code′ k
  ... | iₖ Σ, bsₖ =
    , op B1 0x5b ⦂ bsₚ ⦂ op B1 0x15 ⦂ op B1 0x61 ⦂ Δ (+ (3 +ℕ iₖ +ℕ 4))
      ⦂ op B1 0x57 ⦂ bsₖ
      ⦂ op B1 0x61 ⦂ Δ (-ℤ (+ skip)) ⦂ op B1 0x56
      ⦂ op B1 0x5b
    where skip = 1 +ℕ iₖ +ℕ 5 +ℕ iₚ +ℕ 1
  code′ KECCAK256 = , op B1 0x20
  code′ MLOAD = , op B1 0x51
  code′ MSTORE = , op B1 0x52
  code′ MUL = , op B1 0x02
  code′ MOD = , op B1 0x06
  code′ EXP = , op B1 0x0a
  code′ OR = , op B1 0x17
  code′ (PUSH x) = , op B1 0x60 ⦂ op B1 x
  code′ (PUSHSIG x) = , op B1 0x63 ⦂ op BSig x
  code′ DIV = , op B1 0x04
  code′ SDIV = , op B1 0x05
  code′ SGT = , op B1 0x13
  code′ SLOAD = , op B1 0x54
  code′ SLT = , op B1 0x12
  code′ NOT = , op B1 0x19
  code′ ISZERO = , op B1 0x15
  code′ POP = , op B1 0x50
  code′ SSTORE = , op B1 0x55
  code′ STOP = , op B1 0x00
  code′ SUB = , op B1 0x03
  code′ TIMESTAMP = , op B1 0x42
  code′ (DUP x) = , op B1 (0x7f +ℕ x)
  code′ (SWAP x) = , op B1 (0x8f +ℕ x)
  code′ REVERT = , op B1 0xfd
  code′ REVERTIF = , op B1 0x60 ⦂ op B1 0x04 ⦂ op B1 0x57
  code′ RETURN = , op B1 0xf3
  code′ XOR = , op B1 0x18

  code : (o : Oᴱ) → B¹ (proj₁ (code′ o))
  code o = proj₂ (code′ o)

  open import Data.String using (String; _++_; toList; fromList)
  open import Data.List using (length; replicate)

  0-pad : ℕ → String → String
  0-pad n s with (+ n) -ℤ (+ length (toList s))
  0-pad n s | +_ i = fromList (replicate i '0') ++ s
  0-pad n s | ℤ.negsuc n₁ = "{erroneously-huge}"

  ℤ→hex : ℕ → ℤ → String
  ℤ→hex n (+_ x) = 0-pad n (Data.Nat.Show.showInBase 16 x)
    where import Data.Nat.Show
  ℤ→hex _ (ℤ.negsuc n) = "{erroneously-negative}"

  B⁰⋆→String : B⁰⋆ → String
  B⁰⋆→String (B1   x ⟩ x₁) = ℤ→hex 2 (+ x) ++ B⁰⋆→String x₁
  B⁰⋆→String (B2   x ⟩ x₁) = ℤ→hex 4 x ++ B⁰⋆→String x₁
  B⁰⋆→String (BSig x ⟩ x₁) = "[" ++ x ++ "]" ++ B⁰⋆→String x₁
  B⁰⋆→String fin = ""

module Main where
  open Sⁿ
  open EVM
  open EVM-Assembly
  open Sic→EVM

  compile-and-assemble : S² → String
  compile-and-assemble s² = B⁰⋆→String (⋆ (code (S²→Oᴱ s²)))

  assemble : Oᴱ → B⁰⋆
  assemble oᴱ = ⋆ (code (prelude ⟫ oᴱ ⟫ STOP))


-- Section 7: Dappsys, free stuff for dapp developers
--
-- We now define a “standard library” in the Sic language.
--

module Dappsys where
  open Sⁿ

  root = get ⟨ 0 , u ⟩ ≡ 1

  x₁ x₂ x₃ x₄ x₅ : Arg
  x₁ = 0; x₂ = 1; x₃ = 2; x₄ = 3; x₅ = 4

  v = x₁

  _↑_ : S⁰ → S⁰ → S¹ 0
  _↓_ : S⁰ → S⁰ → S¹ 0
  _↥_ : S⁰ → S⁰ → S¹ 0
  _↧_ : S⁰ → S⁰ → S¹ 0

  n ↑ v = n ← get n + v
  n ↥ v = n ← get n + v │ iff get n ≥ 0
  n ↓ v = n ↑ (- v)
  n ↧ v = n ↥ (- v)

  _↧_↥_ : S⁰ → S⁰ → S⁰ → S¹ 0
  k₁ ↧ k₂ ↥ v = (k₁ ↧ v) │ (k₂ ↥ v)

  infix 19 _↧_↥_


-- Section 8: Compiling to Solidity
--
-- We define a compiler from S² to Solidity source code.
--

module Solidity where
  open Sⁿ

  open import Data.List using (List; _∷_; []; _++_)
  open import Data.Nat.Show using (showInBase)

  show = showInBase

  mutual

    sequence : ⟨S⁰⟩ → List String
    sequence (⟨⟩ x) =
      "keccak256(" ∷ ⟦ x ⟧⁰ ++ ")" ∷ []
    sequence (x , s) =
      "keccak256(" ∷ ⟦ x ⟧⁰ ++ ", " ∷ sequence s ++ ")" ∷ []

    ⟦_⟧⁰ : S⁰ → List String
    ⟦ nat x ⟧⁰ = show 10 x ∷ []
    ⟦ u ⟧⁰ = "msg.sender" ∷ []
    ⟦ t ⟧⁰ = "block.timestamp" ∷ []
    ⟦ get x ⟧⁰ = "storage[" ∷ ⟦ x ⟧⁰ ++ "]" ∷ []
    ⟦ ref (# x) ⟧⁰ = "m" ∷ show 10 x ∷ []
    ⟦ arg ($ x) ⟧⁰ = "p" ∷ show 10 x ∷ []
    ⟦ ⟨ x ⟧⁰ = sequence x
    ⟦ x + x₁ ⟧⁰ = "(" ∷ ⟦ x ⟧⁰ ++ " + " ∷ ⟦ x₁ ⟧⁰ ++ ")" ∷ []
    ⟦ x − x₁ ⟧⁰ = "(" ∷ ⟦ x ⟧⁰ ++ " - " ∷ ⟦ x₁ ⟧⁰ ++ ")" ∷ []
    ⟦ x × x₁ ⟧⁰ = "(" ∷ ⟦ x ⟧⁰ ++ " * " ∷ ⟦ x₁ ⟧⁰ ++ ")" ∷ []
    ⟦ x ^ x₁ ⟧⁰ = "(" ∷ ⟦ x ⟧⁰ ++ " ^ " ∷ ⟦ x₁ ⟧⁰ ++ ")" ∷ []
    ⟦ ¬ x ⟧⁰ = "(!" ∷ ⟦ x ⟧⁰ ++ ")" ∷ []
    ⟦ - x ⟧⁰ = "(-" ∷ ⟦ x ⟧⁰ ++ ")" ∷ []
    ⟦ x ∨ x₁ ⟧⁰ = "(" ∷ ⟦ x ⟧⁰ ++ " || " ∷ ⟦ x₁ ⟧⁰ ++ ")" ∷ []
    ⟦ x ∧ x₁ ⟧⁰ = "(" ∷ ⟦ x ⟧⁰ ++ " && " ∷ ⟦ x₁ ⟧⁰ ++ ")" ∷ []
    ⟦ x ≥ x₁ ⟧⁰ = "(" ∷ ⟦ x ⟧⁰ ++ " >= " ∷ ⟦ x₁ ⟧⁰ ++ ")" ∷ []
    ⟦ x ≤ x₁ ⟧⁰ = "(" ∷ ⟦ x ⟧⁰ ++ " <= " ∷ ⟦ x₁ ⟧⁰ ++ ")" ∷ []
    ⟦ x ≡ x₁ ⟧⁰ = "(" ∷ ⟦ x ⟧⁰ ++ " == " ∷ ⟦ x₁ ⟧⁰ ++ ")" ∷ []

  open import Data.List.NonEmpty using (List⁺; toList; length)
  open import Data.List using (intersperse; concatMap; zip; upTo)
  open import Data.Product using () renaming (_×_ to _at_)

  ⟦_⟧ᶠʸⁱ : List⁺ S⁰ → List String
  ⟦ xs ⟧ᶠʸⁱ = intersperse "\n"
               (concatMap f (zip (toList xs) ("a" ∷ "b" ∷ "c" ∷ "d" ∷ [])))
    where
      f : S⁰ at String → List String
      f (x Data.Product., k) =  k ∷ " = " ∷ ⟦ x ⟧⁰ ++ ";" ∷ []
  ⟦_⟧¹ : ∀ {n} → S¹ n → List String
  ⟦ iff x ⟧¹ = "require(" ∷ ⟦ x ⟧⁰ ++ ");" ∷ []
  ⟦ i ≜ x ⟧¹ = "uint256 m" ∷ show 10 i ∷ " = " ∷ ⟦ x ⟧⁰ ++ ";" ∷ []
  ⟦ k ← x ⟧¹ = "storage[" ∷ ⟦ k ⟧⁰ ++ "] = " ∷ ⟦ x ⟧⁰ ++ ";" ∷ []
  ⟦ fyi xs ⟧¹ = ⟦ xs ⟧ᶠʸⁱ
  ⟦ x₁ │ x₂ ⟧¹ = ⟦ x₁ ⟧¹ ++ "\n" ∷ ⟦ x₂ ⟧¹

  fyi-returns : ℕ → List String
  fyi-returns n =
    Data.List.intersperse ", "
      (Data.List.map (λ x → Data.String._++_ "int256 " x)
        (Data.List.take n ("a" ∷ "b" ∷ "c" ∷ "d" ∷ [])))

  ⟦_⟧² : S² → List String
  ⟦ act sig :: k ⟧² =
    "function " ∷ sig ∷ "() returns (" ∷
    fyi-returns (S¹-fyi-size k) ++ ") {\n" ∷
    ⟦ k ⟧¹ ++ "\n}" ∷ []
  ⟦ x₁ // x₂ ⟧² =
    ⟦ x₁ ⟧² ++ "\n" ∷ ⟦ x₂ ⟧²

  S²→Solidity : S² → String
  S²→Solidity s = Data.List.foldr Data.String._++_ "" ⟦ s ⟧²


open Sⁿ public
open Sic→EVM public
open Main public
