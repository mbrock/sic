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

 ---------------------------------------------------------------------
 Copyright © 2018  Mikael Brockman, Daniel Brockman, Rainy McRainface

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU Affero General Public License as
 published by the Free Software Foundation, either version 3 of the
 License, or (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Affero General Public License for more details.

-}

module Sic where


-- Section 0: External dependencies
--
-- We use a bunch of definitions from the standard library.
-- For clarity, we divide our imports into custom bundles,
-- which we can then easily open as needed.
--

module Naturals where
  open import Data.Nat
    using (ℕ; suc; _⊔_; _*_)
    renaming (_+_ to _+ℕ_)
    public

module Integers where
  open import Data.Integer
    using (ℤ; +_)
    renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; -_ to -ℤ_)
    public

module Basics where
  open import Data.Empty using (⊥) public
  open import Data.Unit  using (⊤) public
  open import Data.Bool  using (Bool; not; T) public
  open import Algebra.FunctionProperties
    using (Op₁; Op₂)
    public

module Relations where
  open import Relation.Nullary.Decidable
    using (⌊_⌋) public
  open import Relation.Binary.PropositionalEquality
    using (refl)
    renaming (_≡_ to _≣_)
    public

module Strings where
  open import Data.String
    using (String)
    renaming (_≟_ to _string≟_; _++_ to _string++_)
    public

module Products where
  open import Data.Product
    using (_×_; _,_; ,_; Σ; proj₁; proj₂)
    public

module FiniteSets where
  open import Data.Fin using (Fin; toℕ) public

module Vectors where
  open import Data.Vec
    using (Vec)
    renaming ( map       to mapᵛ
             ; foldr₁    to foldr₁ᵛ
             ; foldr     to foldrᵛ
             ; toList    to toListᵛ
             ; fromList  to fromListᵛ
             ; []        to []ᵛ
             ; _∷_       to _∷ᵛ_
             ; allFin    to allFinᵛ
             ; zip       to zipᵛ
             )
    public

module Lists where
  open import Data.List
    using (List; []; [_]; _∷_; length; _++_;
           all; any; map; concatMap; intersperse; take;
           foldr; zip)
    public
  open import Data.List.NonEmpty
    using (List⁺; _∷⁺_)
    renaming ([_] to [_]⁺; length to length⁺)
    public


-- Section 1: Sic syntax data types
--
-- We define a hierarchy of syntax data types:
--
--   ● S⁰, the expressions (pure formulas);
--   ● S¹, the actions (decisions and updates); and
--   ● S², the contracts (combinations of named actions).
--
-- Defining S³ for multi-contract systems is an exercise for the reader.
--

module Sⁿ where
  open Basics
  open Relations
  open Naturals
  open Vectors
  open Lists
  open Strings

  data Arg : Set where $ : ℕ → Arg
  data Ref : Set where # : ℕ → Ref

  mutual

    -- S⁰, the set of Sic expressions
    data S⁰ : Set where
      -_ ¬_               : Op₁ S⁰   -- Unary negation
      _+_ _−_ _∙_ _^_     : Op₂ S⁰   -- Binary math
      _∨_ _∧_ _≥_ _≤_ _≡_ : Op₂ S⁰   -- Binary logic

      u     : S⁰            -- The invoking user's ID
      t     : S⁰            -- The current time
      nat_  : ℕ → S⁰        -- A natural number literal
      get_  : S⁰ → S⁰       -- Value of a storage slot
      ref_  : Ref → S⁰      -- Value of a memory slot
      arg_  : Arg → S⁰      -- Value of an argument
      ⟨_    : ⟨S⁰⟩ → S⁰     -- Hash of a sequence of values

    -- A nonempty list of S⁰ terms.
    data ⟨S⁰⟩ : Set where
      one-S⁰  : S⁰ → ⟨S⁰⟩
      _,_  : S⁰ → ⟨S⁰⟩ → ⟨S⁰⟩

    -- Some trickery to make ⟨ x₁ , x₂ , ... ⟩ work syntactically.
    _⟩ : S⁰ → ⟨S⁰⟩
    x ⟩ = one-S⁰ x

  mutual

    -- S¹, the set of Sic actions.
    -- The ℕ type parameter is the number of values returned via “fyi”.
    data S¹ : ℕ → Set where
      iff_ :      S⁰ → S¹ 0
      _≜_  : ℕ →  S⁰ → S¹ 0
      _←_  : S⁰ → S⁰ → S¹ 0
      fyi  : ∀ {n} → (xs : Vec S⁰ (suc n)) → S¹ (suc n)
      ext  : ∀ {n} → String → S⁰ → Vec S⁰ n → S¹ 0
      _│_  : ∀ {m n}
           → S¹ m → S¹ n → {_ : fyi-ok m n}
           → S¹ (m ⊔ n)

    -- This is for checking that you don’t use “fyi” more than once
    -- in one action.
    fyi-ok : ℕ → ℕ → Set
    fyi-ok 0       _       = ⊤
    fyi-ok (suc _) 0       = ⊤
    fyi-ok (suc _) (suc _) = ⊥

  S¹-fyi-size : ∀ {n} → S¹ n → ℕ
  S¹-fyi-size {n} _ = n


  -- We define helpers for returning up to 4 values...
  module fyi-helpers where
    fyi₁ : S⁰ → S¹ 1
    fyi₂ : S⁰ → S⁰ → S¹ 2
    fyi₃ : S⁰ → S⁰ → S⁰ → S¹ 3
    fyi₄ : S⁰ → S⁰ → S⁰ → S⁰ → S¹ 4
    fyi₁ a = fyi (a ∷ᵛ []ᵛ)
    fyi₂ a b = fyi (a ∷ᵛ b ∷ᵛ []ᵛ)
    fyi₃ a b c = fyi (a ∷ᵛ b ∷ᵛ c ∷ᵛ []ᵛ)
    fyi₄ a b c d = fyi (a ∷ᵛ b ∷ᵛ c ∷ᵛ d ∷ᵛ []ᵛ)

  open fyi-helpers public

  -- ...and for calling externally with up to 4 values.
  module ext-helpers where
    extⁿ : String → S⁰ → List S⁰ → S¹ 0
    extⁿ s x xs = ext s x (fromListᵛ xs)

    ext₀ : String → S⁰ → S¹ 0
    ext₁ : String → S⁰ → S⁰ → S¹ 0
    ext₂ : String → S⁰ → S⁰ → S⁰ → S¹ 0
    ext₃ : String → S⁰ → S⁰ → S⁰ → S⁰ → S¹ 0
    ext₄ : String → S⁰ → S⁰ → S⁰ → S⁰ → S⁰ → S¹ 0
    ext₀ s x = extⁿ s x []
    ext₁ s x a = extⁿ s x [ a ]
    ext₂ s x a b = extⁿ s x ( a ∷ [ b ] )
    ext₃ s x a b c = extⁿ s x ( a ∷ b ∷ [ c ] )
    ext₄ s x a b c d = extⁿ s x ( a ∷ b ∷ c ∷ [ d ] )

  open ext-helpers public

  sig : Set
  sig = String

  -- S², the set of Sic contracts with named actions.
  mutual
    data S² : Set where
      act_::_ : ∀ {n} → sig → S¹ n → S²
      _//_    : Op₂ S²
      case_then_else_ : S⁰ → Op₂ S²

    all-sigs : S² → List sig
    all-sigs (act s :: _) = s ∷ []
    all-sigs (x₁ // x₂) =
      all-sigs x₁ ++ all-sigs x₂
    all-sigs (case p then x₁ else x₂) =
      all-sigs x₁ ++ all-sigs x₂

    disjoint-sigs : S² → S² → Bool
    disjoint-sigs x y =
      all
        (λ s₁ → not (any (λ s₂ → ⌊ s₁ string≟ s₂ ⌋)
                       (all-sigs y)))
        (all-sigs x)

  -- Syntax precedence list

  infix  1 case_then_else_
  infixr 2 _//_
  infixr 3 act_::_
  infixr 4 _│_

  infix  10 iff_ _≜_ _←_

  infixl 31 _∨_
  infixl 32 _∧_
  infixl 33 ¬_

  infixl 35 _≡_
  infixl 36 _≥_

  infixl 40 _+_ _−_
  infixl 41 _∙_
  infixl 42 -_

  infix  50 get_ ref_ arg_

  infixr 60 ⟨_
  infixr 61 _,_
  infixr 62 _⟩

open Sⁿ using (sig)

module OverloadedNumbers where
  open Naturals
  open Sⁿ

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
  open Basics
  open Naturals
  open Vectors
  open Lists
  open Strings

  -- The O⁰ operations have stack effects, which we encode in the types.
  -- For example, the type of +ₒ denotes taking two items and leaving one.
  -- Sequences like a ┆ b ┆ c must be “well-formed.”

  data O⁰ : ℕ → ℕ → Set where
    _┆_     : ∀ {i j k} → O⁰ i j → O⁰ j k → O⁰ i k
    #ₒ      : ∀ {i} → ℕ → O⁰           i   (suc i)
    refₒ    : ∀ {i} → ℕ → O⁰           i   (suc i)
    getₒ    : ∀ {i} → ℕ → O⁰           i   (suc i)
    argₒ    : ∀ {i} → ℕ → O⁰           i   (suc i)
    callerₒ : ∀ {i}     → O⁰           i   (suc i)
    timeₒ   : ∀ {i}     → O⁰           i   (suc i)
    getₖₒ   : ∀ {i}     → O⁰      (suc i)  (suc i)
    H¹ₒ     : ∀ {i}     → O⁰      (suc i)  (suc i)
    H²ₒ     : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    +ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    −ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ∙ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ^ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ≡ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ≥ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ≤ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ¬ₒ      : ∀ {i}     → O⁰      (suc i)  (suc i)
    ∧ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ∨ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)

  data O¹ : Set where
    _∥_   : O¹ → O¹ → O¹
    iffₒ  :          O⁰ 0 1  → O¹
    setₖₒ : O⁰ 0 1 → O⁰ 0 1  → O¹
    defₒ  :      ℕ → O⁰ 0 1  → O¹
    setₒ  :      ℕ → O⁰ 0 1  → O¹
    fyiₒ  : ∀ {n} → Vec (O⁰ 0 1) (suc n) → O¹
    extₒ  : ∀ {n} → String → O⁰ 0 1 → Vec (O⁰ 0 1) n → O¹

  data O² (sig : Set) : Set where
    sigₒ  : sig → ℕ → O¹ → O² sig
    seqₒ  : Op₂ (O² sig)
    caseₒ : O⁰ 0 1 → Op₂ (O² sig)

  map-O²-sig : ∀ {sig₁ sig₂} → (sig₁ → sig₂) → O² sig₁ → O² sig₂
  map-O²-sig f (sigₒ s x₁ x₂) =
    sigₒ (f s) x₁ x₂
  map-O²-sig f (seqₒ x y) =
    seqₒ (map-O²-sig f x) (map-O²-sig f y)
  map-O²-sig f (caseₒ p x y) =
    caseₒ p (map-O²-sig f x) (map-O²-sig f y)

  infixr  5 _┆_
  infixr 10 _∥_

  -- In order to allocate memory (say, for EVM return values),
  -- we need to compute the memory requirements of operations.

  -- %%%M...R...X...

  O⁰-memory : ∀ {m n} → O⁰ m n → ℕ
  O⁰-memory (refₒ i)  = suc i
  O⁰-memory (o₁ ┆ o₂) = O⁰-memory o₁ ⊔ O⁰-memory o₂
  O⁰-memory x = 0

  O¹-var-memory : O¹ → ℕ
  O¹-var-memory (defₒ i x)    = suc i ⊔ O⁰-memory x
  O¹-var-memory (fyiₒ xs)     = foldr₁ᵛ _⊔_ (mapᵛ O⁰-memory xs)
  O¹-var-memory (extₒ s c xs) = foldrᵛ (λ _ → ℕ) _⊔_ 0 (mapᵛ O⁰-memory xs)
  O¹-var-memory (iffₒ x)      = O⁰-memory x
  O¹-var-memory (setₖₒ k x)   = O⁰-memory x
  O¹-var-memory (setₒ i x)    = O⁰-memory x
  O¹-var-memory (o₁ ∥ o₂)     = O¹-var-memory o₁ ⊔ O¹-var-memory o₂

  O¹-fyi-memory : O¹ → ℕ
  O¹-fyi-memory (fyiₒ {n} xs) = suc n
  O¹-fyi-memory (o₁ ∥ o₂) = O¹-fyi-memory o₁ ⊔ O¹-fyi-memory o₂
  O¹-fyi-memory _         = 0

-- Section 4: Compiling Sic to abstract machine code
--
-- This transformation is mostly a simple linearization,
-- since our abstract machine is based on Sic semantics.
--

module Sⁿ→Oⁿ where
  open Sⁿ
  open Oⁿ

  open Naturals
  open Vectors

  mutual
    ⟨S⁰⟩→O⁰ : ∀ {i} → ⟨S⁰⟩ → O⁰ i (suc i)
    ⟨S⁰⟩→O⁰ (one-S⁰ x) =              ⟦ x ⟧⁰ ┆ H¹ₒ
    ⟨S⁰⟩→O⁰ (x , xs)   = ⟨S⁰⟩→O⁰ xs ┆ ⟦ x ⟧⁰ ┆ H²ₒ

    -- Compiling expressions
    ⟦_⟧⁰ : ∀ {i} → S⁰ → O⁰ i (suc i)
    ⟦ ⟨ xs ⟧⁰      = ⟨S⁰⟩→O⁰ xs
    ⟦ nat n ⟧⁰     = #ₒ n
    ⟦ get x ⟧⁰     = ⟦ x ⟧⁰ ┆ getₖₒ
    ⟦ ref (# x) ⟧⁰ = refₒ x
    ⟦ arg ($ x) ⟧⁰ = argₒ x
    ⟦ u ⟧⁰         = callerₒ
    ⟦ t ⟧⁰         = timeₒ
    ⟦ x + y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ +ₒ
    ⟦ x − y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ −ₒ
    ⟦ x ∙ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ∙ₒ
    ⟦ x ^ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ^ₒ
    ⟦ x ∨ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ∨ₒ
    ⟦ x ∧ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ∧ₒ
    ⟦ x ≥ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ≥ₒ
    ⟦ x ≤ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ≤ₒ
    ⟦ x ≡ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ≡ₒ
    ⟦ ¬ x ⟧⁰       = ⟦ x ⟧⁰ ┆ ¬ₒ
    ⟦ - x ⟧⁰       = #ₒ 0  ┆ ⟦ x ⟧⁰ ┆ −ₒ

  -- Compiling statement sequences
  ⟦_⟧¹ : ∀ {n} → S¹ n → O¹
  ⟦ iff x ⟧¹  = iffₒ ⟦ x ⟧⁰
  ⟦ fyi x ⟧¹  = fyiₒ (mapᵛ ⟦_⟧⁰ x)
  ⟦ ext s c a ⟧¹ = extₒ s (⟦_⟧⁰ c) (mapᵛ ⟦_⟧⁰ a)
  ⟦ i ≜ x ⟧¹  = defₒ i ⟦ x ⟧⁰
  ⟦ k ← x ⟧¹  = setₖₒ ⟦ k ⟧⁰ ⟦ x ⟧⁰
  ⟦ x │ y ⟧¹  = ⟦ x ⟧¹ ∥ ⟦ y ⟧¹

  -- Compiling signature dispatch sequences
  ⟦_⟧² : S² → O² sig
  ⟦ act s :: k ⟧² =
    sigₒ s (S¹-fyi-size k) ⟦ k ⟧¹
  ⟦ a // b     ⟧² =
    seqₒ ⟦ a ⟧² ⟦ b ⟧²
  ⟦ case p then a else b ⟧² =
    caseₒ ⟦ p ⟧⁰ ⟦ a ⟧² ⟦ b ⟧²


  -- Some compile-time assertions
  private
    open Sⁿ
    open Relations

    S¹-memory : ∀ {n} → S¹ n → ℕ
    S¹-memory s = O¹-var-memory ⟦ s ⟧¹

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
  open Naturals
  open Strings

  data Oᴱ : Set where
    ADD          : Oᴱ
    ADDRESS      : Oᴱ
    AND          : Oᴱ
    CALLDATALOAD : Oᴱ
    CALL         : Oᴱ
    CALLER       : Oᴱ
    DIV          : Oᴱ
    DUP          : ℕ → Oᴱ
    EQ           : Oᴱ
    EXP          : Oᴱ
    GAS          : Oᴱ
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
  open Naturals

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

  open Naturals
  open FiniteSets
  open Vectors
  open Strings

  wordsize : ℕ
  wordsize = 32

  -- We use three reserved variables: two for hashing, one for RPOW.
  %hash¹ = 0 * wordsize
  %hash² = 1 * wordsize
  %rpowᶻ = 2 * wordsize

  -- Let mₒ be the first memory address for non-reserved variables.
  m₀ = %rpowᶻ +ℕ wordsize

  ⟦_⟧⁰ᵉ : ∀ {i j} → O⁰ i j → Oᴱ
  ⟦ #ₒ n    ⟧⁰ᵉ  = PUSH n
  ⟦ timeₒ   ⟧⁰ᵉ  = TIMESTAMP
  ⟦ x₁ ┆ x₂ ⟧⁰ᵉ  = ⟦ x₁ ⟧⁰ᵉ ⟫ ⟦ x₂ ⟧⁰ᵉ
  ⟦ callerₒ ⟧⁰ᵉ  = CALLER
  ⟦ refₒ x  ⟧⁰ᵉ  = PUSH (x * wordsize +ℕ m₀) ⟫ MLOAD
  ⟦ getₒ x  ⟧⁰ᵉ  = PUSH x ⟫ SLOAD
  ⟦ argₒ x  ⟧⁰ᵉ  = PUSH (x * wordsize) ⟫ CALLDATALOAD
  ⟦ getₖₒ   ⟧⁰ᵉ  = SLOAD
  ⟦ +ₒ      ⟧⁰ᵉ  = XADD
  ⟦ −ₒ      ⟧⁰ᵉ  = XSUB
  ⟦ ∙ₒ      ⟧⁰ᵉ  = RMUL
  ⟦ ^ₒ      ⟧⁰ᵉ  = RPOW′
  ⟦ ≡ₒ      ⟧⁰ᵉ  = EQ
  ⟦ ≥ₒ      ⟧⁰ᵉ  = SGT ⟫ ISZERO
  ⟦ ≤ₒ      ⟧⁰ᵉ  = SLT ⟫ ISZERO
  ⟦ ¬ₒ      ⟧⁰ᵉ  = ISZERO
  ⟦ ∧ₒ      ⟧⁰ᵉ  = AND
  ⟦ ∨ₒ      ⟧⁰ᵉ  = OR
  ⟦ H¹ₒ     ⟧⁰ᵉ  = PUSH %hash¹ ⟫ MSTORE ⟫
                    PUSH wordsize ⟫ PUSH 0 ⟫ KECCAK256
  ⟦ H²ₒ     ⟧⁰ᵉ  = PUSH %hash¹ ⟫ MSTORE ⟫
                    PUSH %hash² ⟫ MSTORE ⟫
                    PUSH (2 * wordsize) ⟫ PUSH 0 ⟫ KECCAK256

  open Products

  O⁰#→Oᴱ : ∀ {n} → ℕ → (Fin n × O⁰ 0 1) → Oᴱ
  O⁰#→Oᴱ i (j , x) = ⟦ x ⟧⁰ᵉ ⟫ PUSH (i +ℕ (toℕ j) * wordsize) ⟫ MSTORE

  fyiₒ→Oᴱ : ∀ {n} → ℕ → Vec (O⁰ 0 1) (suc n) → Oᴱ
  fyiₒ→Oᴱ {n} i xs =
    foldr₁ᵛ _⟫_ (mapᵛ (O⁰#→Oᴱ i) (zipᵛ (allFinᵛ (suc n)) xs))

  push-sig : String → Oᴱ
  push-sig s = PUSHSIG s ⟫ PUSH 224 ⟫ PUSH 2 ⟫ EXP ⟫ MUL

  extₒ→Oᴱ : ∀ {n} → ℕ → String → O⁰ 0 1 → Vec (O⁰ 0 1) n → Oᴱ
  extₒ→Oᴱ i s c []ᵛ = push-sig s ⟫ PUSH instart ⟫ MSTORE ⟫ call
                   where
                     insize = 4
                     instart = i
                     call = PUSH 0 ⟫ PUSH 0 ⟫ PUSH insize
                            ⟫ PUSH instart ⟫ PUSH 0 ⟫ ⟦ c ⟧⁰ᵉ
                            ⟫ GAS ⟫ CALL ⟫ ISZERO ⟫ REVERTIF
  extₒ→Oᴱ {n} i s c (x ∷ᵛ xs) = push-sig s ⟫ PUSH instart ⟫ MSTORE ⟫
   foldr₁ᵛ _⟫_
       (mapᵛ (O⁰#→Oᴱ (instart +ℕ 4)) (zipᵛ (allFinᵛ n) (x ∷ᵛ xs)))
     ⟫ call
   where
     open import Data.List.NonEmpty using (foldr₁; map; length)
     ys = (x ∷ᵛ xs)
     insize = 4 +ℕ wordsize * n
     instart = i
     call = PUSH 0 ⟫ PUSH 0 ⟫ PUSH insize
            ⟫ PUSH instart ⟫ PUSH 0 ⟫ ⟦ c ⟧⁰ᵉ
            ⟫ GAS ⟫ CALL ⟫ ISZERO ⟫ REVERTIF


  mutual
    O¹→Oᴱ′ : ℕ → ℕ → O¹ → Oᴱ
    O¹→Oᴱ′ m₁ m₂ (iffₒ o)      = ⟦ o ⟧⁰ᵉ ⟫ ISZERO ⟫ JUMPI 3
    O¹→Oᴱ′ m₁ m₂ (defₒ i x)    = ⟦ x ⟧⁰ᵉ ⟫ PUSH (i * wordsize +ℕ m₀) ⟫ MSTORE
    O¹→Oᴱ′ m₁ m₂ (setₒ i x)    = ⟦ x ⟧⁰ᵉ ⟫ PUSH i ⟫ SSTORE
    O¹→Oᴱ′ m₁ m₂ (setₖₒ k x)   = ⟦ x ⟧⁰ᵉ ⟫ ⟦ k ⟧⁰ᵉ ⟫ SSTORE
    O¹→Oᴱ′ m₁ m₂ (fyiₒ xs)     = fyiₒ→Oᴱ offset xs
      where offset = m₁ * wordsize +ℕ m₀
    O¹→Oᴱ′ m₁ m₂ (extₒ s c xs) = extₒ→Oᴱ offset s c xs
      where offset = m₂ * wordsize +ℕ m₀
    O¹→Oᴱ′ m₁ m₂ (o₁ ∥ o₂)     = ⟦ o₁ with-var m₁ with-fyi m₂ ⟧¹ᵉ ⟫
                                 ⟦ o₂ with-var m₁ with-fyi m₂ ⟧¹ᵉ

    ⟦_with-var_with-fyi_⟧¹ᵉ : O¹ → ℕ → ℕ → Oᴱ
    ⟦ o@(_ ∥ _) with-var m₁ with-fyi m₂ ⟧¹ᵉ = O¹→Oᴱ′ m₁ m₂ o
    ⟦ o with-var m₁ with-fyi m₂ ⟧¹ᵉ = tag o (O¹→Oᴱ′ m₁ m₂ o)

  -- This prelude is inserted into every compiled S².
  prelude = JUMP 6 ⟫ JUMPDEST ⟫ REVERT ⟫ JUMPDEST

  -- This is the PC for jumping to the prelude’s revert.
  revert-jumpdest : ℕ
  revert-jumpdest = 4

  return : ℕ → ℕ → Oᴱ
  return offset n =
    PUSH (n * wordsize) ⟫
    PUSH (m₀ +ℕ offset * wordsize) ⟫
    RETURN

  sig-check : String → ℕ → Oᴱ
  sig-check s n =
    PUSH 224 ⟫ PUSH 2 ⟫ EXP ⟫ PUSH 0 ⟫ CALLDATALOAD ⟫ DIV ⟫
    PUSHSIG s ⟫ EQ

  ⟦_⟧²ᵉ : O² String → Oᴱ
  ⟦ seqₒ a b   ⟧²ᵉ = ⟦ a ⟧²ᵉ ⟫ ⟦ b ⟧²ᵉ
  ⟦ sigₒ s n k ⟧²ᵉ =
    sig-check s n ⟫ ISZERO ⟫
      let m₁ = O¹-var-memory k
          m₂ = m₁ +ℕ (O¹-fyi-memory k)
      in
        ELSE (⟦ k with-var m₁ with-fyi m₂ ⟧¹ᵉ ⟫ return m₁ n)
  ⟦ caseₒ p a b ⟧²ᵉ =
    ⟦ p ⟧⁰ᵉ ⟫ ELSE ⟦ a ⟧²ᵉ ⟫ ⟦ b ⟧²ᵉ

  open Sⁿ    using (S²)
  open Sⁿ→Oⁿ using (⟦_⟧²)

  S²→Oᴱ : (sig → String) → S² → Oᴱ
  S²→Oᴱ f s = prelude ⟫ ⟦ map-O²-sig f ⟦ s ⟧² ⟧²ᵉ ⟫ REVERT

  compile : S² → Oᴱ
  compile = S²→Oᴱ (λ x → x)


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
  open Sic→EVM using (revert-jumpdest)

  open Naturals
  open Integers
  open Strings
  open Products

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
  code′ CALL = , op B1 0xf1
  code′ CALLER = , op B1 0x33
  code′ EQ = , op B1 0x14
  code′ GAS = , op B1 0x5a
  code′ JUMPDEST = , op B1 0x5b
  code′ (JUMP x)  = , op B1 0x61 ⦂ op B2 (+ x) ⦂ op B1 0x56
  code′ (JUMPI x) = , op B1 0x61 ⦂ op B2 (+ x) ⦂ op B1 0x57
  code′ (ELSE x) with code′ x
  ... | i , bs = , op B1 0x61 ⦂ Δ (+ (i +ℕ skip)) ⦂ op B1 0x57 ⦂ bs ⦂ op B1 0x5b
    where skip = 3
  code′ (LOOP p k) with code′ p
  ... | iₚ , bsₚ   with code′ k
  ... | iₖ , bsₖ =
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
  code′ REVERTIF = , op B1 0x60 ⦂ op B1 revert-jumpdest ⦂ op B1 0x57
  code′ RETURN = , op B1 0xf3
  code′ XOR = , op B1 0x18

  code : (o : Oᴱ) → B¹ (proj₁ (code′ o))
  code o = proj₂ (code′ o)

  open import Data.String
    using (String; toList; fromList)
    renaming (_++_ to _string++_)
  open import Data.List using (length; replicate)

  0-pad : ℕ → String → String
  0-pad n s with (+ n) -ℤ (+ length (toList s))
  0-pad n s | +_ i = fromList (replicate i '0') string++ s
  0-pad n s | ℤ.negsuc n₁ = "{erroneously-huge}"

  ℤ→hex : ℕ → ℤ → String
  ℤ→hex n (+_ x) = 0-pad n (Data.Nat.Show.showInBase 16 x)
    where import Data.Nat.Show
  ℤ→hex _ (ℤ.negsuc n) = "{erroneously-negative}"

  B⁰⋆→String : B⁰⋆ → String
  B⁰⋆→String (B1   x ⟩ x₁) = ℤ→hex 2 (+ x) string++ B⁰⋆→String x₁
  B⁰⋆→String (B2   x ⟩ x₁) = ℤ→hex 4 x string++ B⁰⋆→String x₁
  B⁰⋆→String (BSig x ⟩ x₁) =
    "[" string++ x string++ "]" string++ B⁰⋆→String x₁
  B⁰⋆→String fin = ""

module Main where
  open Sⁿ
  open EVM
  open EVM-Assembly
  open Sic→EVM

  open Strings

  open import IO

  compile-and-assemble : S² → String
  compile-and-assemble s² = B⁰⋆→String (⋆ (code (compile s²)))

  sic²evm = λ x → run (putStrLn (compile-and-assemble x))

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

  -- The “move statement” which subtracts and adds the same quantity
  -- to different places, failing if either place becomes negative.
  _↧_↥_ : S⁰ → S⁰ → S⁰ → S¹ 0
  k₁ ↧ k₂ ↥ v = (k₁ ↧ v) │ (k₂ ↥ v)

  infix 19 _↧_↥_


-- Section 8: Compiling to Solidity
--
-- We define a compiler from S² to Solidity source code.
--

module Solidity where
  open Sⁿ renaming (_,_ to _,,_)
  open Products
  open Naturals
  open Vectors
  open Lists
  open Strings

  open import Data.Nat.Show using () renaming (showInBase to show)

  mutual

    sequence : ⟨S⁰⟩ → List String
    sequence (one-S⁰ x) =
      "keccak256(" ∷ ⟦ x ⟧ˢ⁰ ++ ")" ∷ []
    sequence (x ,, s) =
      "keccak256(" ∷ ⟦ x ⟧ˢ⁰ ++ ", " ∷ sequence s ++ ")" ∷ []

    ⟦_⟧ˢ⁰ : S⁰ → List String
    ⟦ nat x ⟧ˢ⁰     = show 10 x ∷ []
    ⟦ u ⟧ˢ⁰         = "msg.sender" ∷ []
    ⟦ t ⟧ˢ⁰         = "block.timestamp" ∷ []
    ⟦ get x ⟧ˢ⁰     = "storage[" ∷ ⟦ x ⟧ˢ⁰ ++ "]" ∷ []
    ⟦ ref (# x) ⟧ˢ⁰ = "m" ∷ show 10 x ∷ []
    ⟦ arg ($ x) ⟧ˢ⁰ = "p" ∷ show 10 x ∷ []
    ⟦ ⟨ x ⟧ˢ⁰       = sequence x
    ⟦ x + x₁ ⟧ˢ⁰    = "(" ∷ ⟦ x ⟧ˢ⁰ ++ " + " ∷ ⟦ x₁ ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ x − x₁ ⟧ˢ⁰    = "(" ∷ ⟦ x ⟧ˢ⁰ ++ " - " ∷ ⟦ x₁ ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ x ∙ x₁ ⟧ˢ⁰    = "(" ∷ ⟦ x ⟧ˢ⁰ ++ " * " ∷ ⟦ x₁ ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ x ^ x₁ ⟧ˢ⁰    = "(" ∷ ⟦ x ⟧ˢ⁰ ++ " ^ " ∷ ⟦ x₁ ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ x ∨ x₁ ⟧ˢ⁰    = "(" ∷ ⟦ x ⟧ˢ⁰ ++ " || " ∷ ⟦ x₁ ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ x ∧ x₁ ⟧ˢ⁰    = "(" ∷ ⟦ x ⟧ˢ⁰ ++ " && " ∷ ⟦ x₁ ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ x ≥ x₁ ⟧ˢ⁰    = "(" ∷ ⟦ x ⟧ˢ⁰ ++ " >= " ∷ ⟦ x₁ ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ x ≤ x₁ ⟧ˢ⁰    = "(" ∷ ⟦ x ⟧ˢ⁰ ++ " <= " ∷ ⟦ x₁ ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ x ≡ x₁ ⟧ˢ⁰    = "(" ∷ ⟦ x ⟧ˢ⁰ ++ " == " ∷ ⟦ x₁ ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ ¬ x ⟧ˢ⁰       = "(!" ∷ ⟦ x ⟧ˢ⁰ ++ ")" ∷ []
    ⟦ - x ⟧ˢ⁰       = "(-" ∷ ⟦ x ⟧ˢ⁰ ++ ")" ∷ []

  ⟦_⟧ᶠʸⁱ : ∀ {n} → Vec S⁰ (suc n) → List String
  ⟦ xs ⟧ᶠʸⁱ = intersperse ""
               (concatMap f (zip (toListᵛ xs) ("a" ∷ "b" ∷ "c" ∷ "d" ∷ [])))
    where
      open Products
      f : S⁰ × String → List String
      f (x , k) =  k ∷ " = " ∷ ⟦ x ⟧ˢ⁰ ++ ";\n" ∷ []

  ⟦_⟧ˢ¹ : ∀ {n} → S¹ n → List String
  ⟦ iff x ⟧ˢ¹      = "require(" ∷ ⟦ x ⟧ˢ⁰ ++ " != 0);\n" ∷ []
  ⟦ ext x x₁ xs ⟧ˢ¹ = "" ∷ [] -- TODO
  -- ⟦ ext s c xs ⟧ˢ¹ = "require(" ∷ ⟦ x ⟧ˢ⁰ ++ ".call(bytes4(keccak256(\""
  --                    ∷ s ∷ "\"))));\n" ∷ []
  ⟦ i ≜ x ⟧ˢ¹      = "uint256 m" ∷ show 10 i ∷ " = " ∷ ⟦ x ⟧ˢ⁰ ++ ";\n" ∷ []
  ⟦ k ← x ⟧ˢ¹      = "store["  ∷ ⟦ k ⟧ˢ⁰ ++ "] = " ∷ ⟦ x ⟧ˢ⁰ ++ ";\n" ∷ []
  ⟦ fyi xs ⟧ˢ¹     = ⟦ xs ⟧ᶠʸⁱ
  ⟦ x₁ │ x₂ ⟧ˢ¹    = ⟦ x₁ ⟧ˢ¹ ++ "" ∷ ⟦ x₂ ⟧ˢ¹

  fyi-returns : ℕ → List String
  fyi-returns 0 = "() public" ∷ []
  fyi-returns n = "() public returns (" ∷ intersperse ", "
                   (map (λ x → "int256 " string++ x)
                    (take n ("a" ∷ "b" ∷ "c" ∷ "d" ∷ []))) ++ ")" ∷ []

  ⟦_⟧ˢ² : S² → List String
  ⟦ act sig :: k ⟧ˢ² =
    "function " ∷ sig ∷
    fyi-returns (S¹-fyi-size k) ++ " {\n" ∷
    ⟦ k ⟧ˢ¹ ++ "}" ∷ []
  ⟦ x₁ // x₂ ⟧ˢ² =
    ⟦ x₁ ⟧ˢ² ++ "\n" ∷ ⟦ x₂ ⟧ˢ²
  ⟦ case _ then _ else _ ⟧ˢ² =
    "S²-case-not-implemented;" ∷ []

  S²→Solidity : S² → String
  S²→Solidity s = "contract Anon {\n"
                  +++ "mapping (uint => uint) store;\n"
                  +++ (foldr _+++_ "" ⟦ s ⟧ˢ²)
                  +++ "\n}"
      where open import Data.String renaming (_++_ to _+++_)


-- Section 9: Experimental Sⁿ modifiers and combinators
--

module Combinatronics where
  open Sⁿ
  open Basics
  open Naturals
  open Vectors

  -- The “zone” functions change the storage access of Sⁿ terms
  -- by hashing them together with a given ℕ.

  zone⁰ : ℕ → Op₁ S⁰
  zone⁰ n (- s) = - (zone⁰ n s)
  zone⁰ n (¬ s) = ¬ (zone⁰ n s)
  zone⁰ n (x₁ + x₂) = zone⁰ n x₁ + zone⁰ n x₂
  zone⁰ n (x₁ − x₂) = zone⁰ n x₁ − zone⁰ n x₂
  zone⁰ n (x₁ ∙ x₂) = zone⁰ n x₁ ∙ zone⁰ n x₂
  zone⁰ n (x₁ ^ x₂) = zone⁰ n x₁ ^ zone⁰ n x₂
  zone⁰ n (x₁ ∨ x₂) = zone⁰ n x₁ ∨ zone⁰ n x₂
  zone⁰ n (x₁ ∧ x₂) = zone⁰ n x₁ ∧ zone⁰ n x₂
  zone⁰ n (x₁ ≥ x₂) = zone⁰ n x₁ ≥ zone⁰ n x₂
  zone⁰ n (x₁ ≤ x₂) = zone⁰ n x₁ ≤ zone⁰ n x₂
  zone⁰ n (x₁ ≡ x₂) = zone⁰ n x₁ ≡ zone⁰ n x₂
  zone⁰ n u = u
  zone⁰ n t = t
  zone⁰ n (nat i) = nat i
  zone⁰ n (get s) = get ⟨ (nat n) , zone⁰ n s ⟩
  zone⁰ n (ref x) = ref x
  zone⁰ n (arg x) = arg x
  zone⁰ n (⟨ x) = ⟨ x

  zone¹ : ∀ {n} → ℕ → Op₁ (S¹ n)
  zone¹ n (iff x) = iff (zone⁰ n x)
  zone¹ n (x ≜ x₁) = x ≜ zone⁰ n x₁
  zone¹ n (x ← x₁) = ⟨ (nat n) , zone⁰ n x ⟩ ← zone⁰ n x₁
  zone¹ n (fyi {m} xs) = fyi (mapᵛ (zone⁰ n) xs)
  zone¹ n (ext x x₁ x₂) = ext x (zone⁰ n x₁) (mapᵛ (zone⁰ n) x₂)
  zone¹ n (_│_ {m₁} {m₂} s₁ s₂ {ok}) =
    _│_ {m₁} {m₂} (zone¹ n s₁) (zone¹ n s₂) {ok}

  zone² : ℕ → Op₁ S²
  zone² n (act x :: x₁) =
    act x :: zone¹ n x₁
  zone² n (s₁ // s₂) =
    zone² n s₁ // zone² n s₂
  zone² n (case p then s₁ else s₂) =
    case (zone⁰ n p) then (zone² n s₁)
                     else (zone² n s₂)

  -- If we distinctly zone two S² terms, we can merge them
  -- without storage interference.
  _⊗_ : Op₂ S²
  x ⊗ y = zone² 0 x // zone² 1 y

  private
    open Relations

    ex-1 : (zone² 5 (act "foo" ::       0   ← get       1 )) ≣
                    (act "foo" :: ⟨ 5 , 0 ⟩ ← get ⟨ 5 , 1 ⟩)
    ex-1 = refl


-- Now we open up our modules to users of the language.
open Sⁿ public
open Sic→EVM public
open Main public
open OverloadedNumbers public
open Combinatronics public
