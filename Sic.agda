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
  open import Function   using (_∘_) public
  open import Data.Empty using (⊥) public
  open import Data.Unit  using (⊤) public
  open import Data.Bool  using (Bool; not; T) public
  open import Data.Maybe using (Maybe; maybe; just; nothing) public
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
    using (String; Costring)
    renaming ( _≟_ to _string≟_
             ; _++_ to _string++_
             ; fromList to stringFromList
             )
    public
  open import Data.Char
    using (Char)
    public

module Products where
  open import Data.Product
    using (_×_; _,_; ,_; Σ; proj₁; proj₂)
    public

module Sums where
  open import Data.Sum
    using (_⊎_; inj₁; inj₂)
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
             ; reverse   to reverseᵛ
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

module Sⁿ where
  open Basics
  open Relations
  open Naturals
  open Vectors
  open Lists
  open Strings

  data Arg : Set where $ : ℕ → Arg
  data Ref : Set where # : ℕ → Ref

  data Type : Set where
    Word : Type
    Slot : Type

  mutual

    -- S⁰, the set of Sic expressions
    data S⁰ : Type → Set where
      -_ ¬_               : Op₁ (S⁰ Word)
      _%+_ _%−_ _%×_      : Op₂ (S⁰ Word)
      _+_ _−_ _×_ _∙_ _^_ : Op₂ (S⁰ Word)
      _<_ _>_ _≥_ _≤_ _≡_ : Op₂ (S⁰ Word)
      _∨_ _∧_             : Op₂ (S⁰ Word)

      u     : S⁰ Word            -- The invoking user's ID
      t     : S⁰ Word            -- The current time
      nat_  : ℕ → S⁰ Word        -- A natural number literal
      at_   : ℕ → S⁰ Slot        -- A simple storage slot
      get_  : S⁰ Slot → S⁰ Word  -- Value of a storage slot
      ref_  : Ref → S⁰ Word      -- Value of a memory slot
      arg_  : Arg → S⁰ Word      -- Value of an argument
      ⟨_    : ⟨S⁰⟩ → S⁰ Slot     -- Hash of a sequence of values

    -- A nonempty list of S⁰ terms.
    data ⟨S⁰⟩ : Set where
      one-S⁰ : S⁰ Word → ⟨S⁰⟩
      _,_    : S⁰ Word → ⟨S⁰⟩ → ⟨S⁰⟩

    -- Some trickery to make ⟨ x₁ , x₂ , ... ⟩ work syntactically.
    _⟩ : S⁰ Word → ⟨S⁰⟩
    x ⟩ = one-S⁰ x

  -- An S¹ is “easy” if it doesn’t do any external calls.
  data Ease : Set where
    easy hard : Ease

  _⊔ᵉ_ : Op₂ Ease
  easy ⊔ᵉ easy = easy
  easy ⊔ᵉ hard = hard
  hard ⊔ᵉ easy = hard
  hard ⊔ᵉ hard = hard

  -- This is for checking that you don’t use “fyi” more than once
  -- in one action.
  fyi-ok : ℕ → ℕ → Set
  fyi-ok 0       _       = ⊤
  fyi-ok (suc _) 0       = ⊤
  fyi-ok (suc _) (suc _) = ⊥

  -- S¹, the set of Sic actions.
  -- The ℕ type parameter is the number of values returned via “fyi”.
  data S¹ : Ease → ℕ → Set where
    iff_ : S⁰ Word → S¹ easy 0
    _≜_  : ℕ → S⁰ Word → S¹ easy 0
    _←_  : S⁰ Slot → S⁰ Word → S¹ easy 0
    fyi  : ∀ {n} → (xs : Vec (S⁰ Word) (suc n)) → S¹ easy (suc n)
    ext  : ∀ {n} → String → S⁰ Word → Vec (S⁰ Word) n → S¹ hard 0
    _│_  : ∀ {m n i₁ i₂}
         → S¹ i₁ m → S¹ i₂ n → {_ : fyi-ok m n}
         → S¹ (i₁ ⊔ᵉ i₂) (m ⊔ n)

  S¹-fyi-size : ∀ {ease n} → S¹ ease n → ℕ
  S¹-fyi-size {_} {n} _ = n


  -- We define helpers for returning up to 4 values...
  module fyi-helpers where
    fyi₁ : S⁰ Word → S¹ easy 1
    fyi₂ : S⁰ Word → S⁰ Word → S¹ easy 2
    fyi₃ : S⁰ Word → S⁰ Word → S⁰ Word → S¹ easy 3
    fyi₄ : S⁰ Word → S⁰ Word → S⁰ Word → S⁰ Word → S¹ easy 4
    fyi₁ a = fyi (a ∷ᵛ []ᵛ)
    fyi₂ a b = fyi (a ∷ᵛ b ∷ᵛ []ᵛ)
    fyi₃ a b c = fyi (a ∷ᵛ b ∷ᵛ c ∷ᵛ []ᵛ)
    fyi₄ a b c d = fyi (a ∷ᵛ b ∷ᵛ c ∷ᵛ d ∷ᵛ []ᵛ)

  open fyi-helpers public

  -- ...and for calling externally with up to 4 values.
  module ext-helpers where
    extⁿ : String → S⁰ Word → List (S⁰ Word) → S¹ hard 0
    extⁿ s x xs = ext s x (fromListᵛ xs)

    ext₀ : String → S⁰ Word → S¹ hard 0
    ext₁ : String → S⁰ Word → S⁰ Word → S¹ hard 0
    ext₂ : String → S⁰ Word → S⁰ Word → S⁰ Word → S¹ hard 0
    ext₃ : String → S⁰ Word → S⁰ Word → S⁰ Word → S⁰ Word → S¹ hard 0
    ext₄ : String → S⁰ Word → S⁰ Word → S⁰ Word → S⁰ Word → S⁰ Word → S¹ hard 0
    ext₀ s x = extⁿ s x []
    ext₁ s x a = extⁿ s x [ a ]
    ext₂ s x a b = extⁿ s x ( a ∷ [ b ] )
    ext₃ s x a b c = extⁿ s x ( a ∷ b ∷ [ c ] )
    ext₄ s x a b c d = extⁿ s x ( a ∷ b ∷ c ∷ [ d ] )

  open ext-helpers public

  -- S², the set of Sic contracts with named actions.

  -- We apologize for using the somewhat gender-biased noun “guy”
  -- as the generic term for an external entity that acts on us.
  --
  -- However, note that Guy, as a metavariable, must be instantiated
  -- by some actual set of Alices and Bobs.
  --
  -- S² acts are defined by who is authorized to perform them.
  --
  -- When deploying a concrete system from an S² specification,
  -- you will provide the identity of each “guy” as a parameter
  -- to the deployment procedure.
  --
  data Some (Guy : Set) : Set where
    the : Guy → Some Guy
    anybody : Some Guy

  data S² (Guy : Set) (Act : Set) : Ease → Set where
    _can_::_
      : ∀ {ease n}
      → Some Guy
      → Act
      → S¹ ease n
      → S² Guy Act ease

    _//_
      : ∀ {ease₁ ease₂}
      → S² Guy Act ease₁
      → S² Guy Act ease₂
      → S² Guy Act (ease₁ ⊔ᵉ ease₂)

    case_then_else_
      : ∀ {ease₁ ease₂}
      → S⁰ Word
      → S² Guy Act ease₁
      → S² Guy Act ease₂
      → S² Guy Act (ease₁ ⊔ᵉ ease₂)

  -- Syntax precedence list

  infix  1 case_then_else_
  infixr 2 _//_
  infixr 3 _can_::_
  infixr 4 _│_

  infix  10 iff_ _≜_ _←_

  infixl 31 _∨_
  infixl 32 _∧_
  infixl 33 ¬_

  infixl 35 _≡_
  infixl 36 _≥_ _≤_ _<_ _>_

  infixl 40 _+_ _−_
  infixl 41 _∙_
  infixl 42 -_

  infix  50 get_ ref_ arg_ nat_

  infixr 60 ⟨_
  infixr 61 _,_
  infixr 62 _⟩


module OverloadedNumbers where
  open Naturals
  open Sⁿ

  -- We define a “type class” for overloading number literals.
  record IsNumber {a} (A : Set a) : Set a where
    field
      from-ℕ : ℕ → A

  open IsNumber {{...}} public

  instance
    ℕ-IsNumber    : IsNumber ℕ
    Word-IsNumber : IsNumber (S⁰ Word)
    Slot-IsNumber : IsNumber (S⁰ Slot)
    Ref-IsNumber  : IsNumber Ref
    Arg-IsNumber  : IsNumber Arg
    from-ℕ {{ℕ-IsNumber}}    n = n
    from-ℕ {{Word-IsNumber}} n = nat n
    from-ℕ {{Slot-IsNumber}} n = at n
    from-ℕ {{Ref-IsNumber}}  n = # n
    from-ℕ {{Arg-IsNumber}}  n = $ n

  {-# BUILTIN FROMNAT from-ℕ #-}


-- Section 3: Oⁿ, linearized versions of Sⁿ
--
-- The first phase of compiling is to linearize the recursive expressions;
-- thus, Oⁿ is Sⁿ with expressions flattened into “reverse Polish notation.”
--

module Oⁿ where
  open Basics
  open Naturals
  open Vectors
  open Lists
  open Strings
  open Sⁿ using (Some; the; anybody)

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
    ×ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    %+ₒ     : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    %−ₒ     : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    %×ₒ     : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ∙ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ^ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ≡ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ≥ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    ≤ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    >ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
    <ₒ      : ∀ {i}     → O⁰ (suc (suc i)) (suc i)
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

  data O² (Guy : Set) (Act : Set) : Set where
    actₒ  : Some Guy → Act → ℕ → O¹ → O² Guy Act
    seqₒ  : Op₂ (O² Guy Act)
    caseₒ : O⁰ 0 1 → Op₂ (O² Guy Act)

  map-O²-act : ∀ {Guy Act₁ Act₂} → (Act₁ → Act₂) → O² Guy Act₁ → O² Guy Act₂
  map-O²-act f (actₒ g s x₁ x₂) =
    actₒ g (f s) x₁ x₂
  map-O²-act f (seqₒ x y) =
    seqₒ (map-O²-act f x) (map-O²-act f y)
  map-O²-act f (caseₒ p x y) =
    caseₒ p (map-O²-act f x) (map-O²-act f y)

  map-O²-guy : ∀ {Guy₁ Guy₂ Act} → (Guy₁ → Guy₂) → O² Guy₁ Act → O² Guy₂ Act
  map-O²-guy f (actₒ (the guy) s x₁ x₂) =
    actₒ (the (f guy)) s x₁ x₂
  map-O²-guy f (actₒ anybody s x₁ x₂) =
    actₒ anybody s x₁ x₂
  map-O²-guy f (seqₒ x₁ x₂) =
    seqₒ (map-O²-guy f x₁) (map-O²-guy f x₂)
  map-O²-guy f (caseₒ p x₁ x₂) =
    caseₒ p (map-O²-guy f x₁) (map-O²-guy f x₂)

  infixr  5 _┆_
  infixr 10 _∥_

  -- In order to allocate memory (say, for EVM return values),
  -- we need to compute the memory requirements of operations.

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
    ⟦_⟧⁰ : ∀ {i T} → S⁰ T → O⁰ i (suc i)
    ⟦ ⟨ xs ⟧⁰      = ⟨S⁰⟩→O⁰ xs
    ⟦ at n ⟧⁰      = #ₒ n
    ⟦ nat n ⟧⁰     = #ₒ n
    ⟦ get x ⟧⁰     = ⟦ x ⟧⁰ ┆ getₖₒ
    ⟦ ref (# x) ⟧⁰ = refₒ x
    ⟦ arg ($ x) ⟧⁰ = argₒ x
    ⟦ u ⟧⁰         = callerₒ
    ⟦ t ⟧⁰         = timeₒ
    ⟦ x + y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ +ₒ
    ⟦ x − y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ −ₒ
    ⟦ x × y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ×ₒ
    ⟦ x %+ y ⟧⁰    = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ %+ₒ
    ⟦ x %− y ⟧⁰    = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ %−ₒ
    ⟦ x %× y ⟧⁰    = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ %×ₒ
    ⟦ x ∙ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ∙ₒ
    ⟦ x ^ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ^ₒ
    ⟦ x ∨ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ∨ₒ
    ⟦ x ∧ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ∧ₒ
    ⟦ x ≥ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ≥ₒ
    ⟦ x ≤ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ≤ₒ
    ⟦ x > y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ >ₒ
    ⟦ x < y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ <ₒ
    ⟦ x ≡ y ⟧⁰     = ⟦ y ⟧⁰ ┆ ⟦ x ⟧⁰ ┆ ≡ₒ
    ⟦ ¬ x ⟧⁰       = ⟦ x ⟧⁰ ┆ ¬ₒ
    ⟦ - x ⟧⁰       = #ₒ 0  ┆ ⟦ x ⟧⁰ ┆ −ₒ

  -- Compiling statement sequences
  ⟦_⟧¹ : ∀ {ease n} → S¹ ease n → O¹
  ⟦ iff x ⟧¹  = iffₒ ⟦ x ⟧⁰
  ⟦ fyi x ⟧¹  = fyiₒ (mapᵛ ⟦_⟧⁰ x)
  ⟦ ext s c a ⟧¹ = extₒ s (⟦_⟧⁰ c) (mapᵛ ⟦_⟧⁰ a)
  ⟦ i ≜ x ⟧¹  = defₒ i ⟦ x ⟧⁰
  ⟦ k ← x ⟧¹  = setₖₒ ⟦ k ⟧⁰ ⟦ x ⟧⁰
  ⟦ x │ y ⟧¹  = ⟦ x ⟧¹ ∥ ⟦ y ⟧¹

  -- Compiling signature dispatch sequences
  ⟦_⟧² : ∀ {ease Guy Act} → S² Guy Act ease → O² Guy Act
  ⟦ g can s :: k ⟧² =
    actₒ g s (S¹-fyi-size k) ⟦ k ⟧¹
  ⟦ a // b     ⟧² =
    seqₒ ⟦ a ⟧² ⟦ b ⟧²
  ⟦ case p then a else b ⟧² =
    caseₒ ⟦ p ⟧⁰ ⟦ a ⟧² ⟦ b ⟧²


  -- Some compile-time assertions
  private
    open Sⁿ
    open Relations

    S¹-memory : ∀ {ease n} → S¹ ease n → ℕ
    S¹-memory s = O¹-var-memory ⟦ s ⟧¹

    example-1 : S¹-memory {_} {0} (at 0 ← nat 0) ≣ 0
    example-1 = refl

    example-2 : S¹-memory {_} {0} (0 ≜ nat 0) ≣ 1
    example-2 = refl

    example-3 : S¹-memory {_} {0} (0 ≜ ref 1 + ref 2) ≣ 3
    example-3 = refl


-- Section 4: Reasoning about stack manipulations
--
-- We define a subset of the EVM stack operations for the purpose
-- of proving the stack effects of “pure” stack operations.
--
-- Later, we will use this to help write correct assembly snippets
-- for the Sic arithmetic helpers: overflow-safe signed addition, etc.
--

module StackReasoning (A : Set) where

  postulate
    -- The meaning of these operators don't matter for our reasoning,
    -- so we have them as postulates.
    _+_ _×_ _÷_ _%_ _<_ _>_ _==_ _⊕_ _∨_ _∧_ : A → A → A
    ¬ neg? : A → A
    two : A

  infixr 1 _⤇_
  infixr 2 _⟫_

  infix  21 _<_
  infixl 20 _∧_
  infixl 19 _∨_

  open import Data.List
    using (List; [])
    renaming (_∷_ to _,_) public
  open import Relation.Binary.PropositionalEquality
    using (_≡_; isEquivalence)

  -- We think of the set of stack actions as a relation ⤇ on stacks,
  -- defined by constructors corresponding to the EVM operators.
  --
  -- “X ⤇ Y” is inhabited iff there is some operator sequence that
  -- yields the stack Y when applied to the initial stack X.
  --
  -- Preorder reasoning on this relation is very useful!
  --
  -- The values of X ⤇ Y are “proof terms” of the relation.

  open Naturals

  infix 40 _¤_

  -- We represent a stack as a list and a gas cost,
  -- so that we can also reason about gas usage.
  record Stack (A : Set) : Set where
    constructor _¤_
    field
      gas   : ℕ
      stack : List A

  -- These are the current relevant Ethereum VM gas costs.
  base+    = λ g → 2 +ℕ g
  verylow+ = λ g → 3 +ℕ g
  low+     = λ g → 5 +ℕ g

  data _⤇_ : Stack A → Stack A → Set where
    -- Transitivity (action composition)
    _⟫_   : ∀ {a b c g₁ g₂ g₃}
          → g₁ ¤ a ⤇ g₂ ¤ b
          → g₂ ¤ b ⤇ g₃ ¤ c
          → g₁ ¤ a ⤇ g₃ ¤ c
    -- Reflexivity (needed for preorder)
    noop  : ∀ {a b g₁ g₂}   → g₁ ¤ a  ≡ g₂ ¤ b → g₁ ¤ a ⤇ g₂ ¤ b

    pop   : ∀ {a s g} → g ¤ (a , s) ⤇ base+ g ¤ s

    swap₁ : ∀ {a b s g}
      → g ¤ (a , b , s) ⤇ base+ g ¤ (b , a , s)
    swap₂ : ∀ {a b c s g}
      → g ¤ (a , b , c , s) ⤇ base+ g ¤ (c , b , a , s)
    swap₃ : ∀ {a b c d s g}
      → g ¤ (a , b , c , d , s) ⤇ base+ g ¤ (d , b , c , a , s)

    add   : ∀ {a b s g} → g ¤ (a , b , s) ⤇ verylow+ g ¤ ((a + b) , s)
    slt   : ∀ {a b s g} → g ¤ (a , b , s) ⤇ verylow+ g ¤ ((a < b) , s)
    sgt   : ∀ {a b s g} → g ¤ (a , b , s) ⤇ verylow+ g ¤ ((a > b) , s)
    eq    : ∀ {a b s g} → g ¤ (a , b , s) ⤇ verylow+ g ¤ ((a == b) , s)
    or    : ∀ {a b s g} → g ¤ (a , b , s) ⤇ verylow+ g ¤ ((a ∨ b) , s)
    and   : ∀ {a b s g} → g ¤ (a , b , s) ⤇ verylow+ g ¤ ((a ∧ b) , s)
    xor   : ∀ {a b s g} → g ¤ (a , b , s) ⤇ verylow+ g ¤ ((a ⊕ b) , s)
    mul   : ∀ {a b s g} → g ¤ (a , b , s) ⤇ low+ g     ¤ ((a × b) , s)
    sdiv  : ∀ {a b s g} → g ¤ (a , b , s) ⤇ low+ g     ¤ ((a ÷ b) , s)

    isneg  : ∀ {a s g} → g ¤ (a , s) ⤇ verylow+ (verylow+ g) ¤ (neg? a , s)
    iszero : ∀ {a s g} → g ¤ (a , s) ⤇ verylow+ g ¤ (¬ a , s)

    dup₁  : ∀ {g a s} → g ¤ (a , s) ⤇ base+ g ¤ (a , a , s)
    dup₂  : ∀ {g a b s} → g ¤ (a , b , s) ⤇ base+ g ¤ (b , a , b , s)
    dup₃  : ∀ {g a b c s} → g ¤ (a , b , c , s) ⤇ base+ g ¤ (c , a , b , c , s)
    dup₄  : ∀ {g a b c d s} → g ¤ (a , b , c , d , s) ⤇ base+ g ¤ (d , a , b , c , d , s)
    dup₅  : ∀ {g a b c d e s} → g ¤ (a , b , c , d , e , s) ⤇ base+ g ¤ (e , a , b , c , d , e , s)
    dup₆  : ∀ {g a b c d e f s} → g ¤ (a , b , c , d , e , f , s) ⤇ base+ g ¤ (f , a , b , c , d , e , f , s)
    dup₇  : ∀ {g a b c d e f h s} → g ¤ (a , b , c , d , e , f , h , s) ⤇ base+ g ¤ (h , a , b , c , d , e , f , h , s)

  -- Now we define the necessary algebraic structure
  -- for importing the preorder reasoning module.

  open import Relation.Binary

  ⤇-isPreorder : IsPreorder _≡_ _⤇_
  ⤇-isPreorder = record
    { isEquivalence = isEquivalence; reflexive = noop; trans = _⟫_ }

  ⤇-Preorder : Preorder _ _ _
  ⤇-Preorder = record
    { Carrier = Stack A; _≈_ = _≡_; _∼_ = _⤇_; isPreorder = ⤇-isPreorder }

  -- Finally we export the instantiated preorder reasoning module.
  open import Relation.Binary.PreorderReasoning ⤇-Preorder public

  private
    module Example where
      a,b⤇a+b,a,b : ∀ {a b ◎} → 0 ¤ (a , b , ◎) ⤇ 7 ¤ ((a + b) , a , b , ◎)
      a,b⤇a+b,a,b {a} {b} {◎} = begin
        0 ¤ (a , b , ◎)           ∼⟨ dup₂ ⟩
        2 ¤ (b , a , b , ◎)       ∼⟨ dup₂ ⟩
        4 ¤ (a , b , a , b , ◎)   ∼⟨ add ⟩
        7 ¤ ((a + b) , a , b , ◎) ∎


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
  open Vectors

  wordsize : ℕ
  wordsize = 32

  -- We use some reserved variables.
  %hash¹ = 0 * wordsize
  %hash² = 1 * wordsize
  %rpowˣ = 2 * wordsize
  %rpowⁿ = 3 * wordsize
  %rpowᶻ = 4 * wordsize

  -- Let mₒ be the first memory address for non-reserved variables.
  m₀ = %rpowᶻ +ℕ wordsize

  Addrᴱ = Vec Char 40

  infixr 10 _⟫_
  data Oᴱ : Set where
    NOOP : Oᴱ
    ADD SUB ADDRESS AND CALLDATALOAD CALL CALLER CODECOPY CODESIZE DIV EQ : Oᴱ
    EXP GAS ISZERO JUMPDEST KECCAK256 MLOAD MOD MSTORE MUL NOT OR POP : Oᴱ
    TIMESTAMP RETURN REVERT REVERTIF SDIV SGT SLOAD SLT SSTORE STOP XOR : Oᴱ

    DUP JUMP JUMPI SWAP PUSH : ℕ → Oᴱ

    PUSHSIG      : String → Oᴱ
    PUSHADDR     : Addrᴱ → Oᴱ
    ELSE         : Oᴱ → Oᴱ
    LOOP         : Oᴱ → Oᴱ → Oᴱ
    _⟫_          : Oᴱ → Oᴱ → Oᴱ
    tag          : O¹ → Oᴱ → Oᴱ

  -- The stack reasoning module is very useful for defining
  -- pure stack operations with verified stack effects,
  -- in particular the math snippets we’ll define later.

  open StackReasoning ℕ renaming (_⟫_ to _⟩_)

  private
    -- We can map stack reasoning proof terms to EVM opcode sequences.
    ⟦_⟧ : ∀ {a b} → a ⤇ b → Oᴱ
    ⟦ x₁ ⟩ x₂ ⟧ = ⟦ x₁ ⟧ ⟫ ⟦ x₂ ⟧
    ⟦ noop x ⟧  = NOOP
    ⟦ pop ⟧     = POP
    ⟦ add ⟧     = ADD
    ⟦ xor ⟧     = XOR
    ⟦ slt ⟧     = SLT
    ⟦ sgt ⟧     = SGT
    ⟦ mul ⟧     = MUL
    ⟦ sdiv ⟧    = SDIV
    ⟦ eq ⟧      = EQ
    ⟦ or ⟧      = OR
    ⟦ and ⟧     = AND
    ⟦ iszero ⟧  = ISZERO
    ⟦ isneg ⟧   = PUSH 0 ⟫ SGT
    ⟦ swap₁ ⟧   = SWAP 1
    ⟦ swap₂ ⟧   = SWAP 2
    ⟦ swap₃ ⟧   = SWAP 3
    ⟦ dup₁ ⟧    = DUP 1
    ⟦ dup₂ ⟧    = DUP 2
    ⟦ dup₃ ⟧    = DUP 3
    ⟦ dup₄ ⟧    = DUP 4
    ⟦ dup₅ ⟧    = DUP 5
    ⟦ dup₆ ⟧    = DUP 6
    ⟦ dup₇ ⟧    = DUP 7

  snippet : ∀ {a b} → a ⤇ b → Oᴱ
  snippet = ⟦_⟧


-- Section 6: EVM safe math and exponentiation
--
-- For the EVM, we define our own overflow safe arithmetic.
--
-- We also define multiplication, division, and exponentiation
-- on decimal fixed point numbers.
--

module EVM-Math where
  open EVM

  module _ where
    open Sⁿ
    iadd-bad? : S⁰ Word → S⁰ Word → S⁰ Word
    iadd-bad? x y =
        (x < 0 ∧ (y < 0 ∧ ((x %+ y) > x)))
      ∨ (x > 0 ∧ (y > 0 ∧ ((x %+ y) < x)))

  open Naturals

  open StackReasoning ℕ renaming (_⟫_ to _&_)


  IADD = snippet (impl 0 0 []) ⟫ REVERTIF
    where
      -- This overflow check formula comes from Hacker’s Delight, section 2.13.
      -- Z3 can prove it equivalent to a naïve formula; see “math.z3”.
      bad? = λ x y → neg? (((x + y) ⊕ x) ∧ ((x + y) ⊕ y))

      -- bad?′ = λ x y →
      --     ((neg? x) ∧ (neg? y) ∧ ((x + y) > x))
      --   ∨ (¬ (neg? x) ∧ ¬ (neg? y) ∧ (x + y) < x)

      gas-cost = 30 -- TODO: Optimize for eternal glory!

      -- impl′ : ∀ x y ∅ → 0 ¤ (x , y , ∅) ⤇ _ ¤ (bad?′ x y , x + y , ∅)
      -- impl′ x y ∅ = begin
      --     0 ¤ (x , y , ∅)
      --         ∼⟨ dup₁ & dup₃ & dup₃ & add & sgt ⟩
      --    12 ¤ ((x + y) > x , x , y , ∅)
      --         ∼⟨ dup₂ & isneg & dup₂ & isneg & and & and ⟩
      --    34 ¤ ((neg? x) ∧ (neg? y) ∧ ((x + y) > x) , x , y , ∅)
      --         ∼⟨ dup₃ & isneg & iszero & dup₃ & isneg & iszero ⟩
      --    -- 59 ¤ (¬ (neg? x) ∧ ¬ (neg? y) , ((x + y) > x) ∧ ((neg? x) ∧ (neg? y)) , x , y , ∅)
      --    --      ∼⟨ dup₃ & dup₅ & dup₅ & add & sgt & and & or ⟩
      --    {!!} ¤ {!!} ∼⟨ {!!} ⟩
      --    {!!} ¤ (((neg? x) ∧ neg? y ∧ ((x + y) > x))
      --            ∨ (¬ (neg? x) ∧ ¬ (neg? y) ∧ (x + y) < x) , x + y , ∅) ∎

      impl : ∀ x y ◎ → 0 ¤ (x , y , ◎) ⤇ gas-cost ¤ (bad? x y , x + y , ◎)
      impl x y ◎ = begin
         0 ¤ (x , y , ◎)                                 ∼⟨ dup₂ & dup₂ & add ⟩
         7 ¤ (x + y , x , y , ◎)                         ∼⟨ swap₂ ⟩
         9 ¤ (y , x , x + y , ◎)                         ∼⟨ dup₃ ⟩
        11 ¤ (x + y , y , x , x + y , ◎)                 ∼⟨ xor ⟩
        14 ¤ ((x + y) ⊕ y , x , x + y , ◎)               ∼⟨ swap₁ & dup₃ ⟩
        18 ¤ ((x + y) , x , (x + y) ⊕ y , x + y , ◎)     ∼⟨ xor ⟩
        21 ¤ ((x + y) ⊕ x , (x + y) ⊕ y , x + y , ◎)     ∼⟨ and ⟩
        24 ¤ (((x + y) ⊕ x) ∧ ((x + y) ⊕ y) , x + y , ◎) ∼⟨ isneg ⟩
        30 ¤ (bad? x y , x + y , ◎) ∎

  ISUB = SWAP 1 ⟫ PUSH 0 ⟫ SUB ⟫ IADD

  IMUL = snippet (×-impl 0 0 []) ⟫ REVERTIF
    where
      -- We check for multiplication overflow by verifying the division.
      ×-bad? = λ x y → ¬ (¬ y) ∧ (¬ (((x × y) ÷ y) == x))

      ×-impl : ∀ x y ◎ → 0 ¤ (x , y , ◎) ⤇ 46 ¤ (×-bad? x y , (x × y) , ◎)
      ×-impl = λ x y ◎ → begin
          0 ¤ (x , y , ◎)                          ∼⟨ dup₂ & dup₂ & mul ⟩
          9 ¤ ((x × y) , x , y , ◎)                ∼⟨ swap₂ & swap₁ ⟩
         13 ¤ (x , y , x × y , ◎)                  ∼⟨ dup₂ & dup₁ & dup₃ ⟩
         19 ¤ (x , y , y , x , y , x × y , ◎)      ∼⟨ mul ⟩
         24 ¤ (x × y , y , x , y , x × y , ◎)      ∼⟨ sdiv ⟩
         29 ¤ ((x × y) ÷ y , x , y , x × y , ◎)    ∼⟨ eq ⟩
         32 ¤ (((x × y) ÷ y) == x , y , x × y , ◎) ∼⟨ iszero & swap₁ & iszero & iszero & and ⟩
         46 ¤ (×-bad? x y , x × y , ◎) ∎

  RONE = PUSH 27 ⟫ PUSH 10 ⟫ EXP
  RHALF = PUSH 2 ⟫ RONE ⟫ SDIV
  RTRUNC = RONE ⟫ SWAP 1 ⟫ SDIV

  RMUL = IMUL ⟫ RHALF ⟫ IADD ⟫ RTRUNC

  EVEN = PUSH 1 ⟫ AND ⟫ ISZERO
  HALF = PUSH 2 ⟫ SWAP 1 ⟫ SDIV
  GETX = PUSH %rpowˣ ⟫ MLOAD
  SETX = PUSH %rpowˣ ⟫ MSTORE
  GETN = PUSH %rpowⁿ ⟫ MLOAD
  SETN = PUSH %rpowⁿ ⟫ MSTORE
  GETZ = PUSH %rpowᶻ ⟫ MLOAD
  SETZ = PUSH %rpowᶻ ⟫ MSTORE

  RPOW =
    SETX ⟫ SETN ⟫ RONE ⟫ SETZ ⟫
    GETX ⟫ ISZERO ⟫ GETN ⟫ ISZERO ⟫ AND ⟫ REVERTIF ⟫
    LOOP GETN (
      GETN ⟫ EVEN ⟫ ELSE (GETX ⟫ GETZ ⟫ RMUL ⟫ SETZ) ⟫
      GETX ⟫ GETX ⟫ RMUL ⟫ SETX ⟫ GETN ⟫ HALF ⟫ SETN
    ) ⟫ GETZ

    -- rpow(x, n) => z
    --   z = 1
    --   while (n)
    --     if n & 1
    --       z = rmul(z, x)
    --     x = rmul(x, x)
    --     n = n / 2

  RPOW′ =
    SWAP 1 ⟫ -- 2
    RONE ⟫ -- 3
    SWAP 1 ⟫ -- 3
    LOOP (DUP 1)
      (PUSH 1 ⟫
       DUP 2 ⟫
       AND ⟫
       ISZERO ⟫ ELSE (
         DUP 3 ⟫
         SWAP 1 ⟫
         SWAP 2 ⟫
         RMUL ⟫
         SWAP 1) ⟫
       SWAP 1 ⟫
       SWAP 2 ⟫
       DUP 1 ⟫
       RMUL ⟫
       PUSH 2 ⟫
       SWAP 1 ⟫
       DIV ⟫
       SWAP 1 ⟫
       SWAP 2 ⟫
       SWAP 1) ⟫
     POP ⟫ SWAP 1 ⟫ POP

{-
x n
n x
z(1) n x
n z x
LOOP
  1 n z x
  n 1 n z x
  n&1 n z x
  THEN
    x n z x
    n x z x
    z x n x
    z*x n x
    n z′ x
  z′ n x
  x n z′
  x x n z′
  x*x n z′
  2 n x′ z′
  n 2 x′ z′
  n/2 x′ z′
  x′ n′ z′
  z′ n′ x′
  n′ z′ x′
x′ n′ z′
n′ z′
z′
-}


-- Section 7: Compiling Sic machine code to EVM assembly
--

module Sic→EVM where
  open Sⁿ using (Some; the; anybody)
  open Oⁿ
  open EVM
  open EVM-Math

  open Naturals
  open FiniteSets
  open Vectors
  open Strings

  ⟦_⟧⁰ᵉ : ∀ {i j} → O⁰ i j → Oᴱ
  ⟦ #ₒ n    ⟧⁰ᵉ  = PUSH n
  ⟦ timeₒ   ⟧⁰ᵉ  = TIMESTAMP
  ⟦ x₁ ┆ x₂ ⟧⁰ᵉ  = ⟦ x₁ ⟧⁰ᵉ ⟫ ⟦ x₂ ⟧⁰ᵉ
  ⟦ callerₒ ⟧⁰ᵉ  = CALLER
  ⟦ refₒ x  ⟧⁰ᵉ  = PUSH (x * wordsize +ℕ m₀) ⟫ MLOAD
  ⟦ getₒ x  ⟧⁰ᵉ  = PUSH x ⟫ SLOAD
  ⟦ argₒ x  ⟧⁰ᵉ  = PUSH (4 +ℕ x * wordsize) ⟫ CALLDATALOAD
  ⟦ getₖₒ   ⟧⁰ᵉ  = SLOAD
  ⟦ +ₒ      ⟧⁰ᵉ  = IADD
  ⟦ −ₒ      ⟧⁰ᵉ  = ISUB
  ⟦ ×ₒ      ⟧⁰ᵉ  = IMUL
  ⟦ %+ₒ     ⟧⁰ᵉ  = ADD
  ⟦ %−ₒ     ⟧⁰ᵉ  = SUB
  ⟦ %×ₒ     ⟧⁰ᵉ  = MUL
  ⟦ ∙ₒ      ⟧⁰ᵉ  = RMUL
  ⟦ ^ₒ      ⟧⁰ᵉ  = RPOW
  ⟦ ≡ₒ      ⟧⁰ᵉ  = EQ
  ⟦ ≥ₒ      ⟧⁰ᵉ  = SLT ⟫ ISZERO
  ⟦ ≤ₒ      ⟧⁰ᵉ  = SGT ⟫ ISZERO
  ⟦ >ₒ      ⟧⁰ᵉ  = SGT
  ⟦ <ₒ      ⟧⁰ᵉ  = SLT
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

  constructor-prelude =
    PUSH 13 ⟫ CODESIZE ⟫ SUB ⟫ DUP 1 ⟫
    PUSH 13 ⟫ PUSH 0 ⟫ CODECOPY ⟫ PUSH 0 ⟫ RETURN

  return : ℕ → ℕ → Oᴱ
  return offset n =
    PUSH (n * wordsize) ⟫
    PUSH (m₀ +ℕ offset * wordsize) ⟫
    RETURN

  sig-check : String → ℕ → Oᴱ
  sig-check s n =
    PUSH 224 ⟫ PUSH 2 ⟫ EXP ⟫ PUSH 0 ⟫ CALLDATALOAD ⟫ DIV ⟫
    PUSHSIG s ⟫ EQ

  guy-check : Some Addrᴱ → Oᴱ
  guy-check (the x) = PUSHADDR x ⟫ CALLER ⟫ EQ
  guy-check anybody = PUSH 1

  ⟦_⟧²ᵉ : O² Addrᴱ String → Oᴱ
  ⟦ seqₒ a b   ⟧²ᵉ = ⟦ a ⟧²ᵉ ⟫ ⟦ b ⟧²ᵉ
  ⟦ actₒ guy s n k ⟧²ᵉ =
    guy-check guy ⟫ sig-check s n ⟫ AND ⟫
      let m₁ = O¹-var-memory k
          m₂ = m₁ +ℕ (O¹-fyi-memory k)
      in
        ISZERO ⟫ ELSE (⟦ k with-var m₁ with-fyi m₂ ⟧¹ᵉ ⟫ return m₁ n)
  ⟦ caseₒ p a b ⟧²ᵉ =
    ⟦ p ⟧⁰ᵉ ⟫ ELSE ⟦ b ⟧²ᵉ ⟫ ⟦ a ⟧²ᵉ

  open Sⁿ    using (S²)
  open Sⁿ→Oⁿ using (⟦_⟧²)

  S²→Oᴱ : ∀ {Guy Act ease}
        → (Guy → Addrᴱ)
        → (Act → String)
        → S² Guy Act ease → Oᴱ
  S²→Oᴱ f g s = prelude ⟫ ⟦ map-O²-guy f (map-O²-act g ⟦ s ⟧²) ⟧²ᵉ ⟫ REVERT

  S²→O² : ∀ {Guy Act ease} → S² Guy Act ease → O² Guy Act
  S²→O² x = ⟦ x ⟧²

  O²→Oᴱ : O² Addrᴱ String → Oᴱ
  O²→Oᴱ x = prelude ⟫ ⟦ x ⟧²ᵉ ⟫ REVERT

  compile : ∀ {ease} → S² Addrᴱ String ease → Oᴱ
  compile = S²→Oᴱ (λ x → x) (λ x → x)


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

module External where
  open import IO.Primitive renaming (IO to IO′)
  open Basics
  open Strings

  postulate
    ask : String → IO′ (Maybe String)
    keccak256 : String → String

  {-# FOREIGN GHC import qualified System.Environment as Env #-}
  {-# FOREIGN GHC import Data.Text (pack, unpack) #-}
  {-# COMPILE GHC ask = fmap (fmap pack) . Env.lookupEnv . unpack #-}

  {-# FOREIGN GHC import qualified Data.ByteString as BS #-}
  {-# FOREIGN GHC import qualified Data.ByteString.Lazy as LBS #-}
  {-# FOREIGN GHC import qualified Data.ByteString.Builder as B #-}
  {-# FOREIGN GHC import qualified Data.ByteString.Base16 as BS16 #-}
  {-# FOREIGN GHC import qualified EVM.Types as EVM #-}
  {-# FOREIGN GHC import EVM.Keccak (abiKeccak) #-}
  {-# FOREIGN GHC import Data.Text.Encoding (encodeUtf8, decodeUtf8) #-}

  {-# COMPILE GHC
        keccak256 = decodeUtf8
                  . BS16.encode
                  . BS.take 4
                  . LBS.toStrict
                  . B.toLazyByteString
                  . B.word32BE
                  . abiKeccak
                  . encodeUtf8 #-}

module EVM-Assembly where
  open Sic→EVM using (revert-jumpdest)
  open EVM
  open Naturals
  open Integers
  open Vectors
  open Strings
  open Products
  open External

  data B⁰ : ℕ → Set where
    B0    :          B⁰ 0
    B1    : ℕ      → B⁰ 1
    B2    : ℤ      → B⁰ 2
    BSig  : String → B⁰ 4
    BAddr : Addrᴱ  → B⁰ 20

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

  infixl 1 _⟩_

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
  code′ NOOP = , op B0
  code′ (tag o¹ oᴱ) = code′ oᴱ
  code′ (x₁ ⟫ x₂) = , (proj₂ (code′ x₁) ⦂ proj₂ (code′ x₂))
  code′ ADD = , op B1 0x01
  code′ ADDRESS = , op B1 0x30
  code′ AND = , op B1 0x16
  code′ CALLDATALOAD = , op B1 0x35
  code′ CALL = , op B1 0xf1
  code′ CALLER = , op B1 0x33
  code′ CODESIZE = , op B1 0x38
  code′ CODECOPY = , op B1 0x39
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
  code′ (PUSHADDR x) = , op B1 0x73 ⦂ op BAddr x
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
  ... | +_ i = fromList (replicate i '0') string++ s
  ... | ℤ.negsuc n₁ = "{erroneously-huge}"

  ℤ→hex : ℕ → ℤ → String
  ℤ→hex n (+_ x) = 0-pad n (Data.Nat.Show.showInBase 16 x)
    where import Data.Nat.Show
  ℤ→hex _ (ℤ.negsuc n) = "{erroneously-negative}"

  B⁰⋆→String : B⁰⋆ → String
  B⁰⋆→String (B0     ⟩ x₁) = B⁰⋆→String x₁
  B⁰⋆→String (B1   x ⟩ x₁) = ℤ→hex 2 (+ x) string++ B⁰⋆→String x₁
  B⁰⋆→String (B2   x ⟩ x₁) = ℤ→hex 4 x string++ B⁰⋆→String x₁
  B⁰⋆→String (BSig x ⟩ x₁) = keccak256 x string++ B⁰⋆→String x₁
  B⁰⋆→String (BAddr x ⟩ x₁) =
    stringFromList (toListᵛ x) string++ B⁰⋆→String x₁
  B⁰⋆→String fin = ""

module Linking where
  open Sⁿ
  open Oⁿ
  open EVM
  open EVM-Assembly
  open Sic→EVM
  open External

  open Basics
  open Strings

  import IO.Primitive
  open import IO
  open import Coinduction

  open Naturals
  open Vectors
  open Lists
  open EVM

  data ID : Set where
    parameter : String → ID
    hardcoded : Addrᴱ  → ID
    construct : ID

  fixed-width : (A : Set) → (n : ℕ) → List A → Maybe (Vec A n)
  fixed-width _ ℕ.zero [] = just []ᵛ
  fixed-width _ ℕ.zero (x ∷ xs) = nothing
  fixed-width _ (suc n) [] = nothing
  fixed-width A (suc n) (x ∷ xs) with fixed-width A n xs
  ... | nothing = nothing
  ... | just xs′ = just (x ∷ᵛ xs′)

  addr : String → Maybe Addrᴱ
  addr s = fixed-width Char 40 (Data.String.toList s)
    where import Data.String

  -- Resolve parameters via I/O environment variables.
  resolve : ID → IO (Maybe Addrᴱ)
  resolve (parameter x) =
    ♯ lift (ask x) >>= λ y →
      ♯ IO.return (maybe addr nothing y)
  resolve (hardcoded x) = IO.return (just x)
  resolve (construct) = IO.return nothing

  -- Resolve all the guys in an O² using I/O.
  resolve-O²
    : ∀ {guy act}
    → (guy → ID)
    → O² guy act
    → IO (Maybe (O² Addrᴱ act))
  resolve-O² f (actₒ anybody a n x) =
    IO.return (just (actₒ anybody a n x))
  resolve-O² f (actₒ (the g) a n x) =
    ♯ resolve (f g) >>= maybe
        (λ g′ → ♯ IO.return (just (actₒ (the g′) a n x)))
        (♯ IO.return nothing)
  resolve-O² f (seqₒ x₁ x₂) =
    ♯ resolve-O² f x₁ >>= maybe
        (λ y₁′ → ♯
          (♯ resolve-O² f x₂ >>= maybe
               (λ y₂′ → ♯ IO.return (just (seqₒ y₁′ y₂′)))
               (♯ IO.return nothing)))
        (♯ IO.return nothing)
  resolve-O² f (caseₒ p x₁ x₂) =
    ♯ resolve-O² f x₁ >>= maybe
      (λ y₁′ → ♯
        (♯ resolve-O² f x₂ >>= maybe
          (λ y₂′ → ♯ IO.return (just (caseₒ p y₁′ y₂′)))
          (♯ IO.return nothing)))
      (♯ IO.return nothing)

  compile-and-assemble
    : ∀ {Guy Act ease}
    → (Guy → Addrᴱ)
    → (Act → String)
    → S² Guy Act ease → String
  compile-and-assemble f₁ f₂ s² =
    B⁰⋆→String (⋆ (code (S²→Oᴱ f₁ f₂ s²)))

  assemble : Oᴱ → String
  assemble x = B⁰⋆→String (⋆ (code x))

  compile-and-link
    : ∀ {Guy Act ease}
    → (Guy → ID)
    → (Act → String)
    → S² Guy Act ease
    → IO (Maybe Oᴱ)
  compile-and-link f₁ f₂ x =
    ♯ resolve-O² f₁ (map-O²-act f₂ (S²→O² x)) >>=
        maybe
          (λ y → ♯ (IO.return (just (O²→Oᴱ y))))
          (♯ IO.return nothing)

  assemble-and-print : IO (Maybe Oᴱ) → IO ⊤
  assemble-and-print io = ♯ io >>=
    maybe
      (λ x → ♯ putStrLn (assemble constructor-prelude string++ assemble x))
      (♯ putStrLn "Error: linking failed.")

  link_with-guys_with-acts
    : ∀ {Guy Act ease}
    → S² Guy Act ease
    → (Guy → ID)
    → (Act → String)
    → IO.Primitive.IO ⊤
  link x with-guys f₁ with-acts f₂ =
    run (assemble-and-print (compile-and-link f₁ f₂ x))


-- Section 9: Dappsys, free stuff for dapp developers
--
-- We now define a “standard library” in the Sic language.
--

module Dappsys where
  open Sⁿ

  root = get ⟨ 0 , u ⟩ ≡ 1

  x₁ x₂ x₃ x₄ x₅ : S⁰ Word
  x₁ = arg 0; x₂ = arg 1; x₃ = arg 2; x₄ = arg 3; x₅ = arg 4

  v = x₁

  _↑_ : S⁰ Slot → S⁰ Word → S¹ easy 0
  _↓_ : S⁰ Slot → S⁰ Word → S¹ easy 0
  _↥_ : S⁰ Slot → S⁰ Word → S¹ easy 0
  _↧_ : S⁰ Slot → S⁰ Word → S¹ easy 0

  n ↑ v = n ← get n + v
  n ↥ v = n ← get n + v │ iff get n ≥ 0
  n ↓ v = n ↑ (- v)
  n ↧ v = n ↥ (- v)

  -- The “move statement” which subtracts and adds the same quantity
  -- to different places, failing if either place becomes negative.
  _↧_↥_ : S⁰ Slot → S⁰ Slot → S⁰ Word → S¹ easy 0
  k₁ ↧ k₂ ↥ v = (k₁ ↧ v) │ (k₂ ↥ v)

  infix 19 _↧_↥_


-- Now we open up our modules to users of the language.
open Basics public
open Strings public
open OverloadedNumbers public
open Sⁿ public
open Sic→EVM public
open External public
open Linking public
open EVM-Assembly public
open EVM public
