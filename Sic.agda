--     Sic: A smart contract language and its compiler to EVM
--
-- Copyright © 2018  Mikael Brockman, Daniel Brockman, Rainy McRainface
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU Affero General Public License as
-- published by the Free Software Foundation, either version 3 of the
-- License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU Affero General Public License for more details.

module Sic where


-- Section: External dependencies
--
-- We use a bunch of definitions from the standard library.
-- For clarity, we divide our imports into custom bundles,
-- which we can then easily open as needed.
--

module Naturals where
  open import Data.Nat
    using (ℕ; suc; _⊔_; _*_; compare; _≤?_)
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
  open import Relation.Nullary
    using (yes; no) public
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
             ; _++_      to _++ᵛ_
             ; allFin    to allFinᵛ
             ; zip       to zipᵛ
             ; reverse   to reverseᵛ
             ; tabulate  to tabulateᵛ
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


-- Section: Sic syntax data types
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

  data Arg  : Set where $$ : ℕ → Arg
  data Ref  : Set where ## : ℕ → Ref
  data Type : Set where Word Slot : Type

  -- S⁰, the set of Sic expressions
  mutual
    data S⁰ : Type → Set where
      _+_ _−_ _×_ _∙_ _^_ _<_ _>_ _≥_ _≤_ _≡_ _∨_ _∧_ : Op₂ (S⁰ Word)
      -_ ¬_ : Op₁ (S⁰ Word)
      u : S⁰ Word                    -- The invoking user's ID
      t : S⁰ Word                    -- The current time
      ray : S⁰ Word                  -- The ray 1.0
      nat : ℕ → S⁰ Word              -- A natural number literal
      at_ : ℕ → S⁰ Slot              -- A simple storage slot
      scoped : ℕ → S⁰ Slot           -- A scoped slot
      member : S⁰ Slot → ℕ → S⁰ Slot -- A slot with index
      get_ : S⁰ Slot → S⁰ Word       -- Value of a storage slot
      #  : Ref → S⁰ Word             -- Value of a memory slot
      $  : Arg → S⁰ Word             -- Value of an argument
      ⟨_ : ⟨S⁰⟩ → S⁰ Slot            -- Hash of a sequence of values

    -- A nonempty list of S⁰ terms.
    data ⟨S⁰⟩ : Set where
      one  : S⁰ Word → ⟨S⁰⟩
      _,_ : ⟨S⁰⟩ → S⁰ Word → ⟨S⁰⟩

  -- S¹, the set of Sic actions.
  mutual
    data S¹ : ℕ → Set where
      iff_    : S⁰ Word → S¹ 0
      _≜_     : Ref → S⁰ Word → S¹ 0
      _←_     : S⁰ Slot → S⁰ Word → S¹ 0
      [≥0]_←_ : S⁰ Slot → S⁰ Word → S¹ 0
      fyiᵛ    : ∀ {n} → (xs : Vec (S⁰ Word) n) → S¹ n
      _│_     : ∀ {m n} → S¹ m → S¹ n → {_ : fyi-ok m n} → S¹ (m ⊔ n)
      scope!  : S⁰ Slot → S¹ 0

    -- (Only one fyi per S¹.)
    fyi-ok : ℕ → ℕ → Set
    fyi-ok 0       _       = ⊤
    fyi-ok (suc _) 0       = ⊤
    fyi-ok (suc _) (suc _) = ⊥

  -- S², the set of Sic contracts with named actions.
  data S² (Guy : Set) (Act : Set) : Set where
    _⟶_ : ∀ {n} → Act → S¹ n → S² Guy Act
    _&_ : S² Guy Act → S² Guy Act → S² Guy Act
    case_then_else_ : S⁰ Word → S² Guy Act → S² Guy Act → S² Guy Act
    auth_∷_ : Guy → S² Guy Act → S² Guy Act

  infix   1  case_then_else_
  infixr  2  _&_
  infixr  3  _⟶_
  infixr  4  _│_
  infix  10  iff_ _≜_ _←_ [≥0]_←_
  infixl 31  _∨_
  infixl 32  _∧_
  infixl 33  ¬_
  infixl 35  _≡_
  infixl 36  _≥_ _≤_ _<_ _>_
  infixl 40  _+_ _−_
  infixl 41  _∙_ _×_
  infixl 42  -_
  infix  50  get_
  infixr 60  ⟨_
  infixr 61  _,_


-- Section: Functions that recursively analyze Sⁿ terms
--

module Sⁿ-analysis where
  open Sⁿ
  open Naturals
  open Vectors

  S¹-fyi-size : ∀ {n} → S¹ n → ℕ
  S¹-fyi-size {n} _ = n

  mutual
    S⁰-memory-usage : ∀ {t} → S⁰ t → ℕ
    S⁰-memory-usage (- x)        = S⁰-memory-usage x
    S⁰-memory-usage (¬ x)        = S⁰-memory-usage x
    S⁰-memory-usage (x + y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x − y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x × y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x ∙ y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x ^ y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x < y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x > y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x ≥ y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x ≤ y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x ≡ y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x ∨ y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage (x ∧ y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
    S⁰-memory-usage u            = 0
    S⁰-memory-usage t            = 0
    S⁰-memory-usage ray          = 0
    S⁰-memory-usage (nat x)      = 0
    S⁰-memory-usage (at x)       = 0
    S⁰-memory-usage (scoped x)   = 0
    S⁰-memory-usage (member x i) = S⁰-memory-usage x
    S⁰-memory-usage (get x)      = S⁰-memory-usage x
    S⁰-memory-usage (# (## x))   = suc x
    S⁰-memory-usage ($ x)        = 0
    S⁰-memory-usage (⟨ x)        = ⟨S⁰⟩-memory-usage x

    ⟨S⁰⟩-memory-usage : ⟨S⁰⟩ → ℕ
    ⟨S⁰⟩-memory-usage (one x)  = S⁰-memory-usage x
    ⟨S⁰⟩-memory-usage (xs , x) = S⁰-memory-usage x ⊔ ⟨S⁰⟩-memory-usage xs

  S¹-memory-usage : ∀ {n} → S¹ n → ℕ
  S¹-memory-usage (iff x)           = S⁰-memory-usage x
  S¹-memory-usage (## i ≜ x)        = suc i ⊔ S⁰-memory-usage x
  S¹-memory-usage (x ← y)           = S⁰-memory-usage x ⊔ S⁰-memory-usage y
  S¹-memory-usage ([≥0] x ← y)      = S⁰-memory-usage x ⊔ S⁰-memory-usage y
  S¹-memory-usage (fyiᵛ []ᵛ)        = 0
  S¹-memory-usage (fyiᵛ v@(_ ∷ᵛ _)) = foldr₁ᵛ _⊔_ (mapᵛ S⁰-memory-usage v)
  S¹-memory-usage (x │ y)           = S¹-memory-usage x ⊔ S¹-memory-usage y
  S¹-memory-usage (scope! x)        = S⁰-memory-usage x

  transform-S²
    : ∀ {G₁ G₂ A₁ A₂} → (G₁ → G₂) → (A₁ → A₂)
    → S² G₁ A₁ → S² G₂ A₂
  transform-S² f₁ f₂ (a ⟶ x) =
    f₂ a ⟶ x
  transform-S² f₁ f₂ (x & y) =
    transform-S² f₁ f₂ x & transform-S² f₁ f₂ y
  transform-S² f₁ f₂ (case p then x else y) =
    case p then transform-S² f₁ f₂ x else transform-S² f₁ f₂ y
  transform-S² f₁ f₂ (auth a ∷ x) =
    auth (f₁ a) ∷ transform-S² f₁ f₂ x


-- Section: Metaprogramming utilities
--
-- We extend the Agda environment with some useful stuff.
--

module Varargs where
  open Naturals
  open Vectors

  -- See example below.
  _of_to_ : (n : ℕ) → Set → Set → Set
  ℕ.zero of t₁ to t₂ = t₂
  suc n  of t₁ to t₂ = t₁ → n of t₁ to t₂

  private
    example : 3 of ℕ to ℕ
    example a b c = a * b * c

  -- We can convert a vector-taking function to a vararg function.
  curryᵛ : ∀ {n a b} → (Vec a n → b) → n of a to b
  curryᵛ {ℕ.zero} f = f []ᵛ
  curryᵛ {suc n} f = λ x → curryᵛ λ v → f (x ∷ᵛ v)

  -- And the other way around.
  uncurryᵛ : ∀ {n a b} → n of a to b → Vec a n → b
  uncurryᵛ f []ᵛ = f
  uncurryᵛ f (x ∷ᵛ v) = uncurryᵛ (f x) v

  private
    open Relations
    uncurryᵛ-curryᵛ≡id
      : ∀ {n a b} → (f : Vec a n → b) → (v : Vec a n)
      → uncurryᵛ (curryᵛ f) v ≣ f v
    uncurryᵛ-curryᵛ≡id f []ᵛ = refl
    uncurryᵛ-curryᵛ≡id f (x ∷ᵛ v) = uncurryᵛ-curryᵛ≡id (λ y → f (x ∷ᵛ y)) v

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
    from-ℕ {{Ref-IsNumber}}  n = ## n
    from-ℕ {{Arg-IsNumber}}  n = $$ n

  {-# BUILTIN FROMNAT from-ℕ #-}



-- Section: Higher-level Sⁿ combinators
--
-- We now define a “standard library” in the Sic language.
--

module Dappsys where
  open Sⁿ
  open Naturals
  open Varargs
  open Vectors
  open FiniteSets

  -- Make it easier to use calldata.
  ♯ : ∀ {t} → (n : ℕ) → (n of S⁰ Word to t) → t
  ♯ n f = uncurryᵛ f (mapᵛ (λ i → $ ($$ (toℕ i))) (allFinᵛ n))

  -- Nice syntax for methods using calldata.
  ¶ : ∀ {i A G} → A → (n : ℕ) → n of S⁰ Word to S¹ i → S² G A
  ¶ a b c = a ⟶ ♯ b c

  -- Return with varargs.
  fyi : (n : ℕ) → n of S⁰ Word to S¹ n
  fyi n = curryᵛ {n} fyiᵛ

  -- Should these be built into S¹?
  _↑_ : S⁰ Slot → S⁰ Word → S¹ 0
  _↓_ : S⁰ Slot → S⁰ Word → S¹ 0
  _↥_ : S⁰ Slot → S⁰ Word → S¹ 0
  _↧_ : S⁰ Slot → S⁰ Word → S¹ 0
  n ↑ v = n ← get n + v
  n ↥ v = n ← get n + v │ iff get n ≥ 0
  n ↓ v = n ↑ (- v)
  n ↧ v = n ↥ (- v)

  -- The “move statement” which subtracts and adds the same quantity
  -- to different places, failing if either place becomes negative.
  _↧_↥_ : S⁰ Slot → S⁰ Slot → S⁰ Word → S¹ 0
  k₁ ↧ k₂ ↥ v = (k₁ ↧ v) │ (k₂ ↥ v)

  infix 19 _↧_↥_ _↧_ _↥_

module Storage where
  open Sⁿ
  open Naturals
  open Vectors
  open Varargs
  open FiniteSets

  private
    Vec→⟨S⁰⟩ : ∀ {n} → Vec (S⁰ Word) (suc n) → ⟨S⁰⟩
    Vec→⟨S⁰⟩ (x ∷ᵛ []ᵛ)    = one x
    Vec→⟨S⁰⟩ (x ∷ᵛ y ∷ᵛ v) = Vec→⟨S⁰⟩ (y ∷ᵛ v) , x

    fmap
      : ∀ {t t₁ t₂} → (n : ℕ) → (t₁ → t₂)
      → n of t to t₁
      → n of t to t₂
    fmap ℕ.zero f x = f x
    fmap (suc n) f x = λ a → fmap n f (x a)

  slot_∷_ : ∀ {t : Set} → ℕ → (S⁰ Slot → t) → t
  slot k ∷ f = f (at k)

  open Products renaming (_,_ to _and_)

  -- This is so higher-order I had to lease a new quiet office space
  -- to even think about implementing it.  The logic is not complex,
  -- but we jump through hoops to get the desired syntax at the use site:
  --
  --   slot k maps 2 to 3 ∷ λ foo a b c →
  --     foo ($ 0) ($ 1) 7 8 9  λ aᵢⱼ bᵢⱼ cᵢⱼ →
  --       a i j ← aᵢⱼ + bᵢⱼ ∙ cᵢⱼ
  --
  -- In this example, we define a 2D mapping to a 3-field struct.
  --
  -- foo is bound to a full-struct loader that takes 2+3+1 arguments:
  -- first the mapping indices to load; then a memory index for each field;
  -- and finally a 3-parameter function that gets called with memory getters.
  --
  -- The variables a, b, and c are bound to slot functions, such that
  -- a i j is the slot ⟨ k , i , j , 0 ⟩, and so on.
  --
  slot_∷_×_∷_ : ∀ {t : Set}
    → (k m n : ℕ)
    → (m of S⁰ Word to
        (n of Ref to
          (∀ {x} → n of S⁰ Word to S¹ x → S¹ x))
        → n of (m of S⁰ Word to S⁰ Slot) to t)
    → t
  slot k ∷ m × n ∷ cont =
    uncurryᵛ
      (cont (fmap m curryᵛ (curryᵛ with-loader)))
      (tabulateᵛ λ i → curryᵛ {m} λ v → k-slot v i)

    where
      -- Make the slot ⟨ ⟨ k , v₁ , ... , vₘ ⟩ , i ⟩.
      k-slot : Vec (S⁰ Word) m → Fin n → S⁰ Slot
      k-slot v i = member (⟨ (Vec→⟨S⁰⟩ (reverseᵛ (nat k ∷ᵛ v)))) (toℕ i)

      -- Make the slot prefix ⟨ k , v₁ , ... , vₘ ⟩.
      k-scope : Vec (S⁰ Word) m → S⁰ Slot
      k-scope v = ⟨ Vec→⟨S⁰⟩ (reverseᵛ (nat k ∷ᵛ v))

      with-loader
        : Vec (S⁰ Word) m
        → Vec Ref n
        → ∀ {x} → (n of S⁰ Word to S¹ x)
        → S¹ x
      with-loader ixs []ᵛ g = g  -- Degenerate case of zero struct fields.
      with-loader ixs refs@(_ ∷ᵛ _) g =
        let
          setup =
            -- Build something like
            --
            --     scope! ⟨ k , ixs... ⟩
            --   │ ref₁ ≜ get (scoped 0)
            --   │ ref₂ ≜ get (scoped 1)
            --   │ ...
            --
            -- by mapping and folding the refs vector.
            scope! (k-scope ixs) │
            foldr₁ᵛ (λ s₁ s₂ → s₁ │ s₂)
              (mapᵛ (λ { (i and r) → r ≜ get (scoped (toℕ i)) })
                (zipᵛ (allFinᵛ n) refs))

          proceed =
            -- Call the body function with the memory load expressions.
            uncurryᵛ g (mapᵛ # refs)

        in setup │ proceed

      f₂ : Vec (m of S⁰ Word to S⁰ Slot) n
      f₂ = tabulateᵛ λ i → curryᵛ {m} λ v → k-slot v i


-- Section: Reasoning about stack manipulations
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
    minInt : A

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

    -- XXX: this gas cost is a lie until we implement big word pushing
    minint : ∀ {s g} → g ¤ s ⤇ verylow+ g ¤ (minInt , s)

    dup₁ : ∀ {g a s} → g ¤ (a , s)
              ⤇ base+ g ¤ (a , a , s)
    dup₂ : ∀ {g a b s} → g ¤ (a , b , s)
              ⤇ base+ g ¤ (b , a , b , s)
    dup₃ : ∀ {g a b c s} → g ¤ (a , b , c , s)
              ⤇ base+ g ¤ (c , a , b , c , s)
    dup₄ : ∀ {g a b c d s} → g ¤ (a , b , c , d , s)
              ⤇ base+ g ¤ (d , a , b , c , d , s)
    dup₅ : ∀ {g a b c d e s} → g ¤ (a , b , c , d , e , s)
              ⤇ base+ g ¤ (e , a , b , c , d , e , s)
    dup₆ : ∀ {g a b c d e f s} → g ¤ (a , b , c , d , e , f , s)
              ⤇ base+ g ¤ (f , a , b , c , d , e , f , s)
    dup₇ : ∀ {g a b c d e f h s} → g ¤ (a , b , c , d , e , f , h , s)
              ⤇ base+ g ¤ (h , a , b , c , d , e , f , h , s)

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


-- Section: EVM assembly
--
-- We now introduce a data type denoting EVM assembly.
--
-- Our EVM assembly type has the control flow structures LOOP and ELSE
-- which are taken care of later by the bytecode assembler.
--

module EVM where
  open Sⁿ
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
  %sig   = 5 * wordsize
  %scope = 6 * wordsize

  -- Let mₒ be the first memory address for non-reserved variables.
  m₀ = %scope +ℕ wordsize

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
    tag          : ∀ {n} → S¹ n → Oᴱ → Oᴱ

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
    ⟦ minint ⟧  = PUSH 255 ⟫ PUSH 2 ⟫ EXP
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


-- Section: EVM safe math and exponentiation
--
-- For the EVM, we define our own overflow safe arithmetic.
--
-- We also define multiplication, division, and exponentiation
-- on decimal fixed point numbers.
--

module EVM-Math where
  open EVM
  open Naturals
  open StackReasoning ℕ renaming (_⟫_ to _&_)

  IADD = snippet (impl 0 0 []) ⟫ REVERTIF
    where
      -- This overflow check formula comes from Hacker’s Delight, section 2.13.
      -- Z3 can prove it equivalent to a naïve formula; see “math.z3”.
      -- You can understand it by thinking about the sign bits...
      overflow? = λ x y → neg? (((x + y) ⊕ x) ∧ ((x + y) ⊕ y))

      impl : ∀ x y ◎ → 0 ¤ (x , y , ◎) ⤇ 30 ¤ (overflow? x y , x + y , ◎)
      impl x y ◎ = begin
         0 ¤ (x , y , ◎)                                 ∼⟨ dup₂ & dup₂ & add ⟩
         7 ¤ (x + y , x , y , ◎)                         ∼⟨ swap₂ & dup₃ & xor ⟩
        14 ¤ ((x + y) ⊕ y , x , x + y , ◎)               ∼⟨ swap₁ & dup₃ & xor ⟩
        21 ¤ ((x + y) ⊕ x , (x + y) ⊕ y , x + y , ◎)     ∼⟨ and & isneg ⟩
        30 ¤ (overflow? x y , x + y , ◎) ∎

  IMUL = snippet (impl 0 0 []) ⟫ ISZERO ⟫ REVERTIF
    where
      -- We check for multiplication overflow by verifying the division.
      no-overflow? = λ x y →
        (¬ (neg? y) ∨ (minInt < x)) ∧ (¬ y ∨ ((x × y) ÷ y) == x)

      impl : ∀ x y ◎ →
            0 ¤ (x , y , ◎)
        ⤇ 62 ¤ (no-overflow? x y , (x × y) , ◎)
      impl =
        λ x y ◎ → begin
          0 ¤ (x , y , ◎)
            ∼⟨ dup₂ & dup₂ & mul & swap₂ & swap₁ ⟩
          13 ¤ (x , y , (x × y) , ◎)
            ∼⟨ dup₁ & dup₃ & dup₅ & sdiv & eq ⟩
          27 ¤ ((((x × y) ÷ y) == x) , x , y , (x × y) , ◎)
            ∼⟨ dup₃ & iszero & or & swap₂ & swap₁ ⟩
          39 ¤ (x , y , ¬ y ∨ (((x × y) ÷ y) == x) , (x × y) , ◎)
            ∼⟨ minint & slt & swap₁ & isneg & iszero & or & and ⟩
          62 ¤ (no-overflow? x y , x × y , ◎) ∎

  ISUB = SWAP 1 ⟫ PUSH 0 ⟫ SUB ⟫ IADD
  RONE = PUSH 27 ⟫ PUSH 10 ⟫ EXP
  RHALF = PUSH 2 ⟫ RONE ⟫ SDIV
  RTRUNC = RONE ⟫ SWAP 1 ⟫ SDIV
  RMUL =
    IMUL ⟫ RHALF ⟫ PUSH 0 ⟫ DUP 3 ⟫ SLT ⟫
    PUSH 0 ⟫ NOT ⟫ MUL ⟫ MUL ⟫ IADD ⟫ RTRUNC

  {-
    Pseudocode for RPOW:
       rpow(x, n) => z
         z = 1
         revert if (x, n) == (0, 0)
         revert if n < 0
         while n
           z = rmul(z, x) if n is odd
           n = n / 2
           x = rmul(x, x) if n > 0
  -}

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
    PUSH 0 ⟫ GETN ⟫ SLT ⟫ REVERTIF ⟫
    LOOP GETN (
      GETN ⟫ EVEN ⟫ ELSE (GETX ⟫ GETZ ⟫ RMUL ⟫ SETZ) ⟫
      GETN ⟫ HALF ⟫ SETN ⟫
      GETN ⟫ ISZERO ⟫ ELSE (GETX ⟫ GETX ⟫ RMUL ⟫ SETX)
    ) ⟫ GETZ


-- Section: Compiling Sic to EVM assembly
--

module Sic→EVM where
  open Sⁿ
  open Sⁿ-analysis
  open EVM
  open EVM-Math

  open Naturals
  open FiniteSets
  open Vectors
  open Strings

  hash-one : Oᴱ
  hash-one =
    PUSH %hash¹ ⟫ MSTORE ⟫ PUSH wordsize ⟫ PUSH 0 ⟫ KECCAK256

  hash-two : Oᴱ
  hash-two =
    PUSH %hash¹ ⟫ MSTORE ⟫ PUSH %hash² ⟫ MSTORE ⟫
    PUSH (2 * wordsize) ⟫ PUSH 0 ⟫ KECCAK256

  ⟦_⟧⁰ᵉ : ∀ {t} → S⁰ t → Oᴱ
  ⟦ - x ⟧⁰ᵉ           = PUSH 0 ⟫ ⟦ x ⟧⁰ᵉ ⟫ ISUB
  ⟦ ¬ x ⟧⁰ᵉ           = ⟦ x ⟧⁰ᵉ ⟫ ISZERO
  ⟦ x + y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ IADD
  ⟦ x − y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ ISUB
  ⟦ x × y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ IMUL
  ⟦ x ∙ y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ RMUL
  ⟦ x ^ y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ RPOW
  ⟦ x < y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ SLT
  ⟦ x > y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ SGT
  ⟦ x ≥ y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ SLT ⟫ ISZERO
  ⟦ x ≤ y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ SGT ⟫ ISZERO
  ⟦ x ≡ y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ EQ
  ⟦ x ∨ y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ OR
  ⟦ x ∧ y ⟧⁰ᵉ         = ⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ AND
  ⟦ u ⟧⁰ᵉ             = CALLER
  ⟦ t ⟧⁰ᵉ             = TIMESTAMP
  ⟦ ray ⟧⁰ᵉ           = RONE
  ⟦ nat x ⟧⁰ᵉ         = PUSH x
  ⟦ at x ⟧⁰ᵉ          = PUSH x
  ⟦ scoped x ⟧⁰ᵉ      = PUSH x ⟫ PUSH %scope ⟫ MLOAD ⟫ ADD
  ⟦ member x i ⟧⁰ᵉ    = ⟦ x ⟧⁰ᵉ ⟫ PUSH i ⟫ ADD
  ⟦ get x ⟧⁰ᵉ         = ⟦ x ⟧⁰ᵉ ⟫ SLOAD
  ⟦ # (## x) ⟧⁰ᵉ      = PUSH (m₀ +ℕ x * wordsize) ⟫ MLOAD
  ⟦ $ ($$ x) ⟧⁰ᵉ      = PUSH (4  +ℕ x * wordsize) ⟫ CALLDATALOAD
  ⟦ ⟨ one x ⟧⁰ᵉ       = ⟦ x ⟧⁰ᵉ ⟫ hash-one
  ⟦ ⟨ one x , y ⟧⁰ᵉ   = ⟦ x ⟧⁰ᵉ ⟫ ⟦ y ⟧⁰ᵉ ⟫ hash-two
  ⟦ ⟨ (x , y) , z ⟧⁰ᵉ = ⟦ ⟨ (x , y) ⟧⁰ᵉ ⟫ ⟦ z ⟧⁰ᵉ ⟫ hash-two

  S¹→Oᴱ : ∀ {n} → ℕ → S¹ n → Oᴱ
  S¹→Oᴱ m s@(iff x) =
    tag s (⟦ x ⟧⁰ᵉ ⟫ ISZERO ⟫ REVERTIF)
  S¹→Oᴱ m s@(## i ≜ x) =
    tag s (⟦ x ⟧⁰ᵉ ⟫ PUSH (m₀ +ℕ m * wordsize) ⟫ MSTORE)
  S¹→Oᴱ m s@(x ← y) =
    tag s (⟦ y ⟧⁰ᵉ ⟫ ⟦ x ⟧⁰ᵉ ⟫ SSTORE)
  S¹→Oᴱ m s@([≥0] x ← y) =
    tag s (⟦ y ⟧⁰ᵉ ⟫ DUP 1 ⟫ PUSH 0 ⟫ SGT ⟫ REVERTIF ⟫ ⟦ x ⟧⁰ᵉ ⟫ SSTORE)
  S¹→Oᴱ {0} m s@(fyiᵛ []ᵛ) =
    tag s NOOP
  S¹→Oᴱ {suc n} m s@(fyiᵛ v@(_ ∷ᵛ _)) =
    tag s
      (foldr₁ᵛ _⟫_
        (mapᵛ
          (λ { (i and x) → ⟦ x ⟧⁰ᵉ ⟫ PUSH (m +ℕ toℕ i * wordsize) ⟫ MSTORE })
          (zipᵛ (allFinᵛ (suc n)) v)))
     where open Products renaming (_,_ to _and_)
  S¹→Oᴱ m s@(scope! x) =
    tag s (⟦ x ⟧⁰ᵉ ⟫ PUSH %scope ⟫ MSTORE)
  S¹→Oᴱ m (x │ y) =
    S¹→Oᴱ m x ⟫ S¹→Oᴱ m y

  S¹→tagged-Oᴱ : ∀ {n} → ℕ → S¹ n → Oᴱ
  S¹→tagged-Oᴱ m x = tag x (S¹→Oᴱ m x)

  return : ℕ → ℕ → Oᴱ
  return _ 0 = STOP
  return offset n =
    PUSH (n * wordsize) ⟫
    PUSH (m₀ +ℕ offset * wordsize) ⟫
    RETURN

  ⟦_⟧²ᵉ : S² Addrᴱ String → Oᴱ
  ⟦ x & y ⟧²ᵉ = ⟦ x ⟧²ᵉ ⟫ ⟦ y ⟧²ᵉ
  ⟦ sig ⟶ x ⟧²ᵉ =
    let m = S¹-memory-usage x
        n = S¹-fyi-size x
    in PUSH %sig ⟫ MLOAD ⟫ PUSHSIG sig ⟫ EQ ⟫ ISZERO ⟫
       ELSE (S¹→Oᴱ m x ⟫ return m n)
  ⟦ case p then x else y ⟧²ᵉ =
    ⟦ p ⟧⁰ᵉ ⟫ ELSE ⟦ y ⟧²ᵉ ⟫ ⟦ x ⟧²ᵉ
  ⟦ auth a ∷ x ⟧²ᵉ =
    PUSHADDR a ⟫ CALLER ⟫ EQ ⟫ ISZERO ⟫ ELSE ⟦ x ⟧²ᵉ

  -- This prelude is inserted into every compiled S².
  prelude =
    JUMP 6 ⟫ JUMPDEST ⟫ REVERT ⟫ JUMPDEST ⟫
    PUSH 224 ⟫ PUSH 2 ⟫ EXP ⟫ PUSH 0 ⟫
    CALLDATALOAD ⟫ DIV ⟫ PUSH %sig ⟫ MSTORE

  -- This is the PC for jumping to the prelude’s revert.
  revert-jumpdest : ℕ
  revert-jumpdest = 4

  S²→Oᴱ : ∀ {Guy Act}
        → (Guy → Addrᴱ)
        → (Act → String)
        → S² Guy Act → Oᴱ
  S²→Oᴱ f g s = prelude ⟫ ⟦ transform-S² f g s ⟧²ᵉ ⟫ REVERT

  compile : S² Addrᴱ String → Oᴱ
  compile = S²→Oᴱ (λ x → x) (λ x → x)

  constructor-prelude : Oᴱ
  constructor-prelude =
    PUSH 13 ⟫ CODESIZE ⟫ SUB ⟫ DUP 1 ⟫
    PUSH 13 ⟫ PUSH 0 ⟫ CODECOPY ⟫ PUSH 0 ⟫ RETURN


-- Section: Assembling EVM assembly
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


-- This module is a bit hard to understand.
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
  open Relations

  code′ : Oᴱ → Σ ℕ B¹
  code′ NOOP         = , op B0
  code′ ADD          = , op B1 0x01
  code′ ADDRESS      = , op B1 0x30
  code′ AND          = , op B1 0x16
  code′ CALLDATALOAD = , op B1 0x35
  code′ CALL         = , op B1 0xf1
  code′ CALLER       = , op B1 0x33
  code′ CODESIZE     = , op B1 0x38
  code′ CODECOPY     = , op B1 0x39
  code′ EQ           = , op B1 0x14
  code′ GAS          = , op B1 0x5a
  code′ JUMPDEST     = , op B1 0x5b
  code′ (JUMP x)     = , op B1 0x61 ⦂ op B2 (+ x) ⦂ op B1 0x56
  code′ (JUMPI x)    = , op B1 0x61 ⦂ op B2 (+ x) ⦂ op B1 0x57
  code′ KECCAK256    = , op B1 0x20
  code′ MLOAD        = , op B1 0x51
  code′ MSTORE       = , op B1 0x52
  code′ MUL          = , op B1 0x02
  code′ MOD          = , op B1 0x06
  code′ EXP          = , op B1 0x0a
  code′ OR           = , op B1 0x17
  code′ (PUSH x) with x ≤? 255
  ... | yes _        = , op B1 0x60 ⦂ op B1 x
  ... | no _         = , op B1 0x61 ⦂ op B2 (+ x)
  code′ (PUSHSIG x)  = , op B1 0x63 ⦂ op BSig x
  code′ (PUSHADDR x) = , op B1 0x73 ⦂ op BAddr x
  code′ DIV          = , op B1 0x04
  code′ SDIV         = , op B1 0x05
  code′ SGT          = , op B1 0x13
  code′ SLOAD        = , op B1 0x54
  code′ SLT          = , op B1 0x12
  code′ NOT          = , op B1 0x19
  code′ ISZERO       = , op B1 0x15
  code′ POP          = , op B1 0x50
  code′ SSTORE       = , op B1 0x55
  code′ STOP         = , op B1 0x00
  code′ SUB          = , op B1 0x03
  code′ TIMESTAMP    = , op B1 0x42
  code′ (DUP x)      = , op B1 (0x7f +ℕ x)
  code′ (SWAP x)     = , op B1 (0x8f +ℕ x)
  code′ REVERT       = , op B1 0xfd
  code′ REVERTIF     = , op B1 0x60 ⦂ op B1 revert-jumpdest ⦂ op B1 0x57
  code′ RETURN       = , op B1 0xf3
  code′ XOR          = , op B1 0x18
  code′ (tag o¹ oᴱ)  = code′ oᴱ
  code′ (x₁ ⟫ x₂)    = , (proj₂ (code′ x₁) ⦂ proj₂ (code′ x₂))
  code′ (ELSE x) with code′ x
  ... | i , bs       = , op B1 0x61 ⦂ Δ (+ (i +ℕ skip)) ⦂ op B1 0x57 ⦂ bs ⦂ op B1 0x5b
    where skip       = 3
  code′ (LOOP p k) with code′ p
  ... | iₚ , bsₚ   with code′ k
  ... | iₖ , bsₖ     =
    , op B1 0x5b ⦂ bsₚ ⦂ op B1 0x15 ⦂ op B1 0x61 ⦂ Δ (+ (3 +ℕ iₖ +ℕ 4))
      ⦂ op B1 0x57 ⦂ bsₖ
      ⦂ op B1 0x61 ⦂ Δ (-ℤ (+ skip)) ⦂ op B1 0x56
      ⦂ op B1 0x5b
    where skip       = 1 +ℕ iₖ +ℕ 5 +ℕ iₚ +ℕ 1

  code : (o : Oᴱ) → B¹ (proj₁ (code′ o))
  code o = proj₂ (code′ o)

  open import Data.String
    using (String; toList; fromList)
    renaming (_++_ to _string++_)
  open import Data.List
    using (length; replicate)
  open import Data.Nat.Show
    using (showInBase)

  0-pad : ℕ → String → String
  0-pad n s with (+ n) -ℤ (+ length (toList s))
  ... | +_ i = fromList (replicate i '0') string++ s
  ... | ℤ.negsuc n₁ =
    "{erroneously-huge "
      string++ (showInBase 10 n)
      string++ " "
      string++ s
      string++ "}"

  ℤ→hex : ℕ → ℤ → String
  ℤ→hex n (+_ x)       = 0-pad n (showInBase 16 x)
  ℤ→hex _ (ℤ.negsuc n) = "{erroneously-negative}"

  B⁰⋆→String : B⁰⋆ → String
  B⁰⋆→String fin            = ""
  B⁰⋆→String (B0     ⟩ x₁)  = B⁰⋆→String x₁
  B⁰⋆→String (B1   x ⟩ x₁)  = ℤ→hex 2 (+ x) string++ B⁰⋆→String x₁
  B⁰⋆→String (B2   x ⟩ x₁)  = ℤ→hex 4 x string++ B⁰⋆→String x₁
  B⁰⋆→String (BSig x ⟩ x₁)  = keccak256 x string++ B⁰⋆→String x₁
  B⁰⋆→String (BAddr x ⟩ x₁) =
    stringFromList (toListᵛ x) string++ B⁰⋆→String x₁

module Linking where
  open Sⁿ
  open Sⁿ-analysis
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
      ♯ IO.return
          (maybe
            (λ s → maybe (λ a → just a) nothing (addr s))
            nothing y)
  resolve (hardcoded x) = IO.return (just x)
  resolve (construct) = IO.return nothing

  -- Resolve all the guys in an S² using I/O.
  resolve-S² : ∀ {G A} → (G → ID) → S² G A → IO (Maybe (S² Addrᴱ A))
  resolve-S² f (a ⟶ x) =
    IO.return (just (a ⟶ x))
  resolve-S² f (x & y) =
    ♯ resolve-S² f x >>= maybe
         (λ x′ → ♯
           (♯ resolve-S² f y >>= maybe
                (λ y′ → ♯ IO.return (just (x′ & y′)))
                (♯ IO.return nothing)))
         (♯ IO.return nothing)
  resolve-S² f (case p then x else y) =
    ♯ resolve-S² f x >>= maybe
         (λ x′ → ♯
           (♯ resolve-S² f y >>= maybe
                (λ y′ → ♯ IO.return (just (case p then x′ else y′)))
                (♯ IO.return nothing)))
         (♯ IO.return nothing)
  resolve-S² f (auth a ∷ x) =
    ♯ resolve (f a) >>= maybe
        (λ a′ → ♯
           (♯ resolve-S² f x >>= maybe
                 (λ x′ → ♯ IO.return (just (auth a′ ∷ x′)))
                 (♯ IO.return nothing)))
        (♯ IO.return nothing)

  compile-and-assemble
    : ∀ {Guy Act}
    → (Guy → Addrᴱ)
    → (Act → String)
    → S² Guy Act → String
  compile-and-assemble f₁ f₂ s² =
    B⁰⋆→String (⋆ (code (S²→Oᴱ f₁ f₂ s²)))

  assemble : Oᴱ → String
  assemble x = B⁰⋆→String (⋆ (code x))

  compile-and-link
    : ∀ {Guy Act}
    → (Guy → ID)
    → (Act → String)
    → S² Guy Act
    → IO (Maybe Oᴱ)
  compile-and-link f₁ f₂ x =
    ♯ resolve-S² f₁ (transform-S² (λ { g → g }) f₂ x) >>=
        maybe
          (λ y → ♯ (IO.return (just (compile y))))
          (♯ IO.return nothing)

  assemble-and-print : IO (Maybe Oᴱ) → IO ⊤
  assemble-and-print io = ♯ io >>=
    maybe
      (λ x → ♯ putStrLn (assemble constructor-prelude string++ assemble x))
      (♯ putStrLn "Error: linking failed.")

  link
    : ∀ {Guy Act}
    → S² Guy Act
    → (Guy → ID)
    → (Act → String)
    → IO.Primitive.IO ⊤
  link x f₁ f₂ =
    run (assemble-and-print (compile-and-link f₁ f₂ x))


-- Public modules for language users.

open Sⁿ public
open Dappsys public
open Storage public
open Strings public
open OverloadedNumbers public
open Sic→EVM public
open External public
open Linking public
open EVM-Assembly public
open EVM public

-- And that’s all, folks.
