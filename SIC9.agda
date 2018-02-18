------------------------------------------------------------------------
-- ✿ SIC: Symbolic Instruction Code
--

module SIC9 where

-- Strings for ABI signatures
open import Agda.Builtin.String using (String)

open import Agda.Primitive using (lzero)
open import Algebra using (CommutativeRing)
open import Data.Bool.Base using (if_then_else_; Bool; true; false)
open import Data.Fin.Subset using (Subset)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_; _*_ to _×ℤ_; _<_ to _<ℤ_; _-_ to _−ℤ_)
open import Data.Integer.Properties using (+-*-commutativeRing; <-isStrictTotalOrder)
open import Data.List using (List; _∷_; [])
open import Data.String using (_++_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; _⊔_; suc) renaming (_≟_ to _≟ℕ_; _+_ to _+ℕ_; _*_ to _×ℕ_)
open import Data.Nat.Show using (showInBase)
open import Relation.Binary using (StrictTotalOrder; IsStrictTotalOrder; Rel)
open import Relation.Binary.Core renaming (_≡_ to _≋_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (any)

------------------------------------------------------------------------
-- ✿ Section 1
--     SIC syntax data types
--

mutual
  data S¹ : Set where
    #  : ℕ → S¹
    Uₐ : S¹
    &ₐ : S¹

    _+_ : S¹ → S¹ → S¹
    _−_ : S¹ → S¹ → S¹
    _×_ : S¹ → S¹ → S¹
    _∨_ : S¹ → S¹ → S¹
    _∧_ : S¹ → S¹ → S¹
    _≥_ : S¹ → S¹ → S¹
    _≡_ : S¹ → S¹ → S¹

    get   : ℕ → S¹
    ref   : ℕ → S¹
    arg   : ℕ → S¹
    getₖ_ : ⟨S¹⟩ → S¹
    sha_  : ⟨S¹⟩ → S¹

  data ⟨S¹⟩ : Set where
    ⟨⟩_  : S¹ → ⟨S¹⟩
    _,_  : S¹ → ⟨S¹⟩ → ⟨S¹⟩

$ : ℕ → S¹
$ i = arg i

⟨_ : ⟨S¹⟩ → ⟨S¹⟩
⟨ x = x

_⟩ : S¹ → ⟨S¹⟩
x ⟩ = ⟨⟩ x

⟨⟩-len : ⟨S¹⟩ → ℕ
⟨⟩-len x = {!!}

data Sig : Set where
  sig : String → ℕ → ℕ → Sig

_is_ : Sig → Sig → Bool
sig s₁ x₁ y₁ is sig s₂ x₂ y₂ = s₁ Data.String.== s₂

data S² : Set where
  iff_    : S¹ → S²
  def_≜_  : ℕ → S¹ → S²
  set_←_  : ℕ → S¹ → S²
  setₖ_←_ : ⟨S¹⟩ → S¹ → S²
  out_    : ⟨S¹⟩ → S²

data S³ : Set where
  _│_ : S² → S³ → S³
  _└  : S² → S³

data S⁵ : Set where
  ◎_┌_ : Sig → S³ → S⁵
  _⅋_  : S⁵ → S⁵ → S⁵

------------------------------------------------------------------------
-- ✿ Section 2
--     SIC operator precedence and fixity
--

infixr 1 _⅋_
infixr 2 ◎_┌_
infixr 3  _│_
infixl 4  _└

infix  10 iff_
infix  10 def_≜_
infix  10 set_←_
infix  10 setₖ_←_

infix  31 _∨_
infix  32 _∧_

infixl 35 _≡_
infixl 36 _≥_

infixl 40 _+_ _−_
infixl 41 _×_

infix  50 getₖ_
infix  50 sha_

infixr 60 ⟨_
infixr 61 _,_
infixr 62 _⟩

------------------------------------------------------------------------
-- ✿ Section 4
--     EV²M, the "Ethereum Virtual Virtual Machine"
--

-- Constants
data O⁰ : Set where
  nilₒ    : O⁰
  oneₒ    : O⁰
  callerₒ : O⁰
  calleeₒ : O⁰

-- Static getters
data O¹ : Set where
  refₒ  : ℕ → O¹
  getₒ  : ℕ → O¹
  argₒ  : ℕ → O¹
  sigₒ  : Sig → O¹

-- Dynamic getters
data O² : Set where
  getₖₒ : O²
  H¹ₒ   : O²

-- Binary operations
data O³ : Set where
  +ₒ  : O³
  −ₒ  : O³
  ×ₒ  : O³
  ≡ₒ  : O³
  ≥ₒ  : O³
  ∧ₒ  : O³
  ∨ₒ  : O³
  H²ₒ : O³

-- Consumers
data O⁴ : Set where
  iffₒ :       O⁴
  defₒ : ℕ   → O⁴
  setₒ : ℕ   → O⁴
  outₒ : ℕ   → O⁴

-- Dynamic setters
data O⁵ : Set where
  setₖₒ : O⁵

-- Composed operations with coherent stack effects
data Oⱽ : ℕ → ℕ → Set where
  o⁰   : ∀ {i} → O⁰ → Oⱽ           i   (suc i)    -- Consts
  o¹_  : ∀ {i} → O¹ → Oⱽ           i   (suc i)    -- Reads
  o²   : ∀ {i} → O² → Oⱽ      (suc i)  (suc i)    -- Uses
  o³_  : ∀ {i} → O³ → Oⱽ (suc (suc i)) (suc i)    -- Exprs
  o⁴_  : ∀ {i} → O⁴ → Oⱽ      (suc i)       i     -- Consumers
  o⁵_  : ∀ {i} → O⁵ → Oⱽ (suc (suc i))      i     -- Writes
  _∥_  : ∀ {i j k} → Oⱽ i j → Oⱽ j k → Oⱽ i k     -- Compose
  fork : ∀ {i j k} → Oⱽ i (suc i) → Oⱽ j k → Oⱽ j k
  done : Oⱽ 0 0                                   -- Finish

infixr 10 _∥_

op-ex1 : Oⱽ 0 0
op-ex1 =
    o⁰ oneₒ ∥ o⁰ oneₒ ∥ o³ +ₒ
  ∥ o⁰ oneₒ ∥ o³ +ₒ ∥ o⁴ setₒ 1
  ∥ done

------------------------------------------------------------------------
-- ✿ Section 5
--     “Compilers for the Sⁿ languages to EV²M assembly”
--

mutual
  -- Compiling left-associative hashing of expression sequences
  ⟨comp¹⟩ʰ : ∀ {i} → ⟨S¹⟩ → Oⱽ i (suc i)
  ⟨comp¹⟩ʰ (⟨⟩ x)   = comp¹ x ∥ o² H¹ₒ
  ⟨comp¹⟩ʰ (x , xs) = comp¹ x ∥ ⟨comp¹⟩ʰ xs ∥ o³ H²ₒ

  -- Compiling left-associative hashing of expression sequences
  ⟨comp¹⟩ᵒ : ∀ {i} → ℕ → ⟨S¹⟩ → Oⱽ i i
  ⟨comp¹⟩ᵒ i (⟨⟩ x)   = comp¹ x ∥ o⁴ outₒ i
  ⟨comp¹⟩ᵒ i (x , xs) = comp¹ x ∥ o⁴ outₒ i ∥ ⟨comp¹⟩ᵒ (suc i) xs

  -- Compiling expressions
  comp¹ : ∀ {i} → S¹ → Oⱽ i (suc i)
  comp¹ (# n)     = o⁰ oneₒ
  comp¹ Uₐ        = o⁰ callerₒ
  comp¹ &ₐ        = o⁰ calleeₒ
  comp¹ (get x)   = o¹ getₒ x
  comp¹ (ref x)   = o¹ refₒ x
  comp¹ (arg x)   = o¹ argₒ x
  comp¹ (getₖ k)  = ⟨comp¹⟩ʰ k ∥ o² getₖₒ
  comp¹ (sha k)   = ⟨comp¹⟩ʰ k
  comp¹ (x + y)   = comp¹ x ∥ comp¹ y ∥ o³ +ₒ
  comp¹ (x − y)   = comp¹ x ∥ comp¹ y ∥ o³ −ₒ
  comp¹ (x × y)   = comp¹ x ∥ comp¹ y ∥ o³ ×ₒ
  comp¹ (x ∨ y)   = comp¹ x ∥ comp¹ y ∥ o³ ∨ₒ
  comp¹ (x ∧ y)   = comp¹ x ∥ comp¹ y ∥ o³ ∧ₒ
  comp¹ (x ≥ y)   = comp¹ x ∥ comp¹ y ∥ o³ ≥ₒ
  comp¹ (x ≡ y)   = comp¹ x ∥ comp¹ y ∥ o³ ≡ₒ

-- Compiling statements
comp² : ∀ {i} → S² → Oⱽ i i
comp² (iff x)      = comp¹ x ∥ o⁴ iffₒ
comp² (def i ≜ x)  = comp¹ x ∥ o⁴ defₒ i
comp² (set i ← x)  = comp¹ x ∥ o⁴ setₒ i
comp² (setₖ k ← x) = comp¹ x ∥ ⟨comp¹⟩ʰ k ∥ o⁵ setₖₒ
comp² (out x)      = ⟨comp¹⟩ᵒ (⟨⟩-len x) x

-- Compiling statement sequences
comp³ : ∀ {i} → S³ → Oⱽ i i
comp³ (x │ s) = comp² x ∥ comp³ s
comp³ (x └)   = comp² x

-- Compiling signature dispatch sequences
comp⁵ : ∀ {i} → S⁵ → Oⱽ i i
comp⁵ (◎ s ┌ k)  = fork (o¹ sigₒ s) (comp³ k)
comp⁵ (s₁ ⅋ s₂) = comp⁵ s₁ ∥ comp⁵ s₂


------------------------------------------------------------------------
-- ✿ Section 6
--     “Compiling EV²M to EVM”
--

data Oᴱ : Set where
  _⟫_          : Oᴱ → Oᴱ → Oᴱ
  ADD          : Oᴱ
  ADDRESS      : Oᴱ
  AND          : Oᴱ
  CALLDATALOAD : Oᴱ
  CALLER       : Oᴱ
  EQ           : Oᴱ
  JUMPDEST     : Oᴱ
  JUMPI        : ℕ → Oᴱ
  ΔJUMPI       : ℕ → Oᴱ
  JUMP         : ℕ → Oᴱ
  KECCAK256    : Oᴱ
  MLOAD        : Oᴱ
  MSTORE       : Oᴱ
  MUL          : Oᴱ
  OR           : Oᴱ
  PUSH         : ℕ → Oᴱ
  SDIV         : Oᴱ
  SGT          : Oᴱ
  SLOAD        : Oᴱ
  SLT          : Oᴱ
  NOT          : Oᴱ
  ISZERO       : Oᴱ
  SSTORE       : Oᴱ
  STOP         : Oᴱ
  SUB          : Oᴱ
  TIMESTAMP    : Oᴱ
  DUP          : ℕ → Oᴱ
  SWAP         : ℕ → Oᴱ
  REVERT       : Oᴱ

infixr 10 _⟫_

ADD-safe =
  (PUSH 0 ⟫ DUP  2 ⟫ SLT ⟫ (DUP  3 ⟫ DUP 3 ⟫ ADD)    ⟫ DUP 4 ⟫ SLT ⟫ AND) ⟫
  (DUP  2 ⟫ PUSH 0 ⟫ SLT ⟫ SWAP 3 ⟫ (DUP 1 ⟫ SWAP 4 ⟫ ADD)   ⟫ SLT ⟫ AND) ⟫
  OR

Oᴱ-length : Oᴱ → ℕ
Oᴱ-length (x ⟫ y) = Oᴱ-length x +ℕ Oᴱ-length y
Oᴱ-length _ = 1

Oⱽ→Oᴱ : ∀ {i j} → Oⱽ i j → Oᴱ
Oⱽ→Oᴱ (o⁰ nilₒ)    = PUSH 0
Oⱽ→Oᴱ (o⁰ oneₒ)    = PUSH 1
Oⱽ→Oᴱ (o⁰ callerₒ) = CALLER
Oⱽ→Oᴱ (o⁰ calleeₒ) = ADDRESS
Oⱽ→Oᴱ (o¹ refₒ x)  = PUSH (x +ℕ 64) ⟫ MLOAD
Oⱽ→Oᴱ (o¹ getₒ x)  = PUSH x ⟫ SLOAD
Oⱽ→Oᴱ (o¹ argₒ x)  = PUSH (x ×ℕ 32) ⟫ CALLDATALOAD
Oⱽ→Oᴱ (o¹ sigₒ x)  = CALLDATALOAD ⟫ PUSH 66 ⟫ EQ
Oⱽ→Oᴱ (o² getₖₒ)   = SLOAD
Oⱽ→Oᴱ (o² H¹ₒ)     = PUSH 0  ⟫ MSTORE ⟫
                     PUSH 32 ⟫ PUSH 0 ⟫ KECCAK256
Oⱽ→Oᴱ (o³ +ₒ)      = ADD-safe
Oⱽ→Oᴱ (o³ −ₒ)      = PUSH 0 ⟫ SUB ⟫ ADD-safe
Oⱽ→Oᴱ (o³ ×ₒ)      = MUL
Oⱽ→Oᴱ (o³ ≡ₒ)      = EQ
Oⱽ→Oᴱ (o³ ≥ₒ)      = SLT ⟫ ISZERO
Oⱽ→Oᴱ (o³ ∧ₒ)      = AND
Oⱽ→Oᴱ (o³ ∨ₒ)      = OR
Oⱽ→Oᴱ (o³ H²ₒ)     = PUSH 0  ⟫ MSTORE ⟫
                     PUSH 32 ⟫ MSTORE ⟫
                     PUSH 64 ⟫ PUSH 0 ⟫ KECCAK256
Oⱽ→Oᴱ (o⁴ iffₒ)    = ISZERO ⟫ JUMPI 3
Oⱽ→Oᴱ (o⁴ defₒ x)  = PUSH (x +ℕ 64) ⟫ MSTORE
Oⱽ→Oᴱ (o⁴ setₒ x)  = PUSH x         ⟫ SSTORE
Oⱽ→Oᴱ (o⁴ outₒ i)  = PUSH (i +ℕ 1024) ⟫ MSTORE
Oⱽ→Oᴱ (o⁵ setₖₒ)   = SSTORE
Oⱽ→Oᴱ (o₁ ∥ o₂)    = Oⱽ→Oᴱ o₁ ⟫ Oⱽ→Oᴱ o₂
Oⱽ→Oᴱ (fork o₁ o₂) = Oⱽ→Oᴱ o₁ ⟫ ΔJUMPI (Oᴱ-length (Oⱽ→Oᴱ o₂)) ⟫
                     Oⱽ→Oᴱ o₂
Oⱽ→Oᴱ done         = STOP

-- Oᴱ-absolute : ℕ → Oᴱ → Oᴱ
-- Oᴱ-absolute i (o₁ ⟫ o₂) = {!!}
-- Oᴱ-absolute i (JUMPI x) = {!!}
-- Oᴱ-absolute i (ΔJUMPI x) = {!!}
-- Oᴱ-absolute i (JUMP x) = {!!}
-- Oᴱ-absolute i (PUSH x) = {!!}
-- Oᴱ-absolute i (DUP x) = {!!}
-- Oᴱ-absolute i (SWAP x) = {!!}
-- Oᴱ-absolute i _ = {!!}

hex : ℕ → String
hex x with Data.String.toList (showInBase 16 x)
... | s@(c₁ ∷ c₂ ∷ []) = Data.String.fromList s
... | s@(c₁ ∷ []) = Data.String.fromList ('0' ∷ c₁ ∷ [])
... | s = "ERROR"

code : Oᴱ → String
code (x₁ ⟫ x₂) = code x₁ ++ code x₂
code ADD = "01"
code ADDRESS = "30"
code AND = "16"
code CALLDATALOAD = "35"
code CALLER = "33"
code EQ = "14"
code JUMPDEST = "5b"
code (JUMP x) = "60" ++ hex x ++ "56"
code (JUMPI 0) = "600357"
code (JUMPI x) = "60" ++ hex x ++ "57"
code (ΔJUMPI x) = "60[" ++ hex x ++ "]57"
code KECCAK256 = "20"
code MLOAD = "51"
code MSTORE = "52"
code MUL = "02"
code OR = "17"
code (PUSH x) = "60" ++ hex x
code SDIV = "05"
code SGT = "13"
code SLOAD = "54"
code SLT = "12"
code NOT = "19"
code ISZERO = "15"
code SSTORE = "55"
code STOP = "00"
code SUB = "03"
code TIMESTAMP = "42"
code (DUP x) = hex (0x7f +ℕ x)
code (SWAP x) = hex (0x8f +ℕ x)
code REVERT = hex 0xfd

prelude = JUMP 5 ⟫ JUMPDEST ⟫ REVERT ⟫ JUMPDEST

S³→Code : S³ → String
S³→Code s = code (prelude ⟫ Oⱽ→Oᴱ (comp³ s))

S⁵→Code : S⁵ → String
S⁵→Code s = code (prelude ⟫ Oⱽ→Oᴱ (comp⁵ s))

compile = S⁵→Code

------------------------------------------------------------------------
-- ✿ Section 7
--     “An EV²M semantics”
--

module Machine (®   : CommutativeRing lzero lzero)
               (_≈ᵣ_ : Rel (CommutativeRing.Carrier ®) lzero)
               (_<ᵣ_ : Rel (CommutativeRing.Carrier ®) lzero)
               (sto : IsStrictTotalOrder _≈ᵣ_ _<ᵣ_) where

  open CommutativeRing ® renaming (_+_ to _+ᵣ_; _*_ to _×ᵣ_; _-_ to _−ᵣ_)
  open IsStrictTotalOrder sto

  𝕎 = Carrier

  _∨ᵣ_ : 𝕎 → 𝕎 → 𝕎
  x ∨ᵣ y with ⌊ x ≟ 0# ⌋
  x ∨ᵣ y | false with ⌊ y ≟ 0# ⌋
  x ∨ᵣ y | false | false = 0#
  x ∨ᵣ y | false | true = 1#
  x ∨ᵣ y | true = 1#

  _∧ᵣ_ : 𝕎 → 𝕎 → 𝕎
  x ∧ᵣ y with ⌊ x ≟ 0# ⌋
  x ∧ᵣ y | false = 0#
  x ∧ᵣ y | true with ⌊ y ≟ 0# ⌋
  x ∧ᵣ y | true | true = 1#
  x ∧ᵣ y | true | false = 0#

  _≡ᵣ_ : 𝕎 → 𝕎 → 𝕎
  x ≡ᵣ y with ⌊ x ≟ y ⌋
  x ≡ᵣ y | false = 0#
  x ≡ᵣ y | true = 1#

  _>ᵣ_ : 𝕎 → 𝕎 → 𝕎
  x >ᵣ y with ⌊ y <? x ⌋
  ... | false = 0#
  ... | true  = 1#

  _≥ᵣ_ : 𝕎 → 𝕎 → 𝕎
  x ≥ᵣ y = (x >ᵣ y) ∨ᵣ (x ≡ᵣ y)

  Ξ : Set
  Ξ = ℕ → 𝕎

  _but_is_ : Ξ → ℕ → 𝕎 → Ξ
  x but i is a = λ j → if ⌊ j ≟ℕ i ⌋ then a else x j

  record Eval : Set where
    constructor Γₑ
    field
      p  : Ξ
      m  : Ξ
      d₁ : Ξ
      d₂ : ⟨S¹⟩ → 𝕎
      o  : ⟨S¹⟩

  pos : ℕ → 𝕎
  pos ℕ.zero = 0#
  pos (suc n) = 1# +ᵣ pos n

  eval¹ : S¹ → Eval → 𝕎
  eval¹ (# n)    _ = pos n
  eval¹ Uₐ       _ = 0# -- XXX
  eval¹ &ₐ       _ = 0#
  eval¹ (x + y)  e = eval¹ x e +ᵣ eval¹ y e
  eval¹ (x − y)  e = eval¹ x e −ᵣ eval¹ y e
  eval¹ (x × y)  e = eval¹ x e ×ᵣ eval¹ y e
  eval¹ (x ∨ y)  e = eval¹ x e ∨ᵣ eval¹ y e
  eval¹ (x ∧ y)  e = eval¹ x e ∧ᵣ eval¹ y e
  eval¹ (x ≥ y)  e = eval¹ x e ≥ᵣ eval¹ y e
  eval¹ (x ≡ y)  e = eval¹ x e +ᵣ eval¹ y e
  eval¹ (get  x) (Γₑ p m d₁ d₂ o) = d₁ x
  eval¹ (getₖ x) (Γₑ p m d₁ d₂ o) = d₂ x -- XXX
  eval¹ (ref  x) (Γₑ p m d₁ d₂ o) = m x
  eval¹ (arg  x) (Γₑ p m d₁ d₂ o) = p x
  eval¹ (sha k)  (Γₑ p m d₁ d₂ o) = d₂ k -- XXX

  eval² : S² → Eval → Maybe Eval
  eval² (iff x) e
    with eval¹ x e
  ... | x′ = if ⌊ x′ ≟ 0# ⌋ then nothing else just e
  eval² (def i ≜ x) e@(Γₑ p m d₁ d₂ o)
    with eval¹ x e
  ... | x′ = just (Γₑ p (m but i is x′) d₁ d₂ o)
  eval² (set i ← x) e@(Γₑ p m d₁ d₂ o)
    with eval¹ x e
  ... | x′ = just (Γₑ p m (d₁ but i is x′) d₂ o)
  eval² (setₖ k ← x) e@(Γₑ p m d₁ d₂ o)
    with eval¹ x e
  ... | x′ = just (Γₑ p m d₁ d₂ o) -- XXX
  eval² (out ⟨x⟩) (Γₑ p m d₁ d₂ o) =
    just (Γₑ p m d₁ d₂ o) -- XXX


  eval³ : S³ → Eval → Maybe Eval
  eval³ (x │ s) e with eval² x e
  eval³ (x │ k) e | just e′ = eval³ k e′
  eval³ (x │ k) _ | nothing = nothing
  eval³ (x └) e = eval² x e

------------------------------------------------------------------------
#0 = # 0; #1 = # 1; #2 = # 2; #3 = # 3
x₁ = $ 0; x₂ = $ 1; x₃ = $ 2; x₄ = $ 3
tmp₁ = 0; tmp₂ = 1

Cᵘ = λ u → ⟨ u , #0 ⟩
Dᵘ = λ u → ⟨ u , #1 ⟩
cᵘ = λ u → ⟨ u , #2 ⟩
dᵘ = λ u → ⟨ u , #3 ⟩

root = getₖ ⟨ #0 , Uₐ ⟩ ≡ #1

_↧ₖ_ = λ k Δ → iff (getₖ k ≥ #0) − Δ
_↥ₖ_ = λ k Δ → iff (getₖ k ≥ #0) + Δ

moldᵣ = sig "mold" 3 0
slipᵣ = sig "slip" 3 0
gazeᵤ = sig "gaze" 1 0
dripᵣ = sig "drip" 1 0

Φ = 0; Ψ = 1; Ω = 2

ilk =
   ◎ moldᵣ
   ┌ set Φ ← x₁
   │ set Ψ ← x₂
   │ set Ω ← x₃
   └ ⅋

   let u = $ 0; ΔC = $ 1; ΔD = $ 2
       Cᵤ = Cᵘ u; Dᵤ = Dᵘ u in
   ◎ slipᵣ
   ┌ iff root
   │ Cᵤ ↥ₖ ΔC
   │ Dᵤ ↥ₖ ΔD
   └ ⅋

   let Cᵤ = Cᵘ u; Dᵤ = Dᵘ u; cᵤ = cᵘ u; dᵤ = dᵘ u in
   ◎ gazeᵤ
   ┌ out ⟨ (getₖ Cᵤ) , (getₖ Dᵤ) , (getₖ cᵤ) , (getₖ dᵤ) ⟩
   └ ⅋

   let Δχ = tmp₁ in
   ◎ dripᵣ
   ┌ def Δχ ≜ (Φ ^ (t - t0) − #1) × χ
   └

-- │ dripᵣ → let Δχ=[Φ^(t−t₀)−1]·χ   │
-- │   ΔD=Δχ·Σd → ΔD set χ↑Δχ t₀=t   │
