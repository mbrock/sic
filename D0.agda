module D0 where

open import Sic

data 𝟐 : Set where
  ⊤ : 𝟐 -- Authority
  ⊥ : 𝟐 -- Everybody

data 𝟖 : Set where
  cage live mold feel slip look grab frob : 𝟖

D⁰ : S² 𝟐 𝟖 Holy
D⁰ = slot 0 ∷ λ K →
     slot 1 ∷ 1 × 4 ∷ λ ilk → λ ψ φ Ω Σ →
     slot 2 ∷ 2 × 4 ∷ λ urn → λ c d C D →

   -- XXX: get root address from environment
   case u ≡ 0 then
     ¶ slip 4 (λ i j ΔC ΔD → C i j ←+ ΔC │ D i j ←+ ΔD)
   & ¶ mold 4 (λ i φᵢ ψᵢ Ωᵢ → φ i ← φᵢ │ ψ i ← ψᵢ │ Ω i ← Ωᵢ)
   & ¶ grab 2 (λ i j → c i j ← 0 │ d i j ← 0)
   & ¶ cage 0 (K ← 1)
   else
     ¶ frob 3 (λ i Δc Δd →
     -- Enforce cage absence
        iff ¬ get K
     -- Load ilk and urn state
     │  ilk i   4 5 6 7  λ ψᵢ φᵢ Ωᵢ Σᵢ →
        urn i u 0 1 2 3  λ cᵢᵤ dᵢᵤ Cᵢᵤ Dᵢᵤ →
     -- Increase or decrease cᵢᵤ, dᵢᵤ, and Σᵢ
        0 ≜ cᵢᵤ + Δc │ 1 ≜ dᵢᵤ + Δd │ 7 ≜ Σᵢ + Δd
     -- Enforce safety parameters
     │  iff (φᵢ × dᵢᵤ ≤ ψᵢ × cᵢᵤ) ∨ (Δd ≤ 0 ∧ Δc ≥ 0)
     │  iff (φᵢ × Σᵢ ≤ Ωᵢ)       ∨ (Δd ≤ 0)
     -- Update state, enforcing nonnegative values
     │  c i u ←+ cᵢᵤ │ d i u ←+ dᵢᵤ │ Σ i ←+ Σᵢ
     │  C i u ←+ Cᵢᵤ − Δc
     │  D i u ←+ Dᵢᵤ − Δd × φᵢ)
   & ¶ live 0 (fyi₁ (¬ get K))
   & ¶ feel 1 (λ i → ilk i 0 1 2 3 fyi₄)
   & ¶ look 2 (λ i j → urn i j 0 1 2 3 fyi₄)

main = link D⁰
  (λ { ⊤ → the (parameter "ROOT")
     ; ⊥ → anybody })
  (λ { cage → "cage()"
     ; live → "live()"
     ; mold → "mold(uint256,int256,int256,int256)"
     ; feel → "feel(uint256)"
     ; slip → "slip(uint256,address,int256,int256)"
     ; look → "look(uint256,address)"
     ; grab → "grab(uint256,address)"
     ; frob → "frob(uint256,int256,int256)"
     })
