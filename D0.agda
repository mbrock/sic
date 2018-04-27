module D0 where

open import Sic

data 𝟏 : Set where root : 𝟏
data 𝟖 : Set where cage live mold feel slip look grab frob : 𝟖

D⁰ : S² 𝟏 𝟖 Holy
D⁰ = slot 0 ∷ λ K →
     slot 1 ∷ 1 × 4 ∷ λ ilk → λ ψ φ Ω Σ →
     slot 2 ∷ 2 × 4 ∷ λ urn → λ c d C D →

  auth root ∷
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
    -- Enforce safety
    │  iff (φᵢ × dᵢᵤ ≤ ψᵢ × cᵢᵤ) ∨ (Δd ≤ 0 ∧ Δc ≥ 0)
    │  iff (φᵢ × Σᵢ ≤ Ωᵢ)        ∨ (Δd ≤ 0)
    -- Update state, enforcing nonnegative values
    │  c i u ←+ cᵢᵤ │ d i u ←+ dᵢᵤ │ Σ i ←+ Σᵢ
    │  C i u ←+ Cᵢᵤ − Δc
    │  D i u ←+ Dᵢᵤ − Δd × φᵢ)
  & ¶ live 0 (fyi₁ (¬ get K))
  & ¶ feel 1 (λ i → ilk i 0 1 2 3 fyi₄)
  & ¶ look 2 (λ i j → urn i j 0 1 2 3 fyi₄)

ABI : 𝟖 → String
ABI =
  λ { slip → "slip(uint256,address,int256,int256)"
    ; mold → "mold(uint256,int256,int256,int256)"
    ; grab → "grab(uint256,address)"
    ; cage → "cage()"
    ; frob → "frob(uint256,int256,int256)"
    ; live → "live()"
    ; feel → "feel(uint256)"
    ; look → "look(uint256,address)"
    }

main = link D⁰ (λ { ⊤ → parameter "ROOT" }) ABI

postulate &ROOT : Addrᴱ
D⁰-demo = S²→Oᴱ (λ { ⊤ → &ROOT }) ABI D⁰

-- Some kind of gadget
multi-owner =
  CALLER ⟫ PUSH 1 ⟫ SSTORE ⟫
  PUSH 13 ⟫ CODESIZE ⟫ SUB ⟫ DUP 1 ⟫
  PUSH 13 ⟫ PUSH 0 ⟫ CODECOPY ⟫ PUSH 0 ⟫ RETURN
