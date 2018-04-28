module D0 where

open import Sic

data 𝟏 : Set where root : 𝟏
data 𝟖 : Set where cage live mold feel slip look grab frob : 𝟖

D⁰ : S² 𝟏 𝟖
D⁰ = slot 0 ∷ λ K →
     slot 1 ∷ 1 × 4 ∷ λ ilk → λ ψ φ Ω Σ →
     slot 2 ∷ 2 × 4 ∷ λ urn → λ c d C D →

  ¶ frob 3 (λ i Δc Δd →
       iff ¬ get K
    │  ilk i   4 5 6 7  λ ψᵢ φᵢ Ωᵢ Σᵢ →
       urn i u 0 1 2 3  λ cᵢᵤ dᵢᵤ Cᵢᵤ Dᵢᵤ →
       0 ≜ cᵢᵤ + Δc │ 1 ≜ dᵢᵤ + Δd │ 7 ≜ Σᵢ + Δd
    │  iff (φᵢ × dᵢᵤ ≤ ψᵢ × cᵢᵤ) ∨ (Δd ≤ 0 ∧ Δc ≥ 0)
    │  iff (φᵢ × Σᵢ ≤ Ωᵢ)        ∨ (Δd ≤ 0)
    │  [≥0] c i u ← cᵢᵤ
    │  [≥0] d i u ← dᵢᵤ
    │  [≥0] Σ i   ← Σᵢ
    │  [≥0] C i u ← Cᵢᵤ − Δc
    │  [≥0] D i u ← Dᵢᵤ − Δd × φᵢ)

  & ¶ live 0 (fyi 1 (¬ get K))
  & ¶ feel 1 (λ i   → ilk i   0 1 2 3 (fyi 4))
  & ¶ look 2 (λ i j → urn i j 0 1 2 3 (fyi 4))

  & (auth root ∷
       ¶ slip 4 (λ i j ΔC ΔD → [≥0] C i j ← ΔC │ [≥0] D i j ← ΔD)
     & ¶ mold 4 (λ i φᵢ ψᵢ Ωᵢ → φ i ← φᵢ │ ψ i ← ψᵢ │ Ω i ← Ωᵢ)
     & ¶ grab 2 (λ i j → c i j ← 0 │ d i j ← 0)
     & ¶ cage 0 (K ← 1))

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

-- This one is for inspecting in Emacs.
postulate &ROOT : Addrᴱ
D⁰-demo = S²→Oᴱ (λ { ⊤ → &ROOT }) ABI D⁰
