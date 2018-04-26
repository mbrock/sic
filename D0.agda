module D0 where

open import Sic

data Guy⁰ : Set where root user : Guy⁰
data Act⁰ : Set where live cage look feel slip mold frob grab : Act⁰

D⁰ = slot 0             :: λ K →
     slot 1 maps 1 to 4 :: λ ilk → λ ψ φ Ω Σ →
     slot 2 maps 2 to 4 :: λ urn → λ c d C D →

    root :: cage ⊢ K ← 1
  ⅋ user :: live ⊢ fyi₁ (¬ get K)
  ⅋ user :: look ⊢ 2 args (λ i j → urn i j 0 1 2 3 fyi₄)
  ⅋ user :: feel ⊢ 1 args (λ i   → ilk i   0 1 2 3 fyi₄)
  ⅋ root :: grab ⊢ 2 args (λ i j → c i j ← 0 │ d i j ← 0)
  ⅋ root :: mold ⊢ 4 args (λ i φᵢ ψᵢ Ωᵢ → φ i ← φᵢ │ ψ i ← ψᵢ │ Ω i ← Ωᵢ)
  ⅋ root :: slip ⊢ 4 args (λ i j ΔC ΔD → C i j ←+ ΔC │ D i j ←+ ΔD)
  ⅋ user :: frob ⊢ 3 args  λ i Δc Δd →
        urn i u 0 1 2 3  λ cᵢᵤ dᵢᵤ Cᵢᵤ Dᵢᵤ →
        ilk i   4 5 6 7  λ ψᵢ φᵢ Ωᵢ Σᵢ →
        0 ≜ cᵢᵤ + Δc │ 1 ≜ dᵢᵤ + Δd │ 7 ≜ Σᵢ + Δd
      │ iff ¬ get K
      │ iff (φᵢ ∙ dᵢᵤ ≤ ψᵢ ∙ cᵢᵤ) ∨ (Δd ≤ 0 ∧ Δc ≥ 0)
      │ iff (φᵢ ∙ Σᵢ ≤ Ωᵢ) ∨ (Δd ≤ 0)
      │ c i u ←+ cᵢᵤ │ d i u ←+ dᵢᵤ │ Σ i ←+ Σᵢ
      │ C i u ←+ Cᵢᵤ − Δc
      │ D i u ←+ Dᵢᵤ − Δd ∙ φᵢ
