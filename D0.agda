module D0 where

open import Sic

data Guy⁰ : Set where pal : Guy⁰
data Act⁰ : Set where
  live cage : Act⁰
  look feel gaze : Act⁰
  slip mold frob grab : Act⁰

D⁰ : S² Guy⁰ Act⁰ easy
D⁰ = slot 0             :: λ K →
     slot 1 maps 1 to 4 :: λ ilk → λ ψ φ Ω Σ →
     slot 2 maps 2 to 4 :: λ urn → λ c d C D →

     the pal can cage :: K ← 1
  ⅋ anybody can live :: fyi₁ (¬ get K)
  ⅋ anybody can look :: 2 args (λ i j → fyi₂ (get C i j) (get D i j))
  ⅋ anybody can gaze :: 2 args (λ i j → fyi₂ (get c i j) (get d i j))
  ⅋ anybody can feel :: 1 args (λ i → ilk i 0 1 2 3 fyi₄)
  ⅋ the pal can grab :: 2 args (λ i j → c i j ← 0 │ d i j ← 0)
  ⅋ the pal can mold :: 4 args (λ i φᵢ ψᵢ Ωᵢ → φ i ← φᵢ │ ψ i ← ψᵢ │ Ω i ← Ωᵢ)
  ⅋ the pal can slip :: 4 args (λ i j ΔC ΔD → C i j ←+ ΔC │ D i j ←+ ΔD)
  ⅋ anybody can frob :: 3 args  λ i Δc Δd →
        urn i u 0 1 2 3  λ cᵢᵤ dᵢᵤ Cᵢᵤ Dᵢᵤ →
        ilk i   4 5 6 7  λ ψᵢ φᵢ Ωᵢ Σᵢ →
        0 ≜ cᵢᵤ + Δc │ 1 ≜ dᵢᵤ + Δd │ 7 ≜ Σᵢ + Δd
      │ c i u ←+ cᵢᵤ │ d i u ←+ dᵢᵤ │ Σ i ←+ Σᵢ
      │ C i u ←+ Cᵢᵤ − Δc
      │ D i u ←+ Dᵢᵤ − Δd ∙ φᵢ
      │ iff φᵢ ∙ dᵢᵤ ≤ ψᵢ ∙ cᵢᵤ ∨ (Δd ≤ 0 ∧ Δc ≥ 0)
      │ iff φᵢ ∙ Σᵢ ≤ Ωᵢ ∨ Δd ≤ 0
