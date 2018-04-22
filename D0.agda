module D0 where

open import Sic

data Guy⁰ : Set where pal : Guy⁰
data Act⁰ : Set where form slip mold frob : Act⁰

D⁰ : S² Guy⁰ Act⁰ easy
D⁰ =
  let n = 0 in
  1 maps 1 to 4 :: λ ψ φ Ω Σd →
  2 maps 2 to 4 :: λ c d C D  →
    the pal can form ::
      0 ≜ get n │ n ↑ 1 │ fyi₁ (# 0) │ φ (# 0) ← ray
  ⅋ the pal can mold ::
      3 args (λ i p x → iff p ≥ 0 ∧ p ≤ 2 │ ⟨ nat 1 , p , i ⟩ ← x)
  ⅋ the pal can slip ::
      4 args (λ i j C′ D′ → C i j ← C′ │ D i j ← D′)
  ⅋ anybody can frob ::
      3 args (λ i Δc Δd →
        0 ≜ get c i u │ 1 ≜ get d i u
      │ (C i u ↧ c i u ↥ Δc)
      │ (D i u ↧ Δd ∙ get φ i)
      │ Σd i ↥ Δd
      │ let calm = Δd ≤ 0
            cool = get φ i ∙ get Σd i  ≤ get Ω i
            safe = get φ i ∙ get d i u ≤ get ψ i ∙ get c i u
            nice = # 0     ∙ get d i u ≤ # 1     ∙ get c i u
        in iff (calm ∨ cool) ∧ (safe ∨ (calm ∧ nice)))
