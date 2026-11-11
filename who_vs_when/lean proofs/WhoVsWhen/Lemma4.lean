import WhoVsWhen.Model

/-!
# Lemma 4: expected loss under concurrent decision-making
-/

namespace WhoVsWhen

open MeasureTheory

/-- **Lemma 4** (with the typos corrected). Unit 1's expected loss under concurrent
decision-making is
`(σ₁² + σ₂²)(1 - r₁)β₁/(1 - r₁r₂)²
  + r₁(1 - r₁)((1 - r₁r₂)² - (1 - r₂)²)/(1 - r₁r₂)² · c₁
  + r₁(1 - r₂)²((1 - r₁r₂)² - (1 - r₁))/(1 - r₁r₂)² · c₂`.
Here `cᵢ` is the information loss about state `i`. Lemma 2 gives `cᵢ = σᵢ² V(φᵢ^{sim})` in the
limit partition, with `φᵢ^{sim} = φ_{i,concurrent} = βⱼ/((1 - rᵢ)(1 - rⱼ))`. The formula holds for
every message structure. -/
theorem lemma4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (E : Env Ω P) {r₁ r₂ : ℝ} (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) :
    ∫ ω, L r₁ (E.concD₁ r₁ r₂ ω) (E.concD₂ r₁ r₂ ω) (E.θ₁ ω) ∂P =
      (E.s₁ + E.s₂) * (1 - r₁) * β r₁ r₂ / (1 - r₁ * r₂) ^ 2
        + r₁ * (1 - r₁) * ((1 - r₁ * r₂) ^ 2 - (1 - r₂) ^ 2) / (1 - r₁ * r₂) ^ 2 * E.c₁
        + r₁ * (1 - r₂) ^ 2 * ((1 - r₁ * r₂) ^ 2 - (1 - r₁)) / (1 - r₁ * r₂) ^ 2 * E.c₂ :=
  E.conc_loss_eq h₁ h₂

end WhoVsWhen
