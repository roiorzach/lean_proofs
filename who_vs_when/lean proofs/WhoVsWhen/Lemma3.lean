import WhoVsWhen.Model

/-!
# Lemma 3: expected losses under sequential decision-making
-/

namespace WhoVsWhen

open MeasureTheory

/-- **Lemma 3.** Under sequential decision-making with unit 1 leading, the expected losses are
equations (2) and (3):

* leader: `(1 - r₁) γ₁ (σ₁² + σ₂²) + γ₁ β₁ c₂`;
* follower: `(1 - r₂) r₂ (1 - γ₁)² (σ₁² + σ₂²) - (1 - r₂) r₂ (γ₁² - 2γ₁) c₂`.

Here `c₂` is the information loss about the follower's state; Lemma 2 gives its value in the limit
partition. The formulas hold for every message structure. -/
theorem lemma3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (E : Env Ω P) {r₁ r₂ : ℝ} (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) :
    ∫ ω, L r₁ (E.seqD₁ r₁ r₂ ω) (E.seqD₂ r₁ r₂ ω) (E.θ₁ ω) ∂P =
        (1 - r₁) * γ r₁ r₂ * (E.s₁ + E.s₂) + γ r₁ r₂ * β r₁ r₂ * E.c₂ ∧
      ∫ ω, L r₂ (E.seqD₂ r₁ r₂ ω) (E.seqD₁ r₁ r₂ ω) (E.θ₂ ω) ∂P =
        (1 - r₂) * r₂ * (1 - γ r₁ r₂) ^ 2 * (E.s₁ + E.s₂)
          - (1 - r₂) * r₂ * (γ r₁ r₂ ^ 2 - 2 * γ r₁ r₂) * E.c₂ :=
  ⟨E.leader_loss_eq h₁ h₂, E.follower_loss_eq⟩

end WhoVsWhen
