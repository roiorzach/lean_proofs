import WhoVsWhen.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Lemma 1: equilibrium decisions

The main result is `lemma1`. The helper lemmas compute each unit's expected loss as a quadratic in
its decision and identify the unique minimizer.

A unit's information after the messages is represented by a belief: any probability measure with
a finite second moment. For the sequential leader it is the posterior about `θ₂` given `m₂`. For a
concurrent unit it is the belief about the other unit's decision.
-/

namespace WhoVsWhen

open MeasureTheory

section Integrals

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- Integral of a quadratic polynomial against a probability measure with a finite second
moment. -/
lemma integral_quad (h1 : Integrable (fun x : ℝ => x) ν) (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (a b c : ℝ) :
    ∫ x, (a + b * x + c * x ^ 2) ∂ν = a + b * ∫ x, x ∂ν + c * ∫ x, x ^ 2 ∂ν := by
  have hA : Integrable (fun x : ℝ => a + b * x) ν := (integrable_const a).add (h1.const_mul b)
  have hC : Integrable (fun x : ℝ => c * x ^ 2) ν := h2.const_mul c
  have hB : Integrable (fun x : ℝ => b * x) ν := h1.const_mul b
  rw [integral_add hA hC, integral_add (integrable_const a) hB, integral_const, integral_const_mul,
    integral_const_mul]
  simp

end Integrals

/-! ### Sequential decision-making -/

/-- The follower's loss exceeds its minimum by the squared distance to `(1 - r₂) θ₂ + r₂ d₁`. -/
lemma L_follower_decomp (r₂ θ₂ d₁ d : ℝ) :
    L r₂ d d₁ θ₂ = L r₂ ((1 - r₂) * θ₂ + r₂ * d₁) d₁ θ₂ + (d - ((1 - r₂) * θ₂ + r₂ * d₁)) ^ 2 := by
  unfold L; ring

/-- Having observed the leader's decision `d₁`, the follower's unique
optimal decision is `d₂ = (1 - r₂) θ₂ + r₂ d₁`. -/
lemma follower_br (r₂ θ₂ d₁ : ℝ) (d : ℝ) (hd : d ≠ (1 - r₂) * θ₂ + r₂ * d₁) :
    L r₂ ((1 - r₂) * θ₂ + r₂ * d₁) d₁ θ₂ < L r₂ d d₁ θ₂ := by
  rw [L_follower_decomp r₂ θ₂ d₁ d]
  have : 0 < (d - ((1 - r₂) * θ₂ + r₂ * d₁)) ^ 2 := by
    have : d - ((1 - r₂) * θ₂ + r₂ * d₁) ≠ 0 := sub_ne_zero.mpr hd
    positivity
  linarith

/-- Equation (8): the follower's loss after best-responding, `U₂(θ₂, d₁) = (1 - r₂) r₂ (d₁ - θ₂)²`. -/
lemma follower_value (r₂ θ₂ d₁ : ℝ) :
    L r₂ ((1 - r₂) * θ₂ + r₂ * d₁) d₁ θ₂ = (1 - r₂) * r₂ * (d₁ - θ₂) ^ 2 := by
  unfold L; ring

/-- The leader's expected loss from decision `d`, when the follower best-responds and the leader's
belief about `θ₂` is `ν`. -/
noncomputable def leaderValue (r₁ r₂ θ₁ : ℝ) (ν : Measure ℝ) (d : ℝ) : ℝ :=
  ∫ θ₂, L r₁ d ((1 - r₂) * θ₂ + r₂ * d) θ₁ ∂ν

lemma leaderValue_eq {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h1 : Integrable (fun x : ℝ => x) ν) (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (r₁ r₂ θ₁ d : ℝ) :
    leaderValue r₁ r₂ θ₁ ν d =
      (1 - r₁) * (θ₁ - d) ^ 2 + β r₁ r₂ * (∫ x, x ^ 2 ∂ν - 2 * d * ∫ x, x ∂ν + d ^ 2) := by
  have hpt : ∀ θ₂, L r₁ d ((1 - r₂) * θ₂ + r₂ * d) θ₁ =
      ((1 - r₁) * (θ₁ - d) ^ 2 + β r₁ r₂ * d ^ 2) + (-(2 * β r₁ r₂ * d)) * θ₂ +
        β r₁ r₂ * θ₂ ^ 2 := by
    intro θ₂; unfold L β; ring
  unfold leaderValue
  simp_rw [hpt]
  rw [integral_quad h1 h2]; ring

/-- Whatever the leader's belief `ν` about the follower's state (a
probability measure with finite second moment, e.g. the conditional distribution of `θ₂` given
`m₂`), its unique optimal decision is `d₁ = (1 - γ₁) θ₁ + γ₁ 𝔼_ν θ₂`. -/
lemma leader_br {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h1 : Integrable (fun x : ℝ => x) ν) (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    {r₁ r₂ : ℝ} (hr₁ : Unit01 r₁) (hr₂ : Unit01 r₂) (θ₁ : ℝ) (d : ℝ)
    (hd : d ≠ (1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * ∫ x, x ∂ν) :
    leaderValue r₁ r₂ θ₁ ν ((1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * ∫ x, x ∂ν) <
      leaderValue r₁ r₂ θ₁ ν d := by
  set m := ∫ x, x ∂ν
  have hAB : 0 < (1 - r₁) + β r₁ r₂ := den_γ_pos hr₁ hr₂
  have hstar : (1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * m =
      ((1 - r₁) * θ₁ + β r₁ r₂ * m) / ((1 - r₁) + β r₁ r₂) := by
    rw [one_sub_γ hr₁ hr₂]; unfold γ; field_simp
  have key : ∀ e, leaderValue r₁ r₂ θ₁ ν e =
      leaderValue r₁ r₂ θ₁ ν (((1 - r₁) * θ₁ + β r₁ r₂ * m) / ((1 - r₁) + β r₁ r₂)) +
        ((1 - r₁) + β r₁ r₂) *
          (e - ((1 - r₁) * θ₁ + β r₁ r₂ * m) / ((1 - r₁) + β r₁ r₂)) ^ 2 := by
    intro e
    rw [leaderValue_eq h1 h2, leaderValue_eq h1 h2]
    field_simp; ring
  rw [hstar] at hd ⊢
  rw [key d]
  have : 0 < (d - ((1 - r₁) * θ₁ + β r₁ r₂ * m) / ((1 - r₁) + β r₁ r₂)) ^ 2 := by
    have : d - ((1 - r₁) * θ₁ + β r₁ r₂ * m) / ((1 - r₁) + β r₁ r₂) ≠ 0 := sub_ne_zero.mpr hd
    positivity
  nlinarith

/-- The leader's rule in the paper's notation:
`d₁ = (1 - r₁)/((1 - r₁) + β₁) θ₁ + β₁/((1 - r₁) + β₁) 𝔼(θ₂ | m₂)`. -/
lemma leader_rule_paperForm {r₁ r₂ : ℝ} (hr₁ : Unit01 r₁) (hr₂ : Unit01 r₂) (θ₁ m : ℝ) :
    (1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * m =
      (1 - r₁) / ((1 - r₁) + β r₁ r₂) * θ₁ + β r₁ r₂ / ((1 - r₁) + β r₁ r₂) * m := by
  rw [one_sub_γ hr₁ hr₂]; rfl

/-! ### Concurrent decision-making -/

/-- Unit `i`'s expected loss from decision `d` when its belief about the other unit's decision
is `ν`. -/
noncomputable def concValue (ri θi : ℝ) (ν : Measure ℝ) (d : ℝ) : ℝ :=
  ∫ x, L ri d x θi ∂ν

lemma concValue_eq {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h1 : Integrable (fun x : ℝ => x) ν) (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (ri θi d : ℝ) :
    concValue ri θi ν d =
      (1 - ri) * (θi - d) ^ 2 + ri * (∫ x, x ^ 2 ∂ν - 2 * d * ∫ x, x ∂ν + d ^ 2) := by
  have hpt : ∀ x, L ri d x θi =
      ((1 - ri) * (θi - d) ^ 2 + ri * d ^ 2) + (-(2 * ri * d)) * x + ri * x ^ 2 := by
    intro x; unfold L; ring
  unfold concValue
  simp_rw [hpt]
  rw [integral_quad h1 h2]; ring

/-- Whatever unit `i`'s belief `ν` about the other unit's decision `dⱼ`
(a probability measure with finite second moment), its unique optimal decision is
`dᵢ = (1 - rᵢ) θᵢ + rᵢ 𝔼_ν(dⱼ)`. -/
lemma conc_br {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h1 : Integrable (fun x : ℝ => x) ν) (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    (ri θi d : ℝ) (hd : d ≠ (1 - ri) * θi + ri * ∫ x, x ∂ν) :
    concValue ri θi ν ((1 - ri) * θi + ri * ∫ x, x ∂ν) < concValue ri θi ν d := by
  have key : concValue ri θi ν d = concValue ri θi ν ((1 - ri) * θi + ri * ∫ x, x ∂ν) +
      (d - ((1 - ri) * θi + ri * ∫ x, x ∂ν)) ^ 2 := by
    rw [concValue_eq h1 h2, concValue_eq h1 h2]; ring
  rw [key]
  have : 0 < (d - ((1 - ri) * θi + ri * ∫ x, x ∂ν)) ^ 2 := by
    have : d - ((1 - ri) * θi + ri * ∫ x, x ∂ν) ≠ 0 := sub_ne_zero.mpr hd
    positivity
  linarith

/-- The linear concurrent strategy of unit `i`: `dᵢ = (1 - rᵢ) θᵢ + eᵢ μᵢ + bᵢ μⱼ`, where `μᵢ, μⱼ` are
the posterior means `𝔼(θᵢ | mᵢ)`, `𝔼(θⱼ | mⱼ)` induced by the two messages. -/
noncomputable def concRule (ri rj θi μi μj : ℝ) : ℝ :=
  (1 - ri) * θi + eOwn ri rj * μi + bOth ri rj * μj

/-- Suppose unit `j` uses the linear rule and unit `i`'s
posterior about `θⱼ` has mean `μⱼ` (as it does when `ν` is the conditional law of `θⱼ` given
`mⱼ`). Then unit `i`'s unique best response is its own linear rule. This is the fixed point
behind `dᵢ = (1 - rᵢ) θᵢ + rᵢ 𝔼(dⱼ | mⱼ)`. -/
lemma conc_rule_br {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h1 : Integrable (fun x : ℝ => x) ν) (h2 : Integrable (fun x : ℝ => x ^ 2) ν)
    {ri rj : ℝ} (hi : Unit01 ri) (hj : Unit01 rj) (θi μi μj : ℝ) (hmean : ∫ x, x ∂ν = μj)
    (d : ℝ) (hd : d ≠ concRule ri rj θi μi μj) :
    ∫ θj, L ri (concRule ri rj θi μi μj) (concRule rj ri θj μj μi) θi ∂ν <
      ∫ θj, L ri d (concRule rj ri θj μj μi) θi ∂ν := by
  -- Expected loss as an explicit quadratic in the decision.
  have hval : ∀ e, ∫ θj, L ri e (concRule rj ri θj μj μi) θi ∂ν =
      (1 - ri) * (θi - e) ^ 2 + ri * ((1 - rj) ^ 2 * ∫ x, x ^ 2 ∂ν
        + 2 * (1 - rj) * (eOwn rj ri * μj + bOth rj ri * μi - e) * ∫ x, x ∂ν
        + (eOwn rj ri * μj + bOth rj ri * μi - e) ^ 2) := by
    intro e
    have hpt : ∀ θj, L ri e (concRule rj ri θj μj μi) θi =
        ((1 - ri) * (θi - e) ^ 2 + ri * (eOwn rj ri * μj + bOth rj ri * μi - e) ^ 2)
          + (ri * (2 * (1 - rj) * (eOwn rj ri * μj + bOth rj ri * μi - e))) * θj
          + (ri * (1 - rj) ^ 2) * θj ^ 2 := by
      intro θj; unfold L concRule; ring
    simp_rw [hpt]; rw [integral_quad h1 h2]; ring
  -- The candidate is the minimizer `(1 - rᵢ) θᵢ + rᵢ 𝔼(dⱼ)`.
  have hstar : concRule ri rj θi μi μj =
      (1 - ri) * θi + ri * ((1 - rj) * μj + eOwn rj ri * μj + bOth rj ri * μi) := by
    unfold concRule
    rw [eOwn_fixed hi hj, bOth_fixed hi hj]; ring
  have key : ∫ θj, L ri d (concRule rj ri θj μj μi) θi ∂ν =
      ∫ θj, L ri (concRule ri rj θi μi μj) (concRule rj ri θj μj μi) θi ∂ν +
        (d - concRule ri rj θi μi μj) ^ 2 := by
    rw [hval, hval, hstar, hmean]; ring
  rw [key]
  have : 0 < (d - concRule ri rj θi μi μj) ^ 2 := by
    have : d - concRule ri rj θi μi μj ≠ 0 := sub_ne_zero.mpr hd
    positivity
  linarith

/-- **Lemma 1.** The equilibrium decisions.

1. Sequential decision-making, the follower: having observed `d₁`, its unique optimal decision is
   `d₂ = (1 - r₂) θ₂ + r₂ d₁`.
2. Sequential decision-making, the leader: whatever its posterior `ν` about `θ₂`, its unique optimal
   decision (anticipating the follower's rule) is
   `d₁ = (1 - r₁)/((1 - r₁) + β₁) θ₁ + β₁/((1 - r₁) + β₁) 𝔼(θ₂ | m₂)`.
3. Concurrent decision-making: whatever unit `i`'s belief `ν` about `dⱼ`, its unique optimal
   decision is `dᵢ = (1 - rᵢ) θᵢ + rᵢ 𝔼(dⱼ)`.
4. The linear rules `dᵢ = (1 - rᵢ) θᵢ + eᵢ μᵢ + bᵢ μⱼ` (`concRule`) satisfy item 3 against each
   other: if unit `i`'s posterior about `θⱼ` has mean `μⱼ`, its unique best response to unit `j`'s
   rule is its own rule. -/
theorem lemma1 :
    (∀ r₂ θ₂ d₁ d : ℝ, d ≠ (1 - r₂) * θ₂ + r₂ * d₁ →
      L r₂ ((1 - r₂) * θ₂ + r₂ * d₁) d₁ θ₂ < L r₂ d d₁ θ₂) ∧
    (∀ r₁ r₂ : ℝ, Unit01 r₁ → Unit01 r₂ → ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      Integrable (fun x : ℝ => x) ν → Integrable (fun x : ℝ => x ^ 2) ν → ∀ θ₁ d : ℝ,
      d ≠ (1 - r₁) / ((1 - r₁) + β r₁ r₂) * θ₁ + β r₁ r₂ / ((1 - r₁) + β r₁ r₂) * ∫ x, x ∂ν →
      ∫ θ₂, L r₁ ((1 - r₁) / ((1 - r₁) + β r₁ r₂) * θ₁ + β r₁ r₂ / ((1 - r₁) + β r₁ r₂) * ∫ x, x ∂ν)
          ((1 - r₂) * θ₂ + r₂ * ((1 - r₁) / ((1 - r₁) + β r₁ r₂) * θ₁
            + β r₁ r₂ / ((1 - r₁) + β r₁ r₂) * ∫ x, x ∂ν)) θ₁ ∂ν <
        ∫ θ₂, L r₁ d ((1 - r₂) * θ₂ + r₂ * d) θ₁ ∂ν) ∧
    (∀ ri θi : ℝ, ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      Integrable (fun x : ℝ => x) ν → Integrable (fun x : ℝ => x ^ 2) ν → ∀ d : ℝ,
      d ≠ (1 - ri) * θi + ri * ∫ x, x ∂ν →
      ∫ x, L ri ((1 - ri) * θi + ri * ∫ x, x ∂ν) x θi ∂ν < ∫ x, L ri d x θi ∂ν) ∧
    (∀ ri rj : ℝ, Unit01 ri → Unit01 rj → ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      Integrable (fun x : ℝ => x) ν → Integrable (fun x : ℝ => x ^ 2) ν →
      ∀ θi μi μj : ℝ, ∫ x, x ∂ν = μj → ∀ d : ℝ, d ≠ concRule ri rj θi μi μj →
      ∫ θj, L ri (concRule ri rj θi μi μj) (concRule rj ri θj μj μi) θi ∂ν <
        ∫ θj, L ri d (concRule rj ri θj μj μi) θi ∂ν) := by
  refine ⟨fun r₂ θ₂ d₁ d hd => follower_br r₂ θ₂ d₁ d hd, ?_, ?_, ?_⟩
  · intro r₁ r₂ h₁ h₂ ν _ i1 i2 θ₁ d hd
    rw [← leader_rule_paperForm h₁ h₂] at hd ⊢
    exact leader_br i1 i2 h₁ h₂ θ₁ d hd
  · intro ri θi ν _ i1 i2 d hd
    exact conc_br i1 i2 ri θi d hd
  · intro ri rj hi hj ν _ i1 i2 θi μi μj hm d hd
    exact conc_rule_br i1 i2 hi hj θi μi μj hm d hd

end WhoVsWhen
