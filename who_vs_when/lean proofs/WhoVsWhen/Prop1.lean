import WhoVsWhen.Model

/-!
# Proposition 1: coordination loss for fixed information

The main result is `prop1`. "For a fixed information loss" means that the information is the same
under the timings being compared:
* the leader's state is known to both units (the paper's convention `m₁ = θ₁`, kept under
  concurrent decision-making);
* the follower's state is communicated through the same message.

Coordination loss is `𝔼 (d₁ - d₂)²`.
-/

namespace WhoVsWhen

open MeasureTheory

variable {r₁ r₂ : ℝ}

lemma Kc_pos (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) : 0 < Kc r₁ r₂ := by
  have := Dn_pos h₁ h₂
  have : 0 < 1 - r₁ := by linarith [h₁.2]
  have : 0 < 1 - r₂ := by linarith [h₂.2]
  unfold Kc; positivity

lemma seqCoef_eq (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) :
    (1 - r₂) * (1 - γ r₁ r₂) = (1 - r₁) * (1 - r₂) / ((1 - r₁) + β r₁ r₂) := by
  rw [one_sub_γ h₁ h₂]; ring

/-- The concurrent coordination coefficient is below the sequential one (proof of
Proposition 1(i)): `(1 - r₁)(1 - r₂)/(1 - r₁r₂) < (1 - r₂)(1 - γ₁)`. -/
lemma Kc_lt_seqCoef (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) : Kc r₁ r₂ < (1 - r₂) * (1 - γ r₁ r₂) := by
  rw [seqCoef_eq h₁ h₂]; unfold Kc
  have hD := Dn_pos h₁ h₂
  have hden := den_γ_pos h₁ h₂
  have hu : 0 < 1 - r₁ := by linarith [h₁.2]
  have hv : 0 < 1 - r₂ := by linarith [h₂.2]
  apply div_lt_div_of_pos_left (by positivity) hden
  unfold Dn β; nlinarith [mul_pos (mul_pos h₁.1 h₂.1) hv]

/-- Coordination loss under sequential decision-making, given the leader's state `θL` and the
leader's posterior `ν` about the follower's state. -/
noncomputable def coordSeqPost (rL rF θL : ℝ) (ν : Measure ℝ) : ℝ :=
  ∫ θF, ((1 - γ rL rF) * θL + γ rL rF * (∫ x, x ∂ν)
    - ((1 - rF) * θF + rF * ((1 - γ rL rF) * θL + γ rL rF * ∫ x, x ∂ν))) ^ 2 ∂ν

/-- Coordination loss under concurrent decision-making with the same information: the state `θL`
is known (`μ_L = θL`) and the other state has posterior `ν`. -/
noncomputable def coordConcPost (rL rF θL : ℝ) (ν : Measure ℝ) : ℝ :=
  ∫ θF, (concRule rL rF θL θL (∫ x, x ∂ν) - concRule rF rL θF (∫ x, x ∂ν) θL) ^ 2 ∂ν

section Posterior

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]
  (hi1 : Integrable (fun x : ℝ => x) ν) (hi2 : Integrable (fun x : ℝ => x ^ 2) ν)
include hi1 hi2

lemma coordSeqPost_eq (rL rF θL : ℝ) :
    coordSeqPost rL rF θL ν = (1 - rF) ^ 2 * ((∫ x, x ^ 2 ∂ν - (∫ x, x ∂ν) ^ 2)
      + (1 - γ rL rF) ^ 2 * (θL - ∫ x, x ∂ν) ^ 2) := by
  unfold coordSeqPost
  set m := ∫ x, x ∂ν
  have hpt : ∀ θF, ((1 - γ rL rF) * θL + γ rL rF * m
      - ((1 - rF) * θF + rF * ((1 - γ rL rF) * θL + γ rL rF * m))) ^ 2 =
      (1 - rF) ^ 2 * ((1 - γ rL rF) * θL + γ rL rF * m) ^ 2
        + (-(2 * (1 - rF) ^ 2 * ((1 - γ rL rF) * θL + γ rL rF * m))) * θF
        + (1 - rF) ^ 2 * θF ^ 2 := by intro θF; ring
  simp_rw [hpt]; rw [integral_quad hi1 hi2]; ring

lemma coordConcPost_eq {rL rF : ℝ} (hL : Unit01 rL) (hF : Unit01 rF) (θL : ℝ) :
    coordConcPost rL rF θL ν = (1 - rF) ^ 2 * (∫ x, x ^ 2 ∂ν - (∫ x, x ∂ν) ^ 2)
      + Kc rL rF ^ 2 * (θL - ∫ x, x ∂ν) ^ 2 := by
  unfold coordConcPost
  set m := ∫ x, x ∂ν
  have k1 : 1 - rL + eOwn rL rF - bOth rF rL = Kc rL rF := by
    have := Dn_pos hL hF
    have hD' : Dn rF rL = Dn rL rF := by unfold Dn; ring
    unfold eOwn bOth Kc; rw [hD']; field_simp; unfold Dn; ring
  have k2 : 1 - rF + eOwn rF rL - bOth rL rF = Kc rL rF := by
    have := Dn_pos hL hF
    have hD' : Dn rF rL = Dn rL rF := by unfold Dn; ring
    unfold eOwn bOth Kc; rw [hD']; field_simp; unfold Dn; ring
  set K := Kc rL rF
  have hpt : ∀ θF, (concRule rL rF θL θL m - concRule rF rL θF m θL) ^ 2 =
      (K * (θL - m) + (1 - rF) * m) ^ 2 + (-(2 * (1 - rF) * (K * (θL - m) + (1 - rF) * m))) * θF
        + (1 - rF) ^ 2 * θF ^ 2 := by
    intro θF; unfold concRule
    have : (1 - rL) * θL + eOwn rL rF * θL + bOth rL rF * m
        - ((1 - rF) * θF + eOwn rF rL * m + bOth rF rL * θL) =
        K * (θL - m) + (1 - rF) * m - (1 - rF) * θF := by
      linear_combination θL * k1 - m * k2
    rw [this]; ring
  simp_rw [hpt]; rw [integral_quad hi1 hi2]; ring

/-- Part (i) for a given order. Fix the information: the leader's state `θL` is known, and the
follower's message induces the posterior `ν`. Then concurrent decision-making yields weakly less
coordination loss than sequential decision-making, and strictly less iff the follower's posterior
mean differs from the leader's state. The statement covers both orders (`rL, rF` is either
`r₁, r₂` or `r₂, r₁`). -/
lemma coordConc_le_seq {rL rF : ℝ} (hL : Unit01 rL) (hF : Unit01 rF) (θL : ℝ) :
    coordConcPost rL rF θL ν ≤ coordSeqPost rL rF θL ν ∧
      (coordConcPost rL rF θL ν < coordSeqPost rL rF θL ν ↔ θL ≠ ∫ x, x ∂ν) := by
  rw [coordConcPost_eq hi1 hi2 hL hF, coordSeqPost_eq hi1 hi2]
  have hK := Kc_pos hL hF
  have hlt := Kc_lt_seqCoef hL hF
  have hsq : Kc rL rF ^ 2 < (1 - rF) ^ 2 * (1 - γ rL rF) ^ 2 := by
    rw [← mul_pow]; exact pow_lt_pow_left₀ hlt hK.le (by norm_num)
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg (θL - ∫ x, x ∂ν)]
  · constructor
    · intro h heq; rw [heq, sub_self] at h; simp at h
    · intro h
      have : 0 < (θL - ∫ x, x ∂ν) ^ 2 := by have := sub_ne_zero.mpr h; positivity
      nlinarith

end Posterior

/-- The step in the proof of Proposition 1(ii): `(1 - r₂)(1 - γ₁) < (1 - r₁)(1 - γ₂)` iff `r₁ < r₂`. -/
lemma seqCoef_lt_iff (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) :
    (1 - r₂) * (1 - γ r₁ r₂) < (1 - r₁) * (1 - γ r₂ r₁) ↔ r₁ < r₂ := by
  rw [seqCoef_eq h₁ h₂, seqCoef_eq h₂ h₁]
  have d1 := den_γ_pos h₁ h₂
  have d2 := den_γ_pos h₂ h₁
  have hu : 0 < 1 - r₁ := by linarith [h₁.2]
  have hv : 0 < 1 - r₂ := by linarith [h₂.2]
  rw [mul_comm (1 - r₂) (1 - r₁), div_lt_div_iff_of_pos_left (by positivity) d1 d2]
  have key : (1 - r₁) + β r₁ r₂ - ((1 - r₂) + β r₂ r₁) = r₁ * r₂ * (r₂ - r₁) := by unfold β; ring
  have hpos := mul_pos h₁.1 h₂.1
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Part (ii) in closed form: if the follower's state carries the same information loss
`c ∈ [0, σ₁² + σ₂²]` under either order and `σ₁² + σ₂² > 0`, the expected coordination loss is lower
when unit 1 moves first iff `r₁ < r₂`. -/
lemma coordSeqF_lt_iff (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) {s₁ s₂ c : ℝ} (hc : 0 ≤ c)
    (hcs : c ≤ s₁ + s₂) (hs : 0 < s₁ + s₂) :
    coordSeqF r₁ r₂ s₁ s₂ c < coordSeqF r₂ r₁ s₂ s₁ c ↔ r₁ < r₂ := by
  unfold coordSeqF
  have hk := seqCoef_lt_iff h₁ h₂
  have a1 : 0 < (1 - r₂) * (1 - γ r₁ r₂) :=
    mul_pos (by linarith [h₂.2]) (by linarith [γ_lt_one h₁ h₂])
  have a2 : 0 < (1 - r₁) * (1 - γ r₂ r₁) :=
    mul_pos (by linarith [h₁.2]) (by linarith [γ_lt_one h₂ h₁])
  have hu : 0 < 1 - r₁ := by linarith [h₁.2]
  have hv : 0 < 1 - r₂ := by linarith [h₂.2]
  have hsum : s₂ + s₁ - c = s₁ + s₂ - c := by ring
  rw [hsum]
  constructor
  · intro h
    by_contra hr
    have hr' : r₂ ≤ r₁ := not_lt.mp hr
    have k : (1 - r₁) * (1 - γ r₂ r₁) ≤ (1 - r₂) * (1 - γ r₁ r₂) := by
      rcases hr'.lt_or_eq with hlt | heq
      · exact ((seqCoef_lt_iff h₂ h₁).mpr hlt).le
      · subst heq; exact le_rfl
    have k2 : ((1 - r₁) * (1 - γ r₂ r₁)) ^ 2 ≤ ((1 - r₂) * (1 - γ r₁ r₂)) ^ 2 :=
      pow_le_pow_left₀ a2.le k 2
    have k3 : (1 - r₁) ^ 2 ≤ (1 - r₂) ^ 2 := pow_le_pow_left₀ hu.le (by linarith) 2
    have : (1 - r₁) ^ 2 * (c + (1 - γ r₂ r₁) ^ 2 * (s₁ + s₂ - c)) ≤
        (1 - r₂) ^ 2 * (c + (1 - γ r₁ r₂) ^ 2 * (s₁ + s₂ - c)) := by
      rw [mul_pow, mul_pow] at k2
      nlinarith [mul_le_mul_of_nonneg_right k2 (by linarith : (0 : ℝ) ≤ s₁ + s₂ - c),
        mul_le_mul_of_nonneg_right k3 hc]
    linarith
  · intro h
    have k := hk.mpr h
    have k2 : ((1 - r₂) * (1 - γ r₁ r₂)) ^ 2 < ((1 - r₁) * (1 - γ r₂ r₁)) ^ 2 :=
      pow_lt_pow_left₀ k a1.le (by norm_num)
    have k3 : (1 - r₂) ^ 2 < (1 - r₁) ^ 2 := pow_lt_pow_left₀ (by linarith) hv.le (by norm_num)
    rw [mul_pow, mul_pow] at k2
    rcases hc.lt_or_eq with hc' | hc'
    · nlinarith [mul_lt_mul_of_pos_right k3 hc',
        mul_le_mul_of_nonneg_right k2.le (by linarith : (0 : ℝ) ≤ s₁ + s₂ - c)]
    · subst hc'
      have : 0 < s₁ + s₂ - 0 := by linarith
      nlinarith [mul_lt_mul_of_pos_right k2 this]

/-- **Proposition 1.** Fix the information.

* (i) Whichever unit leads, and for every realization of the messages, concurrent decision-making
  yields weakly less coordination loss than sequential decision-making. The inequality is strict
  unless the follower's posterior mean equals the leader's state. Here `(rL, rF)` is either
  `(r₁, r₂)` or `(r₂, r₁)`, and `ν` is the leader's posterior about the follower's state.
* (ii) If the follower's state carries the same information loss whichever unit follows
  (`c₁ = c₂`), the expected coordination loss is lower when unit 1 moves first than when unit 2
  does iff `r₁ < r₂`. -/
theorem prop1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] :
    (∀ rL rF : ℝ, Unit01 rL → Unit01 rF → ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      Integrable (fun x : ℝ => x) ν → Integrable (fun x : ℝ => x ^ 2) ν → ∀ θL : ℝ,
      coordConcPost rL rF θL ν ≤ coordSeqPost rL rF θL ν ∧
        (coordConcPost rL rF θL ν < coordSeqPost rL rF θL ν ↔ θL ≠ ∫ x, x ∂ν)) ∧
    (∀ (E : Env Ω P) (r₁ r₂ : ℝ), Unit01 r₁ → Unit01 r₂ → E.c₁ = E.c₂ → 0 < E.s₁ + E.s₂ →
      (∫ ω, (E.seqD₁ r₁ r₂ ω - E.seqD₂ r₁ r₂ ω) ^ 2 ∂P <
          ∫ ω, (E.swap.seqD₁ r₂ r₁ ω - E.swap.seqD₂ r₂ r₁ ω) ^ 2 ∂P ↔ r₁ < r₂)) := by
  refine ⟨fun rL rF hL hF ν _ i1 i2 θL => coordConc_le_seq i1 i2 hL hF θL, ?_⟩
  intro E r₁ r₂ h₁ h₂ hc hs
  have e1 := E.coord_seq (r₁ := r₁) (r₂ := r₂)
  have e2 := E.swap.coord_seq (r₁ := r₂) (r₂ := r₁)
  simp only [Env.swap_s₁, Env.swap_s₂, Env.swap_c₂] at e2
  rw [e1, e2, hc]
  have hs₁ : 0 ≤ E.s₁ := integral_nonneg fun _ => sq_nonneg _
  exact coordSeqF_lt_iff h₁ h₂ E.c₂_nonneg (by linarith [E.c₂_le]) hs

end WhoVsWhen
