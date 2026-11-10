import ConformityConcerns.General.Defs
import ConformityConcerns.General.CP.IC

/-!
# Lemma A2 (Continuity of equilibrium payoffs)
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Setting.IsCPBE

variable {S : Setting} {a : ℝ → ℝ} {φ : ℝ → Measure EReal} (h : S.IsCPBE a φ)
include h

/-- Local boundedness of the action rule (on `[v₀ - 1, v₀ + 1]`). -/
lemma locally_bounded (v₀ : ℝ) : ∃ B : ℝ, ∀ v ∈ Icc (v₀ - 1) (v₀ + 1), |a v| ≤ B := by
  set C₀ := (S.confLoss φ (a v₀)).toReal
  set R₀ := |a v₀ - v₀| + 1
  obtain ⟨R, hR⟩ := S.hg.abs_le_of_le (C₀ + S.g R₀)
  refine ⟨R + |v₀| + 1, fun v hv => ?_⟩
  have h1 := h.ic v v₀
  have h2 := U_le (S := S) (a := a) (φ := φ) v
  have h3 : S.U a φ v₀ + S.g (a v₀ - v₀) = -C₀ := by unfold Setting.U; ring
  have hR₀ : 0 < R₀ := by positivity
  have hb1 := abs_le.1 (le_refl |a v₀ - v₀|)
  have hb2 := hv.1
  have hb3 := hv.2
  have h4 : S.g (a v₀ - v) ≤ S.g R₀ := by
    apply S.hg.le_of_abs_le
    rw [abs_of_pos hR₀, abs_le]
    have := le_abs_self (a v₀ - v₀)
    have := neg_abs_le (a v₀ - v₀)
    constructor <;> linarith
  have h5 : S.g (a v - v) ≤ C₀ + S.g R₀ := by linarith
  have h6 := abs_le.1 (hR _ h5)
  have := le_abs_self v₀
  have := neg_abs_le v₀
  rw [abs_le]
  constructor <;> linarith [h6.1, h6.2]

/-- Continuity of the equilibrium payoff. -/
lemma U_continuous : Continuous (S.U a φ) := by
  rw [continuous_iff_continuousAt]
  intro v
  obtain ⟨B, hB⟩ := h.locally_bounded v
  set R := B + |v| + 1
  have hgc : Continuous S.g := S.hg.smooth.continuous
  have hgd : ∀ z, DifferentiableAt ℝ S.g z := fun z =>
    (S.hg.smooth.differentiable (by norm_num)).differentiableAt
  -- the continuity of `g'` bounds it on the compact set where `a` lives
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    S.hg.continuous_deriv.continuousOn
  have hmv : ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R, |S.g x - S.g y| ≤ (|M| + 1) * |x - y| :=
    fun x hx y hy => by
      have h1 : ‖S.g x - S.g y‖ ≤ (|M| + 1) * ‖x - y‖ :=
        (convex_Icc (-R) R).norm_image_sub_le_of_norm_deriv_le (fun z _ => hgd z)
          (fun z hz => (hM z hz).trans ((le_abs_self M).trans (by linarith))) hy hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at h1
      exact h1
  have hc : ContinuousAt (fun w => S.g (a v - w)) v :=
    (hgc.comp (continuous_const.sub continuous_id)).continuousAt
  rw [Metric.continuousAt_iff] at hc ⊢
  intro ε hε
  obtain ⟨δ₂, hδ₂, hcδ⟩ := hc ε hε
  have hM1 : 0 < |M| + 1 := by positivity
  set δ₁ := ε / (|M| + 1) with hδ₁def
  have hδ₁ : 0 < δ₁ := div_pos hε hM1
  refine ⟨min 1 (min δ₁ δ₂), by positivity, fun w hw => ?_⟩
  have hw1 : dist w v < 1 := lt_of_lt_of_le hw (min_le_left _ _)
  have hwδ₁ : dist w v < δ₁ := lt_of_lt_of_le hw ((min_le_right _ _).trans (min_le_left _ _))
  have hwδ₂ : dist w v < δ₂ := lt_of_lt_of_le hw ((min_le_right _ _).trans (min_le_right _ _))
  rw [Real.dist_eq, abs_lt] at hw1
  obtain ⟨hw1a, hw1b⟩ := hw1
  have hwI : w ∈ Icc (v - 1) (v + 1) := ⟨by linarith, by linarith⟩
  have haw := abs_le.1 (hB w hwI)
  have hv1 := le_abs_self v
  have hv2 := neg_abs_le v
  have hlo := h.ic w v
  have hhi := h.ic v w
  have e1 : |S.g (a v - w) - S.g (a v - v)| < ε := by
    have := hcδ hwδ₂; rwa [Real.dist_eq] at this
  have e2 : |S.g (a w - v) - S.g (a w - w)| < ε := by
    have hmem1 : a w - v ∈ Icc (-R) R := ⟨by linarith [haw.1], by linarith [haw.2]⟩
    have hmem2 : a w - w ∈ Icc (-R) R := ⟨by linarith [haw.1], by linarith [haw.2]⟩
    have hd : |(a w - v) - (a w - w)| < δ₁ := by
      rw [show a w - v - (a w - w) = w - v by ring, ← Real.dist_eq]; exact hwδ₁
    calc |S.g (a w - v) - S.g (a w - w)| ≤ (|M| + 1) * |(a w - v) - (a w - w)| :=
          hmv _ hmem1 _ hmem2
      _ < (|M| + 1) * δ₁ := mul_lt_mul_of_pos_left hd hM1
      _ = ε := by rw [hδ₁def]; field_simp
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at e1 e2
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

end Setting.IsCPBE

/-- **Lemma A2.** In every pure compactified perfect Bayesian equilibrium, the equilibrium payoff
`U(v)` is continuous in `v`, and `a` is locally bounded. -/
theorem lemmaA2 (S : Setting) {a : ℝ → ℝ} {φ : ℝ → Measure EReal} (h : S.IsCPBE a φ) :
    Continuous (S.U a φ) ∧ ∀ v₀ : ℝ, ∃ ε > 0, ∃ B : ℝ, ∀ v ∈ Icc (v₀ - ε) (v₀ + ε), |a v| ≤ B := by
  refine ⟨h.U_continuous, fun v₀ => ⟨1, one_pos, h.locally_bounded v₀⟩⟩

end CC.General
