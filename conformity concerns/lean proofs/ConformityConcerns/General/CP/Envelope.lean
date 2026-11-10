import ConformityConcerns.General.CP.Jump
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Envelope theorem and the tail differential equation

At every type where `a` is continuous, `U'(v) = g'(a(v) - v)` (sandwich between the two
imitation bounds). On an open set of separating types `v ≠ μ`, `G(v) = -U(v) - ℓ(v) = g(a(v) - v)`;
`a(v) ≠ v` (else `G` has an interior minimum `0` with `G'(v) = -ℓ'(v) ≠ 0`), so the local inverse
of `g` near `a(v) - v` gives `a'(v) = ℓ'(v)/g'(v - a(v))`, which is positive because `a` is
monotone and both factors are nonzero.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set Asymptotics
open scoped ENNReal

namespace Setting.IsCPBE

variable {S : Setting} {a : ℝ → ℝ} {φ : ℝ → Measure EReal} (h : S.IsCPBE a φ)
include h

/-- **Envelope theorem.** -/
lemma hasDerivAt_U {v : ℝ} (hc : ContinuousAt a v) :
    HasDerivAt (S.U a φ) (deriv S.g (a v - v)) v := by
  set D := deriv S.g (a v - v) with hDdef
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  -- lower bound: imitation of `v` by `w`
  have hL : HasDerivAt (fun w => -S.g (a v - w)) D v := by
    have h1 : HasDerivAt (fun w => a v - w) (-1) v := (hasDerivAt_id v).const_sub (a v)
    have h2 := ((S.hg.hasDerivAt (a v - v)).comp v h1).neg
    convert h2 using 1 <;> first | rfl | ring
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff] at hL
  have hL' := hL hε
  -- upper bound: mean value inequality for `y ↦ g y - D y` near `a v - v`
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.1 S.hg.continuous_deriv.continuousAt ε hε
  have hball : ∀ p ∈ Metric.ball (a v - v) ρ, ∀ q ∈ Metric.ball (a v - v) ρ,
      |(S.g p - D * p) - (S.g q - D * q)| ≤ ε * |p - q| := by
    intro p hp q hq
    have hdy : ∀ y, HasDerivAt (fun y => S.g y - D * y) (deriv S.g y - D) y := by
      intro y
      have := (S.hg.hasDerivAt y).sub ((hasDerivAt_id' y).const_mul D)
      rw [mul_one] at this
      exact this
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun y => S.g y - D * y) (C := ε)
      (s := Metric.ball (a v - v) ρ) (fun y _ => (hdy y).differentiableAt)
      (fun y hy => by
        rw [(hdy y).deriv, Real.norm_eq_abs]
        have := hρ' (Metric.mem_ball.1 hy)
        rw [Real.dist_eq] at this
        exact this.le)
      (convex_ball _ _) hq hp
    simpa [Real.norm_eq_abs] using this
  have hev : ∀ᶠ w in 𝓝 v, a w - v ∈ Metric.ball (a v - v) ρ ∧
      a w - w ∈ Metric.ball (a v - v) ρ := by
    have t1 : Tendsto (fun w => a w - v) (𝓝 v) (𝓝 (a v - v)) := hc.tendsto.sub_const v
    have t2 : Tendsto (fun w => a w - w) (𝓝 v) (𝓝 (a v - v)) := hc.tendsto.sub tendsto_id
    exact (t1.eventually (Metric.ball_mem_nhds _ hρ)).and
      (t2.eventually (Metric.ball_mem_nhds _ hρ))
  filter_upwards [hL', hev] with w hw1 hw2
  have hic1 := h.ic w v
  have hic2 := h.ic v w
  have hup := hball _ hw2.1 _ hw2.2
  rw [show a w - v - (a w - w) = w - v by ring] at hup
  simp only [Real.norm_eq_abs, smul_eq_mul] at hw1 ⊢
  rw [abs_le] at hw1 hup ⊢
  obtain ⟨hw1a, hw1b⟩ := hw1
  obtain ⟨hupa, hupb⟩ := hup
  constructor <;> linarith

variable (hD : S.D1Inf a φ)
include hD

/-- **The tail differential equation** on an open set of separating types other than `μ`. -/
lemma tail_ode {O : Set ℝ} (hO : IsOpen O) (hsep : ∀ v ∈ O, a ⁻¹' {a v} = {v})
    (hμ : ∀ v ∈ O, v ≠ S.μ) :
    ContDiffOn ℝ 1 a O ∧ ∀ v ∈ O, 0 < deriv S.ℓ v / deriv S.g (v - a v) ∧
      HasDerivAt a (deriv S.ℓ v / deriv S.g (v - a v)) v := by
  have hcont : ∀ v ∈ O, ContinuousAt a v := fun v hv => h.continuousAt_of_sep hD hO hsep hv
  have hGO : ∀ v ∈ O, S.g (a v - v) = -S.U a φ v - S.ℓ v := by
    intro v hv; rw [h.U_sep (hsep v hv)]; ring
  -- `a v ≠ v` on `O`
  have hz0 : ∀ v ∈ O, a v - v ≠ 0 := by
    intro v hv h0
    have hG : HasDerivAt (fun w => -S.U a φ w - S.ℓ w) (-deriv S.g (a v - v) - deriv S.ℓ v) v :=
      (h.hasDerivAt_U (hcont v hv)).neg.sub (S.hℓ.hasDerivAt v)
    have hmin : IsLocalMin (fun w => -S.U a φ w - S.ℓ w) v := by
      filter_upwards [hO.mem_nhds hv] with w hw
      rw [← hGO w hw, ← hGO v hv, h0, S.hg.zero]
      exact S.hg.nonneg _
    have := hmin.hasDerivAt_eq_zero hG
    rw [h0, S.hg.deriv_zero] at this
    exact S.hℓ.deriv_ne_zero (hμ v hv) (by linarith)
  have hderiv : ∀ v ∈ O, HasDerivAt a (deriv S.ℓ v / deriv S.g (v - a v)) v := by
    intro v hv
    have hG : HasDerivAt (fun w => -S.U a φ w - S.ℓ w) (-deriv S.g (a v - v) - deriv S.ℓ v) v :=
      (h.hasDerivAt_U (hcont v hv)).neg.sub (S.hℓ.hasDerivAt v)
    have hgd : deriv S.g (a v - v) ≠ 0 := S.hg.deriv_ne_zero (hz0 v hv)
    have hs := S.hg.hasStrictDerivAt (a v - v)
    have hli := hs.eventually_left_inverse hgd
    have hinv := hs.to_localInverse hgd
    set L := HasStrictDerivAt.localInverse S.g (deriv S.g (a v - v)) (a v - v) hs hgd with hLdef
    have hzt : Tendsto (fun w => a w - w) (𝓝 v) (𝓝 (a v - v)) :=
      (hcont v hv).tendsto.sub tendsto_id
    have heq : (fun w => a w - w) =ᶠ[𝓝 v] (L ∘ fun w => -S.U a φ w - S.ℓ w) := by
      filter_upwards [hzt.eventually hli, hO.mem_nhds hv] with w hw1 hw2
      simp only [Function.comp]
      rw [← hGO w hw2]
      exact hw1.symm
    have hinv' : HasDerivAt L (deriv S.g (a v - v))⁻¹ (-S.U a φ v - S.ℓ v) := by
      rw [← hGO v hv]; exact hinv.hasDerivAt
    have hz := (hinv'.comp v hG).congr_of_eventuallyEq heq
    have ha : HasDerivAt a
        ((deriv S.g (a v - v))⁻¹ * (-deriv S.g (a v - v) - deriv S.ℓ v) + 1) v := by
      have := hz.add (hasDerivAt_id' v)
      convert this using 1
      funext w; simp
    convert ha using 1
    have hneg : deriv S.g (v - a v) = -deriv S.g (a v - v) := by
      rw [show v - a v = -(a v - v) by ring, S.hg.deriv_neg]
    rw [hneg]
    field_simp
    ring
  have hcd : ContDiffOn ℝ 1 a O := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hO).2
      ⟨fun v hv => (hderiv v hv).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    have heq : EqOn (deriv a) (fun v => deriv S.ℓ v / deriv S.g (v - a v)) O :=
      fun v hv => (hderiv v hv).deriv
    refine ContinuousOn.congr ?_ heq
    apply ContinuousOn.div S.hℓ.continuous_deriv.continuousOn
    · exact S.hg.continuous_deriv.comp_continuousOn
        (continuousOn_id.sub fun v hv => (hcont v hv).continuousWithinAt)
    · intro v hv
      exact S.hg.deriv_ne_zero (fun h0 => hz0 v hv (by linarith))
  refine ⟨hcd, fun v hv => ⟨?_, hderiv v hv⟩⟩
  have hnn := (hderiv v hv).nonneg_of_monotone h.monotone
  have hne : deriv S.ℓ v / deriv S.g (v - a v) ≠ 0 :=
    div_ne_zero (S.hℓ.deriv_ne_zero (hμ v hv))
      (S.hg.deriv_ne_zero (fun h0 => hz0 v hv (by linarith)))
  exact lt_of_le_of_ne hnn (Ne.symm hne)

end Setting.IsCPBE

end CC.General
