import ConformityConcerns.General.CP.Index
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Proposition A3 (ii): the fully pooling assessment

The fully pooling strategy `a(v) = c` with on-path posterior `F`, posterior `δ_{+∞}` after
`x > c` and `δ_{-∞}` after `x < c`, is a compactified PBE satisfying `D1^∞`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Setting

variable (S : Setting)

lemma poolBelief_self (c : ℝ) : S.poolBelief c c = S.F.map (fun r : ℝ => (r : EReal)) := by
  unfold Setting.poolBelief; simp

lemma poolBelief_gt {c x : ℝ} (hx : c < x) : S.poolBelief c x = Measure.dirac ⊤ := by
  unfold Setting.poolBelief; simp [hx.ne', hx]

lemma poolBelief_lt {c x : ℝ} (hx : x < c) : S.poolBelief c x = Measure.dirac ⊥ := by
  unfold Setting.poolBelief; simp [hx.ne, not_lt.2 hx.le]

lemma poolBelief_prob (c x : ℝ) : IsProbabilityMeasure (S.poolBelief c x) := by
  have := S.hF.prob
  rcases lt_trichotomy x c with hx | hx | hx
  · rw [S.poolBelief_lt hx]; infer_instance
  · rw [hx, S.poolBelief_self]
    infer_instance
  · rw [S.poolBelief_gt hx]; infer_instance

lemma confLoss_poolBelief_self (c : ℝ) :
    S.confLoss (S.poolBelief c) c = ∫⁻ v, ENNReal.ofReal (S.ℓ v) ∂S.F := by
  unfold Setting.confLoss
  rw [S.poolBelief_self, EReal.measurableEmbedding_coe.lintegral_map]
  simp only [ℓbar_coe]

lemma confLoss_poolBelief_ne {c x : ℝ} (hx : x ≠ c) : S.confLoss (S.poolBelief c) x = ∞ := by
  unfold Setting.confLoss
  rcases hx.lt_or_gt with hx | hx
  · rw [S.poolBelief_lt hx, lintegral_dirac, ℓbar_bot]
  · rw [S.poolBelief_gt hx, lintegral_dirac, ℓbar_top]

lemma fullPool_isCPBE (c : ℝ) : S.IsCPBE (fun _ => c) (S.poolBelief c) := by
  have := S.hF.prob
  have hpre : (fun _ : ℝ => c) ⁻¹' {c} = univ := by ext; simp
  refine ⟨measurable_const, S.poolBelief_prob c, ?_, ?_, ?_, ?_, ?_⟩
  · intro v x
    by_cases hx : x = c
    · rw [hx]
    · unfold Setting.loss
      rw [S.confLoss_poolBelief_ne hx, add_top]
      exact le_top
  · intro v
    simp only [hpre, image_univ]
    rw [S.poolBelief_self, EReal.measurableEmbedding_coe.map_apply]
    rw [preimage_range]
    exact measure_univ
  · intro v _
    simp only [hpre, cond_univ]
    exact S.poolBelief_self c
  · intro v hv
    simp only [hpre] at hv
    have : (v + 1) ∈ ({v} : Set ℝ) := hv ▸ mem_univ (v + 1)
    simp at this
  · intro v
    show S.confLoss (S.poolBelief c) c < ∞
    rw [S.confLoss_poolBelief_self]
    exact S.integrable.lintegral_lt_top

/-- The index after `x` in the fully pooling assessment. -/
lemma fullPool_indiff (c x v : ℝ) :
    S.indiff (fun _ => c) (S.poolBelief c) x v =
      S.g (x - v) - S.g (c - v) - (S.confLoss (S.poolBelief c) c).toReal := by
  unfold Setting.indiff Setting.U
  ring

/-- `I_x'(v) = g'(c - v) - g'(x - v)` in the fully pooling assessment. -/
lemma fullPool_hasDerivAt (c x v : ℝ) :
    HasDerivAt (S.indiff (fun _ => c) (S.poolBelief c) x)
      (deriv S.g (c - v) - deriv S.g (x - v)) v := by
  have h1 : ∀ y : ℝ, HasDerivAt (fun w => S.g (y - w)) (-deriv S.g (y - v)) v := fun y => by
    have hl : HasDerivAt (fun w => y - w) (-1) v := (hasDerivAt_id v).const_sub y
    have := (S.hg.hasDerivAt (y - v)).comp v hl
    convert this using 1 <;> first | rfl | ring
  have h2 := ((h1 x).sub (h1 c)).sub_const (S.confLoss (S.poolBelief c) c).toReal
  have e : S.indiff (fun _ => c) (S.poolBelief c) x = fun w =>
      S.g (x - w) - S.g (c - w) - (S.confLoss (S.poolBelief c) c).toReal :=
    funext fun w => S.fullPool_indiff c x w
  rw [e]
  exact h2.congr_deriv (by ring)

/-- If `x > c`, then `S^∞(x) = {+∞}`: `I_x` is strictly decreasing and tends to
`-d L_g - M_f < 0` as `v → +∞`, with `d = x - c`. -/
lemma fullPool_survivors_gt {c x : ℝ} (hgt : c < x) :
    S.survivors (fun _ => c) (S.poolBelief c) x = {(⊤ : EReal)} := by
  refine survivors_eq_top (strictAnti_of_deriv_neg fun v => ?_) ?_
  · rw [(S.fullPool_hasDerivAt c x v).deriv]
    exact sub_neg.2 (S.hg.deriv_strictMono (by linarith))
  · obtain ⟨s, hs⟩ := (S.hg.eventually_neg_of_Lg (d := x - c) (by linarith)
      (M := (S.confLoss (S.poolBelief c) c).toReal) ENNReal.toReal_nonneg).exists
    refine ⟨s + x, ?_⟩
    rw [S.fullPool_indiff, show x - (s + x) = -s by ring, show c - (s + x) = -(s + (x - c)) by ring,
      S.hg.even, S.hg.even]
    exact hs

/-- If `x < c`, then `S^∞(x) = {-∞}`, by the symmetric calculation. -/
lemma fullPool_survivors_lt {c x : ℝ} (hlt : x < c) :
    S.survivors (fun _ => c) (S.poolBelief c) x = {(⊥ : EReal)} := by
  refine survivors_eq_bot (strictMono_of_deriv_pos fun v => ?_) ?_
  · rw [(S.fullPool_hasDerivAt c x v).deriv]
    exact sub_pos.2 (S.hg.deriv_strictMono (by linarith))
  · obtain ⟨s, hs⟩ := (S.hg.eventually_neg_of_Lg (d := c - x) (by linarith)
      (M := (S.confLoss (S.poolBelief c) c).toReal) ENNReal.toReal_nonneg).exists
    refine ⟨x - s, ?_⟩
    rw [S.fullPool_indiff, show x - (x - s) = s by ring, show c - (x - s) = s + (c - x) by ring]
    exact hs

lemma fullPool_D1Inf (c : ℝ) : S.D1Inf (fun _ => c) (S.poolBelief c) := by
  intro x hx
  have hxc : x ≠ c := fun h => hx ⟨0, h.symm⟩
  rcases hxc.lt_or_gt with hlt | hgt
  · rw [S.poolBelief_lt hlt, S.fullPool_survivors_lt hlt]
    exact support_dirac_subset _
  · rw [S.poolBelief_gt hgt, S.fullPool_survivors_gt hgt]
    exact support_dirac_subset _

end Setting

end CC.General
