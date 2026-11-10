import ConformityConcerns.General.CP.Convex

/-!
# Basic consequences of the equilibrium conditions

Incentive-compatibility inequalities (`U(v) ≥ U(w) + g(a w - w) - g(a w - v)`), monotonicity
of the action rule, conformity losses of separating and pooling actions, and properties of the
type distribution.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace TypeDist

variable {F : Measure ℝ} (hF : TypeDist F)
include hF

lemma eq_zero_iff {s : Set ℝ} : F s = 0 ↔ volume s = 0 := by
  obtain ⟨ψ, hψc, hψpos, rfl⟩ := hF.density
  rw [withDensity_apply_eq_zero' (hψc.measurable.ennreal_ofReal.aemeasurable)]
  have : {x | ENNReal.ofReal (ψ x) ≠ 0} = univ := by
    ext x; simp [hψpos x]
  rw [this, univ_inter]

lemma singleton_eq_zero (h : ℝ) : F {h} = 0 := by
  rw [hF.eq_zero_iff]; exact Real.volume_singleton

lemma ae_ne (h : ℝ) : ∀ᵐ v ∂F, v ≠ h := by
  rw [ae_iff]; simpa using hF.singleton_eq_zero h

lemma Ioo_pos {x y : ℝ} (hxy : x < y) : 0 < F (Ioo x y) := by
  rw [pos_iff_ne_zero, Ne, hF.eq_zero_iff, Real.volume_Ioo]
  simpa using hxy

end TypeDist

namespace Setting

variable {S : Setting} {a : ℝ → ℝ} {φ : ℝ → Measure EReal}

lemma ℓbar_coe (v : ℝ) : S.ℓbar (v : EReal) = ENNReal.ofReal (S.ℓ v) := by
  unfold Setting.ℓbar
  simp

lemma ℓbar_top : S.ℓbar ⊤ = ∞ := by unfold Setting.ℓbar; simp

lemma ℓbar_bot : S.ℓbar ⊥ = ∞ := by unfold Setting.ℓbar; simp

lemma confLoss_of_dirac {x v : ℝ} (hx : φ x = Measure.dirac (v : EReal)) :
    S.confLoss φ x = ENNReal.ofReal (S.ℓ v) := by
  unfold Setting.confLoss
  rw [hx, lintegral_dirac, ℓbar_coe]

lemma loss_toReal (x v : ℝ) (hx : S.confLoss φ x ≠ ∞) :
    (S.loss φ x v).toReal = S.g (x - v) + (S.confLoss φ x).toReal := by
  unfold Setting.loss
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hx, ENNReal.toReal_ofReal (S.hg.nonneg _)]

lemma U_le (v : ℝ) : S.U a φ v ≤ -S.g (a v - v) := by
  unfold Setting.U
  have := ENNReal.toReal_nonneg (a := S.confLoss φ (a v))
  linarith

namespace IsCPBE

variable (h : S.IsCPBE a φ)
include h

lemma loss_ne_top (v : ℝ) : S.loss φ (a v) v ≠ ∞ := by
  unfold Setting.loss
  exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, (h.finite v).ne⟩

omit h in
lemma neg_U (v : ℝ) : -S.U a φ v = S.g (a v - v) + (S.confLoss φ (a v)).toReal := by
  unfold Setting.U; ring

/-- Incentive compatibility: type `v` can imitate type `w`. -/
lemma ic (v w : ℝ) : S.U a φ w + S.g (a w - w) - S.g (a w - v) ≤ S.U a φ v := by
  have h1 := h.optimal v (a w)
  have hfin : S.loss φ (a w) v ≠ ∞ := by
    unfold Setting.loss
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, (h.finite w).ne⟩
  have h2 := ENNReal.toReal_mono hfin h1
  rw [loss_toReal _ _ (h.finite v).ne, loss_toReal _ _ (h.finite w).ne] at h2
  unfold Setting.U
  linarith

/-- No profitable deviation to an action `x` with finite conformity loss. -/
lemma not_dev (v x : ℝ) (hx : S.confLoss φ x ≠ ∞)
    (hlt : S.g (x - v) + (S.confLoss φ x).toReal < -S.U a φ v) : False := by
  have h1 := h.optimal v x
  have hfin : S.loss φ x v ≠ ∞ := by
    unfold Setting.loss
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hx⟩
  have h2 := ENNReal.toReal_mono hfin h1
  rw [loss_toReal _ _ (h.finite v).ne, loss_toReal _ _ hx] at h2
  rw [neg_U] at hlt
  linarith

/-- The action rule is weakly increasing. -/
lemma monotone : Monotone a := by
  intro v₁ v₂ hv
  by_contra hlt
  replace hlt := not_le.1 hlt
  rcases hv.lt_or_eq with hv | hv
  · have h1 := h.ic v₁ v₂
    have h2 := h.ic v₂ v₁
    have := sc_incr_diff S.hg.strictConvex hlt hv
    linarith
  · subst hv; exact lt_irrefl _ hlt

/-- Pooling sets are order-connected. -/
lemma mem_of_between {v w₁ w₂ : ℝ} (h₁ : a w₁ = a v) (h₂ : a w₂ = a v) {u : ℝ}
    (hu₁ : w₁ ≤ u) (hu₂ : u ≤ w₂) : a u = a v :=
  le_antisymm (h₂ ▸ h.monotone hu₂) (h₁ ▸ h.monotone hu₁)

/-- A nondegenerate pooling set has positive probability. -/
lemma F_pos_of_nontrivial {v : ℝ} (hT : (a ⁻¹' {a v}).Nontrivial) :
    0 < S.F (a ⁻¹' {a v}) := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := hT
  simp only [mem_preimage, mem_singleton_iff] at hw₁ hw₂
  rcases hne.lt_or_gt with hlt | hlt
  · refine lt_of_lt_of_le (S.hF.Ioo_pos hlt) (measure_mono fun u hu => ?_)
    exact h.mem_of_between hw₁ hw₂ hu.1.le hu.2.le
  · refine lt_of_lt_of_le (S.hF.Ioo_pos hlt) (measure_mono fun u hu => ?_)
    exact h.mem_of_between hw₂ hw₁ hu.1.le hu.2.le

lemma measurableSet_fiber (v : ℝ) : MeasurableSet (a ⁻¹' {a v}) :=
  h.meas (measurableSet_singleton _)

/-- On path, the belief is concentrated on (the image of) the pooling set. -/
lemma ae_onPath (v : ℝ) :
    ∀ᵐ b ∂(φ (a v)), b ∈ (fun r : ℝ => (r : EReal)) '' (a ⁻¹' {a v}) := by
  have := h.prob (a v)
  have hm : MeasurableSet ((fun r : ℝ => (r : EReal)) '' (a ⁻¹' {a v})) :=
    EReal.measurableEmbedding_coe.measurableSet_image' (h.measurableSet_fiber v)
  rw [ae_iff]
  exact (prob_compl_eq_zero_iff hm).2 (h.onPath_supp v)

/-- Upper bound for an on-path conformity loss by the conformity losses in the pooling set. -/
lemma confLoss_le {v : ℝ} {M : ℝ} (hM : ∀ w, a w = a v → S.ℓ w ≤ M) :
    S.confLoss φ (a v) ≤ ENNReal.ofReal M := by
  have := h.prob (a v)
  unfold Setting.confLoss
  calc ∫⁻ b, S.ℓbar b ∂(φ (a v)) ≤ ∫⁻ _b, ENNReal.ofReal M ∂(φ (a v)) := by
        apply lintegral_mono_ae
        filter_upwards [h.ae_onPath v] with b hb
        obtain ⟨w, hw, rfl⟩ := hb
        rw [ℓbar_coe]
        exact ENNReal.ofReal_le_ofReal (hM w hw)
    _ = ENNReal.ofReal M := by simp

lemma confLoss_toReal_le {v : ℝ} {M : ℝ} (hM : ∀ w, a w = a v → S.ℓ w ≤ M) :
    (S.confLoss φ (a v)).toReal ≤ M := by
  have hM0 : 0 ≤ M := (S.hℓ.nonneg v).trans (hM v rfl)
  exact ENNReal.toReal_le_of_le_ofReal hM0 (h.confLoss_le hM)

/-- Separating action: the conformity loss is `ℓ v`. -/
lemma confLoss_sep {v : ℝ} (hv : a ⁻¹' {a v} = {v}) :
    S.confLoss φ (a v) = ENNReal.ofReal (S.ℓ v) :=
  confLoss_of_dirac (h.onPath_dirac v hv)

lemma U_sep {v : ℝ} (hv : a ⁻¹' {a v} = {v}) : S.U a φ v = -(S.g (a v - v) + S.ℓ v) := by
  unfold Setting.U
  rw [h.confLoss_sep hv, ENNReal.toReal_ofReal (S.hℓ.nonneg v)]

/-- Bayes' rule for a positive-probability pool. -/
lemma confLoss_pool {v : ℝ} (hpos : 0 < S.F (a ⁻¹' {a v})) :
    S.confLoss φ (a v) = ∫⁻ w, ENNReal.ofReal (S.ℓ w) ∂(S.F[|a ⁻¹' {a v}]) := by
  unfold Setting.confLoss
  rw [h.onPath_bayes v hpos]
  rw [EReal.measurableEmbedding_coe.lintegral_map]
  simp only [ℓbar_coe]

/-- In a positive-probability pool, the conformity loss strictly exceeds `ℓ hb` when `ℓ hb` is
strictly below `ℓ w` for all pool types `w ≠ hb`. -/
lemma ℓ_lt_confLoss {v hb : ℝ} (hpos : 0 < S.F (a ⁻¹' {a v}))
    (hlt : ∀ w, a w = a v → w ≠ hb → S.ℓ hb < S.ℓ w) :
    S.ℓ hb < (S.confLoss φ (a v)).toReal := by
  have := S.hF.prob
  rw [← ENNReal.ofReal_lt_iff_lt_toReal (S.hℓ.nonneg _) (h.finite v).ne, h.confLoss_pool hpos]
  have : IsProbabilityMeasure (S.F[|a ⁻¹' {a v}]) := cond_isProbabilityMeasure hpos.ne'
  calc ENNReal.ofReal (S.ℓ hb) = ∫⁻ _w, ENNReal.ofReal (S.ℓ hb) ∂(S.F[|a ⁻¹' {a v}]) := by
        simp
    _ < _ := by
      apply lintegral_strict_mono (IsProbabilityMeasure.ne_zero _)
        S.hℓ.continuous.measurable.ennreal_ofReal.aemeasurable (by simp)
      have h1 : ∀ᵐ w ∂(S.F[|a ⁻¹' {a v}]), w ∈ a ⁻¹' {a v} := ae_cond_mem (h.measurableSet_fiber v)
      have h2 : ∀ᵐ w ∂(S.F[|a ⁻¹' {a v}]), w ≠ hb := cond_absolutelyContinuous.ae_le (S.hF.ae_ne hb)
      filter_upwards [h1, h2] with w hw1 hw2
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (S.hℓ.nonneg _)).2 (hlt w hw1 hw2)

end IsCPBE

end Setting

end CC.General
