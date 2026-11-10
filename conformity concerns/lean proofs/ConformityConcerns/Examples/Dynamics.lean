import ConformityConcerns.Dynamics.Defs
import ConformityConcerns.Learning.Defs
import ConformityConcerns.ODE.Defs
import ConformityConcerns.PeriodGame.Defs
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Examples: the hypotheses of the dynamic, learning, period-game and ODE results are satisfiable

* `γ_t` uniform on `[0,1]` has full support on `[0,1]` (Proposition 2, A1);
* `κ_t` uniform on `[1/8, 9/8]` has `Pr(κ_t < κck) > 0` and no atom at `κck`, and `κ_t` uniform on
  `[1, 2]` has `inf Supp > κck` (Proposition A1);
* `γ_t = |N(0,1)|` has support in `[0,∞)` and is unbounded above (Proposition A2);
* `Σ₁ = I` is positive definite;
* `μ, ν_t ~ N(0,1)` satisfy the hypotheses of Propositions A4 and A6 across histories;
* the common-knowledge period game satisfies the standing assumptions of the period game;
* `Ψ(x) = x/8`, `Γ(x) = x` satisfy Lemma A3 (ii) and `Ψ(x) = 2x`, `Γ(x) = x` satisfy Lemma A3 (i).
-/

namespace CC.Examples

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-- The uniform law on `[0,1]`. -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unif01 :=
  ⟨by simp [unif01, Real.volume_Icc]⟩

lemma fullSupport_unif01 : FullSupportUnit unif01 where
  prob := inferInstance
  supp := by simp [unif01, Measure.restrict_apply (measurableSet_Icc.compl)]
  pos := fun a b ha hab hb => by
    rw [unif01, Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_left.mpr (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha hb))]
    simp [Real.volume_Ioo, hab]

/-- `Σ₁ = I`. -/
lemma posDef_one : (1 : M2).PosDef := Matrix.PosDef.one

/-- `κ_t` uniform on `[1/8, 9/8]`. -/
noncomputable def unifKappaLow : Measure ℝ := volume.restrict (Icc (1 / 8) (9 / 8))

instance : IsProbabilityMeasure unifKappaLow :=
  ⟨by simp [unifKappaLow, Real.volume_Icc]; norm_num⟩

lemma unifKappaLow_hyp :
    unifKappaLow (Iic 0) = 0 ∧ unifKappaLow {κck} = 0 ∧ 0 < (unifKappaLow (Iio κck)).toReal := by
  refine ⟨?_, ?_, ?_⟩
  · rw [unifKappaLow, Measure.restrict_apply measurableSet_Iic]
    have : Iic (0 : ℝ) ∩ Icc (1 / 8) (9 / 8) = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      intro h; linarith [h.1, h.2.1]
    rw [this]; simp
  · rw [unifKappaLow, Measure.restrict_apply (measurableSet_singleton _)]
    exact measure_mono_null inter_subset_left (Real.volume_singleton)
  · rw [unifKappaLow, Measure.restrict_apply measurableSet_Iio]
    have : Iio κck ∩ Icc (1 / 8 : ℝ) (9 / 8) = Ico (1 / 8) (1 / 4) := by
      ext x; simp only [κck, mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [this, Real.volume_Ico, ENNReal.toReal_ofReal (by norm_num)]
    norm_num

/-- `κ_t` uniform on `[1, 2]`. -/
noncomputable def unifKappaHigh : Measure ℝ := volume.restrict (Icc 1 2)

instance : IsProbabilityMeasure unifKappaHigh :=
  ⟨by simp [unifKappaHigh, Real.volume_Icc]; norm_num⟩

lemma unifKappaHigh_hyp : unifKappaHigh (Iic 0) = 0 ∧ ∃ κ₀, κck < κ₀ ∧ unifKappaHigh (Iio κ₀) = 0 := by
  refine ⟨?_, 1 / 2, by norm_num [κck], ?_⟩
  · rw [unifKappaHigh, Measure.restrict_apply measurableSet_Iic]
    have : Iic (0 : ℝ) ∩ Icc 1 2 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      intro h; linarith [h.1, h.2.1]
    rw [this]; simp
  · rw [unifKappaHigh, Measure.restrict_apply measurableSet_Iio]
    have : Iio (1 / 2 : ℝ) ∩ Icc 1 2 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_empty_iff_false, iff_false]
      intro h; linarith [h.1, h.2.1]
    rw [this]; simp

lemma gaussian_pos_Ioi (c : ℝ) : 0 < gaussianReal 0 1 (Ioi c) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Ioi,
    lintegral_pos_iff_support (by unfold gaussianPDF; fun_prop)]
  have : Function.support (gaussianPDF 0 1) = univ := by
    ext x; simp
  rw [this, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- `γ_t = |N(0,1)|`: support in `[0, ∞)`, unbounded above. -/
noncomputable def absGauss : Measure ℝ := (gaussianReal 0 1).map (fun x => |x|)

instance : IsProbabilityMeasure absGauss :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

lemma absGauss_hyp : absGauss (Iio 0) = 0 ∧ ∀ M : ℝ, 0 < absGauss (Ioi M) := by
  constructor
  · rw [absGauss, Measure.map_apply (by fun_prop) measurableSet_Iio]
    have : (fun x : ℝ => |x|) ⁻¹' Iio 0 = ∅ := by
      ext x; simp [abs_nonneg]
    simp [this]
  · intro M
    rw [absGauss, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    refine lt_of_lt_of_le (gaussian_pos_Ioi (max M 0)) (measure_mono fun x hx => ?_)
    simp only [mem_Ioi, mem_preimage] at hx ⊢
    exact lt_of_le_of_lt (le_max_left M 0) (lt_of_lt_of_le hx (le_abs_self x))

/-- `N(0,1)` is atomless, integrable, with mean zero (the hypotheses on `μ` and `ν_t`). -/
lemma gaussian_learning_hyp :
    (∀ x, gaussianReal 0 1 {x} = 0) ∧ Integrable id (gaussianReal 0 1) ∧
      ∫ x, x ∂(gaussianReal 0 1) = 0 := by
  refine ⟨fun x => ?_, (memLp_id_gaussianReal 1).integrable le_rfl, integral_id_gaussianReal⟩
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- The common-knowledge period game satisfies the standing assumptions of the period game. -/
lemma ckGame_std (κ : ℝ) (hκ : 0 < κ) :
    (⟨gaussianReal 0 1, id, id, κ, 0⟩ : LG.Game ℝ).Std where
  prob := inferInstance
  gauss := by
    have h : HasGaussianLaw (id : ℝ → ℝ) (gaussianReal 0 1) :=
      ⟨aemeasurable_id, by rw [Measure.map_id]; infer_instance⟩
    convert h.map ((ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) using 1
    funext x; rfl
  varZ_pos := by simp [variance_id_gaussianReal]
  κ_pos := hκ
  c0_nonneg := le_rfl
  measZ := measurable_id

/-- Lemma A3 (ii) hypotheses: `Ψ(x) = x/8`, `Γ(x) = x`, `β = 1/2`. -/
lemma tail_ii_example : ODE.TailData (fun x => x / 8) id ∧
    ∀ x : ℝ, 0 < x → x / 8 ≤ (1 - 1 / 2) * id ((1 / 2) * x) := by
  refine ⟨⟨fun x _ y _ h => by show x / 8 ≤ y / 8; linarith, monotoneOn_id, by fun_prop,
    by fun_prop, fun x hx => by positivity, fun x hx => hx⟩, fun x hx => by
      show x / 8 ≤ (1 - 1 / 2) * ((1 / 2) * x); linarith⟩

/-- Lemma A3 (i) hypotheses: `Ψ(x) = 2x`, `Γ(x) = x`. -/
lemma tail_i_example : ODE.TailData (fun x => 2 * x) id ∧
    ∀ C : ℝ, ∃ ε > 0, ∀ᶠ x in atTop, 1 + ε ≤ 2 * x / id (x + C) := by
  refine ⟨⟨fun x _ y _ h => by show 2 * x ≤ 2 * y; linarith, monotoneOn_id, by fun_prop,
    by fun_prop, fun x hx => by positivity, fun x hx => hx⟩, fun C => ⟨1 / 2, by norm_num, ?_⟩⟩
  filter_upwards [eventually_gt_atTop (3 * |C| + 1)] with x hx
  have hC : -|C| ≤ C ∧ C ≤ |C| := ⟨neg_abs_le C, le_abs_self C⟩
  have hpos : 0 < x + C := by linarith [abs_nonneg C]
  simp only [id]
  rw [le_div_iff₀ hpos]
  nlinarith [abs_nonneg C]

end CC.Examples
