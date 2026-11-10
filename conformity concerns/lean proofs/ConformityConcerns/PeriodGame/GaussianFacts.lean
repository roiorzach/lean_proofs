import ConformityConcerns.PeriodGame.Defs
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Gaussian facts for the period game

For a period game with jointly Gaussian `(Z, v)` we write `v = s̃ Z + R` with the residual
`R = v - s̃ Z`. `R` is uncorrelated with, hence independent of, `Z`, and Gaussian. Consequently,
for any measurable `g` with a measurable left inverse `h`, the joint law of `(g Z, v)` is
`law (g Z) ⊗ₘ postK h`, where `postK h x = N(s̃ h(x) + E R, Var R)` is the posterior of `v` after
the public learns `Z = h x`.
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Facts about one-dimensional Gaussians -/

lemma gauss_pos_Ioo {m : ℝ} {σ : ℝ≥0} (hσ : σ ≠ 0) {a b : ℝ} (hab : a < b) :
    0 < gaussianReal m σ (Ioo a b) := by
  refine pos_iff_ne_zero.2 fun h => ?_
  have := gaussianReal_absolutelyContinuous' m hσ h
  rw [Real.volume_Ioo] at this
  simp only [ENNReal.ofReal_eq_zero] at this
  linarith

lemma gauss_pos_Ioi {m : ℝ} {σ : ℝ≥0} (hσ : σ ≠ 0) (a : ℝ) :
    0 < gaussianReal m σ (Ioi a) :=
  lt_of_lt_of_le (gauss_pos_Ioo hσ (lt_add_one a)) (measure_mono Ioo_subset_Ioi_self)

lemma gauss_pos_Iio {m : ℝ} {σ : ℝ≥0} (hσ : σ ≠ 0) (a : ℝ) :
    0 < gaussianReal m σ (Iio a) :=
  lt_of_lt_of_le (gauss_pos_Ioo hσ (sub_one_lt a)) (measure_mono Ioo_subset_Iio_self)

lemma gauss_singleton {m : ℝ} {σ : ℝ≥0} (hσ : σ ≠ 0) (x : ℝ) :
    gaussianReal m σ {x} = 0 :=
  gaussianReal_absolutelyContinuous m hσ (Real.volume_singleton)

lemma gauss_support {m : ℝ} {σ : ℝ≥0} (hσ : σ ≠ 0) : (gaussianReal m σ).support = univ := by
  have h := (gaussianReal_absolutelyContinuous' m hσ).support_mono
  rw [Measure.support_eq_univ] at h
  exact univ_subset_iff.mp h

lemma gauss_integrable_sub (m : ℝ) (σ : ℝ≥0) (x₀ : ℝ) :
    Integrable (fun x : ℝ => x - x₀) (gaussianReal m σ) :=
  (memLp_id_gaussianReal 1).integrable le_rfl |>.sub (integrable_const _)

lemma gauss_setIntegral_Ici_pos {m : ℝ} {σ : ℝ≥0} (hσ : σ ≠ 0) (x₀ : ℝ) :
    0 < ∫ x in Ici x₀, (x - x₀) ∂(gaussianReal m σ) := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · refine lt_of_lt_of_le (gauss_pos_Ioi hσ x₀) (measure_mono fun x hx => ?_)
    simp only [mem_Ioi] at hx
    refine ⟨?_, le_of_lt hx⟩
    simp only [Function.mem_support, ne_eq, sub_eq_zero]
    exact ne_of_gt hx
  · exact ae_restrict_of_forall_mem measurableSet_Ici fun x hx => sub_nonneg.2 hx
  · exact (gauss_integrable_sub m σ x₀).integrableOn

lemma gauss_setIntegral_Iic_neg {m : ℝ} {σ : ℝ≥0} (hσ : σ ≠ 0) (x₀ : ℝ) :
    ∫ x in Iic x₀, (x - x₀) ∂(gaussianReal m σ) < 0 := by
  have h : 0 < ∫ x in Iic x₀, (x₀ - x) ∂(gaussianReal m σ) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · refine lt_of_lt_of_le (gauss_pos_Iio hσ x₀) (measure_mono fun x hx => ?_)
      simp only [mem_Iio] at hx
      refine ⟨?_, le_of_lt hx⟩
      simp only [Function.mem_support, ne_eq, sub_eq_zero]
      exact ne_of_gt hx
    · exact ae_restrict_of_forall_mem measurableSet_Iic fun x hx => sub_nonneg.2 hx
    · exact ((gauss_integrable_sub m σ x₀).neg.congr
        (ae_of_all _ fun x => by simp)).integrableOn
  have e : ∫ x in Iic x₀, (x - x₀) ∂(gaussianReal m σ) =
      -∫ x in Iic x₀, (x₀ - x) ∂(gaussianReal m σ) := by
    rw [← integral_neg]; congr 1; funext x; ring
  linarith

/-- An a.e. property on a set of positive measure of an atomless measure holds at two
distinct points. -/
lemma exists_two_of_ae {μ : Measure ℝ} (hna : ∀ x, μ {x} = 0) {U : Set ℝ} (hU : 0 < μ U)
    {p : ℝ → Prop} (hp : ∀ᵐ x ∂μ, x ∈ U → p x) :
    ∃ x₀ x₁, x₀ ∈ U ∧ x₁ ∈ U ∧ x₀ ≠ x₁ ∧ p x₀ ∧ p x₁ := by
  have hbad : μ {x | ¬ (x ∈ U → p x)} = 0 := ae_iff.1 hp
  have h1 : ∀ F : Set ℝ, μ F = 0 → ∃ x ∈ U, x ∉ F ∧ p x := by
    intro F hF
    by_contra hcon
    push Not at hcon
    have : U ⊆ F ∪ {x | ¬ (x ∈ U → p x)} := by
      intro x hx
      by_cases hxF : x ∈ F
      · exact Or.inl hxF
      · exact Or.inr fun h => hcon x hx hxF (h hx)
    have h3 : μ U ≤ μ (F ∪ {x | ¬ (x ∈ U → p x)}) := measure_mono this
    have h2 : μ (F ∪ {x | ¬ (x ∈ U → p x)}) ≤ μ F + μ {x | ¬ (x ∈ U → p x)} :=
      measure_union_le _ _
    rw [hF, hbad, add_zero] at h2
    exact absurd (lt_of_lt_of_le hU (h3.trans h2)) (lt_irrefl 0)
  obtain ⟨x₀, hx₀U, -, hx₀⟩ := h1 ∅ measure_empty
  obtain ⟨x₁, hx₁U, hx₁F, hx₁⟩ := h1 {x₀} (hna x₀)
  exact ⟨x₀, x₁, hx₀U, hx₁U, fun h => hx₁F (h ▸ rfl), hx₀, hx₁⟩

namespace Game

variable (G : Game Ω)

/-- The residual `R = v - s̃ Z`. -/
noncomputable def resid (ω : Ω) : ℝ := G.v ω - G.sens * G.Z ω

/-- `E R = μ(h) - s̃ E Z`. -/
noncomputable def residMean : ℝ := ∫ ω, G.resid ω ∂G.P

/-- `Var R = Var(v | Z)`, the posterior variance in a revealing equilibrium. -/
noncomputable def condVar : ℝ := variance G.resid G.P

/-- The posterior of `v` once the public learns `Z = h x`: `N(s̃ h(x) + E R, Var R)`. -/
noncomputable def postK (h : ℝ → ℝ) (hh : Measurable h) : Kernel ℝ ℝ where
  toFun x := gaussianReal (G.sens * h x + G.residMean) G.condVar.toNNReal
  measurable' := measurable_gaussianReal.comp
    (((measurable_const.mul hh).add_const _).prodMk measurable_const)

@[simp] lemma postK_apply (h : ℝ → ℝ) (hh : Measurable h) (x : ℝ) :
    G.postK h hh x = gaussianReal (G.sens * h x + G.residMean) G.condVar.toNNReal := rfl

instance (h : ℝ → ℝ) (hh : Measurable h) : IsMarkovKernel (G.postK h hh) :=
  ⟨fun x => by rw [postK_apply]; infer_instance⟩

lemma condVar_nonneg : 0 ≤ G.condVar := variance_nonneg _ _

lemma postK_mean (h : ℝ → ℝ) (hh : Measurable h) (x : ℝ) :
    ∫ b, b ∂(G.postK h hh x) = G.sens * h x + G.residMean := by
  rw [postK_apply, integral_id_gaussianReal]

lemma postK_var (h : ℝ → ℝ) (hh : Measurable h) (x : ℝ) :
    variance id (G.postK h hh x) = G.condVar := by
  rw [postK_apply, variance_id_gaussianReal, Real.coe_toNNReal _ G.condVar_nonneg]

lemma postK_sq_integrable (h : ℝ → ℝ) (hh : Measurable h) (x : ℝ) :
    Integrable (fun b : ℝ => b ^ 2) (G.postK h hh x) := by
  rw [postK_apply]
  have := (memLp_id_gaussianReal (μ := G.sens * h x + G.residMean)
    (v := G.condVar.toNNReal) 2).integrable_norm_pow (by norm_num)
  simpa using this

variable {G}

section Std

variable (hG : G.Std)
include hG

lemma Std.aemZ : AEMeasurable G.Z G.P := hG.gauss.aemeasurable.fst

lemma Std.aemv : AEMeasurable G.v G.P := hG.gauss.aemeasurable.snd

lemma Std.gZ : HasGaussianLaw G.Z G.P := hG.gauss.fst

lemma Std.gv : HasGaussianLaw G.v G.P := hG.gauss.snd

lemma Std.memLpZ : MemLp G.Z 2 G.P := hG.gZ.memLp_two

lemma Std.memLpv : MemLp G.v 2 G.P := hG.gv.memLp_two

lemma Std.varZ_ne : variance G.Z G.P ≠ 0 := ne_of_gt hG.varZ_pos

lemma Std.gZR : HasGaussianLaw (fun ω => (G.Z ω, G.resid ω)) G.P := by
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ - G.sens • ContinuousLinearMap.fst ℝ ℝ ℝ)
  have h := hG.gauss.map_fun L
  have e : (fun ω => L (G.Z ω, G.v ω)) = fun ω => (G.Z ω, G.resid ω) := by
    funext ω
    simp [L, Game.resid]
  rwa [e] at h

lemma Std.gR : HasGaussianLaw G.resid G.P := hG.gZR.snd

lemma Std.aemR : AEMeasurable G.resid G.P := hG.gR.aemeasurable

lemma Std.memLpR : MemLp G.resid 2 G.P := hG.gR.memLp_two

lemma Std.cov_Z_resid : cov[G.Z, G.resid; G.P] = 0 := by
  have := hG.prob
  have e : G.resid = fun ω => G.v ω - G.sens * G.Z ω := rfl
  rw [e, covariance_fun_sub_right hG.memLpZ hG.memLpv (hG.memLpZ.const_mul _),
    covariance_const_mul_right, covariance_self hG.aemZ, covariance_comm]
  unfold Game.sens
  rw [div_mul_cancel₀ _ hG.varZ_ne, sub_self]

lemma Std.indep : IndepFun G.Z G.resid G.P :=
  HasGaussianLaw.indepFun_of_covariance_eq_zero hG.gZR hG.cov_Z_resid

lemma Std.map_ZR :
    G.P.map (fun ω => (G.Z ω, G.resid ω)) = (G.P.map G.Z).prod (G.P.map G.resid) := by
  have := hG.prob
  exact (indepFun_iff_map_prod_eq_prod_map_map hG.aemZ hG.aemR).1 hG.indep

lemma Std.map_resid : G.P.map G.resid = gaussianReal G.residMean G.condVar.toNNReal :=
  hG.gR.map_eq_gaussianReal

lemma Std.map_Z : G.P.map G.Z = gaussianReal G.meanZ (variance G.Z G.P).toNNReal :=
  hG.gZ.map_eq_gaussianReal

lemma Std.varZ_toNNReal_ne : (variance G.Z G.P).toNNReal ≠ 0 := by
  simpa using hG.varZ_pos

/-- The law of an affine function `k Z + c` of `Z`. -/
lemma Std.map_aff (k c : ℝ) :
    G.P.map (fun ω => k * G.Z ω + c) =
      gaussianReal (k * G.meanZ + c) (⟨k ^ 2, sq_nonneg _⟩ * (variance G.Z G.P).toNNReal) := by
  have e : (fun ω => k * G.Z ω + c) = (fun x => x + c) ∘ (fun x => k * x) ∘ G.Z := rfl
  rw [e, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop)
      ((measurable_const_mul k).comp_aemeasurable hG.aemZ),
    ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hG.aemZ, hG.map_Z,
    gaussianReal_map_const_mul, gaussianReal_map_add_const]
  rfl

lemma Std.aff_var_ne {k : ℝ} (hk : k ≠ 0) :
    (⟨k ^ 2, sq_nonneg _⟩ * (variance G.Z G.P).toNNReal : ℝ≥0) ≠ 0 := by
  refine mul_ne_zero ?_ hG.varZ_toNNReal_ne
  intro h
  have : k ^ 2 = 0 := congrArg NNReal.toReal h
  exact hk (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)

lemma Std.residMean_eq : G.residMean = G.norm - G.sens * G.meanZ := by
  have := hG.prob
  unfold Game.residMean Game.resid Game.norm Game.meanZ
  rw [integral_sub hG.gv.integrable (hG.gZ.integrable.const_mul _), integral_const_mul]

/-- **Conditional law.** If `g` has a measurable left inverse `h`, the joint law of `(g Z, v)` is
`law (g Z) ⊗ₘ postK h`. -/
theorem Std.map_comp_v {g h : ℝ → ℝ} (hg : Measurable g) (hh : Measurable h)
    (hgh : ∀ z, h (g z) = z) :
    G.P.map (fun ω => (g (G.Z ω), G.v ω)) = (G.P.map (fun ω => g (G.Z ω))) ⊗ₘ G.postK h hh := by
  have := hG.prob
  set μ := G.P.map G.Z with hμ
  set ρ := G.P.map G.resid with hρ
  let T : ℝ × ℝ → ℝ × ℝ := fun p => (g p.1, G.sens * p.1 + p.2)
  have hT : Measurable T :=
    (hg.comp measurable_fst).prodMk ((measurable_const.mul measurable_fst).add measurable_snd)
  have e1 : G.P.map (fun ω => (g (G.Z ω), G.v ω)) = (μ.prod ρ).map T := by
    rw [← hG.map_ZR, AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hG.gZR.aemeasurable]
    congr 1
    funext ω
    simp [T, Game.resid]
  have e2 : G.P.map (fun ω => g (G.Z ω)) = μ.map g := by
    rw [hμ, AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hG.aemZ]
    rfl
  rw [e1, e2]
  refine Measure.ext_prod fun {A B} hA hB => ?_
  rw [Measure.map_apply hT (hA.prod hB), Measure.prod_apply (hT (hA.prod hB)),
    Measure.compProd_apply_prod hA hB,
    setLIntegral_map hA (Kernel.measurable_coe _ hB) hg, ← lintegral_indicator (hg hA)]
  congr 1
  funext z
  by_cases hz : g z ∈ A
  · rw [indicator_of_mem (show z ∈ g ⁻¹' A from hz)]
    have e3 : Prod.mk z ⁻¹' (T ⁻¹' A ×ˢ B) = (fun r => G.sens * z + r) ⁻¹' B := by
      ext r
      simp [T, hz]
    rw [e3, postK_apply, hgh, ← Measure.map_apply (measurable_const_add _) hB, hρ,
      hG.map_resid, gaussianReal_map_const_add, add_comm]
  · rw [indicator_of_notMem (show z ∉ g ⁻¹' A from hz)]
    have e3 : Prod.mk z ⁻¹' (T ⁻¹' A ×ˢ B) = ∅ := by
      ext r
      simp [T, hz]
    rw [e3, measure_empty]

end Std

end Game

end CC.LG
