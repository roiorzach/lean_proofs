import ConformityConcerns.PeriodGame.Defs
import ConformityConcerns.Gaussian.CondCore
import ConformityConcerns.Gaussian.BeliefLemmas

/-!
# Facts for the period game at a Gaussian history (used by `PeriodGame/Instance.lean`)

Under `ω ~ N(m, Σ + I)` on `ℝ²`, `Z ω = γ (m₀ + K₀₀ (ω₀ - m₀) + K₀₁ (ω₁ - m₁)) + ω₁` is the affine
function `c + ⟪A, ω⟫` of `ω` with the loading `A = loadA Σ γ`, and `v ω = ω₁ = ⟪e₁, ω⟫`. Hence
`Var Z = Aᵀ (Σ + I) A = varZ Σ γ`, `Var v = 1 + Σ₁₁`, `Cov(v, Z) = V + γ C`, and `(Z, v)` is
jointly Gaussian. Also `Var(θ | h, s, v) = K₀₀ ≥ 0`.
-/

namespace CC

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {S : M2}

lemma inst_posSemidef_add_one (hS : S.PosSemidef) : (S + 1).PosSemidef :=
  (PosDef.posSemidef_add hS PosDef.one).posSemidef

lemma inst_postVarθ_eq (hS : S.PosSemidef) : postVarθ S = gainK S 0 0 := by
  rw [cm_postVar]
  linear_combination -(cm_id0 hS)

lemma inst_gainK00_nonneg (hS : S.PosSemidef) : 0 ≤ gainK S 0 0 := by
  have hP := psd_PSDE hS
  rw [gainK_eq (sym_of_psd hS) (dE_ne hP)]
  simpa using k00E_nonneg hP

lemma inst_postVarθ_nonneg (hS : S.PosSemidef) : 0 ≤ postVarθ S := by
  rw [inst_postVarθ_eq hS]
  exact inst_gainK00_nonneg hS

/-- `Z` as an affine function `c + ⟪A, ω⟫`. -/
lemma inst_Z_affine (m : E2) (S : M2) (γ : ℝ) :
    (fun ω : E2 => γ * (m 0 + gainK S 0 0 * (ω 0 - m 0) + gainK S 0 1 * (ω 1 - m 1)) + ω 1) =
      fun ω => γ * (m 0 - gainK S 0 0 * m 0 - gainK S 0 1 * m 1) +
        ⟪WithLp.toLp 2 (loadA S γ), ω⟫ := by
  funext ω
  simp only [loadA, cc_inner_two]
  ring

/-- `v` as an affine function `0 + ⟪e₁, ω⟫`. -/
lemma inst_v_affine : (fun ω : E2 => ω 1) = fun ω => 0 + ⟪WithLp.toLp 2 ![0, 1], ω⟫ := by
  funext ω
  rw [cc_inner_two]
  ring

variable {m : E2}

lemma inst_cov_aff (hS : S.PosSemidef) (c c' : ℝ) (a a' : Fin 2 → ℝ) :
    cov[fun ω : E2 => c + ⟪WithLp.toLp 2 a, ω⟫, fun ω => c' + ⟪WithLp.toLp 2 a', ω⟫;
      multivariateGaussian m (S + 1)] = a ⬝ᵥ (S + 1) *ᵥ a' := by
  rw [cc_cov_inner, covarianceBilin_multivariateGaussian (inst_posSemidef_add_one hS)]

/-- `Var Z = Aᵀ (Σ + I) A`. -/
lemma inst_variance_Z (hS : S.PosSemidef) (γ : ℝ) :
    variance (fun ω : E2 => γ * (m 0 + gainK S 0 0 * (ω 0 - m 0) + gainK S 0 1 * (ω 1 - m 1)) + ω 1)
      (multivariateGaussian m (S + 1)) = varZ S γ := by
  rw [inst_Z_affine, ← covariance_self (cc_memLp_aff _ _ _).aestronglyMeasurable.aemeasurable, inst_cov_aff hS]
  rfl

/-- `Var v = 1 + Σ₁₁`. -/
lemma inst_variance_v (hS : S.PosSemidef) :
    variance (fun ω : E2 => ω 1) (multivariateGaussian m (S + 1)) = Vt S := by
  rw [variance_eval_multivariateGaussian (inst_posSemidef_add_one hS)]
  simp [Vt, add_comm]

/-- `Cov(v, Z) = V + γ C`. -/
lemma inst_cov_vZ (hS : S.PosSemidef) (γ : ℝ) :
    cov[fun ω : E2 => ω 1,
      fun ω : E2 => γ * (m 0 + gainK S 0 0 * (ω 0 - m 0) + gainK S 0 1 * (ω 1 - m 1)) + ω 1;
      multivariateGaussian m (S + 1)] = Vt S + γ * Ct S := by
  rw [inst_Z_affine, inst_v_affine, inst_cov_aff hS]
  simp [dotProduct, mulVec, Fin.sum_univ_two, loadA, Vt, Ct, Matrix.one_apply]
  linear_combination γ * cm_id1 hS + γ * gainK S 0 0 * cm_symm hS

/-- An affine map of a Gaussian vector into `ℝ × ℝ` has Gaussian law. -/
lemma inst_hasGaussianLaw_pair (μ : Measure E2) [IsGaussian μ] (c c' : ℝ) (a b : E2) :
    HasGaussianLaw (fun ω : E2 => (c + ⟪a, ω⟫, c' + ⟪b, ω⟫)) μ := by
  let L : E2 →L[ℝ] ℝ × ℝ := (innerSL ℝ a).prod (innerSL ℝ b)
  have hT : (fun ω : E2 => (c + ⟪a, ω⟫, c' + ⟪b, ω⟫)) = fun ω => L ω + (c, c') := by
    funext ω
    simp [L, add_comm]
  rw [hT]
  refine ⟨(L.continuous.add continuous_const).measurable.aemeasurable, ?_⟩
  have : μ.map (fun ω => L ω + (c, c')) = (μ.map L).map (fun y => y + (c, c')) := by
    rw [Measure.map_map (measurable_add_const _) L.measurable]
    rfl
  rw [this]
  infer_instance

/-- `(Z, v)` is jointly Gaussian. -/
lemma inst_hasGaussianLaw_Zv (γ : ℝ) :
    HasGaussianLaw
      (fun ω : E2 => (γ * (m 0 + gainK S 0 0 * (ω 0 - m 0) + gainK S 0 1 * (ω 1 - m 1)) + ω 1,
        ω 1)) (multivariateGaussian m (S + 1)) := by
  have h := inst_hasGaussianLaw_pair (multivariateGaussian m (S + 1))
    (γ * (m 0 - gainK S 0 0 * m 0 - gainK S 0 1 * m 1)) 0 (WithLp.toLp 2 (loadA S γ))
    (WithLp.toLp 2 ![0, 1])
  convert h using 1
  funext ω
  exact Prod.ext (congrFun (inst_Z_affine m S γ) ω) (congrFun inst_v_affine ω)

lemma inst_measurable_Z (γ : ℝ) :
    Measurable (fun ω : E2 =>
      γ * (m 0 + gainK S 0 0 * (ω 0 - m 0) + gainK S 0 1 * (ω 1 - m 1)) + ω 1) := by
  fun_prop

end CC
