import ConformityConcerns.Gaussian.Belief
import ConformityConcerns.Gaussian.CondCore
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Gaussian conditioning: the formulas used by the model are Bayes' rule

At a history with Gaussian public beliefs `(θ, μ) ~ N(m, Σ)`, player `t` observes
`s = θ + ε`, `v = μ + ν` with `(ε, ν) ~ N(0, I)` independent of `(θ, μ)`. We realise this on
`Ω₂ = ℝ² × ℝ²` with law `N(m, Σ) ⊗ N(0, I)` and check that:

* the law of `(s, v)` is `N(m, Σ + I)` (the type law of `gameAt`);
* `E(θ | s, v) = θ(h) + K₀₀ (s - θ(h)) + K₀₁ (v - μ(h))` with `K = Σ (Σ + I)⁻¹`;
* `E((x - γθ - v)² | s, v) = (x - Z)² + γ² Var(θ | s, v)` with `Var(θ | s, v) = postVarθ Σ` (the
  adaptation loss of `gameAt`);
* after a revealing period the public observes `Z = γ E(θ | s, v) + v`; the posterior of
  `(θ, μ)` given `Z` is Gaussian with covariance `kalman Σ γ`: the residual of an affine
  regression on `Z` is independent of `Z` and has law `N(0, kalman Σ γ)`.
-/

namespace CC

open MeasureTheory ProbabilityTheory Matrix

/-- Sample space for one period: `((θ, μ), (ε, ν))`. -/
abbrev Ω₂ := EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)

/-- The law of `((θ, μ), (ε, ν))` given the history. -/
noncomputable def periodLaw (m : EuclideanSpace ℝ (Fin 2)) (S : M2) : Measure Ω₂ :=
  (multivariateGaussian m S).prod (stdGaussian (EuclideanSpace ℝ (Fin 2)))

/-- Player `t`'s private information `(s, v) = (θ + ε, μ + ν)`. -/
def privInfo (ω : Ω₂) : EuclideanSpace ℝ (Fin 2) := ω.1 + ω.2

/-- `Z = γ (θ(h) + K₀₀ (s - θ(h)) + K₀₁ (v - μ(h))) + v` as a function of the period outcome. -/
noncomputable def Zof (m : EuclideanSpace ℝ (Fin 2)) (S : M2) (γ : ℝ) (ω : Ω₂) : ℝ :=
  γ * (m 0 + gainK S 0 0 * (privInfo ω 0 - m 0) + gainK S 0 1 * (privInfo ω 1 - m 1)) +
    privInfo ω 1

variable {m : EuclideanSpace ℝ (Fin 2)} {S : M2}

open scoped RealInnerProductSpace

/-! ### Auxiliary facts about `periodLaw`

Every quantity below is an affine function of the four coordinates `(θ, μ, ε, ν)`; `cond_cov`
and `cond_integral` compute covariances and means of such functions (proved in `CondCore`). -/

instance : IsProbabilityMeasure (periodLaw m S) := by unfold periodLaw; infer_instance

instance : IsGaussian (periodLaw m S) := by unfold periodLaw; infer_instance

lemma measurable_privInfo : Measurable privInfo := by
  unfold privInfo; fun_prop

lemma cond_cov (hS : S.PosSemidef) {f g : Ω₂ → ℝ} {c a0 a1 b0 b1 c' a0' a1' b0' b1' : ℝ}
    (hf : ∀ ω, f ω = c + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1))
    (hg : ∀ ω, g ω = c' + (a0' * ω.1 0 + a1' * ω.1 1) + (b0' * ω.2 0 + b1' * ω.2 1)) :
    cov[f, g; periodLaw m S] =
      a0 * (S 0 0 * a0' + S 0 1 * a1') + a1 * (S 1 0 * a0' + S 1 1 * a1') +
        (b0 * b0' + b1 * b1') :=
  cc_cov_coord hS hf hg

lemma cond_integral {f : Ω₂ → ℝ} {c a0 a1 b0 b1 : ℝ}
    (hf : ∀ ω, f ω = c + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1)) :
    ∫ ω, f ω ∂(periodLaw m S) = c + (a0 * m 0 + a1 * m 1) :=
  cc_integral_coord hf

lemma cond_memLp {f : Ω₂ → ℝ} {c a0 a1 b0 b1 : ℝ}
    (hf : ∀ ω, f ω = c + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1)) :
    MemLp f 2 (periodLaw m S) :=
  cc_memLp_coord hf

lemma cond_integrable {f : Ω₂ → ℝ} {c a0 a1 b0 b1 : ℝ}
    (hf : ∀ ω, f ω = c + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1)) :
    Integrable f (periodLaw m S) :=
  cc_integrable_coord hf

/-- The residual `θ - E(θ | s, v)`. -/
noncomputable def resθ (m : EuclideanSpace ℝ (Fin 2)) (S : M2) (ω : Ω₂) : ℝ :=
  ω.1 0 - (m 0 + gainK S 0 0 * (privInfo ω 0 - m 0) + gainK S 0 1 * (privInfo ω 1 - m 1))

/-- `E(θ | s, v)` as a function of the outcome. -/
noncomputable def postMeanθ (m : EuclideanSpace ℝ (Fin 2)) (S : M2) (ω : Ω₂) : ℝ :=
  m 0 + gainK S 0 0 * (privInfo ω 0 - m 0) + gainK S 0 1 * (privInfo ω 1 - m 1)

lemma resθ_coord (ω : Ω₂) :
    resθ m S ω = (-m 0 + gainK S 0 0 * m 0 + gainK S 0 1 * m 1) +
      ((1 - gainK S 0 0) * ω.1 0 + (-gainK S 0 1) * ω.1 1) +
      ((-gainK S 0 0) * ω.2 0 + (-gainK S 0 1) * ω.2 1) := by
  simp [resθ, privInfo]; ring

lemma postMeanθ_coord (ω : Ω₂) :
    postMeanθ m S ω = (m 0 - gainK S 0 0 * m 0 - gainK S 0 1 * m 1) +
      (gainK S 0 0 * ω.1 0 + gainK S 0 1 * ω.1 1) +
      (gainK S 0 0 * ω.2 0 + gainK S 0 1 * ω.2 1) := by
  simp [postMeanθ, privInfo]; ring

lemma measurable_resθ : Measurable (resθ m S) := by
  unfold resθ privInfo; fun_prop

lemma integral_resθ : ∫ ω, resθ m S ω ∂(periodLaw m S) = 0 := by
  rw [cond_integral resθ_coord]; ring

lemma indep_resθ (hS : S.PosSemidef) : IndepFun (resθ m S) privInfo (periodLaw m S) := by
  refine cc_indepFun (periodLaw m S) (resθ m S) privInfo (fun a x y => ?_) (fun a x y => ?_)
    (fun x y => ?_)
  · simp [resθ, privInfo]; ring
  · ext i; simp [privInfo]; ring
  · have hf : ∀ ω, ⟪x, resθ m S ω⟫ = x * (-m 0 + gainK S 0 0 * m 0 + gainK S 0 1 * m 1) +
        ((x * (1 - gainK S 0 0)) * ω.1 0 + (x * -gainK S 0 1) * ω.1 1) +
        ((x * -gainK S 0 0) * ω.2 0 + (x * -gainK S 0 1) * ω.2 1) := by
      intro ω; simp [resθ, privInfo]; ring
    have hg : ∀ ω, ⟪y, privInfo ω⟫ = 0 + (y 0 * ω.1 0 + y 1 * ω.1 1) +
        (y 0 * ω.2 0 + y 1 * ω.2 1) := by
      intro ω; simp [privInfo, PiLp.inner_apply, Fin.sum_univ_two]; ring
    rw [cond_cov hS hf hg]
    linear_combination (-(x * y 0)) * cm_id0 hS + (-(x * y 1)) * cm_id1 hS

lemma variance_resθ (hS : S.PosSemidef) :
    ∫ ω, resθ m S ω ^ 2 ∂(periodLaw m S) = postVarθ S := by
  rw [← variance_of_integral_eq_zero measurable_resθ.aemeasurable integral_resθ,
    ← covariance_self measurable_resθ.aemeasurable, cond_cov hS resθ_coord resθ_coord, cm_postVar]
  linear_combination (gainK S 0 0) * cm_id0 hS + (gainK S 0 1) * cm_id1 hS

lemma stronglyMeasurable_comp_privInfo {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : Measurable φ) :
    StronglyMeasurable[MeasurableSpace.comap privInfo inferInstance] (fun ω => φ (privInfo ω)) :=
  (hφ.comp (comap_measurable privInfo)).stronglyMeasurable

lemma condExp_resθ (hS : S.PosSemidef) :
    (periodLaw m S)[resθ m S | MeasurableSpace.comap privInfo inferInstance] =ᵐ[periodLaw m S]
      fun _ => 0 := by
  have h := cc_condExp_indep measurable_resθ measurable_privInfo (indep_resθ (m := m) hS)
  rwa [integral_resθ] at h

lemma condExp_resθ_sq (hS : S.PosSemidef) :
    (periodLaw m S)[fun ω => resθ m S ω ^ 2 | MeasurableSpace.comap privInfo inferInstance]
      =ᵐ[periodLaw m S] fun _ => postVarθ S := by
  have hind : IndepFun (fun ω => resθ m S ω ^ 2) privInfo (periodLaw m S) :=
    (indep_resθ (m := m) hS).comp (φ := fun r : ℝ => r ^ 2) (ψ := id) (by fun_prop) measurable_id
  have h := cc_condExp_indep (measurable_resθ.pow_const 2) measurable_privInfo hind
  rwa [variance_resθ hS] at h

/-! ### Auxiliary facts for the revealing period

`Z = zC + zA₀ s + zA₁ v` with loading `A = (zA₀, zA₁) = loadA Σ γ`. The regression of `(θ, μ)` on
`Z` has slope `k = Σ A / Var(Z | h)` and intercept `c = m - E(Z | h) k`; the residual is
uncorrelated with `Z` and has covariance `kalman Σ γ`. -/

/-- Loadings and intercept of `Z` on the outcome: `Z = zC + zA₀ (θ + ε) + zA₁ (μ + ν)`. -/
noncomputable def zA0 (S : M2) (γ : ℝ) : ℝ := γ * gainK S 0 0

noncomputable def zA1 (S : M2) (γ : ℝ) : ℝ := 1 + γ * gainK S 0 1

noncomputable def zC (m : EuclideanSpace ℝ (Fin 2)) (S : M2) (γ : ℝ) : ℝ :=
  γ * m 0 - γ * gainK S 0 0 * m 0 - γ * gainK S 0 1 * m 1

/-- The regression coefficient `k = Σ A / Var(Z | h)` of `(θ, μ)` on `Z`. -/
noncomputable def regK (S : M2) (γ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (varZ S γ)⁻¹ • WithLp.toLp 2 (S *ᵥ loadA S γ)

/-- The regression intercept `c = m - E(Z | h) k`. -/
noncomputable def regC (m : EuclideanSpace ℝ (Fin 2)) (S : M2) (γ : ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  m - (γ * m 0 + m 1) • regK S γ

/-- The regression residual `(θ, μ) - c - Z k`. -/
noncomputable def resZ (m : EuclideanSpace ℝ (Fin 2)) (S : M2) (γ : ℝ) (ω : Ω₂) :
    EuclideanSpace ℝ (Fin 2) :=
  ω.1 - regC m S γ - Zof m S γ ω • regK S γ

lemma Zof_coord (γ : ℝ) (ω : Ω₂) :
    Zof m S γ ω = zC m S γ + (zA0 S γ * ω.1 0 + zA1 S γ * ω.1 1) +
      (zA0 S γ * ω.2 0 + zA1 S γ * ω.2 1) := by
  simp [Zof, privInfo, zA0, zA1, zC]; ring

lemma regK_apply0 (γ : ℝ) :
    regK S γ 0 = (varZ S γ)⁻¹ * (S 0 0 * zA0 S γ + S 0 1 * zA1 S γ) := by
  simp [regK, mulVec, dotProduct, loadA, Fin.sum_univ_two, zA0, zA1]

lemma regK_apply1 (γ : ℝ) :
    regK S γ 1 = (varZ S γ)⁻¹ * (S 1 0 * zA0 S γ + S 1 1 * zA1 S γ) := by
  simp [regK, mulVec, dotProduct, loadA, Fin.sum_univ_two, zA0, zA1]

lemma regC_apply (γ : ℝ) (i : Fin 2) :
    regC m S γ i = m i - (γ * m 0 + m 1) * regK S γ i := by
  simp [regC]

lemma cond_varZ_eq (γ : ℝ) :
    varZ S γ = zA0 S γ * ((S 0 0 + 1) * zA0 S γ + S 0 1 * zA1 S γ) +
      zA1 S γ * (S 1 0 * zA0 S γ + (S 1 1 + 1) * zA1 S γ) :=
  cm_varZ_eq S γ

lemma cond_kalman_quad (γ : ℝ) (t : Fin 2 → ℝ) :
    t ⬝ᵥ kalman S γ *ᵥ t = t 0 * (S 0 0 * t 0 + S 0 1 * t 1) + t 1 * (S 1 0 * t 0 + S 1 1 * t 1) -
      (varZ S γ)⁻¹ * (t 0 * (S 0 0 * zA0 S γ + S 0 1 * zA1 S γ) +
        t 1 * (S 1 0 * zA0 S γ + S 1 1 * zA1 S γ)) ^ 2 := by
  simp [kalman, dotProduct, mulVec, vecMulVec, Fin.sum_univ_two, loadA, zA0, zA1]
  ring

lemma inner_resZ_coord (γ : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (ω : Ω₂) :
    ⟪t, resZ m S γ ω⟫ =
      (-(t 0 * regC m S γ 0 + t 1 * regC m S γ 1) -
          (t 0 * regK S γ 0 + t 1 * regK S γ 1) * zC m S γ) +
        ((t 0 - (t 0 * regK S γ 0 + t 1 * regK S γ 1) * zA0 S γ) * ω.1 0 +
          (t 1 - (t 0 * regK S γ 0 + t 1 * regK S γ 1) * zA1 S γ) * ω.1 1) +
        ((-((t 0 * regK S γ 0 + t 1 * regK S γ 1) * zA0 S γ)) * ω.2 0 +
          (-((t 0 * regK S γ 0 + t 1 * regK S γ 1) * zA1 S γ)) * ω.2 1) := by
  simp [resZ, PiLp.inner_apply, Fin.sum_univ_two, Zof_coord]; ring

lemma inner_Zof_coord (γ y : ℝ) (ω : Ω₂) :
    ⟪y, Zof m S γ ω⟫ = y * zC m S γ + ((y * zA0 S γ) * ω.1 0 + (y * zA1 S γ) * ω.1 1) +
      ((y * zA0 S γ) * ω.2 0 + (y * zA1 S γ) * ω.2 1) := by
  simp [Zof_coord]; ring

lemma cond_alg_indep (x0 x1 y a0 a1 s00 s01 s10 s11 V k0 k1 : ℝ)
    (hV : V = a0 * ((s00 + 1) * a0 + s01 * a1) + a1 * (s10 * a0 + (s11 + 1) * a1)) (hV0 : V ≠ 0)
    (hk0 : k0 = V⁻¹ * (s00 * a0 + s01 * a1)) (hk1 : k1 = V⁻¹ * (s10 * a0 + s11 * a1)) :
    (x0 - (x0 * k0 + x1 * k1) * a0) * (s00 * (y * a0) + s01 * (y * a1)) +
        (x1 - (x0 * k0 + x1 * k1) * a1) * (s10 * (y * a0) + s11 * (y * a1)) +
      (-((x0 * k0 + x1 * k1) * a0) * (y * a0) + -((x0 * k0 + x1 * k1) * a1) * (y * a1)) = 0 := by
  subst hk0 hk1
  field_simp
  rw [hV]
  ring

lemma cond_alg_var (t0 t1 a0 a1 s00 s01 s10 s11 V k0 k1 : ℝ) (hsym : s10 = s01)
    (hV : V = a0 * ((s00 + 1) * a0 + s01 * a1) + a1 * (s10 * a0 + (s11 + 1) * a1)) (hV0 : V ≠ 0)
    (hk0 : k0 = V⁻¹ * (s00 * a0 + s01 * a1)) (hk1 : k1 = V⁻¹ * (s10 * a0 + s11 * a1)) :
    (t0 - (t0 * k0 + t1 * k1) * a0) *
          (s00 * (t0 - (t0 * k0 + t1 * k1) * a0) + s01 * (t1 - (t0 * k0 + t1 * k1) * a1)) +
        (t1 - (t0 * k0 + t1 * k1) * a1) *
          (s10 * (t0 - (t0 * k0 + t1 * k1) * a0) + s11 * (t1 - (t0 * k0 + t1 * k1) * a1)) +
      (-((t0 * k0 + t1 * k1) * a0) * -((t0 * k0 + t1 * k1) * a0) +
        -((t0 * k0 + t1 * k1) * a1) * -((t0 * k0 + t1 * k1) * a1)) =
    t0 * (s00 * t0 + s01 * t1) + t1 * (s10 * t0 + s11 * t1) -
      V⁻¹ * (t0 * (s00 * a0 + s01 * a1) + t1 * (s10 * a0 + s11 * a1)) ^ 2 := by
  subst hk0 hk1 hsym
  field_simp
  rw [hV]
  ring

lemma resZ_affine (γ : ℝ) (a : ℝ) (x y : Ω₂) :
    resZ m S γ (a • x + y) = a • (resZ m S γ x - resZ m S γ 0) + resZ m S γ y := by
  ext i; simp [resZ, Zof_coord]; ring

lemma Zof_affine (γ : ℝ) (a : ℝ) (x y : Ω₂) :
    Zof m S γ (a • x + y) = a • (Zof m S γ x - Zof m S γ 0) + Zof m S γ y := by
  simp [Zof_coord]; ring

lemma indep_resZ (hS : S.PosSemidef) (γ : ℝ) :
    IndepFun (resZ m S γ) (Zof m S γ) (periodLaw m S) := by
  refine cc_indepFun (periodLaw m S) (resZ m S γ) (Zof m S γ) (resZ_affine γ) (Zof_affine γ)
    (fun x y => ?_)
  rw [cond_cov hS (inner_resZ_coord γ x) (inner_Zof_coord γ y)]
  exact cond_alg_indep _ _ _ _ _ _ _ _ _ _ _ _ (cond_varZ_eq γ) (cm_varZ_pos hS γ).ne'
    (regK_apply0 γ) (regK_apply1 γ)

lemma var_inner_resZ (hS : S.PosSemidef) (γ : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    Var[fun ω => ⟪t, resZ m S γ ω⟫; periodLaw m S] = t.ofLp ⬝ᵥ kalman S γ *ᵥ t.ofLp := by
  have hm : AEMeasurable (fun ω => ⟪t, resZ m S γ ω⟫) (periodLaw m S) :=
    (cond_memLp (inner_resZ_coord γ t)).aestronglyMeasurable.aemeasurable
  rw [← covariance_self hm, cond_cov hS (inner_resZ_coord γ t) (inner_resZ_coord γ t), cond_kalman_quad]
  exact cond_alg_var _ _ _ _ _ _ _ _ _ _ _ (cm_symm hS) (cond_varZ_eq γ) (cm_varZ_pos hS γ).ne'
    (regK_apply0 γ) (regK_apply1 γ)

lemma integral_inner_resZ (γ : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    ∫ ω, ⟪t, resZ m S γ ω⟫ ∂(periodLaw m S) = 0 := by
  rw [cond_integral (inner_resZ_coord γ t), regC_apply, regC_apply]
  simp [zC, zA0, zA1]; ring

lemma cond_kalman_posSemidef (hS : S.PosSemidef) (γ : ℝ) : (kalman S γ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · ext i j
    have h := hS.1.apply i j
    simp only [star_trivial] at h
    simp [kalman, vecMulVec, h, mul_comm]
  · have h := var_inner_resZ (m := 0) hS γ (WithLp.toLp 2 x)
    simp only at h
    rw [star_trivial, ← h]
    exact variance_nonneg _ _

lemma law_resZ (hS : S.PosSemidef) (γ : ℝ) :
    (periodLaw m S).map (resZ m S γ) = multivariateGaussian 0 (kalman S γ) := by
  have hG : HasGaussianLaw (resZ m S γ) (periodLaw m S) :=
    cc_hasGaussianLaw_affine _ _ (resZ_affine γ)
  apply Measure.ext_of_charFun
  funext t
  rw [hG.charFun_map_eq, charFun_multivariateGaussian (cond_kalman_posSemidef hS γ),
    integral_inner_resZ, var_inner_resZ hS]
  simp

/-- The type law of `gameAt`: `(s, v) ~ N(m, Σ + I)`. -/
theorem privInfo_law (hS : S.PosSemidef) :
    (periodLaw m S).map privInfo = multivariateGaussian m (S + 1) := by
  have h1 : (periodLaw m S).map privInfo =
      Measure.conv (multivariateGaussian m S) (stdGaussian (EuclideanSpace ℝ (Fin 2))) := rfl
  rw [h1]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv, charFun_multivariateGaussian hS, charFun_stdGaussian,
    charFun_multivariateGaussian (hS.add PosSemidef.one), ← Complex.exp_add]
  congr 1
  have h : t.ofLp ⬝ᵥ (S + 1) *ᵥ t.ofLp = t.ofLp ⬝ᵥ S *ᵥ t.ofLp + ‖t‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Matrix.add_mulVec, dotProduct, Fin.sum_univ_two, sq]
    ring
  rw [h]; push_cast; ring

/-- `E(θ | s, v) = θ(h) + K₀₀ (s - θ(h)) + K₀₁ (v - μ(h))`. -/
theorem condExp_theta (hS : S.PosSemidef) :
    (periodLaw m S)[fun ω => ω.1 0 | MeasurableSpace.comap privInfo inferInstance] =ᵐ[periodLaw m S]
      fun ω => m 0 + gainK S 0 0 * (privInfo ω 0 - m 0) + gainK S 0 1 * (privInfo ω 1 - m 1) := by
  have hsplit : (fun ω : Ω₂ => ω.1 0) = resθ m S + postMeanθ m S := by
    funext ω; simp [resθ, postMeanθ]
  have hgm : StronglyMeasurable[MeasurableSpace.comap privInfo inferInstance] (postMeanθ m S) :=
    stronglyMeasurable_comp_privInfo
      (φ := fun y => m 0 + gainK S 0 0 * (y 0 - m 0) + gainK S 0 1 * (y 1 - m 1)) (by fun_prop)
  have hgi : Integrable (postMeanθ m S) (periodLaw m S) := cond_integrable postMeanθ_coord
  rw [hsplit]
  filter_upwards [condExp_add (cond_integrable resθ_coord) hgi
      (MeasurableSpace.comap privInfo inferInstance), condExp_resθ (m := m) hS] with ω h1 h2
  rw [h1, Pi.add_apply, h2, condExp_of_stronglyMeasurable measurable_privInfo.comap_le hgm hgi]
  simp [postMeanθ]

/-- The adaptation loss: `E((x - γθ - v)² | s, v) = (x - Z)² + γ² Var(θ | s, v)`. -/
theorem condExp_adaptation (hS : S.PosSemidef) (γ x : ℝ) :
    (periodLaw m S)[fun ω => (x - γ * ω.1 0 - privInfo ω 1) ^ 2 |
        MeasurableSpace.comap privInfo inferInstance] =ᵐ[periodLaw m S]
      fun ω => (x - Zof m S γ ω) ^ 2 + γ ^ 2 * postVarθ S := by
  set u : Ω₂ → ℝ := fun ω => x - Zof m S γ ω with hu
  set R := resθ m S with hR
  have hsplit : (fun ω => (x - γ * ω.1 0 - privInfo ω 1) ^ 2) =
      (fun ω => u ω ^ 2) + (-2 * γ) • (u * R) + (γ ^ 2) • (fun ω => R ω ^ 2) := by
    funext ω; simp [hu, hR, resθ, Zof]; ring
  have hu_coord : ∀ ω, u ω = (x - (γ * m 0 - γ * gainK S 0 0 * m 0 - γ * gainK S 0 1 * m 1)) +
      ((-(γ * gainK S 0 0)) * ω.1 0 + (-(1 + γ * gainK S 0 1)) * ω.1 1) +
      ((-(γ * gainK S 0 0)) * ω.2 0 + (-(1 + γ * gainK S 0 1)) * ω.2 1) := by
    intro ω; simp [hu, Zof, privInfo]; ring
  have huL := cond_memLp (m := m) (S := S) hu_coord
  have hRL := cond_memLp (m := m) (S := S) (resθ_coord (m := m) (S := S))
  have hum : StronglyMeasurable[MeasurableSpace.comap privInfo inferInstance] u :=
    stronglyMeasurable_comp_privInfo (φ := fun y => x - (γ * (m 0 + gainK S 0 0 * (y 0 - m 0) +
      gainK S 0 1 * (y 1 - m 1)) + y 1)) (by fun_prop)
  have hu2m :
      StronglyMeasurable[MeasurableSpace.comap privInfo inferInstance] (fun ω => u ω ^ 2) :=
    stronglyMeasurable_comp_privInfo (φ := fun y => (x - (γ * (m 0 + gainK S 0 0 * (y 0 - m 0) +
      gainK S 0 1 * (y 1 - m 1)) + y 1)) ^ 2) (by fun_prop)
  have hu2i : Integrable (fun ω => u ω ^ 2) (periodLaw m S) := huL.integrable_sq
  have huRi : Integrable (u * R) (periodLaw m S) := huL.integrable_mul hRL
  have hR2i : Integrable (fun ω => R ω ^ 2) (periodLaw m S) := hRL.integrable_sq
  rw [hsplit]
  filter_upwards [condExp_add (hu2i.add (huRi.smul (-2 * γ))) (hR2i.smul (γ ^ 2))
      (MeasurableSpace.comap privInfo inferInstance),
    condExp_add hu2i (huRi.smul (-2 * γ)) (MeasurableSpace.comap privInfo inferInstance),
    condExp_smul (-2 * γ) (u * R) (MeasurableSpace.comap privInfo inferInstance),
    condExp_smul (γ ^ 2) (fun ω => R ω ^ 2) (MeasurableSpace.comap privInfo inferInstance),
    condExp_mul_of_stronglyMeasurable_left hum huRi (cc_int hRL),
    condExp_resθ (m := m) hS, condExp_resθ_sq (m := m) hS] with ω h1 h2 h3 h4 h5 h6 h7
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, Pi.mul_apply,
    h6, h7, condExp_of_stronglyMeasurable measurable_privInfo.comap_le hu2m hu2i]
  simp [hu]

/-- Bayes' rule after a revealing period: for some affine map `z ↦ c + z • k`, the residual
`(θ, μ) - c - Z • k` is independent of `Z` and has law `N(0, kalman Σ γ)`; so the posterior of
`(θ, μ)` given `Z` is `N(c + Z • k, kalman Σ γ)`. -/
theorem posterior_after_reveal (hS : S.PosSemidef) (γ : ℝ) :
    ∃ c k : EuclideanSpace ℝ (Fin 2),
      IndepFun (fun ω => ω.1 - c - Zof m S γ ω • k) (Zof m S γ) (periodLaw m S) ∧
      (periodLaw m S).map (fun ω => ω.1 - c - Zof m S γ ω • k) =
        multivariateGaussian 0 (kalman S γ) := by
  exact ⟨regC m S γ, regK S γ, indep_resZ hS γ, law_resZ hS γ⟩

end CC
