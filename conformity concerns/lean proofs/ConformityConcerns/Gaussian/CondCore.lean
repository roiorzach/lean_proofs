import ConformityConcerns.Gaussian.CondMatrix
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.ConditionalExpectation

/-!
# Probability tools for `Gaussian/Conditioning.lean`

On `ℝ² × ℝ²` with law `N(m, Σ) ⊗ N(0, I)`:

* covariances and means of affine functions of the four coordinates (`cc_cov_coord`,
  `cc_integral_coord`);
* affine maps of the outcome have Gaussian law (`cc_hasGaussianLaw_affine`), so two affine maps
  with zero cross covariances are independent (`cc_indepFun`);
* a function independent of `Y` has constant conditional expectation given `σ(Y)`
  (`cc_condExp_indep`).
-/

namespace CC

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

lemma cc_int {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (h : MemLp f 2 μ) : Integrable f μ :=
  h.integrable (by norm_num)

section ProdCov

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
lemma cc_cov_fst {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    cov[fun p : α × β => f p.1, fun p => g p.1; μ.prod ν] = cov[f, g; μ] := by
  have h := covariance_map (μ := μ.prod ν) (Z := Prod.fst) (X := f) (Y := g)
    (by rw [Measure.map_fst_prod, measure_univ, one_smul]; exact hf.aestronglyMeasurable)
    (by rw [Measure.map_fst_prod, measure_univ, one_smul]; exact hg.aestronglyMeasurable) measurable_fst.aemeasurable
  rw [Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h.symm

lemma cc_cov_snd {f g : β → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    cov[fun p : α × β => f p.2, fun p => g p.2; μ.prod ν] = cov[f, g; ν] := by
  have h := covariance_map (μ := μ.prod ν) (Z := Prod.snd) (X := f) (Y := g)
    (by rw [Measure.map_snd_prod, measure_univ, one_smul]; exact hf.aestronglyMeasurable)
    (by rw [Measure.map_snd_prod, measure_univ, one_smul]; exact hg.aestronglyMeasurable) measurable_snd.aemeasurable
  rw [Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h.symm

lemma cc_cov_prod_split {f₁ g₁ : α → ℝ} {f₂ g₂ : β → ℝ}
    (hf₁ : MemLp f₁ 2 μ) (hg₁ : MemLp g₁ 2 μ) (hf₂ : MemLp f₂ 2 ν) (hg₂ : MemLp g₂ 2 ν) :
    cov[fun p : α × β => f₁ p.1 + f₂ p.2, fun p => g₁ p.1 + g₂ p.2; μ.prod ν] =
      cov[f₁, g₁; μ] + cov[f₂, g₂; ν] := by
  have a1 : MemLp (fun p : α × β => f₁ p.1) 2 (μ.prod ν) := hf₁.comp_fst ν
  have a2 : MemLp (fun p : α × β => f₂ p.2) 2 (μ.prod ν) := hf₂.comp_snd μ
  have b1 : MemLp (fun p : α × β => g₁ p.1) 2 (μ.prod ν) := hg₁.comp_fst ν
  have b2 : MemLp (fun p : α × β => g₂ p.2) 2 (μ.prod ν) := hg₂.comp_snd μ
  have h12 : cov[fun p : α × β => f₁ p.1, fun p => g₂ p.2; μ.prod ν] = 0 :=
    covariance_fst_snd_prod hf₁ hg₂
  have h21 : cov[fun p : α × β => f₂ p.2, fun p => g₁ p.1; μ.prod ν] = 0 := by
    rw [covariance_comm]; exact covariance_fst_snd_prod hg₁ hf₂
  change cov[(fun p : α × β => f₁ p.1) + (fun p => f₂ p.2),
    (fun p : α × β => g₁ p.1) + (fun p => g₂ p.2); μ.prod ν] = _
  rw [covariance_add_left a1 a2 (b1.add b2), covariance_add_right a1 b1 b2,
    covariance_add_right a2 b1 b2, cc_cov_fst hf₁ hg₁, cc_cov_snd hf₂ hg₂, h12, h21]
  ring

end ProdCov

section InnerGauss

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F]

lemma cc_memLp_inner (μ : Measure F) [IsGaussian μ] (a : F) :
    MemLp (fun x => ⟪a, x⟫) 2 μ := by
  have h : (fun x : F => ⟪a, x⟫) = ⇑(innerSL ℝ a) := by ext x; simp
  rw [h]; exact IsGaussian.memLp_dual _ _ _ (by simp)

lemma cc_memLp_aff (μ : Measure F) [IsGaussian μ] (c : ℝ) (a : F) :
    MemLp (fun x => c + ⟪a, x⟫) 2 μ :=
  (memLp_const c).add (cc_memLp_inner μ a)

variable [CompleteSpace F] [SecondCountableTopology F]

lemma cc_cov_inner (μ : Measure F) [IsGaussian μ] (c c' : ℝ) (a a' : F) :
    cov[fun x => c + ⟪a, x⟫, fun x => c' + ⟪a', x⟫; μ] = covarianceBilin μ a a' := by
  rw [covariance_const_add_left (cc_int (cc_memLp_inner μ a)),
    covariance_const_add_right (cc_int (cc_memLp_inner μ a')),
    covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]

lemma cc_integral_aff (μ : Measure F) [IsGaussian μ] (c : ℝ) (a : F) :
    ∫ x, (c + ⟪a, x⟫) ∂μ = c + ⟪a, ∫ x, x ∂μ⟫ := by
  rw [integral_add (integrable_const c) (cc_int (cc_memLp_inner μ a)), integral_const,
    probReal_univ, one_smul]
  congr 1
  exact integral_inner IsGaussian.integrable_id a

end InnerGauss

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {m : E2} {S : M2}

lemma cc_inner_two (a0 a1 : ℝ) (v : E2) : ⟪WithLp.toLp 2 ![a0, a1], v⟫ = a0 * v 0 + a1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma cc_split {f : E2 × E2 → ℝ} {c a0 a1 b0 b1 : ℝ}
    (hf : ∀ ω, f ω = c + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1)) :
    f = fun p => (c + ⟪WithLp.toLp 2 ![a0, a1], p.1⟫) + (0 + ⟪WithLp.toLp 2 ![b0, b1], p.2⟫) := by
  funext p; rw [hf, cc_inner_two, cc_inner_two]; ring

lemma cc_memLp_coord {f : E2 × E2 → ℝ} {c a0 a1 b0 b1 : ℝ}
    (hf : ∀ ω, f ω = c + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1)) :
    MemLp f 2 ((multivariateGaussian m S).prod (stdGaussian E2)) := by
  rw [cc_split hf]
  exact ((cc_memLp_aff _ c _).comp_fst _).add ((cc_memLp_aff _ 0 _).comp_snd _)

lemma cc_integrable_coord {f : E2 × E2 → ℝ} {c a0 a1 b0 b1 : ℝ}
    (hf : ∀ ω, f ω = c + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1)) :
    Integrable f ((multivariateGaussian m S).prod (stdGaussian E2)) :=
  cc_int (cc_memLp_coord hf)

/-- Covariance of two affine functions of `((θ, μ), (ε, ν)) ~ N(m, Σ) ⊗ N(0, I)`. -/
lemma cc_cov_coord (hS : S.PosSemidef) {f g : E2 × E2 → ℝ}
    {c a0 a1 b0 b1 c' a0' a1' b0' b1' : ℝ}
    (hf : ∀ ω, f ω = c + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1))
    (hg : ∀ ω, g ω = c' + (a0' * ω.1 0 + a1' * ω.1 1) + (b0' * ω.2 0 + b1' * ω.2 1)) :
    cov[f, g; (multivariateGaussian m S).prod (stdGaussian E2)] =
      a0 * (S 0 0 * a0' + S 0 1 * a1') + a1 * (S 1 0 * a0' + S 1 1 * a1') +
        (b0 * b0' + b1 * b1') := by
  rw [cc_split hf, cc_split hg, cc_cov_prod_split (cc_memLp_aff _ _ _) (cc_memLp_aff _ _ _)
    (cc_memLp_aff _ _ _) (cc_memLp_aff _ _ _), cc_cov_inner, cc_cov_inner,
    covarianceBilin_multivariateGaussian hS, covarianceBilin_stdGaussian, innerSL_apply_apply,
    cc_inner_two]
  simp [dotProduct, mulVec, Fin.sum_univ_two]

/-- Mean of an affine function of `((θ, μ), (ε, ν)) ~ N(m, Σ) ⊗ N(0, I)`. -/
lemma cc_integral_coord {f : E2 × E2 → ℝ} {c a0 a1 b0 b1 : ℝ}
    (hf : ∀ ω, f ω = c + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1)) :
    ∫ ω, f ω ∂((multivariateGaussian m S).prod (stdGaussian E2)) = c + (a0 * m 0 + a1 * m 1) := by
  have h1 : ∫ z : E2 × E2, (c + ⟪WithLp.toLp 2 ![a0, a1], z.1⟫)
      ∂((multivariateGaussian m S).prod (stdGaussian E2)) = _ :=
    integral_fun_fst (fun x : E2 => c + ⟪WithLp.toLp 2 ![a0, a1], x⟫)
  have h2 : ∫ z : E2 × E2, (0 + ⟪WithLp.toLp 2 ![b0, b1], z.2⟫)
      ∂((multivariateGaussian m S).prod (stdGaussian E2)) = _ :=
    integral_fun_snd (fun x : E2 => 0 + ⟪WithLp.toLp 2 ![b0, b1], x⟫)
  rw [cc_split hf, integral_add ((cc_int (cc_memLp_aff _ c _)).comp_fst _)
    ((cc_int (cc_memLp_aff _ 0 _)).comp_snd _), h1, h2,
    cc_integral_aff, cc_integral_aff, integral_id_multivariateGaussian, integral_id_stdGaussian]
  simp [cc_inner_two]

section Affine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- An affine map of a Gaussian outcome has Gaussian law. -/
lemma cc_hasGaussianLaw_affine (P : Measure (E2 × E2)) [IsGaussian P] (T : E2 × E2 → F)
    (hT : ∀ (a : ℝ) (x y : E2 × E2), T (a • x + y) = a • (T x - T 0) + T y) :
    HasGaussianLaw T P := by
  let ℓ : (E2 × E2) →ₗ[ℝ] F :=
    { toFun := fun x => T x - T 0
      map_add' := fun x y => by
        have h := hT 1 x y
        rw [one_smul, one_smul] at h
        rw [h]; abel
      map_smul' := fun a x => by
        have h := hT a x 0
        rw [add_zero] at h
        simp [h] }
  let L : (E2 × E2) →L[ℝ] F := LinearMap.toContinuousLinearMap ℓ
  have hTL : T = fun x => L x + T 0 := by funext x; simp [L, ℓ]
  rw [hTL]
  refine ⟨(L.continuous.add continuous_const).measurable.aemeasurable, ?_⟩
  have : P.map (fun x => L x + T 0) = (P.map L).map (fun y => y + T 0) := by
    rw [Measure.map_map (measurable_add_const _) L.measurable]; rfl
  rw [this]; infer_instance

end Affine

section Indep

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [SecondCountableTopology F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [CompleteSpace G]

/-- Two affine maps of a Gaussian outcome with zero cross covariances are independent. -/
lemma cc_indepFun (P : Measure (E2 × E2)) [IsGaussian P] (X : E2 × E2 → F) (Y : E2 × E2 → G)
    (hX : ∀ (a : ℝ) (x y : E2 × E2), X (a • x + y) = a • (X x - X 0) + X y)
    (hY : ∀ (a : ℝ) (x y : E2 × E2), Y (a • x + y) = a • (Y x - Y 0) + Y y)
    (h : ∀ x y, cov[fun ω => ⟪x, X ω⟫, fun ω => ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P := by
  have hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P := by
    refine cc_hasGaussianLaw_affine P _ (fun a x y => ?_)
    simp only [hX a x y, hY a x y]
    ext <;> simp
  exact hXY.indepFun_of_covariance_inner h

end Indep

/-- If `f ⟂ Y` then `E[f | σ(Y)] = E f`. -/
lemma cc_condExp_indep {Ω G : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [MeasurableSpace G] {f : Ω → ℝ} {Y : Ω → G} (hf : Measurable f) (hY : Measurable Y)
    (hind : IndepFun f Y P) :
    P[f | MeasurableSpace.comap Y inferInstance] =ᵐ[P] fun _ => ∫ ω, f ω ∂P :=
  condExp_indep_eq hf.comap_le hY.comap_le (comap_measurable f).stronglyMeasurable
    ((IndepFun_iff_Indep f Y P).1 hind)

end CC
