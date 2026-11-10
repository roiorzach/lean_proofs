import ConformityConcerns.Bridge.Kalman

/-!
# Conditioning on the weight path

The weights are independent of the state and the noises, so integrals against `lawG` are
iterated integrals: first over `(θ, μ)` and the noises (law `Qm S₁`), then over the weights.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

set_option warn.classDefReducibility false

variable (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]

lemma lintegral_lawG (f : Ωg → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f ω ∂(lawG S₁ G) =
      ∫⁻ γ, ∫⁻ p, f (p.1, (p.2, γ)) ∂(Qm S₁) ∂(Measure.infinitePi fun _ : ℕ => G) := by
  unfold lawG Qm
  rw [← Measure.prodAssoc_prod, lintegral_map hf MeasurableEquiv.prodAssoc.measurable]
  exact lintegral_prod_symm (fun a => f (MeasurableEquiv.prodAssoc a))
    (hf.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable

lemma measure_lawG {B : Set Ωg} (hB : MeasurableSet B) :
    lawG S₁ G B = ∫⁻ γ, Qm S₁ ((fun p : E2 × (ℕ → E2) => (p.1, (p.2, γ))) ⁻¹' B)
      ∂(Measure.infinitePi fun _ : ℕ => G) := by
  rw [← lintegral_indicator_one hB, lintegral_lawG S₁ G _ (measurable_one.indicator hB)]
  congr 1
  funext γ
  have hm : Measurable (fun p : E2 × (ℕ → E2) => ((p.1, (p.2, γ)) : Ωg)) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  rw [← lintegral_indicator_one (hm hB)]
  rfl

lemma integrable_coord (S : M2) (i : Fin 2) :
    Integrable (fun x : E2 => x i) (multivariateGaussian 0 S) := by
  rw [← EuclideanSpace.coe_proj]
  exact IsGaussian.integrable_dual _ _

lemma integrable_coord_lawG (i : Fin 2) : Integrable (fun ω : Ωg => ω.1 i) (lawG S₁ G) :=
  (integrable_coord S₁ i).comp_fst _

lemma lintegral_sq_mvG {S : M2} (hS : S.PosSemidef) (i : Fin 2) :
    ∫⁻ u : E2, ‖u i‖ₑ ^ 2 ∂(multivariateGaussian 0 S) = ENNReal.ofReal (S i i) := by
  have hmp := measurePreserving_eval_multivariateGaussian (μ := 0) hS (i := i)
  rw [hmp.lintegral_comp (f := fun x : ℝ => ‖x‖ₑ ^ 2) (by fun_prop)]
  have h1 : ∀ x : ℝ, ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]
  simp_rw [h1]
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal ((0 : E2) i) (S i i).toNNReal) :=
    (memLp_id_gaussianReal 2).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg x)]
  congr 1
  have h0 : ∫ x, x ∂(gaussianReal ((0 : E2) i) (S i i).toNNReal) = 0 := by
    rw [integral_id_gaussianReal]; rfl
  have hv := variance_of_integral_eq_zero (X := id) aemeasurable_id h0
  simp only [id] at hv
  rw [← hv, variance_id_gaussianReal, Real.coe_toNNReal _ (hS.diag_nonneg)]

end CC.Bridge
