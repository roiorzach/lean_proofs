import ConformityConcerns.LearnTheta.Assembly

/-!
# Proposition A5 (`κ ≤ κck`) with the paper's definition of social learning

The paper's definition: for almost every realization `r` of `θ`, `θ(h^t) → r` in probability
conditional on `θ = r`. Conditioning on `θ = r` is the regular conditional distribution
`condDistrib id thetaV P r`. Almost sure convergence implies this: since
`P = (P.map θ) ⊗ condDistrib id θ P`, an almost sure property under `P` holds, for almost every
`r`, almost surely under `condDistrib id θ P r`, and `θ = r` almost surely under it.
-/

namespace CC.LearnTheta

open MeasureTheory ProbabilityTheory Filter Topology

section Generic

variable {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

lemma ae_condDistrib_of_ae (hX : Measurable X) {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ r ∂(P.map X), ∀ᵐ ω ∂(condDistrib id X P r), p ω := by
  set N := toMeasurable P {ω | ¬ p ω}
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hPN : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 h
  have hc := compProd_map_condDistrib (μ := P) (Y := id) hX.aemeasurable aemeasurable_id
  have h0 : ((P.map X) ⊗ₘ condDistrib id X P) (Set.univ ×ˢ N) = 0 := by
    rw [hc, Measure.map_apply (hX.prodMk measurable_id) (MeasurableSet.univ.prod hN)]
    have : (fun a => (X a, id a)) ⁻¹' (Set.univ ×ˢ N) = N := by ext; simp
    rw [this, hPN]
  rw [Measure.compProd_apply_prod MeasurableSet.univ hN, Measure.restrict_univ,
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hN)] at h0
  filter_upwards [h0] with r hr
  exact measure_mono_null (subset_toMeasurable _ _) hr

lemma ae_condDistrib_eq (hX : Measurable X) :
    ∀ᵐ r ∂(P.map X), ∀ᵐ ω ∂(condDistrib id X P r), X ω = r := by
  have hc := compProd_map_condDistrib (μ := P) (Y := id) hX.aemeasurable aemeasurable_id
  have hm : MeasurableSet {z : ℝ × Ω | X z.2 = z.1} :=
    measurableSet_eq_fun (hX.comp measurable_snd) measurable_fst
  have h : ∀ᵐ z ∂((P.map X) ⊗ₘ condDistrib id X P), X z.2 = z.1 := by
    rw [hc, ae_map_iff (hX.prodMk measurable_id).aemeasurable hm]
    exact Eventually.of_forall fun ω => rfl
  exact Measure.ae_ae_of_ae_compProd h

/-- Almost sure convergence of the posterior mean to `X` gives social learning in the paper's
sense. -/
theorem socialLearning_of_ae (hX : Measurable X) {post : ℕ → Ω → ℝ}
    (hpost : ∀ n, Measurable (post n))
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => post n ω) atTop (𝓝 (X ω))) :
    ∀ᵐ r ∂(P.map X), TendstoInMeasure (condDistrib id X P r) post atTop (fun _ => r) := by
  filter_upwards [ae_condDistrib_of_ae hX h, ae_condDistrib_eq hX] with r h1 h2
  refine tendstoInMeasure_of_tendsto_ae (fun n => (hpost n).aestronglyMeasurable) ?_
  filter_upwards [h1, h2] with ω a b
  rw [← b]
  exact a

end Generic

variable (Lθ Lε : Measure ℝ) (ψ : ℝ → ℝ) [IsProbabilityMeasure Lθ] [IsProbabilityMeasure Lε]
  [IsProbabilityMeasure (vLaw ψ)]

/-- **Proposition A5, `κ ≤ κck`, social learning in the paper's sense.** In every profile that is
fully revealing at (almost) every history, for almost every realization `r` of `θ`,
`θ(h^t) → r` in probability conditional on `θ = r`. -/
theorem propA5_learning_def (hθ : Integrable (fun x => x ^ 2) Lθ) (hψc : Continuous ψ)
    (hψpos : ∀ x, 0 < ψ x) (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : P = law Lθ Lε (vLaw ψ))
    (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (hrev : ∀ t, ∀ᵐ ω ∂P, StrictMono (c t (hist P c t ω))) :
    ∀ᵐ r ∂(P.map thetaV), TendstoInMeasure (condDistrib id thetaV P r)
      (fun t => P[thetaV | histSigma P c t]) atTop (fun _ => r) := by
  have hX : Measurable thetaV := measurable_pi_apply 0
  have hpost : ∀ t, Measurable (P[thetaV | histSigma P c t]) := fun t =>
    stronglyMeasurable_condExp.measurable.mono (histSigma_le P c hc t) le_rfl
  exact socialLearning_of_ae hX hpost
    (propA5_learning Lθ Lε ψ hθ hψc hψpos P hP c hc hrev)

end CC.LearnTheta
