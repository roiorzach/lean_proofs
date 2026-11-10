import ConformityConcerns.BridgeK.Defs

/-!
# From almost sure statements to the paper's definition of social learning

As `Bridge/SL.lean`, on any standard Borel sample space.
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

lemma k_ae_condDistrib (hX : Measurable X) {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
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

lemma k_ae_condDistrib_eq (hX : Measurable X) :
    ∀ᵐ r ∂(P.map X), ∀ᵐ ω ∂(condDistrib id X P r), X ω = r := by
  have hc := compProd_map_condDistrib (μ := P) (Y := id) hX.aemeasurable aemeasurable_id
  have hm : MeasurableSet {z : ℝ × Ω | X z.2 = z.1} :=
    measurableSet_eq_fun (hX.comp measurable_snd) measurable_fst
  have h : ∀ᵐ z ∂((P.map X) ⊗ₘ condDistrib id X P), X z.2 = z.1 := by
    rw [hc, ae_map_iff (hX.prodMk measurable_id).aemeasurable hm]
    exact Eventually.of_forall fun ω => rfl
  exact Measure.ae_ae_of_ae_compProd h

/-- Almost sure convergence of the posterior mean to `X` gives social learning. -/
theorem slOccurs_of_ae (hX : Measurable X) {post : ℕ → Ω → ℝ} (hpost : ∀ n, Measurable (post n))
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => post n ω) atTop (𝓝 (X ω))) : SLOccurs P X post := by
  unfold SLOccurs
  filter_upwards [k_ae_condDistrib hX h, k_ae_condDistrib_eq hX] with r h1 h2
  refine tendstoInMeasure_of_tendsto_ae (fun n => (hpost n).aestronglyMeasurable) ?_
  filter_upwards [h1, h2] with ω a b
  rw [← b]
  exact a

/-- If the posterior mean converges almost surely to `L` and `L ≠ X` almost surely, social
learning fails. -/
theorem slFails_of (hX : Measurable X) {post : ℕ → Ω → ℝ}
    {L : Ω → ℝ} (h1 : ∀ᵐ ω ∂P, Tendsto (fun n => post n ω) atTop (𝓝 (L ω)))
    (h2 : P {ω | L ω = X ω} = 0) : SLFails P X post := by
  unfold SLFails
  have h2' : ∀ᵐ ω ∂P, L ω ≠ X ω := by
    rw [ae_iff]; simpa using h2
  filter_upwards [k_ae_condDistrib hX h1, k_ae_condDistrib hX h2', k_ae_condDistrib_eq hX]
    with r a1 a2 a3
  intro hT
  obtain ⟨ns, hns, hae⟩ := hT.exists_seq_tendsto_ae
  have hfalse : ∀ᵐ ω ∂(condDistrib id X P r), False := by
    filter_upwards [hae, a1, a2, a3] with ω b1 b2 b3 b4
    have hL : L ω = r := tendsto_nhds_unique (b2.comp hns.tendsto_atTop) b1
    exact b3 (hL.trans b4.symm)
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-- Failure of social learning excludes its occurrence. -/
theorem not_slOccurs_of_slFails (_hX : Measurable X) {post : ℕ → Ω → ℝ}
    (h : SLFails P X post) : ¬ SLOccurs P X post := by
  intro h'
  have : ∀ᵐ r ∂(P.map X), False := by
    filter_upwards [h, h'] with r a b
    exact a b
  obtain ⟨_, h⟩ := this.exists
  exact h

end CC.BridgeK
