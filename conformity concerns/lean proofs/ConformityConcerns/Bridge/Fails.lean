import ConformityConcerns.Bridge.Fubini

/-!
# No learning when there are finitely many revealing dates

If almost every weight path has finitely many revealing dates, then `E(x_i | all information)`
differs from `x_i` almost surely: along such a path, after the last revealing date `T`, the
information is `(γ, obs_0, …, obs_{T-1})`, and `x_i` is the Kalman mean (a function of these
observations) plus an independent `N(0, (Σ_T)_{ii})` error with `(Σ_T)_{ii} > 0`.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

set_option warn.classDefReducibility false

variable (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]

/-- **No learning.** If almost every weight path has finitely many revealing dates, the
conditional expectation of `x_i` given all the information differs from `x_i` almost surely. -/
theorem fails_core (hS₁ : S₁.PosSemidef) (i : Fin 2)
    (hdiag : ∀ γ t, 0 < SigP κ S₁ γ t i i)
    (hfin : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G), ∃ T, ∀ t, T ≤ t → ¬ revP κ S₁ γ t) :
    lawG S₁ G {ω | (lawG S₁ G)[fun ω => ω.1 i | ⨆ t, infoSigma κ S₁ t] ω = ω.1 i} = 0 := by
  set L := (lawG S₁ G)[fun ω => ω.1 i | ⨆ t, infoSigma κ S₁ t] with hLdef
  have hsm : StronglyMeasurable[⨆ t, infoSigma κ S₁ t] L := stronglyMeasurable_condExp
  have hsm' := hsm.mono (iSup_infoSigma_le κ S₁)
  obtain ⟨g, hg, hLg⟩ := hsm'.exists_eq_measurable_comp
  have hΓ : Measurable (fun ω : Ωg => (gam ω, fun s => obs κ S₁ s ω)) :=
    measurable_gam.prodMk (measurable_obsSeq κ S₁)
  have hset : {ω | L ω = ω.1 i} = {ω : Ωg | g (gam ω, fun s => obs κ S₁ s ω) = ω.1 i} := by
    rw [hLg]; rfl
  have hB : MeasurableSet {ω : Ωg | g (gam ω, fun s => obs κ S₁ s ω) = ω.1 i} :=
    measurableSet_eq_fun (hg.measurable.comp hΓ) (br_meas_coord measurable_fst i)
  rw [hset, measure_lawG S₁ G hB]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hfin] with γ hγ
  obtain ⟨T, hT⟩ := hγ
  have hobs : ∀ p : E2 × (ℕ → E2), obsF κ S₁ γ p.1 p.2 = Ytr κ S₁ γ p.1 p.2 T := by
    intro p
    funext s
    simp only [Ytr, trunc]
    split_ifs with h
    · rfl
    · exact obsF_pool κ S₁ (hT s (not_lt.1 h))
  let H : (ℕ → ℝ) → ℝ := fun y => g (γ, y) - kmean κ S₁ γ y T i
  have hH : Measurable H :=
    (hg.measurable.comp (measurable_const.prodMk measurable_id)).sub
      (br_meas_coord (measurable_kmean_fix κ S₁ γ T) i)
  have hset2 : (fun p : E2 × (ℕ → E2) => ((p.1, (p.2, γ)) : Ωg)) ⁻¹'
      {ω : Ωg | g (gam ω, fun s => obs κ S₁ s ω) = ω.1 i} =
      {p | (errF κ S₁ γ p.1 p.2 T) i = H (Ytr κ S₁ γ p.1 p.2 T)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    change g (γ, obsF κ S₁ γ p.1 p.2) = p.1 i ↔ _
    rw [hobs p]
    simp only [errF, PiLp.sub_apply, H, ← hobs p]
    constructor <;> intro h <;> linarith
  rw [hset2]
  obtain ⟨K1, K2⟩ := kalman_fiber κ S₁ γ hS₁ T
  have hev : Measurable (fun u : E2 => u i) := br_meas_coord measurable_id i
  refine br_prob_eq_zero_of_indep (hev.comp (measurable_errF κ S₁ γ T))
    (hH.comp (measurable_Ytr κ S₁ γ T)) (K1.comp hev hH) ?_
  intro y
  have e : (fun p : E2 × (ℕ → E2) => (errF κ S₁ γ p.1 p.2 T) i) =
      (fun u : E2 => u i) ∘ (fun p => errF κ S₁ γ p.1 p.2 T) := rfl
  rw [e, ← Measure.map_map hev (measurable_errF κ S₁ γ T), K2,
    (measurePreserving_eval_multivariateGaussian (SigmaC_psd' (fun _ => κ) γ S₁ hS₁ T)).map_eq]
  have := nullSingletonClass_gaussianReal (μ := (0 : E2) i)
    (v := (SigP κ S₁ γ T i i).toNNReal) (by simpa using hdiag γ T)
  exact measure_singleton y

end CC.Bridge
