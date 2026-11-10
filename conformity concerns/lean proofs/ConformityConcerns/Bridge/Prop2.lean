import ConformityConcerns.Bridge.Defs
import ConformityConcerns.Dynamics.LongRun
import ConformityConcerns.Bridge.Hist
import ConformityConcerns.Bridge.Occurs
import ConformityConcerns.Bridge.Fails
import ConformityConcerns.Bridge.SL

/-!
# Proposition 2 with the paper's definition of social learning
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology

/-- The weights and the equilibrium actions generate the same information as the weights and the
observations, so `postTheta`, `postMu` are the posterior means given the public history. -/
theorem histSigma_eq (κ : ℝ) (_hκ : 0 < κ) (S₁ : M2) (_hS : S₁.PosDef) (G : Measure ℝ)
    [IsProbabilityMeasure G] (t : ℕ) :
    histSigma κ S₁ G t = infoSigma κ S₁ t :=
  histSigma_eq_info κ S₁ G t

/-- **Proposition 2 (paper's definition of social learning).** Suppose `Σ₁ ≻ 0` and `γ_t` is
i.i.d. with full support on `[0,1]`. If `κ < κck`, social learning about preferences and
fundamentals occurs. If `κ > κck`, it fails. -/
theorem prop2_socialLearning (S₁ : M2) (hS : S₁.PosDef) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : FullSupportUnit G)
    (κ : ℝ) (hκ : 0 < κ) :
    (κ < κck → SLOccurs (lawG S₁ G) thetaV (postTheta κ S₁ G) ∧
        SLOccurs (lawG S₁ G) muV (postMu κ S₁ G)) ∧
    (κck < κ → SLFails (lawG S₁ G) thetaV (postTheta κ S₁ G) ∧
        SLFails (lawG S₁ G) muV (postMu κ S₁ G)) := by
  have hvis : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G), (∀ t, γ t ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ᶠ t in atTop, γ t ∈ Set.Ioo a b :=
    fullSupport_visits G hG
  have hθ : Measurable thetaV := br_meas_coord measurable_fst 0
  have hμ : Measurable muV := br_meas_coord measurable_fst 1
  have hpostθ : ∀ n, Measurable (postTheta κ S₁ G n) := fun n =>
    (meas_info_postTheta κ S₁ G n).mono (infoSigma_le κ S₁ n) le_rfl
  have hpostμ : ∀ n, Measurable (postMu κ S₁ G n) := fun n =>
    (meas_info_postMu κ S₁ G n).mono (infoSigma_le κ S₁ n) le_rfl
  refine ⟨fun hκ' => ?_, fun hκ' => ?_⟩
  · have hlim : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G),
        Tendsto (fun t => SigP κ S₁ γ t) atTop (𝓝 0) := by
      filter_upwards [hvis] with γ hγ
      exact prop2_low_core κ hκ hκ' S₁ hS γ hγ.1 hγ.2
    exact ⟨slOccurs_of_ae hθ hpostθ (occurs_core κ S₁ G hS.posSemidef 0 hlim),
      slOccurs_of_ae hμ hpostμ (occurs_core κ S₁ G hS.posSemidef 1 hlim)⟩
  · have hfin : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G),
        ∃ T, ∀ t, T ≤ t → ¬ revP κ S₁ γ t := by
      filter_upwards [hvis] with γ hγ
      obtain ⟨T, hT⟩ := prop2_high_core κ hκ' S₁ hS.posSemidef γ hγ.1
      exact ⟨T, fun t ht => (hT t ht).1⟩
    have hdiag : ∀ i : Fin 2, ∀ γ t, 0 < SigP κ S₁ γ t i i := fun i γ t =>
      SigmaC_diag_pos _ γ S₁ hS.posSemidef t i hS.diag_pos
    have hlev : ∀ i : Fin 2, ∀ᵐ ω ∂(lawG S₁ G),
        Tendsto (fun n => (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ n] ω) atTop
          (𝓝 ((lawG S₁ G)[fun ω => ω.1 i | ⨆ n, infoSigma κ S₁ n] ω)) := fun i =>
      tendsto_ae_condExp (ℱ := infoFilt κ S₁) _
    exact ⟨slFails_of hθ (hlev 0) (fails_core κ S₁ G hS.posSemidef 0 (hdiag 0) hfin),
      slFails_of hμ (hlev 1) (fails_core κ S₁ G hS.posSemidef 1 (hdiag 1) hfin)⟩

end CC.Bridge
