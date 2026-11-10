import ConformityConcerns.BridgeK.Prop3
import ConformityConcerns.Interventions.PriorCov

/-!
# Proposition 3 (1) for every prior of the model, with the paper's definition of social learning

For `σ_θ, σ_μ ≥ 0` and `ρ ∈ (-1, 1)`. Social learning about a variable is defined when its prior
variance is positive, so each conclusion assumes that. If `σ_θ = 0`, `θ` stays known and an
individual-oriented intervention changes nothing; symmetrically for `σ_μ = 0`.
-/

namespace CC.BridgeK

open MeasureTheory Set Filter Topology

set_option warn.classDefReducibility false

/-- **Proposition 3 (1), for every prior of the model (paper's definition of social learning).**
When `κ > κck`, for `σ_θ, σ_μ ≥ 0` and `ρ ∈ (-1, 1)`: if `σ_μ > 0`, after an individual-oriented
intervention at any date social learning about preferences fails; if `σ_θ > 0`, after a
peer-oriented intervention at any date social learning about fundamentals fails. -/
theorem prop3_1_socialLearning_prior (κ : ℝ) (hκ : κck < κ) {σθ σμ ρ : ℝ} (hθ : 0 ≤ σθ)
    (hμ : 0 ≤ σμ) (hρ : |ρ| < 1) (Gγ : Measure ℝ) [IsProbabilityMeasure Gγ]
    (hGγ : FullSupportUnit Gγ) (τ : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    (0 < σμ → SLFails (lawK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ) muV
      (postMuK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ (individualAt τ n))) ∧
    (0 < σθ → SLFails (lawK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ) thetaV
      (postThetaK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ (peerAt τ n))) := by
  set S₁ := priorCov σθ σμ ρ with hS₁
  have hpsd : S₁.PosSemidef := priorCov_psd hρ
  refine ⟨fun hμ' => ?_, fun hθ' => ?_⟩
  · rcases hθ.eq_or_lt with h | h
    · have hzero : S₁ 0 0 = 0 := by simp [hS₁, ← h]
      have hμpos : 0 < S₁ 1 1 := by simpa [hS₁] using pow_pos hμ' 2
      have key := prop3_core κ hκ S₁ hpsd Gγ hGγ τ n hn 0 1 (fun κs γs => by
        have hP := SigmaC_posSemidef κs γs S₁ hpsd τ
        have h00 : SigmaC κs S₁ γs τ 0 0 = 0 := by
          refine le_antisymm ?_ ((psd_iff _).1 hP).2.1
          have := SigmaC_anti00 (κ := κs) (γ := γs) hpsd (Nat.zero_le τ)
          simpa [SigmaC, hzero] using this
        simp only [discCov, ↓reduceIte]
        rw [observeTheta_of_zero hP h00 n]
        exact ⟨hP, SigmaC_diag_pos κs γs S₁ hpsd τ 1 hμpos⟩)
      have e : postMuK S₁ (Measure.dirac κ) Gγ (individualAt τ n) = fun m =>
          (lawK S₁ (Measure.dirac κ) Gγ)[fun ω => ω.1 1 |
            infoSigmaK S₁ (interventionAt τ 0 n) m] :=
        funext fun m => postMuK_eq _ _ _ _ m
      rw [e]
      exact key
    · exact (prop3_1_socialLearning κ hκ S₁ (priorCov_posDef h hμ' hρ) Gγ hGγ τ n hn).1
  · rcases hμ.eq_or_lt with h | h
    · have hzero : S₁ 1 1 = 0 := by simp [hS₁, ← h]
      have hθpos : 0 < S₁ 0 0 := by simpa [hS₁] using pow_pos hθ' 2
      have key := prop3_core κ hκ S₁ hpsd Gγ hGγ τ n hn 1 0 (fun κs γs => by
        have hP := SigmaC_posSemidef κs γs S₁ hpsd τ
        have h11 : SigmaC κs S₁ γs τ 1 1 = 0 := by
          refine le_antisymm ?_ ((psd_iff _).1 hP).2.2.1
          have := SigmaC_anti11 (κ := κs) (γ := γs) hpsd (Nat.zero_le τ)
          simpa [SigmaC, hzero] using this
        have hne : ((1 : Fin 2) = 0) = False := by simp
        simp only [discCov, hne, ↓reduceIte]
        rw [observeMu_of_zero hP h11 n]
        exact ⟨hP, SigmaC_diag_pos κs γs S₁ hpsd τ 0 hθpos⟩)
      have e : postThetaK S₁ (Measure.dirac κ) Gγ (peerAt τ n) = fun m =>
          (lawK S₁ (Measure.dirac κ) Gγ)[fun ω => ω.1 0 |
            infoSigmaK S₁ (interventionAt τ 1 n) m] :=
        funext fun m => postThetaK_eq _ _ _ _ m
      rw [e]
      exact key
    · exact (prop3_1_socialLearning κ hκ S₁ (priorCov_posDef hθ' h hρ) Gγ hGγ τ n hn).2

/-- **Proposition 3 (1), for every prior of the model, as worded in the paper.** When `κ > κck`,
an individual-oriented intervention (respectively, peer-oriented intervention) never results in
social learning about `μ` when `σ_μ > 0` (respectively, about `θ` when `σ_θ > 0`). -/
theorem prop3_1_never_prior (κ : ℝ) (hκ : κck < κ) {σθ σμ ρ : ℝ} (hθ : 0 ≤ σθ)
    (hμ : 0 ≤ σμ) (hρ : |ρ| < 1) (Gγ : Measure ℝ) [IsProbabilityMeasure Gγ]
    (hGγ : FullSupportUnit Gγ) (τ : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    (0 < σμ → ¬ SLOccurs (lawK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ) muV
      (postMuK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ (individualAt τ n))) ∧
    (0 < σθ → ¬ SLOccurs (lawK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ) thetaV
      (postThetaK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ (peerAt τ n))) := by
  obtain ⟨h1, h2⟩ := prop3_1_socialLearning_prior κ hκ hθ hμ hρ Gγ hGγ τ n hn
  exact ⟨fun h => not_slOccurs_of_slFails (Bridge.br_meas_coord measurable_fst 1) (h1 h),
    fun h => not_slOccurs_of_slFails (Bridge.br_meas_coord measurable_fst 0) (h2 h)⟩

end CC.BridgeK
