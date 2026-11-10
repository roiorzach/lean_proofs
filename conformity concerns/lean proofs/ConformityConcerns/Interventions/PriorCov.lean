import ConformityConcerns.Interventions.Fragility

/-!
# Proposition 3 (1) for every prior of the model

Section 2 allows `σ_θ, σ_μ ≥ 0` and `ρ ∈ (-1, 1)` (`priorCov`), so one prior variance may be zero.
`prop3_1_prior` is Proposition 3 (1) for all such priors. Social learning about a variable is
defined when its prior variance is positive, so each conclusion assumes that.

If `σ_θ = 0`, then `θ` is known and an individual-oriented intervention changes nothing
(`observeTheta_of_zero`); symmetrically for `σ_μ = 0` and a peer-oriented intervention.
-/

namespace CC

open Set Filter Topology Matrix

/-- The prior covariance of Section 2, with `σ_θ, σ_μ ≥ 0` and `ρ ∈ (-1, 1)`. -/
def priorCov (σθ σμ ρ : ℝ) : M2 := !![σθ ^ 2, ρ * σθ * σμ; ρ * σθ * σμ, σμ ^ 2]

section

variable {σθ σμ ρ : ℝ}

@[simp] lemma priorCov_00 : priorCov σθ σμ ρ 0 0 = σθ ^ 2 := by simp [priorCov]
@[simp] lemma priorCov_01 : priorCov σθ σμ ρ 0 1 = ρ * σθ * σμ := by simp [priorCov]
@[simp] lemma priorCov_10 : priorCov σθ σμ ρ 1 0 = ρ * σθ * σμ := by simp [priorCov]
@[simp] lemma priorCov_11 : priorCov σθ σμ ρ 1 1 = σμ ^ 2 := by simp [priorCov]

lemma rho_sq_lt_one (hρ : |ρ| < 1) : ρ ^ 2 < 1 := by
  have := sq_lt_one_iff_abs_lt_one ρ
  exact this.2 hρ

lemma priorCov_psd (hρ : |ρ| < 1) : (priorCov σθ σμ ρ).PosSemidef := by
  refine psd_of_entries _ (by simp) (by simpa using sq_nonneg σθ) (by simpa using sq_nonneg σμ) ?_
  have h := rho_sq_lt_one hρ
  simp only [priorCov_00, priorCov_01, priorCov_11]
  have hn : 0 ≤ σθ ^ 2 * σμ ^ 2 := by positivity
  nlinarith

lemma priorCov_posDef (hθ : 0 < σθ) (hμ : 0 < σμ) (hρ : |ρ| < 1) :
    (priorCov σθ σμ ρ).PosDef := by
  refine (pd_iff _).2 ⟨by simp, by simpa using pow_pos hθ 2, ?_⟩
  have h := rho_sq_lt_one hρ
  simp only [priorCov_00, priorCov_01, priorCov_11]
  have hn : 0 < σθ ^ 2 * σμ ^ 2 := by positivity
  nlinarith

end

/-- If `θ` is known, a signal about `θ` changes nothing. -/
lemma observeTheta_of_zero {S : M2} (hS : S.PosSemidef) (h : S 0 0 = 0) (n : ℝ) :
    observeTheta S n = S := by
  have h01 := off_zero_of_left hS h
  have h10 : S 1 0 = 0 := (sym_of_psd hS).trans h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [observeTheta, vecMulVec_apply, mulVec, dotProduct, Fin.sum_univ_two, h, h01, h10]

/-- If `μ` is known, a signal about `μ` changes nothing. -/
lemma observeMu_of_zero {S : M2} (hS : S.PosSemidef) (h : S 1 1 = 0) (n : ℝ) :
    observeMu S n = S := by
  have h01 := off_zero_of_right hS h
  have h10 : S 1 0 = 0 := (sym_of_psd hS).trans h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [observeMu, vecMulVec_apply, mulVec, dotProduct, Fin.sum_univ_two, h, h01, h10]

/-- **Proposition 3 (1), for every prior of the model.** When `κ > κck`, for `σ_θ, σ_μ ≥ 0` and
`ρ ∈ (-1, 1)`: if `σ_μ > 0`, an individual-oriented intervention never results in `σ²_{μ,t} → 0`;
if `σ_θ > 0`, a peer-oriented intervention never results in `σ²_{θ,t} → 0`. -/
theorem prop3_1_prior (κ : ℝ) (hκ : κck < κ) {σθ σμ ρ : ℝ} (hθ : 0 ≤ σθ) (hμ : 0 ≤ σμ)
    (hρ : |ρ| < 1) (n : ℝ) (hn : 0 ≤ n) (γ : ℕ → ℝ) (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) :
    (0 < σμ → ¬ Tendsto (fun t => SigmaSeq (fun _ => κ)
      (observeTheta (priorCov σθ σμ ρ) n) γ t 1 1) atTop (𝓝 0)) ∧
    (0 < σθ → ¬ Tendsto (fun t => SigmaSeq (fun _ => κ)
      (observeMu (priorCov σθ σμ ρ) n) γ t 0 0) atTop (𝓝 0)) := by
  have hpsd := priorCov_psd (σθ := σθ) (σμ := σμ) hρ
  refine ⟨fun hμ' => ?_, fun hθ' => ?_⟩
  · rcases hθ.eq_or_lt with h | h
    · rw [observeTheta_of_zero hpsd (by simp [← h]) n]
      exact not_tendsto_of_theta_known κ hκ _ hpsd γ (by simp [← h]) (by simpa using pow_pos hμ' 2)
    · exact (prop3_1 κ hκ _ (priorCov_posDef h hμ' hρ) n hn γ hγ).1
  · rcases hμ.eq_or_lt with h | h
    · rw [observeMu_of_zero hpsd (by simp [← h]) n]
      exact not_tendsto_zero_of_pos κ hκ _ hpsd γ hγ 0 (by simpa using pow_pos hθ' 2)
    · exact (prop3_1 κ hκ _ (priorCov_posDef hθ' h hρ) n hn γ hγ).2

end CC
