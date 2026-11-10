import ConformityConcerns.BridgeK.BeliefsCore

/-!
# Public beliefs are Gaussian with covariance `Σ_t` (supporting statement)

As `Bridge/Beliefs.lean` (Lemma 3, last claim) in the generalized model: given the public
information at date `t` (weights `w_0, …, w_t`, disclosures `d_0, …, d_t`, observations at dates
`< t`), the conditional law of `(θ, μ)` is `N(m_t, Σ_t)` with `Σ_t = SigK` (so after a disclosure
the covariance is the `observeTheta` / `observeMu` update, and the revealing criterion and the
actions use the actual posterior covariance).
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory

/-- The public information at date `t` (it generates `infoSigmaK S₁ D t`). -/
noncomputable def infoVecK (S₁ : M2) (D : Sched) (t : ℕ) (ω : Ωk) :
    (Fin (t + 1) → ℝ × ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ) :=
  ((fun i : Fin (t + 1) => wts ω i), (fun i : Fin (t + 1) => discVal D i ω),
    (fun i : Fin t => obsK S₁ D i ω))

/-- **Public beliefs are Gaussian.** For every date `t`, the posterior of `(θ, μ)` given the
public information is `N(m_t, Σ_t)` almost surely, for a measurable mean map `m_t`. -/
theorem beliefsK_gaussian (S₁ : M2) (hS : S₁.PosSemidef) (G Gγ : Measure ℝ)
    [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ] (D : Sched)
    (hD : ∀ t i n, D t = some (i, n) → 0 ≤ n) (t : ℕ) :
    ∃ mt : (Fin (t + 1) → ℝ × ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ) → E2, Measurable mt ∧
      ∀ᵐ ω ∂(lawK S₁ G Gγ),
        condDistrib (fun ω : Ωk => ω.1) (infoVecK S₁ D t) (lawK S₁ G Gγ) (infoVecK S₁ D t ω) =
          multivariateGaussian (mt (infoVecK S₁ D t ω)) (SigK S₁ D (wts ω) t) :=
  ⟨mtF S₁ D t, measurable_mtF S₁ D t, beliefs_coreK S₁ D t G Gγ hS hD⟩

end CC.BridgeK
