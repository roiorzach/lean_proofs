import ConformityConcerns.Bridge.Defs
import ConformityConcerns.Bridge.BeliefsCore

/-!
# Lemma 3 (last claim): public beliefs are Gaussian at every on-path history

Along the equilibrium information structure (weights and observations), the conditional law of
`(θ, μ)` given the public information at date `t` is Gaussian, with mean an (affine) function of
the information and covariance `Σ_t`, the covariance process used throughout (`SigmaC`).
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology

/-- The public information at date `t`: the weights `γ_0, …, γ_t` and the observations at dates
`< t` (it generates `infoSigma κ S₁ t`). -/
noncomputable def infoVec (κ : ℝ) (S₁ : M2) (t : ℕ) (ω : Ωg) : (Fin (t + 1) → ℝ) × (Fin t → ℝ) :=
  ((fun i : Fin (t + 1) => gam ω i), (fun i : Fin t => obs κ S₁ i ω))

/-- **Lemma 3 (public beliefs are Gaussian).** For every date `t`, the posterior of `(θ, μ)` given
the public information is `N(m_t, Σ_t)` almost surely, for a measurable mean map `m_t`. -/
theorem beliefs_gaussian (S₁ : M2) (hS : S₁.PosSemidef) (G : Measure ℝ) [IsProbabilityMeasure G]
    (κ : ℝ) (t : ℕ) :
    ∃ mt : (Fin (t + 1) → ℝ) × (Fin t → ℝ) → E2, Measurable mt ∧
      ∀ᵐ ω ∂(lawG S₁ G),
        condDistrib (fun ω : Ωg => ω.1) (infoVec κ S₁ t) (lawG S₁ G) (infoVec κ S₁ t ω) =
          multivariateGaussian (mt (infoVec κ S₁ t ω)) (Sig κ S₁ ω t) :=
  ⟨mtF κ S₁ t, measurable_mtF κ S₁ t, beliefs_core κ S₁ t hS G⟩

end CC.Bridge
