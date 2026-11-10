import ConformityConcerns.Gaussian.Belief
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Probability.ProductMeasure

/-!
# Dynamics of public beliefs

`SigmaC κ S₁ γ t` is the posterior covariance `Σ_t` of `(θ, μ)` at date `t` (date `0` is the
paper's period 1, `SigmaC … 0 = Σ₁`), when the conformity concern at date `t` is `κ t` and the
observed weight is `γ t`: a date is revealing iff the criterion of Corollary 1 holds
(`revCrit`), in which case the public observes `Z_t` and `Σ` is updated by `kalman`; otherwise
`Σ` is unchanged. (`PeriodGame/Instance.lean` shows that this is the covariance process of the
signaling equilibrium, using Corollary 1.)

`revCount κ S₁ γ t = N_t` is the number of revealing dates before `t`.
-/

namespace CC

open Filter Topology Set MeasureTheory

/-- The posterior covariance process. -/
noncomputable def SigmaC (κ : ℕ → ℝ) (S₁ : M2) (γ : ℕ → ℝ) : ℕ → M2
  | 0 => S₁
  | t + 1 =>
    haveI := Classical.propDecidable (revCrit (κ t) (SigmaC κ S₁ γ t) (γ t))
    if revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) then kalman (SigmaC κ S₁ γ t) (γ t)
    else SigmaC κ S₁ γ t

/-- `N_t`: number of revealing dates `s < t`. -/
noncomputable def revCount (κ : ℕ → ℝ) (S₁ : M2) (γ : ℕ → ℝ) (t : ℕ) : ℕ :=
  haveI := Classical.decPred (fun s => revCrit (κ s) (SigmaC κ S₁ γ s) (γ s))
  ((Finset.range t).filter fun s => revCrit (κ s) (SigmaC κ S₁ γ s) (γ s)).card

/-- `γ_t` has full support on `[0,1]`: a probability law on `[0,1]` charging every open
subinterval. -/
structure FullSupportUnit (G : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure G
  supp : G (Icc 0 1)ᶜ = 0
  pos : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → 0 < G (Ioo a b)

/-- The i.i.d. law of the whole sequence `(γ_t)_t`. -/
noncomputable def iidSeq (G : Measure ℝ) : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => G

end CC
