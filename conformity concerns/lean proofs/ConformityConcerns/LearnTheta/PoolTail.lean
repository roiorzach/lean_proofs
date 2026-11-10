import ConformityConcerns.LearnTheta.Defs
import ConformityConcerns.LearnTheta.PoolTailAux.Core
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Proposition A5, case `κ > κck`: the tails of the central pool vanish (deterministic part)

Fix a path along which the public's beliefs about `Y_t = E(θ | s_t, h^t)` concentrate at the
true `θ = c`: the conditional laws `η t` of `Y_t` satisfy `∫ (y - c)² dη_t → 0`. At each date the
expected conformity loss of a revealed type is `m_t = mfun ψ (η t)`, the type distribution is
`η t ∗ G` (`G` with density `ψ`), and play is a central pooling equilibrium satisfying `D1^∞`:
the upper tail `(vhi t, ∞)` (with `μ t ≤ vhi t`, `μ t` the minimiser of `m_t`) is separating and
`a_t' = κ m_t' / (2 (x - a_t))` there. If adaptation losses are bounded by `B`, the mass of the
upper tail cannot stay above `δ > 0` infinitely often (last paragraph of the proof of
Proposition A5); symmetrically for the lower tail.
-/

namespace CC.LearnTheta

open MeasureTheory Filter Topology Set

/-- The far upper tail of the type law `η t ∗ G` vanishes uniformly. -/
lemma conv_upper_tail {ψ : ℝ → ℝ} [IsProbabilityMeasure (vLaw ψ)]
    {c : ℝ} {η : ℕ → Measure ℝ} [∀ t, IsProbabilityMeasure (η t)]
    (hη2 : ∀ t, Integrable (fun y => (y - c) ^ 2) (η t))
    (hηc : Tendsto (fun t => ∫ y, (y - c) ^ 2 ∂η t) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) : ∃ K₀ : ℝ, ∀ᶠ t in atTop, ∀ u, K₀ ≤ u →
      Measure.conv (η t) (vLaw ψ) (Ioi (c + u)) < ENNReal.ofReal ε := by
  obtain ⟨N, hN⟩ := PoolTailAux.exists_Ioi_lt (vLaw ψ) (half_pos hε)
  refine ⟨N + 1, ?_⟩
  filter_upwards [PoolTailAux.eventually_meas_far_lt hη2 hηc one_pos (half_pos hε)] with t ht u hu
  have h1 := PoolTailAux.conv_Ioi_le (η t) (vLaw ψ) c zero_le_one (c + u)
  have h2 : vLaw ψ (Ioi (c + u - c - 1)) ≤ vLaw ψ (Ioi (N : ℝ)) :=
    measure_mono (Ioi_subset_Ioi (by linarith))
  calc Measure.conv (η t) (vLaw ψ) (Ioi (c + u))
      ≤ η t {y | 1 ^ 2 ≤ (y - c) ^ 2} + vLaw ψ (Ioi (c + u - c - 1)) := h1
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add ht (h2.trans_lt hN)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- The far lower tail of the type law `η t ∗ G` vanishes uniformly. -/
lemma conv_lower_tail {ψ : ℝ → ℝ} [IsProbabilityMeasure (vLaw ψ)]
    {c : ℝ} {η : ℕ → Measure ℝ} [∀ t, IsProbabilityMeasure (η t)]
    (hη2 : ∀ t, Integrable (fun y => (y - c) ^ 2) (η t))
    (hηc : Tendsto (fun t => ∫ y, (y - c) ^ 2 ∂η t) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) : ∃ K₀ : ℝ, ∀ᶠ t in atTop, ∀ u, K₀ ≤ u →
      Measure.conv (η t) (vLaw ψ) (Iio (c - u)) < ENNReal.ofReal ε := by
  obtain ⟨N, hN⟩ := PoolTailAux.exists_Iio_lt (vLaw ψ) (half_pos hε)
  refine ⟨N + 1, ?_⟩
  filter_upwards [PoolTailAux.eventually_meas_far_lt hη2 hηc one_pos (half_pos hε)] with t ht u hu
  have h1 := PoolTailAux.conv_Iio_le (η t) (vLaw ψ) c zero_le_one (c - u)
  have h2 : vLaw ψ (Iio (c - u - c + 1)) ≤ vLaw ψ (Iio (-(N : ℝ))) :=
    measure_mono (Iio_subset_Iio (by linarith))
  calc Measure.conv (η t) (vLaw ψ) (Iio (c - u))
      ≤ η t {y | 1 ^ 2 ≤ (y - c) ^ 2} + vLaw ψ (Iio (c - u - c + 1)) := h1
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add ht (h2.trans_lt hN)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- **Upper tail (case `κ > κck`).** Along a path where `∫ (y - c)² dη_t → 0`, the upper tail of
the central pool cannot keep probability at least `δ > 0`. -/
theorem upper_tail_false (κ : ℝ) (hκ : κck < κ) (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψpos : ∀ x, 0 < ψ x) (hψb : ∃ C, ∀ x, ψ x ≤ C) [IsProbabilityMeasure (vLaw ψ)]
    (c : ℝ) (η : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (η t)]
    (hη2 : ∀ t, Integrable (fun y => (y - c) ^ 2) (η t))
    (hηc : Tendsto (fun t => ∫ y, (y - c) ^ 2 ∂η t) atTop (𝓝 0))
    (a : ℕ → ℝ → ℝ) (μ : ℕ → ℝ) (vhi : ℕ → EReal)
    (hconv : ∀ t, StrictConvexOn ℝ univ (mfun ψ (η t)))
    (hdiff : ∀ t, Differentiable ℝ (mfun ψ (η t)))
    (hmin : ∀ t x, mfun ψ (η t) (μ t) ≤ mfun ψ (η t) x)
    (hμ : ∀ t, ((μ t : ℝ) : EReal) ≤ vhi t)
    (hode : ∀ t (x : ℝ), vhi t < (x : EReal) →
      0 < κ * deriv (mfun ψ (η t)) x / (2 * (x - a t x)) ∧
        HasDerivAt (a t) (κ * deriv (mfun ψ (η t)) x / (2 * (x - a t x))) x)
    (B : ℝ) (hB : ∀ t, ∫⁻ x, ENNReal.ofReal ((a t x - x) ^ 2) ∂(Measure.conv (η t) (vLaw ψ)) ≤
      ENNReal.ofReal B)
    (δ : ℝ) (hδ : 0 < δ)
    (hfreq : ∃ᶠ t in atTop,
      ENNReal.ofReal δ ≤ Measure.conv (η t) (vLaw ψ) {x : ℝ | vhi t < (x : EReal)}) :
    False :=
  PoolTailAux.upper_core hκ (c := c) (fun t => mfun ψ (η t))
    (fun lo hi _ hε => PoolTailAux.mfun_unif hψc hψpos hψb hη2 hηc lo hi hε)
    (fun t x => PoolTailAux.mfun_nonneg hψpos (η t) x) (fun t => (hconv t).convexOn) hdiff
    a μ vhi hmin hμ hode (fun t => Measure.conv (η t) (vLaw ψ))
    (conv_upper_tail hη2 hηc) B hB δ hδ hfreq

/-- **Lower tail (case `κ > κck`).** Along a path where `∫ (y - c)² dη_t → 0`, the lower tail of
the central pool cannot keep probability at least `δ > 0`. -/
theorem lower_tail_false (κ : ℝ) (hκ : κck < κ) (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψpos : ∀ x, 0 < ψ x) (hψb : ∃ C, ∀ x, ψ x ≤ C) [IsProbabilityMeasure (vLaw ψ)]
    (c : ℝ) (η : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (η t)]
    (hη2 : ∀ t, Integrable (fun y => (y - c) ^ 2) (η t))
    (hηc : Tendsto (fun t => ∫ y, (y - c) ^ 2 ∂η t) atTop (𝓝 0))
    (a : ℕ → ℝ → ℝ) (μ : ℕ → ℝ) (vlo : ℕ → EReal)
    (hconv : ∀ t, StrictConvexOn ℝ univ (mfun ψ (η t)))
    (hdiff : ∀ t, Differentiable ℝ (mfun ψ (η t)))
    (hmin : ∀ t x, mfun ψ (η t) (μ t) ≤ mfun ψ (η t) x)
    (hμ : ∀ t, vlo t ≤ ((μ t : ℝ) : EReal))
    (hode : ∀ t (x : ℝ), (x : EReal) < vlo t →
      0 < κ * deriv (mfun ψ (η t)) x / (2 * (x - a t x)) ∧
        HasDerivAt (a t) (κ * deriv (mfun ψ (η t)) x / (2 * (x - a t x))) x)
    (B : ℝ) (hB : ∀ t, ∫⁻ x, ENNReal.ofReal ((a t x - x) ^ 2) ∂(Measure.conv (η t) (vLaw ψ)) ≤
      ENNReal.ofReal B)
    (δ : ℝ) (hδ : 0 < δ)
    (hfreq : ∃ᶠ t in atTop,
      ENNReal.ofReal δ ≤ Measure.conv (η t) (vLaw ψ) {x : ℝ | (x : EReal) < vlo t}) :
    False :=
  PoolTailAux.lower_core hκ (c := c) (fun t => mfun ψ (η t))
    (fun lo hi _ hε => PoolTailAux.mfun_unif hψc hψpos hψb hη2 hηc lo hi hε)
    (fun t x => PoolTailAux.mfun_nonneg hψpos (η t) x) (fun t => (hconv t).convexOn) hdiff
    a μ vlo hmin hμ hode (fun t => Measure.conv (η t) (vLaw ψ))
    (conv_lower_tail hη2 hηc) B hB δ hδ hfreq

end CC.LearnTheta
