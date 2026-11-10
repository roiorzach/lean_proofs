import ConformityConcerns.PeriodGame.Dichotomy
import ConformityConcerns.PeriodGame.RevealingAux

/-!
# Lemma 1 and Corollary 1 (when is the signaling equilibrium revealing?)
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 1.** A signaling equilibrium exists, and the signaling equilibrium is revealing at
`h^t` if and only if some `α_t` satisfies `(1 + κ α_t²) s̃(h^t) = α_t` (and pooling otherwise).

The standing assumptions `Game.Std` include that `Z` is measurable, as it is an affine
function of `(s_t, v_t)`. -/
theorem lemma1 (G : Game Ω) (hG : G.Std) :
    (∃ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsSignalingEq a φ) ∧
    ∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsSignalingEq a φ →
      (G.IsRevealing a ↔ ∃ α : ℝ, (1 + G.κ * α ^ 2) * G.sens = α) ∧
      (G.IsPooling a ↔ ¬ ∃ α : ℝ, (1 + G.κ * α ^ 2) * G.sens = α) := by
  exact hG.lemma1 hG.measZ

/-- The signaling equilibrium explicitly (proof of Lemma 1): when revealing, Social Optimality
selects the root `α_t` of smallest magnitude, so `a_t = E Z + λ (Z - E Z)` with
`λ = 1/(1 + κ α_t²) = (1 + √(1 - 4κ s̃²))/2`; when pooling, `a_t = E Z`. The ex-ante loss is
`(1 - λ)² Var Z + κ Var v` (revealing) or `Var Z + κ Var v` (pooling).

The standing assumptions `Game.Std` include that `Z` is measurable, as it is an affine
function of `(s_t, v_t)`. -/
theorem signalingEq_char (G : Game Ω) (hG : G.Std) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsSignalingEq a φ) :
    (G.κ * G.sens ^ 2 ≤ κck →
      a =ᵐ[G.P] fun ω => G.meanZ + (1 + √(1 - 4 * G.κ * G.sens ^ 2)) / 2 * (G.Z ω - G.meanZ)) ∧
    (κck < G.κ * G.sens ^ 2 → a =ᵐ[G.P] fun _ => G.meanZ) ∧
    G.exLoss a φ = ENNReal.ofReal
      ((if G.κ * G.sens ^ 2 ≤ κck then ((1 - √(1 - 4 * G.κ * G.sens ^ 2)) / 2) ^ 2 else 1) *
        variance G.Z G.P + G.κ * variance G.v G.P) := by
  exact hG.signalingEq_char hG.measZ hE

/-- The quadratic-formula step of Corollary 1. -/
theorem slope_root_iff (κ s : ℝ) (hκ : 0 < κ) :
    (∃ α : ℝ, (1 + κ * α ^ 2) * s = α) ↔ |s| ≤ √(κck / κ) := by
  rw [slope_root_iff_four, abs_le_sqrt_iff_four hκ]

/-- **Corollary 1.** The signaling equilibrium is revealing at `h^t` iff `|s̃(h^t)| ≤ √(κck/κ)`.

The standing assumptions `Game.Std` include that `Z` is measurable, as it is an affine
function of `(s_t, v_t)`. -/
theorem corollary1 (G : Game Ω) (hG : G.Std) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsSignalingEq a φ) : G.IsRevealing a ↔ |G.sens| ≤ √(κck / G.κ) := by
  exact hG.corollary1 hG.measZ hE

end CC.LG
