import ConformityConcerns.PeriodGame.Defs
import Mathlib.Probability.Distributions.Gaussian.Real
import ConformityConcerns.PeriodGame.DichotomyAux

/-!
# Lemma 3 (linear dichotomy)
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The conclusion of Lemma 3 from the strong form. -/
lemma Game.RevealingWith.lemma3_concl {G : Game Ω} {a : Ω → ℝ} {φ : Kernel ℝ ℝ} {l : ℝ}
    (h : G.RevealingWith a φ l) :
    G.IsRevealing a ∧ (G.P.map a).support = univ ∧
      ∃ α β σ2 : ℝ, 0 ≤ σ2 ∧ (∀ x, ∫ b, b ∂(φ x) = α * x + β ∧ variance id (φ x) = σ2) ∧
        ∀ᵐ x ∂(G.P.map a), φ x = gaussianReal (α * x + β) σ2.toNNReal := by
  obtain ⟨hl, -, ha, hsupp, hall, hgauss⟩ := h
  refine ⟨⟨l, (1 - l) * G.meanZ, hl, ha.mono fun ω hω => by rw [hω]; ring⟩, hsupp,
    G.sens / l, G.norm - G.sens / l * G.meanZ, G.condVar, G.condVar_nonneg,
    fun x => ⟨(hall x).2.1, (hall x).2.2⟩, hgauss⟩

/-- **Lemma 3 when `s̃(h) ≠ 0`** (no measurability needed). -/
theorem lemma3_of_sens_ne_zero (G : Game Ω) (hG : G.Std) (hs : G.sens ≠ 0) {a : Ω → ℝ}
    {φ : Kernel ℝ ℝ} (hE : G.IsLinearEq a φ) :
    G.IsPooling a ∨
      (G.IsRevealing a ∧ (G.P.map a).support = univ ∧
        ∃ α β σ2 : ℝ, 0 ≤ σ2 ∧ (∀ x, ∫ b, b ∂(φ x) = α * x + β ∧ variance id (φ x) = σ2) ∧
          ∀ᵐ x ∂(G.P.map a), φ x = gaussianReal (α * x + β) σ2.toNNReal) := by
  rcases hG.lemma3_ne hs hE with h | ⟨l, hl⟩
  · exact Or.inl h
  · exact Or.inr hl.lemma3_concl

/-- **Lemma 3** under the additional hypothesis that `Z` is measurable. -/
theorem lemma3_of_measurable (G : Game Ω) (hG : G.Std) (hZ : Measurable G.Z) {a : Ω → ℝ}
    {φ : Kernel ℝ ℝ} (hE : G.IsLinearEq a φ) (hSO : G.sens = 0 → G.IsSignalingEq a φ) :
    G.IsPooling a ∨
      (G.IsRevealing a ∧ (G.P.map a).support = univ ∧
        ∃ α β σ2 : ℝ, 0 ≤ σ2 ∧ (∀ x, ∫ b, b ∂(φ x) = α * x + β ∧ variance id (φ x) = σ2) ∧
          ∀ᵐ x ∂(G.P.map a), φ x = gaussianReal (α * x + β) σ2.toNNReal) := by
  rcases hG.lemma3_strong hZ hE hSO with h | ⟨l, hl⟩
  · exact Or.inl h
  · exact Or.inr hl.lemma3_concl

/-- **Lemma 3.** If public beliefs at `h^t` are Gaussian, then in any equilibrium satisfying
Linearity and, if `s̃(h^t) = 0`, Social Optimality, `a_t` is either constant or strictly
increasing and affine in `Z_t` (almost surely); in the latter case every action is on path and
`φ(· | h^t, a_t)` is Gaussian with variance independent of `a_t`.

The standing assumptions `Game.Std` include that `Z` is measurable, as it is an affine
function of `(s_t, v_t)`. -/
theorem lemma3 (G : Game Ω) (hG : G.Std) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsLinearEq a φ)
    (hSO : G.sens = 0 → G.IsSignalingEq a φ) :
    G.IsPooling a ∨
      (G.IsRevealing a ∧ (G.P.map a).support = univ ∧
        ∃ α β σ2 : ℝ, 0 ≤ σ2 ∧ (∀ x, ∫ b, b ∂(φ x) = α * x + β ∧ variance id (φ x) = σ2) ∧
          ∀ᵐ x ∂(G.P.map a), φ x = gaussianReal (α * x + β) σ2.toNNReal) := by
  by_cases hs : G.sens = 0
  · exact lemma3_of_measurable G hG hG.measZ hE hSO
  · exact lemma3_of_sens_ne_zero G hG hs hE

end CC.LG
