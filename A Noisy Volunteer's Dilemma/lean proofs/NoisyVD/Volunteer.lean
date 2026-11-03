import NoisyVD.ThresholdLower
import NoisyVD.FirstBest

/-!
# Proposition `prop_volunteers`

The Volunteer's Dilemma is the special case `A = Ω = Bool` of the general model, so Statements 1, 2,
the first claim of Statement 3, and Statement 4 follow from Proposition `prop_general_failures`.  The
threshold claim combines Lemmas `lemma_threshold_value` and `lemma_threshold_cutoff`.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

namespace VD

variable {E : Env Bool Bool}

/-- The threshold claim of Statement 3: `liminf Π^T(n) > Π^SQ ↔ F'(0) > \bar F_0`, where
`\bar F_0 = Fbar π H |L| (F(0)(1-F(0)))` depends only on `π, H, L, F(0)`. -/
theorem threshold_iff (hV : Assumptions E) (hN : E.Noise) {t : ℝ} (ht : 0 < t) (hS : Smooth E t) :
    (0 < Fbar (pr E) (H E) (-L E) (E.F 0 * (1 - E.F 0))) ∧
    (E.PiSQ < liminf E.PiT atTop ↔ Fbar (pr E) (H E) (-L E) (E.F 0 * (1 - E.F 0)) < t) := by
  have hs0 := F_zero_pos hN
  have hs1 := F_zero_lt_one hN
  have hSpos : 0 < E.F 0 * (1 - E.F 0) := mul_pos hs0 (by linarith)
  have hpar := par hV hSpos
  obtain ⟨hF0, hiff⟩ := lemma_threshold_cutoff hpar
  obtain ⟨_, hlim⟩ := lemma_threshold_value hV hN ht hS
  refine ⟨hF0, ?_⟩
  rw [hlim.liminf_eq, ← hiff t ht]
  constructor <;> intro h <;> linarith

/-- **Proposition 3 (`prop_volunteers`).** -/
theorem prop_volunteers (hV : Assumptions E) (hN : E.Noise) :
    -- Statement 1
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, E.Pi n = E.PiSQ) ∧
    -- Statement 2
    (HasDerivAt E.F 0 0 → Tendsto E.Pi atTop (𝓝 E.PiSQ)) ∧
    -- Statement 3, first claim
    (∀ t > 0, HasDerivAt E.F t 0 → limsup E.Pi atTop < E.PiFB) ∧
    -- Statement 3, second claim
    (0 < Fbar (pr E) (H E) (-L E) (E.F 0 * (1 - E.F 0)) ∧
      ∀ (U : Set ℝ) (t : ℝ), IsOpen U → (0 : ℝ) ∈ U → ContDiffOn ℝ 1 E.F U → deriv E.F 0 = t → 0 < t →
        (E.PiSQ < liminf E.PiT atTop ↔ Fbar (pr E) (H E) (-L E) (E.F 0 * (1 - E.F 0)) < t)) ∧
    -- Statement 4
    (∀ α > 0, Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α) → Tendsto E.Pi atTop (𝓝 E.PiFB)) := by
  have hs0 := F_zero_pos hN
  have hs1 := F_zero_lt_one hN
  have hSpos : 0 < E.F 0 * (1 - E.F 0) := mul_pos hs0 (by linarith)
  refine ⟨fun δ hδ h => Env.prop_general_1 E hN hδ h, fun h => Env.prop_general_2 E hN (PiSQ_lt_PiFB hV) h,
    fun t _ h => Env.prop_general_3 E hN (PiSQ_lt_PiFB hV) h,
    ⟨(lemma_threshold_cutoff (par hV hSpos)).1, ?_⟩, fun α hα h => Env.prop_general_4 E hα h⟩
  intro U t hU h0 hF hder ht
  exact (threshold_iff hV hN ht (Smooth.of_contDiffOn hU h0 hF hder)).2

end VD

end NoisyVD
