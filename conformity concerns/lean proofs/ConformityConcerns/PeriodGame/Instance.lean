import ConformityConcerns.PeriodGame.Revealing
import ConformityConcerns.PeriodGame.InstFacts
import ConformityConcerns.Dynamics.Defs
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The period game at a Gaussian history, and the covariance process of the signaling equilibrium

At a history where `(θ, μ) | h ~ N(m, Σ)`, player `t`'s private information is
`ω = (s_t, v_t) ~ N(m, Σ + I)`, `Z = γ (θ(h) + K₀₀ (s - θ(h)) + K₀₁ (v - μ(h))) + v` and
`c0 = γ² Var(θ | h, s, v)`.
-/

namespace CC

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal

/-- The period game at a history with Gaussian beliefs `N(m, Σ)`, weight `γ`, concern `κ`. -/
noncomputable def gameAt (m : EuclideanSpace ℝ (Fin 2)) (S : M2) (γ κ : ℝ) :
    LG.Game (EuclideanSpace ℝ (Fin 2)) where
  P := multivariateGaussian m (S + 1)
  Z := fun ω => γ * (m 0 + gainK S 0 0 * (ω 0 - m 0) + gainK S 0 1 * (ω 1 - m 1)) + ω 1
  v := fun ω => ω 1
  κ := κ
  c0 := γ ^ 2 * postVarθ S

variable {m : EuclideanSpace ℝ (Fin 2)} {S : M2} {γ κ : ℝ}

theorem gameAt_std (hS : S.PosSemidef) (hκ : 0 < κ) : (gameAt m S γ κ).Std where
  prob := inferInstanceAs (IsProbabilityMeasure (multivariateGaussian m (S + 1)))
  gauss := inst_hasGaussianLaw_Zv γ
  varZ_pos := by
    rw [show variance (gameAt m S γ κ).Z (gameAt m S γ κ).P = varZ S γ from inst_variance_Z hS γ]
    exact cm_varZ_pos hS γ
  κ_pos := hκ
  c0_nonneg := mul_nonneg (sq_nonneg γ) (inst_postVarθ_nonneg hS)
  measZ := inst_measurable_Z γ

lemma gameAt_measurable_Z : Measurable (gameAt m S γ κ).Z := inst_measurable_Z γ

theorem gameAt_variance_Z (hS : S.PosSemidef) :
    variance (gameAt m S γ κ).Z (gameAt m S γ κ).P = varZ S γ :=
  inst_variance_Z hS γ

theorem gameAt_variance_v (hS : S.PosSemidef) :
    variance (gameAt m S γ κ).v (gameAt m S γ κ).P = Vt S :=
  inst_variance_v hS

/-- `Var(Z | h) = V + 2γC + γ²H` (the denominator of the sensitivity). -/
theorem varZ_eq (hS : S.PosSemidef) : varZ S γ = Vt S + 2 * γ * Ct S + γ ^ 2 * Ht S := by
  have hs := sym_of_psd hS
  have hd := dE_ne (psd_PSDE hS)
  rw [varZ_eq_vZE hs hd, vZE_eq_VCH hs hd]

/-- The sensitivity of the period game is `(V + γC)/(V + 2γC + γ²H)` (the formula in the proof of Proposition 2). -/
theorem gameAt_sens (hS : S.PosSemidef) : (gameAt m S γ κ).sens = sens S γ := by
  rw [LG.Game.sens, gameAt_variance_Z hS, varZ_eq hS,
    show cov[(gameAt m S γ κ).v, (gameAt m S γ κ).Z; (gameAt m S γ κ).P] = Vt S + γ * Ct S from
      inst_cov_vZ hS γ, sens]

/-- The signaling equilibrium at every history with covariance `Σ` (any means) is revealing. -/
def periodRevealing (κ : ℝ) (S : M2) (γ : ℝ) : Prop :=
  ∀ (m : EuclideanSpace ℝ (Fin 2)) (a : EuclideanSpace ℝ (Fin 2) → ℝ) (φ : Kernel ℝ ℝ),
    (gameAt m S γ κ).IsSignalingEq a φ → (gameAt m S γ κ).IsRevealing a

lemma gameAt_revCrit_iff (hκ : 0 < κ) : |sens S γ| ≤ √(κck / κ) ↔ revCrit κ S γ := by
  rw [revCrit, Real.le_sqrt (abs_nonneg _) (div_nonneg κck_pos.le hκ.le), sq_abs,
    le_div_iff₀ hκ, mul_comm]

/-- By Corollary 1, the period is revealing iff `κ s̃² ≤ κck`. -/
theorem periodRevealing_iff (hS : S.PosSemidef) (hκ : 0 < κ) :
    periodRevealing κ S γ ↔ revCrit κ S γ := by
  have key : ∀ m : EuclideanSpace ℝ (Fin 2),
      |(gameAt m S γ κ).sens| ≤ √(κck / (gameAt m S γ κ).κ) ↔ revCrit κ S γ := fun m => by
    rw [gameAt_sens hS, show (gameAt m S γ κ).κ = κ from rfl, gameAt_revCrit_iff hκ]
  constructor
  · intro h
    have hG := gameAt_std (m := 0) (γ := γ) hS hκ
    obtain ⟨a, φ, hE⟩ := (hG.lemma1 gameAt_measurable_Z).1
    exact (key 0).1 ((hG.corollary1 gameAt_measurable_Z hE).1 (h 0 a φ hE))
  · intro h m a φ hE
    exact ((gameAt_std hS hκ).corollary1 gameAt_measurable_Z hE).2 ((key m).2 h)

/-- The posterior covariance process of the signaling equilibrium: after a revealing period the
public observes `Z_t` (an affine bijection of `a_t`) and updates by `kalman`. -/
noncomputable def SigmaSeq (κ : ℕ → ℝ) (S₁ : M2) (γ : ℕ → ℝ) : ℕ → M2
  | 0 => S₁
  | t + 1 =>
    haveI := Classical.propDecidable (periodRevealing (κ t) (SigmaSeq κ S₁ γ t) (γ t))
    if periodRevealing (κ t) (SigmaSeq κ S₁ γ t) (γ t) then kalman (SigmaSeq κ S₁ γ t) (γ t)
    else SigmaSeq κ S₁ γ t

/-- The signaling-equilibrium covariance process is the process `SigmaC` driven by the
criterion of Corollary 1. -/
theorem SigmaSeq_eq_SigmaC (κ : ℕ → ℝ) (hκ : ∀ t, 0 < κ t) (S₁ : M2) (hS : S₁.PosSemidef)
    (γ : ℕ → ℝ) : SigmaSeq κ S₁ γ = SigmaC κ S₁ γ := by
  have key : ∀ t, SigmaSeq κ S₁ γ t = SigmaC κ S₁ γ t ∧ (SigmaC κ S₁ γ t).PosSemidef := by
    intro t
    induction t with
    | zero => exact ⟨rfl, hS⟩
    | succ t ih =>
      obtain ⟨h1, h2⟩ := ih
      have hiff := periodRevealing_iff (γ := γ t) h2 (hκ t)
      simp only [SigmaSeq, SigmaC, h1]
      by_cases hc : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)
      · have hp : periodRevealing (κ t) (SigmaSeq κ S₁ γ t) (γ t) := by rw [h1]; exact hiff.2 hc
        exact ⟨by simp only [hp, hc, ↓reduceIte], by simp only [hc, ↓reduceIte]; exact kalman_psd h2 _⟩
      · have hp : ¬ periodRevealing (κ t) (SigmaSeq κ S₁ γ t) (γ t) := by
          rw [h1]; exact mt hiff.1 hc
        exact ⟨by simp only [hp, hc, ↓reduceIte], by simp only [hc, ↓reduceIte]; exact h2⟩
  funext t
  exact (key t).1

end CC
