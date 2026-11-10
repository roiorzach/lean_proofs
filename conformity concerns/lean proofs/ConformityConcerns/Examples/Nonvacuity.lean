import ConformityConcerns.PeriodGame.CommonKnowledge
import ConformityConcerns.PeriodGame.Instance
import ConformityConcerns.General.CentralPooling
import ConformityConcerns.General.KnownMu
import ConformityConcerns.General.Quadratic
import ConformityConcerns.Examples.General
import ConformityConcerns.Examples.Dynamics

/-!
# Non-vacuity of the main definitions

* The linear–Gaussian period game: in the common-knowledge game with `κ = 1/8` a revealing
  signaling equilibrium exists, and with `κ = 1` a pooling one; the period game at a Gaussian
  history `gameAt` satisfies the standing assumptions.
* The general-loss environment: a compactified PBE satisfying `D1^∞` exists (the fully pooling
  one), and for `κ ≤ κck` a fully revealing one.
* Proposition A5's fixed-history environment: `m(x) = x²/2` (so `0 < m'' ≤ 2`, `x* = 0`) with
  quadratic adaptation loss is a valid `Setting`.
-/

namespace CC.Examples

open MeasureTheory ProbabilityTheory General

/-- A revealing signaling equilibrium exists in the common-knowledge game with `κ = 1/8`. -/
example : ∃ (a : ℝ → ℝ) (φ : Kernel ℝ ℝ),
    (LG.ckGame (1 / 8)).IsSignalingEq a φ ∧ (LG.ckGame (1 / 8)).IsRevealing a := by
  have hG := LG.ckGame_std (κ := 1 / 8) (by norm_num)
  obtain ⟨a, φ, h⟩ := (LG.lemma1 _ hG).1
  refine ⟨a, φ, h, (LG.corollary1 _ hG h).2 ?_⟩
  rw [LG.ckGame_sens]
  show |(1 : ℝ)| ≤ √(κck / (1 / 8))
  rw [abs_one, Real.one_le_sqrt]
  norm_num [κck]

/-- With `κ = 1` the signaling equilibrium of the common-knowledge game pools. -/
example : ∃ (a : ℝ → ℝ) (φ : Kernel ℝ ℝ),
    (LG.ckGame 1).IsSignalingEq a φ ∧ (LG.ckGame 1).IsPooling a := by
  have hG := LG.ckGame_std (κ := 1) (by norm_num)
  obtain ⟨a, φ, h⟩ := (LG.lemma1 _ hG).1
  refine ⟨a, φ, h, ((LG.lemma1 _ hG).2 a φ h).2.2 ?_⟩
  rintro ⟨α, hα⟩
  rw [LG.ckGame_sens] at hα
  have : (LG.ckGame 1).κ = 1 := rfl
  rw [this] at hα
  nlinarith [sq_nonneg (α - 1 / 2)]

/-- The period game at the history with `Σ = I`, `γ = 1/2`, `κ = 1` satisfies the standing
assumptions. -/
example : (gameAt 0 (1 : M2) (1 / 2) 1).Std := gameAt_std Matrix.PosDef.one.posSemidef one_pos

/-- In the general-loss environment a compactified PBE satisfying `D1^∞` exists. -/
example (κ μ : ℝ) (hκ : 0 < κ) :
    ∃ (a : ℝ → ℝ) (φ : ℝ → Measure EReal),
      (quadSetting κ μ hκ).IsCPBE a φ ∧ (quadSetting κ μ hκ).D1Inf a φ :=
  ⟨_, _, propA3_ii (quadSetting κ μ hκ) 0⟩

/-- For `κ ≤ κck` a fully revealing `D1^∞` equilibrium exists (Proposition A4). -/
example : ∃ (a : ℝ → ℝ) (φ : ℝ → Measure EReal), (quadSetting (1 / 8) 0 (by norm_num)).IsCPBE a φ ∧
    (quadSetting (1 / 8) 0 (by norm_num)).D1Inf a φ ∧ StrictMono a := by
  obtain ⟨Φ, hΦ, -, -, h⟩ := propA4_revealing (1 / 8) (by norm_num) (by norm_num [κck])
  obtain ⟨φ, h1, h2⟩ := h (quadSetting (1 / 8) 0 (by norm_num)) rfl rfl
  refine ⟨_, φ, h1, h2, fun x y hxy => ?_⟩
  simp only [quadSetting, sub_zero, zero_add]
  exact hΦ hxy

/-- Proposition A5's fixed-history environment with `m(x) = x²/2`: the hypotheses of
`propA5_period` hold for `quadSetting (κ/2) 0`. -/
example (κ : ℝ) (hκ : 0 < κ) :
    let m : ℝ → ℝ := fun x => x ^ 2 / 2
    ContDiff ℝ 2 m ∧ (∀ x, 0 < iteratedDeriv 2 m x ∧ iteratedDeriv 2 m x ≤ 2) ∧
      deriv m (quadSetting (κ / 2) 0 (by positivity)).μ = 0 ∧
      (quadSetting (κ / 2) 0 (by positivity)).g = (fun z => z ^ 2) ∧
      (quadSetting (κ / 2) 0 (by positivity)).ℓ =
        fun x => κ * (m x - m (quadSetting (κ / 2) 0 (by positivity)).μ) := by
  intro m
  have hd : deriv m = fun x => x := by
    funext x
    have : HasDerivAt m x x := by
      have := (hasDerivAt_pow 2 x).div_const 2
      simpa [m] using this
    exact this.deriv
  have h2 : ∀ x, iteratedDeriv 2 m x = 1 := fun x => by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd]; simp
  refine ⟨by fun_prop, fun x => by rw [h2]; norm_num, ?_, rfl, ?_⟩
  · show deriv m 0 = 0
    rw [hd]
  · funext x
    show κ / 2 * (x - 0) ^ 2 = κ * (x ^ 2 / 2 - 0 ^ 2 / 2)
    ring

end CC.Examples
