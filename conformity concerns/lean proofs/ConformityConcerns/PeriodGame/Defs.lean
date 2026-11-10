import ConformityConcerns.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.Convex.Hull

/-!
# The linear–Gaussian period game (Sections 2–4)

Fix a period `t` and a public history `h^t` at which public beliefs are Gaussian. Player `t`'s
private type is a point `ω` of a probability space `(Ω, P)` (for instance `(s_t, v_t)` with its
conditional law given `h^t`). Two random variables matter:

* `Z ω = γ_t E(θ | h^t, s_t, v_t) + v_t`, the payoff-relevant statistic: by Gaussian conditioning
  `E((x - γ_t θ - v_t)² | h^t, s_t, v_t) = (x - Z)² + c0` with `c0 = γ_t² Var(θ | h^t, s_t, v_t)`;
* `v ω = v_t`, the preference type about which the public forms its belief.

`(Z, v)` is jointly Gaussian given `h^t`. A strategy is a measurable `a : Ω → ℝ`; the public's
belief after action `x` is a probability measure `φ x` on preference types (a Markov kernel).
The norm is `μ(h^t) = E(v | h^t)`. Player `t`'s payoff from `x` is
`-(x - Z)² - c0 - κ ∫ (b - μ(h^t))² φ(db | x)`; we work with the loss
`(x - Z)² + κ ∫ (b - μ(h^t))² dφ(x) ∈ [0, ∞]`.

* Perfect Bayesian equilibrium: every type best-responds, and beliefs are given by Bayes' rule on
  path: the joint law of (action, type) disintegrates as `(law of a) ⊗ φ`.
* Linearity: on `I(h^t)`, the convex hull of the support of the action, the posterior mean and the
  posterior variance are affine in the action.
* Social optimality: among linear equilibria at `h^t`, maximise player `t`'s expected utility.
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The linear–Gaussian period game at a fixed history. -/
structure Game (Ω : Type*) [MeasurableSpace Ω] where
  /-- Law of player `t`'s private information given `h^t`. -/
  P : Measure Ω
  /-- `Z = γ_t E(θ | h^t, s_t, v_t) + v_t`. -/
  Z : Ω → ℝ
  /-- The preference type `v_t`. -/
  v : Ω → ℝ
  /-- Conformity concern `κ`. -/
  κ : ℝ
  /-- Constant part of the adaptation loss, `γ_t² Var(θ | h^t, s_t, v_t)`. -/
  c0 : ℝ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Standing assumptions: `P` is a probability measure, `(Z, v)` is jointly Gaussian with
`Var Z > 0`, `κ > 0`, `c0 ≥ 0`, and `Z` is measurable (a random variable). -/
structure Game.Std (G : Game Ω) : Prop where
  prob : IsProbabilityMeasure G.P
  gauss : HasGaussianLaw (fun ω => (G.Z ω, G.v ω)) G.P
  varZ_pos : 0 < variance G.Z G.P
  κ_pos : 0 < G.κ
  c0_nonneg : 0 ≤ G.c0
  measZ : Measurable G.Z

namespace Game

variable (G : Game Ω)

/-- The norm `μ(h^t) = E(v_t | h^t)`. -/
noncomputable def norm : ℝ := ∫ ω, G.v ω ∂G.P

/-- `E(Z_t | h^t)`. -/
noncomputable def meanZ : ℝ := ∫ ω, G.Z ω ∂G.P

/-- The sensitivity `s̃(h^t) = Cov(v_t, Z_t | h^t)/Var(Z_t | h^t)`. -/
noncomputable def sens : ℝ := cov[G.v, G.Z; G.P] / variance G.Z G.P

/-- Expected conformity loss `∫ (b - μ(h^t))² φ(db | x)` after action `x`. -/
noncomputable def confLoss (φ : Kernel ℝ ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ b, ENNReal.ofReal ((b - G.norm) ^ 2) ∂(φ x)

/-- Loss of type `ω` from action `x`: `(x - Z)² + κ ∫ (b - μ)² dφ(x)` (payoff `= -loss - c0`). -/
noncomputable def loss (φ : Kernel ℝ ℝ) (ω : Ω) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((x - G.Z ω) ^ 2) + ENNReal.ofReal G.κ * G.confLoss φ x

/-- Perfect Bayesian equilibrium of the period game. -/
structure IsPBE (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : Prop where
  meas : Measurable a
  markov : IsMarkovKernel φ
  optimal : ∀ ω x, G.loss φ ω (a ω) ≤ G.loss φ ω x
  bayes : (G.P.map a) ⊗ₘ φ = G.P.map (fun ω => (a ω, G.v ω))

/-- `I(h^t)`: the convex hull of the support of the action. -/
def actionHull (a : Ω → ℝ) : Set ℝ := convexHull ℝ (G.P.map a).support

/-- Linearity: on `I(h^t)` the posterior mean and variance are affine in the action. -/
def IsLinear (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : Prop :=
  ∃ α β p q : ℝ, ∀ x ∈ G.actionHull a,
    Integrable (fun b : ℝ => b ^ 2) (φ x) ∧ ∫ b, b ∂(φ x) = α * x + β ∧
      variance id (φ x) = p * x + q

/-- A linear equilibrium. -/
def IsLinearEq (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : Prop := G.IsPBE a φ ∧ G.IsLinear a φ

/-- Ex-ante expected loss `E(loss)`; expected utility is `-(exLoss) - c0`. -/
noncomputable def exLoss (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : ℝ≥0∞ := ∫⁻ ω, G.loss φ ω (a ω) ∂G.P

/-- Signaling equilibrium: a linear equilibrium satisfying social optimality. -/
def IsSignalingEq (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : Prop :=
  G.IsLinearEq a φ ∧ ∀ (a' : Ω → ℝ) (φ' : Kernel ℝ ℝ), G.IsLinearEq a' φ' → G.exLoss a φ ≤ G.exLoss a' φ'

/-- Pooling: the action is (almost surely) constant. -/
def IsPooling (a : Ω → ℝ) : Prop := ∃ c : ℝ, a =ᵐ[G.P] fun _ => c

/-- Revealing: the action is (almost surely) a strictly increasing affine function of `Z`. -/
def IsRevealing (a : Ω → ℝ) : Prop := ∃ k b : ℝ, 0 < k ∧ a =ᵐ[G.P] fun ω => k * G.Z ω + b

/-- Equilibrium utility of type `ω`: `-(loss) - c0`. -/
noncomputable def utility (a : Ω → ℝ) (φ : Kernel ℝ ℝ) (ω : Ω) : ℝ :=
  -(G.loss φ ω (a ω)).toReal - G.c0

/-- Expected utility `E(u_t | h^t)`. -/
noncomputable def exUtility (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : ℝ := -(G.exLoss a φ).toReal - G.c0

/-- Expected adaptation payoff `E(-(a_t - γ_t θ - v_t)² | h^t) = -(E((a - Z)²) + c0)`. -/
noncomputable def exAdapt (a : Ω → ℝ) : ℝ := -(∫ ω, (a ω - G.Z ω) ^ 2 ∂G.P) - G.c0

end Game

end CC.LG
