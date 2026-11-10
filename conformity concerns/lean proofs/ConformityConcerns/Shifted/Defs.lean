import ConformityConcerns.PeriodGame.Defs

/-!
# Shifted preferences (online appendix, "Shifted Preferences"): the period game

Players want their perceived preference type to be `c` units above the public mean, so the
conformity term of equation (1) becomes `-κ ∫ (b - μ(h^t) - c)² φ(db | h^t, a_t)`.

The game is the linear–Gaussian period game `Game` of `PeriodGame/Defs.lean` (same private
information, same `Z`, `v`, `κ`, `c0`, same sensitivity `s̃ = Cov(v, Z)/Var Z`); only the
conformity loss changes. The equilibrium notions are those of the baseline with the shifted
loss:

* `IsShPBE c`: perfect Bayesian equilibrium (every type best-responds to the shifted loss;
  beliefs follow Bayes' rule on path);
* `IsShLinearEq c`: a perfect Bayesian equilibrium satisfying Linearity (`Game.IsLinear`,
  unchanged: it does not involve the loss);
* `IsShSignalingEq c`: Social Optimality, i.e. a linear equilibrium minimising the ex-ante
  loss among all linear equilibria at `h^t`;
* `IsShAltEq c`: the alternative selection of the last sentence of the section: the
  payoff-maximising revealing linear equilibrium whenever a revealing linear equilibrium
  exists, and otherwise the payoff-maximising linear equilibrium (Social Optimality).

`IsPooling`, `IsRevealing`, `sens`, `meanZ`, `norm` are those of `Game`.
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Game

variable (G : Game Ω)

/-- Shifted conformity loss `∫ (b - μ(h^t) - c)² φ(db | x)` after action `x`. -/
noncomputable def shConfLoss (c : ℝ) (φ : Kernel ℝ ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ b, ENNReal.ofReal ((b - G.norm - c) ^ 2) ∂(φ x)

/-- Loss of type `ω` from action `x` with shift `c`: `(x - Z)² + κ ∫ (b - μ - c)² dφ(x)`
(payoff `= -loss - c0`). -/
noncomputable def shLoss (c : ℝ) (φ : Kernel ℝ ℝ) (ω : Ω) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((x - G.Z ω) ^ 2) + ENNReal.ofReal G.κ * G.shConfLoss c φ x

/-- Perfect Bayesian equilibrium of the period game with shift `c`. -/
structure IsShPBE (c : ℝ) (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : Prop where
  meas : Measurable a
  markov : IsMarkovKernel φ
  optimal : ∀ ω x, G.shLoss c φ ω (a ω) ≤ G.shLoss c φ ω x
  bayes : (G.P.map a) ⊗ₘ φ = G.P.map (fun ω => (a ω, G.v ω))

/-- A linear equilibrium of the period game with shift `c`. -/
def IsShLinearEq (c : ℝ) (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : Prop :=
  G.IsShPBE c a φ ∧ G.IsLinear a φ

/-- Ex-ante expected loss with shift `c`; expected utility is `-(shExLoss) - c0`. -/
noncomputable def shExLoss (c : ℝ) (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, G.shLoss c φ ω (a ω) ∂G.P

/-- Signaling equilibrium with shift `c`: a linear equilibrium satisfying Social Optimality. -/
def IsShSignalingEq (c : ℝ) (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : Prop :=
  G.IsShLinearEq c a φ ∧
    ∀ (a' : Ω → ℝ) (φ' : Kernel ℝ ℝ), G.IsShLinearEq c a' φ' →
      G.shExLoss c a φ ≤ G.shExLoss c a' φ'

/-- A revealing linear equilibrium exists at `h^t` with shift `c`. -/
def HasShRevealingEq (c : ℝ) : Prop :=
  ∃ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShLinearEq c a φ ∧ G.IsRevealing a

/-- The alternative selection: if a revealing linear equilibrium exists, the payoff-maximising
revealing linear equilibrium; otherwise the payoff-maximising linear equilibrium. -/
def IsShAltEq (c : ℝ) (a : Ω → ℝ) (φ : Kernel ℝ ℝ) : Prop :=
  G.IsShLinearEq c a φ ∧
    (G.HasShRevealingEq c → G.IsRevealing a ∧
      ∀ (a' : Ω → ℝ) (φ' : Kernel ℝ ℝ), G.IsShLinearEq c a' φ' → G.IsRevealing a' →
        G.shExLoss c a φ ≤ G.shExLoss c a' φ') ∧
    (¬ G.HasShRevealingEq c →
      ∀ (a' : Ω → ℝ) (φ' : Kernel ℝ ℝ), G.IsShLinearEq c a' φ' →
        G.shExLoss c a φ ≤ G.shExLoss c a' φ')

/-- `λ = (1 + √(1 - 4κ s̃²))/2`: the slope on `Z` of the revealing rule with the root `α` of
smallest magnitude, `λ = 1/(1 + κα²)` (as in `signalingEq_char`). -/
noncomputable def lam : ℝ := (1 + √(1 - 4 * G.κ * G.sens ^ 2)) / 2

/-- The threshold `c̄ = λ √(λ (2 - λ) Var Z) / (κ |s̃|)` on `|c|` (for `s̃ ≠ 0`): it solves
`κ² s̃² c̄² = λ³ (2 - λ) Var Z`, where revealing and pooling give the same ex-ante loss. -/
noncomputable def cbar : ℝ :=
  G.lam * √(G.lam * (2 - G.lam) * variance G.Z G.P) / (G.κ * |G.sens|)

end Game

end CC.LG
