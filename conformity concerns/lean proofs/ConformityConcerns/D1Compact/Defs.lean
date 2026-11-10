import ConformityConcerns.General.Defs

/-!
# The period game with a compact type space: `D1^∞` and ordinary D1

Online Appendix, Section "Refinements and Central Pooling with General Losses", the Note after
Definition A1: "When the type space is a compact interval, `D1^∞` and ordinary D1 support the
same equilibrium strategies."

The type space is a compact interval `[lo, hi]` with `lo < hi`, and the type distribution `F`
has a continuous density that is positive on `[lo, hi]` (and `F` puts no mass outside it).
The adaptation loss `g` and the conformity loss `ℓ` (with norm `μ`) satisfy the standing
assumptions `AdaptLoss` and `ConfLoss` of `General/Defs.lean`; `μ` need not lie in `[lo, hi]`.
A belief is a Borel probability measure on `ℝ` that puts no mass outside `[lo, hi]`. Since `ℓ`
is continuous, every belief has a finite conformity loss `∫ ℓ dψ`, so no boundary labels `±∞`
are needed and all payoffs are real.

* `CSetting.survivors`, `CSetting.D1Inf`: `D1^∞` on the compact type space. The survivor set
  after `x` is the set of minimizers over `[lo, hi]` of the clipped index
  `J_x(v) = min {I_x(v), 0}`, where `I_x(v) = U(v) + g(x - v)` (Definition A1 with `[lo, hi]`
  in place of `[-∞, +∞]`).
* `CSetting.D1Elim`, `CSetting.D1Surv`, `CSetting.D1`: ordinary D1 (Cho and Kreps 1987). The
  receiver's possible responses to `x` are the beliefs. Type `v` is eliminated after `x` if
  some other type `v'` strictly gains from `x` under every belief under which `v` weakly gains
  from `x` (gains are relative to the equilibrium payoffs `U(v)`, `U(v')`). After an off-path
  action, beliefs put no mass outside the types that are not eliminated, unless every type is
  eliminated, in which case beliefs are unrestricted (the usual convention).
-/

namespace CC.General.Compact

open MeasureTheory ProbabilityTheory Set

/-- A type distribution on `[lo, hi]` with a continuous density that is positive there. -/
structure CTypeDist (F : Measure ℝ) (lo hi : ℝ) : Prop where
  prob : IsProbabilityMeasure F
  density : ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Icc lo hi) ∧ (∀ x ∈ Icc lo hi, 0 < ψ x) ∧
    F = (volume.restrict (Icc lo hi)).withDensity (fun x => ENNReal.ofReal (ψ x))

/-- The single-period environment with the compact type space `[lo, hi]`. -/
structure CSetting where
  g : ℝ → ℝ
  ℓ : ℝ → ℝ
  μ : ℝ
  lo : ℝ
  hi : ℝ
  F : Measure ℝ
  lo_lt_hi : lo < hi
  hg : AdaptLoss g
  hℓ : ConfLoss ℓ μ
  hF : CTypeDist F lo hi

namespace CSetting

variable (S : CSetting)

/-- A belief: a probability measure on `ℝ` with no mass outside the type space `[lo, hi]`. -/
def IsBelief (ψ : Measure ℝ) : Prop :=
  IsProbabilityMeasure ψ ∧ ψ (Icc S.lo S.hi)ᶜ = 0

/-- Payoff `-g(x - v) - ∫ ℓ dψ` of type `v` from action `x` when the belief after `x` is `ψ`. -/
noncomputable def payoff (x v : ℝ) (ψ : Measure ℝ) : ℝ :=
  -S.g (x - v) - ∫ b, S.ℓ b ∂ψ

/-- A pure perfect Bayesian equilibrium `(a, φ)` of the compact game: every belief is a belief
on `[lo, hi]`; (i) every type in `[lo, hi]` maximizes; (ii) at every on-path action `x`,
beliefs put probability one on `{v ∈ [lo, hi] : a v = x}`, are given by Bayes' rule when this
set has positive `F`-probability, and equal `δ_v` when it is `{v}`. -/
structure IsCPBE (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) : Prop where
  meas : Measurable a
  belief : ∀ x, S.IsBelief (φ x)
  optimal : ∀ v ∈ Icc S.lo S.hi, ∀ x, S.payoff x v (φ x) ≤ S.payoff (a v) v (φ (a v))
  onPath_supp : ∀ v ∈ Icc S.lo S.hi, φ (a v) (Icc S.lo S.hi ∩ a ⁻¹' {a v}) = 1
  onPath_bayes : ∀ v ∈ Icc S.lo S.hi, 0 < S.F (a ⁻¹' {a v}) →
    φ (a v) = S.F[|a ⁻¹' {a v}]
  onPath_dirac : ∀ v ∈ Icc S.lo S.hi, Icc S.lo S.hi ∩ a ⁻¹' {a v} = {v} →
    φ (a v) = Measure.dirac v

/-- Equilibrium payoff `U(v)`. -/
noncomputable def U (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) (v : ℝ) : ℝ :=
  S.payoff (a v) v (φ (a v))

/-- Indifference index `I_x(v) = U(v) + g(x - v)`. -/
noncomputable def indiff (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) (x v : ℝ) : ℝ :=
  S.U a φ v + S.g (x - v)

/-- Clipped index `J_x(v) = min {I_x(v), 0}`. -/
noncomputable def clipped (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) (x v : ℝ) : ℝ :=
  min (S.indiff a φ x v) 0

/-- The `D1^∞` survivor set on the compact type space: `argmin_{z ∈ [lo, hi]} J_x(z)`. -/
def survivors (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) (x : ℝ) : Set ℝ :=
  {z | z ∈ Icc S.lo S.hi ∧ ∀ z' ∈ Icc S.lo S.hi, S.clipped a φ x z ≤ S.clipped a φ x z'}

/-- `D1^∞` on the compact type space: after every off-path action `x`,
`supp φ(x) ⊆ argmin_{[lo, hi]} J_x`. -/
def D1Inf (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) : Prop :=
  ∀ x, x ∉ a '' Icc S.lo S.hi → (φ x).support ⊆ S.survivors a φ x

/-- Ordinary D1 elimination: type `v` is eliminated after `x` if some other type `v'` gains
strictly from `x` under every belief under which `v` gains weakly from `x`. -/
def D1Elim (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) (x v : ℝ) : Prop :=
  ∃ v' ∈ Icc S.lo S.hi, v' ≠ v ∧ ∀ ψ : Measure ℝ, S.IsBelief ψ →
    S.U a φ v ≤ S.payoff x v ψ → S.U a φ v' < S.payoff x v' ψ

/-- The types that ordinary D1 does not eliminate after `x`. -/
def D1Surv (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) (x : ℝ) : Set ℝ :=
  {v | v ∈ Icc S.lo S.hi ∧ ¬ S.D1Elim a φ x v}

/-- Ordinary D1: after every off-path action `x`, if some type is not eliminated, the belief
puts no mass outside the types that are not eliminated. -/
def D1 (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) : Prop :=
  ∀ x, x ∉ a '' Icc S.lo S.hi → (S.D1Surv a φ x).Nonempty →
    (φ x).support ⊆ S.D1Surv a φ x

end CSetting

end CC.General.Compact
