import ConformityConcerns.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Refinements and central pooling with general losses (Online Appendix, Section A3)

A fixed public history is suppressed. A privately informed player has type `v ∈ ℝ` with
distribution `F` (everywhere-positive continuous density), chooses an action `x ∈ ℝ`, and is
evaluated according to a *compactified* posterior `φ x`, a Borel probability measure on the
extended reals `EReal = [-∞, +∞]`. Utility is `-g(x - v) - ∫ ℓ̄ dφ(x)`, where `ℓ̄` is the
conformity loss `ℓ` on finite types and `+∞` at `±∞`.

The paper writes the conformity loss as `f(b - μ)` with `f` even, strictly convex, `C²`,
`f 0 = 0`. We allow a general conformity loss `ℓ` that is `C²`, strictly convex and minimised
(with value `0`) at the norm `μ`; `ℓ b = f (b - μ)` is the paper's case (see
`Setting.ofEven`), and the same framework covers the conformity loss `κ (m - min m)` of
Proposition A5. We work with losses in `ℝ≥0∞` (payoff = `-loss`), so that an infinite
conformity loss (positive mass on `±∞`) is the payoff `-∞`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- Standing assumptions on the adaptation loss `g`: `C²`, even, strictly convex, `g 0 = 0`. -/
structure AdaptLoss (g : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 2 g
  even : ∀ z, g (-z) = g z
  strictConvex : StrictConvexOn ℝ univ g
  zero : g 0 = 0

/-- Standing assumptions on a conformity loss `ℓ` (the loss from being perceived as type `b`)
with norm `μ`: `C²`, strictly convex, minimised at `μ` with `ℓ μ = 0`. -/
structure ConfLoss (ℓ : ℝ → ℝ) (μ : ℝ) : Prop where
  smooth : ContDiff ℝ 2 ℓ
  strictConvex : StrictConvexOn ℝ univ ℓ
  zero : ℓ μ = 0
  isMin : ∀ b, ℓ μ ≤ ℓ b

/-- A type distribution with an everywhere-positive continuous density. -/
structure TypeDist (F : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure F
  density : ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ x, 0 < ψ x) ∧
    F = volume.withDensity (fun x => ENNReal.ofReal (ψ x))

/-- The single-period environment of Section A3 (with a general conformity loss). -/
structure Setting where
  g : ℝ → ℝ
  ℓ : ℝ → ℝ
  μ : ℝ
  F : Measure ℝ
  hg : AdaptLoss g
  hℓ : ConfLoss ℓ μ
  hF : TypeDist F
  /-- `M_f = ∫ ℓ dF < ∞`. -/
  integrable : Integrable ℓ F
  /-- `0 < M_f`. -/
  Mpos : 0 < ∫ v, ℓ v ∂F

namespace Setting

variable (S : Setting)

/-- Extended conformity loss `ℓ̄` on `EReal`: `ℓ` at finite types, `+∞` at `±∞`. -/
noncomputable def ℓbar (b : EReal) : ℝ≥0∞ :=
  if b = ⊤ ∨ b = ⊥ then ∞ else ENNReal.ofReal (S.ℓ b.toReal)

/-- Conformity loss `∫ ℓ̄ dφ(x)` after action `x` under compactified beliefs `φ`. -/
noncomputable def confLoss (φ : ℝ → Measure EReal) (x : ℝ) : ℝ≥0∞ := ∫⁻ b, S.ℓbar b ∂(φ x)

/-- Total loss of type `v` choosing `x` (the payoff is `-loss`). -/
noncomputable def loss (φ : ℝ → Measure EReal) (x v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (S.g (x - v)) + S.confLoss φ x

/-- A pure compactified perfect Bayesian equilibrium `(a, φ)`: (i) every finite type maximises;
(ii) at every on-path action `x`, beliefs put probability one on `{v : a v = x}`, are given by
Bayes' rule when this set has positive `F`-probability, and equal `δ_v` when it is `{v}`;
and on-path conformity payoffs are finite. -/
structure IsCPBE (a : ℝ → ℝ) (φ : ℝ → Measure EReal) : Prop where
  meas : Measurable a
  prob : ∀ x, IsProbabilityMeasure (φ x)
  optimal : ∀ v x, S.loss φ (a v) v ≤ S.loss φ x v
  onPath_supp : ∀ v, φ (a v) ((fun r : ℝ => (r : EReal)) '' (a ⁻¹' {a v})) = 1
  onPath_bayes : ∀ v, 0 < S.F (a ⁻¹' {a v}) →
    φ (a v) = (S.F[|a ⁻¹' {a v}]).map (fun r : ℝ => (r : EReal))
  onPath_dirac : ∀ v, a ⁻¹' {a v} = {v} → φ (a v) = Measure.dirac (v : EReal)
  finite : ∀ v, S.confLoss φ (a v) < ∞

/-- Equilibrium payoff `U(v)` (finite on path). -/
noncomputable def U (a : ℝ → ℝ) (φ : ℝ → Measure EReal) (v : ℝ) : ℝ :=
  -(S.g (a v - v) + (S.confLoss φ (a v)).toReal)

/-- Indifference index `I_x(v) = U(v) + g(x - v)`. -/
noncomputable def indiff (a : ℝ → ℝ) (φ : ℝ → Measure EReal) (x v : ℝ) : ℝ :=
  S.U a φ v + S.g (x - v)

/-- Clipped index `J_x(v) = min {I_x(v), 0}`. -/
noncomputable def clipped (a : ℝ → ℝ) (φ : ℝ → Measure EReal) (x v : ℝ) : ℝ :=
  min (S.indiff a φ x v) 0

/-- Extension `J̄_x` of the clipped index to `EReal` by `liminf` at `±∞`. -/
noncomputable def extIndex (a : ℝ → ℝ) (φ : ℝ → Measure EReal) (x : ℝ) (z : EReal) : EReal :=
  if z = ⊤ then liminf (fun v : ℝ => ((S.clipped a φ x v : ℝ) : EReal)) atTop
  else if z = ⊥ then liminf (fun v : ℝ => ((S.clipped a φ x v : ℝ) : EReal)) atBot
  else ((S.clipped a φ x z.toReal : ℝ) : EReal)

/-- The `D1^∞` survivor set `S^∞(x) = argmin_{z ∈ [-∞,∞]} J̄_x(z)`. -/
def survivors (a : ℝ → ℝ) (φ : ℝ → Measure EReal) (x : ℝ) : Set EReal :=
  {z | ∀ z', S.extIndex a φ x z ≤ S.extIndex a φ x z'}

/-- The `D1^∞` refinement: after every off-path action `x`, `supp φ(x) ⊆ S^∞(x)`. -/
def D1Inf (a : ℝ → ℝ) (φ : ℝ → Measure EReal) : Prop :=
  ∀ x, x ∉ range a → (φ x).support ⊆ S.survivors a φ x

/-- Central pooling with cutoffs `vlo ≤ μ ≤ vhi` and pool action `c`: `a = c` on `(vlo, vhi)`,
no type outside `[vlo, vhi]` chooses `c`, `T(c)` is the only nondegenerate pooling set, and `a`
is strictly increasing on each component of `ℝ \ [vlo, vhi]`. (A fully separating equilibrium
satisfies this with `vlo = vhi = μ`, `c = a μ`.) -/
def IsCentralPoolingWith (a : ℝ → ℝ) (vlo vhi : EReal) (c : ℝ) : Prop :=
  vlo ≤ (S.μ : EReal) ∧ (S.μ : EReal) ≤ vhi ∧
  (∀ v : ℝ, vlo < (v : EReal) → (v : EReal) < vhi → a v = c) ∧
  (∀ v : ℝ, ((v : EReal) < vlo ∨ vhi < (v : EReal)) → a v ≠ c) ∧
  (∀ x : ℝ, (a ⁻¹' {x}).Nontrivial → x = c) ∧
  StrictMonoOn a {v : ℝ | (v : EReal) < vlo} ∧ StrictMonoOn a {v : ℝ | vhi < (v : EReal)}

/-- `a` is a central pooling strategy. -/
def IsCentralPooling (a : ℝ → ℝ) : Prop := ∃ vlo vhi : EReal, ∃ c : ℝ, S.IsCentralPoolingWith a vlo vhi c

/-- On each separating tail `a` is `C¹` with `a'(v) = ℓ'(v)/g'(v - a(v)) > 0`
(the paper's `a'(v) = f'(v - μ)/g'(v - a(v))`). -/
def TailODE (a : ℝ → ℝ) (vlo vhi : EReal) : Prop :=
  ContDiffOn ℝ 1 a {v : ℝ | vhi < (v : EReal)} ∧ ContDiffOn ℝ 1 a {v : ℝ | (v : EReal) < vlo} ∧
  ∀ v : ℝ, ((v : EReal) < vlo ∨ vhi < (v : EReal)) →
    0 < deriv S.ℓ v / deriv S.g (v - a v) ∧ HasDerivAt a (deriv S.ℓ v / deriv S.g (v - a v)) v

/-- The fully pooling assessment: pool on `c`; on-path belief `F`; after `x > c` the belief is
`δ_{+∞}` and after `x < c` it is `δ_{-∞}`. -/
noncomputable def poolBelief (c x : ℝ) : Measure EReal :=
  if x = c then S.F.map (fun r : ℝ => (r : EReal))
  else if c < x then Measure.dirac ⊤ else Measure.dirac ⊥

end Setting

end CC.General
