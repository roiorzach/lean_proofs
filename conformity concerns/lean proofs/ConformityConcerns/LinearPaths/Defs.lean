import ConformityConcerns.Bridge.Defs
import ConformityConcerns.PeriodGame.Instance

/-!
# Lemma 3 along any linear profile: definitions

The primitives are those of `Bridge/Defs.lean`, on the sample space `Ωg` with law `lawG S₁ G`:
`(θ, μ) ~ N(0, Σ₁)`, `(ε_t, ν_t)` i.i.d. `N(0, I)`, `γ_t` i.i.d. `~ G`, all independent. Player
`t`'s private information is `(s_t, v_t) = (θ, μ) + (ε_t, ν_t)` (`priv t`). Lean's date `0` is the
paper's period 1.

* `Hist t` is a public history `h^t = (γ_0, a_0, …, γ_{t-1}, a_{t-1}, γ_t)`, stored as the weights
  `γ_0, …, γ_t` and the actions `a_0, …, a_{t-1}`.
* A (pure) strategy profile `σ : Profile` gives player `t`'s action `σ t h x` at public history `h`
  when his private information is `x = (s_t, v_t)`.
* `hist σ t ω` is the realised (on-path) history and `act σ t ω` the realised action.
* `post S₁ G σ t` is the public posterior of `(θ, μ)` given `h^t`: Mathlib's `condDistrib`, a
  version of the conditional law, determined at almost every on-path history.
* `PeriodLinearEq κ m S γ a`: in the period game at a history where public beliefs about
  `(θ, μ)` are `N(m, S)` and the weight is `γ` (`gameAt m S γ κ`), the period strategy `a` is,
  with some public beliefs `φ` about the preference type, a linear equilibrium, and a signaling
  equilibrium (Social Optimality) if `s̃ = 0`.
* `IsLinearProfile κ S₁ G σ`: at almost every on-path history `h^t` at which public beliefs are
  Gaussian, say `N(m, S)`, the period strategy `σ t h^t` satisfies `PeriodLinearEq κ m S γ_t`.
  The posterior enters only through the antecedent "if it is `N(m, S)`", so the condition does
  not presuppose that beliefs are Gaussian. The public beliefs `φ` may depend on the history in
  any way; in the paper they are part of the equilibrium assessment.
-/

namespace CC.LinearPaths

open MeasureTheory ProbabilityTheory
open CC.Bridge

/-- A public history `h^t = (γ_0, a_0, …, γ_{t-1}, a_{t-1}, γ_t)`: the weights `γ_0, …, γ_t` and
the actions `a_0, …, a_{t-1}`. -/
abbrev Hist (t : ℕ) := (Fin (t + 1) → ℝ) × (Fin t → ℝ)

/-- A pure strategy profile: `σ t h x` is player `t`'s action at public history `h` when his
private information is `x = (s_t, v_t)`. -/
abbrev Profile := ∀ t : ℕ, Hist t → E2 → ℝ

/-- The realised actions `a_0, …, a_{t-1}`. -/
def acts (σ : Profile) : (t : ℕ) → Ωg → (Fin t → ℝ)
  | 0 => fun _ => Fin.elim0
  | t + 1 => fun ω =>
      Fin.snoc (acts σ t ω) (σ t ((fun i : Fin (t + 1) => gam ω i), acts σ t ω) (priv t ω))

/-- The realised public history `h^t`. -/
def hist (σ : Profile) (t : ℕ) (ω : Ωg) : Hist t :=
  ((fun i : Fin (t + 1) => gam ω i), acts σ t ω)

/-- The realised action `a_t` of player `t`. -/
def act (σ : Profile) (t : ℕ) (ω : Ωg) : ℝ := σ t (hist σ t ω) (priv t ω)

/-- The public posterior of `(θ, μ)` given the history `h^t`. -/
noncomputable def post (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G] (σ : Profile)
    (t : ℕ) : Kernel (Hist t) E2 :=
  condDistrib (fun ω : Ωg => ω.1) (hist σ t) (lawG S₁ G)

/-- In the period game at a history with public beliefs `N(m, S)` about `(θ, μ)` and weight `γ`,
the period strategy `a` is (with some public beliefs `φ`) a linear equilibrium, and a signaling
equilibrium if `s̃ = 0`. -/
def PeriodLinearEq (κ : ℝ) (m : E2) (S : M2) (γ : ℝ) (a : E2 → ℝ) : Prop :=
  ∃ φ : Kernel ℝ ℝ, (gameAt m S γ κ).IsLinearEq a φ ∧
    ((gameAt m S γ κ).sens = 0 → (gameAt m S γ κ).IsSignalingEq a φ)

/-- Linearity, and Social Optimality if `s̃(h^t) = 0`, at the history `h` of date `t`: if public
beliefs at `h` are `N(m, S)`, the period strategy `σ t h` satisfies `PeriodLinearEq` in the
period game at `h` (whose weight `γ_t` is the last weight of `h`). -/
def LinearAt (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G] (σ : Profile) (t : ℕ)
    (h : Hist t) : Prop :=
  ∀ (m : E2) (S : M2), S.PosSemidef → post S₁ G σ t h = multivariateGaussian m S →
    PeriodLinearEq κ m S (h.1 (Fin.last t)) (σ t h)

/-- The profile satisfies Linearity, and Social Optimality where `s̃(h^t) = 0`, at almost every
on-path history (at every date). -/
def IsLinearProfile (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]
    (σ : Profile) : Prop :=
  ∀ t, ∀ᵐ ω ∂(lawG S₁ G), LinearAt κ S₁ G σ t (hist σ t ω)

lemma acts_succ (σ : Profile) (t : ℕ) (ω : Ωg) :
    acts σ (t + 1) ω = Fin.snoc (acts σ t ω) (act σ t ω) := rfl

lemma hist_last (σ : Profile) (t : ℕ) (ω : Ωg) : (hist σ t ω).1 (Fin.last t) = gam ω t := rfl

end CC.LinearPaths
