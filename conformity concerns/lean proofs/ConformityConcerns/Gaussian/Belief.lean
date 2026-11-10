import ConformityConcerns.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Gaussian public beliefs (Section 4.1 and the proofs of Appendix A)

Public beliefs about `(θ, μ)` at a history are Gaussian with covariance `Σ` (index `0` is `θ`,
index `1` is `μ`). Given `h^t`, the private information is `(s, v) = (θ, μ) + (ε, ν)` with
`(ε, ν)` standard normal, so `(s, v) | h ~ N(m, Σ + I)`, and by Gaussian conditioning
`E(θ | h, s, v) = θ(h) + K₀₀ (s - θ(h)) + K₀₁ (v - μ(h))` with gain `K = Σ (Σ + I)⁻¹`.
The payoff-relevant statistic is `Z = γ E(θ | h, s, v) + v`, i.e. up to a constant
`Z = Aᵀ (s, v)` with loading `A = (γ K₀₀, 1 + γ K₀₁)`.

* `Vt S = Var(v | h) = 1 + Σ₁₁`, `Ct S = Cov(v, θ | h) = Σ₀₁`,
  `Ht S = Var(E(θ | h, s, v) | h) = (K (Σ + I) Kᵀ)₀₀`,
* `varZ S γ = Var(Z | h) = Aᵀ (Σ + I) A`,
* `sens S γ = (V + γ C)/(V + 2γ C + γ² H)` is the sensitivity `s̃(h)` (the formula in the proof of Proposition 2),
* `postVarθ S = Var(θ | h, s, v) = ((I - K) Σ)₀₀`,
* `kalman S γ = Σ - (Σ A)(Σ A)ᵀ / Var(Z | h)` is the posterior covariance after a revealing
  period (observing `Z`).
-/

namespace CC

open Matrix

/-- 2×2 real matrices (covariances of `(θ, μ)`). -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

/-- Gain matrix `K = Σ (Σ + I)⁻¹`. -/
noncomputable def gainK (S : M2) : M2 := S * (S + 1)⁻¹

/-- Loading of `Z` on `(s, v)`: `A = (γ K₀₀, 1 + γ K₀₁)`. -/
noncomputable def loadA (S : M2) (γ : ℝ) : Fin 2 → ℝ := ![γ * gainK S 0 0, 1 + γ * gainK S 0 1]

/-- `V_t = Var(v_t | h^t) = 1 + σ²_{μ,t}`. -/
def Vt (S : M2) : ℝ := 1 + S 1 1

/-- `C_t = Cov(v_t, θ | h^t) = (Σ_t)₀₁`. -/
def Ct (S : M2) : ℝ := S 0 1

/-- `H_t = Var(E(θ | h^t, s_t, v_t) | h^t) = (K (Σ + I) Kᵀ)₀₀`. -/
noncomputable def Ht (S : M2) : ℝ := (gainK S * (S + 1) * (gainK S)ᵀ) 0 0

/-- `Var(Z_t | h^t) = Aᵀ (Σ + I) A`. -/
noncomputable def varZ (S : M2) (γ : ℝ) : ℝ := loadA S γ ⬝ᵥ ((S + 1) *ᵥ loadA S γ)

/-- The sensitivity `s̃(h^t) = (V + γ C)/(V + 2 γ C + γ² H)`. -/
noncomputable def sens (S : M2) (γ : ℝ) : ℝ :=
  (Vt S + γ * Ct S) / (Vt S + 2 * γ * Ct S + γ ^ 2 * Ht S)

/-- `Var(θ | h, s, v) = ((I - K) Σ)₀₀`. -/
noncomputable def postVarθ (S : M2) : ℝ := ((1 - gainK S) * S) 0 0

/-- Posterior covariance after observing `Z` (a revealing period). -/
noncomputable def kalman (S : M2) (γ : ℝ) : M2 :=
  S - (varZ S γ)⁻¹ • vecMulVec (S *ᵥ loadA S γ) (S *ᵥ loadA S γ)

/-- Posterior covariance after a public signal `θ + η` with `Var η = n ≥ 0`
(an individual-oriented intervention; `n = 0` reveals `θ`). -/
noncomputable def observeTheta (S : M2) (n : ℝ) : M2 :=
  S - (S 0 0 + n)⁻¹ • vecMulVec (S *ᵥ ![1, 0]) (S *ᵥ ![1, 0])

/-- Posterior covariance after a public signal `μ + η` with `Var η = n ≥ 0`
(a peer-oriented intervention; `n = 0` reveals `μ`). -/
noncomputable def observeMu (S : M2) (n : ℝ) : M2 :=
  S - (S 1 1 + n)⁻¹ • vecMulVec (S *ᵥ ![0, 1]) (S *ᵥ ![0, 1])

/-- The revealing criterion of Corollary 1: `|s̃| ≤ √(κck/κ)`, i.e. `κ s̃² ≤ κck`. -/
def revCrit (κ : ℝ) (S : M2) (γ : ℝ) : Prop := κ * sens S γ ^ 2 ≤ κck

end CC
