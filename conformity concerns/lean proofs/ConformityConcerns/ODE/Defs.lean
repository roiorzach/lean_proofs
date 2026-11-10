import ConformityConcerns.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Tail solutions of the differential equation (Online Appendix, Section A4)

`IsRightTailSol Ψ Γ c d a` is the paper's "right-tail solution on `[d, ∞)`" of
`a'(v) = Ψ(v - c) / Γ(v - a(v))`: `a` is continuous on `[d, ∞)`, `C¹` on `(d, ∞)`,
satisfies `a v < v` for `v > d`, and solves the equation on `(d, ∞)`.

`IsLeftTailSol Ψ Γ c d a` is the paper's "left-tail solution on `(-∞, d]`" of
`a'(v) = Ψ(c - v) / Γ(a(v) - v)`.

`TailData Ψ Γ` collects the standing hypotheses of Lemma A3: `Ψ, Γ : (0,∞) → (0,∞)` are
increasing and `C¹`.  (Functions are total on `ℝ`; only their values on `(0, ∞)` matter.)
-/

namespace CC.ODE

open Set Filter Topology

/-- Standing hypotheses of Lemma A3 on `Ψ` and `Γ`: increasing, `C¹` and positive on `(0,∞)`. -/
structure TailData (Ψ Γ : ℝ → ℝ) : Prop where
  Ψ_mono : MonotoneOn Ψ (Ioi 0)
  Γ_mono : MonotoneOn Γ (Ioi 0)
  Ψ_C1 : ContDiffOn ℝ 1 Ψ (Ioi 0)
  Γ_C1 : ContDiffOn ℝ 1 Γ (Ioi 0)
  Ψ_pos : ∀ x, 0 < x → 0 < Ψ x
  Γ_pos : ∀ x, 0 < x → 0 < Γ x

/-- A right-tail solution on `[d, ∞)` of `a'(v) = Ψ(v - c)/Γ(v - a(v))`
(`a ∈ C([d,∞)) ∩ C¹((d,∞))`, `a v < v` for `v > d`, equation on `(d, ∞)`). -/
def IsRightTailSol (Ψ Γ : ℝ → ℝ) (c d : ℝ) (a : ℝ → ℝ) : Prop :=
  ContinuousOn a (Ici d) ∧ ContDiffOn ℝ 1 a (Ioi d) ∧ (∀ v, d < v → a v < v) ∧
    ∀ v, d < v → HasDerivAt a (Ψ (v - c) / Γ (v - a v)) v

/-- A left-tail solution on `(-∞, d]` of `a'(v) = Ψ(c - v)/Γ(a(v) - v)`
(`a ∈ C((-∞,d]) ∩ C¹((-∞,d))`, `a v > v` for `v < d`, equation on `(-∞, d)`). -/
def IsLeftTailSol (Ψ Γ : ℝ → ℝ) (c d : ℝ) (a : ℝ → ℝ) : Prop :=
  ContinuousOn a (Iic d) ∧ ContDiffOn ℝ 1 a (Iio d) ∧ (∀ v, v < d → v < a v) ∧
    ∀ v, v < d → HasDerivAt a (Ψ (c - v) / Γ (a v - v)) v

end CC.ODE
