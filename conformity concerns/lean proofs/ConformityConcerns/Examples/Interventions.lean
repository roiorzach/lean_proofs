import ConformityConcerns.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Example: the hypotheses of Proposition 4 are satisfiable

Independent `θ ~ N(0, σ²_θ)`, `μ ~ N(0, σ²_μ)`, `ε₁, ν₁ ~ N(0,1)`: the four coordinates of
`ℝ⁴` under the product of these laws.
-/

namespace CC.Examples

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The laws of `(θ, μ, ε₁, ν₁)`. -/
noncomputable def prop4Laws (σθ2 σμ2 : ℝ≥0) : Fin 4 → Measure ℝ :=
  ![gaussianReal 0 σθ2, gaussianReal 0 σμ2, gaussianReal 0 1, gaussianReal 0 1]

instance (σθ2 σμ2 : ℝ≥0) (i : Fin 4) : IsProbabilityMeasure (prop4Laws σθ2 σμ2 i) := by
  fin_cases i <;> simp [prop4Laws] <;> infer_instance

lemma prop4_hyp (σθ2 σμ2 : ℝ≥0) :
    let P := Measure.pi (prop4Laws σθ2 σμ2)
    HasLaw (fun ω : Fin 4 → ℝ => ω 0) (gaussianReal 0 σθ2) P ∧
    HasLaw (fun ω : Fin 4 → ℝ => ω 1) (gaussianReal 0 σμ2) P ∧
    HasLaw (fun ω : Fin 4 → ℝ => ω 2) (gaussianReal 0 1) P ∧
    HasLaw (fun ω : Fin 4 → ℝ => ω 3) (gaussianReal 0 1) P ∧
    (∀ i : Fin 4, Measurable (fun ω : Fin 4 → ℝ => ω i)) ∧
    iIndepFun ![fun ω : Fin 4 → ℝ => ω 0, fun ω => ω 1, fun ω => ω 2, fun ω => ω 3] P := by
  intro P
  have hlaw : ∀ i : Fin 4, HasLaw (fun ω : Fin 4 → ℝ => ω i) (prop4Laws σθ2 σμ2 i) P :=
    fun i => ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  refine ⟨hlaw 0, hlaw 1, hlaw 2, hlaw 3, fun i => measurable_pi_apply i, ?_⟩
  have h := iIndepFun_pi (μ := prop4Laws σθ2 σμ2) (X := fun _ : Fin 4 => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)
  convert h using 1
  funext i
  fin_cases i <;> rfl

end CC.Examples
