import ConformityConcerns.LearnTheta.ClaimAux.Cond
import Mathlib.Probability.CondVar

/-!
# Tower property and `E(E(θ | m₂)² | m₁) ≤ E(θ² | m₁)` for finite measures
-/

namespace CC.LearnTheta.ClaimAux

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The tower property for a finite measure. -/
theorem condExp_tower_fin [IsFiniteMeasure P] (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ mΩ) (f : Ω → ℝ) :
    P[P[f | m₂] | m₁] =ᵐ[P] P[f | m₁] :=
  condExp_condExp_of_le h12 h2

/-- `E(E(θ | m₂)² | m₁) ≤ E(θ² | m₁)` for `m₁ ≤ m₂`. -/
theorem condExp_sq_condExp_le [IsFiniteMeasure P] (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ mΩ) {θ : Ω → ℝ}
    (hθ : MemLp θ 2 P) :
    P[fun ω => (P[θ | m₂]) ω ^ 2 | m₁] ≤ᵐ[P] P[fun ω => θ ω ^ 2 | m₁] := by
  have h1 : (fun ω => (P[θ | m₂]) ω ^ 2) ≤ᵐ[P] P[fun ω => θ ω ^ 2 | m₂] := by
    have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp h2 hθ
    have hnn : 0 ≤ᵐ[P] condVar m₂ θ P :=
      condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
    filter_upwards [hv, hnn] with ω a b
    rw [a] at b
    have e : (fun ω => θ ω ^ 2) = θ ^ 2 := rfl
    rw [e]
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.zero_apply] at b
    linarith
  have h2' := condExp_mono (m := m₁) (hθ.condExp (m := m₂) one_le_two).integrable_sq
    integrable_condExp h1
  exact h2'.trans_eq (condExp_tower_fin h12 h2 _)

end CC.LearnTheta.ClaimAux
