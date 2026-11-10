import ConformityConcerns.D1Compact.Key

/-!
# The Note after Definition A1

"When the type space is a compact interval, `D1^∞` and ordinary D1 support the same
equilibrium strategies": a strategy `a` is part of an equilibrium satisfying `D1^∞` if and only
if it is part of an equilibrium satisfying ordinary D1.
-/

namespace CC.General.Compact

open MeasureTheory ProbabilityTheory Set

/-- **Note after Definition A1.** On a compact type space, `D1^∞` and ordinary D1 support the
same equilibrium strategies. -/
theorem noteA1 (S : CSetting) (a : ℝ → ℝ) :
    (∃ φ : ℝ → Measure ℝ, S.IsCPBE a φ ∧ S.D1Inf a φ) ↔
      (∃ φ : ℝ → Measure ℝ, S.IsCPBE a φ ∧ S.D1 a φ) := by
  constructor
  · rintro ⟨φ, h, hD⟩
    obtain ⟨φ', h', hD1, -⟩ :=
      CSetting.exists_refined h fun x hx => CSetting.keyCond_of_D1Inf h hD hx
    exact ⟨φ', h', hD1⟩
  · rintro ⟨φ, h, hD⟩
    obtain ⟨φ', h', -, hDI⟩ :=
      CSetting.exists_refined h fun x hx => CSetting.keyCond_of_D1 h hD hx
    exact ⟨φ', h', hDI⟩

end CC.General.Compact
