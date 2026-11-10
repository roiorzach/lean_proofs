import ConformityConcerns.Dynamics.Defs
import ConformityConcerns.Dynamics.Lemmas

/-!
# Lemma A1 (Information Accounting)

The proof uses neither `γ_t ≤ 1` nor a constant `κ`, so the lemma is stated for arbitrary
sequences `κ t` and `γ t`.
-/

namespace CC

open Matrix Filter Topology Set

/-- **Lemma A1.** With `Λ_t = Σ_t⁻¹`: `Λ_{t+1} = Λ_t` at pooling dates; at revealing dates
`Λ_{t+1} = Λ_t + A Aᵀ/‖A‖²`, the increment is a rank-one orthogonal projection, so
`tr Λ_{t+1} = tr Λ_t + 1`; hence `tr Λ_t = tr Λ_1 + N_t` and
`min {σ²_θ,t, σ²_μ,t} ≥ 1/(tr Λ_1 + N_t)`. -/
theorem lemmaA1 (κ γ : ℕ → ℝ) (S₁ : M2) (hS : S₁.PosDef) (t : ℕ) :
    let S := SigmaC κ S₁ γ
    let A := loadA (S t) (γ t)
    let Pr : M2 := (A ⬝ᵥ A)⁻¹ • vecMulVec A A
    (S t).PosDef ∧
    (¬ revCrit (κ t) (S t) (γ t) → (S (t + 1))⁻¹ = (S t)⁻¹) ∧
    (revCrit (κ t) (S t) (γ t) → (S (t + 1))⁻¹ = (S t)⁻¹ + Pr) ∧
    (0 < A ⬝ᵥ A ∧ Prᵀ = Pr ∧ Pr * Pr = Pr ∧ Pr.rank = 1 ∧ Pr.trace = 1) ∧
    ((S t)⁻¹).trace = (S₁⁻¹).trace + revCount κ S₁ γ t ∧
    1 / ((S₁⁻¹).trace + revCount κ S₁ γ t) ≤ min (S t 0 0) (S t 1 1) := by
  dsimp only
  have hpd : ∀ t, (SigmaC κ S₁ γ t).PosDef := SigmaC_pd κ γ S₁ hS
  have hA : ∀ t, 0 < loadA (SigmaC κ S₁ γ t) (γ t) ⬝ᵥ loadA (SigmaC κ S₁ γ t) (γ t) :=
    fun t => loadA_dot_pos (hpd t).posSemidef _
  have htr : ∀ t, ((SigmaC κ S₁ γ t)⁻¹).trace = (S₁⁻¹).trace + revCount κ S₁ γ t := by
    intro t
    induction t with
    | zero => simp [revCount, SigmaC]
    | succ t ih =>
      rw [revCount_succ]
      split_ifs with h
      · rw [SigmaC_succ_rev κ γ S₁ h, kalman_inv (hpd t), trace_add, ih,
          (proj_props _ (hA t)).2.2.2]
        push_cast; ring
      · rw [SigmaC_succ_pool κ γ S₁ h, ih]; simp
  refine ⟨hpd t, fun h => by rw [SigmaC_succ_pool κ γ S₁ h],
    fun h => by rw [SigmaC_succ_rev κ γ S₁ h, kalman_inv (hpd t)],
    ⟨hA t, proj_props _ (hA t)⟩, htr t, ?_⟩
  rw [← htr t]
  exact inv_trace_bound (hpd t)

end CC
