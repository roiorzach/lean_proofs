import ConformityConcerns.Gaussian.Belief
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Star.Real

/-!
# 2×2 matrix facts used in `Gaussian/Conditioning.lean`

For a positive semidefinite `Σ`: symmetry, the quadratic form is nonnegative, `Σ + I` is
invertible, `K (Σ + I) = Σ` for `K = Σ (Σ + I)⁻¹` (entrywise in row `0`), and `Var(Z | h) > 0`.
-/

namespace CC

open Matrix

variable {S : M2}

lemma cm_symm (hS : S.PosSemidef) : S 1 0 = S 0 1 := by
  have := hS.1.apply 0 1
  simpa using this

lemma cm_quad (hS : S.PosSemidef) (x y : ℝ) :
    0 ≤ S 0 0 * x ^ 2 + 2 * S 0 1 * x * y + S 1 1 * y ^ 2 := by
  have h := hS.dotProduct_mulVec_nonneg ![x, y]
  have hs := cm_symm hS
  simp [dotProduct, mulVec, Fin.sum_univ_two] at h
  rw [hs] at h
  linear_combination h

lemma cm_det_ne (hS : S.PosSemidef) : (S + 1).det ≠ 0 :=
  (PosDef.posSemidef_add hS PosDef.one).det_pos.ne'

lemma cm_gainK_mul (hS : S.PosSemidef) : gainK S * (S + 1) = S := by
  rw [gainK, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (cm_det_ne hS)),
    Matrix.mul_one]

/-- Row `0`, column `0` of `K (Σ + I) = Σ`. -/
lemma cm_id0 (hS : S.PosSemidef) :
    gainK S 0 0 * (S 0 0 + 1) + gainK S 0 1 * S 1 0 = S 0 0 := by
  have h := congrFun (congrFun (cm_gainK_mul hS) 0) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h

/-- Row `0`, column `1` of `K (Σ + I) = Σ`. -/
lemma cm_id1 (hS : S.PosSemidef) :
    gainK S 0 0 * S 0 1 + gainK S 0 1 * (S 1 1 + 1) = S 0 1 := by
  have h := congrFun (congrFun (cm_gainK_mul hS) 0) 1
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h

lemma cm_postVar (S : M2) : postVarθ S = (1 - gainK S 0 0) * S 0 0 - gainK S 0 1 * S 1 0 := by
  simp [postVarθ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, sub_eq_add_neg]

lemma cm_varZ_eq (S : M2) (γ : ℝ) :
    varZ S γ = (γ * gainK S 0 0) * ((S 0 0 + 1) * (γ * gainK S 0 0) + S 0 1 * (1 + γ * gainK S 0 1))
      + (1 + γ * gainK S 0 1) * (S 1 0 * (γ * gainK S 0 0) + (S 1 1 + 1) * (1 + γ * gainK S 0 1)) := by
  simp [varZ, loadA, dotProduct, mulVec, Fin.sum_univ_two, Matrix.one_apply]

lemma cm_varZ_pos (hS : S.PosSemidef) (γ : ℝ) : 0 < varZ S γ := by
  have h0 := cm_id0 hS
  have h1 := cm_id1 hS
  have hs := cm_symm hS
  rw [cm_varZ_eq]
  set A0 := γ * gainK S 0 0 with hA0
  set A1 := 1 + γ * gainK S 0 1 with hA1
  have hq := cm_quad hS A0 A1
  have hA : 0 < A0 ^ 2 + A1 ^ 2 := by
    by_contra hcon
    have ha0 : A0 = 0 := by nlinarith [sq_nonneg A0, sq_nonneg A1]
    have ha1 : A1 = 0 := by nlinarith [sq_nonneg A0, sq_nonneg A1]
    have hγ : γ ≠ 0 := by
      rintro rfl
      simp [hA1] at ha1
    have hK0 : gainK S 0 0 = 0 := by
      rcases mul_eq_zero.1 (hA0 ▸ ha0) with h | h
      · exact absurd h hγ
      · exact h
    set k := gainK S 0 1
    rw [hK0, hs] at h0
    rw [hK0] at h1
    -- `S₀₀ = k S₀₁`, `S₀₁ = k (S₁₁ + 1)`; the quadratic form at `(1, -k)` equals `-k²`.
    have hq' := cm_quad hS 1 (-k)
    have hk : k = 0 := by nlinarith [sq_nonneg k]
    rw [hA1, hk] at ha1
    norm_num at ha1
  rw [hs]
  nlinarith [hq, hA]

end CC
