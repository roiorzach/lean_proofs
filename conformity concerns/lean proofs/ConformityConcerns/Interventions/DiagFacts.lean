import ConformityConcerns.Interventions.Sensitivity
import ConformityConcerns.Gaussian.BeliefLemmas
import Mathlib.Tactic.LinearCombination

/-!
# Small 2×2 matrix facts used in the interventions and corollaries files

Positive (semi)definiteness of 2×2 matrices in coordinates, and the public-signal updates
`observeTheta`, `observeMu`, `kalman` at diagonal covariances.
-/

namespace CC

open Matrix

lemma quadForm_two (S : M2) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (S *ᵥ x) = x 0 * (S 0 0 * x 0 + S 0 1 * x 1) + x 1 * (S 1 0 * x 0 + S 1 1 * x 1) := by
  simp [dotProduct, mulVec, Fin.sum_univ_two]

lemma quad_nonneg_two {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c) (x y : ℝ) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h
    have : b = 0 := by nlinarith [sq_nonneg b]
    subst this; nlinarith [sq_nonneg y]
  · have key : a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) =
        (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by ring
    have : 0 ≤ a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (a * x + b * y), sq_nonneg y]
    by_contra hneg; push Not at hneg
    nlinarith [mul_pos h (neg_pos.2 hneg)]

/-- A symmetric 2×2 matrix with nonnegative diagonal and nonnegative determinant is PSD. -/
lemma psd_of_entries (S : M2) (hs : S 1 0 = S 0 1) (h0 : 0 ≤ S 0 0) (h1 : 0 ≤ S 1 1)
    (hd : S 0 1 ^ 2 ≤ S 0 0 * S 1 1) : S.PosSemidef := by
  have hH : S.IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hs]
  refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
  rw [quadForm_two, hs]
  have := quad_nonneg_two h0 h1 hd (x 0) (x 1)
  nlinarith [this]

/-- Coordinates of a positive definite 2×2 matrix. -/
lemma entries_of_posDef {S : M2} (h : S.PosDef) :
    S 1 0 = S 0 1 ∧ 0 < S 0 0 ∧ 0 < S 1 1 ∧ S 0 1 ^ 2 < S 0 0 * S 1 1 := by
  have hs : S 1 0 = S 0 1 := by
    have := congrFun (congrFun h.isHermitian 0) 1
    simpa using this
  have hq : ∀ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) →
      0 < S 0 0 * x ^ 2 + 2 * S 0 1 * x * y + S 1 1 * y ^ 2 := by
    intro x y hxy
    have hne : (![x, y] : Fin 2 → ℝ) ≠ 0 := by
      intro h0; rcases hxy with hx | hy
      · exact hx (by simpa using congrFun h0 0)
      · exact hy (by simpa using congrFun h0 1)
    have := h.dotProduct_mulVec_pos hne
    rw [quadForm_two] at this
    simp [hs] at this; nlinarith [this]
  have h0 : 0 < S 0 0 := by simpa using hq 1 0 (Or.inl one_ne_zero)
  have h1 : 0 < S 1 1 := by simpa using hq 0 1 (Or.inr one_ne_zero)
  refine ⟨hs, h0, h1, ?_⟩
  have e2 := hq (S 0 1) (- S 0 0) (Or.inr (by simpa using h0.ne'))
  nlinarith

lemma psd_diag (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (!![x, 0; 0, y] : M2).PosSemidef :=
  psd_of_entries _ (by simp) (by simpa using hx) (by simpa using hy) (by simp; positivity)

lemma observeTheta_apply (S : M2) (n : ℝ) (i j : Fin 2) :
    observeTheta S n i j = S i j - (S 0 0 + n)⁻¹ * (S i 0 * S j 0) := by
  simp [observeTheta, vecMulVec_apply, mulVec, dotProduct, Fin.sum_univ_two]

lemma observeMu_apply (S : M2) (n : ℝ) (i j : Fin 2) :
    observeMu S n i j = S i j - (S 1 1 + n)⁻¹ * (S i 1 * S j 1) := by
  simp [observeMu, vecMulVec_apply, mulVec, dotProduct, Fin.sum_univ_two]

lemma observeTheta_diag (x y : ℝ) (hx : 0 ≤ x) :
    observeTheta !![x, 0; 0, y] 1 = !![x / (1 + x), 0; 0, y] := by
  have hx' : x + 1 ≠ 0 := by positivity
  ext i j; fin_cases i <;> fin_cases j <;> simp [observeTheta_apply]
  field_simp; ring

lemma observeMu_diag (x y : ℝ) (hy : 0 ≤ y) :
    observeMu !![x, 0; 0, y] 1 = !![x, 0; 0, y / (1 + y)] := by
  have hy' : y + 1 ≠ 0 := by positivity
  ext i j; fin_cases i <;> fin_cases j <;> simp [observeMu_apply]
  field_simp; ring

/-- An individual-oriented public signal keeps the posterior PSD and the variance of `μ`
positive. -/
lemma observeTheta_props {S : M2} (hS : S.PosDef) {n : ℝ} (hn : 0 ≤ n) :
    (observeTheta S n).PosSemidef ∧ 0 < observeTheta S n 1 1 := by
  obtain ⟨hs, h0, h1, hd⟩ := entries_of_posDef hS
  have hp : 0 < S 0 0 + n := by linarith
  have e00 : observeTheta S n 0 0 = S 0 0 * n / (S 0 0 + n) := by
    rw [observeTheta_apply]; field_simp; ring
  have e01 : observeTheta S n 0 1 = S 0 1 * n / (S 0 0 + n) := by
    rw [observeTheta_apply, hs]; field_simp; ring
  have e10 : observeTheta S n 1 0 = S 0 1 * n / (S 0 0 + n) := by
    rw [observeTheta_apply, hs]; field_simp; ring
  have e11 : observeTheta S n 1 1 = (S 0 0 * S 1 1 - S 0 1 ^ 2 + S 1 1 * n) / (S 0 0 + n) := by
    rw [observeTheta_apply, hs]; field_simp; ring
  have hpos : 0 < observeTheta S n 1 1 := by
    rw [e11]; apply div_pos _ hp; nlinarith [mul_nonneg h1.le hn]
  refine ⟨psd_of_entries _ (by rw [e01, e10]) (by rw [e00]; positivity) hpos.le ?_, hpos⟩
  rw [e00, e01, e11, div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ n * (S 0 0 * S 1 1 - S 0 1 ^ 2) := mul_nonneg hn (by linarith)
  have key : S 0 0 * n * (S 0 0 * S 1 1 - S 0 1 ^ 2 + S 1 1 * n) * (S 0 0 + n) ^ 2 -
      (S 0 1 * n) ^ 2 * ((S 0 0 + n) * (S 0 0 + n)) =
      n * (S 0 0 * S 1 1 - S 0 1 ^ 2) * (S 0 0 + n) ^ 3 := by ring
  nlinarith [mul_nonneg this (pow_pos hp 3).le]

/-- A peer-oriented public signal keeps the posterior PSD and the variance of `θ` positive. -/
lemma observeMu_props {S : M2} (hS : S.PosDef) {n : ℝ} (hn : 0 ≤ n) :
    (observeMu S n).PosSemidef ∧ 0 < observeMu S n 0 0 := by
  obtain ⟨hs, h0, h1, hd⟩ := entries_of_posDef hS
  have hp : 0 < S 1 1 + n := by linarith
  have e11 : observeMu S n 1 1 = S 1 1 * n / (S 1 1 + n) := by
    rw [observeMu_apply]; field_simp; ring
  have e01 : observeMu S n 0 1 = S 0 1 * n / (S 1 1 + n) := by
    rw [observeMu_apply]; field_simp; ring
  have e10 : observeMu S n 1 0 = S 0 1 * n / (S 1 1 + n) := by
    rw [observeMu_apply, hs]; field_simp; ring
  have e00 : observeMu S n 0 0 = (S 0 0 * S 1 1 - S 0 1 ^ 2 + S 0 0 * n) / (S 1 1 + n) := by
    rw [observeMu_apply]; field_simp; ring
  have hpos : 0 < observeMu S n 0 0 := by
    rw [e00]; apply div_pos _ hp; nlinarith [mul_nonneg h0.le hn]
  refine ⟨psd_of_entries _ (by rw [e01, e10]) hpos.le (by rw [e11]; positivity) ?_, hpos⟩
  rw [e00, e01, e11, div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ n * (S 0 0 * S 1 1 - S 0 1 ^ 2) := mul_nonneg hn (by linarith)
  have key : (S 0 0 * S 1 1 - S 0 1 ^ 2 + S 0 0 * n) * (S 1 1 * n) * (S 1 1 + n) ^ 2 -
      (S 0 1 * n) ^ 2 * ((S 1 1 + n) * (S 1 1 + n)) =
      n * (S 0 0 * S 1 1 - S 0 1 ^ 2) * (S 1 1 + n) ^ 3 := by ring
  nlinarith [mul_nonneg this (pow_pos hp 3).le]

/-- A zero variance forces a zero covariance. -/
lemma off_zero_of_left {S : M2} (hS : S.PosSemidef) (h : S 0 0 = 0) : S 0 1 = 0 := by
  obtain ⟨-, -, -, hd⟩ := (psd_iff S).1 hS
  rw [h, zero_mul] at hd
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm hd (sq_nonneg _))

lemma off_zero_of_right {S : M2} (hS : S.PosSemidef) (h : S 1 1 = 0) : S 0 1 = 0 := by
  obtain ⟨-, -, -, hd⟩ := (psd_iff S).1 hS
  rw [h, mul_zero] at hd
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm hd (sq_nonneg _))

end CC
