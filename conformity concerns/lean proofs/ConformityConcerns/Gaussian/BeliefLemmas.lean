import ConformityConcerns.Gaussian.Belief
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Algebra of the 2×2 Gaussian belief update

Explicit formulas for the gain `K = Σ(Σ+I)⁻¹`, the loading `A`, `Var(Z)`, the sensitivity and the
Kalman update in terms of the entries `a = Σ₀₀`, `b = Σ₀₁ = Σ₁₀`, `c = Σ₁₁` of a symmetric `Σ`,
and the positivity facts used in the proofs of Lemma A1, Proposition 2 and Propositions A1, A2.
-/

namespace CC

open Matrix

/-! ### 2×2 positive (semi)definiteness in coordinates -/

/-- Coordinate form of positive semidefiniteness (entries `0 0`, `0 1`, `1 1`). -/
def PSDE (S : M2) : Prop := 0 ≤ S 0 0 ∧ 0 ≤ S 1 1 ∧ S 0 1 ^ 2 ≤ S 0 0 * S 1 1

lemma quad_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c) (x y : ℝ) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h
    have : b = 0 := by nlinarith [sq_nonneg b]
    subst this; nlinarith [sq_nonneg y]
  · have key : a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) = (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by ring
    have : 0 ≤ a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (a * x + b * y), sq_nonneg y]
    by_contra hneg; push Not at hneg
    nlinarith [mul_pos h (neg_pos.2 hneg)]

lemma quadForm_fin_two (S : M2) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (S *ᵥ x) = x 0 * (S 0 0 * x 0 + S 0 1 * x 1) + x 1 * (S 1 0 * x 0 + S 1 1 * x 1) := by
  simp [dotProduct, mulVec, Fin.sum_univ_two]

lemma isHermitian_of_sym {S : M2} (hs : S 1 0 = S 0 1) : S.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hs]

lemma psd_iff (S : M2) : S.PosSemidef ↔ S 1 0 = S 0 1 ∧ PSDE S := by
  constructor
  · intro h
    have hs : S 1 0 = S 0 1 := by
      have := congrFun (congrFun h.isHermitian 0) 1
      simpa using this
    have q := h.dotProduct_mulVec_nonneg
    have hq : ∀ x y : ℝ, 0 ≤ S 0 0 * x ^ 2 + 2 * S 0 1 * x * y + S 1 1 * y ^ 2 := by
      intro x y
      have := q ![x, y]
      rw [quadForm_fin_two] at this
      simp [hs] at this; nlinarith [this]
    have h0 : 0 ≤ S 0 0 := by simpa using hq 1 0
    have h1 : 0 ≤ S 1 1 := by simpa using hq 0 1
    refine ⟨hs, h0, h1, ?_⟩
    have e1 := hq (S 1 1) (- S 0 1)
    have e2 := hq (S 0 1) (- S 0 0)
    have e3 := hq 1 (- S 0 1)
    rcases eq_or_lt_of_le (add_nonneg h0 h1) with hz | hz
    · have ha : S 0 0 = 0 := by linarith
      have hc : S 1 1 = 0 := by linarith
      rw [ha, hc] at e3 ⊢; nlinarith
    · have hm : 0 ≤ (S 0 0 + S 1 1) * (S 0 0 * S 1 1 - S 0 1 ^ 2) := by nlinarith
      by_contra hneg; push Not at hneg
      nlinarith [mul_pos hz (by linarith : 0 < S 0 1 ^ 2 - S 0 0 * S 1 1)]
  · rintro ⟨hs, h0, h1, hb⟩
    refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_sym hs) fun x => ?_
    rw [quadForm_fin_two, hs]
    have := quad_nonneg h0 h1 hb (x 0) (x 1)
    nlinarith [this]

lemma pd_iff (S : M2) : S.PosDef ↔ S 1 0 = S 0 1 ∧ 0 < S 0 0 ∧ S 0 1 ^ 2 < S 0 0 * S 1 1 := by
  constructor
  · intro h
    have hs : S 1 0 = S 0 1 := by
      have := congrFun (congrFun h.isHermitian 0) 1
      simpa using this
    have hq : ∀ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) → 0 < S 0 0 * x ^ 2 + 2 * S 0 1 * x * y + S 1 1 * y ^ 2 := by
      intro x y hxy
      have hne : (![x, y] : Fin 2 → ℝ) ≠ 0 := by
        intro h0; rcases hxy with hx | hy
        · exact hx (by simpa using congrFun h0 0)
        · exact hy (by simpa using congrFun h0 1)
      have := h.dotProduct_mulVec_pos hne
      rw [quadForm_fin_two] at this
      simp [hs] at this; nlinarith [this]
    have h0 : 0 < S 0 0 := by simpa using hq 1 0 (Or.inl one_ne_zero)
    refine ⟨hs, h0, ?_⟩
    have e2 := hq (S 0 1) (- S 0 0) (Or.inr (by simpa using h0.ne'))
    nlinarith
  · rintro ⟨hs, h0, hb⟩
    refine PosDef.of_dotProduct_mulVec_pos (isHermitian_of_sym hs) fun x hx => ?_
    rw [quadForm_fin_two, hs]
    have key : S 0 0 * (x 0 * (S 0 0 * x 0 + S 0 1 * x 1) + x 1 * (S 0 1 * x 0 + S 1 1 * x 1)) =
        (S 0 0 * x 0 + S 0 1 * x 1) ^ 2 + (S 0 0 * S 1 1 - S 0 1 ^ 2) * x 1 ^ 2 := by ring
    have hpos : 0 < S 0 0 * (x 0 * (S 0 0 * x 0 + S 0 1 * x 1) + x 1 * (S 0 1 * x 0 + S 1 1 * x 1)) := by
      rw [key]
      by_cases h1 : x 1 = 0
      · have h0' : x 0 ≠ 0 := by
          intro h0'; apply hx; ext i; fin_cases i <;> simp [h0', h1]
        rw [h1]; have : 0 < (S 0 0 * x 0) ^ 2 := by positivity
        nlinarith
      · have : 0 < x 1 ^ 2 := by positivity
        nlinarith [sq_nonneg (S 0 0 * x 0 + S 0 1 * x 1)]
    by_contra hneg; push Not at hneg
    nlinarith [mul_nonneg h0.le (by linarith : (0:ℝ) ≤ -(x 0 * (S 0 0 * x 0 + S 0 1 * x 1) + x 1 * (S 0 1 * x 0 + S 1 1 * x 1)))]

/-! ### Explicit formulas -/

/-- Inverse of a symmetric 2×2 matrix with nonzero determinant. -/
lemma inv_sym_eq (M : M2) (hs : M 1 0 = M 0 1) (hd : M 0 0 * M 1 1 - M 0 1 ^ 2 ≠ 0) :
    M⁻¹ = !![M 1 1 / (M 0 0 * M 1 1 - M 0 1 ^ 2), - M 0 1 / (M 0 0 * M 1 1 - M 0 1 ^ 2);
      - M 0 1 / (M 0 0 * M 1 1 - M 0 1 ^ 2), M 0 0 / (M 0 0 * M 1 1 - M 0 1 ^ 2)] := by
  apply Matrix.inv_eq_right_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hs] <;> field_simp <;> ring

section Explicit

variable (S : M2)

/-- `det (Σ + I)` for symmetric `Σ`. -/
noncomputable def dE : ℝ := (1 + S 0 0) * (1 + S 1 1) - S 0 1 ^ 2
/-- `K₀₀`. -/
noncomputable def k00E : ℝ := (S 0 0 * (1 + S 1 1) - S 0 1 ^ 2) / dE S
/-- `K₀₁ = K₁₀`. -/
noncomputable def k01E : ℝ := S 0 1 / dE S
/-- `K₁₁`. -/
noncomputable def k11E : ℝ := (S 1 1 * (1 + S 0 0) - S 0 1 ^ 2) / dE S
/-- `A₀ = γ K₀₀`. -/
noncomputable def A0E (γ : ℝ) : ℝ := γ * k00E S
/-- `A₁ = 1 + γ K₀₁`. -/
noncomputable def A1E (γ : ℝ) : ℝ := 1 + γ * k01E S
/-- `Var(Z) = Aᵀ (Σ + I) A`. -/
noncomputable def vZE (γ : ℝ) : ℝ :=
  (1 + S 0 0) * A0E S γ ^ 2 + 2 * S 0 1 * A0E S γ * A1E S γ + (1 + S 1 1) * A1E S γ ^ 2
/-- `(Σ A)₀`. -/
noncomputable def F0E (γ : ℝ) : ℝ := S 0 0 * A0E S γ + S 0 1 * A1E S γ
/-- `(Σ A)₁`. -/
noncomputable def F1E (γ : ℝ) : ℝ := S 0 1 * A0E S γ + S 1 1 * A1E S γ
/-- `H = (K (Σ + I) Kᵀ)₀₀ = (Σ K)₀₀`. -/
noncomputable def HE : ℝ := S 0 0 * k00E S + S 0 1 * k01E S
/-- The sensitivity. -/
noncomputable def sensE (γ : ℝ) : ℝ := (1 + S 1 1 + γ * S 0 1) / vZE S γ
/-- Decrease of the trace at a revealing date. -/
noncomputable def DE (γ : ℝ) : ℝ := (F0E S γ ^ 2 + F1E S γ ^ 2) / vZE S γ

end Explicit

section Sym

variable {S : M2} (hs : S 1 0 = S 0 1) (hd : dE S ≠ 0)
include hs hd

lemma inv_add_one_eq :
    (S + 1)⁻¹ = !![(1 + S 1 1) / dE S, - S 0 1 / dE S; - S 0 1 / dE S, (1 + S 0 0) / dE S] := by
  have hd' : (S + 1) 0 0 * (S + 1) 1 1 - (S + 1) 0 1 ^ 2 ≠ 0 := by
    convert hd using 1; simp [dE]; ring
  rw [inv_sym_eq (S + 1) (by simp [hs]) hd']
  ext i j; fin_cases i <;> fin_cases j <;> simp [dE] <;> ring

lemma gainK_eq : gainK S = !![k00E S, k01E S; k01E S, k11E S] := by
  rw [gainK, inv_add_one_eq hs hd]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hs, k00E, k01E, k11E] <;> field_simp <;> ring

lemma loadA_eq (γ : ℝ) : loadA S γ = ![A0E S γ, A1E S γ] := by
  simp [loadA, gainK_eq hs hd, A0E, A1E]

lemma Ht_eq : Ht S = HE S := by
  simp only [Ht, gainK_eq hs hd, HE]
  simp [Matrix.mul_apply, Fin.sum_univ_two, hs, k00E, k01E, k11E, vecMul, dotProduct]
  field_simp
  simp only [dE]; ring

lemma varZ_eq_vZE (γ : ℝ) : varZ S γ = vZE S γ := by
  simp [varZ, loadA_eq hs hd, dotProduct, mulVec, Fin.sum_univ_two, hs, vZE]; ring

lemma vZE_eq_VCH (γ : ℝ) : vZE S γ = Vt S + 2 * γ * Ct S + γ ^ 2 * Ht S := by
  rw [Ht_eq hs hd]
  simp only [vZE, A0E, A1E, HE, Vt, Ct, k00E, k01E]
  field_simp
  simp only [dE]; ring

lemma sens_eq_sensE (γ : ℝ) : sens S γ = sensE S γ := by
  rw [sens, ← vZE_eq_VCH hs hd, sensE, Vt, Ct]

lemma mulVec_loadA_zero (γ : ℝ) : (S *ᵥ loadA S γ) 0 = F0E S γ := by
  simp [loadA_eq hs hd, mulVec, dotProduct, Fin.sum_univ_two, F0E]

lemma mulVec_loadA_one (γ : ℝ) : (S *ᵥ loadA S γ) 1 = F1E S γ := by
  simp [loadA_eq hs hd, mulVec, dotProduct, Fin.sum_univ_two, F1E, hs]

lemma kalman_apply (γ : ℝ) (i j : Fin 2) :
    kalman S γ i j = S i j - (vZE S γ)⁻¹ * ((S *ᵥ loadA S γ) i * (S *ᵥ loadA S γ) j) := by
  simp [kalman, varZ_eq_vZE hs hd, vecMulVec_apply]

lemma kalman00 (γ : ℝ) : kalman S γ 0 0 = S 0 0 - F0E S γ ^ 2 / vZE S γ := by
  rw [kalman_apply hs hd, mulVec_loadA_zero hs hd]; ring

lemma kalman11 (γ : ℝ) : kalman S γ 1 1 = S 1 1 - F1E S γ ^ 2 / vZE S γ := by
  rw [kalman_apply hs hd, mulVec_loadA_one hs hd]; ring

lemma kalman01 (γ : ℝ) : kalman S γ 0 1 = S 0 1 - F0E S γ * F1E S γ / vZE S γ := by
  rw [kalman_apply hs hd, mulVec_loadA_zero hs hd, mulVec_loadA_one hs hd]; ring

lemma kalman10 (γ : ℝ) : kalman S γ 1 0 = S 0 1 - F0E S γ * F1E S γ / vZE S γ := by
  rw [kalman_apply hs hd, mulVec_loadA_zero hs hd, mulVec_loadA_one hs hd, hs]; ring

end Sym


/-! ### Positivity facts (coordinate form) -/

/-- Rank-one update in coordinates: positivity of the updated entries and its determinant. -/
lemma kal_real {a b c x y : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c)
    (hn : 0 < x ^ 2 + y ^ 2) :
    let v := (1 + a) * x ^ 2 + 2 * b * x * y + (1 + c) * y ^ 2
    let f0 := a * x + b * y
    let f1 := b * x + c * y
    x ^ 2 + y ^ 2 ≤ v ∧ f0 ^ 2 ≤ a * (v - (x ^ 2 + y ^ 2)) ∧ f1 ^ 2 ≤ c * (v - (x ^ 2 + y ^ 2)) ∧
    a * (x ^ 2 + y ^ 2) / v ≤ a - f0 ^ 2 / v ∧ c * (x ^ 2 + y ^ 2) / v ≤ c - f1 ^ 2 / v ∧
    (a - f0 ^ 2 / v) * (c - f1 ^ 2 / v) - (b - f0 * f1 / v) ^ 2 =
      (a * c - b ^ 2) * (x ^ 2 + y ^ 2) / v := by
  intro v f0 f1
  have hQ := quad_nonneg ha hc hb x y
  have hvQ : v = (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) + (x ^ 2 + y ^ 2) := by
    simp only [v]; ring
  have hv : 0 < v := by rw [hvQ]; linarith
  have h0 : f0 ^ 2 ≤ a * (v - (x ^ 2 + y ^ 2)) := by
    have : a * (v - (x ^ 2 + y ^ 2)) - f0 ^ 2 = (a * c - b ^ 2) * y ^ 2 := by
      rw [hvQ]; simp only [f0]; ring
    nlinarith [sq_nonneg y]
  have h1 : f1 ^ 2 ≤ c * (v - (x ^ 2 + y ^ 2)) := by
    have : c * (v - (x ^ 2 + y ^ 2)) - f1 ^ 2 = (a * c - b ^ 2) * x ^ 2 := by
      rw [hvQ]; simp only [f1]; ring
    nlinarith [sq_nonneg x]
  refine ⟨by rw [hvQ]; linarith, h0, h1, ?_, ?_, ?_⟩
  · rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hv]; nlinarith
  · rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hv]; nlinarith
  · have key : a * f1 ^ 2 + c * f0 ^ 2 - 2 * b * f0 * f1 =
        (a * c - b ^ 2) * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) := by
      simp only [f0, f1]; ring
    field_simp
    linear_combination (v * (a * c - b ^ 2)) * hvQ - v * key

section PSD

variable {S : M2} (hP : PSDE S)
include hP

lemma dE_ge_one : 1 ≤ dE S := by
  obtain ⟨h0, h1, hb⟩ := hP
  simp only [dE]; nlinarith

lemma dE_pos : 0 < dE S := lt_of_lt_of_le one_pos (dE_ge_one hP)

lemma dE_ne : dE S ≠ 0 := (dE_pos hP).ne'

lemma k00E_ge : S 0 0 / dE S ≤ k00E S := by
  obtain ⟨h0, h1, hb⟩ := hP
  have hd := dE_pos ⟨h0, h1, hb⟩
  rw [k00E]; exact (div_le_div_iff_of_pos_right hd).2 (by nlinarith)

lemma k00E_nonneg : 0 ≤ k00E S :=
  le_trans (div_nonneg hP.1 (dE_pos hP).le) (k00E_ge hP)

lemma k00E_le_one : k00E S ≤ 1 := by
  obtain ⟨h0, h1, hb⟩ := hP
  rw [k00E, div_le_one (dE_pos ⟨h0, h1, hb⟩), dE]; nlinarith

lemma abs_k01E_le : |k01E S| ≤ 1 / 2 := by
  obtain ⟨h0, h1, hb⟩ := hP
  have hd := dE_pos ⟨h0, h1, hb⟩
  rw [k01E, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  have h2 : 2 * |S 0 1| ≤ S 0 0 + S 1 1 := by
    rcases abs_cases (S 0 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    · by_contra hc; push Not at hc
      nlinarith [sq_nonneg (S 0 0 - S 1 1)]
  simp only [dE]; nlinarith

lemma HE_nonneg : 0 ≤ HE S := by
  obtain ⟨h0, h1, hb⟩ := hP
  have hd := dE_pos ⟨h0, h1, hb⟩
  rw [HE, k00E, k01E, mul_div_assoc', mul_div_assoc', ← add_div]
  apply div_nonneg _ hd.le
  have : S 0 1 * S 0 1 ≤ S 0 0 * S 1 1 := by nlinarith
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h1, sq_nonneg (S 0 1),
    mul_nonneg h0 (by nlinarith : (0:ℝ) ≤ S 0 0 * S 1 1 - S 0 1 ^ 2)]

lemma HE_le : HE S ≤ S 0 0 := by
  obtain ⟨h0, h1, hb⟩ := hP
  have hd := dE_pos ⟨h0, h1, hb⟩
  rw [HE, k00E, k01E, mul_div_assoc', mul_div_assoc', ← add_div, div_le_iff₀ hd, dE]
  nlinarith

lemma A_pos (γ : ℝ) : 0 < A0E S γ ^ 2 + A1E S γ ^ 2 := by
  obtain ⟨h0, h1, hb⟩ := hP
  have hd := dE_pos ⟨h0, h1, hb⟩
  by_contra hc; push Not at hc
  have hx : A0E S γ = 0 := by nlinarith [sq_nonneg (A0E S γ), sq_nonneg (A1E S γ)]
  have hy : A1E S γ = 0 := by nlinarith [sq_nonneg (A0E S γ), sq_nonneg (A1E S γ)]
  rw [A0E, k00E, mul_div_assoc', div_eq_zero_iff] at hx
  rw [A1E, k01E] at hy
  rcases hx with hx | hx
  · rcases mul_eq_zero.1 hx with hg | hx
    · rw [hg] at hy; simp at hy
    · have ha : S 0 0 = 0 := by nlinarith
      have hb0 : S 0 1 = 0 := by nlinarith
      rw [hb0] at hy; simp at hy
  · exact hd.ne' hx

lemma vZE_ge (γ : ℝ) : A0E S γ ^ 2 + A1E S γ ^ 2 ≤ vZE S γ :=
  (kal_real hP.1 hP.2.1 hP.2.2 (A_pos hP γ)).1

lemma vZE_pos (γ : ℝ) : 0 < vZE S γ := lt_of_lt_of_le (A_pos hP γ) (vZE_ge hP γ)

lemma vZE_ne (γ : ℝ) : vZE S γ ≠ 0 := (vZE_pos hP γ).ne'

lemma vZE_expand (γ : ℝ) : vZE S γ = 1 + S 1 1 + 2 * γ * S 0 1 + γ ^ 2 * HE S := by
  have hd := dE_ne hP
  simp only [vZE, A0E, A1E, HE, k00E, k01E]
  field_simp
  simp only [dE]; ring

omit hP in
lemma F0E_eq (γ : ℝ) : F0E S γ = S 0 1 + γ * HE S := by
  simp only [F0E, A0E, A1E, HE]; ring

lemma one_sub_sensE (γ : ℝ) : 1 - sensE S γ = γ * F0E S γ / vZE S γ := by
  have hv := vZE_ne hP γ
  rw [sensE, F0E_eq, eq_div_iff hv, sub_mul, div_mul_cancel₀ _ hv, vZE_expand hP]; ring

lemma DE_nonneg (γ : ℝ) : 0 ≤ DE S γ := div_nonneg (by positivity) (vZE_pos hP γ).le

lemma F0sq_le_DE (γ : ℝ) : F0E S γ ^ 2 / vZE S γ ≤ DE S γ := by
  have := vZE_pos hP γ
  rw [DE]; exact (div_le_div_iff_of_pos_right this).2 (by nlinarith [sq_nonneg (F1E S γ)])

lemma A1E_ge (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) : 1 / 2 ≤ A1E S γ := by
  have := abs_le.1 (abs_k01E_le hP)
  rw [A1E]; nlinarith

lemma vZE_ge_quarter (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) : 1 / 4 ≤ vZE S γ := by
  have h1 := A1E_ge hP γ hγ0 hγ1
  have := vZE_ge hP γ
  nlinarith [sq_nonneg (A0E S γ)]

end PSD

/-! ### Kalman update preserves positivity -/

lemma kalman_psd {S : M2} (h : S.PosSemidef) (γ : ℝ) : (kalman S γ).PosSemidef := by
  obtain ⟨hs, hP⟩ := (psd_iff S).1 h
  have hd := dE_ne hP
  have K := kal_real hP.1 hP.2.1 hP.2.2 (A_pos hP γ)
  simp only at K
  obtain ⟨-, -, -, ha, hc, hdet⟩ := K
  rw [psd_iff]
  refine ⟨by rw [kalman10 hs hd, kalman01 hs hd], ?_, ?_, ?_⟩
  · rw [kalman00 hs hd]; exact le_trans (by have := hP.1; have := A_pos hP γ; have := vZE_pos hP γ; positivity) ha
  · rw [kalman11 hs hd]; exact le_trans (by have := hP.2.1; have := A_pos hP γ; have := vZE_pos hP γ; positivity) hc
  · rw [kalman00 hs hd, kalman11 hs hd, kalman01 hs hd]
    have : 0 ≤ (S 0 0 * S 1 1 - S 0 1 ^ 2) * (A0E S γ ^ 2 + A1E S γ ^ 2) / vZE S γ := by
      have := hP.2.2; have := A_pos hP γ; have := vZE_pos hP γ
      apply div_nonneg _ this.le; apply mul_nonneg <;> linarith
    simp only [F0E, F1E, vZE] at *
    linarith

lemma kalman_pd {S : M2} (h : S.PosDef) (γ : ℝ) : (kalman S γ).PosDef := by
  obtain ⟨hs, h0, hb⟩ := (pd_iff S).1 h
  have hP : PSDE S := ⟨h0.le, by nlinarith [sq_nonneg (S 0 1)], hb.le⟩
  have hd := dE_ne hP
  have K := kal_real hP.1 hP.2.1 hP.2.2 (A_pos hP γ)
  simp only at K
  obtain ⟨-, -, -, ha, -, hdet⟩ := K
  rw [pd_iff]
  have hv := vZE_pos hP γ
  have hn := A_pos hP γ
  refine ⟨by rw [kalman10 hs hd, kalman01 hs hd], ?_, ?_⟩
  · rw [kalman00 hs hd]; exact lt_of_lt_of_le (by positivity) ha
  · rw [kalman00 hs hd, kalman11 hs hd, kalman01 hs hd]
    have : 0 < (S 0 0 * S 1 1 - S 0 1 ^ 2) * (A0E S γ ^ 2 + A1E S γ ^ 2) / vZE S γ := by
      apply div_pos _ hv; apply mul_pos <;> linarith
    simp only [F0E, F1E, vZE] at *
    linarith


/-! ### Lemma A1: precision update -/

lemma pd_PSDE {S : M2} (h : S.PosDef) : PSDE S := by
  obtain ⟨-, h0, hb⟩ := (pd_iff S).1 h
  exact ⟨h0.le, by nlinarith [sq_nonneg (S 0 1)], hb.le⟩

lemma psd_PSDE {S : M2} (h : S.PosSemidef) : PSDE S := ((psd_iff S).1 h).2

lemma sym_of_psd {S : M2} (h : S.PosSemidef) : S 1 0 = S 0 1 := ((psd_iff S).1 h).1

lemma smul_vecMulVec_two (t x y : ℝ) :
    t • vecMulVec ![x, y] ![x, y] = !![t * (x * x), t * (x * y); t * (y * x), t * (y * y)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma kalman_inv {S : M2} (h : S.PosDef) (γ : ℝ) :
    (kalman S γ)⁻¹ = S⁻¹ + (loadA S γ ⬝ᵥ loadA S γ)⁻¹ • vecMulVec (loadA S γ) (loadA S γ) := by
  obtain ⟨hs, h0, hb⟩ := (pd_iff S).1 h
  have hP := pd_PSDE h
  have hd := dE_ne hP
  have hδ : S 0 0 * S 1 1 - S 0 1 ^ 2 ≠ 0 := by
    have : 0 < S 0 0 * S 1 1 - S 0 1 ^ 2 := by linarith
    exact this.ne'
  have hv := vZE_ne hP γ
  have hn : A0E S γ * A0E S γ + A1E S γ * A1E S γ ≠ 0 := by
    have := A_pos hP γ; nlinarith
  have hn2 : A0E S γ ^ 2 + A1E S γ ^ 2 ≠ 0 := (A_pos hP γ).ne'
  have hδ' : -S 0 1 ^ 2 + S 0 0 * S 1 1 ≠ 0 := by convert hδ using 1; ring
  apply Matrix.inv_eq_right_inv
  have hdot : loadA S γ ⬝ᵥ loadA S γ = A0E S γ ^ 2 + A1E S γ ^ 2 := by
    rw [loadA_eq hs hd]; simp [dotProduct, Fin.sum_univ_two]; ring
  rw [hdot, inv_sym_eq S hs hδ, loadA_eq hs hd, smul_vecMulVec_two]
  generalize hδg : S 0 0 * S 1 1 - S 0 1 ^ 2 = δ at hδ ⊢
  generalize hng : A0E S γ ^ 2 + A1E S γ ^ 2 = n at hn2 ⊢
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, kalman00 hs hd, kalman01 hs hd, kalman10 hs hd,
      kalman11 hs hd] <;>
    field_simp <;> rw [← hδg, ← hng] <;> simp only [F0E, F1E, vZE] <;> ring

lemma proj_props (A : Fin 2 → ℝ) (hA : 0 < A ⬝ᵥ A) :
    ((A ⬝ᵥ A)⁻¹ • vecMulVec A A)ᵀ = (A ⬝ᵥ A)⁻¹ • vecMulVec A A ∧
    ((A ⬝ᵥ A)⁻¹ • vecMulVec A A) * ((A ⬝ᵥ A)⁻¹ • vecMulVec A A) =
      (A ⬝ᵥ A)⁻¹ • vecMulVec A A ∧
    ((A ⬝ᵥ A)⁻¹ • vecMulVec A A).rank = 1 ∧ ((A ⬝ᵥ A)⁻¹ • vecMulVec A A).trace = 1 := by
  have hA' : A 0 * A 0 + A 1 * A 1 ≠ 0 := by
    have : A ⬝ᵥ A = A 0 * A 0 + A 1 * A 1 := by simp [dotProduct, Fin.sum_univ_two]
    rw [← this]; exact hA.ne'
  have hA2 : A 0 ^ 2 + A 1 ^ 2 ≠ 0 := by convert hA' using 1; ring
  have hA3 : A 1 ^ 2 + A 0 ^ 2 ≠ 0 := by convert hA' using 1; ring
  refine ⟨by simp [Matrix.transpose_smul], ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply, dotProduct] <;>
      field_simp
  · apply le_antisymm
    · rw [← smul_vecMulVec]; exact rank_vecMulVec_le _ _
    · rw [Matrix.rank]
      apply Submodule.one_le_finrank_iff.2
      intro hbot
      have hmem : A ∈ LinearMap.range ((A ⬝ᵥ A)⁻¹ • vecMulVec A A).mulVecLin := by
        refine ⟨A, ?_⟩
        rw [Matrix.mulVecLin_apply]
        ext i; fin_cases i <;>
          simp [mulVec, vecMulVec_apply, dotProduct, Fin.sum_univ_two] <;> field_simp
      rw [hbot, Submodule.mem_bot] at hmem
      rw [hmem] at hA; simp at hA
  · rw [trace_smul, trace_vecMulVec, smul_eq_mul, inv_mul_cancel₀ hA.ne']

lemma trace_kalman {S : M2} (hs : S 1 0 = S 0 1) (hd : dE S ≠ 0) (γ : ℝ) :
    (kalman S γ).trace = S.trace - DE S γ := by
  rw [trace_fin_two, trace_fin_two, kalman00 hs hd, kalman11 hs hd, DE, add_div]; ring

lemma kalman_sum {S : M2} (hs : S 1 0 = S 0 1) (hd : dE S ≠ 0) (γ : ℝ) :
    kalman S γ 0 0 + 2 * kalman S γ 0 1 + kalman S γ 1 1 =
      S 0 0 + 2 * S 0 1 + S 1 1 - (F0E S γ + F1E S γ) ^ 2 / vZE S γ := by
  rw [kalman00 hs hd, kalman11 hs hd, kalman01 hs hd]; ring

/-- For positive definite `Λ⁻¹ = S`: `1 / tr(S⁻¹) ≤ min (S 0 0) (S 1 1)`. -/
lemma inv_trace_bound {S : M2} (h : S.PosDef) : 1 / (S⁻¹).trace ≤ min (S 0 0) (S 1 1) := by
  obtain ⟨hs, h0, hb⟩ := (pd_iff S).1 h
  have hδ : 0 < S 0 0 * S 1 1 - S 0 1 ^ 2 := by linarith
  have h1 : 0 < S 1 1 := by nlinarith [sq_nonneg (S 0 1)]
  rw [inv_sym_eq S hs hδ.ne', trace_fin_two]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  rw [← add_div, one_div_div]
  apply le_min
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

/-! ### Revealing dates: size of the update -/

/-- If `1 - s = γ F / v` and `s² ≤ r < 1`, then `γ F > 0` and `((1-r)/2)² v² ≤ γ² F²`. -/
lemma rev_bound {s γ F v r : ℝ} (hv : 0 < v) (h1s : 1 - s = γ * F / v) (hr1 : r < 1)
    (hs : s ^ 2 ≤ r) : 0 < γ * F ∧ ((1 - r) / 2) ^ 2 * v ^ 2 ≤ γ ^ 2 * F ^ 2 := by
  have hm : (1 - r) / 2 ≤ 1 - s := by nlinarith [sq_nonneg (1 - s)]
  have hγF : γ * F = (1 - s) * v := by rw [h1s]; field_simp
  have hm0 : 0 < (1 - r) / 2 := by linarith
  refine ⟨by rw [hγF]; exact mul_pos (by linarith) hv, ?_⟩
  have : (1 - r) / 2 * v ≤ γ * F := by rw [hγF]; exact mul_le_mul_of_nonneg_right hm hv.le
  have h0 : 0 ≤ (1 - r) / 2 * v := by positivity
  calc ((1 - r) / 2) ^ 2 * v ^ 2 = ((1 - r) / 2 * v) ^ 2 := by ring
    _ ≤ (γ * F) ^ 2 := pow_le_pow_left₀ h0 this 2
    _ = γ ^ 2 * F ^ 2 := by ring

section Rev

variable {S : M2} (hP : PSDE S) {γ r : ℝ} (hr1 : r < 1) (hsr : sensE S γ ^ 2 ≤ r)
include hP hr1 hsr

/-- At a revealing date (any `γ`), `σ²_θ` falls by at least `((1-r)/2)² K₀₀²`. -/
lemma rev_dec_gen : ((1 - r) / 2) ^ 2 * k00E S ^ 2 ≤ F0E S γ ^ 2 / vZE S γ := by
  have hv := vZE_pos hP γ
  obtain ⟨hpos, hb⟩ := rev_bound hv (one_sub_sensE hP γ) hr1 hsr
  have hγ : γ ≠ 0 := by rintro rfl; simp at hpos
  have hA := vZE_ge hP γ
  have hA0 : γ ^ 2 * k00E S ^ 2 ≤ vZE S γ := by
    have : A0E S γ ^ 2 = γ ^ 2 * k00E S ^ 2 := by rw [A0E]; ring
    nlinarith [sq_nonneg (A1E S γ)]
  have hγ2 : 0 < γ ^ 2 := by positivity
  rw [le_div_iff₀ hv]
  have hm : 0 ≤ ((1 - r) / 2) ^ 2 := sq_nonneg _
  have h3 : γ ^ 2 * (((1 - r) / 2) ^ 2 * k00E S ^ 2 * vZE S γ) ≤ γ ^ 2 * F0E S γ ^ 2 := by
    calc γ ^ 2 * (((1 - r) / 2) ^ 2 * k00E S ^ 2 * vZE S γ)
        = ((1 - r) / 2) ^ 2 * vZE S γ * (γ ^ 2 * k00E S ^ 2) := by ring
      _ ≤ ((1 - r) / 2) ^ 2 * vZE S γ * vZE S γ :=
          mul_le_mul_of_nonneg_left hA0 (mul_nonneg hm hv.le)
      _ = ((1 - r) / 2) ^ 2 * vZE S γ ^ 2 := by ring
      _ ≤ γ ^ 2 * F0E S γ ^ 2 := hb
  exact le_of_mul_le_mul_left h3 hγ2

end Rev

/-- The sensitivity is close to one when `σ²_θ` and `Cov` are small:
`|1 - s̃| (1 - 2γ|C|) ≤ γ (|C| + γ σ²_θ)` for `γ ≥ 0`. -/
lemma sens_near_one {S : M2} (hP : PSDE S) {γ : ℝ} (hγ : 0 ≤ γ) :
    |1 - sensE S γ| * (1 - 2 * γ * |S 0 1|) ≤ γ * (|S 0 1| + γ * S 0 0) := by
  have hv := vZE_pos hP γ
  rw [one_sub_sensE hP, abs_div, abs_of_pos hv, abs_mul, abs_of_nonneg hγ]
  have hH0 := HE_nonneg hP
  have hH1 := HE_le hP
  have hF : |F0E S γ| ≤ |S 0 1| + γ * S 0 0 := by
    rw [F0E_eq]
    calc |S 0 1 + γ * HE S| ≤ |S 0 1| + |γ * HE S| := abs_add_le _ _
      _ = |S 0 1| + γ * HE S := by rw [abs_of_nonneg (mul_nonneg hγ hH0)]
      _ ≤ |S 0 1| + γ * S 0 0 := by gcongr
  have hvl : 1 - 2 * γ * |S 0 1| ≤ vZE S γ := by
    rw [vZE_expand hP]
    have := neg_abs_le (S 0 1)
    have h1 := hP.2.1
    nlinarith [mul_nonneg (sq_nonneg γ) hH0, mul_nonneg hγ (abs_nonneg (S 0 1))]
  rcases le_or_gt (1 - 2 * γ * |S 0 1|) 0 with h | h
  · have : 0 ≤ γ * |F0E S γ| / vZE S γ := by positivity
    nlinarith [mul_nonneg hγ (abs_nonneg (S 0 1)), mul_nonneg hγ (mul_nonneg hγ hP.1)]
  · calc γ * |F0E S γ| / vZE S γ * (1 - 2 * γ * |S 0 1|)
        ≤ γ * |F0E S γ| / vZE S γ * vZE S γ := by gcongr
      _ = γ * |F0E S γ| := by field_simp
      _ ≤ γ * (|S 0 1| + γ * S 0 0) := by gcongr

end CC
