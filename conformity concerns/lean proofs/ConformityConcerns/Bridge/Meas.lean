import ConformityConcerns.Bridge.Defs
import ConformityConcerns.Dynamics.Lemmas
import ConformityConcerns.Gaussian.Conditioning

/-!
# Measurability of the covariance process and of the observations

* the maps `Σ ↦ K`, `(Σ, γ) ↦ A, Var(Z | h), s̃, kalman Σ γ` are measurable, so `γ ↦ Σ_t(γ)` is
  measurable and the revealing event is measurable;
* `Σ_t(γ)` depends only on `γ_0, …, γ_{t-1}`;
* the observations are measurable, `infoSigma t` is a filtration of sub-σ-algebras, and every
  function of `(γ_0, …, γ_t, obs_0, …, obs_{t-1})` is `infoSigma t`-measurable.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix

set_option warn.classDefReducibility false

/-! ### Matrix maps -/

lemma br_measurable_inv : Measurable (fun A : M2 => A⁻¹) := by
  have h : (fun A : M2 => A⁻¹) = fun A => Ring.inverse A.det • A.adjugate := by
    funext A; exact Matrix.inv_def A
  rw [h, Ring.inverse_eq_inv']
  exact (continuous_id.matrix_det.measurable.inv).smul continuous_id.matrix_adjugate.measurable

lemma br_measurable_gainK : Measurable gainK := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have hI : Measurable (fun A : M2 => (A + 1)⁻¹) :=
    br_measurable_inv.comp (Measurable.of_eval_matrix _ fun i j =>
      (measurable_id.eval_matrix (i := i) (j := j)).add measurable_const)
  have h0 : Measurable (fun A : M2 => (A + 1)⁻¹ 0 j) := hI.eval_matrix
  have h1 : Measurable (fun A : M2 => (A + 1)⁻¹ 1 j) := hI.eval_matrix
  have a0 : Measurable (fun A : M2 => A i 0) := measurable_id.eval_matrix
  have a1 : Measurable (fun A : M2 => A i 1) := measurable_id.eval_matrix
  simp only [gainK, Matrix.mul_apply, Fin.sum_univ_two]
  exact (a0.mul h0).add (a1.mul h1)

section Gen

variable {β : Type*} [MeasurableSpace β] {f : β → M2} {g : β → ℝ}

lemma br_meas_entry (hf : Measurable f) (i j : Fin 2) : Measurable (fun x => f x i j) :=
  hf.eval_matrix

lemma br_meas_gainK (hf : Measurable f) (i j : Fin 2) : Measurable (fun x => gainK (f x) i j) :=
  (br_measurable_gainK.comp hf).eval_matrix

lemma br_meas_loadA (hf : Measurable f) (hg : Measurable g) (i : Fin 2) :
    Measurable (fun x => loadA (f x) (g x) i) := by
  fin_cases i
  · simp only [loadA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact hg.mul (br_meas_gainK hf 0 0)
  · simp only [loadA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact measurable_const.add (hg.mul (br_meas_gainK hf 0 1))

lemma br_meas_varZ (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => varZ (f x) (g x)) := by
  have h0 := br_meas_loadA hf hg 0
  have h1 := br_meas_loadA hf hg 1
  have e00 := br_meas_entry hf 0 0
  have e01 := br_meas_entry hf 0 1
  have e10 := br_meas_entry hf 1 0
  have e11 := br_meas_entry hf 1 1
  simp only [varZ, dotProduct, mulVec, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply]
  fun_prop

lemma br_meas_Ht (hf : Measurable f) : Measurable (fun x => Ht (f x)) := by
  have k00 := br_meas_gainK hf 0 0
  have k01 := br_meas_gainK hf 0 1
  have k10 := br_meas_gainK hf 1 0
  have k11 := br_meas_gainK hf 1 1
  have e00 := br_meas_entry hf 0 0
  have e01 := br_meas_entry hf 0 1
  have e10 := br_meas_entry hf 1 0
  have e11 := br_meas_entry hf 1 1
  simp only [Ht, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply,
    Matrix.transpose_apply]
  fun_prop

lemma br_meas_sens (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => sens (f x) (g x)) := by
  have hH := br_meas_Ht hf
  have e01 := br_meas_entry hf 0 1
  have e11 := br_meas_entry hf 1 1
  simp only [sens, Vt, Ct]
  fun_prop

lemma br_meas_revCrit (κ : ℝ) (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | revCrit κ (f x) (g x)} := by
  unfold revCrit
  exact measurableSet_le (measurable_const.mul ((br_meas_sens hf hg).pow_const 2))
    measurable_const

lemma br_meas_kalman (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => kalman (f x) (g x)) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have hv := br_meas_varZ hf hg
  have h0 := br_meas_loadA hf hg 0
  have h1 := br_meas_loadA hf hg 1
  have e00 := br_meas_entry hf 0 0
  have e01 := br_meas_entry hf 0 1
  have e10 := br_meas_entry hf 1 0
  have e11 := br_meas_entry hf 1 1
  have eij := br_meas_entry hf i j
  have ei0 := br_meas_entry hf i 0
  have ei1 := br_meas_entry hf i 1
  have ej0 := br_meas_entry hf j 0
  have ej1 := br_meas_entry hf j 1
  simp only [kalman, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, mulVec, dotProduct,
    Fin.sum_univ_two, smul_eq_mul]
  fun_prop

end Gen

/-! ### The covariance process along a weight path -/

variable (κ : ℝ) (S₁ : M2)

/-- `Σ_t` along the weight path `γ` (constant conformity concern `κ`). -/
noncomputable abbrev SigP (γ : ℕ → ℝ) (t : ℕ) : M2 := SigmaC (fun _ => κ) S₁ γ t

/-- Date `t` is revealing along `γ`. -/
def revP (γ : ℕ → ℝ) (t : ℕ) : Prop := revCrit κ (SigP κ S₁ γ t) (γ t)

lemma measurable_SigP (t : ℕ) : Measurable (fun γ : ℕ → ℝ => SigP κ S₁ γ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hg : Measurable (fun γ : ℕ → ℝ => γ t) := measurable_pi_apply t
    have hrev : MeasurableSet {γ : ℕ → ℝ | revCrit κ (SigP κ S₁ γ t) (γ t)} :=
      br_meas_revCrit κ ih hg
    have h : (fun γ : ℕ → ℝ => SigP κ S₁ γ (t + 1)) = fun γ =>
        haveI := Classical.propDecidable (revCrit κ (SigP κ S₁ γ t) (γ t))
        if revCrit κ (SigP κ S₁ γ t) (γ t) then kalman (SigP κ S₁ γ t) (γ t)
        else SigP κ S₁ γ t := by
      funext γ; rfl
    rw [h]
    classical
    exact Measurable.ite hrev (br_meas_kalman ih hg) ih

lemma measurableSet_revP (t : ℕ) : MeasurableSet {γ : ℕ → ℝ | revP κ S₁ γ t} :=
  br_meas_revCrit κ (measurable_SigP κ S₁ t) (measurable_pi_apply t)

/-- `Σ_t(γ)` depends only on `γ_0, …, γ_{t-1}`. -/
lemma SigP_congr {γ γ' : ℕ → ℝ} {t : ℕ} (h : ∀ s < t, γ s = γ' s) :
    SigP κ S₁ γ t = SigP κ S₁ γ' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
    have ht := h t (Nat.lt_succ_self t)
    show SigmaC (fun _ => κ) S₁ γ (t + 1) = SigmaC (fun _ => κ) S₁ γ' (t + 1)
    simp only [SigmaC]
    change (haveI := Classical.propDecidable (revCrit κ (SigP κ S₁ γ t) (γ t))
        if revCrit κ (SigP κ S₁ γ t) (γ t) then kalman (SigP κ S₁ γ t) (γ t)
        else SigP κ S₁ γ t) =
      (haveI := Classical.propDecidable (revCrit κ (SigP κ S₁ γ' t) (γ' t))
        if revCrit κ (SigP κ S₁ γ' t) (γ' t) then kalman (SigP κ S₁ γ' t) (γ' t)
        else SigP κ S₁ γ' t)
    rw [ih', ht]

lemma revP_congr {γ γ' : ℕ → ℝ} {t : ℕ} (h : ∀ s ≤ t, γ s = γ' s) :
    revP κ S₁ γ t ↔ revP κ S₁ γ' t := by
  unfold revP
  rw [SigP_congr κ S₁ (fun s hs => h s hs.le), h t le_rfl]

end CC.Bridge
