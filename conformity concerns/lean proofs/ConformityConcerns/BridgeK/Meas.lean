import ConformityConcerns.BridgeK.Defs
import ConformityConcerns.Bridge.Meas

/-!
# Measurability of the covariance process in the weight path

`w ↦ SigPre S₁ D w t` and `w ↦ SigK S₁ D w t` are measurable and depend only on `w_0, …, w_{t-1}`;
the revealing event at date `t` is measurable and depends only on `w_0, …, w_t`.
-/

namespace CC.BridgeK

open MeasureTheory Matrix

set_option warn.classDefReducibility false

section Gen

variable {β : Type*} [MeasurableSpace β]

lemma meas_discCov (d : Option (Fin 2 × ℝ)) {f : β → M2} (hf : Measurable f) :
    Measurable (fun x => discCov d (f x)) := by
  rcases d with _ | ⟨i, n⟩
  · exact hf
  · refine Measurable.of_eval_matrix _ fun j k => ?_
    have e00 := Bridge.br_meas_entry hf 0 0
    have e01 := Bridge.br_meas_entry hf 0 1
    have e10 := Bridge.br_meas_entry hf 1 0
    have e11 := Bridge.br_meas_entry hf 1 1
    have ejk := Bridge.br_meas_entry hf j k
    have ej0 := Bridge.br_meas_entry hf j 0
    have ej1 := Bridge.br_meas_entry hf j 1
    have ek0 := Bridge.br_meas_entry hf k 0
    have ek1 := Bridge.br_meas_entry hf k 1
    by_cases hi : i = 0
    · simp only [discCov, hi, ite_true, observeTheta, Matrix.sub_apply, Matrix.smul_apply,
        vecMulVec_apply, mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
      fun_prop
    · simp only [discCov, hi, ite_false, observeMu, Matrix.sub_apply, Matrix.smul_apply,
        vecMulVec_apply, mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
      fun_prop

lemma meas_revCrit_gen {k g : β → ℝ} {f : β → M2} (hk : Measurable k) (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {x | revCrit (k x) (f x) (g x)} := by
  unfold revCrit
  exact measurableSet_le (hk.mul ((Bridge.br_meas_sens hf hg).pow_const 2)) measurable_const

lemma meas_stepCov {k g : β → ℝ} {f : β → M2} (hk : Measurable k) (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun x => stepCov (k x) (g x) (f x)) := by
  have h : (fun x => stepCov (k x) (g x) (f x)) = fun x =>
      haveI := Classical.propDecidable (revCrit (k x) (f x) (g x))
      if revCrit (k x) (f x) (g x) then kalman (f x) (g x) else f x := by
    funext x; rfl
  rw [h]
  classical
  exact Measurable.ite (meas_revCrit_gen hk hf hg) (Bridge.br_meas_kalman hf hg) hf

end Gen

variable (S₁ : M2) (D : Sched)

lemma measurable_SigPre (t : ℕ) : Measurable (fun w : ℕ → ℝ × ℝ => SigPre S₁ D w t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hw : Measurable (fun w : ℕ → ℝ × ℝ => w t) := measurable_pi_apply t
    exact meas_stepCov (measurable_fst.comp hw) (meas_discCov (D t) ih)
      (measurable_snd.comp hw)

lemma measurable_SigK (t : ℕ) : Measurable (fun w : ℕ → ℝ × ℝ => SigK S₁ D w t) :=
  meas_discCov (D t) (measurable_SigPre S₁ D t)

/-- `SigPre S₁ D w t` depends only on `w_0, …, w_{t-1}`. -/
lemma SigPre_congr {w w' : ℕ → ℝ × ℝ} {t : ℕ} (h : ∀ s < t, w s = w' s) :
    SigPre S₁ D w t = SigPre S₁ D w' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
    have ht := h t (Nat.lt_succ_self t)
    show stepCov (w t).1 (w t).2 (discCov (D t) (SigPre S₁ D w t)) =
      stepCov (w' t).1 (w' t).2 (discCov (D t) (SigPre S₁ D w' t))
    rw [ih', ht]

lemma SigK_congr {w w' : ℕ → ℝ × ℝ} {t : ℕ} (h : ∀ s < t, w s = w' s) :
    SigK S₁ D w t = SigK S₁ D w' t := by
  unfold SigK; rw [SigPre_congr S₁ D h]

/-- Date `t` is revealing along the weight path `w`. -/
def revW (w : ℕ → ℝ × ℝ) (t : ℕ) : Prop := revCrit (w t).1 (SigK S₁ D w t) (w t).2

lemma measurableSet_revW (t : ℕ) : MeasurableSet {w : ℕ → ℝ × ℝ | revW S₁ D w t} :=
  meas_revCrit_gen (measurable_fst.comp (measurable_pi_apply t)) (measurable_SigK S₁ D t)
    (measurable_snd.comp (measurable_pi_apply t))

lemma revW_congr {w w' : ℕ → ℝ × ℝ} {t : ℕ} (h : ∀ s ≤ t, w s = w' s) :
    revW S₁ D w t ↔ revW S₁ D w' t := by
  unfold revW
  rw [SigK_congr S₁ D (fun s hs => h s hs.le), h t le_rfl]

lemma revK_eq (t : ℕ) (ω : Ωk) : revK S₁ D t ω ↔ revW S₁ D (wts ω) t := Iff.rfl

end CC.BridgeK
