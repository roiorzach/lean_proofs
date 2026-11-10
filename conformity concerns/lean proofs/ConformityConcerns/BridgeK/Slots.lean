import ConformityConcerns.BridgeK.Meas
import ConformityConcerns.BridgeK.Gauss

/-!
# Public signals as a sequence of slots

Date `t` has two slots: slot `2t` is the disclosure at date `t` (noise `ξ_{2t}`), slot `2t + 1` is
the action at date `t` (noise `ξ_{2t+1}`). The signal in slot `k` is `a_k · x + b_k · ξ_k` with
loadings `(a_k, b_k)` (`ld`): `(e_i, √n e_i)` for a disclosure of `x_i + √n ξ`, `(A_t, A_t)` for a
revealing action, `(0, 0)` otherwise. `Cs k` is the covariance before slot `k`
(`SigPre t` before slot `2t`, `SigK t` before slot `2t + 1`), and `km y k` is the Kalman mean of
`(θ, μ)` after the signals `y_0, …, y_{k-1}`.
-/

namespace CC.BridgeK

open MeasureTheory Matrix

set_option warn.classDefReducibility false

/-- Loadings of a disclosure slot. -/
noncomputable def ldD (d : Option (Fin 2 × ℝ)) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  match d with
  | none => (0, 0)
  | some (i, n) => (eVec i, nVec i n)

/-- Loadings of an action slot. -/
noncomputable def ldA (κ γ : ℝ) (S : M2) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  haveI := Classical.propDecidable (revCrit κ S γ)
  if revCrit κ S γ then (loadA S γ, loadA S γ) else (0, 0)

variable (S₁ : M2) (D : Sched)

/-- The covariance before slot `k`. -/
noncomputable def Cs (w : ℕ → ℝ × ℝ) (k : ℕ) : M2 :=
  if k % 2 = 0 then SigPre S₁ D w (k / 2) else SigK S₁ D w (k / 2)

/-- The loadings of slot `k`. -/
noncomputable def ld (w : ℕ → ℝ × ℝ) (k : ℕ) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  if k % 2 = 0 then ldD (D (k / 2)) else ldA (w (k / 2)).1 (w (k / 2)).2 (SigK S₁ D w (k / 2))

lemma two_mul_mod (t : ℕ) : (2 * t) % 2 = 0 := by omega
lemma two_mul_div (t : ℕ) : (2 * t) / 2 = t := by omega
lemma two_mul_add_mod (t : ℕ) : (2 * t + 1) % 2 = 1 := by omega
lemma two_mul_add_div (t : ℕ) : (2 * t + 1) / 2 = t := by omega

lemma Cs_even (w : ℕ → ℝ × ℝ) (t : ℕ) : Cs S₁ D w (2 * t) = SigPre S₁ D w t := by
  simp [Cs]

lemma Cs_odd (w : ℕ → ℝ × ℝ) (t : ℕ) : Cs S₁ D w (2 * t + 1) = SigK S₁ D w t := by
  simp [Cs, two_mul_add_div]

lemma ld_even (w : ℕ → ℝ × ℝ) (t : ℕ) : ld S₁ D w (2 * t) = ldD (D t) := by
  simp [ld]

lemma ld_odd (w : ℕ → ℝ × ℝ) (t : ℕ) :
    ld S₁ D w (2 * t + 1) = ldA (w t).1 (w t).2 (SigK S₁ D w t) := by
  simp [ld, two_mul_add_div]

/-- Noise variances of the scheduled disclosures are nonnegative. -/
def SchedOK (D : Sched) : Prop := ∀ t i n, D t = some (i, n) → 0 ≤ n

lemma schedOK_noDisc : SchedOK noDisc := by
  intro t i n h; simp [noDisc] at h

lemma schedOK_interventionAt (τ : ℕ) (i : Fin 2) {n : ℝ} (hn : 0 ≤ n) :
    SchedOK (interventionAt τ i n) := by
  intro t j m h
  simp only [interventionAt] at h
  split_ifs at h with ht
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact hn

lemma Cs_succ (hD : SchedOK D) (w : ℕ → ℝ × ℝ) (k : ℕ) :
    Cs S₁ D w (k + 1) = updG (Cs S₁ D w k) (ld S₁ D w k).1 (ld S₁ D w k).2 := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [Cs_odd, Cs_even, ld_even]
    unfold SigK
    rcases h : D t with _ | ⟨i, n⟩
    · simp [ldD, discCov, updG_zero]
    · simp only [ldD]
      rw [updG_disc _ i (hD t i n h)]
  · have e : 2 * t + 1 + 1 = 2 * (t + 1) := by ring
    rw [e, Cs_even, Cs_odd, ld_odd]
    show stepCov (w t).1 (w t).2 (SigK S₁ D w t) = _
    unfold stepCov ldA
    split_ifs
    · rw [updG_loadA]
    · rw [updG_zero]

lemma Cs_psd (hD : SchedOK D) (hS : S₁.PosSemidef) (w : ℕ → ℝ × ℝ) (k : ℕ) :
    (Cs S₁ D w k).PosSemidef := by
  induction k with
  | zero =>
    have h := Cs_even S₁ D w 0
    rw [mul_zero] at h
    rw [h]; exact hS
  | succ k ih => rw [Cs_succ S₁ D hD]; exact updG_posSemidef ih

lemma SigK_psd (hD : SchedOK D) (hS : S₁.PosSemidef) (w : ℕ → ℝ × ℝ) (t : ℕ) :
    (SigK S₁ D w t).PosSemidef := by
  rw [← Cs_odd]; exact Cs_psd S₁ D hD hS w _

/-! ### Signals and the Kalman mean along a weight path -/

/-- The signal of slot `k` as a function of the state `x` and the noises `ξ`. -/
noncomputable def sigF (w : ℕ → ℝ × ℝ) (x : E2) (ξ : ℕ → E2) (k : ℕ) : ℝ :=
  ZG (ld S₁ D w k).1 (ld S₁ D w k).2 (x, ξ k)

/-- The Kalman mean after the signals `y_0, …, y_{k-1}`. -/
noncomputable def km (w : ℕ → ℝ × ℝ) (y : ℕ → ℝ) : ℕ → E2
  | 0 => 0
  | k + 1 => km w y k + (y k - Bridge.dotA (ld S₁ D w k).1 (km w y k)) •
      kG (Cs S₁ D w k) (ld S₁ D w k).1 (ld S₁ D w k).2

/-- `Cs` and `ld` at slot `k` depend only on `w_s` with `2 s ≤ k`. -/
lemma Cs_congr {w w' : ℕ → ℝ × ℝ} {k : ℕ} (h : ∀ s, 2 * s ≤ k → w s = w' s) :
    Cs S₁ D w k = Cs S₁ D w' k := by
  unfold Cs
  split_ifs
  · exact SigPre_congr S₁ D (fun s hs => h s (by omega))
  · exact SigK_congr S₁ D (fun s hs => h s (by omega))

lemma ld_congr {w w' : ℕ → ℝ × ℝ} {k : ℕ} (h : ∀ s, 2 * s ≤ k → w s = w' s) :
    ld S₁ D w k = ld S₁ D w' k := by
  unfold ld
  split_ifs
  · rfl
  · rw [SigK_congr S₁ D (fun s hs => h s (by omega)), h (k / 2) (by omega)]

lemma km_congr {w w' : ℕ → ℝ × ℝ} {y y' : ℕ → ℝ} {k : ℕ} (hw : ∀ s, 2 * s < k → w s = w' s)
    (hy : ∀ j < k, y j = y' j) : km S₁ D w y k = km S₁ D w' y' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih (fun s hs => hw s (by omega)) (fun j hj => hy j (by omega))
    have hC := Cs_congr S₁ D (w := w) (w' := w') (k := k) (fun s hs => hw s (by omega))
    have hL := ld_congr S₁ D (w := w) (w' := w') (k := k) (fun s hs => hw s (by omega))
    simp only [km]
    rw [ih', hC, hL, hy k (Nat.lt_succ_self k)]

lemma km_trunc (w : ℕ → ℝ × ℝ) (y : ℕ → ℝ) (k : ℕ) :
    km S₁ D w (Bridge.trunc k y) k = km S₁ D w y k :=
  km_congr S₁ D (fun _ _ => rfl) (fun j hj => by simp [Bridge.trunc, hj])

/-! ### Measurability -/

lemma measurable_ld_pair (k : ℕ) (j : Fin 2) :
    Measurable (fun w : ℕ → ℝ × ℝ => (ld S₁ D w k).1 j) ∧
      Measurable (fun w : ℕ → ℝ × ℝ => (ld S₁ D w k).2 j) := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' k
  · simp only [ld_even]; exact ⟨measurable_const, measurable_const⟩
  · have hS := measurable_SigK S₁ D t
    have hk : Measurable (fun w : ℕ → ℝ × ℝ => (w t).1) :=
      measurable_fst.comp (measurable_pi_apply t)
    have hg : Measurable (fun w : ℕ → ℝ × ℝ => (w t).2) :=
      measurable_snd.comp (measurable_pi_apply t)
    have hr := meas_revCrit_gen hk hS hg
    have hA := Bridge.br_meas_loadA hS hg j
    have e1 : (fun w : ℕ → ℝ × ℝ => (ld S₁ D w (2 * t + 1)).1 j) = fun w =>
        @ite _ (revCrit (w t).1 (SigK S₁ D w t) (w t).2) (Classical.propDecidable _)
          (loadA (SigK S₁ D w t) (w t).2 j) 0 := by
      funext w; rw [ld_odd]; unfold ldA; split_ifs <;> rfl
    have e2 : (fun w : ℕ → ℝ × ℝ => (ld S₁ D w (2 * t + 1)).2 j) = fun w =>
        @ite _ (revCrit (w t).1 (SigK S₁ D w t) (w t).2) (Classical.propDecidable _)
          (loadA (SigK S₁ D w t) (w t).2 j) 0 := by
      funext w; rw [ld_odd]; unfold ldA; split_ifs <;> rfl
    rw [e1, e2]
    exact ⟨Measurable.ite hr hA measurable_const, Measurable.ite hr hA measurable_const⟩

lemma measurable_Cs (k : ℕ) : Measurable (fun w : ℕ → ℝ × ℝ => Cs S₁ D w k) := by
  unfold Cs
  split_ifs
  · exact measurable_SigPre S₁ D _
  · exact measurable_SigK S₁ D _

lemma measurable_VG_slot (k : ℕ) :
    Measurable (fun w : ℕ → ℝ × ℝ => VG (Cs S₁ D w k) (ld S₁ D w k).1 (ld S₁ D w k).2) := by
  have hC := measurable_Cs S₁ D k
  obtain ⟨a0, b0⟩ := measurable_ld_pair S₁ D k 0
  obtain ⟨a1, b1⟩ := measurable_ld_pair S₁ D k 1
  have e00 := Bridge.br_meas_entry hC 0 0
  have e01 := Bridge.br_meas_entry hC 0 1
  have e10 := Bridge.br_meas_entry hC 1 0
  have e11 := Bridge.br_meas_entry hC 1 1
  have e : (fun w : ℕ → ℝ × ℝ => VG (Cs S₁ D w k) (ld S₁ D w k).1 (ld S₁ D w k).2) =
      fun w => (ld S₁ D w k).1 0 * (Cs S₁ D w k 0 0 * (ld S₁ D w k).1 0 +
          Cs S₁ D w k 0 1 * (ld S₁ D w k).1 1) +
        (ld S₁ D w k).1 1 * (Cs S₁ D w k 1 0 * (ld S₁ D w k).1 0 +
          Cs S₁ D w k 1 1 * (ld S₁ D w k).1 1) +
        ((ld S₁ D w k).2 0 * (ld S₁ D w k).2 0 + (ld S₁ D w k).2 1 * (ld S₁ D w k).2 1) :=
    funext fun w => VG_eq _ _ _
  rw [e]
  exact ((a0.mul ((e00.mul a0).add (e01.mul a1))).add
    (a1.mul ((e10.mul a0).add (e11.mul a1)))).add ((b0.mul b0).add (b1.mul b1))

lemma measurable_kG_slot (k : ℕ) (j : Fin 2) :
    Measurable (fun w : ℕ → ℝ × ℝ => kG (Cs S₁ D w k) (ld S₁ D w k).1 (ld S₁ D w k).2 j) := by
  have hC := measurable_Cs S₁ D k
  obtain ⟨a0, -⟩ := measurable_ld_pair S₁ D k 0
  obtain ⟨a1, -⟩ := measurable_ld_pair S₁ D k 1
  have ej0 := Bridge.br_meas_entry hC j 0
  have ej1 := Bridge.br_meas_entry hC j 1
  have e : (fun w : ℕ → ℝ × ℝ => kG (Cs S₁ D w k) (ld S₁ D w k).1 (ld S₁ D w k).2 j) =
      fun w => (VG (Cs S₁ D w k) (ld S₁ D w k).1 (ld S₁ D w k).2)⁻¹ *
        (Cs S₁ D w k j 0 * (ld S₁ D w k).1 0 + Cs S₁ D w k j 1 * (ld S₁ D w k).1 1) :=
    funext fun w => kG_apply j
  rw [e]
  exact (measurable_VG_slot S₁ D k).inv.mul ((ej0.mul a0).add (ej1.mul a1))

lemma measurable_km (k : ℕ) :
    Measurable (fun p : (ℕ → ℝ × ℝ) × (ℕ → ℝ) => km S₁ D p.1 p.2 k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    refine Bridge.br_meas_E2 fun j => ?_
    have hm0 := Bridge.br_meas_coord ih 0
    have hm1 := Bridge.br_meas_coord ih 1
    have hmj := Bridge.br_meas_coord ih j
    obtain ⟨a0, -⟩ := measurable_ld_pair S₁ D k 0
    obtain ⟨a1, -⟩ := measurable_ld_pair S₁ D k 1
    have hf : Measurable (Prod.fst : (ℕ → ℝ × ℝ) × (ℕ → ℝ) → (ℕ → ℝ × ℝ)) := measurable_fst
    have hK := (measurable_kG_slot S₁ D k j).comp hf
    have a0' := a0.comp hf
    have a1' := a1.comp hf
    have hy : Measurable (fun p : (ℕ → ℝ × ℝ) × (ℕ → ℝ) => p.2 k) :=
      (measurable_pi_apply k).comp measurable_snd
    have e : (fun p : (ℕ → ℝ × ℝ) × (ℕ → ℝ) => km S₁ D p.1 p.2 (k + 1) j) = fun p =>
        km S₁ D p.1 p.2 k j + (p.2 k - ((ld S₁ D p.1 k).1 0 * km S₁ D p.1 p.2 k 0 +
          (ld S₁ D p.1 k).1 1 * km S₁ D p.1 p.2 k 1)) *
          kG (Cs S₁ D p.1 k) (ld S₁ D p.1 k).1 (ld S₁ D p.1 k).2 j := by
      funext p; simp [km, Bridge.dotA]
    rw [e]
    exact hmj.add ((hy.sub ((a0'.mul hm0).add (a1'.mul hm1))).mul hK)

lemma measurable_km_fix (w : ℕ → ℝ × ℝ) (k : ℕ) :
    Measurable (fun y : ℕ → ℝ => km S₁ D w y k) :=
  (measurable_km S₁ D k).comp (measurable_const.prodMk measurable_id)

end CC.BridgeK
