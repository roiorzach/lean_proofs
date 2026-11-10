import ConformityConcerns.Dynamics.Defs
import ConformityConcerns.Gaussian.BeliefLemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Basic properties of the covariance process `SigmaC`
-/

namespace CC

open Matrix Filter Topology Set

section Basic

variable (κ γ : ℕ → ℝ) (S₁ : M2)

lemma SigmaC_succ_rev {t : ℕ} (h : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)) :
    SigmaC κ S₁ γ (t + 1) = kalman (SigmaC κ S₁ γ t) (γ t) := by
  simp only [SigmaC]; rw [ite_eq_left h]

lemma SigmaC_succ_pool {t : ℕ} (h : ¬ revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)) :
    SigmaC κ S₁ γ (t + 1) = SigmaC κ S₁ γ t := by
  simp only [SigmaC]; rw [ite_eq_right h]

lemma SigmaC_psd' (hS : S₁.PosSemidef) (t : ℕ) : (SigmaC κ S₁ γ t).PosSemidef := by
  induction t with
  | zero => exact hS
  | succ t ih =>
    by_cases h : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)
    · rw [SigmaC_succ_rev κ γ S₁ h]; exact kalman_psd ih _
    · rw [SigmaC_succ_pool κ γ S₁ h]; exact ih

lemma SigmaC_pd (hS : S₁.PosDef) (t : ℕ) : (SigmaC κ S₁ γ t).PosDef := by
  induction t with
  | zero => exact hS
  | succ t ih =>
    by_cases h : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)
    · rw [SigmaC_succ_rev κ γ S₁ h]; exact kalman_pd ih _
    · rw [SigmaC_succ_pool κ γ S₁ h]; exact ih

variable {κ γ S₁}

lemma SigmaC_sym (hS : S₁.PosSemidef) (t : ℕ) : SigmaC κ S₁ γ t 1 0 = SigmaC κ S₁ γ t 0 1 :=
  sym_of_psd (SigmaC_psd' κ γ S₁ hS t)

lemma SigmaC_PSDE (hS : S₁.PosSemidef) (t : ℕ) : PSDE (SigmaC κ S₁ γ t) :=
  psd_PSDE (SigmaC_psd' κ γ S₁ hS t)

/-- One step of the recursion in coordinates. -/
lemma SigmaC_step (hS : S₁.PosSemidef) (t : ℕ) :
    (revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) →
      SigmaC κ S₁ γ (t + 1) 0 0 = SigmaC κ S₁ γ t 0 0 -
          F0E (SigmaC κ S₁ γ t) (γ t) ^ 2 / vZE (SigmaC κ S₁ γ t) (γ t) ∧
      SigmaC κ S₁ γ (t + 1) 1 1 = SigmaC κ S₁ γ t 1 1 -
          F1E (SigmaC κ S₁ γ t) (γ t) ^ 2 / vZE (SigmaC κ S₁ γ t) (γ t) ∧
      (SigmaC κ S₁ γ (t + 1)).trace = (SigmaC κ S₁ γ t).trace - DE (SigmaC κ S₁ γ t) (γ t) ∧
      SigmaC κ S₁ γ (t + 1) 0 0 + 2 * SigmaC κ S₁ γ (t + 1) 0 1 + SigmaC κ S₁ γ (t + 1) 1 1 =
        SigmaC κ S₁ γ t 0 0 + 2 * SigmaC κ S₁ γ t 0 1 + SigmaC κ S₁ γ t 1 1 -
          (F0E (SigmaC κ S₁ γ t) (γ t) + F1E (SigmaC κ S₁ γ t) (γ t)) ^ 2 /
            vZE (SigmaC κ S₁ γ t) (γ t)) := by
  intro h
  have hs := SigmaC_sym (κ := κ) (γ := γ) hS t
  have hd := dE_ne (SigmaC_PSDE (κ := κ) (γ := γ) hS t)
  rw [SigmaC_succ_rev κ γ S₁ h]
  exact ⟨kalman00 hs hd _, kalman11 hs hd _, trace_kalman hs hd _, kalman_sum hs hd _⟩

lemma SigmaC_anti00 (hS : S₁.PosSemidef) : Antitone fun t => SigmaC κ S₁ γ t 0 0 := by
  refine antitone_nat_of_succ_le fun t => ?_
  by_cases h : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)
  · rw [(SigmaC_step hS t h).1]
    have := vZE_pos (SigmaC_PSDE (κ := κ) (γ := γ) hS t) (γ t)
    have : 0 ≤ F0E (SigmaC κ S₁ γ t) (γ t) ^ 2 / vZE (SigmaC κ S₁ γ t) (γ t) := by positivity
    linarith
  · rw [SigmaC_succ_pool κ γ S₁ h]

lemma SigmaC_anti11 (hS : S₁.PosSemidef) : Antitone fun t => SigmaC κ S₁ γ t 1 1 := by
  refine antitone_nat_of_succ_le fun t => ?_
  by_cases h : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)
  · rw [(SigmaC_step hS t h).2.1]
    have := vZE_pos (SigmaC_PSDE (κ := κ) (γ := γ) hS t) (γ t)
    have : 0 ≤ F1E (SigmaC κ S₁ γ t) (γ t) ^ 2 / vZE (SigmaC κ S₁ γ t) (γ t) := by positivity
    linarith
  · rw [SigmaC_succ_pool κ γ S₁ h]

lemma SigmaC_antiSum (hS : S₁.PosSemidef) :
    Antitone fun t => SigmaC κ S₁ γ t 0 0 + 2 * SigmaC κ S₁ γ t 0 1 + SigmaC κ S₁ γ t 1 1 := by
  refine antitone_nat_of_succ_le fun t => ?_
  by_cases h : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)
  · rw [(SigmaC_step hS t h).2.2.2]
    have := vZE_pos (SigmaC_PSDE (κ := κ) (γ := γ) hS t) (γ t)
    have : 0 ≤ (F0E (SigmaC κ S₁ γ t) (γ t) + F1E (SigmaC κ S₁ γ t) (γ t)) ^ 2 /
      vZE (SigmaC κ S₁ γ t) (γ t) := by positivity
    linarith
  · rw [SigmaC_succ_pool κ γ S₁ h]

lemma SigmaC_antiTrace (hS : S₁.PosSemidef) : Antitone fun t => (SigmaC κ S₁ γ t).trace := by
  intro s t hst
  simp only [trace_fin_two]
  exact add_le_add (SigmaC_anti00 hS hst) (SigmaC_anti11 hS hst)

lemma sum_nonneg_of_PSDE {S : M2} (h : PSDE S) : 0 ≤ S 0 0 + 2 * S 0 1 + S 1 1 := by
  have := quad_nonneg h.1 h.2.1 h.2.2 1 1
  linarith

/-- An antitone sequence bounded below has increments tending to zero. -/
lemma eventually_dec_lt {u : ℕ → ℝ} (hu : Antitone u) (hb : ∀ t, 0 ≤ u t) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ t in atTop, u t - u (t + 1) < ε := by
  have hT := tendsto_atTop_ciInf hu ⟨0, by rintro _ ⟨t, rfl⟩; exact hb t⟩
  have h2 : Tendsto (fun t => u t - u (t + 1)) atTop (𝓝 0) := by
    have := hT.sub (hT.comp (tendsto_add_atTop_nat 1))
    simpa using this
  exact h2.eventually (gt_mem_nhds hε)

/-- The limit of the covariance process. -/
lemma SigmaC_tendsto (hS : S₁.PosSemidef) :
    ∃ L : M2, Tendsto (SigmaC κ S₁ γ) atTop (𝓝 L) ∧ L 1 0 = L 0 1 ∧ PSDE L := by
  have hP := SigmaC_PSDE (κ := κ) (γ := γ) hS
  have ha := tendsto_atTop_ciInf (SigmaC_anti00 (κ := κ) (γ := γ) hS)
    ⟨0, by rintro _ ⟨t, rfl⟩; exact (hP t).1⟩
  have hc := tendsto_atTop_ciInf (SigmaC_anti11 (κ := κ) (γ := γ) hS)
    ⟨0, by rintro _ ⟨t, rfl⟩; exact (hP t).2.1⟩
  have hs := tendsto_atTop_ciInf (SigmaC_antiSum (κ := κ) (γ := γ) hS)
    ⟨0, by rintro _ ⟨t, rfl⟩; exact sum_nonneg_of_PSDE (hP t)⟩
  set a := ⨅ t, SigmaC κ S₁ γ t 0 0
  set c := ⨅ t, SigmaC κ S₁ γ t 1 1
  set s := ⨅ t, (SigmaC κ S₁ γ t 0 0 + 2 * SigmaC κ S₁ γ t 0 1 + SigmaC κ S₁ γ t 1 1)
  have hb : Tendsto (fun t => SigmaC κ S₁ γ t 0 1) atTop (𝓝 ((s - a - c) / 2)) := by
    have := ((hs.sub ha).sub hc).div_const 2
    refine this.congr fun t => ?_
    ring
  have hb' : Tendsto (fun t => SigmaC κ S₁ γ t 1 0) atTop (𝓝 ((s - a - c) / 2)) :=
    hb.congr fun t => (SigmaC_sym hS t).symm
  refine ⟨!![a, (s - a - c) / 2; (s - a - c) / 2, c], ?_, by simp, ?_⟩
  · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simpa
  · refine ⟨by simpa using ge_of_tendsto' ha fun t => (hP t).1,
      by simpa using ge_of_tendsto' hc fun t => (hP t).2.1, ?_⟩
    have hdet : Tendsto (fun t => SigmaC κ S₁ γ t 0 0 * SigmaC κ S₁ γ t 1 1 -
        SigmaC κ S₁ γ t 0 1 ^ 2) atTop (𝓝 (a * c - ((s - a - c) / 2) ^ 2)) :=
      (ha.mul hc).sub (hb.pow 2)
    have := ge_of_tendsto' hdet fun t => sub_nonneg.2 (hP t).2.2
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    linarith

/-- If eventually no date is revealing, `Σ_t` is eventually constant. -/
lemma SigmaC_const_of_pool {T : ℕ} (h : ∀ t, T ≤ t → ¬ revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)) :
    ∀ t, T ≤ t → SigmaC κ S₁ γ t = SigmaC κ S₁ γ T := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => rw [SigmaC_succ_pool κ γ S₁ (h t ht), ih]

/-- If every late revealing date lowers `σ²_θ` by at least `δ > 0`, then eventually every date is
pooling and `Σ_t` is constant. -/
lemma eventually_pool_of_dec (hS : S₁.PosSemidef) {δ : ℝ} (hδ : 0 < δ)
    (hdec : ∀ᶠ t in atTop, revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) →
      δ ≤ F0E (SigmaC κ S₁ γ t) (γ t) ^ 2 / vZE (SigmaC κ S₁ γ t) (γ t)) :
    ∃ T, ∀ t, T ≤ t → ¬ revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) ∧
      SigmaC κ S₁ γ t = SigmaC κ S₁ γ T := by
  have h2 := eventually_dec_lt (SigmaC_anti00 (κ := κ) (γ := γ) hS)
    (fun t => (SigmaC_PSDE (κ := κ) (γ := γ) hS t).1) hδ
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hdec.and h2)
  have hpool : ∀ t, T ≤ t → ¬ revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) := by
    intro t ht hrev
    obtain ⟨h1, h3⟩ := hT t ht
    have := h1 hrev
    rw [(SigmaC_step hS t hrev).1] at h3
    linarith
  exact ⟨T, fun t ht => ⟨hpool t ht, SigmaC_const_of_pool hpool t ht⟩⟩

end Basic

/-! ### Counting revealing dates -/

lemma revCount_succ (κ γ : ℕ → ℝ) (S₁ : M2) (t : ℕ) :
    haveI := Classical.propDecidable (revCrit (κ t) (SigmaC κ S₁ γ t) (γ t))
    revCount κ S₁ γ (t + 1) = revCount κ S₁ γ t +
      if revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) then 1 else 0 := by
  classical
  simp only [revCount, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma card_filter_le_of_imp {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (T t : ℕ)
    (h : ∀ s, T ≤ s → p s → q s) :
    ((Finset.range t).filter p).card ≤ T + ((Finset.range t).filter q).card := by
  calc ((Finset.range t).filter p).card
      ≤ (Finset.range T ∪ (Finset.range t).filter q).card := by
        apply Finset.card_le_card
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_range] at hs
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_filter]
        by_cases hsT : s < T
        · exact Or.inl hsT
        · exact Or.inr ⟨hs.1, h s (not_lt.1 hsT) hs.2⟩
    _ ≤ (Finset.range T).card + ((Finset.range t).filter q).card := Finset.card_union_le _ _
    _ = T + ((Finset.range t).filter q).card := by rw [Finset.card_range]

lemma revCount_le_of_imp (κ γ : ℕ → ℝ) (S₁ : M2) {q : ℕ → Prop} [DecidablePred q] (T t : ℕ)
    (h : ∀ s, T ≤ s → revCrit (κ s) (SigmaC κ S₁ γ s) (γ s) → q s) :
    revCount κ S₁ γ t ≤ T + ((Finset.range t).filter q).card := by
  classical
  unfold revCount
  exact card_filter_le_of_imp T t h

lemma le_revCount_of_imp (κ γ : ℕ → ℝ) (S₁ : M2) {q : ℕ → Prop} [DecidablePred q] (T t : ℕ)
    (h : ∀ s, T ≤ s → q s → revCrit (κ s) (SigmaC κ S₁ γ s) (γ s)) :
    ((Finset.range t).filter q).card ≤ T + revCount κ S₁ γ t := by
  classical
  unfold revCount
  exact card_filter_le_of_imp T t h

lemma revCount_le_of_pool (κ γ : ℕ → ℝ) (S₁ : M2) (T t : ℕ)
    (h : ∀ s, T ≤ s → ¬ revCrit (κ s) (SigmaC κ S₁ γ s) (γ s)) :
    revCount κ S₁ γ t ≤ T := by
  have := revCount_le_of_imp κ γ S₁ (q := fun _ => False) T t (fun s hs hr => h s hs hr)
  simpa using this

end CC

namespace CC

open Matrix Filter Topology Set

lemma loadA_dot_pos {S : M2} (h : S.PosSemidef) (γ : ℝ) :
    0 < loadA S γ ⬝ᵥ loadA S γ := by
  have hP := psd_PSDE h
  rw [loadA_eq (sym_of_psd h) (dE_ne hP)]
  have := A_pos hP γ
  simp [dotProduct, Fin.sum_univ_two]; nlinarith

lemma kalman_diag_pos {S : M2} (h : S.PosSemidef) (γ : ℝ) (i : Fin 2) (hi : 0 < S i i) :
    0 < kalman S γ i i := by
  have hP := psd_PSDE h
  have hs := sym_of_psd h
  have hd := dE_ne hP
  have K := kal_real hP.1 hP.2.1 hP.2.2 (A_pos hP γ)
  simp only at K
  obtain ⟨-, -, -, ha, hc, -⟩ := K
  have hv := vZE_pos hP γ
  have hn := A_pos hP γ
  fin_cases i
  · simp only [Fin.zero_eta] at hi ⊢
    rw [kalman00 hs hd]
    exact lt_of_lt_of_le (by positivity) ha
  · simp only [Fin.mk_one] at hi ⊢
    rw [kalman11 hs hd]
    exact lt_of_lt_of_le (by positivity) hc

/-- `2|C| ≤ tr Σ`. -/
lemma two_abs_off_le {S : M2} (hP : PSDE S) : 2 * |S 0 1| ≤ S 0 0 + S 1 1 := by
  obtain ⟨h0, h1, hb⟩ := hP
  rcases abs_cases (S 0 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    nlinarith [sq_nonneg (S 0 0 - S 1 1), sq_nonneg (S 0 0 + S 1 1), add_nonneg h0 h1]

/-- `Var(Z_t | h^t)` is bounded above on `γ ∈ [0,1]`. -/
lemma vZE_le {S : M2} (hP : PSDE S) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    vZE S γ ≤ 1 + 2 * (S 0 0 + S 1 1) := by
  rw [vZE_expand hP]
  have hH := HE_le hP
  have hH0 := HE_nonneg hP
  have h2 := two_abs_off_le hP
  have h3 : 2 * γ * S 0 1 ≤ 2 * |S 0 1| := by
    nlinarith [le_abs_self (S 0 1), abs_nonneg (S 0 1), neg_abs_le (S 0 1)]
  have hγ2 : γ ^ 2 ≤ 1 := by nlinarith
  have h4 : γ ^ 2 * HE S ≤ HE S := by nlinarith [mul_le_mul_of_nonneg_right hγ2 hH0]
  linarith

section Revealing

variable {κ γ : ℕ → ℝ} {S₁ : M2}

/-- Taking traces in the update, `∑_{t ∈ ℛ} ‖Σ_t A_t‖²/Var(Z_t | h^t) ≤ tr Σ₁`, along a sequence
`φ` of revealing dates (proof of Proposition 2, Case 1). -/
lemma sum_DE_le (hS : S₁.PosSemidef) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hrev : ∀ n, revCrit (κ (φ n)) (SigmaC κ S₁ γ (φ n)) (γ (φ n))) (N : ℕ) :
    ∑ n ∈ Finset.range N, DE (SigmaC κ S₁ γ (φ n)) (γ (φ n)) ≤
      (SigmaC κ S₁ γ (φ 0)).trace - (SigmaC κ S₁ γ (φ N)).trace := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h1 := (SigmaC_step hS (φ N) (hrev N)).2.2.1
    have h2 := SigmaC_antiTrace (κ := κ) (γ := γ) hS
      (show φ N + 1 ≤ φ (N + 1) from hφ (Nat.lt_succ_self N))
    simp only at h2
    linarith

/-- `Σ_t A_t → 0` along a sequence of revealing dates (proof of Proposition 2, Case 1). -/
lemma FA_tendsto (hS : S₁.PosSemidef) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hrev : ∀ n, revCrit (κ (φ n)) (SigmaC κ S₁ γ (φ n)) (γ (φ n)))
    (hγ : ∀ n, γ (φ n) ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => F0E (SigmaC κ S₁ γ (φ n)) (γ (φ n))) atTop (𝓝 0) ∧
      Tendsto (fun n => F1E (SigmaC κ S₁ γ (φ n)) (γ (φ n))) atTop (𝓝 0) := by
  have hP := SigmaC_PSDE (κ := κ) (γ := γ) hS
  have htr0 : ∀ t, 0 ≤ (SigmaC κ S₁ γ t).trace := fun t => by
    rw [trace_fin_two]; exact add_nonneg (hP t).1 (hP t).2.1
  have htr : ∀ t, (SigmaC κ S₁ γ t).trace ≤ S₁.trace := fun t =>
    SigmaC_antiTrace (κ := κ) (γ := γ) hS (Nat.zero_le t)
  have hsum : Summable fun n => DE (SigmaC κ S₁ γ (φ n)) (γ (φ n)) :=
    summable_of_sum_range_le (c := S₁.trace) (fun n => DE_nonneg (hP _) _) fun N => by
      have := sum_DE_le hS hφ hrev N
      linarith [htr (φ 0), htr0 (φ N)]
  -- `Var(Z_t | h^t)` is bounded above, so `‖Σ_t A_t‖² → 0`
  have hsq : Tendsto (fun n => F0E (SigmaC κ S₁ γ (φ n)) (γ (φ n)) ^ 2 +
      F1E (SigmaC κ S₁ γ (φ n)) (γ (φ n)) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hsum.tendsto_atTop_zero.const_mul (1 + 2 * S₁.trace))
    have hv := vZE_pos (hP (φ n)) (γ (φ n))
    have hle := vZE_le (hP (φ n)) (hγ n).1 (hγ n).2
    have htn := htr (φ n)
    rw [trace_fin_two] at htn
    have hS1 : vZE (SigmaC κ S₁ γ (φ n)) (γ (φ n)) ≤ 1 + 2 * S₁.trace := by linarith
    calc _ = vZE (SigmaC κ S₁ γ (φ n)) (γ (φ n)) * DE (SigmaC κ S₁ γ (φ n)) (γ (φ n)) := by
          rw [DE]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hS1 (DE_nonneg (hP _) _)
  have key : ∀ f g : ℕ → ℝ, Tendsto (fun n => f n ^ 2 + g n ^ 2) atTop (𝓝 0) →
      Tendsto f atTop (𝓝 0) := fun f g h => by
    have h2 : Tendsto (fun n => f n ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _) (fun n => by nlinarith [sq_nonneg (g n)]) h
    have h3 := h2.sqrt
    simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h3
    exact (tendsto_zero_iff_abs_tendsto_zero f).2 h3
  refine ⟨key _ (fun n => F1E (SigmaC κ S₁ γ (φ n)) (γ (φ n))) hsq,
    key _ (fun n => F0E (SigmaC κ S₁ γ (φ n)) (γ (φ n))) ?_⟩
  simpa only [add_comm] using hsq

end Revealing

/-- Case 1 of Proposition 2, for `κ_t ≥ κ₀ > κck` and `γ_t ∈ [0,1]`: there is a finite time after
which every period is pooling. If the set of revealing dates were infinite, `Σ_t A_t → 0` along it,
so `s̃ → 1` along it, contradicting Corollary 1. -/
lemma high_core_gen {κ γ : ℕ → ℝ} {S₁ : M2} (hS : S₁.PosSemidef) {κ₀ : ℝ} (hκ₀ : κck < κ₀)
    (hκ : ∀ t, κ₀ ≤ κ t) (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) :
    ∃ T, ∀ t, T ≤ t → ¬ revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) ∧
      SigmaC κ S₁ γ t = SigmaC κ S₁ γ T := by
  have hκ0 : 0 < κ₀ := lt_trans κck_pos hκ₀
  have hP := SigmaC_PSDE (κ := κ) (γ := γ) hS
  have hr1 : κck / κ₀ < 1 := by rw [div_lt_one hκ0]; exact hκ₀
  have hfin : ∃ T, ∀ t, T ≤ t → ¬ revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) := by
    by_contra hinf
    push Not at hinf
    have hfreq : ∃ᶠ t in atTop, revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) :=
      frequently_atTop.2 hinf
    obtain ⟨φ, hφ, hrev⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨h0, -⟩ := FA_tendsto hS hφ hrev fun n => hγ _
    -- `1 - s̃ = γ_t (Σ_t A_t)₁/Var(Z_t | h^t)` and `Var(Z_t | h^t) ≥ 1/4`, so `s̃ → 1` along `ℛ`
    have h1 : Tendsto (fun n => 1 - sensE (SigmaC κ S₁ γ (φ n)) (γ (φ n))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n => 4 * |F0E (SigmaC κ S₁ γ (φ n)) (γ (φ n))|)
        (fun n => ?_) (by simpa using (h0.abs).const_mul 4)
      have hv := vZE_ge_quarter (hP (φ n)) (γ (φ n)) (hγ _).1 (hγ _).2
      have hv0 : 0 < vZE (SigmaC κ S₁ γ (φ n)) (γ (φ n)) := by linarith
      rw [one_sub_sensE (hP (φ n)), Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hv0,
        abs_of_nonneg (hγ (φ n)).1, div_le_iff₀ hv0]
      have h01 := (hγ (φ n)).2
      have ha := abs_nonneg (F0E (SigmaC κ S₁ γ (φ n)) (γ (φ n)))
      nlinarith [mul_le_of_le_one_left ha h01, (hγ (φ n)).1, mul_nonneg ha (sub_nonneg.2 hv)]
    have hs1 : Tendsto (fun n => sensE (SigmaC κ S₁ γ (φ n)) (γ (φ n)) ^ 2) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n => sensE (SigmaC κ S₁ γ (φ n)) (γ (φ n))) atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
        simpa using this
      simpa using h2.pow 2
    obtain ⟨n, hn⟩ := (hs1.eventually (lt_mem_nhds hr1)).exists
    -- Corollary 1 at the revealing date `φ n`
    have hle : κ (φ n) * sens (SigmaC κ S₁ γ (φ n)) (γ (φ n)) ^ 2 ≤ κck := hrev n
    rw [sens_eq_sensE (SigmaC_sym hS _) (dE_ne (hP _))] at hle
    have : sensE (SigmaC κ S₁ γ (φ n)) (γ (φ n)) ^ 2 ≤ κck / κ₀ := by
      rw [le_div_iff₀ hκ0]
      nlinarith [sq_nonneg (sensE (SigmaC κ S₁ γ (φ n)) (γ (φ n))), hκ (φ n)]
    linarith
  obtain ⟨T, hT⟩ := hfin
  exact ⟨T, fun t ht => ⟨hT t ht, SigmaC_const_of_pool hT t ht⟩⟩

end CC
