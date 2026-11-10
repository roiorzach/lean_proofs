import ConformityConcerns.Dynamics.Accounting
import ConformityConcerns.Dynamics.LongRun
import ConformityConcerns.Dynamics.LemmasRate

/-!
# Proposition A2 (Unbounded Stakes)
-/

namespace CC

open Matrix Filter Topology Set MeasureTheory

/-- The pathwise part of Proposition A2: for a weight sequence in `[0,∞)` whose frequency of
exceeding `γ̄` converges to `ε > 0`. -/
lemma propA2_path {κ : ℝ} (hκ : κck < κ) {S₁ : M2} (hS : S₁.PosDef) {γ : ℕ → ℝ}
    (hγ0 : ∀ t, 0 ≤ γ t) {γbar ε : ℝ} (hγbar : 0 < γbar) (hε : 0 < ε)
    (hfreq : Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range n, (Ioi γbar).indicator (fun _ => (1 : ℝ)) (γ i)) / n) atTop (𝓝 ε)) :
    ∀ c < 1, ∀ᶠ t : ℕ in atTop,
      c ≤ ε * t * min (SigmaC (fun _ => κ) S₁ γ t 0 0) (SigmaC (fun _ => κ) S₁ γ t 1 1) := by
  intro c hc
  have hPSD : S₁.PosSemidef := hS.posSemidef
  have hP := SigmaC_PSDE (κ := fun _ => κ) (γ := γ) hPSD
  have hsym := SigmaC_sym (κ := fun _ => κ) (γ := γ) hPSD
  have hS₁P := psd_PSDE hPSD
  set L := (S₁⁻¹).trace
  have hL : 0 < L := trace_inv_pos hS
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  set r := κck / κ with hr
  have hr1 : r < 1 := (div_lt_one hκ0).2 hκ
  set m := (1 - r) / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hsr : ∀ t, revCrit κ (SigmaC (fun _ => κ) S₁ γ t) (γ t) →
      sensE (SigmaC (fun _ => κ) S₁ γ t) (γ t) ^ 2 ≤ r := fun t h =>
    sensE_sq_le hκ0 le_rfl (hsym t) (hP t) h
  refine final_bound hL hε.le (lemmaA1_bound (fun _ => κ) γ S₁ hS) ?_
  by_cases hq : ∃ q > 0, ∀ t, q ≤ SigmaC (fun _ => κ) S₁ γ t 0 0
  · -- `σ²_θ` stays away from zero: finitely many revealing dates
    obtain ⟨q, hq0, hqt⟩ := hq
    set D := (1 + S₁ 0 0) * (1 + S₁ 1 1) with hD
    have hS00 := hS₁P.1
    have hS11 := hS₁P.2.1
    have hD0 : 0 < D := by positivity
    have hk : ∀ t, q / D ≤ k00E (SigmaC (fun _ => κ) S₁ γ t) := by
      intro t
      have ha := SigmaC_anti00 (κ := fun _ => κ) (γ := γ) hPSD (Nat.zero_le t)
      have hc := SigmaC_anti11 (κ := fun _ => κ) (γ := γ) hPSD (Nat.zero_le t)
      simp only at ha hc
      refine le_trans ?_ (k00E_ge (hP t))
      have hdpos := dE_pos (hP t)
      have hdD : dE (SigmaC (fun _ => κ) S₁ γ t) ≤ D := by
        have h1 := (hP t).1; have h2 := (hP t).2.1
        simp only [dE, hD]
        have : (SigmaC (fun _ => κ) S₁ γ t) 0 0 ≤ S₁ 0 0 := ha
        have : (SigmaC (fun _ => κ) S₁ γ t) 1 1 ≤ S₁ 1 1 := hc
        nlinarith [sq_nonneg (SigmaC (fun _ => κ) S₁ γ t 0 1)]
      calc q / D ≤ SigmaC (fun _ => κ) S₁ γ t 0 0 / D := by gcongr; exact hqt t
        _ ≤ SigmaC (fun _ => κ) S₁ γ t 0 0 / dE (SigmaC (fun _ => κ) S₁ γ t) :=
          div_le_div_of_nonneg_left (hP t).1 hdpos hdD
    have hδ : 0 < m ^ 2 * (q / D) ^ 2 := by positivity
    obtain ⟨T, hT⟩ := eventually_pool_of_dec hPSD hδ (Eventually.of_forall fun t hrev => by
      refine le_trans ?_ (rev_dec_gen (hP t) hr1 (hsr t hrev))
      have h0 : 0 ≤ q / D := by positivity
      have := pow_le_pow_left₀ h0 (hk t) 2
      exact mul_le_mul_of_nonneg_left this (sq_nonneg _))
    refine key_of_le (M := fun _ => (T : ℝ)) hε hε.le hc (Eventually.of_forall fun t => ?_)
      ?_ hL.le
    · exact_mod_cast revCount_le_of_pool _ _ _ T t fun s hs => (hT s hs).1
    · exact tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)
  · -- `σ²_θ → 0`: late revealing dates have `γ_t > γ̄`
    push Not at hq
    have ha : ∀ q > 0, ∀ᶠ t in atTop, SigmaC (fun _ => κ) S₁ γ t 0 0 < q := fun q hq0 => by
      obtain ⟨t0, ht0⟩ := hq q hq0
      exact eventually_atTop.2 ⟨t0, fun t ht =>
        lt_of_le_of_lt (SigmaC_anti00 (κ := fun _ => κ) (γ := γ) hPSD ht) ht0⟩
    have hb : ∀ β > 0, ∀ᶠ t in atTop, |SigmaC (fun _ => κ) S₁ γ t 0 1| < β := fun β hβ => by
      filter_upwards [ha (β ^ 2 / (S₁ 1 1 + 1)) (div_pos (by positivity)
        (by linarith [hS₁P.2.1]))] with t ht
      have hc1 := SigmaC_anti11 (κ := fun _ => κ) (γ := γ) hPSD (Nat.zero_le t)
      simp only at hc1
      have h11 : (0 : ℝ) < S₁ 1 1 + 1 := by linarith [hS₁P.2.1]
      apply abs_lt_of_sq_lt_sq _ hβ.le
      have h2 : SigmaC (fun _ => κ) S₁ γ t 0 0 * (S₁ 1 1 + 1) < β ^ 2 := by
        rwa [lt_div_iff₀ h11] at ht
      have : SigmaC (fun _ => κ) S₁ γ t 1 1 ≤ S₁ 1 1 + 1 := by
        have : SigmaC (fun _ => κ) S₁ γ t 1 1 ≤ S₁ 1 1 := hc1
        linarith
      calc SigmaC (fun _ => κ) S₁ γ t 0 1 ^ 2
          ≤ SigmaC (fun _ => κ) S₁ γ t 0 0 * SigmaC (fun _ => κ) S₁ γ t 1 1 := (hP t).2.2
        _ ≤ SigmaC (fun _ => κ) S₁ γ t 0 0 * (S₁ 1 1 + 1) :=
          mul_le_mul_of_nonneg_left this (hP t).1
        _ < β ^ 2 := h2
    have hgt : ∀ᶠ t in atTop, revCrit κ (SigmaC (fun _ => κ) S₁ γ t) (γ t) → γbar < γ t := by
      filter_upwards [ha (m / (8 * γbar ^ 2)) (by positivity),
        hb (min (1 / (4 * γbar)) (m / (8 * γbar))) (by positivity)] with t hat hbt hrev
      by_contra hle
      push Not at hle
      have hb1 : |SigmaC (fun _ => κ) S₁ γ t 0 1| ≤ 1 / (4 * γbar) :=
        le_trans hbt.le (min_le_left _ _)
      have hb2 : |SigmaC (fun _ => κ) S₁ γ t 0 1| ≤ m / (8 * γbar) :=
        le_trans hbt.le (min_le_right _ _)
      have h1 := sens_close (hP t) hγbar (hγ0 t) hle hb1
      have h2 := one_sub_ge_of_sq_le (hsr t hrev)
      have h3 : 2 * γbar * (|SigmaC (fun _ => κ) S₁ γ t 0 1| +
          γbar * SigmaC (fun _ => κ) S₁ γ t 0 0) < m := by
        have e1 : 2 * γbar * |SigmaC (fun _ => κ) S₁ γ t 0 1| ≤ m / 4 := by
          have := mul_le_mul_of_nonneg_left hb2 (by positivity : (0 : ℝ) ≤ 2 * γbar)
          have e : 2 * γbar * (m / (8 * γbar)) = m / 4 := by field_simp; ring
          linarith
        have e2 : 2 * γbar * (γbar * SigmaC (fun _ => κ) S₁ γ t 0 0) < m / 4 := by
          have := mul_lt_mul_of_pos_left hat (by positivity : (0 : ℝ) < 2 * γbar ^ 2)
          have e : 2 * γbar ^ 2 * (m / (8 * γbar ^ 2)) = m / 4 := by field_simp; ring
          nlinarith
        nlinarith
      have := le_abs_self (1 - sensE (SigmaC (fun _ => κ) S₁ γ t) (γ t))
      rw [← hm] at h2
      linarith
    obtain ⟨T, hT⟩ := eventually_atTop.1 hgt
    refine key_of_le (M := fun t => (T : ℝ) +
        ∑ i ∈ Finset.range t, (Ioi γbar).indicator (fun _ => (1 : ℝ)) (γ i))
      hε le_rfl hc (Eventually.of_forall fun t => ?_) ?_ hL.le
    · classical
      have := revCount_le_of_imp (fun _ => κ) γ S₁ (q := fun s => γ s ∈ Ioi γbar) T t
        fun s hs hr => hT s hs hr
      rw [sum_indicator_eq_card]
      exact_mod_cast this
    · have h := (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).add hfreq
      rw [zero_add] at h
      exact h.congr fun t => by rw [add_div]

/-- **Proposition A2.** Suppose `Σ₁ ≻ 0` and `κ > κck`. Let `(γ_t)` be i.i.d. with support in
`[0,∞)` and unbounded above, and `ε_γ̄ = Pr(γ_t > γ̄)`. Then for every `γ̄ > 0`,
`liminf ε_γ̄ t min{σ²_θ,t, σ²_μ,t} ≥ 1` almost surely (stated as: for every `c < 1`,
eventually `c ≤ ε_γ̄ t min{…}`). -/
theorem propA2 (κ : ℝ) (hκ : κck < κ) (S₁ : M2) (hS : S₁.PosDef) (G : Measure ℝ)
    [IsProbabilityMeasure G] (hG0 : G (Iio 0) = 0) (hunb : ∀ M : ℝ, 0 < G (Ioi M))
    (γbar : ℝ) (hγbar : 0 < γbar) :
    ∀ᵐ γ ∂(iidSeq G), ∀ c < 1, ∀ᶠ t : ℕ in atTop,
      c ≤ (G (Ioi γbar)).toReal * t *
        min (SigmaC (fun _ => κ) S₁ γ t 0 0) (SigmaC (fun _ => κ) S₁ γ t 1 1) := by
  have hε : 0 < (G (Ioi γbar)).toReal :=
    ENNReal.toReal_pos (hunb γbar).ne' (measure_ne_top _ _)
  have h1 := ae_forall_mem G (measurableSet_Ici (a := (0 : ℝ))) (by rw [compl_Ici]; exact hG0)
  have h2 := slln_freq G (measurableSet_Ioi (a := γbar))
  simp only [iidSeq]
  filter_upwards [h1, h2] with γ hγ0 hfreq
  exact propA2_path hκ hS (fun t => hγ0 t) hγbar hε hfreq

end CC
