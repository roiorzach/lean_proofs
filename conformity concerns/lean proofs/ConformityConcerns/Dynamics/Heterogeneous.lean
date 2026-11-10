import ConformityConcerns.Dynamics.Accounting
import ConformityConcerns.Dynamics.LongRun
import ConformityConcerns.Dynamics.LemmasRate

/-!
# Proposition A1 (Heterogeneous Conformity Concerns)

`(κ_t, γ_t)` are i.i.d. pairs with law `Gκ ⊗ Gγ` (so `κ_t` and `γ_t` are independent of each
other and over time), publicly observed; period `t` is revealing iff `κ_t s̃(h^t)² ≤ κck`.
-/

namespace CC

open Matrix Filter Topology Set MeasureTheory

/-- The covariance process driven by the realised pairs `ω t = (κ_t, γ_t)`. -/
noncomputable def SigmaH (S₁ : M2) (ω : ℕ → ℝ × ℝ) : ℕ → M2 :=
  SigmaC (fun t => (ω t).1) S₁ (fun t => (ω t).2)

/-- `N_t` for the process driven by `ω`. -/
noncomputable def revCountH (S₁ : M2) (ω : ℕ → ℝ × ℝ) (t : ℕ) : ℕ :=
  revCount (fun t => (ω t).1) S₁ (fun t => (ω t).2) t

/-- Late dates: `κ_t < κck - η` forces revelation and revelation forces `κ_t ≤ κck + η`, once
`Σ_t` is close to zero. -/
lemma sandwich_eventually {S₁ : M2} (hS : S₁.PosSemidef) {κ γ : ℕ → ℝ}
    (hκpos : ∀ t, 0 < κ t) (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (SigmaC κ S₁ γ) atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, (κ t < κck - η → revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)) ∧
      (revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) → κ t ≤ κck + η) := by
  have hP := SigmaC_PSDE (κ := κ) (γ := γ) hS
  have hsym := SigmaC_sym (κ := κ) (γ := γ) hS
  have hk := κck_pos
  set β₀ := min (1 / 2) (η / (4 * (κck + η))) with hβ₀
  have hβ0 : 0 < β₀ := lt_min (by norm_num) (by positivity)
  have hβ1 : β₀ ≤ 1 / 2 := min_le_left _ _
  have hβ2 : β₀ * (4 * (κck + η)) ≤ η := by
    have := min_le_right (1 / 2) (η / (4 * (κck + η)))
    rw [← hβ₀] at this
    rwa [le_div_iff₀ (by positivity)] at this
  have ha0 : Tendsto (fun t => SigmaC κ S₁ γ t 0 0) atTop (𝓝 0) := by
    simpa using tendsto_entry hlim 0 0
  have hb0 : Tendsto (fun t => |SigmaC κ S₁ γ t 0 1|) atTop (𝓝 0) := by
    simpa using (tendsto_entry hlim 0 1).abs
  have ha := ha0.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < β₀ / 8))
  have hb := hb0.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < min (1 / 4) (β₀ / 8)))
  filter_upwards [ha, hb] with t hat hbt
  have hb1 : |SigmaC κ S₁ γ t 0 1| ≤ 1 / (4 * 1) :=
    le_trans hbt.le (le_trans (min_le_left _ _) (by norm_num))
  have hb2 : |SigmaC κ S₁ γ t 0 1| ≤ β₀ / 8 := le_trans hbt.le (min_le_right _ _)
  have hclose := sens_close (hP t) one_pos (hγ t).1 (hγ t).2 hb1
  have hs1 : |1 - sensE (SigmaC κ S₁ γ t) (γ t)| ≤ β₀ := by
    have := (hP t).1
    nlinarith
  rw [abs_le] at hs1
  set s := sensE (SigmaC κ S₁ γ t) (γ t)
  have hrev_iff : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) ↔ κ t * s ^ 2 ≤ κck := by
    show κ t * sens (SigmaC κ S₁ γ t) (γ t) ^ 2 ≤ κck ↔ _
    rw [sens_eq_sensE (hsym t) (dE_ne (hP t))]
  have hkt := hκpos t
  refine ⟨fun hlt => hrev_iff.2 ?_, fun hrev => ?_⟩
  · have hs2 : s ^ 2 ≤ 1 + 3 * β₀ := by nlinarith
    have : κ t * s ^ 2 ≤ κ t * (1 + 3 * β₀) := mul_le_mul_of_nonneg_left hs2 hkt.le
    nlinarith
  · have h := hrev_iff.1 hrev
    have hs2 : 1 - 2 * β₀ ≤ s ^ 2 := by nlinarith
    by_contra hgt
    push Not at hgt
    have : κ t * (1 - 2 * β₀) ≤ κ t * s ^ 2 := mul_le_mul_of_nonneg_left hs2 hkt.le
    nlinarith

/-- The frequency of revealing dates converges to `ε` (pathwise). -/
lemma freq_path {S₁ : M2} (hS : S₁.PosSemidef) {κ γ : ℕ → ℝ}
    (hκpos : ∀ t, 0 < κ t) (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (SigmaC κ S₁ γ) atTop (𝓝 0)) {ε : ℝ} {α β : ℕ → ℝ}
    (hα : Tendsto α atTop (𝓝 ε)) (hβ : Tendsto β atTop (𝓝 ε))
    (hlow : ∀ n : ℕ, Tendsto (fun t : ℕ => (∑ i ∈ Finset.range t,
      (Iio (κck - 1 / ((n : ℝ) + 1))).indicator (fun _ => (1 : ℝ)) (κ i)) / t) atTop (𝓝 (α n)))
    (hupp : ∀ n : ℕ, Tendsto (fun t : ℕ => (∑ i ∈ Finset.range t,
      (Iic (κck + 1 / ((n : ℝ) + 1))).indicator (fun _ => (1 : ℝ)) (κ i)) / t) atTop (𝓝 (β n))) :
    Tendsto (fun t : ℕ => (revCount κ S₁ γ t : ℝ) / t) atTop (𝓝 ε) := by
  refine tendsto_order.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨n, hn⟩ := (hα.eventually (lt_mem_nhds hx)).exists
    obtain ⟨T, hT⟩ := eventually_atTop.1
      (sandwich_eventually hS hκpos hγ hlim (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    have hcount : ∀ t, (∑ i ∈ Finset.range t, (Iio (κck - 1 / ((n : ℝ) + 1))).indicator
        (fun _ => (1 : ℝ)) (κ i)) ≤ T + revCount κ S₁ γ t := by
      intro t
      classical
      have := le_revCount_of_imp κ γ S₁ (q := fun s => κ s ∈ Iio (κck - 1 / ((n : ℝ) + 1))) T t
        fun s hs hq => (hT s hs).1 hq
      rw [sum_indicator_eq_card]; exact_mod_cast this
    have hlim2 := (hlow n).sub (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ))
    rw [sub_zero] at hlim2
    filter_upwards [hlim2.eventually (lt_mem_nhds hn), eventually_gt_atTop 0] with t ht ht0
    have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
    have := hcount t
    rw [← sub_div, lt_div_iff₀ ht0'] at ht
    rw [lt_div_iff₀ ht0']
    linarith
  · obtain ⟨n, hn⟩ := (hβ.eventually (gt_mem_nhds hx)).exists
    obtain ⟨T, hT⟩ := eventually_atTop.1
      (sandwich_eventually hS hκpos hγ hlim (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    have hcount : ∀ t, (revCount κ S₁ γ t : ℝ) ≤ T + ∑ i ∈ Finset.range t,
        (Iic (κck + 1 / ((n : ℝ) + 1))).indicator (fun _ => (1 : ℝ)) (κ i) := by
      intro t
      classical
      have := revCount_le_of_imp κ γ S₁ (q := fun s => κ s ∈ Iic (κck + 1 / ((n : ℝ) + 1))) T t
        fun s hs hr => (hT s hs).2 hr
      rw [sum_indicator_eq_card]; exact_mod_cast this
    have hlim2 := (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).add (hupp n)
    rw [zero_add] at hlim2
    filter_upwards [hlim2.eventually (gt_mem_nhds hn), eventually_gt_atTop 0] with t ht ht0
    have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
    have := hcount t
    rw [← add_div, div_lt_iff₀ ht0'] at ht
    rw [div_lt_iff₀ ht0']
    linarith

/-- **Proposition A1.** Let `κ_t` be i.i.d. with law `Gκ` on `(0,∞)`, `ε = Pr(κ_t < κck)`, and
`Gκ({κck}) = 0`. If `ε > 0`, social learning about preferences and fundamentals occurs,
`N_t/t → ε` almost surely, and `liminf ε t min{σ²_θ,t, σ²_μ,t} ≥ 1` almost surely. If
`inf Supp(κ_t) > κck`, social learning fails (finitely many revealing dates). -/
theorem propA1 (Gκ Gγ : Measure ℝ) [IsProbabilityMeasure Gκ] (hκpos : Gκ (Iic 0) = 0)
    (hatom : Gκ {κck} = 0) (hGγ : FullSupportUnit Gγ) (S₁ : M2) (hS : S₁.PosDef) :
    let P := Measure.infinitePi fun _ : ℕ => Gκ.prod Gγ
    let ε := (Gκ (Iio κck)).toReal
    (0 < ε → ∀ᵐ ω ∂P,
        Tendsto (SigmaH S₁ ω) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => (revCountH S₁ ω t : ℝ) / t) atTop (𝓝 ε) ∧
        ∀ c < 1, ∀ᶠ t : ℕ in atTop, c ≤ ε * t * min (SigmaH S₁ ω t 0 0) (SigmaH S₁ ω t 1 1)) ∧
    ((∃ κ₀, κck < κ₀ ∧ Gκ (Iio κ₀) = 0) → ∀ᵐ ω ∂P, ∃ T, ∃ Sinf : M2, Sinf.PosDef ∧
        ∀ t, T ≤ t → ¬ revCrit (ω t).1 (SigmaH S₁ ω t) (ω t).2 ∧ SigmaH S₁ ω t = Sinf) := by
  dsimp only
  have := hGγ.prob
  set μ := Gκ.prod Gγ with hμ
  have hfst : ∀ A : Set ℝ, μ (Prod.fst ⁻¹' A) = Gκ A := fun A => by
    rw [← Set.prod_univ, hμ, Measure.prod_prod, measure_univ, mul_one]
  have hsnd : ∀ A : Set ℝ, μ (Prod.snd ⁻¹' A) = Gγ A := fun A => by
    rw [← Set.univ_prod, hμ, Measure.prod_prod, measure_univ, one_mul]
  have hγae : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ), ∀ t, (ω t).2 ∈ Icc (0 : ℝ) 1 :=
    ae_forall_mem μ (s := Prod.snd ⁻¹' Icc 0 1) (measurable_snd measurableSet_Icc)
      (by rw [← preimage_compl, hsnd, hGγ.supp])
  refine ⟨fun hε => ?_, fun ⟨κ₀, hκ₀, h0⟩ => ?_⟩
  · -- choose `κ̄ < κck` charged by `Gκ`
    have hex : ∃ n : ℕ, 0 < Gκ (Iic (κck - 1 / ((n : ℝ) + 1))) := by
      by_contra hne
      push Not at hne
      have hsub : Iio κck ⊆ ⋃ n : ℕ, Iic (κck - 1 / ((n : ℝ) + 1)) := by
        intro x hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (mem_Iio.1 hx))
        exact mem_iUnion.2 ⟨n, by simp only [mem_Iic]; linarith⟩
      have h0 : Gκ (Iio κck) = 0 :=
        measure_mono_null hsub (measure_iUnion_null fun n => le_antisymm (hne n) zero_le)
      rw [h0] at hε; simp at hε
    obtain ⟨n₀, hn₀⟩ := hex
    set κbar := κck - 1 / ((n₀ : ℝ) + 1)
    have hκbar : κbar < κck := by
      have : (0 : ℝ) < 1 / ((n₀ : ℝ) + 1) := by positivity
      linarith
    have hκpos' : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ), ∀ t, (ω t).1 ∈ Ioi (0 : ℝ) :=
      ae_forall_mem μ (s := Prod.fst ⁻¹' Ioi 0) (measurable_fst measurableSet_Ioi)
        (by rw [← preimage_compl, compl_Ioi, hfst, hκpos])
    have hvis : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ), ∀ p q : ℚ, (0 : ℝ) ≤ p →
        (p : ℝ) < q → (q : ℝ) ≤ 1 → ∃ᶠ t in atTop, (ω t).1 ≤ κbar ∧ (ω t).2 ∈ Ioo (p : ℝ) q := by
      rw [ae_all_iff]; intro p; rw [ae_all_iff]; intro q
      by_cases hpq : (0 : ℝ) ≤ p ∧ (p : ℝ) < q ∧ (q : ℝ) ≤ 1
      · have hpos : 0 < μ (Iic κbar ×ˢ Ioo (p : ℝ) q) := by
          rw [hμ, Measure.prod_prod]
          exact ENNReal.mul_pos hn₀.ne' (hGγ.pos p q hpq.1 hpq.2.1 hpq.2.2).ne'
        filter_upwards [ae_frequently_mem μ (measurableSet_Iic.prod measurableSet_Ioo) hpos]
          with ω hω
        intro _ _ _
        exact hω.mono fun t ht => ⟨ht.1, ht.2⟩
      · exact ae_of_all _ fun ω h0 h1 h2 => absurd ⟨h0, h1, h2⟩ hpq
    have hlow : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ), ∀ n : ℕ,
        Tendsto (fun t : ℕ => (∑ i ∈ Finset.range t,
          (Iio (κck - 1 / ((n : ℝ) + 1))).indicator (fun _ => (1 : ℝ)) (ω i).1) / t) atTop
          (𝓝 (Gκ (Iio (κck - 1 / ((n : ℝ) + 1)))).toReal) := by
      rw [ae_all_iff]; intro n
      filter_upwards [slln_freq μ (measurable_fst (measurableSet_Iio
        (a := κck - 1 / ((n : ℝ) + 1))))] with ω hω
      rw [hfst] at hω
      exact hω
    have hupp : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ), ∀ n : ℕ,
        Tendsto (fun t : ℕ => (∑ i ∈ Finset.range t,
          (Iic (κck + 1 / ((n : ℝ) + 1))).indicator (fun _ => (1 : ℝ)) (ω i).1) / t) atTop
          (𝓝 (Gκ (Iic (κck + 1 / ((n : ℝ) + 1)))).toReal) := by
      rw [ae_all_iff]; intro n
      filter_upwards [slln_freq μ (measurable_fst (measurableSet_Iic
        (a := κck + 1 / ((n : ℝ) + 1))))] with ω hω
      rw [hfst] at hω
      exact hω
    -- the limits of the two families of probabilities
    have hα : Tendsto (fun n : ℕ => (Gκ (Iio (κck - 1 / ((n : ℝ) + 1)))).toReal) atTop
        (𝓝 (Gκ (Iio κck)).toReal) := by
      have hmono : Monotone fun n : ℕ => Iio (κck - 1 / ((n : ℝ) + 1)) := by
        intro m n hmn x hx
        simp only [mem_Iio] at hx ⊢
        have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
        linarith
      have hU : (⋃ n : ℕ, Iio (κck - 1 / ((n : ℝ) + 1))) = Iio κck := by
        ext x; simp only [mem_iUnion, mem_Iio]
        constructor
        · rintro ⟨n, hn⟩; have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith
        · intro hx
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
          exact ⟨n, by linarith⟩
      have := tendsto_measure_iUnion_atTop (μ := Gκ) hmono
      rw [hU] at this
      exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
    have hβ : Tendsto (fun n : ℕ => (Gκ (Iic (κck + 1 / ((n : ℝ) + 1)))).toReal) atTop
        (𝓝 (Gκ (Iio κck)).toReal) := by
      have hanti : Antitone fun n : ℕ => Iic (κck + 1 / ((n : ℝ) + 1)) := by
        intro m n hmn x hx
        simp only [mem_Iic] at hx ⊢
        have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
        linarith
      have hI : (⋂ n : ℕ, Iic (κck + 1 / ((n : ℝ) + 1))) = Iic κck := by
        ext x; simp only [mem_iInter, mem_Iic]
        constructor
        · intro h
          by_contra hx; push Not at hx
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
          have := h n; linarith
        · intro hx n; have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith
      have := tendsto_measure_iInter_atTop (μ := Gκ)
        (fun n => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
      rw [hI] at this
      have hIic : Gκ (Iic κck) = Gκ (Iio κck) := by
        apply le_antisymm
        · rw [← Iio_union_right]
          calc Gκ (Iio κck ∪ {κck}) ≤ Gκ (Iio κck) + Gκ {κck} := measure_union_le _ _
            _ = Gκ (Iio κck) := by rw [hatom, add_zero]
        · exact measure_mono Iio_subset_Iic_self
      rw [hIic] at this
      exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
    filter_upwards [hγae, hκpos', hvis, hlow, hupp] with ω hγω hκω hvω hlω huω
    have hlim : Tendsto (SigmaH S₁ ω) atTop (𝓝 0) :=
      learning_core hS.posSemidef hκbar fun a b ha hab hb =>
        visits_of_rat hvω a b ha.le hab hb
    have hfreq := freq_path hS.posSemidef (κ := fun t => (ω t).1) (γ := fun t => (ω t).2)
      (fun t => hκω t) hγω hlim hα hβ hlω huω
    refine ⟨hlim, hfreq, fun c hc => ?_⟩
    exact final_bound (trace_inv_pos hS) hε.le
      (lemmaA1_bound (fun t => (ω t).1) (fun t => (ω t).2) S₁ hS)
      (key_of_le hε le_rfl hc (Eventually.of_forall fun t => le_rfl) hfreq
        (trace_inv_pos hS).le)
  · -- `inf Supp κ_t > κck`: finitely many revealing dates
    have hκae : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ), ∀ t, (ω t).1 ∈ Ici κ₀ :=
      ae_forall_mem μ (s := Prod.fst ⁻¹' Ici κ₀) (measurable_fst measurableSet_Ici)
        (by rw [← preimage_compl, compl_Ici, hfst, h0])
    filter_upwards [hγae, hκae] with ω hγω hκω
    obtain ⟨T, hT⟩ := high_core_gen (κ := fun t => (ω t).1) (γ := fun t => (ω t).2)
      hS.posSemidef hκ₀ (fun t => hκω t) hγω
    exact ⟨T, SigmaH S₁ ω T, SigmaC_pd _ _ _ hS T, hT⟩

end CC
