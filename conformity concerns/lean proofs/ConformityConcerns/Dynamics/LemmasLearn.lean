import ConformityConcerns.Dynamics.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.ContinuousOn

/-!
# The learning argument (Case 2 of Proposition 2)

Continuity of the explicit belief formulas in `(Σ, γ)` and the deterministic learning core,
stated for an arbitrary sequence of conformity concerns `κ_t` (so that it also covers
Proposition A1).
-/

namespace CC

open Matrix Filter Topology Set

section Cont

variable {S : M2} {γ : ℝ}

lemma cE (i j : Fin 2) : Continuous fun p : M2 × ℝ => p.1 i j := continuous_fst.matrix_elem i j

lemma cont_dE : Continuous fun p : M2 × ℝ => dE p.1 := by
  have h0 := cE 0 0; have h1 := cE 0 1; have h2 := cE 1 1
  simp only [dE]; fun_prop

lemma ca_k00E (hd : dE S ≠ 0) : ContinuousAt (fun p : M2 × ℝ => k00E p.1) (S, γ) := by
  have h0 := cE 0 0; have h1 := cE 0 1; have h2 := cE 1 1
  simp only [k00E]
  exact ContinuousAt.div (by fun_prop) cont_dE.continuousAt hd

lemma ca_k01E (hd : dE S ≠ 0) : ContinuousAt (fun p : M2 × ℝ => k01E p.1) (S, γ) := by
  simp only [k01E]
  exact ContinuousAt.div (cE 0 1).continuousAt cont_dE.continuousAt hd

lemma ca_A0E (hd : dE S ≠ 0) : ContinuousAt (fun p : M2 × ℝ => A0E p.1 p.2) (S, γ) := by
  simp only [A0E]; exact continuousAt_snd.mul (ca_k00E hd)

lemma ca_A1E (hd : dE S ≠ 0) : ContinuousAt (fun p : M2 × ℝ => A1E p.1 p.2) (S, γ) := by
  simp only [A1E]; exact continuousAt_const.add (continuousAt_snd.mul (ca_k01E hd))

lemma ca_F0E (hd : dE S ≠ 0) : ContinuousAt (fun p : M2 × ℝ => F0E p.1 p.2) (S, γ) := by
  have h0 := (cE 0 0).continuousAt (x := (S, γ)); have h1 := (cE 0 1).continuousAt (x := (S, γ))
  have a0 := ca_A0E (γ := γ) hd; have a1 := ca_A1E (γ := γ) hd
  simp only [F0E]; fun_prop

lemma ca_F1E (hd : dE S ≠ 0) : ContinuousAt (fun p : M2 × ℝ => F1E p.1 p.2) (S, γ) := by
  have h1 := (cE 0 1).continuousAt (x := (S, γ)); have h2 := (cE 1 1).continuousAt (x := (S, γ))
  have a0 := ca_A0E (γ := γ) hd; have a1 := ca_A1E (γ := γ) hd
  simp only [F1E]; fun_prop

end Cont

/-- `Σ_∞ (e₂ + γ̄ᵢ K_∞ e₁) = 0` for two distinct `γ̄ᵢ` implies `Σ_∞ = 0`. Subtracting gives
`Σ_∞ K_∞ e₁ = Σ_∞² (Σ_∞ + I)⁻¹ e₁ = 0`. As this matrix has the same kernel as `Σ_∞`, `Σ_∞ e₁ = 0`.
Then `K_∞ e₁ = 0`, so `Σ_∞ e₂ = 0`. -/
lemma zero_of_F {L : M2} (hP : PSDE L) {g1 g2 : ℝ} (hne : g1 ≠ g2) (h1 : F0E L g1 = 0)
    (h1' : F1E L g1 = 0) (h2 : F0E L g2 = 0) (h2' : F1E L g2 = 0) :
    L 0 0 = 0 ∧ L 0 1 = 0 ∧ L 1 1 = 0 := by
  have hg : g1 - g2 ≠ 0 := sub_ne_zero.2 hne
  -- subtracting: `Σ K e₁ = 0`
  have hw0 : L 0 0 * k00E L + L 0 1 * k01E L = 0 := by
    apply mul_left_cancel₀ hg
    simp only [F0E, A0E, A1E] at h1 h2
    linear_combination h1 - h2
  have hw1 : L 0 1 * k00E L + L 1 1 * k01E L = 0 := by
    apply mul_left_cancel₀ hg
    simp only [F1E, A0E, A1E] at h1' h2'
    linear_combination h1' - h2'
  -- `K e₁ = Σ u` with `u = (Σ + I)⁻¹ e₁`
  have hd := dE_pos hP
  set u0 := (1 + L 1 1) / dE L with hu0
  set u1 := -L 0 1 / dE L with hu1
  have e0 : k00E L = L 0 0 * u0 + L 0 1 * u1 := by
    rw [hu0, hu1, k00E]; field_simp; ring
  have e1 : k01E L = L 0 1 * u0 + L 1 1 * u1 := by
    rw [hu0, hu1, k01E]; field_simp; ring
  have f0 : (1 + L 0 0) * u0 + L 0 1 * u1 = 1 := by
    rw [hu0, hu1]; field_simp; simp only [dE]; ring
  have f1 : L 0 1 * u0 + (1 + L 1 1) * u1 = 0 := by
    rw [hu0, hu1]; field_simp; ring
  -- same kernel: `Σ² u = 0` gives `Σ u = 0`
  have hw : k00E L ^ 2 + k01E L ^ 2 = 0 := by
    have : k00E L ^ 2 + k01E L ^ 2 =
        u0 * (L 0 0 * k00E L + L 0 1 * k01E L) + u1 * (L 0 1 * k00E L + L 1 1 * k01E L) := by
      linear_combination k00E L * e0 + k01E L * e1
    rw [this, hw0, hw1]; ring
  have hk0 : k00E L = 0 := by nlinarith [sq_nonneg (k00E L), sq_nonneg (k01E L)]
  have hk1 : k01E L = 0 := by nlinarith [sq_nonneg (k00E L), sq_nonneg (k01E L)]
  -- `(Σ + I) u = e₁` and `Σ u = 0` give `u = e₁`, so `Σ e₁ = 0`
  have hu : u0 = 1 ∧ u1 = 0 := by
    rw [hk0] at e0; rw [hk1] at e1
    exact ⟨by linarith, by linarith⟩
  rw [hu.1, hu.2] at e0 e1
  have ha : L 0 0 = 0 := by rw [hk0] at e0; linarith
  have hb : L 0 1 = 0 := by rw [hk1] at e1; linarith
  refine ⟨ha, hb, ?_⟩
  simp only [F1E, A0E, A1E, hk0, hk1, hb] at h1'
  simpa using h1'

/-- For `γ ∈ [0, δ]`, the choice of `δ` in Case 2 of Proposition 2 puts the sensitivity in
`(0, c_κ]`. -/
lemma sensE_mem_of_small {S : M2} (hP : PSDE S) {B c δ g : ℝ} (hC : |S 0 1| ≤ B) (hc : 1 < c)
    (hδB : δ * B ≤ 1 / 2) (hδc : (2 * c - 1) * (δ * B) ≤ (c - 1) / 2) (hB : 0 ≤ B)
    (hg0 : 0 ≤ g) (hgδ : g ≤ δ) : 0 < sensE S g ∧ sensE S g ≤ c := by
  have hv := vZE_pos hP g
  have hgC : -(δ * B) ≤ g * S 0 1 := by
    have := (abs_le.1 hC).1
    nlinarith [mul_nonneg hg0 (by linarith : 0 ≤ S 0 1 + B), mul_nonneg (sub_nonneg.2 hgδ) hB]
  have hV : 1 ≤ 1 + S 1 1 := by linarith [hP.2.1]
  have hH := HE_nonneg hP
  refine ⟨div_pos (by linarith) hv, ?_⟩
  rw [sensE, div_le_iff₀ hv, vZE_expand hP]
  have h1 : (2 * c - 1) * (-(δ * B)) ≤ (2 * c - 1) * (g * S 0 1) :=
    mul_le_mul_of_nonneg_left hgC (by linarith)
  have h2 : 0 ≤ c * (g ^ 2 * HE S) := by positivity
  have h3 : (c - 1) * 1 ≤ (c - 1) * (1 + S 1 1) := mul_le_mul_of_nonneg_left hV (by linarith)
  nlinarith

/-- **Learning core** (Case 2 of Proposition 2). Suppose that for some `κ̄ < κck`, every open
subinterval of `(0,1]` is visited infinitely often by `γ_t` at dates with `κ_t ≤ κ̄`. Then
`Σ_t → 0`. -/
theorem learning_core {κ γ : ℕ → ℝ} {S₁ : M2} (hS : S₁.PosSemidef) {κbar : ℝ}
    (hκbar : κbar < κck)
    (hvisit : ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 → ∃ᶠ t in atTop, κ t ≤ κbar ∧ γ t ∈ Ioo a b) :
    Tendsto (SigmaC κ S₁ γ) atTop (𝓝 0) := by
  have hP := SigmaC_PSDE (κ := κ) (γ := γ) hS
  -- the uniform bounds `1 ≤ V_t ≤ B`, `|C_t| ≤ B`, `0 ≤ H_t ≤ B`
  have h00 := fun t => SigmaC_anti00 (κ := κ) (γ := γ) hS (Nat.zero_le t)
  have h11 := fun t => SigmaC_anti11 (κ := κ) (γ := γ) hS (Nat.zero_le t)
  simp only [SigmaC] at h00 h11
  set B := 1 + (S₁ 0 0 + S₁ 1 1) with hB
  have hS0 := (psd_PSDE hS).1
  have hS1 := (psd_PSDE hS).2.1
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hbd : ∀ t, 1 ≤ 1 + SigmaC κ S₁ γ t 1 1 ∧ 1 + SigmaC κ S₁ γ t 1 1 ≤ B ∧
      |SigmaC κ S₁ γ t 0 1| ≤ B ∧ 0 ≤ HE (SigmaC κ S₁ γ t) ∧ HE (SigmaC κ S₁ γ t) ≤ B := fun t => by
    have h2 := two_abs_off_le (hP t)
    have h3 := abs_nonneg (SigmaC κ S₁ γ t 0 1)
    have h4 := HE_le (hP t)
    exact ⟨by linarith [(hP t).2.1], by linarith [h11 t], by linarith [h00 t, h11 t, (hP t).1],
      HE_nonneg (hP t), by linarith [h00 t]⟩
  -- `c_κ = (2√κ̄)⁻¹ > 1`, with `κ̄` replaced by a positive bound if necessary
  set κ' := max κbar (κck / 2) with hκ'
  have hκ'0 : 0 < κ' := lt_of_lt_of_le (half_pos κck_pos) (le_max_right _ _)
  have hκ'1 : κ' < κck := max_lt hκbar (half_lt_self κck_pos)
  have hsq0 : 0 < √κ' := Real.sqrt_pos.2 hκ'0
  have hsq1 : 2 * √κ' < 1 := by
    have : √κ' < 1 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      rw [κck_eq] at hκ'1
      norm_num; linarith
    linarith
  set c := (2 * √κ')⁻¹ with hc
  have hc1 : 1 < c := by rw [hc]; exact (one_lt_inv₀ (by positivity)).2 hsq1
  have hκc : κ' * c ^ 2 = κck := by
    have : √κ' ^ 2 = κ' := Real.sq_sqrt hκ'0.le
    rw [hc, κck_eq, inv_pow, mul_pow, this]
    field_simp
    norm_num
  -- the choice of `δ`
  set δ := min 1 (min (1 / (2 * B)) ((c - 1) / (2 * (2 * c - 1) * B))) with hδ
  have h2c : 0 < 2 * c - 1 := by linarith
  have hδ0 : 0 < δ := lt_min one_pos (lt_min (by positivity) (div_pos (by linarith) (by positivity)))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδB : δ * B ≤ 1 / 2 := by
    have h : δ ≤ 1 / (2 * B) := (min_le_right _ _).trans (min_le_left _ _)
    calc δ * B ≤ 1 / (2 * B) * B := mul_le_mul_of_nonneg_right h hB0.le
      _ = 1 / 2 := by field_simp
  have hδc : (2 * c - 1) * (δ * B) ≤ (c - 1) / 2 := by
    have h : δ ≤ (c - 1) / (2 * (2 * c - 1) * B) := (min_le_right _ _).trans (min_le_right _ _)
    calc (2 * c - 1) * (δ * B) ≤ (2 * c - 1) * ((c - 1) / (2 * (2 * c - 1) * B) * B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hB0.le) h2c.le
      _ = (c - 1) / 2 := by field_simp
  -- the signaling equilibrium is revealing whenever `κ_t ≤ κ̄` and `γ_t ∈ [0, δ]`
  have hrev : ∀ t, κ t ≤ κbar → 0 ≤ γ t → γ t ≤ δ →
      revCrit (κ t) (SigmaC κ S₁ γ t) (γ t) := by
    intro t hκt h0 h1
    obtain ⟨hs0, hsc⟩ := sensE_mem_of_small (hP t) (hbd t).2.2.1 hc1 hδB hδc hB0.le h0 h1
    show κ t * sens (SigmaC κ S₁ γ t) (γ t) ^ 2 ≤ κck
    rw [sens_eq_sensE (SigmaC_sym hS t) (dE_ne (hP t))]
    have hsq' := pow_le_pow_left₀ hs0.le hsc 2
    have h2 : κ t * sensE (SigmaC κ S₁ γ t) (γ t) ^ 2 ≤ κ' * sensE (SigmaC κ S₁ γ t) (γ t) ^ 2 :=
      mul_le_mul_of_nonneg_right (hκt.trans (le_max_left _ _)) (sq_nonneg _)
    have h3 := mul_le_mul_of_nonneg_left hsq' hκ'0.le
    linarith
  -- `Σ_t → Σ_∞`, and `Σ_∞ (e₂ + γ̄ K_∞ e₁) = 0` for every `γ̄ ∈ (0, δ)`
  obtain ⟨L, hL, hLs, hLP⟩ := SigmaC_tendsto (κ := κ) (γ := γ) hS
  have hdL := dE_ne hLP
  have hF : ∀ g, 0 < g → g < δ → F0E L g = 0 ∧ F1E L g = 0 := by
    intro g hg0 hgδ
    have hm : 0 < min g (δ - g) := lt_min hg0 (by linarith)
    set ρ : ℕ → ℝ := fun n => min g (δ - g) / ((n : ℝ) + 2) with hρ
    have hρ0 : ∀ n, 0 < ρ n := fun n => by positivity
    have hρ1 : ∀ n, ρ n < min g (δ - g) := fun n => by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      exact div_lt_self hm (by linarith)
    have hρt : Tendsto ρ atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have ha : ∀ n, 0 < g - ρ n := fun n => by linarith [hρ1 n, min_le_left g (δ - g)]
    have hb : ∀ n, g + ρ n < δ := fun n => by linarith [hρ1 n, min_le_right g (δ - g)]
    obtain ⟨φ, hφ, hφv⟩ := extraction_forall_of_frequently fun n =>
      hvisit (g - ρ n) (g + ρ n) (ha n) (by linarith [hρ0 n]) (by linarith [hb n])
    have hlow : ∀ n, 0 < γ (φ n) := fun n => (ha n).trans (hφv n).2.1
    have hhigh : ∀ n, γ (φ n) < δ := fun n => (hφv n).2.2.trans (hb n)
    have hγ : Tendsto (fun n => γ (φ n)) atTop (𝓝 g) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        (by simpa using tendsto_const_nhds.sub hρt) (by simpa using tendsto_const_nhds.add hρt)
        (fun n => (hφv n).2.1.le) (fun n => (hφv n).2.2.le)
    have hrevφ : ∀ n, revCrit (κ (φ n)) (SigmaC κ S₁ γ (φ n)) (γ (φ n)) := fun n =>
      hrev _ (hφv n).1 (hlow n).le (hhigh n).le
    obtain ⟨h0, h1⟩ := FA_tendsto hS hφ hrevφ fun n => ⟨(hlow n).le, (hhigh n).le.trans hδ1⟩
    have hp : Tendsto (fun n => (SigmaC κ S₁ γ (φ n), γ (φ n))) atTop (𝓝 (L, g)) :=
      (hL.comp hφ.tendsto_atTop).prodMk_nhds hγ
    exact ⟨tendsto_nhds_unique ((ca_F0E (γ := g) hdL).tendsto.comp hp) h0,
      tendsto_nhds_unique ((ca_F1E (γ := g) hdL).tendsto.comp hp) h1⟩
  -- two distinct weights give `Σ_∞ = 0`
  obtain ⟨h1, h1'⟩ := hF (δ / 3) (by positivity) (by linarith)
  obtain ⟨h2, h2'⟩ := hF (2 * δ / 3) (by positivity) (by linarith)
  obtain ⟨ha, hb, hc'⟩ := zero_of_F hLP (by intro h; linarith) h1 h1' h2 h2'
  have hL0 : L = 0 := by
    ext i j; fin_cases i <;> fin_cases j
    · exact ha
    · exact hb
    · simpa [hLs] using hb
    · exact hc'
  rwa [hL0] at hL

end CC
