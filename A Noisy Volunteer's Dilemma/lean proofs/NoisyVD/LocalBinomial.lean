import NoisyVD.LocalLimit

/-!
# Lemma `lemma_local_binomial`, in the exact form stated in the paper

As in the paper, the mass bound and the tail limit come from the Berry--Esseen bound `eq_be`
(`bpmf_le_massConst`, `uniform_tail`), and the local limit comes from Stirling's formula
(`local_limit_seq`).  We write `⌊·⌋₊` for the floor: since `ns + t√n → ∞` uniformly, it agrees with the
integer floor for all large `n`.
-/

open Set Filter Topology Real

namespace NoisyVD

/-- **Lemma `lemma_local_binomial`.** -/
theorem lemma_local_binomial :
    (∀ l : ℝ, 0 < l → l ≤ 1 / 2 → ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ p ∈ Icc l (1 - l), ∀ k : ℕ,
      bpmf m p k ≤ C / √(m : ℝ)) ∧
    (∀ s : ℝ, 0 < s → s < 1 → ∀ K L₀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x t : ℝ, |x| ≤ K → |t| ≤ K →
      ∀ l : ℤ, |(l : ℝ)| ≤ L₀ →
      |√(n : ℝ) * bpmf ((n : ℤ) + l).toNat (s + x / √(n : ℝ)) ⌊(n : ℝ) * s + t * √(n : ℝ)⌋₊
          - 1 / √(s * (1 - s)) * phi ((t - x) / √(s * (1 - s)))| < ε ∧
      |btail ((n : ℤ) + l).toNat (s + x / √(n : ℝ)) ⌊(n : ℝ) * s + t * √(n : ℝ)⌋₊
          - (1 - Phi ((t - x) / √(s * (1 - s))))| < ε) := by
  refine ⟨fun l hl hl' => ⟨massConst l, fun m hm p hp k => bpmf_le_massConst hm hl hl' hp k⟩, ?_⟩
  intro s hs0 hs1 K L₀ ε hε
  set S := s * (1 - s) with hSdef
  have hS : 0 < S := mul_pos hs0 (by linarith)
  set σ := √S with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hS
  set l₀ : ℝ := min s (1 - s) / 2 with hl₀
  have hl₀pos : 0 < l₀ := by
    rw [hl₀]
    have := lt_min hs0 (show 0 < 1 - s by linarith)
    linarith
  have hl₁ : l₀ ≤ s / 2 := by
    rw [hl₀]; apply div_le_div_of_nonneg_right (min_le_left _ _); norm_num
  have hl₂ : l₀ ≤ (1 - s) / 2 := by
    rw [hl₀]; apply div_le_div_of_nonneg_right (min_le_right _ _); norm_num
  have hlhalf : l₀ ≤ 1 / 2 := by linarith
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  -- `s + x/√n` stays in `[l₀, 1-l₀]`
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((tendsto_order.1
    (Tendsto.const_div_atTop hsq K)).2 l₀ hl₀pos)
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hnge, x, t, hx, ht, ℓ, hℓ, hbad⟩ : ∃ (n : ℕ → ℕ), (∀ j, j + N₀ + 1 ≤ n j) ∧
      ∃ (x t : ℕ → ℝ), (∀ j, |x j| ≤ K) ∧ (∀ j, |t j| ≤ K) ∧ ∃ ℓ : ℕ → ℤ, (∀ j, |(ℓ j : ℝ)| ≤ L₀) ∧
      ∀ j, |√(n j : ℝ) * bpmf ((n j : ℤ) + ℓ j).toNat (s + x j / √(n j : ℝ))
            ⌊(n j : ℝ) * s + t j * √(n j : ℝ)⌋₊ - 1 / σ * phi ((t j - x j) / σ)| < ε →
        ε ≤ |btail ((n j : ℤ) + ℓ j).toNat (s + x j / √(n j : ℝ))
            ⌊(n j : ℝ) * s + t j * √(n j : ℝ)⌋₊ - (1 - Phi ((t j - x j) / σ))| := by
    choose n hn x t hx ht ℓ hℓ hbad using fun j => hcon (j + N₀ + 1)
    exact ⟨n, hn, x, t, hx, ht, ℓ, hℓ, hbad⟩
  have hnt : Tendsto n atTop atTop :=
    tendsto_atTop_mono (fun j => (by have := hnge j; omega : j ≤ n j)) tendsto_id
  have hNt : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hnt
  have hsn : Tendsto (fun j => √(n j : ℝ)) atTop atTop := Real.tendsto_sqrt_atTop.comp hNt
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hx 0)
  have hL0 : 0 ≤ L₀ := (abs_nonneg _).trans (hℓ 0)
  have hnpos : ∀ j, (0 : ℝ) < n j := fun j => by
    have := hnge j
    exact_mod_cast (show 0 < n j by omega)
  have hspos : ∀ j, 0 < √(n j : ℝ) := fun j => Real.sqrt_pos.2 (hnpos j)
  let p : ℕ → ℝ := fun j => s + x j / √(n j : ℝ)
  have hpclose : ∀ j, |x j / √(n j : ℝ)| ≤ K / √(n j : ℝ) := fun j => by
    rw [abs_div, abs_of_pos (hspos j)]
    exact div_le_div_of_nonneg_right (hx j) (hspos j).le
  have hpI : ∀ j, p j ∈ Icc l₀ (1 - l₀) := fun j => by
    have h1 : K / √(n j : ℝ) < l₀ := hN₀ _ (by have := hnge j; omega)
    have h2 := abs_le.1 ((hpclose j).trans h1.le)
    simp only [p]
    constructor <;> linarith [h2.1, h2.2]
  have hKroot : Tendsto (fun j => K / √(n j : ℝ)) atTop (𝓝 0) := Tendsto.const_div_atTop hsn K
  have hps : Tendsto p atTop (𝓝 s) := by
    have h1 : Tendsto (fun j => x j / √(n j : ℝ)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun j => by rw [Real.norm_eq_abs]; exact hpclose j) hKroot
    have := h1.const_add s
    simpa [p] using this
  let m : ℕ → ℕ := fun j => ((n j : ℤ) + ℓ j).toNat
  have hL0nat : ∀ᶠ j in atTop, L₀ + 1 ≤ (n j : ℝ) := hNt.eventually_ge_atTop _
  have hmcast : ∀ᶠ j in atTop, (m j : ℝ) = (n j : ℝ) + ℓ j := by
    filter_upwards [hL0nat] with j hj
    have h1 := abs_le.1 (hℓ j)
    have h2 : (0 : ℝ) ≤ (n j : ℝ) + ℓ j := by linarith [h1.1]
    have h3 : (0 : ℤ) ≤ (n j : ℤ) + ℓ j := by exact_mod_cast h2
    simp only [m]
    have h4 : ((((n j : ℤ) + ℓ j).toNat : ℤ) : ℝ) = (((n j : ℤ) + ℓ j : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg h3]
    push_cast at h4
    exact h4
  have hmt : Tendsto m atTop atTop := by
    apply tendsto_natCast_atTop_iff (R := ℝ) |>.1
    have h1 : Tendsto (fun j => (n j : ℝ) + (-L₀)) atTop atTop := tendsto_atTop_add_const_right _ _ hNt
    refine tendsto_atTop_mono' _ ?_ h1
    filter_upwards [hmcast] with j hj
    rw [hj]
    have := abs_le.1 (hℓ j)
    linarith [this.1]
  have hm1 : ∀ᶠ j in atTop, 1 ≤ m j := hmt.eventually_ge_atTop 1
  have hratio : Tendsto (fun j => (m j : ℝ) / n j) atTop (𝓝 1) := by
    have h1 : Tendsto (fun j => L₀ / (n j : ℝ)) atTop (𝓝 0) := Tendsto.const_div_atTop hNt L₀
    have h2 : Tendsto (fun j => (m j : ℝ) / n j - 1) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h1
      filter_upwards [hmcast] with j hj
      rw [hj]
      have e : ((n j : ℝ) + ℓ j) / n j - 1 = (ℓ j : ℝ) / n j := by
        have := (hnpos j).ne'
        field_simp
        ring
      rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (hnpos j)]
      exact div_le_div_of_nonneg_right (hℓ j) (hnpos j).le
    have := h2.add_const 1
    simpa using this
  have hpq : Tendsto (fun j => p j * (1 - p j)) atTop (𝓝 S) := hps.mul (tendsto_const_nhds.sub hps)
  let sd : ℕ → ℝ := fun j => sdev (m j) (p j)
  have hsdform : ∀ᶠ j in atTop, sd j = √(n j : ℝ) * √((m j : ℝ) / n j * (p j * (1 - p j))) := by
    refine Eventually.of_forall fun j => ?_
    simp only [sd, sdev]
    rw [← Real.sqrt_mul (hnpos j).le]
    congr 1
    have := (hnpos j).ne'
    field_simp
  have hroot : Tendsto (fun j => √((m j : ℝ) / n j * (p j * (1 - p j)))) atTop (𝓝 σ) := by
    have := (hratio.mul hpq).sqrt
    simpa [σ] using this
  -- `√n / sd → 1/σ`
  have hrr : Tendsto (fun j => √(n j : ℝ) / sd j) atTop (𝓝 (1 / σ)) := by
    have h1 : Tendsto (fun j => 1 / √((m j : ℝ) / n j * (p j * (1 - p j)))) atTop (𝓝 (1 / σ)) :=
      tendsto_const_nhds.div hroot hσ.ne'
    refine h1.congr' ?_
    filter_upwards [hsdform, hroot.eventually (lt_mem_nhds (half_lt_self hσ))] with j hj hj2
    rw [hj]
    have hr : 0 < √((m j : ℝ) / n j * (p j * (1 - p j))) := by linarith [half_pos hσ]
    have hs' := (hspos j).ne'
    rw [div_mul_cancel_left₀ hs']
    rw [one_div]
  have hsdpos : ∀ᶠ j in atTop, 0 < sd j := by
    filter_upwards [hm1] with j hj
    exact sdev_pos hj (lt_of_lt_of_le hl₀pos (hpI j).1) (lt_of_le_of_lt (hpI j).2 (by linarith))
  have hsdt : Tendsto sd atTop atTop := by
    have hc : 0 < l₀ * (1 - l₀) := mul_pos hl₀pos (by linarith)
    have hm' : Tendsto (fun j => (m j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hmt
    have h1 : Tendsto (fun j => √((m j : ℝ) * (l₀ * (1 - l₀)))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (hm'.atTop_mul_const hc)
    refine tendsto_atTop_mono (fun j => ?_) h1
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (mul_one_sub_ge (hpI j)) (Nat.cast_nonneg _))
  let y : ℕ → ℝ := fun j => (n j : ℝ) * s + t j * √(n j : ℝ)
  let k : ℕ → ℕ := fun j => ⌊y j⌋₊
  have hy0 : ∀ᶠ j in atTop, 0 ≤ y j := by
    have h1 := hsn.eventually_ge_atTop (K / s)
    filter_upwards [h1] with j hj
    rw [div_le_iff₀ hs0] at hj
    have hsqj := Real.mul_self_sqrt (hnpos j).le
    have h2 := abs_le.1 (ht j)
    have h3 : -K * √(n j : ℝ) ≤ t j * √(n j : ℝ) :=
      mul_le_mul_of_nonneg_right h2.1 (hspos j).le
    simp only [y]
    nlinarith
  -- the numerator of the `z`-score
  set B₀ : ℝ := 1 + L₀ * (1 + K) with hB₀
  have hA : ∀ᶠ j in atTop, |((k j : ℝ) - m j * p j) - (t j - x j) * √(n j : ℝ)| ≤ B₀ := by
    filter_upwards [hy0, hmcast, hNt.eventually_ge_atTop 1] with j hj0 hmj hn1
    have h1 : (k j : ℝ) ≤ y j := Nat.floor_le hj0
    have h2 : y j < (k j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hsq1 : 1 ≤ √(n j : ℝ) := by
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt hn1
    have hsqj := Real.mul_self_sqrt (hnpos j).le
    have e : (k j : ℝ) - m j * p j - (t j - x j) * √(n j : ℝ)
        = ((k j : ℝ) - y j) - ℓ j * s - ℓ j * (x j / √(n j : ℝ)) := by
      have hd : (n j : ℝ) * (x j / √(n j : ℝ)) = x j * √(n j : ℝ) := by
        have e0 : (n j : ℝ) * (x j / √(n j : ℝ)) = x j * ((n j : ℝ) / √(n j : ℝ)) := by ring
        rw [e0, Real.div_sqrt]
      rw [hmj]
      simp only [p, y]
      linear_combination -hd
    rw [e]
    have h3 : |(k j : ℝ) - y j| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have h4 : |(ℓ j : ℝ) * s| ≤ L₀ := by
      rw [abs_mul, abs_of_pos hs0]
      have := hℓ j
      have := abs_nonneg (ℓ j : ℝ)
      nlinarith
    have h5 : |(ℓ j : ℝ) * (x j / √(n j : ℝ))| ≤ L₀ * K := by
      rw [abs_mul]
      have h6 : |x j / √(n j : ℝ)| ≤ K := by
        refine (hpclose j).trans ?_
        rw [div_le_iff₀ (hspos j)]
        nlinarith
      exact mul_le_mul (hℓ j) h6 (abs_nonneg _) hL0
    calc |(k j : ℝ) - y j - ℓ j * s - ℓ j * (x j / √(n j : ℝ))|
        ≤ |(k j : ℝ) - y j - ℓ j * s| + |(ℓ j : ℝ) * (x j / √(n j : ℝ))| := abs_sub _ _
      _ ≤ |(k j : ℝ) - y j| + |(ℓ j : ℝ) * s| + |(ℓ j : ℝ) * (x j / √(n j : ℝ))| := by
          gcongr
          exact abs_sub _ _
      _ ≤ B₀ := by rw [hB₀]; linarith
  -- the `z`-score
  let z : ℕ → ℝ := fun j => zscore (m j) (p j) (k j)
  let u : ℕ → ℝ := fun j => (t j - x j) / σ
  have hub : ∀ j, |t j - x j| ≤ 2 * K := fun j => by
    have h1 := abs_le.1 (hx j)
    have h2 := abs_le.1 (ht j)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hzu : Tendsto (fun j => z j - u j) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => |√(n j : ℝ) / sd j - 1 / σ| * (2 * K)) atTop (𝓝 0) := by
      have := (hrr.sub_const (1 / σ)).abs.mul_const (2 * K)
      simpa using this
    have h2 : Tendsto (fun j => B₀ / sd j) atTop (𝓝 0) := Tendsto.const_div_atTop hsdt B₀
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine squeeze_zero_norm' ?_ h3
    filter_upwards [hA, hsdpos] with j hj hsdj
    have e : z j - u j = (t j - x j) * (√(n j : ℝ) / sd j - 1 / σ)
        + (((k j : ℝ) - m j * p j) - (t j - x j) * √(n j : ℝ)) / sd j := by
      simp only [z, u, zscore]
      show ((k j : ℝ) - m j * p j) / sd j - (t j - x j) / σ = _
      field_simp
      ring
    rw [e, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_div _ (sd j), abs_of_pos hsdj, mul_comm]
    have hb1 : |√(n j : ℝ) / sd j - 1 / σ| * |t j - x j| ≤ |√(n j : ℝ) / sd j - 1 / σ| * (2 * K) :=
      mul_le_mul_of_nonneg_left (hub j) (abs_nonneg _)
    have hb2 : |(k j : ℝ) - m j * p j - (t j - x j) * √(n j : ℝ)| / sd j ≤ B₀ / sd j :=
      div_le_div_of_nonneg_right hj hsdj.le
    linarith
  have hzb : ∀ᶠ j in atTop, |z j| ≤ 2 * K / σ + 1 := by
    filter_upwards [(tendsto_order.1 hzu.abs).2 1 (by simp)] with j hj
    have h1 : |u j| ≤ 2 * K / σ := by
      simp only [u]
      rw [abs_div, abs_of_pos hσ]
      exact div_le_div_of_nonneg_right (hub j) hσ.le
    have h2 : |z j| ≤ |z j - u j| + |u j| := by
      have := abs_add_le (z j - u j) (u j)
      simpa using this
    linarith
  have hll := local_limit_seq hl₀pos hlhalf hmt hpI hzb
  have hφ : Tendsto (fun j => phi (z j) - phi (u j)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun j => phi 0 * |z j - u j|) (fun j => ?_) ?_
    · rw [Real.norm_eq_abs]; exact abs_phi_sub_le _ _
    · have := hzu.abs.const_mul (phi 0)
      simpa using this
  -- local claim
  have hlocal : Tendsto (fun j => √(n j : ℝ) * bpmf (m j) (p j) (k j) - 1 / σ * phi (u j)) atTop (𝓝 0) := by
    have t1 : Tendsto (fun j => √(n j : ℝ) / sd j * (sd j * bpmf (m j) (p j) (k j) - phi (z j))) atTop (𝓝 0) := by
      have := hrr.mul hll
      simpa using this
    have t2 : Tendsto (fun j => (√(n j : ℝ) / sd j - 1 / σ) * phi (z j)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun j => |√(n j : ℝ) / sd j - 1 / σ| * phi 0) (fun j => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (phi_pos _)]
        exact mul_le_mul_of_nonneg_left (phi_le _) (abs_nonneg _)
      · have := (hrr.sub_const (1 / σ)).abs.mul_const (phi 0)
        simpa using this
    have t3 := hφ.const_mul (1 / σ)
    have hsum := (t1.add t2).add t3
    simp only [add_zero, mul_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hsdpos] with j hj
    have := hj.ne'
    field_simp
    ring
  obtain ⟨N₁, hN₁⟩ := uniform_tail hl₀pos hlhalf (show 0 < ε / 2 by linarith)
  have hΦ : ∀ᶠ j in atTop, |Phi (z j) - Phi (u j)| < ε / 2 := by
    have h1 : Tendsto (fun j => phi 0 * |z j - u j|) atTop (𝓝 0) := by
      have := hzu.abs.const_mul (phi 0)
      simpa using this
    filter_upwards [(tendsto_order.1 h1).2 (ε / 2) (by linarith)] with j hj
    exact lt_of_le_of_lt (abs_Phi_sub_le _ _) hj
  obtain ⟨j, hj1, hj2, hj3⟩ := (((tendsto_order.1 hlocal.abs).2 ε (by simpa using hε)).and
    ((hmt.eventually_ge_atTop N₁).and hΦ)).exists
  have htail := hbad j hj1
  have h4 := hN₁ _ hj2 _ (hpI j) (k j)
  have h5 : |btail (m j) (p j) (k j) - (1 - Phi (u j))|
      ≤ |btail (m j) (p j) (k j) - (1 - Phi (z j))| + |Phi (z j) - Phi (u j)| := by
    have := abs_add_le (btail (m j) (p j) (k j) - (1 - Phi (z j))) (Phi (u j) - Phi (z j))
    have e : btail (m j) (p j) (k j) - (1 - Phi (z j)) + (Phi (u j) - Phi (z j))
        = btail (m j) (p j) (k j) - (1 - Phi (u j)) := by ring
    rw [e, abs_sub_comm (Phi (u j))] at this
    exact this
  have h6 : |btail (m j) (p j) (k j) - (1 - Phi (u j))| < ε := by
    have h7 : |btail (m j) (p j) (k j) - (1 - Phi (zscore (m j) (p j) (k j)))| < ε / 2 := h4
    have h8 : |btail (m j) (p j) (k j) - (1 - Phi (z j))| < ε / 2 := h7
    linarith
  exact absurd htail (not_le.2 h6)

end NoisyVD
