import NoisyVD.BerryEsseen

/-!
# De Moivre--Laplace local limit theorem, uniformly over `p ∈ [l, 1-l]`

Derived from Stirling's formula (`Stirling.tendsto_stirlingSeq_sqrt_pi`).
-/

open Finset Real Filter Topology

namespace NoisyVD

lemma log_taylor {w : ℝ} (hw : |w| ≤ 1 / 2) :
    |(1 + w) * log (1 + w) - w - w ^ 2 / 2| ≤ 4 * |w| ^ 3 := by
  have h1 : |(-w)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sub_neg_eq_add, abs_neg] at h
  set r : ℝ := -w + w ^ 2 / 2 + log (1 + w) with hr'
  have hreq : (-w) ^ 1 / (((0 : ℕ) : ℝ) + 1) + (-w) ^ (1 + 1) / (((1 : ℕ) : ℝ) + 1) + log (1 + w) = r := by
    rw [hr']; push_cast; ring
  rw [hreq] at h
  have hw0 : 0 ≤ |w| := abs_nonneg w
  have hb : |r| ≤ 2 * |w| ^ 3 := by
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ |w| ^ 3 := by positivity
    have e : |w| ^ (2 + 1) = |w| ^ 3 := rfl
    rw [e]
    nlinarith
  have hlog : log (1 + w) = w - w ^ 2 / 2 + r := by rw [hr']; ring
  have hexp : (1 + w) * log (1 + w) - w - w ^ 2 / 2 = -w ^ 3 / 2 + (1 + w) * r := by
    rw [hlog]; ring
  rw [hexp]
  have h1w : |1 + w| ≤ 3 / 2 := by
    rw [abs_le]; constructor <;> linarith [abs_le.1 hw |>.1, abs_le.1 hw |>.2]
  calc |-w ^ 3 / 2 + (1 + w) * r| ≤ |-w ^ 3 / 2| + |(1 + w) * r| := abs_add_le _ _
    _ = |w| ^ 3 / 2 + |1 + w| * |r| := by
        rw [abs_mul, abs_div, abs_neg, abs_pow]; norm_num
    _ ≤ |w| ^ 3 / 2 + 3 / 2 * (2 * |w| ^ 3) := by
        gcongr
    _ ≤ 4 * |w| ^ 3 := by nlinarith [pow_nonneg hw0 3]

/-- The relative-entropy expansion in the proof of Lemma `lemma_local_binomial`. -/
lemma entropy_expansion {M p k n' : ℝ} (hM : 0 < M) (hp : 0 < p) (hp1 : p < 1) (hk : k + n' = M)
    (h1 : |(k - M * p) / (M * p)| ≤ 1 / 2) (h2 : |(k - M * p) / (M * (1 - p))| ≤ 1 / 2) :
    |k * log (k / (M * p)) + n' * log (n' / (M * (1 - p)))
        - (k - M * p) ^ 2 / (2 * (M * (p * (1 - p))))|
      ≤ 4 * |k - M * p| ^ 3 * (1 / (M * p) ^ 2 + 1 / (M * (1 - p)) ^ 2) := by
  have hq : 0 < 1 - p := by linarith
  set a : ℝ := k - M * p with ha
  set w1 : ℝ := a / (M * p) with hw1
  set w2 : ℝ := -a / (M * (1 - p)) with hw2
  have hMp : 0 < M * p := by positivity
  have hMq : 0 < M * (1 - p) := by positivity
  have hk1 : k / (M * p) = 1 + w1 := by
    rw [hw1, ha]; field_simp; ring
  have hn1 : n' / (M * (1 - p)) = 1 + w2 := by
    have : n' = M * (1 - p) - a := by rw [ha]; linarith
    rw [hw2, this]; field_simp; ring
  have hk2 : k = M * p * (1 + w1) := by
    rw [hw1, ha]; field_simp; ring
  have hn2 : n' = M * (1 - p) * (1 + w2) := by
    have : n' = M * (1 - p) - a := by rw [ha]; linarith
    rw [hw2, this]; field_simp; ring
  have hw1' : |w1| ≤ 1 / 2 := h1
  have hw2' : |w2| ≤ 1 / 2 := by
    rw [hw2, neg_div, abs_neg]; exact h2
  have t1 := log_taylor hw1'
  have t2 := log_taylor hw2'
  set R1 : ℝ := (1 + w1) * log (1 + w1) - w1 - w1 ^ 2 / 2 with hR1
  set R2 : ℝ := (1 + w2) * log (1 + w2) - w2 - w2 ^ 2 / 2 with hR2
  have hT : k * log (k / (M * p)) + n' * log (n' / (M * (1 - p)))
      - a ^ 2 / (2 * (M * (p * (1 - p)))) = M * p * R1 + M * (1 - p) * R2 := by
    rw [hk1, hn1]
    have e1 : k * log (1 + w1) = M * p * ((1 + w1) * log (1 + w1)) := by
      rw [hk2]; ring
    have e2 : n' * log (1 + w2) = M * (1 - p) * ((1 + w2) * log (1 + w2)) := by
      rw [hn2]; ring
    rw [e1, e2, hR1, hR2, hw1, hw2]
    field_simp
    ring
  rw [hT]
  have b1 : |M * p * R1| ≤ 4 * |a| ^ 3 * (1 / (M * p) ^ 2) := by
    rw [abs_mul, abs_of_pos hMp]
    have : |w1| ^ 3 = |a| ^ 3 / (M * p) ^ 3 := by
      rw [hw1, abs_div, abs_of_pos hMp, div_pow]
    calc M * p * |R1| ≤ M * p * (4 * |w1| ^ 3) := by gcongr
      _ = 4 * |a| ^ 3 * (1 / (M * p) ^ 2) := by
          rw [this]; field_simp
  have b2 : |M * (1 - p) * R2| ≤ 4 * |a| ^ 3 * (1 / (M * (1 - p)) ^ 2) := by
    rw [abs_mul, abs_of_pos hMq]
    have : |w2| ^ 3 = |a| ^ 3 / (M * (1 - p)) ^ 3 := by
      rw [hw2, abs_div, abs_of_pos hMq, abs_neg, div_pow]
    calc M * (1 - p) * |R2| ≤ M * (1 - p) * (4 * |w2| ^ 3) := by gcongr
      _ = 4 * |a| ^ 3 * (1 / (M * (1 - p)) ^ 2) := by
          rw [this]; field_simp
  calc |M * p * R1 + M * (1 - p) * R2| ≤ |M * p * R1| + |M * (1 - p) * R2| := abs_add_le _ _
    _ ≤ _ := by rw [mul_add]; linarith

/-- Stirling's formula rewritten for the binomial mass function. -/
lemma bpmf_stirling_form {k n' : ℕ} (hk : 0 < k) (hn : 0 < n') {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    bpmf (k + n') p k =
      (Stirling.stirlingSeq (k + n') / (Stirling.stirlingSeq k * Stirling.stirlingSeq n'))
      * (√(2 * ((k + n' : ℕ) : ℝ)) / (√(2 * (k : ℝ)) * √(2 * (n' : ℝ))))
      * exp (-((k : ℝ) * log ((k : ℝ) / (((k + n' : ℕ) : ℝ) * p))
          + (n' : ℝ) * log ((n' : ℝ) / (((k + n' : ℕ) : ℝ) * (1 - p))))) := by
  have hq : 0 < 1 - p := by linarith
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hnr : (0 : ℝ) < n' := by exact_mod_cast hn
  set m : ℕ := k + n' with hm
  have hmr : (0 : ℝ) < m := by rw [hm]; push_cast; positivity
  have he : 0 < exp 1 := exp_pos 1
  -- factorial in terms of the Stirling sequence
  have hfac : ∀ j : ℕ, 0 < j → (j.factorial : ℝ)
      = Stirling.stirlingSeq j * (√(2 * (j : ℝ)) * ((j : ℝ) / exp 1) ^ j) := by
    intro j hj
    have hjr : (0 : ℝ) < j := by exact_mod_cast hj
    have h1 : 0 < √(2 * (j : ℝ)) := Real.sqrt_pos.2 (by positivity)
    have h2 : 0 < ((j : ℝ) / exp 1) ^ j := by positivity
    unfold Stirling.stirlingSeq
    field_simp
  have hchoose : (m.choose k : ℝ) = (m.factorial : ℝ) / ((k.factorial : ℝ) * (n'.factorial : ℝ)) := by
    have := Nat.cast_choose ℝ (show k ≤ m by rw [hm]; omega)
    rw [this]
    have : m - k = n' := by rw [hm]; omega
    rw [this]
  have hexp1 : exp (-((k : ℝ) * log ((k : ℝ) / ((m : ℝ) * p)))) = ((m : ℝ) * p / k) ^ k := by
    have hpos : 0 < (m : ℝ) * p / k := by positivity
    rw [← Real.exp_log (pow_pos hpos k), Real.log_pow, Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    congr 1
    ring
  have hexp2 : exp (-((n' : ℝ) * log ((n' : ℝ) / ((m : ℝ) * (1 - p)))))
      = ((m : ℝ) * (1 - p) / n') ^ n' := by
    have hpos : 0 < (m : ℝ) * (1 - p) / n' := by positivity
    rw [← Real.exp_log (pow_pos hpos n'), Real.log_pow, Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    congr 1
    ring
  rw [neg_add, exp_add, hexp1, hexp2]
  have hsk : 0 < Stirling.stirlingSeq k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos j
  have hsn : 0 < Stirling.stirlingSeq n' := by
    obtain ⟨j, rfl⟩ : ∃ j, n' = j + 1 := ⟨n' - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos j
  have hbm : bpmf m p k = (m.choose k : ℝ) * p ^ k * (1 - p) ^ n' := by
    unfold bpmf
    have : m - k = n' := by rw [hm]; omega
    rw [this]
  rw [hbm, hchoose, hfac m (by rw [hm]; omega), hfac k hk, hfac n' hn]
  have hs1 : 0 < √(2 * (k : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 0 < √(2 * (n' : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hpowm : ((m : ℝ) / exp 1) ^ m = ((m : ℝ) / exp 1) ^ k * ((m : ℝ) / exp 1) ^ n' := by
    rw [hm, pow_add]
  rw [hpowm]
  have hmk : ((m : ℝ) * p / k) ^ k = ((m : ℝ) / exp 1) ^ k / ((k : ℝ) / exp 1) ^ k * p ^ k := by
    rw [← div_pow, ← mul_pow]
    congr 1
    field_simp
  have hmn : ((m : ℝ) * (1 - p) / n') ^ n'
      = ((m : ℝ) / exp 1) ^ n' / ((n' : ℝ) / exp 1) ^ n' * (1 - p) ^ n' := by
    rw [← div_pow, ← mul_pow]
    congr 1
    field_simp
  rw [hmk, hmn]
  have h3 : 0 < ((k : ℝ) / exp 1) ^ k := by positivity
  have h4 : 0 < ((n' : ℝ) / exp 1) ^ n' := by positivity
  field_simp

/-- Local limit theorem along an arbitrary sequence of parameters. -/
theorem local_limit_seq {l : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2) {m k : ℕ → ℕ} {p : ℕ → ℝ}
    (hm : Tendsto m atTop atTop) (hp : ∀ j, p j ∈ Set.Icc l (1 - l)) {R : ℝ}
    (hz : ∀ᶠ j in atTop, |zscore (m j) (p j) (k j)| ≤ R) :
    Tendsto (fun j => sdev (m j) (p j) * bpmf (m j) (p j) (k j) - phi (zscore (m j) (p j) (k j)))
      atTop (𝓝 0) := by
  have hl1 : 0 < 1 - l := by linarith
  have hp0 : ∀ j, 0 < p j := fun j => lt_of_lt_of_le hl (hp j).1
  have hp1 : ∀ j, p j < 1 := fun j => lt_of_le_of_lt (hp j).2 (by linarith)
  have hq0 : ∀ j, 0 < 1 - p j := fun j => by linarith [hp1 j]
  have hql : ∀ j, l ≤ 1 - p j := fun j => by linarith [(hp j).2]
  -- sequences
  let M : ℕ → ℝ := fun j => (m j : ℝ)
  let a : ℕ → ℝ := fun j => (k j : ℝ) - M j * p j
  let x : ℕ → ℝ := fun j => (k j : ℝ) / M j
  have hMt : Tendsto M atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hm1 : ∀ᶠ j in atTop, 1 ≤ m j := hm.eventually_ge_atTop 1
  have hMpos : ∀ᶠ j in atTop, 0 < M j := hm1.mono fun j hj => by
    have : (1 : ℝ) ≤ (m j : ℝ) := by exact_mod_cast hj
    show (0 : ℝ) < (m j : ℝ)
    linarith
  set R' : ℝ := |R| with hR'
  have hR0 : 0 ≤ R' := abs_nonneg R
  -- `|a j| ≤ R' √M`
  have ha : ∀ᶠ j in atTop, |a j| ≤ R' * √(M j) := by
    filter_upwards [hz, hMpos] with j hj hMj
    have hpq : 0 < p j * (1 - p j) := mul_pos (hp0 j) (hq0 j)
    have hs : 0 < sdev (m j) (p j) := Real.sqrt_pos.2 (mul_pos hMj hpq)
    have h1 : |a j| ≤ R * sdev (m j) (p j) := by
      unfold zscore at hj
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs] at hj
      exact hj
    have h2 : sdev (m j) (p j) ≤ √(M j) := by
      apply Real.sqrt_le_sqrt
      have : p j * (1 - p j) ≤ 1 := by nlinarith [hp0 j, hp1 j]
      show (m j : ℝ) * (p j * (1 - p j)) ≤ (m j : ℝ)
      have hMj' : (0 : ℝ) < (m j : ℝ) := hMj
      nlinarith
    have hR2 : R ≤ R' := le_abs_self R
    have h0 : 0 ≤ sdev (m j) (p j) := hs.le
    calc |a j| ≤ R * sdev (m j) (p j) := h1
      _ ≤ R' * sdev (m j) (p j) := mul_le_mul_of_nonneg_right hR2 h0
      _ ≤ R' * √(M j) := mul_le_mul_of_nonneg_left h2 hR0
  -- `√M → ∞`
  have hsqrtM : Tendsto (fun j => √(M j)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hMt
  have hinv : Tendsto (fun j => R' / √(M j)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop hsqrtM R'
  -- `a / M → 0`
  have hamb : ∀ᶠ j in atTop, |a j / M j| ≤ R' / √(M j) := by
    filter_upwards [ha, hMpos] with j hj hMj
    have hs : 0 < √(M j) := Real.sqrt_pos.2 hMj
    rw [abs_div, abs_of_pos hMj, div_le_div_iff₀ hMj hs]
    have hsq : √(M j) * √(M j) = M j := Real.mul_self_sqrt hMj.le
    calc |a j| * √(M j) ≤ R' * √(M j) * √(M j) := mul_le_mul_of_nonneg_right hj hs.le
      _ = R' * M j := by rw [mul_assoc, hsq]
  have hxp : Tendsto (fun j => x j - p j) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => a j / M j) atTop (𝓝 0) :=
      squeeze_zero_norm' (hamb.mono fun j hj => by rw [Real.norm_eq_abs]; exact hj) hinv
    refine h1.congr' ?_
    filter_upwards [hMpos] with j hMj
    show a j / M j = x j - p j
    simp only [a, x]
    field_simp
  have hxclose : ∀ᶠ j in atTop, |x j - p j| ≤ l / 2 := by
    have := (tendsto_order.1 hxp.abs).2 (l / 2) (by simp only [abs_zero]; linarith)
    exact this.mono fun j hj => hj.le
  have hxI : ∀ᶠ j in atTop, l / 2 ≤ x j ∧ x j ≤ 1 - l / 2 := by
    filter_upwards [hxclose] with j hj
    have := abs_le.1 hj
    have h1 := (hp j).1
    have h2 := (hp j).2
    constructor <;> linarith [this.1, this.2]
  -- `k` and `n'`
  have hkge : ∀ᶠ j in atTop, l / 2 * M j ≤ (k j : ℝ) := by
    filter_upwards [hxI, hMpos] with j hj hMj
    have := hj.1
    simp only [x] at this
    rwa [le_div_iff₀ hMj] at this
  have hkle : ∀ᶠ j in atTop, (k j : ℝ) + l / 2 * M j ≤ M j := by
    filter_upwards [hxI, hMpos] with j hj hMj
    have := hj.2
    simp only [x] at this
    rw [div_le_iff₀ hMj] at this
    nlinarith
  have hkm : ∀ᶠ j in atTop, k j ≤ m j := by
    filter_upwards [hkle, hMpos] with j hj hMj
    have h : (k j : ℝ) ≤ (m j : ℝ) := by
      have : 0 < l / 2 * M j := by positivity
      show (k j : ℝ) ≤ M j
      linarith
    exact_mod_cast h
  let n' : ℕ → ℕ := fun j => m j - k j
  have hn'cast : ∀ᶠ j in atTop, (n' j : ℝ) = M j - (k j : ℝ) := by
    filter_upwards [hkm] with j hj
    simp only [n', M]
    rw [Nat.cast_sub hj]
  have hlM : Tendsto (fun j => l / 2 * M j) atTop atTop :=
    hMt.const_mul_atTop (by positivity)
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_natCast_atTop_iff (R := ℝ) |>.1
    exact tendsto_atTop_mono' _ hkge hlM
  have hn't : Tendsto n' atTop atTop := by
    apply tendsto_natCast_atTop_iff (R := ℝ) |>.1
    refine tendsto_atTop_mono' _ ?_ hlM
    filter_upwards [hn'cast, hkle] with j h1 h2
    rw [h1]; linarith
  -- Stirling factors
  have hst : Tendsto (fun j => Stirling.stirlingSeq (m j)
      / (Stirling.stirlingSeq (k j) * Stirling.stirlingSeq (n' j))) atTop (𝓝 (√π)⁻¹) := by
    have h1 := Stirling.tendsto_stirlingSeq_sqrt_pi.comp hm
    have h2 := Stirling.tendsto_stirlingSeq_sqrt_pi.comp hkt
    have h3 := Stirling.tendsto_stirlingSeq_sqrt_pi.comp hn't
    have hpi : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    have := h1.div (h2.mul h3) (mul_ne_zero hpi hpi)
    have e : √π / (√π * √π) = (√π)⁻¹ := by field_simp
    rw [e] at this
    exact this
  -- the `G` factor
  let G : ℕ → ℝ := fun j => p j * (1 - p j) / (x j * (1 - x j))
  have hGt : Tendsto G atTop (𝓝 1) := by
    have h1 : ∀ᶠ j in atTop, |G j - 1| ≤ |x j - p j| * (4 / l ^ 2) := by
      filter_upwards [hxI] with j hj
      have hx1 : 0 < x j := by linarith [hj.1]
      have hx2 : 0 < 1 - x j := by linarith [hj.2]
      have hxx : l ^ 2 / 4 ≤ x j * (1 - x j) := by
        have h3 : l / 2 ≤ 1 - x j := by linarith [hj.2]
        have := mul_le_mul hj.1 h3 (by positivity) hx1.le
        nlinarith
      have hxxpos : 0 < x j * (1 - x j) := mul_pos hx1 hx2
      have e : G j - 1 = (x j - p j) * (x j + p j - 1) / (x j * (1 - x j)) := by
        simp only [G]
        field_simp
        ring
      rw [e, abs_div, abs_mul, abs_of_pos hxxpos, div_le_iff₀ hxxpos]
      have hb : |x j + p j - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith [hj.1, hj.2, hp0 j, hp1 j]
      have h4 : 0 ≤ |x j - p j| := abs_nonneg _
      have h5 : (4 / l ^ 2) * (x j * (1 - x j)) ≥ 1 := by
        have : (4 / l ^ 2) * (l ^ 2 / 4) = 1 := by field_simp
        have hpos : 0 < 4 / l ^ 2 := by positivity
        nlinarith
      nlinarith
    have h2 : Tendsto (fun j => |x j - p j| * (4 / l ^ 2)) atTop (𝓝 0) := by
      have := hxp.abs.mul_const (4 / l ^ 2)
      simpa using this
    have h3 : Tendsto (fun j => G j - 1) atTop (𝓝 0) :=
      squeeze_zero_norm' (h1.mono fun j hj => by simpa [Real.norm_eq_abs] using hj) h2
    have := h3.add_const 1
    simpa using this
  have hsqrtG : Tendsto (fun j => √(G j / 2)) atTop (𝓝 (√(1 / 2))) :=
    (hGt.div_const 2).sqrt
  -- the remainder in the entropy expansion
  let T : ℕ → ℝ := fun j => (k j : ℝ) * log ((k j : ℝ) / (M j * p j))
    + (n' j : ℝ) * log ((n' j : ℝ) / (M j * (1 - p j)))
  let rr : ℕ → ℝ := fun j => T j - (a j) ^ 2 / (2 * (M j * (p j * (1 - p j))))
  have hrb : ∀ᶠ j in atTop, |rr j| ≤ 8 * R' ^ 3 / l ^ 2 / √(M j) := by
    have hs1 : ∀ᶠ j in atTop, R' / √(M j) ≤ l / 2 := by
      have := (tendsto_order.1 hinv).2 (l / 2) (by linarith)
      exact this.mono fun j hj => hj.le
    filter_upwards [ha, hamb, hs1, hMpos, hn'cast] with j h1 h2 h3 hMj hn
    have hMpj : 0 < M j * p j := mul_pos hMj (hp0 j)
    have hMqj : 0 < M j * (1 - p j) := mul_pos hMj (hq0 j)
    have hamj : |a j / M j| ≤ l / 2 := h2.trans h3
    have hAl : |a j| ≤ l / 2 * M j := by
      rw [abs_div, abs_of_pos hMj, div_le_iff₀ hMj] at hamj
      exact hamj
    have hw1 : |a j / (M j * p j)| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hMpj, div_le_iff₀ hMpj]
      have : l * M j ≤ p j * M j := mul_le_mul_of_nonneg_right (hp j).1 hMj.le
      nlinarith
    have hw2 : |a j / (M j * (1 - p j))| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hMqj, div_le_iff₀ hMqj]
      have : l * M j ≤ (1 - p j) * M j := mul_le_mul_of_nonneg_right (hql j) hMj.le
      nlinarith
    have hsum : (k j : ℝ) + (n' j : ℝ) = M j := by rw [hn]; ring
    have h := entropy_expansion hMj (hp0 j) (hp1 j) hsum hw1 hw2
    refine h.trans ?_
    have hs : 0 < √(M j) := Real.sqrt_pos.2 hMj
    have hsq : √(M j) * √(M j) = M j := Real.mul_self_sqrt hMj.le
    have hA3 : |a j| ^ 3 ≤ (R' * √(M j)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
    have hp2 : 1 / (M j * p j) ^ 2 ≤ 1 / (M j * l) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hp j).1 hMj.le) 2
    have hq2 : 1 / (M j * (1 - p j)) ^ 2 ≤ 1 / (M j * l) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hql j) hMj.le) 2
    calc 4 * |(k j : ℝ) - M j * p j| ^ 3 * (1 / (M j * p j) ^ 2 + 1 / (M j * (1 - p j)) ^ 2)
        ≤ 4 * (R' * √(M j)) ^ 3 * (1 / (M j * l) ^ 2 + 1 / (M j * l) ^ 2) := by
          have hnn : 0 ≤ 1 / (M j * p j) ^ 2 + 1 / (M j * (1 - p j)) ^ 2 := by positivity
          have hle : |(k j : ℝ) - M j * p j| ^ 3 ≤ (R' * √(M j)) ^ 3 := hA3
          gcongr
      _ = 8 * R' ^ 3 / l ^ 2 / √(M j) := by
          have hM2 : M j ^ 2 = √(M j) ^ 4 := by
            rw [show √(M j) ^ 4 = (√(M j) * √(M j)) ^ 2 by ring, hsq]
          field_simp
          rw [hM2]
          ring
  have hrt : Tendsto rr atTop (𝓝 0) := by
    have h2 : Tendsto (fun j => 8 * R' ^ 3 / l ^ 2 / √(M j)) atTop (𝓝 0) :=
      Tendsto.const_div_atTop hsqrtM _
    exact squeeze_zero_norm' (hrb.mono fun j hj => by simpa [Real.norm_eq_abs] using hj) h2
  have hexpr : Tendsto (fun j => exp (-rr j)) atTop (𝓝 1) := by
    have h := hrt.neg
    rw [neg_zero] at h
    have := (Real.continuous_exp.tendsto 0).comp h
    rw [Real.exp_zero] at this
    exact this
  -- assembling
  let bracket : ℕ → ℝ := fun j =>
    (Stirling.stirlingSeq (m j) / (Stirling.stirlingSeq (k j) * Stirling.stirlingSeq (n' j)))
      * √(G j / 2) * exp (-rr j) - (√(2 * π))⁻¹
  have hbr : Tendsto bracket atTop (𝓝 0) := by
    have h := ((hst.mul hsqrtG).mul hexpr).sub_const (√(2 * π))⁻¹
    have e : (√π)⁻¹ * √(1 / 2) * 1 - (√(2 * π))⁻¹ = 0 := by
      have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
      have h2 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_div (by norm_num)]
      simp only [Real.sqrt_one]
      field_simp
      ring
    rw [e] at h
    exact h
  have heq : ∀ᶠ j in atTop,
      sdev (m j) (p j) * bpmf (m j) (p j) (k j) - phi (zscore (m j) (p j) (k j))
        = bracket j * exp (-(zscore (m j) (p j) (k j)) ^ 2 / 2) := by
    have hk1 := hkt.eventually_ge_atTop 1
    have hn1 := hn't.eventually_ge_atTop 1
    filter_upwards [hk1, hn1, hkm, hMpos, hn'cast] with j hkj hnj hkmj hMj hn
    have hmeq : m j = k j + n' j := by simp only [n']; omega
    have hform := bpmf_stirling_form (k := k j) (n' := n' j) hkj hnj (hp0 j) (hp1 j)
    rw [← hmeq] at hform
    have hkr : (0 : ℝ) < k j := by exact_mod_cast hkj
    have hnr : (0 : ℝ) < n' j := by exact_mod_cast hnj
    have hpq : 0 < p j * (1 - p j) := mul_pos (hp0 j) (hq0 j)
    have hsdpos : 0 < sdev (m j) (p j) := Real.sqrt_pos.2 (mul_pos hMj hpq)
    have hsdsq : sdev (m j) (p j) * sdev (m j) (p j) = M j * (p j * (1 - p j)) :=
      Real.mul_self_sqrt (mul_pos hMj hpq).le
    -- `σ D = √(G/2)`
    have hx1 : x j = (k j : ℝ) / M j := rfl
    have hx2 : 1 - x j = (n' j : ℝ) / M j := by
      rw [hn, hx1]; field_simp
    have hGeq : G j / 2 = (M j * (p j * (1 - p j))) * (2 * M j) / ((2 * (k j : ℝ)) * (2 * (n' j : ℝ))) := by
      simp only [G]
      rw [hx2, hx1]
      field_simp
    have hD : sdev (m j) (p j) * (√(2 * ((m j : ℕ) : ℝ)) / (√(2 * (k j : ℝ)) * √(2 * (n' j : ℝ))))
        = √(G j / 2) := by
      rw [hGeq]
      show √((m j : ℝ) * (p j * (1 - p j))) * _ = _
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity : (0 : ℝ) ≤ M j * (p j * (1 - p j))),
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (k j : ℝ))]
      show √(M j * (p j * (1 - p j))) * _ = _
      ring
    -- exponent
    have hzsq : (zscore (m j) (p j) (k j)) ^ 2 = (a j) ^ 2 / (M j * (p j * (1 - p j))) := by
      unfold zscore
      rw [div_pow]
      congr 1
      rw [sq, hsdsq]
    have hT : T j = (zscore (m j) (p j) (k j)) ^ 2 / 2 + rr j := by
      rw [hzsq]
      simp only [rr]
      field_simp
      ring
    have hexpT : exp (-T j) = exp (-(zscore (m j) (p j) (k j)) ^ 2 / 2) * exp (-rr j) := by
      rw [← exp_add, hT]
      congr 1
      ring
    have hTdef : exp (-((k j : ℝ) * log ((k j : ℝ) / (((m j : ℕ) : ℝ) * p j))
          + (n' j : ℝ) * log ((n' j : ℝ) / (((m j : ℕ) : ℝ) * (1 - p j))))) = exp (-T j) := rfl
    rw [hform, hTdef, hexpT]
    simp only [bracket, phi]
    have hD' := hD
    calc sdev (m j) (p j) * (Stirling.stirlingSeq (m j)
          / (Stirling.stirlingSeq (k j) * Stirling.stirlingSeq (n' j))
          * (√(2 * ((m j : ℕ) : ℝ)) / (√(2 * (k j : ℝ)) * √(2 * (n' j : ℝ))))
          * (exp (-(zscore (m j) (p j) (k j)) ^ 2 / 2) * exp (-rr j)))
          - (√(2 * π))⁻¹ * exp (-(zscore (m j) (p j) (k j)) ^ 2 / 2)
        = (Stirling.stirlingSeq (m j)
          / (Stirling.stirlingSeq (k j) * Stirling.stirlingSeq (n' j)))
          * (sdev (m j) (p j) * (√(2 * ((m j : ℕ) : ℝ)) / (√(2 * (k j : ℝ)) * √(2 * (n' j : ℝ)))))
          * exp (-rr j) * exp (-(zscore (m j) (p j) (k j)) ^ 2 / 2)
          - (√(2 * π))⁻¹ * exp (-(zscore (m j) (p j) (k j)) ^ 2 / 2) := by ring
      _ = _ := by rw [hD']; ring
  have hbound : ∀ᶠ j in atTop,
      ‖sdev (m j) (p j) * bpmf (m j) (p j) (k j) - phi (zscore (m j) (p j) (k j))‖ ≤ |bracket j| := by
    filter_upwards [heq] with j hj
    rw [hj, Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    have : exp (-(zscore (m j) (p j) (k j)) ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg (zscore (m j) (p j) (k j))]
    have h0 := abs_nonneg (bracket j)
    nlinarith
  have := hbr.abs
  simp only [abs_zero] at this
  exact squeeze_zero_norm' hbound this

end NoisyVD
