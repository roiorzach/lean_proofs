import NoisyVD.Cutoff
import NoisyVD.LocalBinomial

/-!
# Asymptotics of the pivotal probability under threshold rules

The estimates that drive Lemma `lemma_threshold_value`:

* `pivot_tail_uniform` is the application of Lemma `lemma_local_binomial` in the paper's proof, with
  `ℓ = -1`, `x = σ y_{ω,n}` and `t = (T_n - 1 - ns)/√n` for the pivotal probability, and `ℓ = 0`,
  `t = (T_n - ns)/√n` for the tail;
* `tendsto_sqrt_mul_F_sub` is the expansion `F(x) = s + tx + o(x)`;
* `btail_le_of_gap` and `one_sub_btail_le` are Chebyshev's inequality for threshold rules.
-/

open Set Filter Topology Real

namespace NoisyVD

/-- `Pr(Bin(m,p) = T-1)`, the probability of being pivotal at threshold `T`. -/
noncomputable def rho (m : ℕ) (p : ℝ) (T : ℕ) : ℝ := if T = 0 then 0 else bpmf m p (T - 1)

lemma rho_nonneg {m T : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ rho m p T := by
  unfold rho
  split_ifs
  · exact le_rfl
  · exact bpmf_nonneg h0 h1

lemma continuous_rho (m T : ℕ) : Continuous fun p => rho m p T := by
  unfold rho
  split_ifs
  · exact continuous_const
  · exact continuous_bpmf _ _

lemma rho_le_mass {m T : ℕ} (hm : 1 ≤ m) {l p : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2)
    (hp : p ∈ Icc l (1 - l)) : rho m p T ≤ massConst l / √(m : ℝ) := by
  unfold rho
  split_ifs
  · have := massConst_pos hl hl'
    positivity
  · exact bpmf_le_massConst hm hl hl' hp _

/-- `u = (T - np)/(σ√n)`, which equals `c - y` for `c = (T - ns)/(σ√n)` and `y = √n (p - s)/σ`. -/
noncomputable def uStat (s : ℝ) (n T : ℕ) (p : ℝ) : ℝ :=
  ((T : ℝ) - n * p) / (√(s * (1 - s)) * √(n : ℝ))

lemma uStat_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {n : ℕ} (hn : 1 ≤ n) (T : ℕ) (p : ℝ) :
    uStat s n T p = ((T : ℝ) - n * s) / (√(s * (1 - s)) * √(n : ℝ)) - √(n : ℝ) * (p - s) / √(s * (1 - s)) := by
  have hS : 0 < √(s * (1 - s)) := Real.sqrt_pos.2 (mul_pos hs0 (by linarith))
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
  have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hnr.le
  unfold uStat
  field_simp
  rw [show √(n : ℝ) ^ 2 = √(n : ℝ) * √(n : ℝ) by ring, hsq]
  ring

/-- **The application of Lemma `lemma_local_binomial`** in the proof of Lemma `lemma_threshold_value`.
Uniformly over thresholds `T` and probabilities `p` with `c = (T - ns)/(σ√n)` and `y = √n (p - s)/σ` bounded,
`√n Pr(Bin(n-1,p) = T-1) - φ(u)/σ → 0` and `Pr(Bin(n,p) ≥ T) - Φ(-u) → 0`, where `u = c - y`. -/
theorem pivot_tail_uniform {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (T : ℕ) (p : ℝ),
      |√(n : ℝ) * (p - s) / √(s * (1 - s))| ≤ K →
      |((T : ℝ) - n * s) / (√(s * (1 - s)) * √(n : ℝ))| ≤ K →
      |√(n : ℝ) * rho (n - 1) p T - phi (uStat s n T p) / √(s * (1 - s))| < ε ∧
        |btail n p T - Phi (-uStat s n T p)| < ε := by
  have hS : 0 < s * (1 - s) := mul_pos hs0 (by linarith)
  set σ := √(s * (1 - s)) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hS
  obtain ⟨N₁, hN₁⟩ := lemma_local_binomial.2 s hs0 hs1 (σ * |K| + 1) 1 (ε / 2) (by linarith)
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => (phi 0 / (σ * σ)) / √(n : ℝ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop hsq _
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (((tendsto_order.1 hsmall).2 (ε / 2) (by linarith)).and
    ((hsq.eventually_gt_atTop (σ * |K| / s)).and
      ((hsq.eventually_ge_atTop 1).and (eventually_ge_atTop 2))))
  refine ⟨max N₁ N₂, fun n hn T p hy hc => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN₂ n ((le_max_right _ _).trans hn)
  have hnN₁ : n ≥ N₁ := (le_max_left _ _).trans hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
  have hsqn : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hnr.le
  set c := ((T : ℝ) - n * s) / (σ * √(n : ℝ)) with hcdef
  set y := √(n : ℝ) * (p - s) / σ with hydef
  have hu : uStat s n T p = c - y := uStat_eq hs0 hs1 (by omega) T p
  have hcK : |c| ≤ |K| := hc.trans (le_abs_self K)
  have hyK : |y| ≤ |K| := hy.trans (le_abs_self K)
  -- `T ≥ 1`
  have hT1 : 1 ≤ T := by
    have hT0 : (0 : ℝ) < T := by
      have e : (T : ℝ) = n * s + σ * √(n : ℝ) * c := by
        rw [hcdef]
        field_simp
        ring
      rw [e]
      have h5 : -|K| ≤ c := (abs_le.1 hcK).1
      have h6 : σ * √(n : ℝ) * (-|K|) ≤ σ * √(n : ℝ) * c :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
      rw [div_lt_iff₀ hs0] at h2
      nlinarith
    exact_mod_cast hT0
  -- the parameters of Lemma `lemma_local_binomial`
  set x := σ * y with hx
  set t₀ := σ * c with ht₀
  set t₁ := t₀ - 1 / √(n : ℝ) with ht₁
  have hinv : 1 / √(n : ℝ) ≤ 1 := by
    rw [div_le_one hsn]
    exact h3
  have hinv0 : 0 < 1 / √(n : ℝ) := by positivity
  have hxK : |x| ≤ σ * |K| + 1 := by
    rw [hx, abs_mul, abs_of_pos hσ]
    nlinarith [mul_le_mul_of_nonneg_left hyK hσ.le]
  have ht₀K : |t₀| ≤ σ * |K| + 1 := by
    rw [ht₀, abs_mul, abs_of_pos hσ]
    nlinarith [mul_le_mul_of_nonneg_left hcK hσ.le]
  have ht₁K : |t₁| ≤ σ * |K| + 1 := by
    have h5 := abs_sub t₀ (1 / √(n : ℝ))
    rw [abs_of_pos hinv0] at h5
    have h6 : |t₀| ≤ σ * |K| := by
      rw [ht₀, abs_mul, abs_of_pos hσ]
      exact mul_le_mul_of_nonneg_left hcK hσ.le
    rw [ht₁]
    linarith
  have hpar : s + x / √(n : ℝ) = p := by
    rw [hx, hydef]
    field_simp
    ring
  have hfloor₀ : ⌊(n : ℝ) * s + t₀ * √(n : ℝ)⌋₊ = T := by
    have e : (n : ℝ) * s + t₀ * √(n : ℝ) = T := by
      rw [ht₀, hcdef]
      field_simp
      ring
    rw [e, Nat.floor_natCast]
  have hfloor₁ : ⌊(n : ℝ) * s + t₁ * √(n : ℝ)⌋₊ = T - 1 := by
    have e : (n : ℝ) * s + t₁ * √(n : ℝ) = ((T - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hT1, ht₁, ht₀, hcdef]
      field_simp
      push_cast
      ring
    rw [e, Nat.floor_natCast]
  have hl₁ : ((n : ℤ) + (-1 : ℤ)).toNat = n - 1 := by omega
  have hl₀ : ((n : ℤ) + (0 : ℤ)).toNat = n := by omega
  have hA := (hN₁ n hnN₁ x t₁ hxK ht₁K (-1) (by simp)).1
  have hB := (hN₁ n hnN₁ x t₀ hxK ht₀K 0 (by simp)).2
  rw [hl₁, hpar, hfloor₁] at hA
  rw [hl₀, hpar, hfloor₀] at hB
  constructor
  · -- the pivotal probability
    have hρ : rho (n - 1) p T = bpmf (n - 1) p (T - 1) := by
      unfold rho
      rw [ite_eq_right (by omega)]
    rw [hρ, hu]
    have e1 : (t₁ - x) / σ = (c - y) - 1 / (σ * √(n : ℝ)) := by
      rw [ht₁, ht₀, hx]
      field_simp
      ring
    rw [e1] at hA
    have h5 := abs_phi_sub_le ((c - y) - 1 / (σ * √(n : ℝ))) (c - y)
    rw [show (c - y) - 1 / (σ * √(n : ℝ)) - (c - y) = -(1 / (σ * √(n : ℝ))) by ring, abs_neg,
      abs_of_pos (by positivity : 0 < 1 / (σ * √(n : ℝ)))] at h5
    have h6 : 1 / σ * |phi ((c - y) - 1 / (σ * √(n : ℝ))) - phi (c - y)|
        ≤ (phi 0 / (σ * σ)) / √(n : ℝ) := by
      calc 1 / σ * |phi ((c - y) - 1 / (σ * √(n : ℝ))) - phi (c - y)|
          ≤ 1 / σ * (phi 0 * (1 / (σ * √(n : ℝ)))) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = (phi 0 / (σ * σ)) / √(n : ℝ) := by field_simp
    have e2 : √(n : ℝ) * bpmf (n - 1) p (T - 1) - phi (c - y) / σ
        = (√(n : ℝ) * bpmf (n - 1) p (T - 1) - 1 / σ * phi ((c - y) - 1 / (σ * √(n : ℝ))))
          + 1 / σ * (phi ((c - y) - 1 / (σ * √(n : ℝ))) - phi (c - y)) := by
      ring
    rw [e2]
    refine lt_of_le_of_lt (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / σ)]
    linarith
  · -- the tail
    rw [hu, Phi_neg]
    have e1 : (t₀ - x) / σ = c - y := by
      rw [ht₀, hx]
      field_simp
    rw [e1] at hB
    have e2 : 1 - (1 - Phi (c - y)) = Phi (c - y) := by ring
    have e3 : btail n p T - (1 - Phi (-(c - y))) = btail n p T - (1 - (1 - Phi (c - y))) := by
      rw [Phi_neg]
    linarith

/-- The first-order expansion `F(x) = s + tx + o(x)`: if `√n x_j` is bounded then
`√n (F(x_j) - s - t x_j) → 0`. -/
theorem tendsto_sqrt_mul_F_err {F : ℝ → ℝ} {t s : ℝ} (hF : HasDerivAt F t 0) (hFs : F 0 = s)
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {x : ℕ → ℝ} {C : ℝ}
    (hb : ∀ᶠ j in atTop, |√(n j : ℝ) * x j| ≤ C) :
    Tendsto (fun j => √(n j : ℝ) * (F (x j) - s - t * x j)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun j => √(n j : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hx : Tendsto x atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => C / √(n j : ℝ)) atTop (𝓝 0) := Tendsto.const_div_atTop hsq C
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [hb, hsq.eventually_gt_atTop 0] with j hj hj0
    rw [Real.norm_eq_abs, le_div_iff₀ hj0]
    rwa [abs_mul, abs_of_pos hj0, mul_comm] at hj
  have hlo := hasDerivAt_iff_isLittleO_nhds_zero.1 hF
  rw [Metric.tendsto_nhds]
  intro c hc
  set c' : ℝ := c / (2 * (|C| + 1)) with hc'
  have hc'pos : 0 < c' := by rw [hc']; positivity
  have hlo2 := (Asymptotics.isLittleO_iff.1 hlo) hc'pos
  filter_upwards [hx.eventually hlo2, hb] with j hj hbj
  simp only [zero_add, smul_eq_mul, Real.norm_eq_abs, hFs] at hj
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [show F (x j) - s - t * x j = F (x j) - s - x j * t by ring]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hbj
  calc √(n j : ℝ) * |F (x j) - s - x j * t| ≤ √(n j : ℝ) * (c' * |x j|) :=
        mul_le_mul_of_nonneg_left hj (Real.sqrt_nonneg _)
    _ = c' * (√(n j : ℝ) * |x j|) := by ring
    _ ≤ c' * (|C| + 1) :=
        mul_le_mul_of_nonneg_left (hbj.trans ((le_abs_self C).trans (by linarith))) hc'pos.le
    _ < c := by
        rw [hc']
        have hpos : 0 < 2 * (|C| + 1) := by positivity
        rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
        nlinarith [abs_nonneg C]

/-- The first-order expansion `F(x) = s + tx + o(x)`: if `√n x_j → A` then `√n (F(x_j) - s) → t A`. -/
theorem tendsto_sqrt_mul_F_sub {F : ℝ → ℝ} {t s : ℝ} (hF : HasDerivAt F t 0) (hFs : F 0 = s)
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {x : ℕ → ℝ} {A : ℝ}
    (hA : Tendsto (fun j => √(n j : ℝ) * x j) atTop (𝓝 A)) :
    Tendsto (fun j => √(n j : ℝ) * (F (x j) - s)) atTop (𝓝 (t * A)) := by
  have hb : ∀ᶠ j in atTop, |√(n j : ℝ) * x j| ≤ |A| + 1 :=
    (tendsto_order.1 hA.abs).2 (|A| + 1) (by linarith) |>.mono fun j hj => hj.le
  have h1 := (tendsto_sqrt_mul_F_err hF hFs hn hb).add (hA.const_mul t)
  rw [zero_add] at h1
  refine h1.congr fun j => ?_
  ring

/-! ### Chebyshev's inequality for threshold rules -/

/-- If `T` is at least `a` below the mean, `1 - Pr(Bin(n,p) ≥ T) ≤ n/(4a²)`. -/
lemma one_sub_btail_le {n T : ℕ} {p a : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (ha : 0 < a)
    (hT : (T : ℝ) + a ≤ n * p) : 1 - btail n p T ≤ n / (4 * a ^ 2) := by
  have hsum : 1 - btail n p T
      = ∑ k ∈ Finset.range (n + 1), if T ≤ k then 0 else bpmf n p k := by
    rw [← bpmf_sum n p]
    unfold btail
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have hcheb := bpmf_chebyshev (m := n) h0 h1 ha
  have hle : (∑ k ∈ Finset.range (n + 1), if T ≤ k then 0 else bpmf n p k)
      ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => a ≤ |(k : ℝ) - (n : ℝ) * p|), bpmf n p k := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : T ≤ k
    · rw [ite_eq_left hk]
      split_ifs
      · exact bpmf_nonneg h0 h1
      · exact le_rfl
    · rw [ite_eq_right hk]
      have hlt : (k : ℝ) + 1 ≤ T := by exact_mod_cast (not_le.1 hk)
      rw [ite_eq_left]
      rw [abs_sub_comm, le_abs]
      left
      linarith
  have hpq : (n : ℝ) * p * (1 - p) / a ^ 2 ≤ n / (4 * a ^ 2) := by
    have hq : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs : 0 ≤ (n : ℝ) * a ^ 2 := by positivity
    nlinarith
  rw [hsum]
  exact hle.trans (hcheb.trans hpq)

/-- If `T` is at least `a` above the mean, `Pr(Bin(n,p) ≥ T) ≤ n/(4a²)`. -/
lemma btail_le_of_gap {n T : ℕ} {p a : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (ha : 0 < a)
    (hT : (n : ℝ) * p + a ≤ T) : btail n p T ≤ n / (4 * a ^ 2) := by
  have hcheb := bpmf_chebyshev (m := n) h0 h1 ha
  have hle : btail n p T
      ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => a ≤ |(k : ℝ) - (n : ℝ) * p|), bpmf n p k := by
    unfold btail
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : T ≤ k
    · rw [ite_eq_left hk]
      have hk' : (T : ℝ) ≤ k := by exact_mod_cast hk
      rw [ite_eq_left]
      rw [le_abs]
      left
      linarith
    · rw [ite_eq_right hk]
      split_ifs
      · exact bpmf_nonneg h0 h1
      · exact le_rfl
  have hpq : (n : ℝ) * p * (1 - p) / a ^ 2 ≤ n / (4 * a ^ 2) := by
    have hq : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs : 0 ≤ (n : ℝ) * a ^ 2 := by positivity
    nlinarith
  exact hle.trans (hcheb.trans hpq)

end NoisyVD
