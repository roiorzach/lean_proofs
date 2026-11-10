import ConformityConcerns.LearnTheta.Defs
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Convergence facts when the beliefs `η t` concentrate at `c`

If `∫ (y - c)² dη_t → 0`, then integrals `∫ f x y dη_t` of continuous integrands with quadratic
growth converge to `f x c` uniformly in `x` on compact intervals; in particular
`mfun ψ (η t) → (x - c)²` uniformly on compact intervals. We also bound the tails of the type
distribution `η t ∗ G`.
-/

namespace CC.LearnTheta.PoolTailAux

open MeasureTheory Filter Topology Set

variable {η : ℕ → Measure ℝ} [∀ t, IsProbabilityMeasure (η t)] {c : ℝ}

/-- Uniform convergence of `∫ f x y dη_t` to `f x c` on a compact interval of `x`. -/
theorem eventually_unif_integral
    (hη2 : ∀ t, Integrable (fun y => (y - c) ^ 2) (η t))
    (hηc : Tendsto (fun t => ∫ y, (y - c) ^ 2 ∂η t) atTop (𝓝 0))
    {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) {lo hi A : ℝ}
    (hA : ∀ x ∈ Icc lo hi, ∀ y, |f x y| ≤ A * (1 + (y - c) ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ x ∈ Icc lo hi, |∫ y, f x y ∂η t - f x c| ≤ ε := by
  have hcomp : IsCompact (Icc lo hi ×ˢ Icc (c - 1) (c + 1)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨r, hr, hrf⟩ := Metric.uniformContinuousOn_iff_le.1
    (hcomp.uniformContinuousOn_of_continuous hf.continuousOn) (ε / 2) (by positivity)
  set r' := min r 1 with hr'
  have hr'0 : 0 < r' := lt_min hr one_pos
  have hr1 : r' ≤ 1 := min_le_right _ _
  have hrr : r' ≤ r := min_le_left _ _
  set A' := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  set M := A' * (2 / r' ^ 2 + 1) with hM
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ x ∈ Icc lo hi, ∀ y, |f x y - f x c| ≤ ε / 2 + M * (y - c) ^ 2 := by
    intro x hx y
    have hMy : 0 ≤ M * (y - c) ^ 2 := by positivity
    by_cases hy : |y - c| ≤ r'
    · have hy' := abs_le.1 hy
      have h1 : (x, y) ∈ Icc lo hi ×ˢ Icc (c - 1) (c + 1) :=
        ⟨hx, ⟨by linarith [hy'.1], by linarith [hy'.2]⟩⟩
      have h2 : (x, c) ∈ Icc lo hi ×ˢ Icc (c - 1) (c + 1) :=
        ⟨hx, ⟨by linarith, by linarith⟩⟩
      have h3 : dist (x, y) (x, c) ≤ r := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq]
        exact max_le hr.le (hy.trans hrr)
      have h4 := hrf _ h1 _ h2 h3
      rw [Real.dist_eq] at h4
      simp only [Function.uncurry_apply_pair] at h4
      linarith
    · push Not at hy
      have hA1 := hA x hx y
      have hA2 := hA x hx c
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        mul_one] at hA2
      have hsq : r' ^ 2 < (y - c) ^ 2 := by
        have := pow_lt_pow_left₀ hy hr'0.le (n := 2) two_ne_zero
        rwa [sq_abs] at this
      have h5 : 2 ≤ 2 / r' ^ 2 * (y - c) ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      have h6 : A * (1 + (y - c) ^ 2) ≤ A' * (1 + (y - c) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h7 : A ≤ A' := le_max_left _ _
      have h8 : A' * (2 + (y - c) ^ 2) ≤ M * (y - c) ^ 2 := by
        rw [hM, mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hA'0
        nlinarith
      have h9 := abs_sub (f x y) (f x c)
      nlinarith
  have hev : ∀ᶠ t in atTop, M * ∫ y, (y - c) ^ 2 ∂η t < ε / 2 := by
    have := hηc.const_mul M
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with t ht x hx
  have hcx : Continuous (f x) := hf.uncurry_left x
  have hint : Integrable (fun y => f x y) (η t) := by
    refine Integrable.mono' ((integrable_const A).add ((hη2 t).const_mul A))
      hcx.aestronglyMeasurable (Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs]
    have := hA x hx y
    have h' : A * (1 + (y - c) ^ 2) = A + A * (y - c) ^ 2 := by ring
    simp only [Pi.add_apply]
    linarith
  have heq : ∫ y, f x y ∂η t - f x c = ∫ y, (f x y - f x c) ∂η t := by
    rw [integral_sub hint (integrable_const _), integral_const]
    simp
  rw [heq]
  have hb := norm_integral_le_of_norm_le ((integrable_const (ε / 2)).add ((hη2 t).const_mul M))
    (Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hpt x hx y))
  simp only [Pi.add_apply] at hb
  rw [Real.norm_eq_abs, integral_add (integrable_const _) ((hη2 t).const_mul M), integral_const,
    integral_const_mul] at hb
  simp only [probReal_univ, smul_eq_mul, one_mul] at hb
  linarith

/-- `mfun ψ (η t) → (x - c)²` uniformly on compact intervals. -/
theorem mfun_unif {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x)
    (hψb : ∃ C, ∀ x, ψ x ≤ C)
    (hη2 : ∀ t, Integrable (fun y => (y - c) ^ 2) (η t))
    (hηc : Tendsto (fun t => ∫ y, (y - c) ^ 2 ∂η t) atTop (𝓝 0))
    (lo hi : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ x ∈ Icc lo hi, |mfun ψ (η t) x - (x - c) ^ 2| ≤ ε := by
  rcases (Icc lo hi).eq_empty_or_nonempty with hE | hne
  · exact Eventually.of_forall (fun t x hx => by rw [hE] at hx; exact absurd hx (notMem_empty x))
  obtain ⟨Cψ, hCψ⟩ := hψb
  obtain ⟨x₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (hψc.comp (continuous_id.sub continuous_const) (g := ψ) (f := fun x => x - c)).continuousOn
  set p := ψ (x₀ - c) with hpdef
  have hp : 0 < p := hψpos _
  have hpx : ∀ x ∈ Icc lo hi, p ≤ ψ (x - c) := fun x hx => hmin hx
  set R := max |lo - c| |hi - c| with hRdef
  have hR : ∀ x ∈ Icc lo hi, (x - c) ^ 2 ≤ R ^ 2 := by
    intro x hx
    have : |x - c| ≤ R := by
      rw [abs_le]; constructor
      · have := neg_abs_le (lo - c); have := le_max_left |lo - c| |hi - c|; linarith [hx.1]
      · have := le_abs_self (hi - c); have := le_max_right |lo - c| |hi - c|; linarith [hx.2]
    have h0 : 0 ≤ |x - c| := abs_nonneg _
    calc (x - c) ^ 2 = |x - c| ^ 2 := (sq_abs _).symm
      _ ≤ R ^ 2 := pow_le_pow_left₀ h0 this 2
  have hC0 : 0 ≤ Cψ := (hψpos 0).le.trans (hCψ 0)
  set ε₀ := min (p / 2) (ε * p / (4 * (R ^ 2 + 1))) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by positivity)
  have hε₀1 : ε₀ ≤ p / 2 := min_le_left _ _
  have hε₀2 : ε₀ ≤ ε * p / (4 * (R ^ 2 + 1)) := min_le_right _ _
  have hε₀3 : ε₀ * (R ^ 2 + 1) ≤ ε * p / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    rw [le_div_iff₀ (by positivity)] at hε₀2
    linarith
  have hD := eventually_unif_integral hη2 hηc (f := fun x y => ψ (x - y))
    (hψc.comp (continuous_fst.sub continuous_snd)) (A := Cψ) (lo := lo) (hi := hi)
    (fun x _ y => by
      rw [abs_of_pos (hψpos _)]
      have : 0 ≤ Cψ * (y - c) ^ 2 := by positivity
      linarith [hCψ (x - y)]) hε₀
  have hN := eventually_unif_integral hη2 hηc (f := fun x y => (x - y) ^ 2 * ψ (x - y))
    (by change Continuous (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2 * ψ (p.1 - p.2)); fun_prop)
    (A := 2 * Cψ * (R ^ 2 + 1)) (lo := lo) (hi := hi)
    (fun x hx y => by
      have hψ0 := hψpos (x - y)
      rw [abs_of_nonneg (by positivity)]
      have h1 : (x - y) ^ 2 ≤ 2 * (x - c) ^ 2 + 2 * (y - c) ^ 2 := by
        nlinarith [sq_nonneg (x - c + (y - c))]
      have h2 : (x - y) ^ 2 * ψ (x - y) ≤ (x - y) ^ 2 * Cψ :=
        mul_le_mul_of_nonneg_left (hCψ _) (sq_nonneg _)
      have h3 := hR x hx
      nlinarith [mul_nonneg hC0 (mul_nonneg (sq_nonneg R) (sq_nonneg (y - c))),
        mul_nonneg hC0 (sq_nonneg (y - c))]) hε₀
  filter_upwards [hD, hN] with t hDt hNt x hx
  have h1 := hDt x hx
  have h2 := hNt x hx
  have hd := hpx x hx
  have hRx := hR x hx
  set D := ∫ y, ψ (x - y) ∂η t with hDdef
  set N := ∫ y, (x - y) ^ 2 * ψ (x - y) ∂η t with hNdef
  set q := (x - c) ^ 2 with hq
  have hq0 : 0 ≤ q := sq_nonneg _
  have hDpos : p / 2 ≤ D := by
    have := (abs_le.1 h1).1
    linarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDpos
  have h3 : |q * (D - ψ (x - c))| ≤ R ^ 2 * ε₀ := by
    rw [abs_mul, abs_of_nonneg hq0]
    exact mul_le_mul hRx h1 (abs_nonneg _) (by positivity)
  have h4 : |N - q * D| ≤ ε * p / 4 := by
    have : N - q * D = (N - q * ψ (x - c)) - q * (D - ψ (x - c)) := by ring
    rw [this]
    have h5 := abs_sub (N - q * ψ (x - c)) (q * (D - ψ (x - c)))
    have h6 : N - q * ψ (x - c) = N - (x - c) ^ 2 * ψ (x - c) := rfl
    rw [h6] at h5
    nlinarith
  have hm : mfun ψ (η t) x = N / D := rfl
  rw [hm]
  have : N / D - q = (N - q * D) / D := by field_simp
  rw [this, abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  nlinarith

/-- The upper tail of `η ∗ G` splits into a far deviation of `y` and a tail of `G`. -/
theorem conv_Ioi_le (η G : Measure ℝ) [IsProbabilityMeasure η] [IsProbabilityMeasure G]
    (c : ℝ) {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    Measure.conv η G (Ioi u) ≤ η {y | r ^ 2 ≤ (y - c) ^ 2} + G (Ioi (u - c - r)) := by
  rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Ioi]
  calc (η.prod G) ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Ioi u)
      ≤ (η.prod G) ({y | r ^ 2 ≤ (y - c) ^ 2} ×ˢ univ ∪ univ ×ˢ Ioi (u - c - r)) := by
        apply measure_mono
        intro p hp
        simp only [mem_preimage, mem_Ioi] at hp
        by_cases h : r ^ 2 ≤ (p.1 - c) ^ 2
        · left; exact ⟨h, mem_univ _⟩
        · right
          refine ⟨mem_univ _, ?_⟩
          push Not at h
          have := (abs_lt.1 (abs_lt_of_sq_lt_sq h hr)).2
          simp only [mem_Ioi]; linarith
    _ ≤ (η.prod G) ({y | r ^ 2 ≤ (y - c) ^ 2} ×ˢ univ) + (η.prod G) (univ ×ˢ Ioi (u - c - r)) :=
        measure_union_le _ _
    _ = _ := by
        rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, one_mul]

/-- The lower tail of `η ∗ G` splits into a far deviation of `y` and a tail of `G`. -/
theorem conv_Iio_le (η G : Measure ℝ) [IsProbabilityMeasure η] [IsProbabilityMeasure G]
    (c : ℝ) {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    Measure.conv η G (Iio u) ≤ η {y | r ^ 2 ≤ (y - c) ^ 2} + G (Iio (u - c + r)) := by
  rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Iio]
  calc (η.prod G) ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio u)
      ≤ (η.prod G) ({y | r ^ 2 ≤ (y - c) ^ 2} ×ˢ univ ∪ univ ×ˢ Iio (u - c + r)) := by
        apply measure_mono
        intro p hp
        simp only [mem_preimage, mem_Iio] at hp
        by_cases h : r ^ 2 ≤ (p.1 - c) ^ 2
        · left; exact ⟨h, mem_univ _⟩
        · right
          refine ⟨mem_univ _, ?_⟩
          push Not at h
          have := (abs_lt.1 (abs_lt_of_sq_lt_sq h hr)).1
          simp only [mem_Iio]; linarith
    _ ≤ (η.prod G) ({y | r ^ 2 ≤ (y - c) ^ 2} ×ˢ univ) + (η.prod G) (univ ×ˢ Iio (u - c + r)) :=
        measure_union_le _ _
    _ = _ := by
        rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, one_mul]

/-- Chebyshev: the mass of `η t` far from `c` vanishes. -/
theorem eventually_meas_far_lt (hη2 : ∀ t, Integrable (fun y => (y - c) ^ 2) (η t))
    (hηc : Tendsto (fun t => ∫ y, (y - c) ^ 2 ∂η t) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, η t {y | r ^ 2 ≤ (y - c) ^ 2} < ENNReal.ofReal ε := by
  have hev : ∀ᶠ t in atTop, ∫ y, (y - c) ^ 2 ∂η t < r ^ 2 * ε :=
    hηc.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with t ht
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun y => sq_nonneg (y - c))) (hη2 t) (r ^ 2)
  have h1 : (η t).real {y | r ^ 2 ≤ (y - c) ^ 2} < ε := by
    by_contra h
    push Not at h
    have : r ^ 2 * ε ≤ r ^ 2 * (η t).real {y | r ^ 2 ≤ (y - c) ^ 2} :=
      mul_le_mul_of_nonneg_left h (by positivity)
    linarith
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 h1

/-- The upper tail of a probability measure on `ℝ` vanishes. -/
theorem exists_Ioi_lt (G : Measure ℝ) [IsProbabilityMeasure G] {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, G (Ioi (N : ℝ)) < ENNReal.ofReal ε := by
  have h := tendsto_measure_iInter_atTop (μ := G) (s := fun n : ℕ => Ioi (n : ℝ))
    (fun n => measurableSet_Ioi.nullMeasurableSet)
    (fun i j hij => Ioi_subset_Ioi (Nat.cast_le.2 hij)) ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n : ℕ, Ioi (n : ℝ)) = ∅ := by
    rw [iInter_eq_empty_iff]
    intro x
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact ⟨n, fun h => absurd (mem_Ioi.1 h) (not_lt.2 hn)⟩
  rw [hempty, measure_empty] at h
  exact (h.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists

/-- The lower tail of a probability measure on `ℝ` vanishes. -/
theorem exists_Iio_lt (G : Measure ℝ) [IsProbabilityMeasure G] {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, G (Iio (-(N : ℝ))) < ENNReal.ofReal ε := by
  have h := tendsto_measure_iInter_atTop (μ := G) (s := fun n : ℕ => Iio (-(n : ℝ)))
    (fun n => measurableSet_Iio.nullMeasurableSet)
    (fun i j hij => Iio_subset_Iio (neg_le_neg (Nat.cast_le.2 hij))) ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n : ℕ, Iio (-(n : ℝ))) = ∅ := by
    rw [iInter_eq_empty_iff]
    intro x
    obtain ⟨n, hn⟩ := exists_nat_ge (-x)
    exact ⟨n, fun h => by have := mem_Iio.1 h; linarith⟩
  rw [hempty, measure_empty] at h
  exact (h.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists

lemma mfun_nonneg {ψ : ℝ → ℝ} (hψpos : ∀ x, 0 < ψ x) (η : Measure ℝ) (x : ℝ) :
    0 ≤ mfun ψ η x :=
  div_nonneg (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (hψpos _).le)
    (integral_nonneg fun _ => (hψpos _).le)

end CC.LearnTheta.PoolTailAux
