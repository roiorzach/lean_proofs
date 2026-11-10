import ConformityConcerns.LearnTheta.PoolTailAux.ODE
import ConformityConcerns.LearnTheta.PoolTailAux.Conv

/-!
# The tails of the central pool vanish: abstract core

`upper_core` is the last paragraph of the proof of Proposition A5 with the convergence inputs
(uniform convergence of `m_t` to `(x - c)²` on compacts, vanishing far tails of the type law)
taken as hypotheses. `lower_core` follows by reflecting `x ↦ -x`.
-/

namespace CC.LearnTheta.PoolTailAux

open MeasureTheory Filter Topology Set Real

theorem upper_core {κ : ℝ} (hκ : κck < κ) {c : ℝ} (m : ℕ → ℝ → ℝ)
    (hU : ∀ lo hi ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ x ∈ Icc lo hi, |m t x - (x - c) ^ 2| ≤ ε)
    (hm0 : ∀ t x, 0 ≤ m t x)
    (hconv : ∀ t, ConvexOn ℝ univ (m t))
    (hdiff : ∀ t, Differentiable ℝ (m t))
    (a : ℕ → ℝ → ℝ) (μ : ℕ → ℝ) (vhi : ℕ → EReal)
    (hmin : ∀ t x, m t (μ t) ≤ m t x)
    (hμ : ∀ t, ((μ t : ℝ) : EReal) ≤ vhi t)
    (hode : ∀ t (x : ℝ), vhi t < (x : EReal) →
      0 < κ * deriv (m t) x / (2 * (x - a t x)) ∧
        HasDerivAt (a t) (κ * deriv (m t) x / (2 * (x - a t x))) x)
    (F : ℕ → Measure ℝ)
    (hFtail : ∀ ε : ℝ, 0 < ε → ∃ K₀ : ℝ, ∀ᶠ t in atTop, ∀ u, K₀ ≤ u →
      F t (Ioi (c + u)) < ENNReal.ofReal ε)
    (B : ℝ) (hB : ∀ t, ∫⁻ x, ENNReal.ofReal ((a t x - x) ^ 2) ∂F t ≤ ENNReal.ofReal B)
    (δ : ℝ) (hδ : 0 < δ)
    (hfreq : ∃ᶠ t in atTop, ENNReal.ofReal δ ≤ F t {x : ℝ | vhi t < (x : EReal)}) : False := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  have hκd : 0 < κ - κck := sub_pos.2 hκ
  -- WLOG `B > 0`
  set B' := max B 1 with hB'def
  have hB'0 : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB' : ∀ t, ∫⁻ x, ENNReal.ofReal ((a t x - x) ^ 2) ∂F t ≤ ENNReal.ofReal B' :=
    fun t => (hB t).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the minimisers converge to `c`
  have hμc : ∀ s : ℝ, 0 < s → ∀ᶠ t in atTop, |μ t - c| ≤ s := by
    intro s hs
    filter_upwards [hU (c - s) (c + s) (s ^ 2 / 3) (by positivity)] with t ht
    have hc := ht c ⟨by linarith, by linarith⟩
    have hp := ht (c + s) ⟨by linarith, by linarith⟩
    have hn := ht (c - s) ⟨by linarith, by linarith⟩
    rw [show (c - c) ^ 2 = (0 : ℝ) by ring, sub_zero] at hc
    rw [show (c + s - c) ^ 2 = s ^ 2 by ring] at hp
    rw [show (c - s - c) ^ 2 = s ^ 2 by ring] at hn
    have hc' := (abs_le.1 hc).2
    have hp' := (abs_le.1 hp).1
    have hn' := (abs_le.1 hn).1
    have hs2 : 0 < s ^ 2 := pow_pos hs 2
    rw [abs_le]
    constructor
    · by_contra h
      push Not at h
      have hm := (hconv t).le_max_of_mem_Icc (mem_univ (μ t)) (mem_univ c) (z := c - s)
        ⟨by linarith, by linarith⟩
      rw [max_eq_right (hmin t c)] at hm
      linarith
    · by_contra h
      push Not at h
      have hm := (hconv t).le_max_of_mem_Icc (mem_univ c) (mem_univ (μ t)) (z := c + s)
        ⟨by linarith, by linarith⟩
      rw [max_eq_left (hmin t c)] at hm
      linarith
  -- constants
  set ρ : ℝ := (κ + κck) / (2 * κ) with hρ
  set ε₁ : ℝ := (1 - ρ) / 4 with hε₁
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one (by positivity)]; linarith
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; linarith
  have hκρ : κ * (1 - 4 * ε₁) = (κ + κck) / 2 := by
    rw [hε₁, hρ]; field_simp; ring
  set e := min ε₁ 1 with he
  have he0 : 0 < e := lt_min hε₁0 one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε₁ := min_le_left _ _
  obtain ⟨K₀, hK₀⟩ := hFtail (δ / 2) (by positivity)
  set K : ℝ := max (K₀ + 1) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKK₀ : K₀ + 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  set C' : ℝ := 4 * B' / δ with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set M : ℝ := κ * ((K + 1) ^ 2 + 1) with hM
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = K * exp (((√(C' + M) + K) / K) ^ 2 / (κ - κck)) := ⟨_, rfl⟩
  have hKZ : K ≤ Z := by
    rw [hZ]; exact le_mul_of_one_le_right hK0.le (one_le_exp (by positivity))
  -- pick a date `t` where everything holds
  have hev := (hμc e he0).and ((hU (c - 1) (c + Z + K + 1) e he0).and hK₀)
  obtain ⟨t, hδt, hμt, hUt, hFt⟩ := (hfreq.and_eventually hev).exists
  have hμt' := abs_le.1 hμt
  have hmμ : m t (μ t) ≤ e := by
    have := hUt c ⟨by linarith, by linarith⟩
    rw [show (c - c) ^ 2 = (0 : ℝ) by ring, sub_zero] at this
    linarith [(abs_le.1 this).2, hmin t c]
  -- the quadratic lower bound on `[μ + K, μ + Z]`
  have hlow : ∀ x ∈ Icc (μ t + K) (μ t + Z),
      (κ + κck) * (x - μ t) ^ 2 / 2 ≤ κ * (m t x - m t (μ t)) := by
    intro x hx
    have hxU := hUt x ⟨by linarith [hx.1, hμt'.1], by linarith [hx.2, hμt'.2]⟩
    have h1 := (abs_le.1 hxU).1
    have hxc : x - c = (x - μ t) + (μ t - c) := by ring
    rw [hxc] at h1
    set z := x - μ t with hz
    set d := μ t - c with hd
    have hz1 : 1 ≤ z := by linarith [hx.1]
    have hd' : -ε₁ ≤ d := by linarith [hμt'.1]
    have hzd : z * -ε₁ ≤ z * d := mul_le_mul_of_nonneg_left hd' (by linarith)
    have hzz : z ≤ z ^ 2 := by rw [sq]; exact le_mul_of_one_le_right (by linarith) hz1
    have hz2 : 1 ≤ z ^ 2 := le_trans hz1 hzz
    have hsq : z ^ 2 - 2 * (z * ε₁) ≤ (z + d) ^ 2 := by
      have h0 := sq_nonneg d
      have e0 : (z + d) ^ 2 = z ^ 2 + 2 * (z * d) + d ^ 2 := by ring
      have e1 : z * -ε₁ = -(z * ε₁) := by ring
      linarith
    have hA1 : ε₁ * z ≤ ε₁ * z ^ 2 := mul_le_mul_of_nonneg_left hzz hε₁0.le
    have hA2 : ε₁ * 1 ≤ ε₁ * z ^ 2 := mul_le_mul_of_nonneg_left hz2 hε₁0.le
    have key : z ^ 2 * (1 - 4 * ε₁) ≤ m t x - m t (μ t) := by
      have e2 : z ^ 2 * (1 - 4 * ε₁) = z ^ 2 - 4 * (ε₁ * z ^ 2) := by ring
      have e3 : z * ε₁ = ε₁ * z := by ring
      linarith
    calc (κ + κck) * z ^ 2 / 2 = κ * (1 - 4 * ε₁) * z ^ 2 := by rw [hκρ]; ring
      _ = κ * (z ^ 2 * (1 - 4 * ε₁)) := by ring
      _ ≤ κ * (m t x - m t (μ t)) := mul_le_mul_of_nonneg_left key hκ0.le
  -- the far upper tail has mass `< δ / 2`
  have hFt' : F t (Ioi (μ t + K)) < ENNReal.ofReal (δ / 2) := by
    have := hFt (μ t - c + K) (by linarith [hμt'.1])
    rwa [show c + (μ t - c + K) = μ t + K by ring] at this
  set S : Set ℝ := {x : ℝ | vhi t < (x : EReal)} ∩ Iic (μ t + K) with hS
  have hSmeas : MeasurableSet S :=
    ((isOpen_Ioi.preimage continuous_coe_real_ereal).measurableSet).inter measurableSet_Iic
  have hFS : ENNReal.ofReal (δ / 2) < F t S := by
    by_contra h
    push Not at h
    have h1 : F t {x : ℝ | vhi t < (x : EReal)} ≤ F t S + F t (Ioi (μ t + K)) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro x hx
      by_cases hxK : x ≤ μ t + K
      · exact Or.inl ⟨hx, hxK⟩
      · exact Or.inr (not_le.1 hxK)
    have h2 : F t S + F t (Ioi (μ t + K)) < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
      ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h) h hFt'
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves] at h2
    exact absurd (hδt.trans h1) (not_le.2 h2)
  -- a point of the near tail with a moderate adaptation loss
  obtain ⟨x₁, hx₁S, hx₁w⟩ : ∃ x ∈ S, (a t x - x) ^ 2 ≤ C' := by
    by_contra h
    push Not at h
    have h1 : S.indicator (fun _ => ENNReal.ofReal C') ≤
        fun x => ENNReal.ofReal ((a t x - x) ^ 2) := by
      intro x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]; exact ENNReal.ofReal_le_ofReal (h x hx).le
      · rw [indicator_of_notMem hx]; exact zero_le
    have h2 := (lintegral_mono h1).trans (hB' t)
    rw [lintegral_indicator_const hSmeas] at h2
    have h3 : ENNReal.ofReal C' * ENNReal.ofReal (δ / 2) ≤ ENNReal.ofReal C' * F t S := by
      gcongr
    rw [← ENNReal.ofReal_mul hC'0, show C' * (δ / 2) = 2 * B' by rw [hC']; field_simp; ring]
      at h3
    have h4 : ENNReal.ofReal B' < ENNReal.ofReal (2 * B') :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    exact absurd (h3.trans h2) (not_le.2 h4)
  have hμx₁ : μ t < x₁ := by
    have := lt_of_le_of_lt (hμ t) hx₁S.1; exact_mod_cast this
  have hx₁K : x₁ ≤ μ t + K := hx₁S.2
  have hL₁ : κ * (m t x₁ - m t (μ t)) ≤ M := by
    have hxU := hUt x₁ ⟨by linarith [hμt'.1], by linarith [hμt'.2]⟩
    have h1 := (abs_le.1 hxU).2
    have h2 : (x₁ - c) ^ 2 ≤ (K + 1) ^ 2 :=
      sq_le_sq' (by linarith [hμt'.1]) (by linarith [hμt'.2])
    have h3 := hm0 t (μ t)
    rw [hM]
    apply mul_le_mul_of_nonneg_left _ hκ0.le
    linarith
  rw [hZ] at hlow
  exact tail_ode_false hκ (hμ t) (hdiff t) (hmin t) (hode t) hK0 hx₁S.1 hx₁K hx₁w hL₁ hlow

theorem lower_core {κ : ℝ} (hκ : κck < κ) {c : ℝ} (m : ℕ → ℝ → ℝ)
    (hU : ∀ lo hi ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ x ∈ Icc lo hi, |m t x - (x - c) ^ 2| ≤ ε)
    (hm0 : ∀ t x, 0 ≤ m t x)
    (hconv : ∀ t, ConvexOn ℝ univ (m t))
    (hdiff : ∀ t, Differentiable ℝ (m t))
    (a : ℕ → ℝ → ℝ) (μ : ℕ → ℝ) (vlo : ℕ → EReal)
    (hmin : ∀ t x, m t (μ t) ≤ m t x)
    (hμ : ∀ t, vlo t ≤ ((μ t : ℝ) : EReal))
    (hode : ∀ t (x : ℝ), (x : EReal) < vlo t →
      0 < κ * deriv (m t) x / (2 * (x - a t x)) ∧
        HasDerivAt (a t) (κ * deriv (m t) x / (2 * (x - a t x))) x)
    (F : ℕ → Measure ℝ)
    (hFtail : ∀ ε : ℝ, 0 < ε → ∃ K₀ : ℝ, ∀ᶠ t in atTop, ∀ u, K₀ ≤ u →
      F t (Iio (c - u)) < ENNReal.ofReal ε)
    (B : ℝ) (hB : ∀ t, ∫⁻ x, ENNReal.ofReal ((a t x - x) ^ 2) ∂F t ≤ ENNReal.ofReal B)
    (δ : ℝ) (hδ : 0 < δ)
    (hfreq : ∃ᶠ t in atTop, ENNReal.ofReal δ ≤ F t {x : ℝ | (x : EReal) < vlo t}) : False := by
  have hU' : ∀ lo hi ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ x ∈ Icc lo hi,
      |m t (-x) - (x - -c) ^ 2| ≤ ε := by
    intro lo hi ε hε
    filter_upwards [hU (-hi) (-lo) ε hε] with t ht x hx
    have := ht (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rwa [show (x - -c) ^ 2 = (-x - c) ^ 2 by ring]
  have hconv' : ∀ t, ConvexOn ℝ univ (fun x => m t (-x)) := by
    intro t
    refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
    have := (hconv t).2 (mem_univ (-x)) (mem_univ (-y)) hp hq hpq
    simp only [smul_eq_mul] at this ⊢
    rw [show -(p * x + q * y) = p * -x + q * -y by ring]
    exact this
  have hdiff' : ∀ t, Differentiable ℝ (fun x => m t (-x)) :=
    fun t => (hdiff t).comp differentiable_neg
  have hmin' : ∀ t x, m t (-(-μ t)) ≤ m t (-x) := fun t x => by
    rw [neg_neg]; exact hmin t (-x)
  have hμ' : ∀ t, ((-μ t : ℝ) : EReal) ≤ -vlo t := fun t => by
    rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact hμ t
  have hode' : ∀ t (x : ℝ), -vlo t < (x : EReal) →
      0 < κ * deriv (fun x => m t (-x)) x / (2 * (x - -a t (-x))) ∧
        HasDerivAt (fun x => -a t (-x))
          (κ * deriv (fun x => m t (-x)) x / (2 * (x - -a t (-x)))) x := by
    intro t x hx
    have hx' : ((-x : ℝ) : EReal) < vlo t := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_comm.1 hx
    obtain ⟨hpos, ha⟩ := hode t (-x) hx'
    have hexpr : κ * deriv (fun x => m t (-x)) x / (2 * (x - -a t (-x))) =
        κ * deriv (m t) (-x) / (2 * (-x - a t (-x))) := by
      rw [deriv_comp_neg, show 2 * (x - -a t (-x)) = -(2 * (-x - a t (-x))) by ring, mul_neg,
        neg_div_neg_eq]
    refine ⟨by rw [hexpr]; exact hpos, ?_⟩
    have h2 : HasDerivAt (fun y => a t (-y))
        (κ * deriv (m t) (-x) / (2 * (-x - a t (-x))) * -1) x :=
      ha.comp x (hasDerivAt_neg x)
    convert h2.neg using 1
    rw [hexpr]; ring
  set F' : ℕ → Measure ℝ := fun t => (F t).map (MeasurableEquiv.neg ℝ) with hF'
  have hFtail' : ∀ ε : ℝ, 0 < ε → ∃ K₀ : ℝ, ∀ᶠ t in atTop, ∀ u, K₀ ≤ u →
      F' t (Ioi (-c + u)) < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨K₀, hK₀⟩ := hFtail ε hε
    refine ⟨K₀, ?_⟩
    filter_upwards [hK₀] with t ht u hu
    have hset : (MeasurableEquiv.neg ℝ) ⁻¹' Ioi (-c + u) = Iio (c - u) := by
      ext y; simp only [mem_preimage, MeasurableEquiv.neg_apply, mem_Ioi, mem_Iio]
      constructor <;> intro h <;> linarith
    simp only [hF']
    rw [MeasurableEquiv.map_apply, hset]
    exact ht u hu
  have hB' : ∀ t, ∫⁻ x, ENNReal.ofReal (((fun x => -a t (-x)) x - x) ^ 2) ∂F' t ≤
      ENNReal.ofReal B := by
    intro t
    simp only [hF']
    rw [MeasureTheory.lintegral_map_equiv]
    refine le_trans (le_of_eq ?_) (hB t)
    congr 1
    funext y
    simp only [MeasurableEquiv.neg_apply, neg_neg]
    congr 1
    ring
  have hfreq' : ∃ᶠ t in atTop, ENNReal.ofReal δ ≤ F' t {x : ℝ | -vlo t < (x : EReal)} := by
    refine hfreq.mono fun t ht => ?_
    have hset : (MeasurableEquiv.neg ℝ) ⁻¹' {x : ℝ | -vlo t < (x : EReal)} =
        {x : ℝ | (x : EReal) < vlo t} := by
      ext y
      simp only [mem_preimage, MeasurableEquiv.neg_apply, mem_ofPred_eq, EReal.coe_neg,
        EReal.neg_lt_neg_iff]
    simp only [hF']
    rw [MeasurableEquiv.map_apply, hset]
    exact ht
  exact upper_core hκ (c := -c) (fun t x => m t (-x)) hU' (fun t x => hm0 t (-x)) hconv' hdiff'
    (fun t x => -a t (-x)) (fun t => -μ t) (fun t => -vlo t) hmin' hμ' hode' F' hFtail' B hB'
    δ hδ hfreq'

end CC.LearnTheta.PoolTailAux
