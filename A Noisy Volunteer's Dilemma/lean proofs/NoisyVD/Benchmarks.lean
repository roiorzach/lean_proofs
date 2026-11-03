import NoisyVD.Volunteer

/-!
# The motivating benchmarks: Propositions `prop_no_clueless` and `prop_noise_threshold`
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

namespace VD

variable {E : Env Bool Bool}

lemma bpmf_zero (m : ℕ) (p : ℝ) : bpmf m p 0 = (1 - p) ^ m := by
  simp [bpmf]

lemma rho_one (m : ℕ) (p : ℝ) : rho m p 1 = (1 - p) ^ m := by
  simp [rho, bpmf_zero]

/-- `Pr(Bin(n,p) ≥ 1) = 1 - (1-p)^n`. -/
lemma btail_one (n : ℕ) (p : ℝ) : btail n p 1 = 1 - (1 - p) ^ n := by
  unfold btail
  have h := bpmf_sum n p
  rw [Finset.sum_range_succ'] at h
  rw [Finset.sum_range_succ']
  simp only [Nat.le_add_left, ite_true, not_le.2 Nat.zero_lt_one, ite_false, add_zero] at *
  rw [bpmf_zero] at h
  linarith

/-- The rule of the no-noise benchmark: investigate iff at least one report is made. -/
noncomputable abbrev oneReport : Rule Bool := thresholdRule 1 true false

lemma gross_oneReport {n : ℕ} (p : ℝ) (ω : Bool) :
    E.gross n oneReport p ω = (1 - p) ^ (n - 1) * G E ω := by
  rw [gross_threshold, rho_one]
  rfl

/-- The assumptions on the cost distribution in the benchmark (implied by a positive continuous
density on `[a, b]`, see `CostDensity`). -/
structure BenchmarkCost (E : Env Bool Bool) (a b : ℝ) : Prop where
  a_nonneg : 0 ≤ a
  a_lt : a < b
  cont : Continuous E.F
  F_a : E.F a = 0
  F_b : E.F b = 1
  strict : StrictMonoOn E.F (Icc a b)

namespace BenchmarkCost

variable {a b : ℝ}

lemma F_eq_zero (h : BenchmarkCost E a b) {x : ℝ} (hx : x ≤ a) : E.F x = 0 :=
  le_antisymm ((Env.F_mono E hx).trans_eq h.F_a) (Env.F_nonneg E x)

lemma F_eq_one (h : BenchmarkCost E a b) {x : ℝ} (hx : b ≤ x) : E.F x = 1 :=
  le_antisymm (Env.F_le_one E x) (h.F_b ▸ Env.F_mono E hx)

/-- Equation `eq_indifference` has a unique solution, which lies in `(a, b)`. -/
lemma exists_unique_cutoff (h : BenchmarkCost E a b) {Hv : ℝ} (hH : a < Hv) {n : ℕ} (hn : 2 ≤ n) :
    ∃ c ∈ Ioo a b, c = Hv * (1 - E.F c) ^ (n - 1) ∧
      ∀ c', c' = Hv * (1 - E.F c') ^ (n - 1) → c' = c := by
  have hm : n - 1 ≠ 0 := by omega
  have hHpos : 0 < Hv := lt_of_le_of_lt h.a_nonneg hH
  let g : ℝ → ℝ := fun c => c - Hv * (1 - E.F c) ^ (n - 1)
  have hg : Continuous g := by
    have := h.cont
    exact continuous_id.sub (continuous_const.mul ((continuous_const.sub this).pow _))
  have hga : g a < 0 := by
    simp only [g, h.F_a, sub_zero, one_pow, mul_one]
    linarith
  have hgb : 0 < g b := by
    simp only [g, h.F_b, sub_self, zero_pow hm, mul_zero, sub_zero]
    linarith [h.a_nonneg, h.a_lt]
  obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc h.a_lt.le hg.continuousOn
    (show (0 : ℝ) ∈ Icc (g a) (g b) from ⟨hga.le, hgb.le⟩)
  have hca : a < c := by
    refine lt_of_le_of_ne hc.1 ?_
    rintro rfl
    linarith
  have hcb : c < b := by
    refine lt_of_le_of_ne hc.2 ?_
    rintro rfl
    linarith
  have hceq : c = Hv * (1 - E.F c) ^ (n - 1) := by
    have : c - Hv * (1 - E.F c) ^ (n - 1) = 0 := hgc
    linarith
  refine ⟨c, ⟨hca, hcb⟩, hceq, fun c' hc' => ?_⟩
  -- any solution is in `(a, b)`
  have hc'a : a < c' := by
    by_contra hcon
    push Not at hcon
    rw [h.F_eq_zero hcon, sub_zero, one_pow, mul_one] at hc'
    linarith
  have hc'b : c' < b := by
    by_contra hcon
    push Not at hcon
    rw [h.F_eq_one hcon, sub_self, zero_pow hm, mul_zero] at hc'
    linarith [h.a_nonneg, h.a_lt]
  -- `g` is strictly increasing on `[a, b]`
  have hmono : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → x < y →
      Hv * (1 - E.F y) ^ (n - 1) ≤ Hv * (1 - E.F x) ^ (n - 1) := by
    intro x y hx hy hxy
    apply mul_le_mul_of_nonneg_left _ hHpos.le
    apply pow_le_pow_left₀
    · linarith [Env.F_le_one E y]
    · linarith [Env.F_mono E hxy.le]
  rcases lt_trichotomy c' c with hlt | heq | hgt
  · have := hmono c' c ⟨hc'a.le, hc'b.le⟩ ⟨hca.le, hcb.le⟩ hlt
    linarith
  · exact heq
  · have := hmono c c' ⟨hca.le, hcb.le⟩ ⟨hc'a.le, hc'b.le⟩ hgt
    linarith

/-- `ν*(n)` is decreasing in `n`, because the right-hand side of `eq_indifference` decreases with `n`. -/
lemma cutoff_succ_le (_h : BenchmarkCost E a b) {Hv : ℝ} (hH : 0 < Hv) {n : ℕ} (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (hc₁ : c₁ = Hv * (1 - E.F c₁) ^ (n - 1)) (hc₂ : c₂ = Hv * (1 - E.F c₂) ^ (n + 1 - 1)) : c₂ ≤ c₁ := by
  by_contra hcon
  push Not at hcon
  have h1 : 0 ≤ 1 - E.F c₂ := by linarith [Env.F_le_one E c₂]
  have h2 : 1 - E.F c₂ ≤ 1 := by linarith [Env.F_nonneg E c₂]
  have h3 : (1 - E.F c₂) ^ (n + 1 - 1) ≤ (1 - E.F c₂) ^ (n - 1) :=
    pow_le_pow_of_le_one h1 h2 (by omega)
  have h4 : (1 - E.F c₂) ^ (n - 1) ≤ (1 - E.F c₁) ^ (n - 1) :=
    pow_le_pow_left₀ h1 (by linarith [Env.F_mono E hcon.le]) _
  have h5 : c₂ ≤ c₁ := by
    rw [hc₂, hc₁]
    exact mul_le_mul_of_nonneg_left (h3.trans h4) hH.le
  linarith

/-- `ν*(n) → ν̲`.  The sequence is decreasing and bounded below, so its limit exists; were the limit above
`ν̲`, the right-hand side of `eq_indifference` would converge to zero. -/
lemma tendsto_cutoff (h : BenchmarkCost E a b) {Hv : ℝ} (hH : 0 < Hv) {c : ℕ → ℝ}
    (hc : ∀ n, 2 ≤ n → c n ∈ Ioo a b ∧ c n = Hv * (1 - E.F (c n)) ^ (n - 1)) :
    Tendsto c atTop (𝓝 a) := by
  let c' : ℕ → ℝ := fun j => c (j + 2)
  have hanti : Antitone c' := antitone_nat_of_succ_le fun j => by
    have h1 := (hc (j + 2) (by omega)).2
    have h2 := (hc (j + 2 + 1) (by omega)).2
    exact cutoff_succ_le h hH (n := j + 2) (by omega) h1 h2
  have hbdd : BddBelow (range c') := ⟨a, by
    rintro _ ⟨j, rfl⟩
    exact (hc (j + 2) (by omega)).1.1.le⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ j, c' j with hL
  have haL : a ≤ L := le_ciInf fun j => (hc (j + 2) (by omega)).1.1.le
  have hLc : ∀ j, L ≤ c' j := fun j => ciInf_le hbdd j
  have hLb : L < b := lt_of_le_of_lt (hLc 0) (hc 2 le_rfl).1.2
  have hLa : L = a := by
    by_contra hne
    have hlt : a < L := lt_of_le_of_ne haL (Ne.symm hne)
    have hFL : 0 < E.F L := by
      have := h.strict ⟨le_rfl, h.a_lt.le⟩ ⟨haL, hLb.le⟩ hlt
      rwa [h.F_a] at this
    have h1F : 1 - E.F L < 1 := by linarith
    have h0F : 0 ≤ 1 - E.F L := by linarith [Env.F_le_one E L]
    have hpow : Tendsto (fun j : ℕ => Hv * (1 - E.F L) ^ (j + 1)) atTop (𝓝 (Hv * 0)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one h0F h1F).comp (tendsto_add_atTop_nat 1)).const_mul _
    rw [mul_zero] at hpow
    have hle : ∀ j, c' j ≤ Hv * (1 - E.F L) ^ (j + 1) := fun j => by
      have h2 := (hc (j + 2) (by omega)).2
      have h3 : (1 - E.F (c' j)) ^ (j + 1) ≤ (1 - E.F L) ^ (j + 1) :=
        pow_le_pow_left₀ (by linarith [Env.F_le_one E (c' j)])
          (by linarith [Env.F_mono E (hLc j)]) _
      calc c' j = Hv * (1 - E.F (c' j)) ^ (j + 2 - 1) := h2
        _ ≤ Hv * (1 - E.F L) ^ (j + 1) := mul_le_mul_of_nonneg_left h3 hH.le
    have hzero : L ≤ 0 := le_of_tendsto_of_tendsto' hlim hpow hle
    linarith [h.a_nonneg]
  rw [hLa] at hlim
  exact (tendsto_add_atTop_iff_nat 2).1 hlim

end BenchmarkCost

/-- **Proposition 1 (`prop_no_clueless`).**  Fix `F` as in the benchmark and the rule "investigate iff
at least one report".  For every `n ≥ 2` there is a unique cutoff `ν*(n) ∈ (ν̲, ν̄)`; a symmetric
equilibrium exists; in every symmetric equilibrium types above zero stay silent when `ω = 0` (so
there is never an investigation there), and types use the cutoff `ν*(n)` when `ω = 1`, whence the
probability of no investigation in state `1` is `(1 - F(ν*(n)))^n`.  This probability converges to
`ν̲/H < 1`.  We allow `ν̲ ≥ 0`, as the paper notes that the same proof covers `ν̲ = 0`. -/
theorem prop_no_clueless {a b : ℝ} (hC : BenchmarkCost E a b) (hH : a < H E) (hL : L E < 0) :
    (∀ n : ℕ, 2 ≤ n → ∃ c ∈ Ioo a b, c = H E * (1 - E.F c) ^ (n - 1) ∧
      (∀ c', c' = H E * (1 - E.F c') ^ (n - 1) → c' = c) ∧
      (∃ s : Strat Bool, E.IsEq n oneReport s) ∧
      ∀ s : Strat Bool, E.IsEq n oneReport s →
        (∀ x > 0, s.σ false x = 0) ∧ E.rp s false = 0 ∧ btail n (E.rp s false) 1 = 0 ∧
        (∀ x < c, s.σ true x = 1) ∧ (∀ x > c, s.σ true x = 0) ∧ E.rp s true = E.F c ∧
        1 - btail n (E.rp s true) 1 = (1 - E.F c) ^ n) ∧
    (∀ c : ℕ → ℝ, (∀ n, 2 ≤ n → c n ∈ Ioo a b ∧ c n = H E * (1 - E.F (c n)) ^ (n - 1)) →
      Tendsto (fun n => (1 - E.F (c n)) ^ n) atTop (𝓝 (a / H E))) ∧
    a / H E < 1 := by
  have hHpos : 0 < H E := lt_of_le_of_lt hC.a_nonneg hH
  refine ⟨fun n hn => ?_, fun c hc => ?_, by rw [div_lt_one hHpos]; exact hH⟩
  · obtain ⟨c, hcI, hceq, huniq⟩ := hC.exists_unique_cutoff hH hn
    refine ⟨c, hcI, hceq, huniq, E.exists_equilibrium n oneReport, fun s he => ?_⟩
    have hp0 := Env.rp_nonneg E s false
    have hp1 := Env.rp_le_one E s false
    have hq0 := Env.rp_nonneg E s true
    have hq1 := Env.rp_le_one E s true
    -- state `0`
    have hg0 : E.gross n oneReport (E.rp s false) false ≤ 0 := by
      rw [gross_oneReport]
      exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (by linarith) _) hL.le
    have hσ0 : ∀ x > 0, s.σ false x = 0 := fun x hx => (he false x).2 (lt_of_le_of_lt hg0 hx)
    have hrp0 : E.rp s false = 0 := by
      have h1 := (Env.band E he false).2
      have h2 : E.F (E.gross n oneReport (E.rp s false) false) = 0 :=
        hC.F_eq_zero (hg0.trans hC.a_nonneg)
      rw [h2] at h1
      exact le_antisymm h1 hp0
    -- state `1`
    have hrp1 := rp_eq_F he (ω := true) hC.cont.continuousAt
    have hgc : E.gross n oneReport (E.rp s true) true = c := by
      apply huniq
      conv_lhs => rw [gross_oneReport]
      have e : E.F (E.gross n oneReport (E.rp s true) true) = E.rp s true := hrp1.symm
      rw [e]
      have : G E true = H E := rfl
      rw [this]
      ring
    rw [hgc] at hrp1
    refine ⟨hσ0, hrp0, ?_, fun x hx => ?_, fun x hx => ?_, hrp1, ?_⟩
    · rw [hrp0, btail_one]
      simp
    · refine (he true x).1 ?_
      rwa [hgc]
    · refine (he true x).2 ?_
      rwa [hgc]
    · rw [hrp1, btail_one]
      ring
  · -- convergence: `ν*(n) → ν̲`, and `(1 - F(ν*(n)))^n = (ν*(n)/H)^{n/(n-1)}`
    have hct : Tendsto c atTop (𝓝 a) := hC.tendsto_cutoff hHpos hc
    have hbase : Tendsto (fun n => c n / H E) atTop (𝓝 (a / H E)) := hct.div_const _
    have hexp : Tendsto (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun n : ℕ => 1 + 1 / ((n - 1 : ℕ) : ℝ)) atTop (𝓝 (1 + 0)) :=
        (tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_sub_atTop_nat 1)).const_add 1
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hc' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hne : (n : ℝ) - 1 ≠ 0 := by linarith
      rw [hc']
      field_simp
      ring
    have hrpow := hbase.rpow hexp (Or.inr one_pos)
    rw [Real.rpow_one] at hrpow
    refine hrpow.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h3 := (hc n hn).2
    have h0 : 0 ≤ 1 - E.F (c n) := by linarith [Env.F_le_one E (c n)]
    have hm : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
      exact this.ne'
    have e : c n / H E = (1 - E.F (c n)) ^ (n - 1) := by
      conv_lhs => rw [h3]
      field_simp
    rw [e, ← Real.rpow_natCast, ← Real.rpow_mul h0, mul_div_cancel₀ _ hm, Real.rpow_natCast]

/-- The density hypothesis of Section 2: `F` has a strictly positive continuous density on `[a, b]`. -/
structure CostDensity (E : Env Bool Bool) (a b : ℝ) (f : ℝ → ℝ) : Prop where
  a_nonneg : 0 ≤ a
  a_lt : a < b
  f_cont : ContinuousOn f (Icc a b)
  f_pos : ∀ x ∈ Icc a b, 0 < f x
  F_eq : ∀ x ∈ Icc a b, E.F x = ∫ y in a..x, f y
  F_b : E.F b = 1

/-- A positive continuous density yields the hypotheses used in Proposition 1. -/
theorem CostDensity.toBenchmark {a b : ℝ} {f : ℝ → ℝ} (h : CostDensity E a b f) :
    BenchmarkCost E a b := by
  have hab := h.a_lt
  have hFa : E.F a = 0 := by
    rw [h.F_eq a ⟨le_rfl, hab.le⟩]; simp
  have hint : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → IntervalIntegrable f volume x y := fun x y hx hy =>
    (h.f_cont.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have hstrict : StrictMonoOn E.F (Icc a b) := by
    intro x hx y hy hxy
    rw [h.F_eq x hx, h.F_eq y hy, ← intervalIntegral.integral_add_adjacent_intervals
      (hint a x ⟨le_rfl, hab.le⟩ hx) (hint x y hx hy)]
    have hpos : 0 < ∫ t in x..y, f t := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on (hint x y hx hy) _ hxy
      intro t ht
      exact h.f_pos t ⟨hx.1.trans ht.1.le, ht.2.le.trans hy.2⟩
    linarith
  refine ⟨h.a_nonneg, hab, ?_, hFa, h.F_b, hstrict⟩
  -- continuity: `F = G ∘ clamp`
  let cl : ℝ → ℝ := fun x => max a (min x b)
  have hcl : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclI : ∀ x, cl x ∈ Icc a b := fun x =>
    ⟨le_max_left _ _, max_le hab.le (min_le_right _ _)⟩
  have hGc : ContinuousOn (fun x => ∫ y in a..x, f y) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := a) (b := b) (f := f)
      (μ := volume) (by rw [uIcc_of_le hab.le]; exact h.f_cont.integrableOn_Icc)
    rwa [uIcc_of_le hab.le] at this
  have hFeq : E.F = fun x => ∫ y in a..cl x, f y := by
    funext x
    rw [← h.F_eq _ (hclI x)]
    rcases le_total x a with hx | hx
    · have h1 : cl x = a := by
        simp only [cl]
        rw [min_eq_left (hx.trans hab.le), max_eq_left hx]
      rw [h1, hFa]
      exact le_antisymm ((Env.F_mono E hx).trans_eq hFa) (Env.F_nonneg E x)
    · rcases le_total x b with hx2 | hx2
      · have h1 : cl x = x := by
          simp only [cl]
          rw [min_eq_left hx2, max_eq_right hx]
        rw [h1]
      · have h1 : cl x = b := by
          simp only [cl]
          rw [min_eq_right hx2, max_eq_right hab.le]
        rw [h1, h.F_b]
        exact le_antisymm (Env.F_le_one E x) (h.F_b ▸ Env.F_mono E hx2)
  rw [hFeq]
  exact hGc.comp_continuous hcl hclI

/-- **The benchmark payoff.**  Along the equilibria of Proposition 1 the decision-maker's payoff
converges to `Π^FB - π ν̲`.  In particular it is continuous in `ν̲ = inf supp ν_i` and tends to the
first-best as `ν̲ ↓ 0`, and equals it in the limit when `ν̲ = 0` (Sections 2 and 6 of the paper). -/
theorem benchmark_limit_payoff (hV : Assumptions E) {a b : ℝ} (hC : BenchmarkCost E a b)
    (hH : a < H E) {c : ℕ → ℝ}
    (hc : ∀ n, 2 ≤ n → c n ∈ Ioo a b ∧ c n = H E * (1 - E.F (c n)) ^ (n - 1)) {s : ℕ → Strat Bool}
    (hs : ∀ n, 2 ≤ n → E.IsEq n oneReport (s n)) :
    Tendsto (fun n => E.payoff n oneReport (s n)) atTop (𝓝 (E.PiFB - pr E * a)) := by
  obtain ⟨hprop, hlim, _⟩ := prop_no_clueless hC hH hV.L_neg
  have hHpos : 0 < H E := hV.H_pos
  have hl := hlim c hc
  have hgoal : Tendsto (fun n => E.PiSQ + pr E * H E * (1 - (1 - E.F (c n)) ^ n)) atTop
      (𝓝 (E.PiSQ + pr E * H E * (1 - a / H E))) :=
    ((hl.const_sub 1).const_mul _).const_add _
  have hval : E.PiSQ + pr E * H E * (1 - a / H E) = E.PiFB - pr E * a := by
    have h1 := PiFB_sub_PiSQ hV
    have h2 : pr E * H E * (1 - a / H E) = pr E * H E - pr E * a := by
      field_simp
    rw [h2]
    linarith
  rw [hval] at hgoal
  refine hgoal.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  obtain ⟨c', hc'I, hc'eq, huniq, _, hall⟩ := hprop n hn
  have hcc : c n = c' := huniq _ (hc n hn).2
  obtain ⟨_, _, h0, _, _, _, h1⟩ := hall (s n) (hs n hn)
  have hrule : (oneReport : Rule Bool) = dirRule true 1 := rfl
  rw [hrule, payoff_dir hV true n 1 (s n)]
  simp only [Idir, ite_true]
  rw [h0]
  have h2 : btail n (E.rp (s n) true) 1 = 1 - (1 - E.F c') ^ n := by linarith
  rw [h2, hcc]
  ring

/-! ### Proposition 2 -/

/-- The reporting probability when each individual is mechanical with probability `ε`, a mechanical
individual reporting with probability `1/2`. -/
noncomputable def mechRp (E : Env Bool Bool) (ε : ℝ) (s : Strat Bool) (ω : Bool) : ℝ :=
  ε / 2 + (1 - ε) * E.rp s ω

/-- Symmetric equilibrium in the model with mechanical individuals: rational types best respond. -/
def IsEqMech (E : Env Bool Bool) (ε : ℝ) (n : ℕ) (d : Rule Bool) (s : Strat Bool) : Prop :=
  ∀ ω x, (x < E.gross n d (mechRp E ε s ω) ω → s.σ ω x = 1) ∧
    (E.gross n d (mechRp E ε s ω) ω < x → s.σ ω x = 0)

/-- The decision-maker's payoff in the model with mechanical individuals. -/
noncomputable def payoffMech (E : Env Bool Bool) (ε : ℝ) (n : ℕ) (d : Rule Bool) (s : Strat Bool) : ℝ :=
  ∫ ω, bexp n (mechRp E ε s ω) (fun k => E.v d k ω) ∂(E.prior : Measure Bool)

lemma mechRp_mem {ε : ℝ} (_h0 : 0 < ε) (h1 : ε ≤ 1) (s : Strat Bool) (ω : Bool) :
    mechRp E ε s ω ∈ Icc (ε / 2) (1 - ε / 2) := by
  have hp0 := Env.rp_nonneg E s ω
  have hp1 := Env.rp_le_one E s ω
  unfold mechRp
  have h2 : 0 ≤ 1 - ε := by linarith
  constructor
  · nlinarith
  · nlinarith

/-- A state-independent report distribution yields at most `Π^SQ`. -/
lemma integral_bexp_const_le (E : Env Bool Bool) (n : ℕ) (d : Rule Bool) {p : ℝ} (h0 : 0 ≤ p)
    (h1 : p ≤ 1) : ∫ ω, bexp n p (fun k => E.v d k ω) ∂(E.prior : Measure Bool) ≤ E.PiSQ := by
  unfold bexp
  rw [integral_finsetSum _ fun k _ => (E.integrable_v d k).const_mul _]
  have h : ∀ k ∈ Finset.range (n + 1), ∫ ω, bpmf n p k * E.v d k ω ∂(E.prior : Measure Bool)
      ≤ bpmf n p k * E.PiSQ := by
    intro k _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (E.integral_v_le_PiSQ d k) (bpmf_nonneg h0 h1)
  calc _ ≤ ∑ k ∈ Finset.range (n + 1), bpmf n p k * E.PiSQ := Finset.sum_le_sum h
    _ = E.PiSQ := by rw [← Finset.sum_mul, bpmf_sum, one_mul]

/-- **Proposition 2 (`prop_noise_threshold`).**  Fix `ε > 0`.  Rational costs are at least `a > 0`
almost surely.  Then for all large `n` and every threshold, in every symmetric equilibrium no
rational type reports and the decision-maker's payoff is at most `Π^SQ`.  The cutoff `n*` depends only
on `ε`, `a`, `H` and `L`. -/
theorem prop_noise_threshold {a ε : ℝ} (ha : 0 < a) (hFa : E.Fm a = 0) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ nStar : ℕ, ∀ n ≥ nStar, ∀ (T : ℕ) (s : Strat Bool),
      IsEqMech E ε n (thresholdRule T true false) s →
      (∀ ω, ∀ x ≥ a, s.σ ω x = 0) ∧ (∀ ω, E.rp s ω = 0) ∧
        payoffMech E ε n (thresholdRule T true false) s ≤ E.PiSQ := by
  set l := ε / 2 with hl
  have hl0 : 0 < l := by rw [hl]; linarith
  have hl1 : l ≤ 1 / 2 := by rw [hl]; linarith
  set C := massConst l with hC
  have hCpos : 0 < C := massConst_pos hl0 hl1
  set D : ℝ := max |H E| |L E| + 1 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  -- choose `n*` with `D C / √(n-1) < a`
  have hlim : Tendsto (fun n : ℕ => D * C / √((n - 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))) _
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 a ha)
  refine ⟨max N₁ 2, fun n hn T s he => ?_⟩
  have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hm : 1 ≤ n - 1 := by omega
  have hsm : 0 < √((n - 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  -- the gross benefit is below `a`
  have hgross : ∀ ω, E.gross n (thresholdRule T true false) (mechRp E ε s ω) ω < a := by
    intro ω
    have hp := mechRp_mem (E := E) hε0 hε1 s ω
    rw [gross_threshold]
    have hρ := rho_le_mass (T := T) hm hl0 hl1 hp
    have hρ0 : 0 ≤ rho (n - 1) (mechRp E ε s ω) T :=
      rho_nonneg (by linarith [hp.1]) (by linarith [hp.2])
    have hG : E.u true ω - E.u false ω ≤ D := by
      have h1 : E.u true ω - E.u false ω ≤ max |H E| |L E| := by
        cases ω
        · exact (le_abs_self _).trans (le_max_right _ _)
        · exact (le_abs_self _).trans (le_max_left _ _)
      rw [hD]; linarith
    calc rho (n - 1) (mechRp E ε s ω) T * (E.u true ω - E.u false ω)
        ≤ rho (n - 1) (mechRp E ε s ω) T * D := mul_le_mul_of_nonneg_left hG hρ0
      _ ≤ C / √((n - 1 : ℕ) : ℝ) * D := mul_le_mul_of_nonneg_right hρ hDpos.le
      _ = D * C / √((n - 1 : ℕ) : ℝ) := by ring
      _ < a := hN₁ n hn1
  have hσ : ∀ ω, ∀ x ≥ a, s.σ ω x = 0 := fun ω x hx =>
    (he ω x).2 (lt_of_lt_of_le (hgross ω) hx)
  -- no rational type reports
  have hrp : ∀ ω, E.rp s ω = 0 := by
    intro ω
    refine le_antisymm ?_ (Env.rp_nonneg E s ω)
    have h1 : E.Fm a = ∫ x, (Iio a).indicator (fun _ => (1 : ℝ)) x ∂(E.cost : Measure ℝ) := by
      rw [integral_indicator_const _ measurableSet_Iio]
      simp [Env.Fm]
    have h2 : E.rp s ω ≤ E.Fm a := by
      rw [h1]
      refine integral_mono (Env.integrable_sigma E s ω)
        ((integrable_const (1 : ℝ)).indicator measurableSet_Iio) fun x => ?_
      by_cases hx : x < a
      · rw [indicator_of_mem (mem_Iio.2 hx)]
        exact (s.mem ω x).2
      · rw [indicator_of_notMem (by simpa using hx), hσ ω x (not_lt.1 hx)]
    linarith
  refine ⟨hσ, hrp, ?_⟩
  -- only mechanical types report, so the report count is independent of the state
  have hconst : ∀ ω, mechRp E ε s ω = ε / 2 := fun ω => by
    unfold mechRp
    rw [hrp ω]; ring
  unfold payoffMech
  simp_rw [hconst]
  exact integral_bexp_const_le E n _ (by linarith) (by linarith)

end VD

end NoisyVD
