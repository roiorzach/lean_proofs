import NoisyVD.Transfer

/-!
# Biased individuals: the upper bounds continue to hold over monotone rules

The appendix states that, given Proposition `prop_monotone`, the upper bounds of Proposition
`prop_volunteers` continue to hold when `Π(n)` is redefined as the supremum over monotone decision
rules and equilibria in which individuals do not play weakly dominated actions.  This file proves it.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

namespace VD

variable {E : Env Bool Bool}

/-- `x_k = E_{a ∼ d(k)} a`, the probability of investigating following `k` reports. -/
noncomputable def rateX (d : Rule Bool) (k : ℕ) : ℝ := (d k : Measure Bool).real {true}

/-- `v_k(ω)` is determined by the investigation probability. -/
lemma v_eq_rate (d : Rule Bool) (k : ℕ) (ω : Bool) :
    E.v d k ω = rateX d k * E.u true ω + (1 - rateX d k) * E.u false ω := by
  unfold Env.v
  rw [integral_fintype (f := fun a => E.u a ω) Integrable.of_finite, Fintype.sum_bool]
  have h : ((d k : Measure Bool)).real {false} = 1 - rateX d k := by
    have h1 : ({true} : Set Bool) ∪ {false} = univ := by
      ext b; cases b <;> simp
    have hd : Disjoint ({true} : Set Bool) {false} := by simp
    have := measureReal_union (μ := (d k : Measure Bool)) hd (measurableSet_singleton false)
    rw [h1] at this
    simp only [probReal_univ] at this
    unfold rateX
    linarith
  rw [h]
  simp only [smul_eq_mul, rateX]

/-- An equilibrium with biased individuals in which nobody plays a weakly dominated action. -/
structure BiasedEq (E : Env Bool Bool) (pu pd : ℝ) (n : ℕ) (d : Rule Bool) (σu σd : Bool → ℝ)
    (s : Strat Bool) : Prop where
  up : ∀ ω, NoDominated (n - 1) (Uup (rateX d)) (σu ω)
  down : ∀ ω, NoDominated (n - 1) (Udown (rateX d)) (σd ω)
  unbiased : ∀ ω y,
    (y < E.gross n d (biasedRp pu pd (σu ω) (σd ω) (E.rp s ω)) ω → s.σ ω y = 1) ∧
    (E.gross n d (biasedRp pu pd (σu ω) (σd ω) (E.rp s ω)) ω < y → s.σ ω y = 0)

/-- The decision-maker's payoff with biased individuals. -/
noncomputable def biasedPayoff (E : Env Bool Bool) (pu pd : ℝ) (n : ℕ) (d : Rule Bool)
    (σu σd : Bool → ℝ) (s : Strat Bool) : ℝ :=
  ∫ ω, bexp n (biasedRp pu pd (σu ω) (σd ω) (E.rp s ω)) (fun k => E.v d k ω) ∂(E.prior : Measure Bool)

/-- Biased types' behaviour under a monotone nonconstant rule. -/
lemma dominance_values {n : ℕ} {x : ℕ → ℝ} (hmono : MonotoneRule n x) (hnc : NonconstantRule n x)
    {σu σd : ℝ} (hσu : NoDominated (n - 1) (Uup x) σu) (hσd : NoDominated (n - 1) (Udown x) σd) :
    (σu = 1 ∧ σd = 0) ∨ (σu = 0 ∧ σd = 1) := by
  obtain ⟨k₀, hk₀, hne⟩ := hnc
  have hk₀' : k₀ ≤ n - 1 := by omega
  rcases hmono with hinc | hdec
  · left
    refine ⟨hσu.1 ⟨fun k hk => hinc k (by omega), k₀, hk₀', lt_of_le_of_ne (hinc k₀ hk₀) hne.symm⟩,
      hσd.2 ⟨fun k hk => ?_, k₀, hk₀', ?_⟩⟩
    · have := hinc k (by omega)
      show -x (k + 1) ≤ -x (k + 0)
      simpa using this
    · have := lt_of_le_of_ne (hinc k₀ hk₀) hne.symm
      show -x (k₀ + 1) < -x (k₀ + 0)
      simpa using this
  · right
    refine ⟨hσu.2 ⟨fun k hk => hdec k (by omega), k₀, hk₀', lt_of_le_of_ne (hdec k₀ hk₀) hne⟩,
      hσd.1 ⟨fun k hk => ?_, k₀, hk₀', ?_⟩⟩
    · have := hdec k (by omega)
      show -x (k + 0) ≤ -x (k + 1)
      simpa using this
    · have := lt_of_le_of_ne (hdec k₀ hk₀) hne
      show -x (k₀ + 0) < -x (k₀ + 1)
      simpa using this

/-- The band for any strategy that uses the cutoff `c`. -/
lemma rp_band_of_cutoff (E : Env Bool Bool) {s : Strat Bool} {ω : Bool} {c : ℝ}
    (h1 : ∀ y, y < c → s.σ ω y = 1) (h2 : ∀ y, c < y → s.σ ω y = 0) :
    E.Fm c ≤ E.rp s ω ∧ E.rp s ω ≤ E.F c := by
  constructor
  · have e : E.Fm c = ∫ x, (Iio c).indicator (fun _ => (1 : ℝ)) x ∂(E.cost : Measure ℝ) := by
      rw [integral_indicator_const _ measurableSet_Iio]
      simp [Env.Fm]
    rw [e]
    refine integral_mono ?_ (Env.integrable_sigma E s ω) fun x => ?_
    · exact (integrable_const (1 : ℝ)).indicator measurableSet_Iio
    · by_cases hx : x < c
      · rw [indicator_of_mem (mem_Iio.2 hx), h1 x hx]
      · rw [indicator_of_notMem (by simpa using hx)]
        exact (s.mem ω x).1
  · have e : E.F c = ∫ x, (Iic c).indicator (fun _ => (1 : ℝ)) x ∂(E.cost : Measure ℝ) := by
      rw [integral_indicator_const _ measurableSet_Iic]
      simp [Env.F]
    rw [e]
    refine integral_mono (Env.integrable_sigma E s ω) ?_ fun x => ?_
    · exact (integrable_const (1 : ℝ)).indicator measurableSet_Iic
    · by_cases hx : x ≤ c
      · rw [indicator_of_mem (mem_Iic.2 hx)]
        exact (s.mem ω x).2
      · rw [indicator_of_notMem (by simpa using hx), h2 x (not_le.1 hx)]

/-- The strategy with constant report probability, realising an arbitrary profile `q`. -/
noncomputable def constStrat (q : Bool → ℝ) (hq : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) : Strat Bool where
  σ := fun ω _ => q ω
  meas := (Measurable.of_discrete (f := q)).comp measurable_fst
  mem := fun ω _ => hq ω

lemma rp_constStrat (E : Env Bool Bool) (q : Bool → ℝ) (hq : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) (ω : Bool) :
    E.rp (constStrat q hq) ω = q ω := by
  simp [Env.rp, constStrat]

/-- The key estimate: under a monotone rule, either reports do not matter or the report probabilities
lie in a band whose width is the gap of `F` around zero. -/
theorem biased_key (E : Env Bool Bool) (hFB : E.PiSQ < E.PiFB) {pu pd : ℝ} (hpu : 0 < pu) (hpd : 0 < pd)
    (hsum : pu + pd < 1) {n : ℕ} (hn : 2 ≤ n) {d : Rule Bool} (hmono : MonotoneRule n (rateX d)) {σu σd : Bool → ℝ}
    {s : Strat Bool} (he : BiasedEq E pu pd n d σu σd s) :
    biasedPayoff E pu pd n d σu σd s ≤ E.PiSQ ∨
    ∃ P Q : ℝ, P ∈ Icc (min pu pd) (1 - min pu pd) ∧ Q ∈ Icc (min pu pd) (1 - min pu pd) ∧ P ≤ Q ∧
      Q - P ≤ E.F (Env.pivConst E.B (min pu pd) / √(n : ℝ))
        - E.F (-2 * (Env.pivConst E.B (min pu pd) / √(n : ℝ))) ∧
      biasedPayoff E pu pd n d σu σd s ≤ (1 - tv n P Q) * E.PiSQ + tv n P Q * E.PiFB := by
  by_cases hnc : NonconstantRule n (rateX d)
  swap
  · -- a rule that is constant on `{0,…,n}` ignores the reports
    left
    unfold NonconstantRule at hnc
    push Not at hnc
    have hconst : ∀ k ≤ n, rateX d k = rateX d 0 := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        rw [hnc k (by omega), ih (by omega)]
    have hv : ∀ ω, ∀ k ≤ n, E.v d k ω = E.v d 0 ω := fun ω k hk => by
      rw [v_eq_rate, v_eq_rate, hconst k hk]
    have hpt : ∀ ω, bexp n (biasedRp pu pd (σu ω) (σd ω) (E.rp s ω)) (fun k => E.v d k ω) = E.v d 0 ω := by
      intro ω
      rw [bexp_congr (w := fun _ => E.v d 0 ω) (fun k hk => hv ω k hk)]
      unfold bexp
      rw [← Finset.sum_mul, bpmf_sum, one_mul]
    unfold biasedPayoff
    simp_rw [hpt]
    exact E.integral_v_le_PiSQ d 0
  right
  set l := min pu pd with hl
  have hl0 : 0 < l := lt_min hpu hpd
  have hl1 : l ≤ 1 / 2 := by
    have h1 := min_le_left pu pd
    have h2 := min_le_right pu pd
    linarith
  set w := 1 - pu - pd with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  have hw1 : w ≤ 1 := by rw [hw]; linarith
  set M := Env.pivConst E.B l with hM
  set h := M / √(n : ℝ) with hh
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMpos : 0 < M := Env.pivConst_pos (E.B_pos_of_lt hFB) hl0 hl1
  have hh0 : 0 < h := div_pos hMpos (Real.sqrt_pos.2 hnr)
  -- the biased types' behaviour is the same in every state
  obtain ⟨a, ha, hq⟩ : ∃ a, (a = pu ∨ a = pd) ∧ ∀ ω, biasedRp pu pd (σu ω) (σd ω) (E.rp s ω) = a + w * E.rp s ω := by
    rcases hmono with hinc | hdec
    · refine ⟨pu, Or.inl rfl, fun ω => ?_⟩
      have hu := (dominance_values (Or.inl hinc) hnc (he.up ω) (he.down ω))
      have hk := hnc
      obtain ⟨k₀, hk₀, hne⟩ := hk
      have h1 := lt_of_le_of_ne (hinc k₀ hk₀) hne.symm
      rcases hu with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · unfold biasedRp; rw [h2, h3]; ring
      · -- the other branch contradicts monotonicity
        exfalso
        have h4 := (he.up ω).1 ⟨fun k hk => hinc k (by omega), k₀, by omega, h1⟩
        rw [h2] at h4
        norm_num at h4
    · refine ⟨pd, Or.inr rfl, fun ω => ?_⟩
      have hu := (dominance_values (Or.inr hdec) hnc (he.up ω) (he.down ω))
      obtain ⟨k₀, hk₀, hne⟩ := hnc
      have h1 := lt_of_le_of_ne (hdec k₀ hk₀) hne
      rcases hu with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exfalso
        have h4 := (he.up ω).2 ⟨fun k hk => hdec k (by omega), k₀, by omega, h1⟩
        rw [h2] at h4
        norm_num at h4
      · unfold biasedRp; rw [h2, h3]; ring
  have hqmem : ∀ ω, biasedRp pu pd (σu ω) (σd ω) (E.rp s ω) ∈ Icc l (1 - l) := fun ω =>
    prop_monotone hpu hpd hsum hmono hnc (he.up ω) (he.down ω)
      ⟨Env.rp_nonneg E s ω, Env.rp_le_one E s ω⟩
  -- the band
  have hband : ∀ ω, E.Fm (-h) ≤ E.rp s ω ∧ E.rp s ω ≤ E.F h := by
    intro ω
    have hbd := abs_le.1 (Env.abs_gross_le_of_mem E hn d hl0 hl1 (hqmem ω) ω)
    obtain ⟨h1, h2⟩ := rp_band_of_cutoff E (s := s) (ω := ω)
      (fun y hy => (he.unbiased ω y).1 hy) (fun y hy => (he.unbiased ω y).2 hy)
    exact ⟨(Env.Fm_mono E hbd.1).trans h1, h2.trans (Env.F_mono E hbd.2)⟩
  let P := max (a + w * E.Fm (-h)) l
  let Q := min (a + w * E.F h) (1 - l)
  have hqPQ : ∀ ω, biasedRp pu pd (σu ω) (σd ω) (E.rp s ω) ∈ Icc P Q := by
    intro ω
    have h1 := hqmem ω
    rw [hq ω] at h1 ⊢
    have h2 := hband ω
    refine ⟨max_le (by nlinarith [h2.1]) h1.1, le_min (by nlinarith [h2.2]) h1.2⟩
  have hPl : l ≤ P := le_max_right _ _
  have hQl : Q ≤ 1 - l := min_le_right _ _
  have hPQ : P ≤ Q := (hqPQ true).1.trans (hqPQ true).2
  refine ⟨P, Q, ⟨hPl, hPQ.trans hQl⟩, ⟨hPl.trans hPQ, hQl⟩, hPQ, ?_, ?_⟩
  · have h1 : Q ≤ a + w * E.F h := min_le_left _ _
    have h2 : a + w * E.Fm (-h) ≤ P := le_max_left _ _
    have h3 : E.F (-2 * h) ≤ E.Fm (-h) := Env.F_le_Fm E (by linarith)
    have h4 : E.Fm (-h) ≤ E.F h := (Env.Fm_mono E (by linarith)).trans (Env.Fm_le_F E h)
    have h5 : 0 ≤ E.F h - E.Fm (-h) := by linarith
    nlinarith
  · let hq01 : ∀ ω, biasedRp pu pd (σu ω) (σd ω) (E.rp s ω) ∈ Icc (0 : ℝ) 1 := fun ω =>
      ⟨by linarith [(hqmem ω).1], by linarith [(hqmem ω).2]⟩
    let s' := constStrat (fun ω => biasedRp pu pd (σu ω) (σd ω) (E.rp s ω)) hq01
    have hrp' : ∀ ω, E.rp s' ω = biasedRp pu pd (σu ω) (σd ω) (E.rp s ω) := rp_constStrat E _ hq01
    have hbound := Env.payoff_le_tv E n d s' (a := P) (b := Q) (by linarith) (by linarith)
      (fun ω => by rw [hrp' ω]; exact hqPQ ω)
    have heq : E.payoff n d s' = biasedPayoff E pu pd n d σu σd s := by
      unfold Env.payoff biasedPayoff
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      show bexp n (E.rp s' ω) _ = _
      rw [hrp' ω]
    rw [← heq]
    exact hbound

/-- **The upper bounds with biased individuals.** Uniformly over monotone rules and equilibria without
weakly dominated actions. -/
theorem biased_upper (E : Env Bool Bool) (hFB : E.PiSQ < E.PiFB) {pu pd : ℝ} (hpu : 0 < pu) (hpd : 0 < pd)
    (hsum : pu + pd < 1) :
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, ∀ (d : Rule Bool) (σu σd : Bool → ℝ)
      (s : Strat Bool), MonotoneRule n (rateX d) → BiasedEq E pu pd n d σu σd s →
        biasedPayoff E pu pd n d σu σd s ≤ E.PiSQ) ∧
    (HasDerivAt E.F 0 0 → ∀ ε > 0, ∀ᶠ n in atTop, ∀ (d : Rule Bool) (σu σd : Bool → ℝ)
      (s : Strat Bool), MonotoneRule n (rateX d) → BiasedEq E pu pd n d σu σd s →
        biasedPayoff E pu pd n d σu σd s ≤ E.PiSQ + ε) ∧
    (∀ t, HasDerivAt E.F t 0 → ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ᶠ n in atTop, ∀ (d : Rule Bool)
      (σu σd : Bool → ℝ) (s : Strat Bool), MonotoneRule n (rateX d) → BiasedEq E pu pd n d σu σd s →
        biasedPayoff E pu pd n d σu σd s ≤ β * E.PiSQ + (1 - β) * E.PiFB) := by
  set l := min pu pd with hl
  have hl0 : 0 < l := lt_min hpu hpd
  have hl1 : l ≤ 1 / 2 := by
    have h1 := min_le_left pu pd
    have h2 := min_le_right pu pd
    linarith
  set M := Env.pivConst E.B l with hM
  have hMpos : 0 < M := Env.pivConst_pos (E.B_pos_of_lt hFB) hl0 hl1
  have hSF := E.PiSQ_le_PiFB
  refine ⟨fun δ hδ hF => ?_, fun hF ε hε => ?_, fun t hF => ?_⟩
  · -- Statement 1
    obtain ⟨N, hN⟩ := exists_nat_gt ((2 * M / δ) ^ 2)
    refine ⟨max N 2, fun n hn d σu σd s hmono he => ?_⟩
    have hn2 : 2 ≤ n := by
      have := le_max_right N 2
      omega
    have hnN : (N : ℝ) < n := by
      have := le_max_left N 2
      exact_mod_cast (show N < n by omega)
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
    have hsmall : 2 * (M / √(n : ℝ)) < δ := by
      have h1 : 2 * M / δ < √(n : ℝ) := Real.lt_sqrt_of_sq_lt (hN.trans hnN)
      rw [div_lt_iff₀ hδ] at h1
      have e : 2 * (M / √(n : ℝ)) = 2 * M / √(n : ℝ) := by ring
      rw [e, div_lt_iff₀ hs]
      linarith
    have hh0 : 0 < M / √(n : ℝ) := div_pos hMpos hs
    rcases biased_key E hFB hpu hpd hsum hn2 hmono he with h | ⟨P, Q, _, _, hPQ, hgap, hbound⟩
    · exact h
    · have h1 : E.F (M / √(n : ℝ)) ≤ E.F δ := Env.F_mono E (by linarith)
      have h2 : E.F (-δ) ≤ E.F (-2 * (M / √(n : ℝ))) := Env.F_mono E (by linarith)
      have hPQe : P = Q := le_antisymm hPQ (by linarith)
      have htv : tv n P Q = 0 := by
        unfold tv
        rw [hPQe]
        simp
      rw [htv] at hbound
      simpa using hbound
  · -- Statement 2
    have hgap := Env.tendsto_sqrt_mul_gap hF hMpos
    simp only [mul_zero] at hgap
    let θ : ℕ → ℝ := fun n =>
      √((√(n : ℝ) * (E.F (M / √(n : ℝ)) - E.F (-2 * (M / √(n : ℝ))))) ^ 2 / (2 * l))
    have hθ : Tendsto θ atTop (𝓝 0) := by
      have := ((hgap.pow 2).div_const (2 * l)).sqrt
      simpa [θ] using this
    have hlim : Tendsto (fun n => θ n * (E.PiFB - E.PiSQ)) atTop (𝓝 0) := by
      have := hθ.mul_const (E.PiFB - E.PiSQ)
      simpa using this
    filter_upwards [(tendsto_order.1 hlim).2 ε hε, eventually_ge_atTop 2] with n hn hn2 d σu σd s hmono he
    rcases biased_key E hFB hpu hpd hsum hn2 hmono he with h | ⟨P, Q, hPm, hQm, hPQ, hgap', hbound⟩
    · linarith
    · have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have htv : tv n P Q ≤ θ n := by
        refine (tv_le_of_close hl0 hPm hQm).trans (Real.sqrt_le_sqrt ?_)
        have hg0 : 0 ≤ Q - P := by linarith
        have hsq : (P - Q) ^ 2 ≤ (E.F (M / √(n : ℝ)) - E.F (-2 * (M / √(n : ℝ)))) ^ 2 := by
          have : (P - Q) ^ 2 = (Q - P) ^ 2 := by ring
          rw [this]
          exact pow_le_pow_left₀ hg0 hgap' 2
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [mul_pow, Real.sq_sqrt hnr.le]
        exact mul_le_mul_of_nonneg_left hsq hnr.le
      have : tv n P Q * (E.PiFB - E.PiSQ) ≤ θ n * (E.PiFB - E.PiSQ) :=
        mul_le_mul_of_nonneg_right htv (by linarith)
      nlinarith
  · -- Statement 3
    have hgap := Env.tendsto_sqrt_mul_gap hF hMpos
    set C : ℝ := (3 * M * t) ^ 2 + 1 with hC
    have hev : ∀ᶠ n : ℕ in atTop,
        (√(n : ℝ) * (E.F (M / √(n : ℝ)) - E.F (-2 * (M / √(n : ℝ))))) ^ 2 < C :=
      (tendsto_order.1 (hgap.pow 2)).2 C (by rw [hC]; linarith)
    set τ : ℝ := √(1 - exp (-C / l)) with hτ
    have hτ1 : τ < 1 := sqrt_one_sub_exp_lt_one
    have hτ0 : 0 ≤ τ := Real.sqrt_nonneg _
    refine ⟨1 - τ, by linarith, by linarith, ?_⟩
    have hm2 : ∀ᶠ n : ℕ in atTop, C / (2 * l) ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    filter_upwards [eventually_ge_atTop 2, hev, hm2] with n hn hevn hmn d σu σd s hmono he
    rcases biased_key E hFB hpu hpd hsum hn hmono he with h | ⟨P, Q, hPm, hQm, hPQ, hgap', hbound⟩
    · nlinarith
    · have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have htv : tv n P Q ≤ τ := by
        refine tv_le_of_bounded hl0 hPm hQm (by omega) ?_ hmn
        have hg0 : 0 ≤ Q - P := by linarith
        have hsq : (P - Q) ^ 2 ≤ (E.F (M / √(n : ℝ)) - E.F (-2 * (M / √(n : ℝ)))) ^ 2 := by
          have : (P - Q) ^ 2 = (Q - P) ^ 2 := by ring
          rw [this]
          exact pow_le_pow_left₀ hg0 hgap' 2
        have hmul : (n : ℝ) * (P - Q) ^ 2
            ≤ (n : ℝ) * (E.F (M / √(n : ℝ)) - E.F (-2 * (M / √(n : ℝ)))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hnr.le
        rw [mul_pow, Real.sq_sqrt hnr.le] at hevn
        linarith
      have : tv n P Q * (E.PiFB - E.PiSQ) ≤ τ * (E.PiFB - E.PiSQ) :=
        mul_le_mul_of_nonneg_right htv (by linarith)
      nlinarith

end VD

end NoisyVD
