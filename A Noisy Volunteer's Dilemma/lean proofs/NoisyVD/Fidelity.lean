import NoisyVD.Biased
import NoisyVD.Example

/-!
# Fidelity checks

Machine-checked evidence that the definitions and statements mean what the paper says:

* `phi`, `Phi` agree with Mathlib's standard Gaussian; `Fm` is the left limit of `F`; the `sSup`s
  defining `B`, `Π^SQ`, `Π^FB` are attained maxima;
* reading Bayesian Nash equilibrium as "almost every type in almost every state" leaves the set of
  attainable payoffs unchanged;
* more direct forms of Propositions 1, B1 and B2, existence of equilibrium in Proposition 2, and the
  threshold claim for the reinterpreted models of Appendix B.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

/-! ### Cross-checks of the definitions -/

/-- `phi` is Mathlib's standard normal density. -/
theorem phi_eq_gaussianPDFReal (x : ℝ) : phi x = ProbabilityTheory.gaussianPDFReal 0 1 x := by
  simp [phi, ProbabilityTheory.gaussianPDFReal]

/-- `Phi` is Mathlib's standard normal distribution function. -/
theorem Phi_eq_cdf (x : ℝ) :
    Phi x = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x := by
  rw [ProbabilityTheory.cdf_eq_real]
  have h : ProbabilityTheory.gaussianReal 0 1 = Example.normalMeasure := by
    rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ one_ne_zero]
    unfold Example.normalMeasure ProbabilityTheory.gaussianPDF
    congr 1
    funext y
    rw [phi_eq_gaussianPDFReal]
  rw [h, Example.normal_real _ measurableSet_Iic]
  rfl

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

namespace Env

/-- `Fm c` is the left limit `F(c⁻)`. -/
theorem tendsto_F_left (E : Env A Ω) (c : ℝ) : Tendsto E.F (𝓝[<] c) (𝓝 (E.Fm c)) := by
  rw [tendsto_order]
  constructor
  · intro y hy
    obtain ⟨c₀, hc₀, hy₀⟩ := E.exists_lt_Fm hy
    filter_upwards [Ioo_mem_nhdsLT hc₀] with x hx
    exact lt_of_lt_of_le hy₀ ((Fm_mono E hx.1.le).trans (Fm_le_F E x))
  · intro y hy
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact lt_of_le_of_lt (F_le_Fm E hx) hy

/-- `F` is right continuous, so it is a distribution function. -/
theorem tendsto_F_right (E : Env A Ω) (c : ℝ) : Tendsto E.F (𝓝[>] c) (𝓝 (E.F c)) := by
  rw [tendsto_order]
  constructor
  · intro y hy
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact lt_of_lt_of_le hy (F_mono E (le_of_lt hx))
  · intro y hy
    exact (E.upperSemicontinuous_F c y hy).filter_mono nhdsWithin_le_nhds

/-- `B` is the range of `u^p`: its two parts are attained. -/
theorem B_attained (E : Env A Ω) :
    (∃ a ω, E.u a ω = E.uMax) ∧ (∃ a ω, E.u a ω = E.uMin) := by
  have := E.nonempty_state
  have hne : (range (Function.uncurry E.u)).Nonempty := range_nonempty _
  obtain ⟨x, hx⟩ := E.isCompact_range_u.exists_isGreatest hne
  obtain ⟨z, hz⟩ := E.isCompact_range_u.exists_isLeast hne
  obtain ⟨⟨a, ω⟩, rfl⟩ := hx.1
  obtain ⟨⟨a', ω'⟩, rfl⟩ := hz.1
  exact ⟨⟨a, ω, hx.csSup_eq.symm⟩, ⟨a', ω', hz.csInf_eq.symm⟩⟩

/-! ### Equilibrium notion -/

/-- Bayesian Nash equilibrium in the "almost every" sense: best response by almost every type in
almost every state. -/
def IsEqAE (E : Env A Ω) (n : ℕ) (d : Rule A) (s : Strat Ω) : Prop :=
  ∀ᵐ ω ∂(E.prior : Measure Ω), ∀ᵐ x ∂(E.cost : Measure ℝ),
    (x < E.gross n d (E.rp s ω) ω → s.σ ω x = 1) ∧ (E.gross n d (E.rp s ω) ω < x → s.σ ω x = 0)

/-- **The almost-everywhere reading of equilibrium gives the same attainable payoffs**, hence the
same `Π(n)`.  The paper's Lemmas 1 and 2 speak of every type, which is the definition `IsEq`. -/
theorem payoffs_ae_eq (E : Env A Ω) (n : ℕ) :
    {y | ∃ (d : Rule A) (s : Strat Ω), E.IsEqAE n d s ∧ y = E.payoff n d s} = E.payoffs n := by
  ext y
  constructor
  · rintro ⟨d, s, he, rfl⟩
    obtain ⟨s₀, hs₀⟩ := E.exists_equilibrium n d
    let c : Ω → ℝ := fun ω => E.gross n d (E.rp s ω) ω
    have hgc := E.continuous_gross n d
    have hcm : Measurable c := hgc.measurable.comp ((measurable_id).prodMk (measurable_rp E s))
    let c₀ : Ω → ℝ := fun ω => E.gross n d (E.rp s₀ ω) ω
    have hc₀m : Measurable c₀ := hgc.measurable.comp ((measurable_id).prodMk (measurable_rp E s₀))
    let G : Set Ω := {ω | E.Fm (c ω) ≤ E.rp s ω ∧ E.rp s ω ≤ E.F (c ω)}
    have hGm : MeasurableSet G :=
      (measurableSet_le ((measurable_Fm E).comp hcm) (measurable_rp E s)).inter
        (measurableSet_le (measurable_rp E s) ((measurable_F E).comp hcm))
    -- almost every state is in `G`
    have hG : ∀ᵐ ω ∂(E.prior : Measure Ω), ω ∈ G := by
      filter_upwards [he] with ω hω
      constructor
      · have h1 : E.Fm (c ω) = ∫ x, (Iio (c ω)).indicator (fun _ => (1 : ℝ)) x ∂(E.cost : Measure ℝ) := by
          rw [integral_indicator_const _ measurableSet_Iio]
          simp [Fm]
        rw [h1]
        refine integral_mono_ae ?_ (integrable_sigma E s ω) ?_
        · exact (integrable_const (1 : ℝ)).indicator measurableSet_Iio
        · filter_upwards [hω] with x hx
          by_cases hxc : x < c ω
          · rw [indicator_of_mem (mem_Iio.2 hxc), hx.1 hxc]
          · rw [indicator_of_notMem (by simpa using hxc)]
            exact (s.mem ω x).1
      · have h1 : E.F (c ω) = ∫ x, (Iic (c ω)).indicator (fun _ => (1 : ℝ)) x ∂(E.cost : Measure ℝ) := by
          rw [integral_indicator_const _ measurableSet_Iic]
          simp [F]
        rw [h1]
        refine integral_mono_ae (integrable_sigma E s ω) ?_ ?_
        · exact (integrable_const (1 : ℝ)).indicator measurableSet_Iic
        · filter_upwards [hω] with x hx
          by_cases hxc : x ≤ c ω
          · rw [indicator_of_mem (mem_Iic.2 hxc)]
            exact (s.mem ω x).2
          · rw [indicator_of_notMem (by simpa using hxc), hx.2 (not_le.1 hxc)]
    classical
    let q : Ω → ℝ := fun ω => if ω ∈ G then E.rp s ω else E.rp s₀ ω
    let c' : Ω → ℝ := fun ω => if ω ∈ G then c ω else c₀ ω
    have hqm : Measurable q := Measurable.ite hGm (measurable_rp E s) (measurable_rp E s₀)
    have hc'm : Measurable c' := Measurable.ite hGm hcm hc₀m
    have hband : ∀ ω, E.Fm (c' ω) ≤ q ω ∧ q ω ≤ E.F (c' ω) := by
      intro ω
      by_cases hω : ω ∈ G
      · simp only [q, c', ite_eq_left hω]
        exact hω
      · simp only [q, c', ite_eq_right hω]
        exact band E hs₀ ω
    obtain ⟨s', hrp, h1, h2⟩ := E.exists_cutoff_strategy hqm hc'm hband
    have hgross : ∀ ω, E.gross n d (E.rp s' ω) ω = c' ω := by
      intro ω
      rw [hrp ω]
      by_cases hω : ω ∈ G
      · simp only [q, c', ite_eq_left hω]
        rfl
      · simp only [q, c', ite_eq_right hω]
        rfl
    refine ⟨d, s', fun ω x => ?_, ?_⟩
    · rw [hgross ω]
      exact ⟨h1 ω x, h2 ω x⟩
    · unfold payoff
      refine integral_congr_ae ?_
      filter_upwards [hG] with ω hω
      show bexp n (E.rp s ω) _ = bexp n (E.rp s' ω) _
      rw [hrp ω]
      simp only [q, ite_eq_left hω]
  · rintro ⟨d, s, he, rfl⟩
    exact ⟨d, s, Eventually.of_forall fun ω => Eventually.of_forall fun x => he ω x, rfl⟩

end Env

/-! ### More direct forms of the benchmark results -/

namespace VD

variable {E : Env Bool Bool}

/-- **Proposition 1, limit claim, stated along equilibria.**  Along any sequence of symmetric
equilibria, the probability of no investigation in state `1` converges to `ν̲/H`, and there is never
an investigation in state `0`. -/
theorem prop_no_clueless_limit {a b : ℝ} (hC : BenchmarkCost E a b) (hH : a < H E) (hL : L E < 0)
    {s : ℕ → Strat Bool} (hs : ∀ n, 2 ≤ n → E.IsEq n oneReport (s n)) :
    (∀ n, 2 ≤ n → btail n (E.rp (s n) false) 1 = 0) ∧
      Tendsto (fun n => 1 - btail n (E.rp (s n) true) 1) atTop (𝓝 (a / H E)) := by
  obtain ⟨hprop, hlim, _⟩ := prop_no_clueless hC hH hL
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨c, _, _, _, _, hall⟩ := hprop n hn
    exact (hall (s n) (hs n hn)).2.2.1
  · classical
    let c : ℕ → ℝ := fun n => if h : 2 ≤ n then Classical.choose (hprop n h) else a
    have hc : ∀ n (h : 2 ≤ n), c n = Classical.choose (hprop n h) := fun n h => dite_eq_left h
    have hspec : ∀ n, 2 ≤ n → c n ∈ Ioo a b ∧ c n = H E * (1 - E.F (c n)) ^ (n - 1) := by
      intro n h
      rw [hc n h]
      have := Classical.choose_spec (hprop n h)
      exact ⟨this.1, this.2.1⟩
    refine (hlim c hspec).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have := Classical.choose_spec (hprop n hn)
    rw [hc n hn]
    exact (this.2.2.2.2 (s n) (hs n hn)).2.2.2.2.2.2.symm

/-- **Proposition 2 is not vacuous**: for all large `n` an equilibrium exists under every threshold. -/
theorem exists_eq_mech {a ε : ℝ} (ha : 0 < a) (hFa : E.Fm a = 0) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ nStar : ℕ, ∀ n ≥ nStar, ∀ T : ℕ, ∃ s : Strat Bool,
      IsEqMech E ε n (thresholdRule T true false) s := by
  set l := ε / 2 with hl
  have hl0 : 0 < l := by rw [hl]; linarith
  have hl1 : l ≤ 1 / 2 := by rw [hl]; linarith
  set D : ℝ := max |H E| |L E| + 1 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hlim : Tendsto (fun n : ℕ => D * massConst l / √((n - 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))) _
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 a ha)
  refine ⟨max N₁ 2, fun n hn T => ?_⟩
  have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hm : 1 ≤ n - 1 := by omega
  have hsm : 0 < √((n - 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  -- only mechanical types report, and the rational types abstain at every positive-mass type
  let c : Bool → ℝ := fun ω => E.gross n (thresholdRule T true false) (ε / 2) ω
  have hlI : ε / 2 ∈ Icc l (1 - l) := ⟨le_rfl, by rw [hl]; linarith⟩
  have hca : ∀ ω, c ω < a := by
    intro ω
    show E.gross n (thresholdRule T true false) (ε / 2) ω < a
    rw [gross_threshold]
    have hρ := rho_le_mass (T := T) hm hl0 hl1 hlI
    have hρ0 : 0 ≤ rho (n - 1) (ε / 2) T := rho_nonneg (by linarith) (by linarith)
    have hG : E.u true ω - E.u false ω ≤ D := by
      have h1 : E.u true ω - E.u false ω ≤ max |H E| |L E| := by
        cases ω
        · exact (le_abs_self _).trans (le_max_right _ _)
        · exact (le_abs_self _).trans (le_max_left _ _)
      rw [hD]; linarith
    calc rho (n - 1) (ε / 2) T * (E.u true ω - E.u false ω)
        ≤ rho (n - 1) (ε / 2) T * D := mul_le_mul_of_nonneg_left hG hρ0
      _ ≤ massConst l / √((n - 1 : ℕ) : ℝ) * D := mul_le_mul_of_nonneg_right hρ hDpos.le
      _ = D * massConst l / √((n - 1 : ℕ) : ℝ) := by ring
      _ < a := hN₁ n hn1
  have hband : ∀ ω, E.Fm (min (c ω) a) ≤ 0 ∧ (0 : ℝ) ≤ E.F (min (c ω) a) := fun ω =>
    ⟨(Env.Fm_mono E (min_le_right _ _)).trans_eq hFa, Env.F_nonneg E _⟩
  obtain ⟨s, hrp, h1, h2⟩ := E.exists_cutoff_strategy (q := fun _ => 0)
    (c := fun ω => min (c ω) a) measurable_const Measurable.of_discrete hband
  have hmin : ∀ ω, min (c ω) a = c ω := fun ω => min_eq_left (hca ω).le
  refine ⟨s, fun ω x => ?_⟩
  have hq : mechRp E ε s ω = ε / 2 := by
    unfold mechRp
    rw [hrp ω]; ring
  rw [hq]
  have e : E.gross n (thresholdRule T true false) (ε / 2) ω = c ω := rfl
  rw [e]
  have h1' := h1 ω x
  have h2' := h2 ω x
  rw [hmin ω] at h1' h2'
  exact ⟨h1', h2'⟩

/-! ### The threshold claim for the reinterpreted models -/

/-- **The threshold claim for behavioural types and noisy communication.** With `F̃` the reinterpreted
distribution, `liminf Π^T(n) > Π^SQ` iff `F̃'(0) > \bar F_0`, where `\bar F_0` is evaluated at `F̃(0)`. -/
theorem micro_threshold_iff (hV : Assumptions E) {w₁ w₀ g : ℝ} (h : MixPar w₁ w₀ g) {t : ℝ}
    (ht : 0 < t) (hS : Smooth E t) :
    (0 < Fbar (pr E) (H E) (-L E)
      ((w₁ + (1 - w₁ - w₀) * E.F 0) * (1 - (w₁ + (1 - w₁ - w₀) * E.F 0)))) ∧
    (E.PiSQ < liminf (E.microPiT w₁ w₀ g) atTop ↔
      Fbar (pr E) (H E) (-L E)
        ((w₁ + (1 - w₁ - w₀) * E.F 0) * (1 - (w₁ + (1 - w₁ - w₀) * E.F 0)))
        < (1 - w₁ - w₀) * (t * g)) := by
  have hg := h.g_pos
  have hw : 0 < 1 - w₁ - w₀ := by linarith [h.sum_lt]
  have hB := E.B_nonneg
  have hF0 : (E.mixEnv h).F 0 = w₁ + (1 - w₁ - w₀) * E.F 0 := by
    have := E.mix_F h (c := 0) (by simp; linarith)
    simpa using this
  have hV' : Assumptions (E.mixEnv h) := ⟨hV.H_pos, hV.L_neg, hV.pr_pos, hV.prior⟩
  have hN' := E.mix_noise h
  have hS' : Smooth (E.mixEnv h) ((1 - w₁ - w₀) * (t * g)) := by
    refine ⟨E.mix_hasDerivAt h hS.hasDeriv, ?_⟩
    obtain ⟨ε₀, hε₀, hcont⟩ := hS.cont
    refine ⟨min (ε₀ / g) (E.B + 1), lt_min (div_pos hε₀ hg) (by linarith), fun x hx => ?_⟩
    have hx1 : |x| < E.B + 1 := lt_of_lt_of_le hx (min_le_right _ _)
    have hx2 : |x| < ε₀ / g := lt_of_lt_of_le hx (min_le_left _ _)
    have hgx : |g * x| < ε₀ := by
      rw [abs_mul, abs_of_pos hg]
      rw [lt_div_iff₀ hg] at hx2
      linarith
    have hnear : ∀ᶠ c in 𝓝 x, (E.mixEnv h).F c = w₁ + (1 - w₁ - w₀) * E.F (g * c) := by
      have h1 : Continuous fun c : ℝ => |c| := continuous_abs
      filter_upwards [h1.continuousAt.eventually (gt_mem_nhds hx1)] with c hc
      exact E.mix_F h hc
    have hc2 : ContinuousAt (fun c => w₁ + (1 - w₁ - w₀) * E.F (g * c)) x := by
      have h3 : ContinuousAt (fun c : ℝ => E.F (g * c)) x :=
        ContinuousAt.comp (f := fun c : ℝ => g * c) (hcont _ hgx) (by fun_prop)
      exact continuousAt_const.add (continuousAt_const.mul h3)
    exact hc2.congr (hnear.mono fun c hc => hc.symm)
  have htpos : 0 < (1 - w₁ - w₀) * (t * g) := mul_pos hw (mul_pos ht hg)
  have hfun : E.microPiT w₁ w₀ g = (E.mixEnv h).PiT := funext (E.microPiT_eq h)
  have key := threshold_iff hV' hN' htpos hS'
  rw [hF0] at key
  rw [hfun]
  exact key

end VD

/-! ### Propositions B1 and B2 at the level of the game -/

/-- **Proposition `prop_monotone`, stated for a decision rule over `{0,1}`.** -/
theorem prop_monotone_rule {n : ℕ} {d : Rule Bool} {pu pd : ℝ} (hpu : 0 < pu) (hpd : 0 < pd)
    (hsum : pu + pd < 1) (hmono : MonotoneRule n (VD.rateX d)) (hnc : NonconstantRule n (VD.rateX d))
    {σu σd τ : ℝ} (hσu : NoDominated (n - 1) (Uup (VD.rateX d)) σu)
    (hσd : NoDominated (n - 1) (Udown (VD.rateX d)) σd) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    biasedRp pu pd σu σd τ ∈ Icc (min pu pd) (1 - min pu pd) :=
  prop_monotone hpu hpd hsum hmono hnc hσu hσd hτ

/-- **Proposition `prop_tie_breaking`, stated at the level of the game.**  Upward-biased types have
utility `a`, downward-biased types `-a`, and neither pays a cost.  Each best responds to the others'
reporting probability `p`, the upward-biased reporting and the downward-biased abstaining when
indifferent. -/
theorem prop_tie_breaking_game {n : ℕ} {x : ℕ → ℝ} {p pu pd : ℝ} (hpu : 0 < pu) (hpd : 0 < pd)
    (hsum : pu + pd < 1) {σu σd τ : ℝ} (hσu : σu ∈ Icc (0 : ℝ) 1) (hσd : σd ∈ Icc (0 : ℝ) 1)
    (hBRu : ∀ r ∈ Icc (0 : ℝ) 1,
      r * indivU (m := n - 1) p x 0 1 + (1 - r) * indivU (m := n - 1) p x 0 0
        ≤ σu * indivU (m := n - 1) p x 0 1 + (1 - σu) * indivU (m := n - 1) p x 0 0)
    (hBRd : ∀ r ∈ Icc (0 : ℝ) 1,
      r * indivU (m := n - 1) p (fun k => -x k) 0 1 + (1 - r) * indivU (m := n - 1) p (fun k => -x k) 0 0
        ≤ σd * indivU (m := n - 1) p (fun k => -x k) 0 1
          + (1 - σd) * indivU (m := n - 1) p (fun k => -x k) 0 0)
    (htieu : indivU (m := n - 1) p x 0 1 = indivU (m := n - 1) p x 0 0 → σu = 1)
    (htied : indivU (m := n - 1) p x 0 1 = indivU (m := n - 1) p x 0 0 → σd = 0)
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    biasedRp pu pd σu σd τ ∈ Icc (min pu pd) (1 - min pu pd) := by
  have hgain := indivU_gain (m := n - 1) p x 0
  have hgain' := indivU_gain (m := n - 1) p (fun k => -x k) 0
  have hneg : marginal (n - 1) p (fun k => -x k) = -marginal (n - 1) p x := by
    unfold marginal
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hneg] at hgain'
  obtain ⟨hu1, hu2⟩ := (bestResponse_iff hσu).1 hBRu
  obtain ⟨hd1, hd2⟩ := (bestResponse_iff hσd).1 hBRd
  refine prop_tie_breaking hpu hpd hsum (Δ := marginal (n - 1) p x) ⟨?_, ?_, ?_, ?_⟩ hτ
  · intro h
    rcases h.eq_or_lt with h0 | h0
    · refine htieu ?_
      linarith
    · exact hu1 (by linarith)
  · intro h
    exact hu2 (by linarith)
  · intro h
    rcases h.eq_or_lt with h0 | h0
    · refine htied ?_
      linarith
    · exact hd2 (by linarith)
  · intro h
    exact hd1 (by linarith)

end NoisyVD
