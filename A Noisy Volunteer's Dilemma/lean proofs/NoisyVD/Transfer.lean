import NoisyVD.Game
import NoisyVD.FirstBest

/-!
# Reinterpretations in Appendix `app_microfoundations`

*Behavioural types and noisy communication.*  Dropping Assumption 1, suppose a share `w₁` of the
population effectively always reports, a share `w₀` effectively never reports and the remaining share
`w = 1 - w₁ - w₀` consists of rational types who best respond to `g Δ`, where `Δ` is the gross
benefit of a report on the observed count.  This covers behavioural types (`w₁ = ε₁`, `w₀ = ε₀`,
`g = 1`) and noisy communication (`w₁ = w₀ = 1 - p`, `g = 2p - 1`).  We show the resulting game
*is* the model of Section 3 with the reinterpreted cost distribution
`F̃(c) = w₁ + w F(g c)` near zero (this is the footnote in the appendix), so that all of the results
apply: the sets of attainable payoffs coincide.

*Biased individuals.*  With upward- and downward-biased individuals and monotone rules, the upper
bounds of Proposition `prop_volunteers` continue to hold over equilibria without weakly dominated
actions.
-/

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace NoisyVD

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-- The parameters of the reinterpretation. -/
structure MixPar (w₁ w₀ g : ℝ) : Prop where
  w₁_pos : 0 < w₁
  w₀_pos : 0 < w₀
  sum_lt : w₁ + w₀ < 1
  g_pos : 0 < g

/-- The reinterpreted cost distribution: an atom `w₁` below `-B`, an atom `w₀` above `B` and the
rescaled original distribution with weight `w = 1 - w₁ - w₀`. -/
noncomputable def mixMeasure (ν : Measure ℝ) (B w₁ w₀ g : ℝ) : Measure ℝ :=
  ENNReal.ofReal w₁ • Measure.dirac (-B - 1) + ENNReal.ofReal w₀ • Measure.dirac (B + 1)
    + ENNReal.ofReal (1 - w₁ - w₀) • ν.map (fun x => x / g)

lemma isProb_mixMeasure {ν : Measure ℝ} [IsProbabilityMeasure ν] (B : ℝ) {w₁ w₀ g : ℝ}
    (h : MixPar w₁ w₀ g) : IsProbabilityMeasure (mixMeasure ν B w₁ w₀ g) := by
  constructor
  have hm : Measurable fun x : ℝ => x / g := measurable_id.div_const g
  have h1 := h.w₁_pos.le
  have h0 := h.w₀_pos.le
  have hw : 0 ≤ 1 - w₁ - w₀ := by linarith [h.sum_lt]
  simp only [mixMeasure, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h1 h0, ← ENNReal.ofReal_add (by linarith) hw]
  have : w₁ + w₀ + (1 - w₁ - w₀) = 1 := by ring
  rw [this]
  simp

/-- Integration against the reinterpreted distribution. -/
lemma integral_mixMeasure {ν : Measure ℝ} [IsProbabilityMeasure ν] (B : ℝ) {w₁ w₀ g : ℝ}
    (h : MixPar w₁ w₀ g) {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) :
    ∫ y, f y ∂(mixMeasure ν B w₁ w₀ g) = w₁ * f (-B - 1) + w₀ * f (B + 1)
      + (1 - w₁ - w₀) * ∫ x, f (x / g) ∂ν := by
  have hm : Measurable fun x : ℝ => x / g := measurable_id.div_const g
  have h1 := h.w₁_pos.le
  have h0 := h.w₀_pos.le
  have hw : 0 ≤ 1 - w₁ - w₀ := by linarith [h.sum_lt]
  have hprob : ∀ {μ : Measure ℝ} [IsProbabilityMeasure μ], Integrable f μ := fun {μ} _ =>
    Env.integrable_of_bdd μ hf hb
  have : IsProbabilityMeasure (ν.map fun x => x / g) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have i1 : Integrable f (ENNReal.ofReal w₁ • Measure.dirac (-B - 1)) :=
    hprob.smul_measure ENNReal.ofReal_ne_top
  have i2 : Integrable f (ENNReal.ofReal w₀ • Measure.dirac (B + 1)) :=
    hprob.smul_measure ENNReal.ofReal_ne_top
  have i3 : Integrable f (ENNReal.ofReal (1 - w₁ - w₀) • ν.map fun x => x / g) :=
    hprob.smul_measure ENNReal.ofReal_ne_top
  unfold mixMeasure
  rw [integral_add_measure (i1.add_measure i2) i3, integral_add_measure i1 i2,
    integral_smul_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, integral_map hm.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal hw]
  simp [smul_eq_mul]

namespace Env

/-- The model of Section 3 with the reinterpreted cost distribution. -/
noncomputable def mixEnv (E : Env A Ω) {w₁ w₀ g : ℝ} (h : MixPar w₁ w₀ g) : Env A Ω where
  u := E.u
  u_cont := E.u_cont
  prior := E.prior
  cost := ⟨mixMeasure (E.cost : Measure ℝ) E.B w₁ w₀ g, isProb_mixMeasure E.B h⟩

variable (E : Env A Ω) {w₁ w₀ g : ℝ} (h : MixPar w₁ w₀ g)

lemma mixEnv_B : (E.mixEnv h).B = E.B := rfl
lemma mixEnv_PiSQ : (E.mixEnv h).PiSQ = E.PiSQ := rfl
lemma mixEnv_PiFB : (E.mixEnv h).PiFB = E.PiFB := rfl

lemma mix_real_eq {S : Set ℝ} (hS : MeasurableSet S) :
    ((E.mixEnv h).cost : Measure ℝ).real S
      = w₁ * S.indicator (fun _ => (1 : ℝ)) (-E.B - 1) + w₀ * S.indicator (fun _ => (1 : ℝ)) (E.B + 1)
        + (1 - w₁ - w₀) * ∫ x, S.indicator (fun _ => (1 : ℝ)) (x / g) ∂(E.cost : Measure ℝ) := by
  have hb : ∀ x, |S.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := fun x => by
    by_cases hx : x ∈ S <;> simp [hx]
  have hm : Measurable (S.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hS
  have h1 := integral_mixMeasure (ν := (E.cost : Measure ℝ)) E.B h hm hb
  rw [integral_indicator_const _ hS] at h1
  simp only [smul_eq_mul, mul_one] at h1
  exact h1

/-- Assumption 1 holds for the reinterpreted distribution, even though it need not hold for `F`. -/
lemma mix_noise : (E.mixEnv h).Noise := by
  have hB := E.B_nonneg
  have hw : 0 ≤ 1 - w₁ - w₀ := by linarith [h.sum_lt]
  have hint : ∀ S : Set ℝ, 0 ≤ ∫ x, S.indicator (fun _ => (1 : ℝ)) (x / g) ∂(E.cost : Measure ℝ) :=
    fun S => integral_nonneg fun x => indicator_nonneg (fun _ _ => zero_le_one) _
  constructor
  · rw [mixEnv_B, mix_real_eq E h measurableSet_Iio,
      indicator_of_mem (mem_Iio.2 (by linarith : -E.B - 1 < -E.B)),
      indicator_of_notMem (by simp only [mem_Iio, not_lt]; linarith)]
    have := mul_nonneg hw (hint (Iio (-E.B)))
    have := h.w₁_pos
    linarith
  · rw [mixEnv_B, mix_real_eq E h measurableSet_Ioi,
      indicator_of_notMem (by simp only [mem_Ioi, not_lt]; linarith),
      indicator_of_mem (mem_Ioi.2 (by linarith : E.B < E.B + 1))]
    have := mul_nonneg hw (hint (Ioi E.B))
    have := h.w₀_pos
    linarith

/-- The footnote of the appendix: `F̃(c) = w₁ + (1 - w₁ - w₀) F(g c)` near zero. -/
lemma mix_F {c : ℝ} (hc : |c| < E.B + 1) :
    (E.mixEnv h).F c = w₁ + (1 - w₁ - w₀) * E.F (g * c) := by
  have hc' := abs_lt.1 hc
  have hg := h.g_pos
  show ((E.mixEnv h).cost : Measure ℝ).real (Iic c) = _
  rw [mix_real_eq E h measurableSet_Iic,
    indicator_of_mem (mem_Iic.2 (by linarith : -E.B - 1 ≤ c)),
    indicator_of_notMem (by simp only [mem_Iic, not_le]; linarith)]
  have h1 : ∀ x : ℝ, (Iic c).indicator (fun _ => (1 : ℝ)) (x / g)
      = (Iic (g * c)).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    have hiff : x / g ∈ Iic c ↔ x ∈ Iic (g * c) := by
      rw [mem_Iic, mem_Iic, div_le_iff₀ hg]
      constructor <;> intro hh <;> linarith
    by_cases hx : x ∈ Iic (g * c)
    · rw [indicator_of_mem (hiff.2 hx), indicator_of_mem hx]
    · rw [indicator_of_notMem (mt hiff.1 hx), indicator_of_notMem hx]
  simp_rw [h1]
  rw [integral_indicator_const _ measurableSet_Iic]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
  rfl

/-- The overall reporting probability in the micro-founded game. -/
noncomputable def mq (E : Env A Ω) (w₁ w₀ : ℝ) (s : Strat Ω) (ω : Ω) : ℝ :=
  w₁ + (1 - w₁ - w₀) * E.rp s ω

/-- Equilibrium of the micro-founded game: rational types best respond to `g Δ`. -/
def IsMicroEq (E : Env A Ω) (w₁ w₀ g : ℝ) (n : ℕ) (d : Rule A) (s : Strat Ω) : Prop :=
  ∀ ω x, (x < g * E.gross n d (E.mq w₁ w₀ s ω) ω → s.σ ω x = 1) ∧
    (g * E.gross n d (E.mq w₁ w₀ s ω) ω < x → s.σ ω x = 0)

/-- The decision-maker's payoff in the micro-founded game. -/
noncomputable def microPayoff (E : Env A Ω) (w₁ w₀ : ℝ) (n : ℕ) (d : Rule A) (s : Strat Ω) : ℝ :=
  ∫ ω, bexp n (E.mq w₁ w₀ s ω) (fun k => E.v d k ω) ∂(E.prior : Measure Ω)

/-- `Π(n)` of the micro-founded game. -/
noncomputable def microPi (E : Env A Ω) (w₁ w₀ g : ℝ) (n : ℕ) : ℝ :=
  sSup {y | ∃ (d : Rule A) (s : Strat Ω), E.IsMicroEq w₁ w₀ g n d s ∧ y = E.microPayoff w₁ w₀ n d s}

lemma mq_mem (h : MixPar w₁ w₀ g) (s : Strat Ω) (ω : Ω) : E.mq w₁ w₀ s ω ∈ Icc (0 : ℝ) 1 := by
  have h1 := rp_nonneg E s ω
  have h2 := rp_le_one E s ω
  have h3 := h.w₁_pos
  have h4 := h.w₀_pos
  have h5 := h.sum_lt
  unfold mq
  constructor
  · have : 0 ≤ 1 - w₁ - w₀ := by linarith
    nlinarith
  · nlinarith

lemma mix_v (d : Rule A) (k : ℕ) (ω : Ω) : (E.mixEnv h).v d k ω = E.v d k ω := rfl

lemma mix_gross (n : ℕ) (d : Rule A) (p : ℝ) (ω : Ω) :
    (E.mixEnv h).gross n d p ω = E.gross n d p ω := rfl

/-- **The two games have the same attainable payoffs under every decision rule.** -/
theorem micro_rule_iff (n : ℕ) (d : Rule A) (y : ℝ) :
    (∃ s : Strat Ω, E.IsMicroEq w₁ w₀ g n d s ∧ y = E.microPayoff w₁ w₀ n d s) ↔
      ∃ s' : Strat Ω, (E.mixEnv h).IsEq n d s' ∧ y = (E.mixEnv h).payoff n d s' := by
  have hg := h.g_pos
  constructor
  · -- from the micro-founded game to the reinterpreted model
    rintro ⟨s, he, rfl⟩
    let s' : Strat Ω :=
      { σ := fun ω y => s.σ ω (g * y)
        meas := s.meas.comp (measurable_fst.prodMk (measurable_snd.const_mul g))
        mem := fun ω y => s.mem ω _ }
    have hrp : ∀ ω, (E.mixEnv h).rp s' ω = E.mq w₁ w₀ s ω := by
      intro ω
      have hbd := abs_le.1 (E.abs_gross_le n d (mq_mem E h s ω).1 (mq_mem E h s ω).2 ω)
      have h1 : s.σ ω (g * (-E.B - 1)) = 1 := (he ω _).1 (by
        apply mul_lt_mul_of_pos_left _ hg
        linarith [hbd.1])
      have h2 : s.σ ω (g * (E.B + 1)) = 0 := (he ω _).2 (by
        apply mul_lt_mul_of_pos_left _ hg
        linarith [hbd.2])
      have hm : Measurable fun y => s.σ ω (g * y) :=
        (Strat.measurable_slice s ω).comp (measurable_id.const_mul g)
      have hbd2 : ∀ y, |s.σ ω (g * y)| ≤ 1 := fun y => by
        rw [abs_le]; constructor <;> linarith [(s.mem ω (g * y)).1, (s.mem ω (g * y)).2]
      show ∫ y, s.σ ω (g * y) ∂(mixMeasure (E.cost : Measure ℝ) E.B w₁ w₀ g) = _
      rw [integral_mixMeasure E.B h hm hbd2, h1, h2]
      have h3 : ∀ x, s.σ ω (g * (x / g)) = s.σ ω x := fun x => by
        rw [mul_div_cancel₀ _ hg.ne']
      simp_rw [h3]
      unfold mq rp
      ring
    refine ⟨s', fun ω y => ?_, ?_⟩
    · rw [hrp ω, mix_gross]
      refine ⟨fun hy => (he ω _).1 (mul_lt_mul_of_pos_left hy hg),
        fun hy => (he ω _).2 (mul_lt_mul_of_pos_left hy hg)⟩
    · unfold microPayoff payoff
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      show bexp n (E.mq w₁ w₀ s ω) _ = bexp n ((E.mixEnv h).rp s' ω) _
      rw [hrp ω]
      rfl
  · -- from the reinterpreted model to the micro-founded game
    rintro ⟨s', he, rfl⟩
    let s : Strat Ω :=
      { σ := fun ω x => s'.σ ω (x / g)
        meas := s'.meas.comp (measurable_fst.prodMk (measurable_snd.div_const g))
        mem := fun ω x => s'.mem ω _ }
    have hrp : ∀ ω, (E.mixEnv h).rp s' ω = E.mq w₁ w₀ s ω := by
      intro ω
      have hbd := abs_le.1 (E.abs_gross_le n d (rp_nonneg (E.mixEnv h) s' ω)
        (rp_le_one (E.mixEnv h) s' ω) ω)
      have h1 : s'.σ ω (-E.B - 1) = 1 := (he ω _).1 (by
        rw [mix_gross]; linarith [hbd.1])
      have h2 : s'.σ ω (E.B + 1) = 0 := (he ω _).2 (by
        rw [mix_gross]; linarith [hbd.2])
      have hbd2 : ∀ y, |s'.σ ω y| ≤ 1 := fun y => by
        rw [abs_le]; constructor <;> linarith [(s'.mem ω y).1, (s'.mem ω y).2]
      show ∫ y, s'.σ ω y ∂(mixMeasure (E.cost : Measure ℝ) E.B w₁ w₀ g) = _
      rw [integral_mixMeasure E.B h (Strat.measurable_slice s' ω) hbd2, h1, h2]
      unfold mq rp
      ring
    refine ⟨s, fun ω x => ?_, ?_⟩
    · rw [← hrp ω]
      constructor
      · intro hx
        refine (he ω _).1 ?_
        rw [mix_gross, div_lt_iff₀ hg]
        linarith
      · intro hx
        refine (he ω _).2 ?_
        rw [mix_gross, lt_div_iff₀ hg]
        linarith
    · unfold microPayoff payoff
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      show bexp n ((E.mixEnv h).rp s' ω) _ = bexp n (E.mq w₁ w₀ s ω) _
      rw [hrp ω]
      rfl

/-- **The two games have the same attainable payoffs.** -/
theorem microPayoffs_eq (n : ℕ) :
    {y | ∃ (d : Rule A) (s : Strat Ω), E.IsMicroEq w₁ w₀ g n d s ∧ y = E.microPayoff w₁ w₀ n d s}
      = (E.mixEnv h).payoffs n := by
  ext y
  constructor
  · rintro ⟨d, s, he, hy⟩
    obtain ⟨s', he', hy'⟩ := (E.micro_rule_iff h n d y).1 ⟨s, he, hy⟩
    exact ⟨d, s', he', hy'⟩
  · rintro ⟨d, s', he, hy⟩
    obtain ⟨s, he', hy'⟩ := (E.micro_rule_iff h n d y).2 ⟨s', he, hy⟩
    exact ⟨d, s, he', hy'⟩

/-- `Π^T(n)` of the micro-founded game. -/
noncomputable def microPiT (E : Env A Ω) (w₁ w₀ g : ℝ) (n : ℕ) : ℝ :=
  sSup {y | ∃ (T : ℕ) (a₁ a₀ : A) (s : Strat Ω), T ≤ n + 1 ∧
    E.IsMicroEq w₁ w₀ g n (thresholdRule T a₁ a₀) s ∧
    y = E.microPayoff w₁ w₀ n (thresholdRule T a₁ a₀) s}

theorem microPiT_eq (n : ℕ) : E.microPiT w₁ w₀ g n = (E.mixEnv h).PiT n := by
  unfold microPiT PiT
  congr 1
  ext y
  constructor
  · rintro ⟨T, a₁, a₀, s, hT, he, hy⟩
    obtain ⟨s', he', hy'⟩ := (E.micro_rule_iff h n _ y).1 ⟨s, he, hy⟩
    exact ⟨T, a₁, a₀, s', hT, he', hy'⟩
  · rintro ⟨T, a₁, a₀, s', hT, he, hy⟩
    obtain ⟨s, he', hy'⟩ := (E.micro_rule_iff h n _ y).2 ⟨s', he, hy⟩
    exact ⟨T, a₁, a₀, s, hT, he', hy'⟩

theorem microPi_eq (n : ℕ) : E.microPi w₁ w₀ g n = (E.mixEnv h).Pi n := by
  unfold microPi Pi
  rw [microPayoffs_eq E h]

/-- Differentiability of the reinterpreted distribution at zero. -/
lemma mix_hasDerivAt (h : MixPar w₁ w₀ g) {t : ℝ} (ht : HasDerivAt E.F t 0) :
    HasDerivAt (E.mixEnv h).F ((1 - w₁ - w₀) * (t * g)) 0 := by
  have hB := E.B_nonneg
  have hnear : ∀ᶠ c in 𝓝 (0 : ℝ), (E.mixEnv h).F c = w₁ + (1 - w₁ - w₀) * E.F (g * c) := by
    have : ∀ᶠ c in 𝓝 (0 : ℝ), |c| < E.B + 1 := by
      have h1 : Continuous fun c : ℝ => |c| := continuous_abs
      exact h1.continuousAt.eventually (gt_mem_nhds (by simp; linarith))
    filter_upwards [this] with c hc
    exact E.mix_F h hc
  have h1 : HasDerivAt (fun c => g * c) g 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul g
  have ht' : HasDerivAt E.F t (g * 0) := by simpa using ht
  have h2 := (ht'.comp (0 : ℝ) h1).const_mul (1 - w₁ - w₀)
  have h3 := h2.const_add w₁
  exact h3.congr_of_eventuallyEq hnear

/-- **All the payoff results apply to the micro-founded game**, with `F` as the distribution of
`ν_i` among rational types.  Assumption 1 on `F` is not needed. -/
theorem micro_prop (h : MixPar w₁ w₀ g) (hFB : E.PiSQ < E.PiFB) :
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, E.microPi w₁ w₀ g n = E.PiSQ) ∧
    (HasDerivAt E.F 0 0 → Tendsto (E.microPi w₁ w₀ g) atTop (𝓝 E.PiSQ)) ∧
    (∀ t, HasDerivAt E.F t 0 → limsup (E.microPi w₁ w₀ g) atTop < E.PiFB) ∧
    (∀ α > 0, Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α) →
      Tendsto (E.microPi w₁ w₀ g) atTop (𝓝 E.PiFB)) := by
  have hg := h.g_pos
  have hB := E.B_nonneg
  have hw : 0 < 1 - w₁ - w₀ := by linarith [h.sum_lt]
  have hN := E.mix_noise h
  have hfun : E.microPi w₁ w₀ g = (E.mixEnv h).Pi := funext (microPi_eq E h)
  rw [hfun]
  -- the reinterpreted distribution near zero
  have hnear : ∀ᶠ c in 𝓝 (0 : ℝ), (E.mixEnv h).F c = w₁ + (1 - w₁ - w₀) * E.F (g * c) := by
    have : ∀ᶠ c in 𝓝 (0 : ℝ), |c| < E.B + 1 := by
      have h1 : Continuous fun c : ℝ => |c| := continuous_abs
      exact h1.continuousAt.eventually (gt_mem_nhds (by simp; linarith))
    filter_upwards [this] with c hc
    exact E.mix_F h hc
  have hderiv : ∀ t, HasDerivAt E.F t 0 → HasDerivAt (E.mixEnv h).F ((1 - w₁ - w₀) * (t * g)) 0 := by
    intro t ht
    have h1 : HasDerivAt (fun c => g * c) g 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul g
    have ht' : HasDerivAt E.F t (g * 0) := by simpa using ht
    have h2 := (ht'.comp (0 : ℝ) h1).const_mul (1 - w₁ - w₀)
    have h3 := h2.const_add w₁
    exact h3.congr_of_eventuallyEq hnear
  refine ⟨fun δ hδ hF => ?_, fun hF => ?_, fun t hF => ?_, fun α hα hF => ?_⟩
  · -- Statement 1
    set δ' := min (δ / g) ((E.B + 1) / 2) with hδ'
    have hδ'pos : 0 < δ' := lt_min (div_pos hδ hg) (by linarith)
    have h1 : |δ'| < E.B + 1 := by
      rw [abs_of_pos hδ'pos]
      linarith [min_le_right (δ / g) ((E.B + 1) / 2)]
    have h2 : |-δ'| < E.B + 1 := by rwa [abs_neg]
    have h3 : g * δ' ≤ δ := by
      have := min_le_left (δ / g) ((E.B + 1) / 2)
      rw [le_div_iff₀ hg] at this
      linarith
    have h4 : 0 < g * δ' := mul_pos hg hδ'pos
    have h5 : E.F (g * δ') ≤ E.F δ := E.F_mono h3
    have h6 : E.F (-δ) ≤ E.F (g * -δ') := E.F_mono (by nlinarith)
    have h7 : E.F (g * -δ') ≤ E.F (g * δ') := E.F_mono (by nlinarith)
    have hF' : (E.mixEnv h).F δ' - (E.mixEnv h).F (-δ') = 0 := by
      rw [E.mix_F h h1, E.mix_F h h2]
      have : E.F (g * δ') = E.F (g * -δ') := by linarith
      rw [this]
      ring
    exact prop_general_1 (E.mixEnv h) hN hδ'pos hF'
  · -- Statement 2
    have := hderiv 0 hF
    simp only [zero_mul, mul_zero] at this
    exact prop_general_2 (E.mixEnv h) hN hFB this
  · -- Statement 3
    exact prop_general_3 (E.mixEnv h) hN hFB (hderiv t hF)
  · -- Statement 4
    have hgt : Tendsto (fun δ : ℝ => g * δ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h1 : Tendsto (fun δ : ℝ => g * δ) (𝓝 0) (𝓝 (g * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact mul_pos hg hδ
    have h1 := (hF.comp hgt).const_mul (1 - w₁ - w₀)
    have hpos : 0 < (1 - w₁ - w₀) * α := mul_pos hw hα
    refine prop_general_4 (E.mixEnv h) hpos (h1.congr' ?_)
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < E.B + 1 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < E.B + 1 by linarith)] with δ hδ using hδ.2
    filter_upwards [self_mem_nhdsWithin, hev] with δ hδ hδ2
    have hδ0 : 0 < δ := hδ
    have h2 : |δ| < E.B + 1 := by rwa [abs_of_pos hδ0]
    have h3 : |-δ| < E.B + 1 := by rwa [abs_neg]
    rw [E.mix_F h h2, E.mix_F h h3]
    simp only [Function.comp, mul_neg]
    ring

end Env

end NoisyVD
