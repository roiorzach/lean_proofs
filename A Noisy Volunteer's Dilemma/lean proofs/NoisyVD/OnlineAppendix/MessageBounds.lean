import NoisyVD.OnlineAppendix.Messages

/-!
# Proposition `prop_general_message_upper_bounds`, for any game satisfying the domination condition

* `abs_W_sub_W0`: the second-moment comparison behind Statement 2.
* `sq_regret_le`: the inverse-moment comparison behind Statement 3.
* `prop_upper`: the three statements.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal

namespace NoisyVD

namespace OA

variable {A Ω X : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [MeasurableSpace X] [MeasurableSingletonClass X]

namespace MsgGame

variable {g : MsgGame A Ω X} {n : ℕ} {Λ : ℝ}

lemma B_eq : g.env.B = g.env.uMax - g.env.uMin := rfl

lemma maxU_le_uMax (ω : Ω) : g.env.maxU ω ≤ g.env.uMax := by
  obtain ⟨a, ha⟩ := g.env.exists_maxU ω
  rw [← ha]
  exact g.env.u_le_uMax a ω

/-- The regret `Z_ω(y) = max_a u^p(a,ω) - V_ω(y)`, with `0 ≤ Z_ω ≤ B`. -/
noncomputable def Rg (g : MsgGame A Ω X) (d : MRule A X n) (ω : Ω) (y : Fin n → X) : ℝ :=
  g.env.maxU ω - g.V d ω y

lemma Rg_mem (d : MRule A X n) (ω : Ω) (y : Fin n → X) : g.Rg d ω y ∈ Icc 0 g.env.B := by
  unfold Rg
  have h1 := V_le_maxU (g := g) d ω y
  have h2 := (V_mem (g := g) d ω y).1
  have h3 := maxU_le_uMax (g := g) ω
  rw [B_eq]
  constructor <;> linarith

lemma measurable_Rg (d : MRule A X n) (ω : Ω) : Measurable (g.Rg d ω) :=
  measurable_const.sub (measurable_V d ω)

lemma integral_Rg (d : MRule A X n) (ω : Ω) (μ : Measure (Fin n → X)) [IsProbabilityMeasure μ] :
    ∫ y, g.Rg d ω y ∂μ = g.env.maxU ω - ∫ y, g.V d ω y ∂μ := by
  unfold Rg
  have hb : BM (g.V d ω) := BM.of_mem (measurable_V d ω) (V_mem d ω)
  rw [(BM.const _).integral_sub hb]
  simp

/-- The second-moment comparison. -/
theorem abs_W_sub_W0 (hΛ : g.Dom Λ) (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω) {c : ℝ}
    (hc : (1 - g.ε) * Λ * g.q σ ω ≤ c) (hc1 : c ≤ 1) :
    |g.W d σ ω - g.W0 d ω| ≤ g.env.B * √(exp ((n : ℝ) * c ^ 2) - 1) := by
  obtain ⟨r, hr⟩ := tilt hΛ σ ω hc hc1
  have h := hr.abs_sub_le (measurable_Rg d ω) (Rg_mem (g := g) d ω)
  rw [integral_Rg, integral_Rg] at h
  have e : g.W d σ ω - g.W0 d ω
      = -((g.env.maxU ω - ∫ y, g.V d ω y ∂(Measure.pi fun _ : Fin n => g.obs σ ω))
        - (g.env.maxU ω - ∫ y, g.V d ω y ∂(Measure.pi fun _ : Fin n => g.baseObs))) := by
    simp only [W, W0]
    ring
  rw [e, abs_neg]
  exact h

/-- The inverse-moment comparison: `(R⁰)² ≤ B e^{2 n c²} R`. -/
theorem sq_regret_le (hΛ : g.Dom Λ) (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω) {c : ℝ}
    (hc : (1 - g.ε) * Λ * g.q σ ω ≤ c) (hc1 : c ≤ 1 / 2) :
    (g.env.maxU ω - g.W0 d ω) ^ 2
      ≤ g.env.B * exp (2 * (n : ℝ) * c ^ 2) * (g.env.maxU ω - g.W d σ ω) := by
  obtain ⟨r, hr⟩ := tilt hΛ σ ω hc (by linarith)
  have h := hr.sq_le hc1 (measurable_Rg d ω) (Rg_mem (g := g) d ω)
  rw [integral_Rg, integral_Rg] at h
  exact h

lemma bm_W0 (d : MRule A X n) : BM (g.W0 d) := BM.of_mem (measurable_W0 d) (W0_mem d)

lemma bm_maxU : BM g.env.maxU := by
  refine ⟨g.env.continuous_maxU.measurable, max |g.env.uMax| |g.env.uMin|, g.env.abs_maxU_le⟩

/-- The payoff is at most `Π^SQ + B √(e^{n c²} - 1)`. -/
theorem payoff_le_sq (hΛ : g.Dom Λ) (d : MRule A X n) (σ : MStrat Ω X) {c : ℝ}
    (hc : ∀ ω, (1 - g.ε) * Λ * g.q σ ω ≤ c) (hc1 : c ≤ 1) :
    g.payoff d σ ≤ g.env.PiSQ + g.env.B * √(exp ((n : ℝ) * c ^ 2) - 1) := by
  set e := g.env.B * √(exp ((n : ℝ) * c ^ 2) - 1) with he
  have h1 : g.payoff d σ ≤ ∫ ω, (g.W0 d ω + e) ∂(g.env.prior : Measure Ω) := by
    refine integral_mono ((bm_W d σ).integrable _) (((bm_W0 d).add (BM.const e)).integrable _) fun ω => ?_
    have := (abs_le.1 (abs_W_sub_W0 hΛ d σ ω (hc ω) hc1)).2
    simp only
    linarith
  rw [(bm_W0 d).integral_add (BM.const e)] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  have h2 := integral_W0_le (g := g) d
  linarith

/-- The payoff is at most `Π^FB - e^{-2 n c²} Δ² / B`, with `Δ = Π^FB - Π^SQ`. -/
theorem payoff_le_fb (hΛ : g.Dom Λ) (d : MRule A X n) (σ : MStrat Ω X) {c : ℝ}
    (hc : ∀ ω, (1 - g.ε) * Λ * g.q σ ω ≤ c) (hc1 : c ≤ 1 / 2) :
    (g.env.PiFB - g.env.PiSQ) ^ 2
      ≤ g.env.B * exp (2 * (n : ℝ) * c ^ 2) * (g.env.PiFB - g.payoff d σ) := by
  set Δ := g.env.PiFB - g.env.PiSQ with hΔ
  have hΔ0 : 0 ≤ Δ := by
    have := g.env.PiSQ_le_PiFB
    rw [hΔ]
    linarith
  let f : Ω → ℝ := fun ω => g.env.maxU ω - g.W0 d ω
  have hf : BM f := bm_maxU.sub (bm_W0 d)
  have hint : ∫ ω, f ω ∂(g.env.prior : Measure Ω) = g.env.PiFB - ∫ ω, g.W0 d ω ∂(g.env.prior : Measure Ω) := by
    simp only [f]
    rw [bm_maxU.integral_sub (bm_W0 d)]
    rfl
  have hΔle : Δ ≤ ∫ ω, f ω ∂(g.env.prior : Measure Ω) := by
    rw [hint, hΔ]
    linarith [integral_W0_le (g := g) d]
  -- Jensen
  have hJ : (∫ ω, f ω ∂(g.env.prior : Measure Ω)) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂(g.env.prior : Measure Ω) := by
    have h := sq_integral_mul_le (μ := (g.env.prior : Measure Ω)) hf (BM.const (1 : ℝ))
    simpa using h
  have hB0 : 0 ≤ g.env.B := g.env.B_nonneg
  set E := g.env.B * exp (2 * (n : ℝ) * c ^ 2) with hE
  have hreg : ∫ ω, f ω ^ 2 ∂(g.env.prior : Measure Ω)
      ≤ ∫ ω, E * (g.env.maxU ω - g.W d σ ω) ∂(g.env.prior : Measure Ω) :=
    integral_mono ((hf.pow 2).integrable _) (((BM.const E).mul (bm_maxU.sub (bm_W d σ))).integrable _)
      fun ω => sq_regret_le hΛ d σ ω (hc ω) hc1
  rw [integral_const_mul, bm_maxU.integral_sub (bm_W d σ)] at hreg
  have hsq : Δ ^ 2 ≤ (∫ ω, f ω ∂(g.env.prior : Measure Ω)) ^ 2 := pow_le_pow_left₀ hΔ0 hΔle 2
  calc Δ ^ 2 ≤ _ := hsq
    _ ≤ _ := hJ
    _ ≤ _ := hreg
    _ = _ := rfl

/-! ### The status quo -/

lemma isProb_update (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (i : Fin n) (j : Fin n) :
    IsProbabilityMeasure (Function.update (fun _ : Fin n => P) i Q j) := by
  by_cases h : j = i
  · rw [h, Function.update_self]
    infer_instance
  · rw [Function.update_of_ne h]
    infer_instance

/-- The constant rule. -/
noncomputable def constMRule (a : A) (n : ℕ) : MRule A X n where
  κ := Kernel.const _ (Measure.dirac a)
  markov := inferInstance
  symm := fun _ _ => rfl

/-- All rational individuals send `∅`. -/
noncomputable def silent (g : MsgGame A Ω X) : MStrat Ω X where
  κ := Kernel.const _ (Measure.dirac g.nullMsg)
  markov := inferInstance

lemma V_const (a : A) (ω : Ω) (y : Fin n → X) : g.V (constMRule a n) ω y = g.env.u a ω := by
  simp [V, constMRule]

lemma ae_cost_nonneg : ∀ᵐ x ∂(g.env.cost : Measure ℝ), 0 ≤ x := by
  rw [ae_iff]
  have : {x : ℝ | ¬0 ≤ x} = Iio 0 := by
    ext x
    simp
  rw [this]
  exact g.cost_nonneg

lemma msgCost_nonneg {x : ℝ} (hx : 0 ≤ x) (m : X) : 0 ≤ g.msgCost m x := by
  unfold msgCost
  split_ifs
  · exact le_rfl
  · exact hx

lemma isEq_const (a : A) : g.IsEq (constMRule a n) g.silent := by
  intro ω
  filter_upwards [ae_cost_nonneg (g := g)] with x hx
  have hU : ∀ (i : Fin n) (m : X), g.U (constMRule a n) g.silent ω i m = g.env.u a ω := by
    intro i m
    have := isProb_update (g.obs g.silent ω) (g.record m) i
    unfold U
    simp only [V_const, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hk : g.silent.κ (ω, x) = Measure.dirac g.nullMsg := rfl
  rw [hk, ae_dirac_eq]
  refine Filter.eventually_pure.2 fun i m' => ?_
  simp only [netU, hU]
  have h1 := msgCost_nonneg (g := g) hx m'
  have h2 : g.msgCost g.nullMsg x = 0 := by simp [msgCost]
  linarith

lemma payoff_const (a : A) : g.payoff (constMRule a n) g.silent = ∫ ω, g.env.u a ω ∂(g.env.prior : Measure Ω) := by
  unfold payoff W
  simp only [V_const, integral_const, probReal_univ, smul_eq_mul, one_mul]

lemma PiSQ_mem (n : ℕ) : g.env.PiSQ ∈ g.payoffs n := by
  obtain ⟨a, ha⟩ := g.env.exists_statusQuo
  exact ⟨constMRule a n, g.silent, isEq_const a, by rw [payoff_const, ha]⟩

lemma le_PiFB (n : ℕ) : ∀ y ∈ g.payoffs n, y ≤ g.env.PiFB := by
  rintro y ⟨d, σ, _, rfl⟩
  exact payoff_le_PiFB d σ

lemma PiSQ_le_Pi (n : ℕ) : g.env.PiSQ ≤ g.Pi n := le_csSup ⟨_, le_PiFB n⟩ (PiSQ_mem n)

lemma Pi_le_PiFB (n : ℕ) : g.Pi n ≤ g.env.PiFB := csSup_le ⟨_, PiSQ_mem n⟩ (le_PiFB n)

lemma PiFB_sub_PiSQ_le : g.env.PiFB - g.env.PiSQ ≤ g.env.B := by
  obtain ⟨a, ha⟩ := g.env.exists_statusQuo
  have h1 : g.env.PiFB ≤ g.env.uMax := by
    have := integral_mono (μ := (g.env.prior : Measure Ω)) g.env.integrable_maxU
      (integrable_const g.env.uMax) (maxU_le_uMax (g := g))
    simpa [Env.PiFB] using this
  have h2 : g.env.uMin ≤ g.env.PiSQ := by
    rw [← ha]
    have := integral_mono (μ := (g.env.prior : Measure Ω)) (integrable_const g.env.uMin)
      (g.env.integrable_u_right a) (fun ω => g.env.uMin_le_u a ω)
    simpa using this
  rw [B_eq]
  linarith

/-! ### The three statements -/

/-- `√n F(M/√n) → M F'₊(0)` when `F(0) = 0`. -/
lemma tendsto_sqrt_mul_F {F : ℝ → ℝ} {t M : ℝ} (hF0 : F 0 = 0) (hF : HasDerivWithinAt F t (Ici 0) 0)
    (hM : 0 < M) : Tendsto (fun n : ℕ => √(n : ℝ) * F (M / √(n : ℝ))) atTop (𝓝 (M * t)) := by
  have hslope : Tendsto (slope F 0) (𝓝[>] 0) (𝓝 t) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).1 hF.Ioi_of_Ici
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => M / √(n : ℝ)) atTop (𝓝 0) := Tendsto.const_div_atTop hsq M
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < M / √(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos hM (Real.sqrt_pos.2 this)
  have h1 : Tendsto (fun n : ℕ => M / √(n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hh, hpos.mono fun n hn => hn⟩
  have h2 := (hslope.comp h1).const_mul M
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
  simp only [Function.comp, slope_def_field, hF0, sub_zero]
  field_simp

section Statements

variable (hΛ : g.Dom Λ)

include hΛ

lemma one_sub_eps_mul_nonneg : 0 ≤ (1 - g.ε) * Λ :=
  mul_nonneg (by linarith [g.ε_lt]) hΛ.nonneg

/-- If `q_{n,ω} = 0`, the law of an observed message is `P⁰`, which does not depend on the state. -/
lemma obs_eq_base (σ : MStrat Ω X) (ω : Ω) (hq : g.q σ ω = 0) : g.obs σ ω = g.baseObs := by
  refine Measure.ext fun S hS => ?_
  have h := abs_obs_sub_le hΛ σ ω hS
  rw [hq] at h
  simp only [mul_zero, zero_mul] at h
  have h2 : (g.obs σ ω).real S = g.baseObs.real S := sub_eq_zero.1 (abs_nonpos_iff.1 h)
  rw [measureReal_def, measureReal_def] at h2
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h2

/-- **Statement 1.**  Once `M_G/√n < δ`, `q_{n,ω} = 0` in every state and every symmetric equilibrium.  The
observation profile is therefore independent of the state, so every decision rule yields at most `Π^SQ`. -/
theorem statement1 {δ : ℝ} (hδ : 0 < δ) (hF : g.env.F δ = 0) :
    ∃ nStar : ℕ, ∀ n > nStar, g.Pi n = g.env.PiSQ := by
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => g.hG Λ n) atTop (𝓝 0) :=
    Tendsto.const_div_atTop hsq _
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 δ hδ)
  refine ⟨max N 1, fun n hn => le_antisymm ?_ (PiSQ_le_Pi n)⟩
  have hn1 : 0 < n := by
    have := le_max_right N 1
    omega
  have hnN : N ≤ n := by
    have := le_max_left N 1
    omega
  refine csSup_le ⟨_, PiSQ_mem n⟩ ?_
  rintro y ⟨d, σ, he, rfl⟩
  have hq : ∀ ω, g.q σ ω = 0 := fun ω => by
    have h1 := q_le hΛ hn1 he ω
    have h2 : g.env.F (g.hG Λ n) ≤ g.env.F δ := g.env.F_mono (hN n hnN).le
    rw [hF] at h2
    exact le_antisymm (h1.trans h2) (q_nonneg σ ω)
  have hW : ∀ ω, g.W d σ ω = g.W0 d ω := fun ω => by
    unfold MsgGame.W MsgGame.W0
    rw [obs_eq_base hΛ σ ω (hq ω)]
  have hint : g.payoff d σ = ∫ ω, g.W0 d ω ∂(g.env.prior : Measure Ω) :=
    integral_congr_ae (ae_of_all _ hW)
  rw [hint]
  exact integral_W0_le d

/-- For large `n`, the band for `q` is `F(M'/√n)`, with `M' = M_G + 1 > 0`. -/
lemma q_le_c {n : ℕ} (hn : 0 < n) {d : MRule A X n} {σ : MStrat Ω X} (he : g.IsEq d σ) (ω : Ω) :
    (1 - g.ε) * Λ * g.q σ ω
      ≤ (1 - g.ε) * Λ * g.env.F ((g.env.B * √(Λ - 1) + 1) / √(n : ℝ)) := by
  refine mul_le_mul_of_nonneg_left ((q_le hΛ hn he ω).trans (g.env.F_mono ?_))
    (one_sub_eps_mul_nonneg hΛ)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
  exact div_le_div_of_nonneg_right (by linarith) hs.le

/-- **Statement 2.** -/
theorem statement2 (hF0 : g.env.F 0 = 0) (hF : HasDerivWithinAt g.env.F 0 (Ici 0) 0) :
    Tendsto g.Pi atTop (𝓝 g.env.PiSQ) := by
  have hB := g.env.B_nonneg
  set M' := g.env.B * √(Λ - 1) + 1 with hM'
  have hM : 0 < M' := by rw [hM']; positivity
  have ha := tendsto_sqrt_mul_F hF0 hF hM
  rw [mul_zero] at ha
  set C := (1 - g.ε) * Λ with hC
  have hC0 : 0 ≤ C := one_sub_eps_mul_nonneg hΛ
  let a : ℕ → ℝ := fun n => √(n : ℝ) * g.env.F (M' / √(n : ℝ))
  let c : ℕ → ℝ := fun n => C * g.env.F (M' / √(n : ℝ))
  -- `n c² → 0`
  have hnc : Tendsto (fun n : ℕ => (n : ℝ) * c n ^ 2) atTop (𝓝 0) := by
    have h1 := ((ha.pow 2).const_mul (C ^ 2))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h1
    refine h1.congr fun n => ?_
    simp only [c]
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun n : ℕ => M' / √(n : ℝ)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨Tendsto.const_div_atTop hsq M', ?_⟩
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact div_pos hM (Real.sqrt_pos.2 this)
    have hcont : Tendsto g.env.F (𝓝[>] 0) (𝓝 (g.env.F 0)) := by
      have := hF.continuousWithinAt.tendsto
      exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h2 := (hcont.comp h1).const_mul C
    rw [hF0, mul_zero] at h2
    exact h2
  have hlim : Tendsto (fun n : ℕ => g.env.PiSQ + g.env.B * √(exp ((n : ℝ) * c n ^ 2) - 1)) atTop
      (𝓝 g.env.PiSQ) := by
    have h1 : Tendsto (fun n : ℕ => exp ((n : ℝ) * c n ^ 2) - 1) atTop (𝓝 0) := by
      have := (Real.continuous_exp.continuousAt.tendsto.comp hnc).sub_const 1
      simpa using this
    have h2 := (h1.sqrt.const_mul g.env.B).const_add g.env.PiSQ
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall PiSQ_le_Pi) ?_
  filter_upwards [(tendsto_order.1 hc0).2 1 one_pos, eventually_ge_atTop 1] with n hn hn1
  refine csSup_le ⟨_, PiSQ_mem n⟩ ?_
  rintro y ⟨d, σ, he, rfl⟩
  exact payoff_le_sq hΛ d σ (fun ω => q_le_c hΛ (by omega) he ω) hn.le

/-- **Statement 3.** -/
theorem statement3 (hFB : g.env.PiSQ < g.env.PiFB) {t : ℝ} (hF0 : g.env.F 0 = 0)
    (hF : HasDerivWithinAt g.env.F t (Ici 0) 0) : limsup g.Pi atTop < g.env.PiFB := by
  have hB := g.env.B_nonneg
  set M' := g.env.B * √(Λ - 1) + 1 with hM'
  have hM : 0 < M' := by rw [hM']; positivity
  have ha := tendsto_sqrt_mul_F hF0 hF hM
  set C := (1 - g.ε) * Λ with hC
  have hC0 : 0 ≤ C := one_sub_eps_mul_nonneg hΛ
  let c : ℕ → ℝ := fun n => C * g.env.F (M' / √(n : ℝ))
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun n : ℕ => M' / √(n : ℝ)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨Tendsto.const_div_atTop hsq M', ?_⟩
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact div_pos hM (Real.sqrt_pos.2 this)
    have hcont : Tendsto g.env.F (𝓝[>] 0) (𝓝 (g.env.F 0)) := by
      have := hF.continuousWithinAt.tendsto
      exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h2 := (hcont.comp h1).const_mul C
    rw [hF0, mul_zero] at h2
    exact h2
  set K := C ^ 2 * (M' * t + 1) ^ 2 with hK
  set Δ := g.env.PiFB - g.env.PiSQ with hΔ
  have hΔ0 : 0 < Δ := by rw [hΔ]; linarith
  have hBpos : 0 < g.env.B := lt_of_lt_of_le hΔ0 PiFB_sub_PiSQ_le
  set κ := Δ ^ 2 / (g.env.B * exp (2 * K)) with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hev : ∀ᶠ n in atTop, g.Pi n ≤ g.env.PiFB - κ := by
    filter_upwards [(tendsto_order.1 hc0).2 (1 / 2) (by norm_num),
      (tendsto_order.1 ha).2 (M' * t + 1) (by linarith), eventually_ge_atTop 1] with n hn hna hn1
    refine csSup_le ⟨_, PiSQ_mem n⟩ ?_
    rintro y ⟨d, σ, he, rfl⟩
    have h1 := payoff_le_fb hΛ d σ (fun ω => q_le_c hΛ (by omega) he ω) hn.le
    have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    -- `n c² ≤ K`
    have hnK : (n : ℝ) * c n ^ 2 ≤ K := by
      have ha0 : 0 ≤ √(n : ℝ) * g.env.F (M' / √(n : ℝ)) :=
        mul_nonneg (Real.sqrt_nonneg _) (g.env.F_nonneg _)
      have hsq := pow_le_pow_left₀ ha0 hna.le 2
      rw [mul_pow, Real.sq_sqrt hnr] at hsq
      have e : (n : ℝ) * c n ^ 2 = C ^ 2 * ((n : ℝ) * g.env.F (M' / √(n : ℝ)) ^ 2) := by
        simp only [c]
        ring
      rw [e, hK]
      exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    have hexp : exp (2 * (n : ℝ) * c n ^ 2) ≤ exp (2 * K) := by
      apply Real.exp_le_exp.2
      linarith
    have hfb := payoff_le_PiFB (g := g) d σ
    have h2 : Δ ^ 2 ≤ g.env.B * exp (2 * K) * (g.env.PiFB - g.payoff d σ) := by
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
      exact mul_le_mul_of_nonneg_left hexp hB
    have hEpos : 0 < g.env.B * exp (2 * K) := by positivity
    have h3 : κ ≤ g.env.PiFB - g.payoff d σ := by
      rw [hκ, div_le_iff₀ hEpos]
      linarith
    linarith
  have h1 : limsup g.Pi atTop ≤ g.env.PiFB - κ := by
    refine limsup_le_of_le ?_ hev
    exact (isBoundedUnder_of (f := atTop) (u := g.Pi) (r := (· ≥ ·))
      ⟨g.env.PiSQ, PiSQ_le_Pi⟩).isCoboundedUnder_flip
  linarith

/-- **Proposition `prop_general_message_upper_bounds`** for a game with the domination condition. -/
theorem prop_upper (hFB : g.env.PiSQ < g.env.PiFB) :
    (∀ δ > 0, g.env.F δ = 0 → ∃ nStar : ℕ, ∀ n > nStar, g.Pi n = g.env.PiSQ) ∧
    (g.env.F 0 = 0 → HasDerivWithinAt g.env.F 0 (Ici 0) 0 → Tendsto g.Pi atTop (𝓝 g.env.PiSQ)) ∧
    (∀ t > 0, g.env.F 0 = 0 → HasDerivWithinAt g.env.F t (Ici 0) 0 → limsup g.Pi atTop < g.env.PiFB) :=
  ⟨fun _ hδ hF => statement1 hΛ hδ hF, fun h0 hF => statement2 hΛ h0 hF,
    fun _ _ h0 hF => statement3 hΛ hFB h0 hF⟩

end Statements

end MsgGame

end OA

end NoisyVD
