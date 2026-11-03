import NoisyVD.OnlineAppendix.Remarks
import NoisyVD.OnlineAppendix.StateDependent
import NoisyVD.OnlineAppendix.WorstCase
import NoisyVD.OnlineAppendix.NoisySignals
import NoisyVD.Example
import NoisyVD.Game

/-!
# Fidelity checks

Machine-checked evidence that the definitions mean what the Online Appendix says and that the hypotheses
are satisfiable.

* `SDEnv.isEq_iff_bestResponse`, `SDEnv.payoff_eq_profile`, `Signal.isEq_iff_bestResponse`,
  `Signal.payoff_eq_profile`: as `NoisyVD/Game.lean` does for the main model, equilibrium and payoffs are
  derived from expected utilities over report profiles.
* `Signal.integral_interim`: the interim gross benefit is the conditional expectation of `Δ_{n,ω}`
  given the signal.
* `NoisyModel.baseObs_null`, `NoisyModel.obs_null`: `P⁰(∅) = 1 - ε(1-η)` and
  `P_ω(∅) = P⁰(∅) - (1-ε) q_{n,ω}`, the value at `∅` of the identity for `P_ω - P⁰` in the proof of
  Proposition `prop_general_message_upper_bounds`.
* `Examples`: concrete environments satisfying the hypotheses; the truncated-normal recording error named
  in the paper; and a single set of primitives for which noisy recording gives `Π^M(n) = Π^SQ` for large
  `n` while perfect recording gives `Π^M(n) ≥ Π^SQ + κ`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal

namespace NoisyVD

namespace OA

local notation "I" => unitInterval

/-! ### From the game to the reduced form: state-dependent costs -/

namespace SDEnv

variable {E : SDEnv}

/-- **`IsEq` is symmetric Bayesian Nash equilibrium** with state-dependent costs: in every state, every
type's report probability maximises expected utility against i.i.d. reports of the others. -/
theorem isEq_iff_bestResponse {n : ℕ} (d : Rule Bool) (s : Strat Bool) :
    E.IsEq n d s ↔ ∀ ω x, ∀ τ ∈ Icc (0 : ℝ) 1,
      τ * indivU (m := n - 1) (E.rp s ω) (fun k => E.base.v d k ω) x 1
          + (1 - τ) * indivU (m := n - 1) (E.rp s ω) (fun k => E.base.v d k ω) x 0
        ≤ s.σ ω x * indivU (m := n - 1) (E.rp s ω) (fun k => E.base.v d k ω) x 1
          + (1 - s.σ ω x) * indivU (m := n - 1) (E.rp s ω) (fun k => E.base.v d k ω) x 0 := by
  have hgain : ∀ ω x, indivU (m := n - 1) (E.rp s ω) (fun k => E.base.v d k ω) x 1
      - indivU (m := n - 1) (E.rp s ω) (fun k => E.base.v d k ω) x 0
        = E.base.gross n d (E.rp s ω) ω - x := fun ω x => indivU_gain _ _ _
  constructor
  · intro he ω x τ hτ
    refine (bestResponse_iff (s.mem ω x)).2 ⟨fun h => ?_, fun h => ?_⟩ τ hτ
    · exact (he ω x).1 (by have := hgain ω x; linarith)
    · exact (he ω x).2 (by have := hgain ω x; linarith)
  · intro h ω x
    have h2 := (bestResponse_iff (s.mem ω x)).1 (h ω x)
    exact ⟨fun hx => h2.1 (by have := hgain ω x; linarith),
      fun hx => h2.2 (by have := hgain ω x; linarith)⟩

/-- The decision-maker's payoff is the expectation of `u^p` over report profiles. -/
theorem payoff_eq_profile (n : ℕ) (d : Rule Bool) (s : Strat Bool) :
    E.payoff n d s = ∫ ω, ∑ S : Finset (Fin n), profileProb (E.rp s ω) S * E.base.v d S.card ω
      ∂(E.prior : Measure Bool) :=
  integral_congr_ae (Eventually.of_forall fun ω => (sum_profile (E.rp s ω) _).symm)

end SDEnv

/-! ### The interim gross benefit is a conditional expectation -/

namespace Signal

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  {E : Env A Ω} {G : Kernel Ω ℝ} [IsMarkovKernel G]

/-- `∫_A Δ_n(s) dP(s) = ∫_Ω G(A ∣ ω) Δ_{n,ω} dπ(ω)` for every measurable set of signals `A`. -/
theorem integral_interim (n : ℕ) (d : Rule A) (s : Strat ℝ) {T : Set ℝ} (hT : MeasurableSet T) :
    ∫ y in T, interim E G n d s y ∂(marg E G)
      = ∫ ω, (G ω).real T * E.gross n d (stateRp E G s ω) ω ∂(E.prior : Measure Ω) := by
  have := E.nonempty_state
  let h : Ω → ℝ := fun ω => E.gross n d (stateRp E G s ω) ω
  have hm : Measurable h := (E.continuous_gross n d).measurable.comp
    (measurable_id.prodMk (measurable_stateRp s))
  have hb : ∀ ω, |h ω| ≤ E.B := fun ω =>
    E.abs_gross_le n d (stateRp_mem s ω).1 (stateRp_mem s ω).2 ω
  have hbm : BM h := ⟨hm, E.B, hb⟩
  let f : ℝ × Ω → ℝ := fun z => T.indicator (fun _ => (1 : ℝ)) z.1 * h z.2
  have hfm : Measurable f :=
    ((measurable_const.indicator hT).comp measurable_fst).mul (hm.comp measurable_snd)
  have hfb : BM f := by
    refine ⟨hfm, |E.B|, fun z => ?_⟩
    simp only [f]
    by_cases hz : z.1 ∈ T
    · simp only [indicator_of_mem hz, one_mul]
      exact (hb _).trans (le_abs_self _)
    · simp only [indicator_of_notMem hz, zero_mul, abs_zero]
      exact abs_nonneg _
  have hswap := compProd_posterior_eq_map_swap (κ := G) (μ := (E.prior : Measure Ω))
  have hL : ∫ z, f z ∂((marg E G) ⊗ₘ post E G) = ∫ y in T, interim E G n d s y ∂(marg E G) := by
    rw [Measure.integral_compProd (hfb.integrable _), ← integral_indicator hT]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ T
    · simp [f, hy, interim, h]
    · simp [f, hy]
  have hR : ∫ z, f z ∂((marg E G) ⊗ₘ post E G)
      = ∫ ω, (G ω).real T * h ω ∂(E.prior : Measure Ω) := by
    have heq : (marg E G) ⊗ₘ post E G = ((E.prior : Measure Ω) ⊗ₘ G).map Prod.swap := hswap
    rw [heq, integral_map measurable_swap.aemeasurable hfm.aestronglyMeasurable]
    have hfb' : BM fun z : Ω × ℝ => f z.swap := ⟨hfm.comp measurable_swap, by
      obtain ⟨C, hC⟩ := hfb.2
      exact ⟨C, fun z => hC _⟩⟩
    rw [Measure.integral_compProd (hfb'.integrable _)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [f, Prod.fst_swap, Prod.snd_swap]
    rw [integral_mul_const, integral_indicator_const _ hT]
    simp
  rw [← hL, hR]

/-! ### From the game to the reduced form: signals -/

/-- The expected utility of report `r` for type `x` after signal `y`: the state is drawn from the
posterior, and the other `n-1` individuals report i.i.d. with probability `p_{n,ω}`. -/
noncomputable def eu (E : Env A Ω) (G : Kernel Ω ℝ) [IsMarkovKernel G] (n : ℕ) (d : Rule A) (s : Strat ℝ)
    (y x : ℝ) (r : ℕ) : ℝ :=
  ∫ ω, indivU (m := n - 1) (stateRp E G s ω) (fun k => E.v d k ω) x r ∂(post E G y)

lemma bm_indivU (n : ℕ) (d : Rule A) (s : Strat ℝ) (x : ℝ) (r : ℕ) :
    BM fun ω => indivU (m := n - 1) (stateRp E G s ω) (fun k => E.v d k ω) x r := by
  unfold indivU
  refine BM.sub (BM.sum _ fun S _ => ?_) (BM.const _)
  have hq : Measurable (stateRp E G s) := measurable_stateRp s
  have hpr : BM fun ω => profileProb (stateRp E G s ω) S := by
    unfold profileProb
    refine BM.of_mem (a := 0) (b := 1) ?_ fun ω => ?_
    · refine Finset.measurable_prod _ fun i _ => ?_
      by_cases hi : i ∈ S
      · simpa [hi] using hq
      · have h : Measurable fun ω => 1 - stateRp E G s ω := measurable_const.sub hq
        simpa [hi] using h
    · have hmem : ∀ i : Fin (n - 1), (if i ∈ S then stateRp E G s ω else 1 - stateRp E G s ω)
          ∈ Icc (0 : ℝ) 1 := fun i => by
        have h := stateRp_mem (E := E) (G := G) s ω
        split_ifs
        · exact h
        · constructor <;> linarith [h.1, h.2]
      exact ⟨Finset.prod_nonneg fun i _ => (hmem i).1, Finset.prod_le_one₀ (fun i _ => (hmem i).1)
        fun i _ => (hmem i).2⟩
  have hv : BM fun ω => E.v d (S.card + r) ω :=
    ⟨(E.continuous_v d _).measurable, _, E.abs_v_le d _⟩
  exact hpr.mul hv

/-- The interim gain from reporting is the gross benefit minus the cost. -/
theorem eu_gain (n : ℕ) (d : Rule A) (s : Strat ℝ) (y x : ℝ) :
    eu E G n d s y x 1 - eu E G n d s y x 0 = interim E G n d s y - x := by
  unfold eu
  rw [← (bm_indivU n d s x 1).integral_sub (bm_indivU n d s x 0)]
  simp_rw [indivU_gain]
  have hg : BM fun ω => E.gross n d (stateRp E G s ω) ω - x := by
    refine BM.sub ⟨(E.continuous_gross n d).measurable.comp
      (measurable_id.prodMk (measurable_stateRp s)), E.B, fun ω => ?_⟩ (BM.const x)
    exact E.abs_gross_le n d (stateRp_mem s ω).1 (stateRp_mem s ω).2 ω
  have hg' : BM fun ω => E.gross n d (stateRp E G s ω) ω := by
    refine ⟨(E.continuous_gross n d).measurable.comp
      (measurable_id.prodMk (measurable_stateRp s)), E.B, fun ω => ?_⟩
    exact E.abs_gross_le n d (stateRp_mem s ω).1 (stateRp_mem s ω).2 ω
  show ∫ ω, (E.gross n d (stateRp E G s ω) ω - x) ∂(post E G y) = _
  rw [hg'.integral_sub (BM.const x)]
  simp [interim]

/-- **`Signal.IsEq` is symmetric Bayesian Nash equilibrium**: after almost every signal, every type's
report probability maximises interim expected utility. -/
theorem isEq_iff_bestResponse {n : ℕ} (d : Rule A) (s : Strat ℝ) :
    IsEq E G n d s ↔ ∀ᵐ y ∂(marg E G), ∀ x, ∀ τ ∈ Icc (0 : ℝ) 1,
      τ * eu E G n d s y x 1 + (1 - τ) * eu E G n d s y x 0
        ≤ s.σ y x * eu E G n d s y x 1 + (1 - s.σ y x) * eu E G n d s y x 0 := by
  refine eventually_congr (Eventually.of_forall fun y => ?_)
  have hgain := eu_gain (E := E) (G := G) n d s y
  constructor
  · intro he x τ hτ
    refine (bestResponse_iff (s.mem y x)).2 ⟨fun h => ?_, fun h => ?_⟩ τ hτ
    · exact (he x).1 (by have := hgain x; linarith)
    · exact (he x).2 (by have := hgain x; linarith)
  · intro h x
    have h2 := (bestResponse_iff (s.mem y x)).1 (h x)
    exact ⟨fun hx => h2.1 (by have := hgain x; linarith),
      fun hx => h2.2 (by have := hgain x; linarith)⟩

/-- The decision-maker's payoff is the expectation of `u^p` over report profiles: conditional on `ω`,
reports are i.i.d. with probability `p_{n,ω}`. -/
theorem payoff_eq_profile (n : ℕ) (d : Rule A) (s : Strat ℝ) :
    payoff E G n d s = ∫ ω, ∑ S : Finset (Fin n), profileProb (stateRp E G s ω) S * E.v d S.card ω
      ∂(E.prior : Measure Ω) :=
  integral_congr_ae (Eventually.of_forall fun ω => (sum_profile (stateRp E G s ω) _).symm)

end Signal

/-! ### The law of the observed message -/

namespace NoisyModel

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  (N : NoisyModel A Ω)

lemma record_null_null : (N.D.recordK msgNull).real {msgNull} = 1 := by
  rw [N.D.recordK_null]
  simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]

lemma record_inr_null (t : I) : (N.D.recordK (Sum.inr t)).real {msgNull} = 0 := by
  rw [N.D.recordK_inr, measureReal_def, Measure.map_apply measurable_inr (measurableSet_singleton _)]
  have : (Sum.inr ⁻¹' {msgNull} : Set I) = ∅ := by
    ext x
    simp
  simp [this]

lemma noise_null : N.game.noiseObs.real {msgNull} = N.η := by
  have hBM : BM fun z => (N.D.recordK z).real {msgNull} := by
    refine BM.of_mem ?_ fun z => ⟨measureReal_nonneg, measureReal_le_one⟩
    simp only [measureReal_def]
    exact (N.D.recordK.measurable_coe (measurableSet_singleton _)).ennreal_toReal
  show ((N.D.recordK) ∘ₘ (mechMsg N.η)).real {msgNull} = N.η
  have : IsProbabilityMeasure (mechMsg N.η) := isProb_mix N.η_pos.le N.η_lt.le _ _
  rw [real_bind _ (measurableSet_singleton _), N.integral_mech hBM, N.record_null_null]
  simp [N.record_inr_null]

/-- `P⁰(∅) = 1 - ε(1-η)`. -/
theorem baseObs_null : N.game.baseObs.real {msgNull} = 1 - N.ε * (1 - N.η) := by
  have h : N.game.baseObs = mix N.ε N.game.noiseObs (N.D.recordK msgNull) := rfl
  rw [h, mix_real N.ε_pos.le N.ε_lt.le, N.noise_null, N.record_null_null]
  ring

/-- `P_ω(∅) = P⁰(∅) - (1-ε) q_{n,ω}`. -/
theorem obs_null (σ : MStrat Ω Msg) (ω : Ω) :
    (N.game.obs σ ω).real {msgNull} = 1 - N.ε * (1 - N.η) - (1 - N.ε) * N.game.q σ ω := by
  have h : N.game.obs σ ω = mix N.ε N.game.noiseObs (N.game.ratObs σ ω) := rfl
  have hq : (N.game.ratObs σ ω).real {msgNull} = 1 - N.game.q σ ω := by
    have hnull : N.game.nullMsg = msgNull := rfl
    unfold MsgGame.ratObs MsgGame.q
    rw [real_bind _ (measurableSet_singleton _), hnull]
    have hpt : ∀ x, (N.game.ratKernel σ ω x).real {msgNull}
        = 1 - (σ.κ (ω, x)).real {msgNull}ᶜ := by
      intro x
      rw [MsgGame.ratKernel_apply, real_bind _ (measurableSet_singleton _),
        probReal_compl_eq_one_sub (measurableSet_singleton _), sub_sub_cancel]
      have hf : (fun z : Msg => (N.game.record z).real {msgNull})
          = ({msgNull} : Set Msg).indicator fun _ => (1 : ℝ) := by
        funext z
        cases z with
        | inl u =>
          have hu : (Sum.inl u : Msg) = msgNull := rfl
          rw [hu, indicator_of_mem (mem_singleton _)]
          exact N.record_null_null
        | inr t =>
          rw [indicator_of_notMem (by simp)]
          exact N.record_inr_null t
      rw [hf, integral_indicator_const _ (measurableSet_singleton _)]
      simp
    simp_rw [hpt]
    have hb : BM fun x => (σ.κ (ω, x)).real {msgNull}ᶜ := by
      refine BM.of_mem ?_ fun x => ⟨measureReal_nonneg, measureReal_le_one⟩
      simp only [measureReal_def]
      exact ((σ.κ.measurable_coe (measurableSet_singleton _).compl).comp
        measurable_prodMk_left).ennreal_toReal
    rw [(BM.const (1 : ℝ)).integral_sub hb]
    simp
  rw [h, mix_real N.ε_pos.le N.ε_lt.le, N.noise_null, hq]
  ring

end NoisyModel

/-! ### Examples: the hypotheses are satisfiable -/

namespace Examples

/-- The uniform recording density `k ≡ 1`. -/
noncomputable def uniformRecording : RecordingData where
  k := fun _ _ => 1
  k_cont := continuous_const
  k_pos := fun _ _ => one_pos
  k_int := fun _ => by simp

/-- A truncated-normal recording error centered at `m`, the example the paper gives for Assumption
`assumption_noisy_recording`: `k(y ∣ m) = φ((y-m)/τ) / (τ (Φ((1-m)/τ) - Φ(-m/τ)))`. -/
noncomputable def truncatedNormal (τ : ℝ) (hτ : 0 < τ) : RecordingData where
  k := fun m y => phi (((y : ℝ) - m) / τ) / (τ * (Phi ((1 - (m : ℝ)) / τ) - Phi ((0 - (m : ℝ)) / τ)))
  k_cont := by
    have hpos : ∀ m : I, 0 < Phi ((1 - (m : ℝ)) / τ) - Phi ((0 - (m : ℝ)) / τ) := fun m =>
      sub_pos.2 (Phi_strictMono (div_lt_div_of_pos_right (by linarith) hτ))
    refine Continuous.div (continuous_phi.comp (by fun_prop)) ?_ fun z => (mul_pos hτ (hpos z.1)).ne'
    exact continuous_const.mul ((continuous_Phi.comp (by fun_prop)).sub
      (continuous_Phi.comp (by fun_prop)))
  k_pos := fun m y => by
    have hpos : 0 < Phi ((1 - (m : ℝ)) / τ) - Phi ((0 - (m : ℝ)) / τ) :=
      sub_pos.2 (Phi_strictMono (div_lt_div_of_pos_right (by linarith) hτ))
    exact div_pos (phi_pos _) (mul_pos hτ hpos)
  k_int := fun m => by
    have hpos : 0 < Phi ((1 - (m : ℝ)) / τ) - Phi ((0 - (m : ℝ)) / τ) :=
      sub_pos.2 (Phi_strictMono (div_lt_div_of_pos_right (by linarith) hτ))
    set Z := Phi ((1 - (m : ℝ)) / τ) - Phi ((0 - (m : ℝ)) / τ) with hZ
    have hsub : ∫ y : I, phi (((y : ℝ) - m) / τ) / (τ * Z)
        = ∫ y in Icc (0 : ℝ) 1, phi ((y - m) / τ) / (τ * Z) :=
      integral_subtype_comap measurableSet_Icc fun y => phi ((y - m) / τ) / (τ * Z)
    rw [hsub, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    have hderiv : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y => Phi ((y - m) / τ) / Z)
        (phi ((y - m) / τ) / (τ * Z)) y := fun y _ => by
      have h1 : HasDerivAt (fun y : ℝ => (y - m) / τ) (1 / τ) y :=
        ((hasDerivAt_id y).sub_const _).div_const τ
      have h2 := ((hasDerivAt_Phi ((y - m) / τ)).comp y h1).div_const Z
      exact (show HasDerivAt (fun y => Phi ((y - m) / τ) / Z) _ y from h2).congr_deriv (by field_simp)
    have hcont : Continuous fun y : ℝ => phi ((y - m) / τ) / (τ * Z) :=
      (continuous_phi.comp (by fun_prop)).div_const _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable _ _), ← sub_div]
    exact div_self hpos.ne'

/-- The Volunteer's Dilemma of the main-text example (`π = 1/4`, `H = 2`, `L = -1`) with reporting cost
`ν_i = 1`.  Costs vanish near zero, and `ν_i = 1 < H`. -/
noncomputable def envOne : Env Bool Bool :=
  { Example.env with cost := ⟨Measure.dirac 1, inferInstance⟩ }

/-- The maintained assumptions of Section 4 do not depend on the cost distribution. -/
lemma assumptions_congr {E E' : Env Bool Bool} (hu : E'.u = E.u) (hp : E'.prior = E.prior)
    (h : VD.Assumptions E) : VD.Assumptions E' where
  H_pos := by
    have := h.H_pos
    simpa only [VD.H, hu] using this
  L_neg := by
    have := h.L_neg
    simpa only [VD.L, hu] using this
  pr_pos := by
    have := h.pr_pos
    simpa only [VD.pr, hp] using this
  prior := by
    have := h.prior
    simpa only [hu, hp] using this

lemma envOne_assumptions : VD.Assumptions envOne :=
  assumptions_congr (E := Example.env) rfl rfl Example.assumptions

lemma envOne_cost_nonneg : (envOne.cost : Measure ℝ) (Iio 0) = 0 := by
  show (Measure.dirac (1 : ℝ)) (Iio 0) = 0
  simp [Measure.dirac_apply' _ measurableSet_Iio]

lemma envOne_F_half : envOne.F (1 / 2) = 0 := by
  show (Measure.dirac (1 : ℝ)).real (Iic (1 / 2)) = 0
  rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
  norm_num

lemma envOne_F_one : envOne.F 1 = 1 := by
  show (Measure.dirac (1 : ℝ)).real (Iic 1) = 1
  rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
  norm_num

lemma envOne_H : VD.H envOne = 2 := by
  norm_num [VD.H, envOne, Example.env]

/-- The model of Subsection `subsec_general_message_spaces` for `envOne`, with `ε = η = 1/2`. -/
noncomputable def noisyOne : NoisyModel Bool Bool where
  env := envOne
  D := uniformRecording
  ε := 1 / 2
  ε_pos := by norm_num
  ε_lt := by norm_num
  η := 1 / 2
  η_pos := by norm_num
  η_lt := by norm_num
  cost_nonneg := envOne_cost_nonneg

/-- **The role of noisy recording.** For the same primitives, noisy recording gives `Π^M(n) = Π^SQ` for all
large `n`, and perfect recording gives `Π^M(n) ≥ Π^SQ + κ` for every `n ≥ 2`. -/
theorem noisy_vs_perfect :
    (∃ nStar : ℕ, ∀ n > nStar, noisyOne.game.Pi n = envOne.PiSQ) ∧
    (∃ κ > 0, ∀ n, 2 ≤ n →
      envOne.PiSQ + κ ≤ (perfectGame envOne (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) envOne_cost_nonneg).Pi n) := by
  constructor
  · exact MsgGame.statement1 noisyOne.dom (δ := 1 / 2) (by norm_num) envOne_F_half
  · refine perfect_lower envOne_assumptions _ _ _ _ _ (νhat := 1) ?_ ?_ (0 : I)
    · rw [envOne_H]
      norm_num
    · rw [envOne_F_one]
      norm_num

/-- The state-dependent model with common costs: `F₁ = F₀` standard normal. -/
noncomputable def sdCommon : SDEnv where
  u := Example.env.u
  prior := Example.env.prior
  cost := fun _ => Example.env.cost

lemma sdCommon_env (ω : Bool) : sdCommon.env ω = Example.env := rfl

lemma sdCommon_assumptions : VD.Assumptions sdCommon.base :=
  assumptions_congr (E := Example.env) rfl rfl Example.assumptions

lemma sdCommon_noise : sdCommon.Noise := fun _ => Example.noise

/-- The hypotheses of the first part of Proposition `prop_state_dependent` are satisfiable. -/
theorem sdCommon_F : sdCommon.F true 0 = sdCommon.F false 0 := rfl

/-- A law with `F(0) = 1/4` that satisfies the analogue of Assumption 1. -/
noncomputable def twoPoint : Measure ℝ :=
  mix (1 / 4) (Measure.dirac (-(Example.env.B + 1))) (Measure.dirac (Example.env.B + 1))

instance : IsProbabilityMeasure twoPoint := isProb_mix (by norm_num) (by norm_num) _ _

/-- The state-dependent model with `F₁` normal and `F₀` the two-point law. -/
noncomputable def sdDiff : SDEnv where
  u := Example.env.u
  prior := Example.env.prior
  cost := fun ω => if ω then Example.env.cost else ⟨twoPoint, inferInstance⟩

lemma sdDiff_assumptions : VD.Assumptions sdDiff.base :=
  assumptions_congr (E := Example.env) rfl rfl Example.assumptions

lemma twoPoint_F {S : Set ℝ} (hS : MeasurableSet S) :
    twoPoint.real S = (1 / 4) * S.indicator (fun _ => (1 : ℝ)) (-(Example.env.B + 1))
      + (3 / 4) * S.indicator (fun _ => (1 : ℝ)) (Example.env.B + 1) := by
  have h1 : ∀ a : ℝ, (Measure.dirac a).real S = S.indicator (fun _ => (1 : ℝ)) a := fun a => by
    rw [measureReal_def, Measure.dirac_apply' _ hS]
    by_cases ha : a ∈ S <;> simp [ha]
  rw [twoPoint, mix_real (by norm_num) (by norm_num), h1, h1]
  norm_num

lemma sdDiff_noise : sdDiff.Noise := by
  intro ω
  cases ω
  · have hB : (sdDiff.env false).B = Example.env.B := rfl
    have hcost : ((sdDiff.env false).cost : Measure ℝ) = twoPoint := rfl
    have hB0 := Example.env.B_nonneg
    constructor
    · rw [hB, hcost, twoPoint_F measurableSet_Iio]
      have h1 : -(Example.env.B + 1) ∈ Iio (-Example.env.B) := by simp
      rw [indicator_of_mem h1]
      have : 0 ≤ (3 / 4 : ℝ) * (Iio (-Example.env.B)).indicator (fun _ => (1 : ℝ)) (Example.env.B + 1) :=
        mul_nonneg (by norm_num) (indicator_nonneg (fun _ _ => zero_le_one) _)
      linarith
    · rw [hB, hcost, twoPoint_F measurableSet_Ioi]
      have h1 : Example.env.B + 1 ∈ Ioi Example.env.B := by simp
      rw [indicator_of_mem h1]
      have : 0 ≤ (1 / 4 : ℝ) * (Ioi Example.env.B).indicator (fun _ => (1 : ℝ)) (-(Example.env.B + 1)) :=
        mul_nonneg (by norm_num) (indicator_nonneg (fun _ _ => zero_le_one) _)
      linarith
  · exact Example.noise

/-- The hypotheses of the final statement of Proposition `prop_state_dependent` are satisfiable. -/
theorem sdDiff_F : sdDiff.F true 0 ≠ sdDiff.F false 0 := by
  have h1 : sdDiff.F true 0 = Phi 0 := congrFun Example.F_eq 0
  have hB0 := Example.env.B_nonneg
  have h2 : sdDiff.F false 0 = 1 / 4 := by
    show twoPoint.real (Iic 0) = 1 / 4
    rw [twoPoint_F measurableSet_Iic]
    have hm : -(Example.env.B + 1) ∈ Iic (0 : ℝ) := by
      simp only [mem_Iic]
      linarith
    have hp : Example.env.B + 1 ∉ Iic (0 : ℝ) := by
      simp only [mem_Iic, not_le]
      linarith
    rw [indicator_of_mem hm, indicator_of_notMem hp]
    norm_num
  rw [h1, h2, Phi_zero]
  norm_num

end Examples

end OA

end NoisyVD
