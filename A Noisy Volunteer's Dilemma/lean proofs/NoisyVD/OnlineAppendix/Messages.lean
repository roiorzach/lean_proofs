import NoisyVD.OnlineAppendix.ProductMeasure
import NoisyVD.OnlineAppendix.Common

/-!
# The message game (Subsection `subsec_general_message_spaces`)

`MsgGame A Ω X` is the general environment of Section 3 with message space `X`, a free null message,
mechanical individuals and a recording kernel.  The paper's model (`X = {∅} ∪ [0,1]`) is an instance,
and so are the two variants discussed in its remarks: finite messages and perfect recording.

Everything in the proofs that depends on recording enters through one condition, `MsgGame.Dom`: every
recorded law is dominated by the law of the noise.  From it we derive

* `MsgGame.anon_influence`, Lemma `lemma_anonymous_influence`;
* `MsgGame.q_le`, equation `eq_rational_nonnull_message_bound`;
* `MsgGame.tilt`, equation `eq_likelihood_ratio_bound`;
* `MsgGame.prop_upper`, Proposition `prop_general_message_upper_bounds`.
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

/-! ### Mixtures and Markov composition -/

/-- The mixture `ε μ + (1-ε) ν`. -/
noncomputable def mix (ε : ℝ) (μ ν : Measure X) : Measure X :=
  ENNReal.ofReal ε • μ + ENNReal.ofReal (1 - ε) • ν

lemma mix_apply (ε : ℝ) (μ ν : Measure X) (S : Set X) :
    mix ε μ ν S = ENNReal.ofReal ε * μ S + ENNReal.ofReal (1 - ε) * ν S := by
  simp [mix]

lemma isProb_mix {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (mix ε μ ν) := by
  constructor
  rw [mix_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

lemma mix_real {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (S : Set X) :
    (mix ε μ ν).real S = ε * μ.real S + (1 - ε) * ν.real S := by
  rw [measureReal_def, mix_apply, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith)]
  rfl

lemma real_bind {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W] {μ : Measure Z}
    [IsProbabilityMeasure μ] (κ : Kernel Z W) [IsMarkovKernel κ] {S : Set W} (hS : MeasurableSet S) :
    (κ ∘ₘ μ).real S = ∫ z, (κ z).real S ∂μ := by
  rw [measureReal_def, Measure.bind_apply hS κ.aemeasurable]
  simp only [measureReal_def]
  exact (integral_toReal (κ.measurable_coe hS).aemeasurable
    (ae_of_all _ fun z => measure_lt_top _ _)).symm

/-! ### The game -/

/-- The primitives of the message game. -/
structure MsgGame (A Ω X : Type*) [TopologicalSpace A] [TopologicalSpace Ω] [MeasurableSpace Ω]
    [MeasurableSpace X] where
  /-- `u^p`, the prior, and the distribution `F` of the cost of a rational individual. -/
  env : Env A Ω
  /-- The free null message `∅`. -/
  nullMsg : X
  /-- The law of the observed message `y_i` given the intended message `m_i`. -/
  record : Kernel X X
  record_markov : IsMarkovKernel record
  /-- The law of the message intended by a mechanical individual. -/
  mech : Measure X
  mech_prob : IsProbabilityMeasure mech
  /-- The probability of being mechanical. -/
  ε : ℝ
  ε_pos : 0 < ε
  ε_lt : ε < 1
  /-- Costs are nonnegative: `ν_i ≥ 0`. -/
  cost_nonneg : (env.cost : Measure ℝ) (Iio 0) = 0

attribute [instance] MsgGame.record_markov MsgGame.mech_prob

/-- A symmetric decision rule `d_n : X^n → Δ(A)`: measurable and invariant under permutations. -/
structure MRule (A X : Type*) [MeasurableSpace A] [MeasurableSpace X] (n : ℕ) where
  κ : Kernel (Fin n → X) A
  markov : IsMarkovKernel κ
  symm : ∀ (τ : Equiv.Perm (Fin n)) (y : Fin n → X), κ (y ∘ τ) = κ y

attribute [instance] MRule.markov

/-- A symmetric strategy of the rational individuals, with private randomization. -/
structure MStrat (Ω X : Type*) [MeasurableSpace Ω] [MeasurableSpace X] where
  κ : Kernel (Ω × ℝ) X
  markov : IsMarkovKernel κ

attribute [instance] MStrat.markov

namespace MsgGame

variable (g : MsgGame A Ω X)

/-- The law of the observed message of a mechanical individual. -/
noncomputable def noiseObs : Measure X := g.record ∘ₘ g.mech

/-- `P⁰`: the law of an individual's observed message when every rational individual sends `∅`.  It
does not depend on the state. -/
noncomputable def baseObs : Measure X := mix g.ε g.noiseObs (g.record g.nullMsg)

/-- The kernel from a cost type to the law of the observed message of a rational individual. -/
noncomputable def ratKernel (σ : MStrat Ω X) (ω : Ω) : Kernel ℝ X :=
  (g.record ∘ₖ σ.κ).comap (fun x => (ω, x)) measurable_prodMk_left

/-- The law of the observed message of a rational individual in state `ω`. -/
noncomputable def ratObs (σ : MStrat Ω X) (ω : Ω) : Measure X :=
  g.ratKernel σ ω ∘ₘ (g.env.cost : Measure ℝ)

/-- `P_ω`: the law of an individual's observed message in state `ω`. -/
noncomputable def obs (σ : MStrat Ω X) (ω : Ω) : Measure X := mix g.ε g.noiseObs (g.ratObs σ ω)

instance : IsProbabilityMeasure g.noiseObs := by
  unfold noiseObs
  infer_instance

instance : IsProbabilityMeasure g.baseObs :=
  isProb_mix g.ε_pos.le g.ε_lt.le _ _

instance (σ : MStrat Ω X) (ω : Ω) : IsMarkovKernel (g.ratKernel σ ω) := by
  unfold ratKernel
  infer_instance

instance (σ : MStrat Ω X) (ω : Ω) : IsProbabilityMeasure (g.ratObs σ ω) := by
  unfold ratObs
  infer_instance

instance (σ : MStrat Ω X) (ω : Ω) : IsProbabilityMeasure (g.obs σ ω) :=
  isProb_mix g.ε_pos.le g.ε_lt.le _ _

variable {n : ℕ}

/-- `V_ω(y) = ∫ u^p(a,ω) d_n(y)(da)`. -/
noncomputable def V (d : MRule A X n) (ω : Ω) (y : Fin n → X) : ℝ := ∫ a, g.env.u a ω ∂(d.κ y)

/-- `U_{n,ω}(m)`: the expected value of `u^p(a,ω)` for individual `i` when sending `m`, the other
observations being i.i.d. from `P_ω`. -/
noncomputable def U (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω) (i : Fin n) (m : X) : ℝ :=
  ∫ y, g.V d ω y ∂(Measure.pi (Function.update (fun _ : Fin n => g.obs σ ω) i (g.record m)))

open Classical in
/-- The cost of the message `m` for type `x`: `x 1_{m ≠ ∅}`. -/
noncomputable def msgCost (m : X) (x : ℝ) : ℝ := if m = g.nullMsg then 0 else x

/-- Utility `u^i` net of the message cost, equation `eq_general_message_utility`. -/
noncomputable def netU (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω) (i : Fin n) (m : X) (x : ℝ) : ℝ :=
  g.U d σ ω i m - g.msgCost m x

/-- Symmetric Bayesian Nash equilibrium among the rational individuals: in every state, almost every
cost type puts probability one on best replies. -/
def IsEq (d : MRule A X n) (σ : MStrat Ω X) : Prop :=
  ∀ ω, ∀ᵐ x ∂(g.env.cost : Measure ℝ), ∀ᵐ m ∂(σ.κ (ω, x)), ∀ i m',
    g.netU d σ ω i m' x ≤ g.netU d σ ω i m x

/-- `q_{n,ω} = Pr(m_i ≠ ∅ ∣ ω, i is rational)`. -/
noncomputable def q (σ : MStrat Ω X) (ω : Ω) : ℝ :=
  ∫ x, (σ.κ (ω, x)).real {g.nullMsg}ᶜ ∂(g.env.cost : Measure ℝ)

/-- The expected payoff in state `ω`. -/
noncomputable def W (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω) : ℝ :=
  ∫ y, g.V d ω y ∂(Measure.pi fun _ : Fin n => g.obs σ ω)

/-- `E_{e,d_n}[u^p(a,ω)]`. -/
noncomputable def payoff (d : MRule A X n) (σ : MStrat Ω X) : ℝ :=
  ∫ ω, g.W d σ ω ∂(g.env.prior : Measure Ω)

/-- The attainable payoffs over symmetric rules and symmetric equilibria. -/
def payoffs (n : ℕ) : Set ℝ := {y | ∃ (d : MRule A X n) (σ : MStrat Ω X), g.IsEq d σ ∧ y = g.payoff d σ}

/-- `Π^M(n)`, equation `eq_general_message_payoff`. -/
noncomputable def Pi (n : ℕ) : ℝ := sSup (g.payoffs n)

/-- The domination condition: every recorded law is at most `Λ` times the noise `ε P^{mech}`.  The
paper's `Λ` satisfies this under Assumption `assumption_noisy_recording`. -/
def Dom (Λ : ℝ) : Prop :=
  ∀ m S, MeasurableSet S → (g.record m).real S ≤ Λ * (g.ε * g.noiseObs.real S)

variable {g}

lemma msgCost_null (x : ℝ) : g.msgCost g.nullMsg x = 0 := by simp [msgCost]

lemma msgCost_ne {m : X} (hm : m ≠ g.nullMsg) (x : ℝ) : g.msgCost m x = x := by simp [msgCost, hm]

/-! ### Basic properties of the payoff function -/

/-- The law `d_n(y)` as a constant rule of the main-text library. -/
noncomputable def ruleAt (d : MRule A X n) (y : Fin n → X) : Rule A := fun _ => ⟨d.κ y, inferInstance⟩

lemma V_eq_v (d : MRule A X n) (ω : Ω) (y : Fin n → X) : g.V d ω y = g.env.v (ruleAt d y) 0 ω := rfl

lemma V_mem (d : MRule A X n) (ω : Ω) (y : Fin n → X) :
    g.V d ω y ∈ Icc g.env.uMin (g.env.uMin + g.env.B) := by
  rw [V_eq_v]
  exact g.env.v_mem _ ω 0

lemma V_le_maxU (d : MRule A X n) (ω : Ω) (y : Fin n → X) : g.V d ω y ≤ g.env.maxU ω := by
  rw [V_eq_v]
  exact g.env.v_le_maxU _ 0 ω

lemma V_symm (d : MRule A X n) (ω : Ω) (τ : Equiv.Perm (Fin n)) (y : Fin n → X) :
    g.V d ω (y ∘ τ) = g.V d ω y := by
  unfold V
  rw [d.symm]

lemma measurable_V_joint (d : MRule A X n) :
    Measurable fun z : Ω × (Fin n → X) => g.V d z.1 z.2 := by
  let κ' : Kernel (Ω × (Fin n → X)) A := d.κ.comap Prod.snd measurable_snd
  have hf : Measurable fun p : (Ω × (Fin n → X)) × A => g.env.u p.2 p.1.1 :=
    g.env.u_cont.measurable.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  exact (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ')).measurable

lemma measurable_V (d : MRule A X n) (ω : Ω) : Measurable (g.V d ω) :=
  (measurable_V_joint (g := g) d).comp (measurable_const.prodMk measurable_id)

lemma measurable_ratObs (σ : MStrat Ω X) : Measurable (g.ratObs σ) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have h : ∀ ω, g.ratObs σ ω S = ∫⁻ x, (g.record ∘ₖ σ.κ) (ω, x) S ∂(g.env.cost : Measure ℝ) := fun ω => by
    rw [ratObs, Measure.bind_apply hS (Kernel.aemeasurable _)]
    rfl
  simp_rw [h]
  exact ((g.record ∘ₖ σ.κ).measurable_coe hS).lintegral_prod_right'

lemma measurable_obs (σ : MStrat Ω X) : Measurable (g.obs σ) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  simp only [obs, mix_apply]
  exact measurable_const.add
    (measurable_const.mul ((Measure.measurable_coe hS).comp (measurable_ratObs σ)))

/-- A measurable family of probability laws gives a measurable family of its `n`-fold products. -/
noncomputable def piKernel {T : Type*} [MeasurableSpace T] (P : T → Measure X) (hP : Measurable P)
    [∀ t, IsProbabilityMeasure (P t)] (n : ℕ) : Kernel T (Fin n → X) where
  toFun t := Measure.pi fun _ : Fin n => P t
  measurable' := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi ?_
    rintro _ ⟨s, hs, rfl⟩
    have hs' : ∀ i, MeasurableSet (s i) := fun i => hs i (mem_univ i)
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ fun i _ => (Measure.measurable_coe (hs' i)).comp hP

instance {T : Type*} [MeasurableSpace T] (P : T → Measure X) (hP : Measurable P)
    [∀ t, IsProbabilityMeasure (P t)] (n : ℕ) : IsMarkovKernel (piKernel P hP n) :=
  ⟨fun t => by
    show IsProbabilityMeasure (Measure.pi fun _ : Fin n => P t)
    infer_instance⟩

lemma measurable_W (d : MRule A X n) (σ : MStrat Ω X) : Measurable (g.W d σ) := by
  have h := ((measurable_V_joint (g := g) d).stronglyMeasurable.integral_kernel_prod_right'
    (κ := piKernel (g.obs σ) (measurable_obs σ) n)).measurable
  exact h

lemma W_mem (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω) :
    g.W d σ ω ∈ Icc g.env.uMin (g.env.uMin + g.env.B) := by
  have hb : BM (g.V d ω) := BM.of_mem (measurable_V d ω) (V_mem d ω)
  constructor
  · have := integral_mono (μ := Measure.pi fun _ : Fin n => g.obs σ ω) (integrable_const g.env.uMin)
      (hb.integrable _) (fun y => (V_mem d ω y).1)
    simpa [W] using this
  · have := integral_mono (μ := Measure.pi fun _ : Fin n => g.obs σ ω) (hb.integrable _)
      (integrable_const (g.env.uMin + g.env.B)) (fun y => (V_mem d ω y).2)
    simpa [W] using this

lemma bm_W (d : MRule A X n) (σ : MStrat Ω X) : BM (g.W d σ) :=
  BM.of_mem (measurable_W d σ) (W_mem d σ)

lemma W_le_maxU (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω) : g.W d σ ω ≤ g.env.maxU ω := by
  have hb : BM (g.V d ω) := BM.of_mem (measurable_V d ω) (V_mem d ω)
  have := integral_mono (μ := Measure.pi fun _ : Fin n => g.obs σ ω) (hb.integrable _)
    (integrable_const (g.env.maxU ω)) (fun y => V_le_maxU d ω y)
  simpa [W] using this

lemma payoff_le_PiFB (d : MRule A X n) (σ : MStrat Ω X) : g.payoff d σ ≤ g.env.PiFB :=
  integral_mono ((bm_W d σ).integrable _) g.env.integrable_maxU (fun ω => W_le_maxU d σ ω)

/-! ### The state-independent benchmark -/

/-- The expected payoff in state `ω` when the observations are i.i.d. from `P⁰`. -/
noncomputable def W0 (g : MsgGame A Ω X) (d : MRule A X n) (ω : Ω) : ℝ :=
  ∫ y, g.V d ω y ∂(Measure.pi fun _ : Fin n => g.baseObs)

lemma W0_mem (d : MRule A X n) (ω : Ω) :
    g.W0 d ω ∈ Icc g.env.uMin (g.env.uMin + g.env.B) := by
  have hb : BM (g.V d ω) := BM.of_mem (measurable_V d ω) (V_mem d ω)
  constructor
  · have := integral_mono (μ := Measure.pi fun _ : Fin n => g.baseObs) (integrable_const g.env.uMin)
      (hb.integrable _) (fun y => (V_mem d ω y).1)
    simpa [W0] using this
  · have := integral_mono (μ := Measure.pi fun _ : Fin n => g.baseObs) (hb.integrable _)
      (integrable_const (g.env.uMin + g.env.B)) (fun y => (V_mem d ω y).2)
    simpa [W0] using this

lemma W0_le_maxU (d : MRule A X n) (ω : Ω) : g.W0 d ω ≤ g.env.maxU ω := by
  have hb : BM (g.V d ω) := BM.of_mem (measurable_V d ω) (V_mem d ω)
  have := integral_mono (μ := Measure.pi fun _ : Fin n => g.baseObs) (hb.integrable _)
    (integrable_const (g.env.maxU ω)) (fun y => V_le_maxU d ω y)
  simpa [W0] using this

lemma measurable_W0 (d : MRule A X n) : Measurable (g.W0 d) := by
  have h := ((measurable_V_joint (g := g) d).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi fun _ : Fin n => g.baseObs)).measurable
  exact h

/-- Reports drawn from a state-independent law are uninformative: the payoff is at most `Π^SQ`. -/
lemma integral_W0_le (d : MRule A X n) :
    ∫ ω, g.W0 d ω ∂(g.env.prior : Measure Ω) ≤ g.env.PiSQ := by
  set π₀ := Measure.pi fun _ : Fin n => g.baseObs with hπ₀
  have hbd : BM fun z : Ω × (Fin n → X) => g.V d z.1 z.2 :=
    BM.of_mem (measurable_V_joint d) fun z => V_mem d z.1 z.2
  have hswap : ∫ ω, g.W0 d ω ∂(g.env.prior : Measure Ω)
      = ∫ y, (∫ ω, g.V d ω y ∂(g.env.prior : Measure Ω)) ∂π₀ := by
    unfold W0
    exact integral_integral_swap (f := fun ω y => g.V d ω y) (hbd.integrable _)
  rw [hswap]
  have hle : ∀ y, ∫ ω, g.V d ω y ∂(g.env.prior : Measure Ω) ≤ g.env.PiSQ := fun y =>
    g.env.integral_v_le_PiSQ (ruleAt d y) 0
  have hb : BM fun y => ∫ ω, g.V d ω y ∂(g.env.prior : Measure Ω) := by
    refine BM.of_mem (a := g.env.uMin) (b := g.env.uMin + g.env.B) ?_ fun y => ?_
    · exact (hbd.1.stronglyMeasurable.integral_prod_left
        (μ := (g.env.prior : Measure Ω))).measurable
    · have hby : BM fun ω => g.V d ω y := BM.of_mem
        (hbd.1.comp (measurable_id.prodMk measurable_const)) fun ω => V_mem d ω y
      constructor
      · have := integral_mono (μ := (g.env.prior : Measure Ω)) (integrable_const g.env.uMin)
          (hby.integrable _) (fun ω => (V_mem d ω y).1)
        simpa using this
      · have := integral_mono (μ := (g.env.prior : Measure Ω)) (hby.integrable _)
          (integrable_const (g.env.uMin + g.env.B)) (fun ω => (V_mem d ω y).2)
        simpa using this
  have := integral_mono (μ := π₀) (hb.integrable _) (integrable_const g.env.PiSQ) hle
  simpa using this

/-! ### Domination and anonymous influence -/

section Dom

variable {Λ : ℝ}

lemma noise_le_base (S : Set X) : g.ε * g.noiseObs.real S ≤ g.baseObs.real S := by
  have h := g.ε_lt
  rw [baseObs, mix_real g.ε_pos.le g.ε_lt.le]
  have : 0 ≤ (1 - g.ε) * (g.record g.nullMsg).real S :=
    mul_nonneg (by linarith) measureReal_nonneg
  linarith

lemma noise_le_obs (σ : MStrat Ω X) (ω : Ω) (S : Set X) :
    g.ε * g.noiseObs.real S ≤ (g.obs σ ω).real S := by
  have h := g.ε_lt
  rw [obs, mix_real g.ε_pos.le g.ε_lt.le]
  have : 0 ≤ (1 - g.ε) * (g.ratObs σ ω).real S :=
    mul_nonneg (by linarith) measureReal_nonneg
  linarith

lemma Dom.one_le (hΛ : g.Dom Λ) : 1 ≤ Λ := by
  have h := hΛ g.nullMsg univ MeasurableSet.univ
  simp only [probReal_univ, mul_one] at h
  have hε := g.ε_pos
  have hε1 := g.ε_lt
  by_contra hcon
  push Not at hcon
  have h3 : Λ * g.ε < 1 := by nlinarith
  linarith

lemma Dom.nonneg (hΛ : g.Dom Λ) : 0 ≤ Λ := by
  linarith [hΛ.one_le]

lemma Dom.le_obs (hΛ : g.Dom Λ) (σ : MStrat Ω X) (ω : Ω) (m : X) {S : Set X} (hS : MeasurableSet S) :
    (g.record m).real S ≤ Λ * (g.obs σ ω).real S :=
  (hΛ m S hS).trans (mul_le_mul_of_nonneg_left (noise_le_obs σ ω S) hΛ.nonneg)

lemma Dom.le_base (hΛ : g.Dom Λ) (m : X) {S : Set X} (hS : MeasurableSet S) :
    (g.record m).real S ≤ Λ * g.baseObs.real S :=
  (hΛ m S hS).trans (mul_le_mul_of_nonneg_left (noise_le_base S) hΛ.nonneg)

/-- `|U_{n,ω}(m) - E[V_ω]| ≤ (B/2) √((Λ-1)/n)`. -/
lemma Dom.abs_U_sub (hΛ : g.Dom Λ) (hn : 0 < n) (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω)
    (i : Fin n) (m : X) :
    |g.U d σ ω i m - g.W d σ ω| ≤ (g.env.B / 2) * √((Λ - 1) / n) :=
  anon_bound hn (fun _ hS => hΛ.le_obs σ ω m hS) (measurable_V d ω) (V_mem d ω)
    (V_symm d ω) i

/-- **Lemma `lemma_anonymous_influence`.** -/
theorem anon_influence (hΛ : g.Dom Λ) (hn : 0 < n) (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω)
    (i : Fin n) (m m' : X) :
    |g.U d σ ω i m - g.U d σ ω i m'| ≤ g.env.B * √(Λ - 1) / √(n : ℝ) := by
  have h1 := hΛ.abs_U_sub hn d σ ω i m
  have h2 := hΛ.abs_U_sub hn d σ ω i m'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have e : g.env.B * √(Λ - 1) / √(n : ℝ) = 2 * ((g.env.B / 2) * √((Λ - 1) / n)) := by
    rw [Real.sqrt_div' _ hnr.le]
    ring
  rw [e]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `h_n = M_G/√n`, with `M_G = B √(Λ-1)`. -/
noncomputable def hG (g : MsgGame A Ω X) (Λ : ℝ) (n : ℕ) : ℝ := g.env.B * √(Λ - 1) / √(n : ℝ)

/-- In equilibrium, every type above `h_n` sends `∅`. -/
lemma silent_of_gt (hΛ : g.Dom Λ) (hn : 0 < n) {d : MRule A X n} {σ : MStrat Ω X} (he : g.IsEq d σ)
    (ω : Ω) : ∀ᵐ x ∂(g.env.cost : Measure ℝ), g.hG Λ n < x →
      (σ.κ (ω, x)).real {g.nullMsg}ᶜ = 0 := by
  filter_upwards [he ω] with x hx hlt
  have hm : ∀ᵐ m ∂(σ.κ (ω, x)), m = g.nullMsg := by
    filter_upwards [hx] with m hm
    by_contra hne
    have h1 := hm ⟨0, hn⟩ g.nullMsg
    have hc1 : g.msgCost g.nullMsg x = 0 := by simp [msgCost]
    have hc2 : g.msgCost m x = x := by simp [msgCost, hne]
    simp only [netU, hc1, hc2, sub_zero] at h1
    have h2 := anon_influence hΛ hn d σ ω ⟨0, hn⟩ m g.nullMsg
    have h3 := (abs_le.1 h2).2
    have h4 : g.hG Λ n = g.env.B * √(Λ - 1) / √(n : ℝ) := rfl
    linarith
  have hS : (σ.κ (ω, x)) {g.nullMsg}ᶜ = 0 := ae_iff.1 hm
  simp [measureReal_def, hS]

/-- **Equation `eq_rational_nonnull_message_bound`.** -/
theorem q_le (hΛ : g.Dom Λ) (hn : 0 < n) {d : MRule A X n} {σ : MStrat Ω X} (he : g.IsEq d σ)
    (ω : Ω) : g.q σ ω ≤ g.env.F (g.hG Λ n) := by
  have hm : Measurable fun x => (σ.κ (ω, x)).real {g.nullMsg}ᶜ := by
    simp only [measureReal_def]
    exact ((σ.κ.measurable_coe (measurableSet_singleton _).compl).comp
      measurable_prodMk_left).ennreal_toReal
  have hF : g.env.F (g.hG Λ n)
      = ∫ x, (Iic (g.hG Λ n)).indicator (fun _ => (1 : ℝ)) x ∂(g.env.cost : Measure ℝ) := by
    rw [integral_indicator_const _ measurableSet_Iic]
    simp [Env.F]
  rw [hF]
  have hb : BM fun x => (σ.κ (ω, x)).real {g.nullMsg}ᶜ :=
    BM.of_mem hm fun x => ⟨measureReal_nonneg, measureReal_le_one⟩
  refine integral_mono_ae (hb.integrable _)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) ?_
  filter_upwards [silent_of_gt hΛ hn he ω] with x hx
  by_cases hxh : x ≤ g.hG Λ n
  · simp only [indicator_of_mem (mem_Iic.2 hxh)]
    exact measureReal_le_one
  · rw [indicator_of_notMem (by simpa using hxh), hx (not_le.1 hxh)]

/-! ### The likelihood ratio -/

lemma measurable_real_record {S : Set X} (hS : MeasurableSet S) :
    Measurable fun m => (g.record m).real S := by
  simp only [measureReal_def]
  exact (g.record.measurable_coe hS).ennreal_toReal

lemma ratKernel_apply (σ : MStrat Ω X) (ω : Ω) (x : ℝ) :
    g.ratKernel σ ω x = g.record ∘ₘ (σ.κ (ω, x)) := by
  simp [ratKernel, Kernel.comp_apply]

/-- `|P_ω(S) - P⁰(S)| ≤ (1-ε) Λ q P⁰(S)`: equation `eq_likelihood_ratio_bound`, as an inequality between
measures. -/
theorem abs_obs_sub_le (hΛ : g.Dom Λ) (σ : MStrat Ω X) (ω : Ω) {S : Set X} (hS : MeasurableSet S) :
    |(g.obs σ ω).real S - g.baseObs.real S| ≤ (1 - g.ε) * Λ * g.q σ ω * g.baseObs.real S := by
  have hε := g.ε_lt
  set b := g.baseObs.real S with hb
  have hb0 : 0 ≤ b := measureReal_nonneg
  set a0 := (g.record g.nullMsg).real S with ha0
  have ha0le : a0 ≤ Λ * b := hΛ.le_base _ hS
  have hA : ∀ m, |(g.record m).real S - a0| ≤ Λ * b * ({g.nullMsg}ᶜ : Set X).indicator (fun _ => (1 : ℝ)) m := by
    intro m
    by_cases hm : m = g.nullMsg
    · simp [hm, ha0]
    · have hmem : m ∈ ({g.nullMsg}ᶜ : Set X) := hm
      rw [indicator_of_mem hmem, mul_one, abs_le]
      have h1 := hΛ.le_base m hS
      have h2 : 0 ≤ (g.record m).real S := measureReal_nonneg
      have h3 : 0 ≤ a0 := measureReal_nonneg
      constructor <;> linarith
  have hAm := measurable_real_record (g := g) hS
  have hAB : BM fun m => (g.record m).real S :=
    BM.of_mem hAm fun m => ⟨measureReal_nonneg, measureReal_le_one⟩
  -- a fixed type
  have hx : ∀ x, |(g.ratKernel σ ω x).real S - a0|
      ≤ Λ * b * (σ.κ (ω, x)).real {g.nullMsg}ᶜ := by
    intro x
    rw [ratKernel_apply, real_bind g.record hS]
    have hdiff : (∫ m, (g.record m).real S ∂(σ.κ (ω, x))) - a0
        = ∫ m, ((g.record m).real S - a0) ∂(σ.κ (ω, x)) := by
      rw [hAB.integral_sub (BM.const a0)]
      simp
    rw [hdiff]
    have hbound : ∫ m, |(g.record m).real S - a0| ∂(σ.κ (ω, x))
        ≤ ∫ m, Λ * b * ({g.nullMsg}ᶜ : Set X).indicator (fun _ => (1 : ℝ)) m ∂(σ.κ (ω, x)) := by
      refine integral_mono ?_ ?_ hA
      · exact ((hAB.sub (BM.const a0)).integrable _).abs
      · exact ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton _).compl).const_mul _
    rw [integral_const_mul, integral_indicator_const _ (measurableSet_singleton _).compl] at hbound
    simp only [smul_eq_mul, mul_one] at hbound
    exact (abs_integral_le_integral_abs).trans hbound
  -- integrating over types
  have hrat : (g.ratObs σ ω).real S - a0
      = ∫ x, ((g.ratKernel σ ω x).real S - a0) ∂(g.env.cost : Measure ℝ) := by
    have hBx : BM fun x => (g.ratKernel σ ω x).real S := by
      refine BM.of_mem ?_ fun x => ⟨measureReal_nonneg, measureReal_le_one⟩
      simp only [measureReal_def]
      exact ((g.ratKernel σ ω).measurable_coe hS).ennreal_toReal
    rw [hBx.integral_sub (BM.const a0)]
    simp [ratObs, real_bind _ hS]
  have hmq : BM fun x => (σ.κ (ω, x)).real {g.nullMsg}ᶜ := by
    refine BM.of_mem ?_ fun x => ⟨measureReal_nonneg, measureReal_le_one⟩
    simp only [measureReal_def]
    exact ((σ.κ.measurable_coe (measurableSet_singleton _).compl).comp
      measurable_prodMk_left).ennreal_toReal
  have hBx' : BM fun x => (g.ratKernel σ ω x).real S - a0 := by
    refine BM.sub ?_ (BM.const a0)
    refine BM.of_mem ?_ fun x => ⟨measureReal_nonneg, measureReal_le_one⟩
    simp only [measureReal_def]
    exact ((g.ratKernel σ ω).measurable_coe hS).ennreal_toReal
  have hratabs : |(g.ratObs σ ω).real S - a0| ≤ Λ * b * g.q σ ω := by
    rw [hrat]
    refine (abs_integral_le_integral_abs).trans ?_
    have : ∫ x, |(g.ratKernel σ ω x).real S - a0| ∂(g.env.cost : Measure ℝ)
        ≤ ∫ x, Λ * b * (σ.κ (ω, x)).real {g.nullMsg}ᶜ ∂(g.env.cost : Measure ℝ) :=
      integral_mono (hBx'.integrable _).abs ((hmq.integrable _).const_mul _) hx
    rwa [integral_const_mul] at this
  have hdiff : (g.obs σ ω).real S - b = (1 - g.ε) * ((g.ratObs σ ω).real S - a0) := by
    rw [obs, hb, baseObs, mix_real g.ε_pos.le g.ε_lt.le, mix_real g.ε_pos.le g.ε_lt.le]
    ring
  rw [hdiff, abs_mul, abs_of_pos (by linarith : 0 < 1 - g.ε)]
  have := mul_le_mul_of_nonneg_left hratabs (by linarith : 0 ≤ 1 - g.ε)
  calc _ ≤ _ := this
    _ = _ := by ring

lemma q_nonneg (σ : MStrat Ω X) (ω : Ω) : 0 ≤ g.q σ ω :=
  integral_nonneg fun _ => measureReal_nonneg

/-- The density of `P_ω` with respect to `P⁰` is in `[1-c, 1+c]` whenever `(1-ε) Λ q ≤ c ≤ 1`. -/
theorem tilt (hΛ : g.Dom Λ) (σ : MStrat Ω X) (ω : Ω) {c : ℝ} (hc : (1 - g.ε) * Λ * g.q σ ω ≤ c)
    (hc1 : c ≤ 1) : ∃ r : X → ℝ, IsTilt g.baseObs (g.obs σ ω) r c := by
  have hε := g.ε_lt
  have hc0 : 0 ≤ c := le_trans (mul_nonneg (mul_nonneg (by linarith) hΛ.nonneg) (q_nonneg σ ω)) hc
  obtain ⟨r, hr, hmem, heq⟩ := exists_density (P := g.baseObs) (Q := g.obs σ ω) (a := 1 - c) (b := 1 + c)
    (by linarith) (by linarith)
    (fun S hS => by
      have h1 := abs_le.1 (abs_obs_sub_le hΛ σ ω hS)
      have h2 : (1 - g.ε) * Λ * g.q σ ω * g.baseObs.real S ≤ c * g.baseObs.real S :=
        mul_le_mul_of_nonneg_right hc measureReal_nonneg
      linarith [h1.1])
    (fun S hS => by
      have h1 := abs_le.1 (abs_obs_sub_le hΛ σ ω hS)
      have h2 : (1 - g.ε) * Λ * g.q σ ω * g.baseObs.real S ≤ c * g.baseObs.real S :=
        mul_le_mul_of_nonneg_right hc measureReal_nonneg
      linarith [h1.2])
  exact ⟨r, hr, hmem, hc0, hc1, heq⟩

end Dom

end MsgGame

end OA

end NoisyVD
