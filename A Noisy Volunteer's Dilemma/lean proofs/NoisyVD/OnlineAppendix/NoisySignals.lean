import NoisyVD.OnlineAppendix.Common

/-!
# Noisy observation of the state (Proposition `prop_noisy_signals`)

Individuals do not observe `ω`.  Conditional on `ω`, individual `i` observes `s_i ∈ ℝ`, i.i.d. according
to the Markov kernel `G(· ∣ ω)`, independently of the reporting costs.  A symmetric strategy is a
function of `(s_i, ν_i)`: the library's `Strat ℝ`.

The gross benefit of reporting after signal `s` is the posterior mean of `Δ_{n,ω}`, with the posterior
given by Mathlib's Bayesian inverse `G†prior`.  A posterior is unique only up to a null set of signals,
so best response is required for almost every signal.  That admits more equilibria than requiring it at
every signal, so the upper bounds below are stronger than those for the "every signal" formulation, and
the equilibrium attaining `Π^SQ` best responds at every signal.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real ProbabilityTheory

namespace NoisyVD

namespace OA

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-- A compact second-countable Hausdorff space with its Borel sets is standard Borel. -/
instance : StandardBorelSpace Ω := by
  have : TopologicalSpace.MetrizableSpace Ω := inferInstance
  let := TopologicalSpace.metrizableSpaceMetric Ω
  infer_instance

namespace Signal

variable (E : Env A Ω) (G : Kernel Ω ℝ) [IsMarkovKernel G]

/-- The marginal distribution of a signal, `∫ G(· ∣ ω) dπ(ω)`. -/
noncomputable def marg : Measure ℝ := G ∘ₘ (E.prior : Measure Ω)

/-- The posterior over the state after a signal. -/
noncomputable def post : Kernel ℝ Ω :=
  have := E.nonempty_state
  G†(E.prior : Measure Ω)

/-- `Pr(r_i = 1 ∣ s_i = y)`. -/
noncomputable def sigRp (s : Strat ℝ) (y : ℝ) : ℝ := ∫ x, s.σ y x ∂(E.cost : Measure ℝ)

/-- `p_{n,ω} = Pr(r_i = 1 ∣ ω)`. -/
noncomputable def stateRp (s : Strat ℝ) (ω : Ω) : ℝ := ∫ y, sigRp E s y ∂(G ω)

/-- `Δ_n(s) = E[Δ_{n,ω} ∣ s_i = s]`. -/
noncomputable def interim (n : ℕ) (d : Rule A) (s : Strat ℝ) (y : ℝ) : ℝ :=
  ∫ ω, E.gross n d (stateRp E G s ω) ω ∂(post E G y)

/-- Symmetric Bayesian Nash equilibrium under the signal structure `G`. -/
def IsEq (n : ℕ) (d : Rule A) (s : Strat ℝ) : Prop :=
  ∀ᵐ y ∂(marg E G), ∀ x, (x < interim E G n d s y → s.σ y x = 1) ∧ (interim E G n d s y < x → s.σ y x = 0)

/-- `E_{e,d,G}[u^p(a,ω)]`: conditional on `ω` the report count is `Bin(n, p_{n,ω})`. -/
noncomputable def payoff (n : ℕ) (d : Rule A) (s : Strat ℝ) : ℝ := payoffOf E n d (stateRp E G s)

/-- The attainable payoffs over symmetric rules and symmetric equilibria. -/
def payoffs (n : ℕ) : Set ℝ := {y | ∃ (d : Rule A) (s : Strat ℝ), IsEq E G n d s ∧ y = payoff E G n d s}

/-- `Π^G(n)`. -/
noncomputable def Pi (n : ℕ) : ℝ := sSup (payoffs E G n)

variable {E G}

instance : IsProbabilityMeasure (marg E G) := by
  unfold marg
  infer_instance

instance : IsMarkovKernel (post E G) := by
  unfold post
  infer_instance

lemma measurable_slice' (s : Strat ℝ) (y : ℝ) : Measurable (s.σ y) :=
  s.meas.comp (measurable_const.prodMk measurable_id)

lemma measurable_sigRp (s : Strat ℝ) : Measurable (sigRp E s) := by
  have h : StronglyMeasurable (Function.uncurry s.σ) := s.meas.stronglyMeasurable
  exact (h.integral_prod_right (ν := (E.cost : Measure ℝ))).measurable

lemma sigRp_mem (s : Strat ℝ) (y : ℝ) : sigRp E s y ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg fun x => (s.mem y x).1
  · have hint : Integrable (s.σ y) (E.cost : Measure ℝ) :=
      Env.integrable_of_bdd _ (measurable_slice' s y) (C := 1) fun x => by
        rw [abs_le]; constructor <;> linarith [(s.mem y x).1, (s.mem y x).2]
    have h := integral_mono (μ := (E.cost : Measure ℝ)) hint (integrable_const (1 : ℝ))
      (fun x => (s.mem y x).2)
    simpa [sigRp] using h

lemma integrable_sigRp (s : Strat ℝ) (ω : Ω) : Integrable (sigRp E s) (G ω) :=
  Env.integrable_of_bdd _ (measurable_sigRp s) (C := 1) fun y => by
    rw [abs_le]; constructor <;> linarith [(sigRp_mem (E := E) s y).1, (sigRp_mem (E := E) s y).2]

lemma measurable_stateRp (s : Strat ℝ) : Measurable (stateRp E G s) :=
  ((measurable_sigRp s).stronglyMeasurable.integral_kernel (κ := G)).measurable

lemma stateRp_mem_of {s : Strat ℝ} {ω : Ω} {a b : ℝ} (h : ∀ᵐ y ∂(G ω), sigRp E s y ∈ Icc a b) :
    stateRp E G s ω ∈ Icc a b := by
  constructor
  · have := integral_mono_ae (integrable_const a) (integrable_sigRp (E := E) (G := G) s ω)
      (h.mono fun y hy => hy.1)
    simpa [stateRp] using this
  · have := integral_mono_ae (integrable_sigRp (E := E) (G := G) s ω) (integrable_const b)
      (h.mono fun y hy => hy.2)
    simpa [stateRp] using this

lemma stateRp_mem (s : Strat ℝ) (ω : Ω) : stateRp E G s ω ∈ Icc (0 : ℝ) 1 :=
  stateRp_mem_of (Eventually.of_forall fun y => sigRp_mem s y)

/-- From signals to states. -/
lemma ae_state_of_ae_signal {Q : ℝ → Prop} (h : ∀ᵐ y ∂(marg E G), Q y) :
    ∀ᵐ ω ∂(E.prior : Measure Ω), ∀ᵐ y ∂(G ω), Q y :=
  Measure.ae_ae_of_ae_comp h

/-- From states to the posterior. -/
lemma ae_post_of_ae_state {R : Ω → Prop} (h : ∀ᵐ ω ∂(E.prior : Measure Ω), R ω) :
    ∀ᵐ y ∂(marg E G), ∀ᵐ ω ∂(post E G y), R ω := by
  have := E.nonempty_state
  have hc : (post E G) ∘ₘ (marg E G) = (E.prior : Measure Ω) := posterior_comp_self
  rw [← hc] at h
  exact Measure.ae_ae_of_ae_comp h

/-- A bound on `Δ_{n,ω}` for almost every posterior state bounds `Δ_n(y)`. -/
lemma abs_interim_le {n : ℕ} {d : Rule A} {s : Strat ℝ} {y : ℝ} {C : ℝ}
    (h : ∀ᵐ ω ∂(post E G y), |E.gross n d (stateRp E G s ω) ω| ≤ C) :
    |interim E G n d s y| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := post E G y)
    (f := fun ω => E.gross n d (stateRp E G s ω) ω) (C := C)
    (h.mono fun ω hω => by rwa [Real.norm_eq_abs])
  simpa [interim] using this

/-- The reporting probability after a signal is pinned between `F(-C⁻)` and `F(C)`. -/
lemma sigRp_band {n : ℕ} {d : Rule A} {s : Strat ℝ} {y C : ℝ}
    (hbr : ∀ x, (x < interim E G n d s y → s.σ y x = 1) ∧ (interim E G n d s y < x → s.σ y x = 0))
    (hC : |interim E G n d s y| ≤ C) : sigRp E s y ∈ Icc (E.Fm (-C)) (E.F C) := by
  obtain ⟨h1, h2⟩ := band_of_br (μ := (E.cost : Measure ℝ)) (measurable_slice' s y)
    (fun x => s.mem y x) (Eventually.of_forall hbr)
  have h' := abs_le.1 hC
  exact ⟨(E.Fm_mono h'.1).trans h1, h2.trans (E.F_mono h'.2)⟩

/-- Lemma `lemma_noise` under the signal structure. -/
theorem lemma_noise_signal {n : ℕ} {d : Rule A} {s : Strat ℝ} (he : IsEq E G n d s) :
    ∀ᵐ ω ∂(E.prior : Measure Ω), stateRp E G s ω ∈ Icc E.epsStar (1 - E.epsStar) := by
  have hy : ∀ᵐ y ∂(marg E G), sigRp E s y ∈ Icc E.epsStar (1 - E.epsStar) := by
    filter_upwards [he] with y hbr
    have hC : |interim E G n d s y| ≤ E.B :=
      abs_interim_le (Eventually.of_forall fun ω =>
        E.abs_gross_le n d (stateRp_mem s ω).1 (stateRp_mem s ω).2 ω)
    have hb := sigRp_band hbr hC
    constructor
    · exact (min_le_left _ _).trans hb.1
    · have h4 := E.F_add_Ioi E.B
      have h5 : E.epsStar ≤ (E.cost : Measure ℝ).real (Ioi E.B) := min_le_right _ _
      linarith [hb.2]
  filter_upwards [ae_state_of_ae_signal hy] with ω hω
  exact stateRp_mem_of hω

/-- `|Δ_{n,ω}| ≤ h_n := M/√n` for almost every state: Lemma `lemma_pivotal`. -/
theorem abs_gross_le_signal (hN : E.Noise) {n : ℕ} (hn : 2 ≤ n) {d : Rule A} {s : Strat ℝ}
    (he : IsEq E G n d s) :
    ∀ᵐ ω ∂(E.prior : Measure Ω), |E.gross n d (stateRp E G s ω) ω| ≤ E.hn n := by
  filter_upwards [lemma_noise_signal he] with ω hω
  exact Env.abs_gross_le_pivot E hN hn d hω ω

/-- `|Δ_n(s)| ≤ h_n` for almost every signal. -/
theorem abs_interim_le_signal (hN : E.Noise) {n : ℕ} (hn : 2 ≤ n) {d : Rule A} {s : Strat ℝ}
    (he : IsEq E G n d s) : ∀ᵐ y ∂(marg E G), |interim E G n d s y| ≤ E.hn n := by
  filter_upwards [ae_post_of_ae_state (G := G) (abs_gross_le_signal hN hn he)] with y hy
  exact abs_interim_le hy

/-- **Equation `eq_noisy_signal_reporting_band`.** -/
theorem eq_noisy_signal_reporting_band (hN : E.Noise) {n : ℕ} (hn : 2 ≤ n) {d : Rule A} {s : Strat ℝ}
    (he : IsEq E G n d s) :
    ∀ᵐ ω ∂(E.prior : Measure Ω), stateRp E G s ω ∈ Icc (E.Fm (-(E.hn n))) (E.F (E.hn n)) := by
  have hy : ∀ᵐ y ∂(marg E G), sigRp E s y ∈ Icc (E.Fm (-(E.hn n))) (E.F (E.hn n)) := by
    filter_upwards [he, abs_interim_le_signal hN hn he] with y hbr hC
    exact sigRp_band hbr hC
  filter_upwards [ae_state_of_ae_signal hy] with ω hω
  exact stateRp_mem_of hω

/-! ### The status quo -/

/-- The strategy under which exactly the types with `x < 0` report. -/
noncomputable def negStrat' : Strat ℝ where
  σ := fun _ x => if x < 0 then 1 else 0
  meas := by
    have h : Measurable fun z : ℝ × ℝ => if z.2 < 0 then (1 : ℝ) else 0 :=
      Measurable.ite (measurableSet_lt measurable_snd measurable_const) measurable_const
        measurable_const
    exact h
  mem := fun _ x => by
    by_cases hx : x < 0 <;> simp [hx]

lemma PiSQ_mem_payoffs (n : ℕ) : E.PiSQ ∈ payoffs E G n := by
  obtain ⟨a, ha⟩ := E.exists_statusQuo
  have hk : ∀ k, Env.constRule a k = diracPM a := fun _ => rfl
  refine ⟨Env.constRule a, negStrat', Eventually.of_forall fun y x => ?_, ?_⟩
  · have h0 : interim E G n (Env.constRule a) negStrat' y = 0 := by
      unfold interim
      simp only [E.gross_const hk, integral_zero]
    rw [h0]
    constructor
    · intro hx
      simp [negStrat', hx]
    · intro hx
      simp [negStrat', not_lt.2 hx.le]
  · show E.PiSQ = payoffOf E n _ _
    rw [payoffOf_eq_payoff E n _ (measurable_stateRp _) (stateRp_mem _), E.payoff_const hk, ha]

lemma le_PiFB (n : ℕ) : ∀ y ∈ payoffs E G n, y ≤ E.PiFB := by
  rintro y ⟨d, s, _, rfl⟩
  exact payoffOf_le_PiFB E n d (measurable_stateRp s) (stateRp_mem s)

/-! ### The upper bounds -/

/-- The report count is `Bin(n, p_{n,ω})` with `p_{n,ω} ∈ [p_n^-, p_n^+]`, so the proofs of Statements 1--3
of Proposition `prop_general_failures` apply. -/
theorem bandFamily (hN : E.Noise) : BandFamily E (payoffs E G) E.epsStar E.pMinus E.pPlus where
  l_pos := (Env.lemma_noise E hN).1
  sq_mem := PiSQ_mem_payoffs
  le_fb := le_PiFB
  mem := (E.bandFamily hN).mem
  bound := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    rintro y ⟨d, s, he, rfl⟩
    have hε := (Env.lemma_noise E hN).1
    have hε1 := Env.epsStar_le_half E
    have hae : ∀ᵐ ω ∂(E.prior : Measure Ω), stateRp E G s ω ∈ Icc (E.pMinus n) (E.pPlus n) := by
      filter_upwards [lemma_noise_signal he, eq_noisy_signal_reporting_band hN hn he] with ω h1 h2
      exact ⟨max_le h2.1 h1.1, le_min h2.2 h1.2⟩
    have hab := E.pMinus_le_pPlus hN hn
    have haε : E.epsStar ≤ E.pMinus n := le_max_right _ _
    have hbε : E.pPlus n ≤ 1 - E.epsStar := min_le_right _ _
    exact payoffOf_le_tv_ae E n d (measurable_stateRp s) (lt_of_lt_of_le hε haε)
      (lt_of_le_of_lt hbε (by linarith)) hab hae

/-- Statement 3 of Proposition `prop_noisy_signals`, for any derivative at zero. -/
theorem statement3 (hN : E.Noise) (hFB : E.PiSQ < E.PiFB) {t : ℝ} (hF : HasDerivAt E.F t 0) :
    limsup (Pi E G) atTop < E.PiFB := by
  obtain ⟨β, hβ0, hβ1, h1, h2⟩ := (bandFamily (G := G) hN).limsup_lt hFB
    (g := fun n => E.F (E.hn n) - E.F (-2 * E.hn n))
    (C := 3 * Env.pivConst E.B E.epsStar * t + 1)
    (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact E.pPlus_sub_pMinus_le hN hFB hn)
    ((tendsto_order.1 (E.tendsto_gap hN hFB hF)).2 _ (by linarith) |>.mono fun n hn => hn.le)
  exact lt_of_le_of_lt h1 h2

/-- **Proposition `prop_noisy_signals`.** -/
theorem prop_noisy_signals (hN : E.Noise) (hFB : E.PiSQ < E.PiFB) :
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, Pi E G n = E.PiSQ) ∧
    (HasDerivAt E.F 0 0 → Tendsto (Pi E G) atTop (𝓝 E.PiSQ)) ∧
    (∀ t > 0, HasDerivAt E.F t 0 → limsup (Pi E G) atTop < E.PiFB) := by
  refine ⟨fun δ hδ hF => (bandFamily (G := G) hN).eq_of_le (E.pPlus_le_pMinus hδ hF),
    fun hF => (bandFamily (G := G) hN).tendsto (g := fun n => E.F (E.hn n) - E.F (-2 * E.hn n)) ?_ ?_,
    fun t _ hF => statement3 hN hFB hF⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact E.pPlus_sub_pMinus_le hN hFB hn
  · have := E.tendsto_gap hN hFB hF
    simpa using this

/-! ### Uninformative signals -/

/-- If `s_i` is independent of `ω`, every symmetric equilibrium of every rule yields at most `Π^SQ`. -/
theorem payoff_le_PiSQ_of_const (hG : ∀ ω ω', G ω = G ω') (n : ℕ) (d : Rule A) (s : Strat ℝ) :
    payoff E G n d s ≤ E.PiSQ := by
  have := E.nonempty_state
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hq : ∀ ω, stateRp E G s ω = stateRp E G s ω₀ := fun ω => by
    unfold stateRp
    rw [hG ω ω₀]
  have h01 := stateRp_mem (E := E) (G := G) s ω₀
  unfold payoff
  rw [payoffOf_eq_payoff E n d (measurable_stateRp s) (stateRp_mem s)]
  have h := E.payoff_le_mix n d (constStrat _ (measurable_stateRp s) (stateRp_mem s))
    (w := bpmf n (stateRp E G s ω₀)) (fun k => bpmf_nonneg h01.1 h01.2) (fun ω k => by
      rw [rp_constStrat, hq ω])
  rw [bpmf_sum] at h
  simpa using h

/-- **If `s_i` is independent of `ω`, then `Π^G(n) = Π^SQ` for every `n`**, the extreme example after
Proposition `prop_noisy_signals`. -/
theorem Pi_of_uninformative (hG : ∀ ω ω', G ω = G ω') (n : ℕ) : Pi E G n = E.PiSQ :=
  le_antisymm
    (csSup_le ⟨_, PiSQ_mem_payoffs n⟩ (by
      rintro y ⟨d, s, _, rfl⟩
      exact payoff_le_PiSQ_of_const hG n d s))
    (le_csSup ⟨E.PiFB, le_PiFB n⟩ (PiSQ_mem_payoffs n))

/-- The lower bound in Statement 4 of Proposition `prop_general_failures` need not extend. -/
theorem not_tendsto_PiFB_of_uninformative (hG : ∀ ω ω', G ω = G ω') (hFB : E.PiSQ < E.PiFB) :
    ¬Tendsto (Pi E G) atTop (𝓝 E.PiFB) := by
  intro h
  have h1 : Tendsto (Pi E G) atTop (𝓝 E.PiSQ) := by
    simp_rw [show Pi E G = fun _ => E.PiSQ from funext (Pi_of_uninformative hG)]
    exact tendsto_const_nhds
  exact hFB.ne (tendsto_nhds_unique h1 h)

end Signal

end OA

end NoisyVD
