import NoisyVD.OnlineAppendix.Fidelity

/-!
# A Noisy Volunteer's Dilemma: all results in the Online Appendix

Each theorem below is the Lean statement of a labelled result of the Online Appendix of `current.tex`.
The final block prints the axioms used by each one: only `propext`, `Classical.choice` and `Quot.sound`,
the standard foundations of Lean's Mathlib.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real ProbabilityTheory

namespace NoisyVD

namespace OA

local notation "I" => unitInterval

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-! ### State-dependent reporting costs -/

/-- **Proposition `prop_state_dependent`.** -/
theorem PropositionStateDependent {E : SDEnv} (hV : VD.Assumptions E.base) (hN : E.Noise) :
    (E.F true 0 = E.F false 0 →
      (∀ δ > 0, (∀ ω, E.F ω δ - E.F ω (-δ) = 0) → ∃ nStar : ℕ, ∀ n > nStar, E.Pi n = E.base.PiSQ) ∧
      (HasDerivAt (E.F true) 0 0 → HasDerivAt (E.F false) 0 0 → Tendsto E.Pi atTop (𝓝 E.base.PiSQ)) ∧
      (∀ t₁ t₀ : ℝ, HasDerivAt (E.F true) t₁ 0 → HasDerivAt (E.F false) t₀ 0 →
        ∃ β : ℝ, 0 < β ∧ β < 1 ∧ limsup E.Pi atTop ≤ β * E.base.PiSQ + (1 - β) * E.base.PiFB ∧
          β * E.base.PiSQ + (1 - β) * E.base.PiFB < E.base.PiFB)) ∧
    (E.F true 0 ≠ E.F false 0 → Tendsto E.Pi atTop (𝓝 E.base.PiFB)) :=
  SDEnv.prop_state_dependent hV hN

/-- **Equation `eq_sd_band`.** -/
theorem EqSdBand {E : SDEnv} (hN : E.Noise) {n : ℕ} (hn : 2 ≤ n) {d : Rule Bool} {s : Strat Bool}
    (he : E.IsEq n d s) (ω : Bool) :
    E.Fm ω (-(E.M / √(n : ℝ))) ≤ E.rp s ω ∧ E.rp s ω ≤ E.F ω (E.M / √(n : ℝ)) :=
  SDEnv.eq_sd_band hN hn he ω

/-! ### Worst-case equilibrium selection -/

/-- **Equation `eq_worst_equilibrium_sandwich`.** -/
theorem EqWorstSandwich (E : Env A Ω) (n : ℕ) :
    E.PiSQ ≤ E.PiWT n ∧ E.PiWT n ≤ E.PiW n ∧ E.PiW n ≤ E.Pi n ∧ E.Pi n ≤ E.PiFB :=
  E.sandwich n

/-- **Proposition `prop_worst_equilibrium`.** The paper states this for the Volunteer's Dilemma. Statements 1
and 2 and the first claim in Statement 3 also hold in the general model: see `Env.worst_statement1`,
`Env.worst_statement2` and `Env.worst_statement3`. The paper does not state this. -/
theorem PropositionWorstEquilibrium {E : Env Bool Bool} (hV : VD.Assumptions E) (hN : E.Noise) :
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, E.PiW n = E.PiSQ) ∧
    (HasDerivAt E.F 0 0 → Tendsto E.PiW atTop (𝓝 E.PiSQ)) ∧
    (∀ t > 0, HasDerivAt E.F t 0 → limsup E.PiW atTop < E.PiFB) ∧
    (0 < Fworst (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) ∧
      ∀ (U : Set ℝ) (t : ℝ), IsOpen U → (0 : ℝ) ∈ U → ContDiffOn ℝ 1 E.F U → deriv E.F 0 = t → 0 < t →
        Fworst (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) < t →
        E.PiSQ < liminf E.PiWT atTop) ∧
    (∀ α > 0, Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α) → Tendsto E.PiWT atTop (𝓝 E.PiFB)) :=
  prop_worst_equilibrium hV hN

/-- **Equation `eq_vd_fixed_point`.** -/
theorem EqVdFixedPoint {E : Env Bool Bool} (hN : E.Noise) {U : Set ℝ} (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U)
    (hF : ContDiffOn ℝ 1 E.F U) {t : ℝ} (ht : deriv E.F 0 = t) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (T : ℕ) (s : Strat Bool), E.IsEq n (thresholdRule T true false) s →
      E.rp s true = E.F (VD.H E * rho (n - 1) (E.rp s true) T) ∧
        E.rp s false = E.F (VD.L E * rho (n - 1) (E.rp s false) T) :=
  eq_vd_fixed_point hN (VD.Smooth.of_contDiffOn hU h0 hF ht)

/-- The limit in the proof of Proposition `prop_worst_equilibrium`:
`lim_n inf_{e ∈ E(d_n)} E_{e,d_n}[u^p(a,ω)] = Π^SQ + J(t)`, for `d_n` the threshold rule at `⌈ns⌉`. -/
theorem WorstCaseLimit {E : Env Bool Bool} (hV : VD.Assumptions E) (hN : E.Noise) {U : Set ℝ}
    (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) (hF : ContDiffOn ℝ 1 E.F U) {t : ℝ} (ht : deriv E.F 0 = t) :
    Tendsto (fun n : ℕ => E.worstPayoff n (thresholdRule ⌈(n : ℝ) * E.F 0⌉₊ true false)) atTop
      (𝓝 (E.PiSQ + Jfun (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) t)) :=
  tendsto_worst_ceil hV hN (VD.Smooth.of_contDiffOn hU h0 hF ht)

/-- The properties of `J` in the proof of Proposition `prop_worst_equilibrium`: it is continuous and
strictly increasing, `J(0) = ½[πH - (1-π)ℓ] < 0`, `J(t) → πH`, and `\underline F_0` is its unique zero. -/
theorem WorstCaseCutoff {pr H l S : ℝ} (hp : Par pr H l S) :
    Continuous (Jfun pr H l S) ∧ StrictMono (Jfun pr H l S) ∧
    Jfun pr H l S 0 = (pr * H - (1 - pr) * l) / 2 ∧ Jfun pr H l S 0 < 0 ∧
    Tendsto (Jfun pr H l S) atTop (𝓝 (pr * H)) ∧
    0 < Fworst pr H l S ∧ Jfun pr H l S (Fworst pr H l S) = 0 ∧
    ∀ t, 0 < Jfun pr H l S t ↔ Fworst pr H l S < t :=
  ⟨continuous_Jfun pr H l S, Jfun_strictMono hp, Jfun_zero hp, Jfun_zero_neg hp, tendsto_Jfun_atTop hp,
    Fworst_spec hp⟩

/-! ### Noisy observation of the state -/

/-- **Proposition `prop_noisy_signals`**, for any signal structure `G`. -/
theorem PropositionNoisySignals (E : Env A Ω) (G : Kernel Ω ℝ) [IsMarkovKernel G] (hN : E.Noise)
    (hFB : E.PiSQ < E.PiFB) :
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, Signal.Pi E G n = E.PiSQ) ∧
    (HasDerivAt E.F 0 0 → Tendsto (Signal.Pi E G) atTop (𝓝 E.PiSQ)) ∧
    (∀ t > 0, HasDerivAt E.F t 0 → limsup (Signal.Pi E G) atTop < E.PiFB) :=
  Signal.prop_noisy_signals hN hFB

/-- **Equation `eq_noisy_signal_reporting_band`.** -/
theorem EqNoisySignalBand {E : Env A Ω} {G : Kernel Ω ℝ} [IsMarkovKernel G] (hN : E.Noise) {n : ℕ}
    (hn : 2 ≤ n) {d : Rule A} {s : Strat ℝ} (he : Signal.IsEq E G n d s) :
    ∀ᵐ ω ∂(E.prior : Measure Ω),
      E.Fm (-(Env.pivConst E.B E.epsStar / √(n : ℝ))) ≤ Signal.stateRp E G s ω ∧
        Signal.stateRp E G s ω ≤ E.F (Env.pivConst E.B E.epsStar / √(n : ℝ)) :=
  Signal.eq_noisy_signal_reporting_band hN hn he

/-! ### General message spaces -/

/-- **Equation `general_message_upper_bound`.** -/
theorem EqGeneralMessageUpperBound (D : RecordingData) :
    0 < D.kLo ∧ D.kLo ≤ D.kHi ∧ ∀ m y, D.kLo ≤ D.k m y ∧ D.k m y ≤ D.kHi :=
  ⟨D.kLo_pos, D.kLo_le_kHi, fun m y => ⟨D.kLo_le m y, D.le_kHi m y⟩⟩

/-- **Equation `eq_background_bounds`**: `q_ω ≥ εη`, and `P_ω` has a density `p_ω` on `[0,1]` with
`p_ω(y) ≥ ε(1-η) \underline k` for every `y`. -/
theorem EqBackgroundBounds (N : NoisyModel A Ω) (σ : MStrat Ω Msg) (ω : Ω) :
    N.ε * N.η ≤ N.nullObs σ ω ∧ ∃ p : I → ℝ, Measurable p ∧
      (∀ y, N.ε * (1 - N.η) * N.D.kLo ≤ p y) ∧
      N.obsI σ ω = (volume : Measure I).withDensity fun y => ENNReal.ofReal (p y) := by
  obtain ⟨p, hpm, hp, hobs⟩ := N.exists_obs_density σ ω
  exact ⟨N.eps_eta_le_nullObs σ ω, p, hpm, fun y => (hp y).1, hobs⟩

/-- The likelihood ratios in the proof of Lemma `lemma_anonymous_influence`: for every density `p_ω` of `P_ω` on
`[0,1]` as above, `w_m = NoisyModel.wRatio q_ω p_ω` is the density of `Q_m` with respect to `P_ω`, and
`0 ≤ w_m ≤ Λ`.  The proof of the lemma uses these `w_m`. -/
theorem LikelihoodRatios (N : NoisyModel A Ω) (σ : MStrat Ω Msg) (ω : Ω) {p : I → ℝ} (hpm : Measurable p)
    (hp : ∀ y, p y ∈ Icc (N.ε * (1 - N.η) * N.D.kLo) N.D.kHi)
    (hobs : N.obsI σ ω = (volume : Measure I).withDensity fun y => ENNReal.ofReal (p y)) (m : Msg) :
    (∀ z, NoisyModel.wRatio (N.nullObs σ ω) p N.D m z ∈ Icc 0 N.Lam) ∧
      N.D.recordK m = (N.game.obs σ ω).withDensity
        fun z => ENNReal.ofReal (NoisyModel.wRatio (N.nullObs σ ω) p N.D m z) :=
  N.record_eq_withDensity σ ω hpm hp hobs m

/-- The Bounds on `|U_{n,ω}(m) - E[V_ω]|` in the proof of Lemma `lemma_anonymous_influence`. -/
theorem AnonymousInfluenceMean (N : NoisyModel A Ω) {n : ℕ} (hn : 0 < n) (d : MRule A Msg n)
    (σ : MStrat Ω Msg) (ω : Ω) (i : Fin n) (m : Msg) :
    |N.game.U d σ ω i m - N.game.W d σ ω| ≤ (N.env.B / 2) * √((N.Lam - 1) / n) :=
  N.abs_U_sub_W hn d σ ω i m

/-- **Lemma `lemma_anonymous_influence`.** -/
theorem LemmaAnonymousInfluence (N : NoisyModel A Ω) {n : ℕ} (hn : 0 < n) (d : MRule A Msg n)
    (σ : MStrat Ω Msg) (ω : Ω) (i : Fin n) (m m' : Msg) :
    |N.game.U d σ ω i m - N.game.U d σ ω i m'| ≤ N.env.B * √(N.Lam - 1) / √(n : ℝ) :=
  N.anonymous_influence hn d σ ω i m m'

/-- **Equation `eq_rational_nonnull_message_bound`.** -/
theorem EqRationalNonnullBound (N : NoisyModel A Ω) {n : ℕ} (hn : 0 < n) {d : MRule A Msg n}
    {σ : MStrat Ω Msg} (he : N.game.IsEq d σ) (ω : Ω) :
    N.game.q σ ω ≤ N.env.F (N.MG / √(n : ℝ)) :=
  N.rational_nonnull_bound hn he ω

/-- **Equation `eq_likelihood_ratio_bound`**, as an inequality between measures. -/
theorem EqLikelihoodRatioBound (N : NoisyModel A Ω) (σ : MStrat Ω Msg) (ω : Ω) {S : Set Msg}
    (hS : MeasurableSet S) :
    |(N.game.obs σ ω).real S - N.game.baseObs.real S|
      ≤ (1 - N.ε) * N.Lam * N.game.q σ ω * N.game.baseObs.real S :=
  MsgGame.abs_obs_sub_le N.dom σ ω hS

/-- **Proposition `prop_general_message_upper_bounds`.** -/
theorem PropositionGeneralMessage (N : NoisyModel A Ω) (hFB : N.env.PiSQ < N.env.PiFB) :
    (∀ δ > 0, N.env.F δ = 0 → ∃ nStar : ℕ, ∀ n > nStar, N.game.Pi n = N.env.PiSQ) ∧
    (N.env.F 0 = 0 → HasDerivWithinAt N.env.F 0 (Ici 0) 0 → Tendsto N.game.Pi atTop (𝓝 N.env.PiSQ)) ∧
    (∀ t > 0, N.env.F 0 = 0 → HasDerivWithinAt N.env.F t (Ici 0) 0 →
      limsup N.game.Pi atTop < N.env.PiFB) :=
  N.prop_general_message hFB

/-- **Remark `remark_finite_message_noise`.** -/
theorem RemarkFiniteMessages {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Finite X]
    (E : Env A Ω) (x₀ : X) (χ : Measure X) [IsProbabilityMeasure χ] {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hc : (E.cost : Measure ℝ) (Iio 0) = 0) (hχ : ∀ x, 0 < χ.real {x}) (hFB : E.PiSQ < E.PiFB) :
    (finiteGame E x₀ χ ε h0 h1 hc).Dom (ε * chiMin χ)⁻¹ ∧
    (∀ {n : ℕ}, 0 < n → ∀ (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω) (i : Fin n) (m m' : X),
      |(finiteGame E x₀ χ ε h0 h1 hc).U d σ ω i m - (finiteGame E x₀ χ ε h0 h1 hc).U d σ ω i m'|
        ≤ E.B * √((ε * chiMin χ)⁻¹ - 1) / √(n : ℝ)) ∧
    (∀ δ > 0, E.F δ = 0 → ∃ nStar : ℕ, ∀ n > nStar, (finiteGame E x₀ χ ε h0 h1 hc).Pi n = E.PiSQ) ∧
    (E.F 0 = 0 → HasDerivWithinAt E.F 0 (Ici 0) 0 →
      Tendsto (finiteGame E x₀ χ ε h0 h1 hc).Pi atTop (𝓝 E.PiSQ)) ∧
    (∀ t > 0, E.F 0 = 0 → HasDerivWithinAt E.F t (Ici 0) 0 →
      limsup (finiteGame E x₀ χ ε h0 h1 hc).Pi atTop < E.PiFB) :=
  ⟨finite_dom E x₀ χ h0 h1 hc hχ, remark_finite E x₀ χ h0 h1 hc hχ hFB⟩

/-- **Remark `remark_continuum_message_noise`.** Without noisy recording, under the rule "`a = 1` iff two
identical nonnull messages are observed", let rational individuals send `m⋆` or `∅`.  With
`r = (1-ε) q_{n,ω}`, the payoff in state `ω` is `u(0,ω) + G(ω) Pr(Bin(n,r) ≥ 2)`, the gross benefit of sending
`m⋆` is `G(ω) Pr(Bin(n-1,r) = 1)`, and any other message has the value of `∅`.  These are the formulas of a
Volunteer's Dilemma with a threshold of two, in which mechanical individuals play no role. -/
theorem RemarkContinuumTwoMessages {E : Env Bool Bool} {ε η : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hc : (E.cost : Measure ℝ) (Iio 0) = 0) (t₀ : I) (p : Bool × ℝ → ℝ) (hp : Measurable p)
    (h01 : ∀ z, p z ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 2 ≤ n) (ω : Bool) (i : Fin n) :
    letI g := perfectGame E ε η h0 h1 hη0 hη1 hc
    letI σ := starStrat t₀ p hp h01
    g.W (twoRule n) σ ω = E.u false ω + VD.G E ω * btail n ((1 - ε) * g.q σ ω) 2 ∧
    g.U (twoRule n) σ ω i (mStar t₀) - g.U (twoRule n) σ ω i msgNull
      = VD.G E ω * rho (n - 1) ((1 - ε) * g.q σ ω) 2 ∧
    ∀ m : Msg, m ≠ mStar t₀ → g.U (twoRule n) σ ω i m = g.U (twoRule n) σ ω i msgNull :=
  remark_two_messages hη0 hη1 t₀ p hp h01 hn ω i

/-- **Remark `remark_continuum_message_noise`**, continued: the two-message rule has an equilibrium of this
form.  In state `1` types use the cutoff `H Pr(Bin(n-1,r) = 1)` for `r = (1-ε) p`, in state `0` they stay silent,
and the payoff is `Π^SQ + π H Pr(Bin(n,r) ≥ 2)`. -/
theorem RemarkContinuumTwoEquilibrium {E : Env Bool Bool} {ε η : ℝ} (hV : VD.Assumptions E) (h0 : 0 < ε)
    (h1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1) (hc : (E.cost : Measure ℝ) (Iio 0) = 0) (t₀ : I) {n : ℕ}
    (hn : 2 ≤ n) :
    ∃ (σ : MStrat Bool Msg) (p : ℝ), p ∈ Icc (0 : ℝ) 1 ∧
      E.Fm (VD.H E * rho (n - 1) ((1 - ε) * p) 2) ≤ p ∧
      p ≤ E.F (VD.H E * rho (n - 1) ((1 - ε) * p) 2) ∧
      (perfectGame E ε η h0 h1 hη0 hη1 hc).IsEq (twoRule n) σ ∧
      (perfectGame E ε η h0 h1 hη0 hη1 hc).payoff (twoRule n) σ
        = E.PiSQ + VD.pr E * VD.H E * btail n ((1 - ε) * p) 2 :=
  two_equilibrium hV hη0 hη1 t₀ hn

/-- A further result on Remark `remark_continuum_message_noise`, for the rule "investigate iff one fixed
message is observed", when messages are recorded exactly. -/
theorem RemarkContinuumMessages {E : Env Bool Bool} {ε η : ℝ} (hV : VD.Assumptions E) (h0 : 0 < ε)
    (h1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1) (hc : (E.cost : Measure ℝ) (Iio 0) = 0) {νhat : ℝ}
    (hνhat : νhat < VD.H E) (hF : 0 < E.F νhat) (t₀ : I) :
    ((volume : Measure I).prod (volume : Measure I)) {z | z.1 = z.2} = 0 ∧
    (∀ Λ : ℝ, ¬(perfectGame E ε η h0 h1 hη0 hη1 hc).Dom Λ) ∧
    (∃ κ > 0, ∀ n, 2 ≤ n → E.PiSQ + κ ≤ (perfectGame E ε η h0 h1 hη0 hη1 hc).Pi n) ∧
    (¬∃ nStar : ℕ, ∀ n > nStar, (perfectGame E ε η h0 h1 hη0 hη1 hc).Pi n = E.PiSQ) ∧
    ¬Tendsto (perfectGame E ε η h0 h1 hη0 hη1 hc).Pi atTop (𝓝 E.PiSQ) :=
  remark_continuum hV h0 h1 hη0 hη1 hc hνhat hF t₀

end OA

end NoisyVD

/-! ### Axiom audit -/

#print axioms NoisyVD.OA.PropositionStateDependent
#print axioms NoisyVD.OA.EqSdBand
#print axioms NoisyVD.OA.EqWorstSandwich
#print axioms NoisyVD.OA.PropositionWorstEquilibrium
#print axioms NoisyVD.OA.EqVdFixedPoint
#print axioms NoisyVD.OA.WorstCaseLimit
#print axioms NoisyVD.OA.WorstCaseCutoff
#print axioms NoisyVD.OA.PropositionNoisySignals
#print axioms NoisyVD.OA.EqNoisySignalBand
#print axioms NoisyVD.OA.EqGeneralMessageUpperBound
#print axioms NoisyVD.OA.EqBackgroundBounds
#print axioms NoisyVD.OA.LemmaAnonymousInfluence
#print axioms NoisyVD.OA.EqRationalNonnullBound
#print axioms NoisyVD.OA.EqLikelihoodRatioBound
#print axioms NoisyVD.OA.PropositionGeneralMessage
#print axioms NoisyVD.OA.RemarkFiniteMessages
#print axioms NoisyVD.OA.RemarkContinuumTwoMessages
#print axioms NoisyVD.OA.RemarkContinuumTwoEquilibrium
#print axioms NoisyVD.OA.RemarkContinuumMessages
#print axioms NoisyVD.OA.LikelihoodRatios
#print axioms NoisyVD.OA.AnonymousInfluenceMean
#print axioms NoisyVD.OA.Signal.integral_interim
#print axioms NoisyVD.OA.NoisyModel.baseObs_null
#print axioms NoisyVD.OA.NoisyModel.obs_null
#print axioms NoisyVD.OA.Examples.noisy_vs_perfect
#print axioms NoisyVD.OA.Examples.sdCommon_F
#print axioms NoisyVD.OA.Examples.sdDiff_F
#print axioms NoisyVD.OA.Signal.Pi_of_uninformative
#print axioms NoisyVD.OA.Signal.not_tendsto_PiFB_of_uninformative
#print axioms NoisyVD.OA.SDEnv.isEq_iff_bestResponse
#print axioms NoisyVD.OA.SDEnv.payoff_eq_profile
#print axioms NoisyVD.OA.Signal.isEq_iff_bestResponse
#print axioms NoisyVD.OA.Signal.payoff_eq_profile
#print axioms NoisyVD.OA.Examples.truncatedNormal
