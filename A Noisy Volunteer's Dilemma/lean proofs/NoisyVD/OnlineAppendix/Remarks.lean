import NoisyVD.OnlineAppendix.NoisyRecording
import NoisyVD.Existence

/-!
# Remarks `remark_finite_message_noise` and `remark_continuum_message_noise`

**Finite messages.** With finitely many messages, no recording noise, and mechanical behaviour with full
support `χ`, the domination condition holds with `Λ = (ε χ̲)⁻¹`, so Lemma `lemma_anonymous_influence`
and the three statements of Proposition `prop_general_message_upper_bounds` hold.

**Continuum messages.** Without noisy recording (`y_i = m_i`), two mechanical draws coincide with probability
zero and no single message `m ∈ [0,1]` is ever drawn, so mechanical individuals alone do not suffice.

* `remark_two_messages` and `two_equilibrium` are the remark itself.  Under the rule "`a = 1` iff two identical
  nonnull messages are observed", if rational individuals send `m⋆` or `∅`, the payoff and the reporting
  incentive are those of a Volunteer's Dilemma with a threshold of two, in which mechanical individuals play
  no role, and an equilibrium of this form exists.
* `remark_continuum` is a further result about the rule "investigate iff `m⋆` is observed".  The domination
  condition fails for every `Λ`, and for every `n ≥ 2` there is an equilibrium with payoff at least
  `Π^SQ + κ`, where `κ > 0` does not depend on `n`, even if `F` vanishes near zero.  So the conclusions of
  Statements 1 and 2 of the Proposition, which hold under noisy recording, fail here.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal

namespace NoisyVD

namespace OA

local notation "I" => unitInterval

/-! ### Finite messages -/

section Finite

variable {A Ω X : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [MeasurableSpace X] [MeasurableSingletonClass X] [Finite X]

/-- The game with a finite message space, no recording noise, and mechanical law `χ`. -/
noncomputable def finiteGame (E : Env A Ω) (x₀ : X) (χ : Measure X) [IsProbabilityMeasure χ] (ε : ℝ)
    (h0 : 0 < ε) (h1 : ε < 1) (hc : (E.cost : Measure ℝ) (Iio 0) = 0) : MsgGame A Ω X where
  env := E
  nullMsg := x₀
  record := Kernel.id
  record_markov := inferInstance
  mech := χ
  mech_prob := inferInstance
  ε := ε
  ε_pos := h0
  ε_lt := h1
  cost_nonneg := hc

/-- `\underline χ = min_m χ(m)`. -/
noncomputable def chiMin (χ : Measure X) : ℝ := sInf (range fun x => χ.real {x})

lemma chiMin_le (χ : Measure X) (x : X) : chiMin χ ≤ χ.real {x} :=
  csInf_le (Set.finite_range _).bddBelow ⟨x, rfl⟩

lemma chiMin_pos {χ : Measure X} (hχ : ∀ x, 0 < χ.real {x}) (x₀ : X) : 0 < chiMin χ := by
  have : Nonempty X := ⟨x₀⟩
  have hne : (range fun x => χ.real {x}).Nonempty := range_nonempty _
  obtain ⟨x, hx⟩ := (Set.finite_range _).isCompact.sInf_mem hne
  rw [chiMin, ← hx]
  exact hχ x

/-- With finitely many messages, the domination condition holds with `Λ = (ε χ̲)⁻¹`. -/
theorem finite_dom (E : Env A Ω) (x₀ : X) (χ : Measure X) [IsProbabilityMeasure χ] {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) (hc : (E.cost : Measure ℝ) (Iio 0) = 0) (hχ : ∀ x, 0 < χ.real {x}) :
    (finiteGame E x₀ χ ε h0 h1 hc).Dom (ε * chiMin χ)⁻¹ := by
  intro m S hS
  have hmin := chiMin_pos hχ x₀
  have hrec : (finiteGame E x₀ χ ε h0 h1 hc).record m = Measure.dirac m := Kernel.id_apply m
  have hnoise : (finiteGame E x₀ χ ε h0 h1 hc).noiseObs = χ := Measure.id_comp
  have hε : (finiteGame E x₀ χ ε h0 h1 hc).ε = ε := rfl
  rw [hrec, hnoise, hε]
  by_cases hm : m ∈ S
  · have h2 : (Measure.dirac m).real S = 1 := by
      simp [measureReal_def, Measure.dirac_apply' _ hS, hm]
    rw [h2]
    have h3 : χ.real {m} ≤ χ.real S := measureReal_mono (singleton_subset_iff.2 hm)
    have h4 : chiMin χ ≤ χ.real S := (chiMin_le χ m).trans h3
    have hpos : 0 < ε * chiMin χ := mul_pos h0 hmin
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    nlinarith
  · have h2 : (Measure.dirac m).real S = 0 := by
      simp [measureReal_def, Measure.dirac_apply' _ hS, hm]
    rw [h2]
    have hpos : 0 < ε * chiMin χ := mul_pos h0 hmin
    positivity

/-- **Remark `remark_finite_message_noise`.** Lemma `lemma_anonymous_influence` and Proposition
`prop_general_message_upper_bounds` hold for finite messages with `Λ = (ε χ̲)⁻¹`. -/
theorem remark_finite (E : Env A Ω) (x₀ : X) (χ : Measure X) [IsProbabilityMeasure χ] {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) (hc : (E.cost : Measure ℝ) (Iio 0) = 0) (hχ : ∀ x, 0 < χ.real {x})
    (hFB : E.PiSQ < E.PiFB) :
    (∀ {n : ℕ}, 0 < n → ∀ (d : MRule A X n) (σ : MStrat Ω X) (ω : Ω) (i : Fin n) (m m' : X),
      |(finiteGame E x₀ χ ε h0 h1 hc).U d σ ω i m - (finiteGame E x₀ χ ε h0 h1 hc).U d σ ω i m'|
        ≤ E.B * √((ε * chiMin χ)⁻¹ - 1) / √(n : ℝ)) ∧
    (∀ δ > 0, E.F δ = 0 → ∃ nStar : ℕ, ∀ n > nStar, (finiteGame E x₀ χ ε h0 h1 hc).Pi n = E.PiSQ) ∧
    (E.F 0 = 0 → HasDerivWithinAt E.F 0 (Ici 0) 0 →
      Tendsto (finiteGame E x₀ χ ε h0 h1 hc).Pi atTop (𝓝 E.PiSQ)) ∧
    (∀ t > 0, E.F 0 = 0 → HasDerivWithinAt E.F t (Ici 0) 0 →
      limsup (finiteGame E x₀ χ ε h0 h1 hc).Pi atTop < E.PiFB) :=
  ⟨fun hn d σ ω i m m' => MsgGame.anon_influence (finite_dom E x₀ χ h0 h1 hc hχ) hn d σ ω i m m',
    MsgGame.prop_upper (finite_dom E x₀ χ h0 h1 hc hχ) hFB⟩

end Finite

/-! ### Continuum messages -/

/-- The model without noisy recording: the decision-maker observes `y_i = m_i`. -/
noncomputable def perfectGame {A Ω : Type*} [TopologicalSpace A] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (E : Env A Ω) (ε η : ℝ) (h0 : 0 < ε) (h1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hc : (E.cost : Measure ℝ) (Iio 0) = 0) : MsgGame A Ω Msg where
  env := E
  nullMsg := msgNull
  record := Kernel.id
  record_markov := inferInstance
  mech := mechMsg η
  mech_prob := isProb_mix hη0.le hη1.le _ _
  ε := ε
  ε_pos := h0
  ε_lt := h1
  cost_nonneg := hc

/-- Two independent mechanical draws from `[0,1]` coincide with probability zero: if the decision-maker
observes two identical nonnull messages, she is certain they did not arise from noise. -/
theorem mechanical_draws_distinct :
    ((volume : Measure I).prod (volume : Measure I)) {z | z.1 = z.2} = 0 := by
  have hm : MeasurableSet {z : I × I | z.1 = z.2} := isClosed_eq continuous_fst continuous_snd |>.measurableSet
  rw [Measure.measure_prod_null hm]
  refine ae_of_all _ fun x => ?_
  have : Prod.mk x ⁻¹' {z : I × I | z.1 = z.2} = {x} := by
    ext y
    simp [eq_comm]
  show (volume : Measure I) (Prod.mk x ⁻¹' {z : I × I | z.1 = z.2}) = 0
  rw [this]
  exact measure_singleton x

section Continuum

variable {E : Env Bool Bool} {ε η : ℝ} {h0 : 0 < ε} {h1 : ε < 1} {hη0 : 0 < η} {hη1 : η < 1}
  {hc : (E.cost : Measure ℝ) (Iio 0) = 0}

/-- The message on which rational individuals coordinate. -/
abbrev mStar (t₀ : I) : Msg := Sum.inr t₀

lemma mStar_ne (t₀ : I) : (mStar t₀) ≠ msgNull := Sum.inr_ne_inl

/-- Under perfect recording no message `m ∈ [0,1]` has positive probability under the noise. -/
lemma mech_star (hη0 : 0 < η) (hη1 : η < 1) (t₀ : I) : (mechMsg η).real {mStar t₀} = 0 := by
  rw [mechMsg, mix_real hη0.le hη1.le]
  have h1 : (Measure.dirac msgNull).real {mStar t₀} = 0 := by
    simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
  have h2 : unifMsg.real {mStar t₀} = 0 := by
    have hpre : (Sum.inr ⁻¹' {mStar t₀} : Set I) = {t₀} := by
      ext t
      simp
    simp [measureReal_def, unifMsg, Measure.map_apply measurable_inr (measurableSet_singleton _), hpre]
  rw [h1, h2]
  ring

/-- Without noisy recording, the domination condition fails for every `Λ`. -/
theorem not_dom (t₀ : I) (Λ : ℝ) : ¬(perfectGame E ε η h0 h1 hη0 hη1 hc).Dom Λ := by
  intro h
  have h2 := h (mStar t₀) {mStar t₀} (measurableSet_singleton _)
  have hrec : (perfectGame E ε η h0 h1 hη0 hη1 hc).record (mStar t₀) = Measure.dirac (mStar t₀) :=
    Kernel.id_apply _
  have hnoise : (perfectGame E ε η h0 h1 hη0 hη1 hc).noiseObs = mechMsg η := Measure.id_comp
  rw [hrec, hnoise, mech_star hη0 hη1 t₀] at h2
  simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)] at h2
  linarith

/-! #### The rule "investigate iff `m⋆` is observed" -/

/-- Some individual's observed message is `m⋆`. -/
def hasStar (t₀ : I) (n : ℕ) : Set (Fin n → Msg) := {y | ∃ i, y i = mStar t₀}

lemma hasStar_compl (t₀ : I) (n : ℕ) :
    (hasStar t₀ n)ᶜ = Set.pi univ fun _ => ({mStar t₀} : Set Msg)ᶜ := by
  ext y
  simp [hasStar]

lemma measurableSet_hasStar (t₀ : I) (n : ℕ) : MeasurableSet (hasStar t₀ n) := by
  rw [← compl_compl (hasStar t₀ n), hasStar_compl]
  exact (MeasurableSet.univ_pi fun _ => (measurableSet_singleton _).compl).compl

open Classical in
/-- The rule "investigate iff `m⋆` is observed". -/
noncomputable def starRule (t₀ : I) (n : ℕ) : MRule Bool Msg n where
  κ := Kernel.piecewise (measurableSet_hasStar t₀ n) (Kernel.const _ (Measure.dirac true))
    (Kernel.const _ (Measure.dirac false))
  markov := inferInstance
  symm := fun τ y => by
    have h : y ∘ τ ∈ hasStar t₀ n ↔ y ∈ hasStar t₀ n := by
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨τ i, hi⟩
      · rintro ⟨i, hi⟩
        refine ⟨τ.symm i, ?_⟩
        simpa using hi
    simp only [Kernel.piecewise_apply, h, Kernel.const_apply]

variable (g : MsgGame Bool Bool Msg)

lemma V_star (t₀ : I) {n : ℕ} (ω : Bool) (y : Fin n → Msg) :
    g.V (starRule t₀ n) ω y
      = g.env.u true ω - VD.G g.env ω * (hasStar t₀ n)ᶜ.indicator (fun _ => (1 : ℝ)) y := by
  unfold MsgGame.V starRule
  simp only [Kernel.piecewise_apply, VD.G]
  by_cases hy : y ∈ hasStar t₀ n
  · simp [hy]
  · simp [hy]

/-- `∫ V dμ = u(1,ω) - G(ω) ∏_j (1 - μ_j(m⋆))` for a product law. -/
lemma integral_V_star (t₀ : I) {n : ℕ} (ω : Bool) (μ : Fin n → Measure Msg)
    [∀ j, IsProbabilityMeasure (μ j)] :
    ∫ y, g.V (starRule t₀ n) ω y ∂(Measure.pi μ)
      = g.env.u true ω - VD.G g.env ω * ∏ j, (1 - (μ j).real {mStar t₀}) := by
  have hbox : MeasurableSet (hasStar t₀ n)ᶜ := (measurableSet_hasStar t₀ n).compl
  simp_rw [V_star]
  have hint : Integrable ((hasStar t₀ n)ᶜ.indicator fun _ => (1 : ℝ)) (Measure.pi μ) :=
    (integrable_const _).indicator hbox
  rw [integral_sub (integrable_const _) (hint.const_mul _), integral_const_mul,
    integral_indicator_const _ hbox]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one]
  congr 2
  rw [hasStar_compl, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← measureReal_def, probReal_compl_eq_one_sub (measurableSet_singleton _)]

/-! #### The strategy -/

/-- `σ(ω,x)`: send `m⋆` with probability `p(ω,x)` and `∅` otherwise. -/
noncomputable def starStrat (t₀ : I) (p : Bool × ℝ → ℝ) (hp : Measurable p)
    (h01 : ∀ z, p z ∈ Icc (0 : ℝ) 1) : MStrat Bool Msg where
  κ := {
    toFun := fun z => mix (p z) (Measure.dirac (mStar t₀)) (Measure.dirac msgNull)
    measurable' := by
      refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
      simp only [mix_apply]
      exact (ENNReal.measurable_ofReal.comp hp).mul_const _ |>.add
        ((ENNReal.measurable_ofReal.comp (measurable_const.sub hp)).mul_const _) }
  markov := ⟨fun z => isProb_mix (h01 z).1 (h01 z).2 _ _⟩

lemma ae_mix {p : ℝ} (t₀ : I) {P : Msg → Prop} (hs : 0 < p → P (mStar t₀))
    (hn : p < 1 → P msgNull) :
    ∀ᵐ m ∂(mix p (Measure.dirac (mStar t₀)) (Measure.dirac msgNull)), P m := by
  unfold mix
  rw [ae_add_measure_iff]
  constructor
  · by_cases hp : 0 < p
    · rw [Measure.ae_ennreal_smul_measure_iff (by simpa using hp), ae_dirac_eq]
      exact Filter.eventually_pure.2 (hs hp)
    · have : ENNReal.ofReal p = 0 := ENNReal.ofReal_eq_zero.2 (not_lt.1 hp)
      simp [this]
  · by_cases hp : p < 1
    · rw [Measure.ae_ennreal_smul_measure_iff (by simpa using hp), ae_dirac_eq]
      exact Filter.eventually_pure.2 (hn hp)
    · have : ENNReal.ofReal (1 - p) = 0 := ENNReal.ofReal_eq_zero.2 (by linarith [not_lt.1 hp])
      simp [this]

/-! #### The fixed point -/

/-- A continuous gross benefit has a fixed point of `F(φ(p)⁻) ≤ p ≤ F(φ(p))`. -/
lemma exists_fp (E : Env Bool Bool) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∃ p ∈ Icc (0 : ℝ) 1, E.Fm (φ p) ≤ p ∧ p ≤ E.F (φ p) := by
  let G : Set ℝ := Icc 0 1 ∩ {p | E.Fm (φ p) ≤ p}
  have hlsc : LowerSemicontinuous fun p => E.Fm (φ p) := fun z y hy =>
    hφ.continuousAt.eventually (E.lowerSemicontinuous_Fm (φ z) y hy)
  have hcl : IsClosed G :=
    isClosed_Icc.inter (hlsc.isClosed_epigraph.preimage (continuous_id.prodMk continuous_id))
  have hne : G.Nonempty := ⟨1, ⟨by simp, measureReal_le_one⟩⟩
  have hbdd : BddBelow G := ⟨0, fun p hp => hp.1.1⟩
  have hq : sInf G ∈ G := hcl.csInf_mem hne hbdd
  set q := sInf G with hqdef
  refine ⟨q, hq.1, hq.2, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨y', hy1, hy2⟩ := exists_between hcon
  have husc : ∀ᶠ y in 𝓝 q, E.F (φ y) < y' :=
    hφ.continuousAt.eventually (E.upperSemicontinuous_F _ y' hy1)
  have hlt : ∀ᶠ y in 𝓝[<] q, y' < y := by
    filter_upwards [Ioo_mem_nhdsLT hy2] with y hy using hy.1
  have hlt2 : ∀ᶠ y in 𝓝[<] q, y < q := eventually_mem_nhdsWithin
  obtain ⟨y, hy3, hy4, hy5⟩ := ((husc.filter_mono nhdsWithin_le_nhds).and (hlt.and hlt2)).exists
  have hq0 : 0 ≤ y' := (E.F_nonneg _).trans hy1.le
  have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨hq0.trans hy4.le, hy5.le.trans hq.1.2⟩
  have hnot : y ∉ G := fun h => absurd (csInf_le hbdd h) (not_le.2 hy5)
  have hy6 : y < E.Fm (φ y) := by
    by_contra h
    exact hnot ⟨hy01, not_lt.1 h⟩
  have := E.Fm_le_F (φ y)
  linarith

/-! #### The equilibrium -/

/-- Perfect recording: an equilibrium of the game with the rule "investigate iff `m⋆` is observed", and
its payoff. -/
theorem star_equilibrium (hV : VD.Assumptions E) (h0 : 0 < ε) (h1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hc : (E.cost : Measure ℝ) (Iio 0) = 0) (t₀ : I) {n : ℕ} :
    ∃ (σ : MStrat Bool Msg) (p : ℝ), p ∈ Icc (0 : ℝ) 1 ∧
      E.Fm (VD.H E * (1 - (1 - ε) * p) ^ (n - 1)) ≤ p ∧
      p ≤ E.F (VD.H E * (1 - (1 - ε) * p) ^ (n - 1)) ∧
      (perfectGame E ε η h0 h1 hη0 hη1 hc).IsEq (starRule t₀ n) σ ∧
      (perfectGame E ε η h0 h1 hη0 hη1 hc).payoff (starRule t₀ n) σ
        = E.PiSQ + VD.pr E * VD.H E * (1 - (1 - (1 - ε) * p) ^ n) := by
  set g := perfectGame E ε η h0 h1 hη0 hη1 hc with hg
  have hH := hV.H_pos
  have hL := hV.L_neg
  have hε1 : 0 < 1 - ε := by linarith
  -- the fixed point
  have hφc : Continuous fun p : ℝ => VD.H E * (1 - (1 - ε) * p) ^ (n - 1) := by fun_prop
  obtain ⟨p, hp01, hp1, hp2⟩ := exists_fp E hφc
  set c := VD.H E * (1 - (1 - ε) * p) ^ (n - 1) with hcdef
  obtain ⟨s, hsrp, hs1, hs2⟩ := E.exists_cutoff_strategy (q := fun _ => p) (c := fun _ => c)
    measurable_const measurable_const fun _ => ⟨hp1, hp2⟩
  let f : ℝ → ℝ := s.σ true
  have hfm : Measurable f := Env.Strat.measurable_slice s true
  have hfmem : ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun x => s.mem true x
  have hfint : ∫ x, f x ∂(E.cost : Measure ℝ) = p := hsrp true
  -- the strategy
  let P : Bool × ℝ → ℝ := fun z => if z.1 then f z.2 else 0
  have hPm : Measurable P := by
    refine measurable_from_prod_countable_right fun b => ?_
    cases b
    · simp [P]
    · simpa [P] using hfm
  have hP01 : ∀ z, P z ∈ Icc (0 : ℝ) 1 := fun z => by
    simp only [P]
    split_ifs
    · exact hfmem _
    · simp
  let σ := starStrat t₀ P hPm hP01
  -- the law of the observations
  have hσapply : ∀ ω x, σ.κ (ω, x) = mix (P (ω, x)) (Measure.dirac (mStar t₀)) (Measure.dirac msgNull) :=
    fun _ _ => rfl
  have hdiracS : (Measure.dirac (mStar t₀)).real {mStar t₀} = 1 := by
    simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
  have hdiracN : (Measure.dirac msgNull).real {mStar t₀} = 0 := by
    simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
  have hrat : ∀ ω x, (g.ratKernel σ ω x).real {mStar t₀} = P (ω, x) := fun ω x => by
    rw [MsgGame.ratKernel_apply]
    have hrec : g.record = Kernel.id := rfl
    rw [hrec, Measure.id_comp, hσapply, mix_real (hP01 _).1 (hP01 _).2, hdiracS, hdiracN]
    ring
  have hratObs : ∀ ω, (g.ratObs σ ω).real {mStar t₀} = ∫ x, P (ω, x) ∂(E.cost : Measure ℝ) := fun ω => by
    unfold MsgGame.ratObs
    rw [real_bind _ (measurableSet_singleton _)]
    simp_rw [hrat]
    rfl
  have hnoise : g.noiseObs = mechMsg η := Measure.id_comp
  let ρ : Bool → ℝ := fun ω => if ω then (1 - ε) * p else 0
  have hobs : ∀ ω, (g.obs σ ω).real {mStar t₀} = ρ ω := fun ω => by
    have hg1 : g.ε = ε := rfl
    unfold MsgGame.obs
    rw [mix_real g.ε_pos.le g.ε_lt.le, hratObs, hnoise, mech_star hη0 hη1 t₀, hg1]
    cases ω
    · simp [P, ρ]
    · simp only [P, ite_true, ρ]
      show _ + _ * ∫ x, f x ∂(E.cost : Measure ℝ) = _
      rw [hfint]
      ring
  have hρ01 : ∀ ω, ρ ω ∈ Icc (0 : ℝ) 1 := fun ω => by
    simp only [ρ]
    split_ifs
    · constructor <;> nlinarith [hp01.1, hp01.2]
    · simp
  -- the value of each message
  have hU : ∀ (ω : Bool) (i : Fin n) (m : Msg), g.U (starRule t₀ n) σ ω i m
      = E.u true ω - VD.G E ω * ((if m = mStar t₀ then 0 else 1) * (1 - ρ ω) ^ (n - 1)) := by
    intro ω i m
    have := MsgGame.isProb_update (n := n) (g.obs σ ω) (g.record m) i
    unfold MsgGame.U
    rw [integral_V_star g t₀ ω]
    have hu : g.env = E := rfl
    rw [hu]
    congr 2
    have hrecm : g.record m = Measure.dirac m := Kernel.id_apply m
    have hfun : ∀ j, (1 - (Function.update (fun _ : Fin n => g.obs σ ω) i (g.record m) j).real {mStar t₀})
        = Function.update (fun _ : Fin n => 1 - ρ ω) i (if m = mStar t₀ then 0 else 1) j := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, hrecm]
        by_cases hm : m = mStar t₀
        · subst hm
          simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
        · simp [measureReal_def, hm, Measure.dirac_apply' _ (measurableSet_singleton _)]
      · simp only [Function.update_of_ne hj, hobs]
    simp_rw [hfun]
    rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp only [Finset.prod_const]
    congr 2
    rw [Finset.card_sdiff_of_subset (by simp)]
    simp
  have hW : ∀ ω, g.W (starRule t₀ n) σ ω = E.u true ω - VD.G E ω * (1 - ρ ω) ^ n := by
    intro ω
    unfold MsgGame.W
    rw [integral_V_star g t₀ ω]
    simp [hobs]
    rfl
  refine ⟨σ, p, hp01, hp1, hp2, ?_, ?_⟩
  · -- the best responses
    intro ω
    have hax : ∀ᵐ x ∂(g.env.cost : Measure ℝ), 0 ≤ x := MsgGame.ae_cost_nonneg
    filter_upwards [hax] with x hx
    have hN : g.nullMsg = msgNull := rfl
    have hcN : g.msgCost msgNull x = 0 := MsgGame.msgCost_null x
    have hcS : g.msgCost (mStar t₀) x = x := MsgGame.msgCost_ne (mStar_ne t₀) x
    have hcO : ∀ m : Msg, m ≠ msgNull → g.msgCost m x = x := fun m hm => MsgGame.msgCost_ne hm x
    set y := (1 - ρ ω) ^ (n - 1) with hy
    have hy0 : 0 ≤ y := pow_nonneg (by linarith [(hρ01 ω).2]) _
    -- the three kinds of messages
    have hnetS : ∀ i, g.netU (starRule t₀ n) σ ω i (mStar t₀) x = E.u true ω - x := fun i => by
      simp [MsgGame.netU, hU, hcS]
    have hnetN : ∀ i, g.netU (starRule t₀ n) σ ω i msgNull x = E.u true ω - VD.G E ω * y := fun i => by
      simp [MsgGame.netU, hU, hcN, Ne.symm (mStar_ne t₀), hy]
    have hnetO : ∀ i (m : Msg), m ≠ mStar t₀ → m ≠ msgNull →
        g.netU (starRule t₀ n) σ ω i m x = E.u true ω - VD.G E ω * y - x := fun i m h1' h2' => by
      simp [MsgGame.netU, hU, hcO m h2', h1', hy]
    have hval : ∀ i (m' : Msg), g.netU (starRule t₀ n) σ ω i m' x = E.u true ω - x ∨
        g.netU (starRule t₀ n) σ ω i m' x = E.u true ω - VD.G E ω * y ∨
        g.netU (starRule t₀ n) σ ω i m' x = E.u true ω - VD.G E ω * y - x := fun i m' => by
      by_cases h1' : m' = mStar t₀
      · left
        rw [h1', hnetS]
      · by_cases h2' : m' = msgNull
        · right; left
          rw [h2', hnetN]
        · right; right
          exact hnetO i m' h1' h2'
    rw [hσapply]
    refine ae_mix t₀ ?_ ?_
    · intro hpos i m'
      rw [hnetS]
      cases ω with
      | false =>
        simp [P] at hpos
      | true =>
        have hPf : P (true, x) = f x := by simp [P]
        rw [hPf] at hpos
        have hxc : x ≤ c := by
          by_contra hcon
          have := hs2 true x (not_le.1 hcon)
          have hf0 : f x = 0 := this
          linarith
        have hG : VD.G E true = VD.H E := rfl
        have hyy : y = (1 - (1 - ε) * p) ^ (n - 1) := by simp [hy, ρ]
        have hGy : VD.G E true * y = c := by rw [hG, hyy]
        rcases hval i m' with h | h | h
        · rw [h]
        · rw [h, hGy]
          linarith
        · rw [h, hGy]
          have : 0 ≤ c := by rw [← hGy, hG]; positivity
          linarith
    · intro hlt i m'
      rw [hnetN]
      cases ω with
      | false =>
        have hyy : y = 1 := by simp [hy, ρ]
        have hG : VD.G E false = VD.L E := rfl
        rcases hval i m' with h | h | h
        · rw [h, hyy, hG]
          linarith
        · rw [h]
        · rw [h]
          linarith
      | true =>
        have hPf : P (true, x) = f x := by simp [P]
        rw [hPf] at hlt
        have hcx : c ≤ x := by
          by_contra hcon
          have := hs1 true x (not_le.1 hcon)
          have hf1 : f x = 1 := this
          linarith
        have hG : VD.G E true = VD.H E := rfl
        have hyy : y = (1 - (1 - ε) * p) ^ (n - 1) := by simp [hy, ρ]
        have hGy : VD.G E true * y = c := by rw [hG, hyy]
        rcases hval i m' with h | h | h
        · rw [h, hGy]
          linarith
        · rw [h]
        · rw [h]
          linarith
  · -- the payoff
    unfold MsgGame.payoff
    have hpr : (g.env.prior : Measure Bool) = (E.prior : Measure Bool) := rfl
    rw [hpr]
    simp_rw [hW]
    rw [VD.integral_bool, VD.PiSQ_eq' hV]
    simp only [ρ, ite_true, Bool.false_eq_true, ite_false, sub_zero, one_pow, mul_one]
    have h1' : VD.G E true = VD.H E := rfl
    have h0' : VD.G E false = VD.L E := rfl
    rw [h1', h0']
    unfold VD.H VD.L
    ring

/-- **Without noisy recording, the conclusion of the Proposition fails.** If some type below `H` has
positive probability, then for every `n ≥ 2` there is an equilibrium with payoff at least `Π^SQ + κ`,
with `κ > 0` independent of `n`. -/
theorem perfect_lower (hV : VD.Assumptions E) (h0 : 0 < ε) (h1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hc : (E.cost : Measure ℝ) (Iio 0) = 0) {νhat : ℝ} (hνhat : νhat < VD.H E) (hF : 0 < E.F νhat)
    (t₀ : I) : ∃ κ > 0, ∀ n, 2 ≤ n → E.PiSQ + κ ≤ (perfectGame E ε η h0 h1 hη0 hη1 hc).Pi n := by
  set g := perfectGame E ε η h0 h1 hη0 hη1 hc with hg
  have hH := hV.H_pos
  have hε1 : 0 < 1 - ε := by linarith
  set ybar := max (νhat / VD.H E) (1 - (1 - ε) * E.F νhat) with hybar
  have hybar1 : ybar < 1 := by
    refine max_lt ?_ ?_
    · rw [div_lt_one hH]
      exact hνhat
    · have := mul_pos hε1 hF
      linarith
  have hpr := hV.pr_pos
  refine ⟨VD.pr E * VD.H E * (1 - ybar), by have := mul_pos hpr hH; nlinarith, fun n hn => ?_⟩
  obtain ⟨σ, p, hp01, hp1, hp2, he, hpay⟩ := star_equilibrium (η := η) (n := n) hV h0 h1 hη0 hη1 hc t₀
  set b := 1 - (1 - ε) * p with hb
  have hb0 : 0 ≤ b := by nlinarith [hp01.1, hp01.2]
  have hb1 : b ≤ 1 := by nlinarith [hp01.1, hp01.2]
  have hy : b ^ (n - 1) ≤ ybar := by
    by_cases hcase : VD.H E * b ^ (n - 1) ≤ νhat
    · refine le_trans ?_ (le_max_left _ _)
      rw [le_div_iff₀ hH]
      linarith
    · refine le_trans ?_ (le_max_right _ _)
      have h3 : E.F νhat ≤ E.Fm (VD.H E * b ^ (n - 1)) := E.F_le_Fm (not_le.1 hcase)
      have h4 : E.F νhat ≤ p := h3.trans hp1
      have h5 : b ≤ 1 - (1 - ε) * E.F νhat := by
        have := mul_le_mul_of_nonneg_left h4 hε1.le
        rw [hb]
        linarith
      have h6 : b ^ (n - 1) ≤ b ^ 1 := pow_le_pow_of_le_one hb0 hb1 (by omega)
      rw [pow_one] at h6
      linarith
  have hyn : b ^ n ≤ ybar := (pow_le_pow_of_le_one hb0 hb1 (by omega : n - 1 ≤ n)).trans hy
  have hmem : g.payoff (starRule t₀ n) σ ∈ g.payoffs n := ⟨_, σ, he, rfl⟩
  have hle : g.payoff (starRule t₀ n) σ ≤ g.Pi n := le_csSup ⟨_, MsgGame.le_PiFB n⟩ hmem
  refine le_trans ?_ hle
  rw [hpay]
  have : VD.pr E * VD.H E * (1 - ybar) ≤ VD.pr E * VD.H E * (1 - b ^ n) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_pos hpr hH).le
  linarith

/-- A further result on Remark `remark_continuum_message_noise`, for the rule "investigate iff `m⋆` is
observed".  Without noisy recording: two mechanical draws coincide
with probability zero; the domination condition fails for every `Λ`; and the decision-maker's payoff stays
above `Π^SQ + κ` for every `n ≥ 2`, so the conclusions of Statements 1 and 2 of the Proposition fail,
even when `F` vanishes near zero. -/
theorem remark_continuum (hV : VD.Assumptions E) (h0 : 0 < ε) (h1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hc : (E.cost : Measure ℝ) (Iio 0) = 0) {νhat : ℝ} (hνhat : νhat < VD.H E) (hF : 0 < E.F νhat)
    (t₀ : I) :
    ((volume : Measure I).prod (volume : Measure I)) {z | z.1 = z.2} = 0 ∧
    (∀ Λ : ℝ, ¬(perfectGame E ε η h0 h1 hη0 hη1 hc).Dom Λ) ∧
    (∃ κ > 0, ∀ n, 2 ≤ n → E.PiSQ + κ ≤ (perfectGame E ε η h0 h1 hη0 hη1 hc).Pi n) ∧
    (¬∃ nStar : ℕ, ∀ n > nStar, (perfectGame E ε η h0 h1 hη0 hη1 hc).Pi n = E.PiSQ) ∧
    ¬Tendsto (perfectGame E ε η h0 h1 hη0 hη1 hc).Pi atTop (𝓝 E.PiSQ) := by
  obtain ⟨κ, hκ, hlow⟩ := perfect_lower (η := η) hV h0 h1 hη0 hη1 hc hνhat hF t₀
  refine ⟨mechanical_draws_distinct, fun Λ => not_dom t₀ Λ, ⟨κ, hκ, hlow⟩, ?_, ?_⟩
  · rintro ⟨N, hN⟩
    have h1' := hN (max N 2 + 1) (by have := le_max_left N 2; omega)
    have h2' := hlow (max N 2 + 1) (by have := le_max_right N 2; omega)
    linarith
  · intro hlim
    have hev : ∀ᶠ n in atTop, (perfectGame E ε η h0 h1 hη0 hη1 hc).Pi n < E.PiSQ + κ :=
      (tendsto_order.1 hlim).2 _ (by linarith)
    obtain ⟨n, hn1, hn2⟩ := (hev.and (eventually_ge_atTop 2)).exists
    have := hlow n hn2
    linarith

/-! #### The two-message rule of Remark `remark_continuum_message_noise` -/

/-- Two individuals' observed messages are identical and nonnull. -/
def twoEvent (n : ℕ) : Set (Fin n → Msg) := {y | ∃ i j, i ≠ j ∧ y i = y j ∧ y i ≠ msgNull}

/-- An injective measurable coding of messages, used for measurability of the diagonal. -/
noncomputable def msgCode : Msg → ℝ := Sum.elim (fun _ => -1) fun t => (t : ℝ)

lemma measurable_msgCode : Measurable msgCode :=
  measurable_fun_sum measurable_const continuous_subtype_val.measurable

lemma msgCode_inj {a b : Msg} (h : msgCode a = msgCode b) : a = b := by
  have hinl : ∀ (u : Unit) (t : I), (-1 : ℝ) ≠ (t : ℝ) := fun _ t h => by
    have := t.2.1
    linarith
  rcases a with u | t <;> rcases b with v | t'
  · rfl
  · exact absurd h (hinl u t')
  · exact absurd h.symm (hinl v t)
  · have : (t : ℝ) = t' := h
    rw [Subtype.ext this]

lemma measurableSet_msg_eq {T : Type*} [MeasurableSpace T] {f h : T → Msg} (hf : Measurable f)
    (hh : Measurable h) : MeasurableSet {y | f y = h y} := by
  have : {y | f y = h y} = {y | msgCode (f y) = msgCode (h y)} := by
    ext y
    exact ⟨fun e => congrArg msgCode (show f y = h y from e), fun e => msgCode_inj e⟩
  rw [this]
  exact measurableSet_eq_fun (measurable_msgCode.comp hf) (measurable_msgCode.comp hh)

lemma measurableSet_twoEvent (n : ℕ) : MeasurableSet (twoEvent n) := by
  have : twoEvent n = ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {y : Fin n → Msg | y i = y j} ∩ {y | y i ≠ msgNull} := by
    ext y
    simp only [twoEvent, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
  rw [this]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => ?_
  refine (measurableSet_msg_eq (measurable_pi_apply i) (measurable_pi_apply j)).inter ?_
  have hm : Measurable fun y : Fin n → Msg => y i := measurable_pi_apply i
  exact hm (measurableSet_singleton msgNull).compl

open Classical in
/-- The rule of Remark `remark_continuum_message_noise`: `a = 1` iff two identical nonnull messages are
observed. -/
noncomputable def twoRule (n : ℕ) : MRule Bool Msg n where
  κ := Kernel.piecewise (measurableSet_twoEvent n) (Kernel.const _ (Measure.dirac true))
    (Kernel.const _ (Measure.dirac false))
  markov := inferInstance
  symm := fun τ y => by
    have h : y ∘ τ ∈ twoEvent n ↔ y ∈ twoEvent n := by
      constructor
      · rintro ⟨i, j, hij, h1, h2⟩
        exact ⟨τ i, τ j, fun h => hij (τ.injective h), h1, h2⟩
      · rintro ⟨i, j, hij, h1, h2⟩
        refine ⟨τ.symm i, τ.symm j, fun h => hij (τ.symm.injective h), ?_, ?_⟩ <;> simpa using ‹_›
    simp only [Kernel.piecewise_apply, h, Kernel.const_apply]

lemma V_two {n : ℕ} (ω : Bool) (y : Fin n → Msg) :
    g.V (twoRule n) ω y
      = g.env.u false ω + VD.G g.env ω * (twoEvent n).indicator (fun _ => (1 : ℝ)) y := by
  unfold MsgGame.V twoRule
  simp only [Kernel.piecewise_apply, VD.G]
  by_cases hy : y ∈ twoEvent n
  · simp [hy]
  · simp [hy]

/-- At least two observed messages equal `m⋆`. -/
def twoStar (t₀ : I) (n : ℕ) : Set (Fin n → Msg) := {y | ∃ i j, i ≠ j ∧ y i = mStar t₀ ∧ y j = mStar t₀}

lemma twoStar_subset (t₀ : I) (n : ℕ) : twoStar t₀ n ⊆ twoEvent n := by
  rintro y ⟨i, j, hij, h1, h2⟩
  exact ⟨i, j, hij, h1.trans h2.symm, by rw [h1]; exact mStar_ne t₀⟩

/-- At most one observed message equals `m⋆`, as a disjoint union of boxes. -/
def noStarBox (t₀ : I) (n : ℕ) : Set (Fin n → Msg) := Set.pi univ fun _ => ({mStar t₀} : Set Msg)ᶜ

/-- Exactly the message of individual `i` equals `m⋆`. -/
def oneStarBox (t₀ : I) {n : ℕ} (i : Fin n) : Set (Fin n → Msg) :=
  Set.pi univ (Function.update (fun _ => ({mStar t₀} : Set Msg)ᶜ) i {mStar t₀})

lemma compl_twoStar (t₀ : I) (n : ℕ) :
    (twoStar t₀ n)ᶜ = noStarBox t₀ n ∪ ⋃ i ∈ (Finset.univ : Finset (Fin n)), oneStarBox t₀ i := by
  ext y
  simp only [twoStar, noStarBox, oneStarBox, mem_compl_iff, mem_ofPred_eq, not_exists, not_and,
    mem_union, Set.mem_pi, mem_univ, forall_true_left, Finset.mem_univ, iUnion_true, mem_iUnion,
    mem_singleton_iff]
  constructor
  · intro h
    by_cases hex : ∃ i, y i = mStar t₀
    · obtain ⟨i, hi⟩ := hex
      right
      refine ⟨i, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj
        simpa using hi
      · rw [Function.update_of_ne hj]
        exact fun hj' => h i j (Ne.symm hj) hi hj'
    · left
      push Not at hex
      exact hex
  · rintro (h | ⟨k, hk⟩) i j hij hi hj
    · exact h i hi
    · have hki : ∀ l, y l = mStar t₀ → l = k := fun l hl => by
        by_contra hne
        have := hk l
        rw [Function.update_of_ne hne] at this
        exact this hl
      exact hij ((hki i hi).trans (hki j hj).symm)

lemma disjoint_boxes (t₀ : I) {n : ℕ} :
    Disjoint (noStarBox t₀ n) (⋃ i ∈ (Finset.univ : Finset (Fin n)), oneStarBox t₀ i) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  simp only [Finset.mem_univ, iUnion_true, mem_iUnion] at hy'
  obtain ⟨k, hk⟩ := hy'
  have h1 := hk k (mem_univ k)
  simp only [Function.update_self, mem_singleton_iff] at h1
  exact hy k (mem_univ k) h1

lemma pairwise_oneStar (t₀ : I) {n : ℕ} :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (oneStarBox (n := n) t₀) := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro y hi hj
  have h1 := hi i (mem_univ i)
  simp only [Function.update_self, mem_singleton_iff] at h1
  have h2 := hj i (mem_univ i)
  rw [Function.update_of_ne hij] at h2
  exact h2 h1

lemma measurableSet_noStar (t₀ : I) (n : ℕ) : MeasurableSet (noStarBox t₀ n) :=
  MeasurableSet.univ_pi fun _ => (measurableSet_singleton _).compl

lemma measurableSet_oneStar (t₀ : I) {n : ℕ} (i : Fin n) : MeasurableSet (oneStarBox t₀ i) := by
  refine MeasurableSet.univ_pi fun j => ?_
  by_cases hj : j = i
  · subst hj
    simp
  · rw [Function.update_of_ne hj]
    exact (measurableSet_singleton _).compl

/-- `Pr(at most one observed message equals m⋆)` under a product law. -/
noncomputable def atMostOne {n : ℕ} (r : Fin n → ℝ) : ℝ :=
  ∏ j, (1 - r j) + ∑ i, r i * ∏ j ∈ Finset.univ.erase i, (1 - r j)

lemma real_compl_twoStar (t₀ : I) {n : ℕ} (μ : Fin n → Measure Msg) [∀ j, IsProbabilityMeasure (μ j)] :
    (Measure.pi μ).real (twoStar t₀ n)ᶜ = atMostOne fun j => (μ j).real {mStar t₀} := by
  rw [compl_twoStar, measureReal_union (disjoint_boxes t₀)
    (Finset.measurableSet_biUnion _ fun i _ => measurableSet_oneStar t₀ i) (measure_ne_top _ _)
    (measure_ne_top _ _),
    measureReal_biUnion_finset (pairwise_oneStar t₀) (fun i _ => measurableSet_oneStar t₀ i)
      (fun _ _ => measure_ne_top _ _)]
  unfold atMostOne
  congr 1
  · rw [noStarBox, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← measureReal_def, probReal_compl_eq_one_sub (measurableSet_singleton _)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [oneStarBox, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp only [Function.update_self]
      rfl
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), ← measureReal_def,
        probReal_compl_eq_one_sub (measurableSet_singleton _)]

/-- Two independent messages coincide outside `∅` and `m⋆` with probability zero, if the second law has
no atoms there. -/
lemma pair_null (t₀ : I) {n : ℕ} (μ : Fin n → Measure Msg) [∀ j, IsProbabilityMeasure (μ j)] {i j : Fin n}
    (hij : i ≠ j) (h : ∀ a, a ≠ msgNull → a ≠ mStar t₀ → μ j {a} = 0) :
    Measure.pi μ {y : Fin n → Msg | y i = y j ∧ y i ≠ msgNull ∧ y i ≠ mStar t₀} = 0 := by
  let D : Set (Msg × Msg) := {z | z.1 = z.2 ∧ z.1 ≠ msgNull ∧ z.1 ≠ mStar t₀}
  have hD : MeasurableSet D :=
    (measurableSet_msg_eq measurable_fst measurable_snd).inter
      ((measurable_fst (measurableSet_singleton msgNull).compl).inter
        (measurable_fst (measurableSet_singleton (mStar t₀)).compl))
  have hind := (ProbabilityTheory.iIndepFun_pi (μ := μ) (X := fun _ x => x)
    (fun _ => aemeasurable_id)).indepFun hij
  have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).1 hind
  have hi : (Measure.pi μ).map (fun y => y i) = μ i := (measurePreserving_eval μ i).map_eq
  have hj : (Measure.pi μ).map (fun y => y j) = μ j := (measurePreserving_eval μ j).map_eq
  rw [hi, hj] at hmap
  have heq : (Measure.pi μ) {y : Fin n → Msg | y i = y j ∧ y i ≠ msgNull ∧ y i ≠ mStar t₀}
      = ((μ i).prod (μ j)) D := by
    rw [← hmap, Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hD]
    rfl
  rw [heq, Measure.measure_prod_null hD]
  refine ae_of_all _ fun a => ?_
  show μ j (Prod.mk a ⁻¹' D) = 0
  by_cases ha : a ≠ msgNull ∧ a ≠ mStar t₀
  · have : Prod.mk a ⁻¹' D ⊆ {a} := fun b hb => (hb.1).symm
    exact measure_mono_null this (h a ha.1 ha.2)
  · have : Prod.mk a ⁻¹' D = ∅ := by
      ext b
      simp only [D, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨_, h2, h3⟩
      exact ha ⟨h2, h3⟩
    rw [this, measure_empty]

/-- Messages other than `∅` and `m⋆` coincide with probability zero: the event of two identical nonnull
messages is, up to a null set, the event of two messages equal to `m⋆`.  This is where the noise is removed:
two mechanical draws never coincide. -/
lemma pi_twoEvent_diff_null (t₀ : I) {n : ℕ} (μ : Fin n → Measure Msg) [∀ j, IsProbabilityMeasure (μ j)]
    (hμ : ∀ i j, i ≠ j → (∀ a, a ≠ msgNull → a ≠ mStar t₀ → μ j {a} = 0) ∨
      ∀ a, a ≠ msgNull → a ≠ mStar t₀ → μ i {a} = 0) :
    Measure.pi μ (twoEvent n \ twoStar t₀ n) = 0 := by
  have hsub : twoEvent n \ twoStar t₀ n ⊆
      ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {y : Fin n → Msg | y i = y j ∧ y i ≠ msgNull ∧ y i ≠ mStar t₀} := by
    rintro y ⟨⟨i, j, hij, h1, h2⟩, h3⟩
    simp only [mem_iUnion]
    refine ⟨i, j, hij, h1, h2, fun h4 => h3 ⟨i, j, hij, h4, h1 ▸ h4⟩⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  rcases hμ i j hij with h | h
  · exact pair_null t₀ μ hij h
  · have hset : {y : Fin n → Msg | y i = y j ∧ y i ≠ msgNull ∧ y i ≠ mStar t₀}
        ⊆ {y | y j = y i ∧ y j ≠ msgNull ∧ y j ≠ mStar t₀} := by
      rintro y ⟨h1, h2, h3⟩
      exact ⟨h1.symm, h1 ▸ h2, h1 ▸ h3⟩
    exact measure_mono_null hset (pair_null t₀ μ (Ne.symm hij) h)

/-- The value of the two-message rule under a product law whose only atoms are `∅` and `m⋆`. -/
lemma integral_V_two (t₀ : I) {n : ℕ} (ω : Bool) (μ : Fin n → Measure Msg)
    [∀ j, IsProbabilityMeasure (μ j)]
    (hμ : ∀ i j, i ≠ j → (∀ a, a ≠ msgNull → a ≠ mStar t₀ → μ j {a} = 0) ∨
      ∀ a, a ≠ msgNull → a ≠ mStar t₀ → μ i {a} = 0) :
    ∫ y, g.V (twoRule n) ω y ∂(Measure.pi μ)
      = g.env.u false ω + VD.G g.env ω * (1 - atMostOne fun j => (μ j).real {mStar t₀}) := by
  have hmeas := measurableSet_twoEvent n
  simp_rw [V_two]
  have hint : Integrable ((twoEvent n).indicator fun _ => (1 : ℝ)) (Measure.pi μ) :=
    (integrable_const _).indicator hmeas
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const_mul,
    integral_indicator_const _ hmeas]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one]
  congr 2
  have hae : (Measure.pi μ).real (twoEvent n) = (Measure.pi μ).real (twoStar t₀ n) := by
    have h1 : twoEvent n =ᵐ[Measure.pi μ] twoStar t₀ n := by
      refine (ae_eq_set.2 ⟨pi_twoEvent_diff_null t₀ μ hμ, ?_⟩)
      rw [sdiff_eq_empty.2 (twoStar_subset t₀ n)]
      exact measure_empty
    exact measureReal_congr h1
  have hms : MeasurableSet (twoStar t₀ n) := by
    rw [← compl_compl (twoStar t₀ n), compl_twoStar]
    exact ((measurableSet_noStar t₀ n).union
      (Finset.measurableSet_biUnion _ fun i _ => measurableSet_oneStar t₀ i)).compl
  rw [hae, ← real_compl_twoStar, probReal_compl_eq_one_sub hms]
  ring

/-- For a constant law, `Pr(at most one) = Pr(Bin(n,r) ≤ 1)`. -/
lemma atMostOne_const {n : ℕ} (hn : 2 ≤ n) (r : ℝ) :
    atMostOne (fun _ : Fin n => r) = 1 - btail n r 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h0 : bpmf (m + 2) r 0 = (1 - r) ^ (m + 2) := by simp [bpmf]
  have h1 : bpmf (m + 2) r 1 = ((m : ℝ) + 2) * r * (1 - r) ^ (m + 1) := by
    simp only [bpmf, Nat.choose_one_right, pow_one]
    rw [show m + 2 - 1 = m + 1 by omega]
    push_cast
    ring
  have htail : btail (m + 2) r 2 = 1 - bpmf (m + 2) r 0 - bpmf (m + 2) r 1 := by
    rw [btail_eq]
    have h2 : bcdf (m + 2) r (((2 : ℕ) : ℝ) - 1) = bpmf (m + 2) r 0 + bpmf (m + 2) r 1 := by
      unfold bcdf
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hzero : ∀ k ∈ Finset.range (m + 1), (if (((k + 1 + 1 : ℕ) : ℝ)) ≤ ((2 : ℕ) : ℝ) - 1
          then bpmf (m + 2) r (k + 1 + 1) else 0) = 0 := by
        intro k _
        rw [ite_eq_right]
        push_cast
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      rw [Finset.sum_eq_zero hzero]
      norm_num
      ring
    rw [h2]
    ring
  rw [htail, h0, h1]
  unfold atMostOne
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), nsmul_eq_mul]
  push_cast
  ring

/-- `Pr(at most one)` when individual `i` is replaced by `r₀ ∈ {0, 1}` and the others have `r`. -/
lemma atMostOne_update {n : ℕ} (hn : 2 ≤ n) (r r₀ : ℝ) (i : Fin n) :
    atMostOne (Function.update (fun _ : Fin n => r) i r₀)
      = (1 - r₀) * ((1 - r) ^ (n - 1) + ((n : ℝ) - 1) * (r * (1 - r) ^ (n - 2)))
        + r₀ * (1 - r) ^ (n - 1) := by
  set R : Fin n → ℝ := Function.update (fun _ : Fin n => r) i r₀ with hR
  have hRi : R i = r₀ := by rw [hR, Function.update_self]
  have hRne : ∀ j, j ≠ i → R j = r := fun j hj => by rw [hR, Function.update_of_ne hj]
  have hconst : ∀ s : Finset (Fin n), i ∉ s → ∏ j ∈ s, (1 - R j) = (1 - r) ^ s.card := by
    intro s hs
    calc ∏ j ∈ s, (1 - R j) = ∏ _j ∈ s, (1 - r) :=
          Finset.prod_congr rfl fun j hj => by rw [hRne j fun h => hs (h ▸ hj)]
      _ = _ := by simp
  have hcard : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hnoti : i ∉ Finset.univ.erase i := Finset.notMem_erase i _
  have hprod : ∏ j, (1 - R j) = (1 - r₀) * (1 - r) ^ (n - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hRi, hconst _ hnoti, hcard]
  have hterm : ∀ k ∈ Finset.univ.erase i, R k * ∏ j ∈ Finset.univ.erase k, (1 - R j)
      = r * ((1 - r₀) * (1 - r) ^ (n - 2)) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hmem : i ∈ Finset.univ.erase k := Finset.mem_erase.2 ⟨Ne.symm hki, Finset.mem_univ i⟩
    rw [hRne k hki, ← Finset.mul_prod_erase _ _ hmem, hRi, hconst _ (Finset.notMem_erase i _),
      Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ k)]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show n - 1 - 1 = n - 2 by omega]
  have hsum : ∑ k, R k * ∏ j ∈ Finset.univ.erase k, (1 - R j)
      = r₀ * (1 - r) ^ (n - 1) + ((n : ℝ) - 1) * (r * ((1 - r₀) * (1 - r) ^ (n - 2))) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), hRi, hconst _ hnoti, hcard,
      Finset.sum_congr rfl hterm, Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_sub (by omega)]
    simp
  unfold atMostOne
  rw [hprod, hsum]
  ring

/-- `Pr(Bin(n-1,r) = 1) = (n-1) r (1-r)^{n-2}`. -/
lemma rho_two {n : ℕ} (hn : 2 ≤ n) (r : ℝ) :
    rho (n - 1) r 2 = ((n : ℝ) - 1) * (r * (1 - r) ^ (n - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold rho
  rw [ite_eq_right (by norm_num)]
  simp only [bpmf, show m + 2 - 1 = m + 1 by omega, show 2 - 1 = 1 by norm_num, Nat.choose_one_right,
    pow_one, show m + 1 - 1 = m by omega, show m + 2 - 2 = m by omega]
  push_cast
  ring

/-- Under `starStrat`, `q_{n,ω} = ∫ p(ω,x) dF(x)`. -/
lemma q_starStrat (g : MsgGame Bool Bool Msg) (t₀ : I) (p : Bool × ℝ → ℝ) (hp : Measurable p)
    (h01 : ∀ z, p z ∈ Icc (0 : ℝ) 1) (hnull : g.nullMsg = msgNull) (ω : Bool) :
    g.q (starStrat t₀ p hp h01) ω = ∫ x, p (ω, x) ∂(g.env.cost : Measure ℝ) := by
  unfold MsgGame.q
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show (mix (p (ω, x)) (Measure.dirac (mStar t₀)) (Measure.dirac msgNull)).real {g.nullMsg}ᶜ = _
  rw [mix_real (h01 _).1 (h01 _).2]
  have h1 : (Measure.dirac (mStar t₀)).real ({msgNull} : Set Msg)ᶜ = 1 := by
    simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton msgNull).compl,
      mStar_ne t₀]
  have h2 : (Measure.dirac msgNull).real ({msgNull} : Set Msg)ᶜ = 0 := by
    simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton msgNull).compl]
  rw [hnull, h1, h2]
  ring

/-- The law of an observed message under `starStrat`, without noisy recording: its only atoms are `∅` and
`m⋆`, with `Pr(y_i = m⋆ ∣ ω) = (1-ε) q_{n,ω}`. -/
lemma obs_star (hη0 : 0 < η) (hη1 : η < 1) (t₀ : I) (p : Bool × ℝ → ℝ) (hp : Measurable p)
    (h01 : ∀ z, p z ∈ Icc (0 : ℝ) 1) (ω : Bool) :
    letI g := perfectGame E ε η h0 h1 hη0 hη1 hc
    letI σ := starStrat t₀ p hp h01
    (g.obs σ ω).real {mStar t₀} = (1 - ε) * g.q σ ω ∧
      ∀ a, a ≠ msgNull → a ≠ mStar t₀ → (g.obs σ ω) {a} = 0 := by
  set g := perfectGame E ε η h0 h1 hη0 hη1 hc with hg
  set σ := starStrat t₀ p hp h01 with hσ
  have hrec : g.record = Kernel.id := rfl
  have hnoise : g.noiseObs = mechMsg η := Measure.id_comp
  have hκ : ∀ x, σ.κ (ω, x) = mix (p (ω, x)) (Measure.dirac (mStar t₀)) (Measure.dirac msgNull) :=
    fun _ => rfl
  have hker : ∀ x S, MeasurableSet S → g.ratKernel σ ω x S = σ.κ (ω, x) S := fun x S _ => by
    rw [MsgGame.ratKernel_apply, hrec, Measure.id_comp]
  have hq : g.q σ ω = ∫ x, p (ω, x) ∂(E.cost : Measure ℝ) := q_starStrat g t₀ p hp h01 rfl ω
  have hg1 : g.ε = ε := rfl
  constructor
  · unfold MsgGame.obs
    rw [mix_real g.ε_pos.le g.ε_lt.le, hnoise, mech_star hη0 hη1 t₀, hg1, hq]
    have hrat : (g.ratObs σ ω).real {mStar t₀} = ∫ x, p (ω, x) ∂(E.cost : Measure ℝ) := by
      unfold MsgGame.ratObs
      rw [real_bind _ (measurableSet_singleton _)]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (g.ratKernel σ ω x).real {mStar t₀} = _
      rw [measureReal_def, hker x _ (measurableSet_singleton _), ← measureReal_def, hκ,
        mix_real (h01 _).1 (h01 _).2]
      simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
    rw [hrat]
    ring
  · intro a ha ha'
    unfold MsgGame.obs
    rw [mix_apply]
    have hmech : g.noiseObs {a} = 0 := by
      rw [hnoise]
      rcases a with u | t
      · exact absurd rfl ha
      · have := mech_star (η := η) hη0 hη1 t
        rw [measureReal_def] at this
        have hprob : IsProbabilityMeasure (mechMsg η) := isProb_mix hη0.le hη1.le _ _
        have hf : (mechMsg η) {mStar t} ≠ ⊤ := measure_ne_top _ _
        exact (ENNReal.toReal_eq_zero_iff _).1 this |>.resolve_right hf
    have hrat : g.ratObs σ ω {a} = 0 := by
      unfold MsgGame.ratObs
      rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)]
      refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun x => ?_)
      show g.ratKernel σ ω x {a} = 0
      rw [hker x _ (measurableSet_singleton _), hκ, mix_apply]
      simp [Measure.dirac_apply' _ (measurableSet_singleton _), Ne.symm ha, Ne.symm ha']
    rw [hmech, hrat]
    simp

/-- **Remark `remark_continuum_message_noise`.**  Without noisy recording, consider the rule "`a = 1` iff
two identical nonnull messages are observed", and let rational individuals send `m⋆` or `∅`.  Then the
game is a Volunteer's Dilemma with a threshold of two for action, and mechanical individuals play no role:
with `r = (1-ε) q_{n,ω}` the probability that an individual is rational and sends `m⋆`,

* the payoff in state `ω` is `u(0,ω) + G(ω) Pr(Bin(n,r) ≥ 2)`;
* the gross benefit of sending `m⋆` rather than `∅` is `G(ω) Pr(Bin(n-1,r) = 1)`;
* any other nonnull message has the same value as `∅`, so it is never strictly better.

These are the formulas `bexp_threshold` and `gross_threshold` of the threshold rule with `T = 2`, with
report probability `r`. -/
theorem remark_two_messages (hη0 : 0 < η) (hη1 : η < 1) (t₀ : I) (p : Bool × ℝ → ℝ) (hp : Measurable p)
    (h01 : ∀ z, p z ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 2 ≤ n) (ω : Bool) (i : Fin n) :
    letI g := perfectGame E ε η h0 h1 hη0 hη1 hc
    letI σ := starStrat t₀ p hp h01
    g.W (twoRule n) σ ω = E.u false ω + VD.G E ω * btail n ((1 - ε) * g.q σ ω) 2 ∧
    g.U (twoRule n) σ ω i (mStar t₀) - g.U (twoRule n) σ ω i msgNull
      = VD.G E ω * rho (n - 1) ((1 - ε) * g.q σ ω) 2 ∧
    ∀ m : Msg, m ≠ mStar t₀ → g.U (twoRule n) σ ω i m = g.U (twoRule n) σ ω i msgNull := by
  set g := perfectGame E ε η h0 h1 hη0 hη1 hc with hg
  set σ := starStrat t₀ p hp h01 with hσ
  obtain ⟨hobs, hatoms⟩ := obs_star (E := E) (ε := ε) (h0 := h0) (h1 := h1) (hc := hc) hη0 hη1 t₀ p hp h01 ω
  set r := (1 - ε) * g.q σ ω with hr
  have hrec : ∀ m, g.record m = Measure.dirac m := fun m => Kernel.id_apply m
  have hu : g.env = E := rfl
  -- the value of each message
  have hU : ∀ m : Msg, g.U (twoRule n) σ ω i m
      = E.u false ω + VD.G E ω * (1 - atMostOne (Function.update (fun _ : Fin n => r) i
          (if m = mStar t₀ then 1 else 0))) := by
    intro m
    have := MsgGame.isProb_update (n := n) (g.obs σ ω) (g.record m) i
    unfold MsgGame.U
    rw [integral_V_two g t₀ ω]
    · rw [hu]
      congr 3
      refine congrArg atMostOne (funext fun j => ?_)
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, hrec]
        by_cases hm : m = mStar t₀
        · subst hm
          simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
        · simp [measureReal_def, hm, Measure.dirac_apply' _ (measurableSet_singleton _)]
      · simp only [Function.update_of_ne hj]
        exact hobs
    · intro k l hkl
      by_cases hl : l = i
      · right
        have hk : k ≠ i := fun h => hkl (h.trans hl.symm)
        rw [Function.update_of_ne hk]
        exact hatoms
      · left
        rw [Function.update_of_ne hl]
        exact hatoms
  have hnull : msgNull ≠ mStar t₀ := Ne.symm (mStar_ne t₀)
  refine ⟨?_, ?_, fun m hm => ?_⟩
  · -- the payoff in state `ω`
    unfold MsgGame.W
    rw [integral_V_two g t₀ ω _ (fun _ _ _ => Or.inl hatoms), hu]
    simp only [hobs]
    rw [atMostOne_const hn]
    ring
  · -- the gross benefit
    rw [hU, hU, rho_two hn, ite_eq_left rfl, ite_eq_right hnull, atMostOne_update hn, atMostOne_update hn]
    ring
  · rw [hU, hU, ite_eq_right hm, ite_eq_right hnull]

/-- **An equilibrium under the two-message rule.**  Without noisy recording, the rule "`a = 1` iff two
identical nonnull messages are observed" has an equilibrium in which rational individuals coordinate on `m⋆`.
It is the equilibrium of the Volunteer's Dilemma with a threshold of two: in state `1`, types use the cutoff
`H Pr(Bin(n-1,r) = 1)` for `r = (1-ε) p`; in state `0`, they stay silent; and the payoff is
`Π^SQ + π H Pr(Bin(n,r) ≥ 2)`. -/
theorem two_equilibrium (hV : VD.Assumptions E) (hη0 : 0 < η) (hη1 : η < 1) (t₀ : I) {n : ℕ} (hn : 2 ≤ n) :
    ∃ (σ : MStrat Bool Msg) (p : ℝ), p ∈ Icc (0 : ℝ) 1 ∧
      E.Fm (VD.H E * rho (n - 1) ((1 - ε) * p) 2) ≤ p ∧
      p ≤ E.F (VD.H E * rho (n - 1) ((1 - ε) * p) 2) ∧
      (perfectGame E ε η h0 h1 hη0 hη1 hc).IsEq (twoRule n) σ ∧
      (perfectGame E ε η h0 h1 hη0 hη1 hc).payoff (twoRule n) σ
        = E.PiSQ + VD.pr E * VD.H E * btail n ((1 - ε) * p) 2 := by
  set g := perfectGame E ε η h0 h1 hη0 hη1 hc with hg
  have hH := hV.H_pos
  have hL := hV.L_neg
  have hε1 : 0 < 1 - ε := by linarith
  -- the fixed point
  have hφc : Continuous fun p : ℝ => VD.H E * rho (n - 1) ((1 - ε) * p) 2 :=
    continuous_const.mul ((continuous_rho _ _).comp (continuous_const.mul continuous_id))
  obtain ⟨p, hp01, hp1, hp2⟩ := exists_fp E hφc
  set c := VD.H E * rho (n - 1) ((1 - ε) * p) 2 with hcdef
  obtain ⟨s, hsrp, hs1, hs2⟩ := E.exists_cutoff_strategy (q := fun _ => p) (c := fun _ => c)
    measurable_const measurable_const fun _ => ⟨hp1, hp2⟩
  let f : ℝ → ℝ := s.σ true
  have hfm : Measurable f := Env.Strat.measurable_slice s true
  have hfmem : ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun x => s.mem true x
  have hfint : ∫ x, f x ∂(E.cost : Measure ℝ) = p := hsrp true
  -- the strategy
  let P : Bool × ℝ → ℝ := fun z => if z.1 then f z.2 else 0
  have hPm : Measurable P := by
    refine measurable_from_prod_countable_right fun b => ?_
    cases b
    · simp [P]
    · simpa [P] using hfm
  have hP01 : ∀ z, P z ∈ Icc (0 : ℝ) 1 := fun z => by
    simp only [P]
    split_ifs
    · exact hfmem _
    · simp
  let σ := starStrat t₀ P hPm hP01
  have hσapply : ∀ ω x, σ.κ (ω, x) = mix (P (ω, x)) (Measure.dirac (mStar t₀)) (Measure.dirac msgNull) :=
    fun _ _ => rfl
  have hq : ∀ ω, g.q σ ω = if ω then p else 0 := fun ω => by
    rw [q_starStrat g t₀ P hPm hP01 rfl ω]
    cases ω
    · simp [P]
    · simp only [P, ite_true]
      exact hfint
  have hkey := fun (ω : Bool) (i : Fin n) =>
    remark_two_messages (E := E) (h0 := h0) (h1 := h1) (hc := hc) hη0 hη1 t₀ P hPm hP01 hn ω i
  have hρ0 : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → 0 ≤ rho (n - 1) r 2 := fun r hr => rho_nonneg hr.1 hr.2
  have hr1 : (1 - ε) * p ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hε1.le hp01.1
    · nlinarith [hp01.1, hp01.2]
  refine ⟨σ, p, hp01, hp1, hp2, ?_, ?_⟩
  · -- the best responses
    intro ω
    have hax : ∀ᵐ x ∂(g.env.cost : Measure ℝ), 0 ≤ x := MsgGame.ae_cost_nonneg
    filter_upwards [hax] with x hx
    have hN : g.nullMsg = msgNull := rfl
    have hcN : g.msgCost msgNull x = 0 := MsgGame.msgCost_null x
    have hcS : g.msgCost (mStar t₀) x = x := MsgGame.msgCost_ne (mStar_ne t₀) x
    -- the value of each message, relative to `∅`
    have hval : ∀ i m', g.netU (twoRule n) σ ω i m' x = g.U (twoRule n) σ ω i msgNull
        ∨ g.netU (twoRule n) σ ω i m' x
          = g.U (twoRule n) σ ω i msgNull + VD.G E ω * rho (n - 1) ((1 - ε) * g.q σ ω) 2 - x
        ∨ g.netU (twoRule n) σ ω i m' x = g.U (twoRule n) σ ω i msgNull - x := by
      intro i m'
      obtain ⟨_, h2, h3⟩ := hkey ω i
      by_cases hm1 : m' = mStar t₀
      · right; left
        subst hm1
        unfold MsgGame.netU
        rw [hcS]
        linarith
      · by_cases hm2 : m' = msgNull
        · left
          subst hm2
          unfold MsgGame.netU
          rw [hcN, sub_zero]
        · right; right
          unfold MsgGame.netU
          rw [h3 m' hm1, MsgGame.msgCost_ne hm2 x]
    have hnetS : ∀ i, g.netU (twoRule n) σ ω i (mStar t₀) x
        = g.U (twoRule n) σ ω i msgNull + VD.G E ω * rho (n - 1) ((1 - ε) * g.q σ ω) 2 - x := fun i => by
      have h2 := (hkey ω i).2.1
      unfold MsgGame.netU
      rw [hcS]
      linarith
    have hnetN : ∀ i, g.netU (twoRule n) σ ω i msgNull x = g.U (twoRule n) σ ω i msgNull := fun i => by
      unfold MsgGame.netU
      rw [hcN, sub_zero]
    rw [hσapply]
    cases ω with
    | false =>
      -- state `0`: everyone stays silent
      have hq0 : g.q σ false = 0 := by simpa using hq false
      have hρL : VD.G E false * rho (n - 1) ((1 - ε) * g.q σ false) 2 ≤ 0 := by
        rw [hq0, mul_zero]
        exact mul_nonpos_of_nonpos_of_nonneg hL.le (hρ0 0 (by simp))
      refine ae_mix t₀ (fun hpos => ?_) (fun _ i m' => ?_)
      · simp [P] at hpos
      · rw [hnetN]
        rcases hval i m' with h | h | h <;> rw [h] <;> linarith
    | true =>
      have hq1 : g.q σ true = p := by simpa using hq true
      have hGc : VD.G E true * rho (n - 1) ((1 - ε) * g.q σ true) 2 = c := by
        rw [hq1]
        rfl
      have hc0 : 0 ≤ c := mul_nonneg hH.le (hρ0 _ hr1)
      have hPf : P (true, x) = f x := by simp [P]
      refine ae_mix t₀ (fun hpos i m' => ?_) (fun hlt i m' => ?_)
      · rw [hnetS, hGc]
        rw [hPf] at hpos
        have hxc : x ≤ c := by
          by_contra hcon
          have hf0 : f x = 0 := hs2 true x (not_le.1 hcon)
          linarith
        rcases hval i m' with h | h | h
        · rw [h]
          linarith
        · rw [h, hGc]
        · rw [h]
          linarith
      · rw [hnetN]
        rw [hPf] at hlt
        have hcx : c ≤ x := by
          by_contra hcon
          have hf1 : f x = 1 := hs1 true x (not_le.1 hcon)
          linarith
        rcases hval i m' with h | h | h
        · rw [h]
        · rw [h, hGc]
          linarith
        · rw [h]
          linarith
  · -- the payoff
    have hi : Fin n := ⟨0, by omega⟩
    have hW : ∀ ω, g.W (twoRule n) σ ω
        = E.u false ω + VD.G E ω * btail n ((1 - ε) * (if ω then p else 0)) 2 := fun ω => by
      have := (hkey ω hi).1
      rw [hq ω] at this
      exact this
    have hb0 : btail n 0 2 = 0 := by
      rw [btail_eq]
      have h1 := bcdf_le_one (m := n) (p := 0) le_rfl zero_le_one (((2 : ℕ) : ℝ) - 1)
      have h2 : bcdf n 0 (((2 : ℕ) : ℝ) - 1) = 1 := by
        unfold bcdf
        rw [Finset.sum_range_succ']
        have hz : ∀ k ∈ Finset.range n, (if ((k + 1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ) - 1
            then bpmf n 0 (k + 1) else 0) = 0 := by
          intro k _
          split_ifs
          · simp [bpmf]
          · rfl
        rw [Finset.sum_eq_zero hz]
        simp [bpmf]
      rw [h2]
      ring
    unfold MsgGame.payoff
    have hpr : (g.env.prior : Measure Bool) = (E.prior : Measure Bool) := rfl
    rw [hpr]
    simp_rw [hW]
    rw [VD.integral_bool, VD.PiSQ_eq' hV]
    simp only [ite_true, Bool.false_eq_true, ite_false, mul_zero, hb0]
    have hG : VD.G E true = VD.H E := rfl
    rw [hG]
    ring

end Continuum

end OA

end NoisyVD
