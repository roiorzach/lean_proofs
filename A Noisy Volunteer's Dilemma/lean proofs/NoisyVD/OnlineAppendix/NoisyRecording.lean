import NoisyVD.OnlineAppendix.MessageBounds

/-!
# The paper's message space `X = {∅} ∪ [0,1]` with noisy recording

* `Msg`: the observation space, with `Sum.inl ()` for `∅` and `Sum.inr m` for `m ∈ [0,1]`.
* `RecordingData`: Assumption `assumption_noisy_recording`.
* `NoisyModel.game`: the model of Subsection `subsec_general_message_spaces`.
* `NoisyModel.exists_obs_density`, `NoisyModel.wRatio`, `NoisyModel.record_eq_withDensity`: the density `p_ω`
  and the likelihood ratios `w_m` of the paper, with `0 ≤ w_m ≤ Λ`.
* `NoisyModel.anonymous_influence`: Lemma `lemma_anonymous_influence`, through these `w_m`.
* `NoisyModel.dom`: the paper's constant `Λ` satisfies the domination condition, which yields Proposition
  `prop_general_message_upper_bounds`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal

namespace NoisyVD

namespace OA

local notation "I" => unitInterval

/-- `X = {∅} ∪ [0,1]`. -/
abbrev Msg := Unit ⊕ I

/-- `∅`. -/
abbrev msgNull : Msg := Sum.inl ()

instance : MeasurableSingletonClass Msg := ⟨fun x => by
  cases x with
  | inl u =>
    have : ({Sum.inl u} : Set Msg) = Sum.inl '' {u} := by simp
    rw [this]
    exact MeasurableSet.inl_image (measurableSet_singleton u)
  | inr m =>
    have : ({Sum.inr m} : Set Msg) = Sum.inr '' {m} := by simp
    rw [this]
    exact MeasurableSet.inr_image (measurableSet_singleton m)⟩

/-- The uniform law on `[0,1]` as a law on `X`. -/
noncomputable def unifMsg : Measure Msg := (volume : Measure I).map Sum.inr

instance : IsProbabilityMeasure unifMsg := by
  unfold unifMsg
  infer_instance

/-- A mechanical individual sends `∅` with probability `η` and otherwise draws uniformly from `[0,1]`. -/
noncomputable def mechMsg (η : ℝ) : Measure Msg := mix η (Measure.dirac msgNull) unifMsg

/-- **Assumption `assumption_noisy_recording`.** `k m y = k(y ∣ m)` is a density on `[0,1]` for every `m`,
continuous and strictly positive on `[0,1]²`. -/
structure RecordingData where
  k : I → I → ℝ
  k_cont : Continuous (Function.uncurry k)
  k_pos : ∀ m y, 0 < k m y
  k_int : ∀ m, ∫ y, k m y = 1

namespace RecordingData

variable (D : RecordingData)

/-- `\underline k`. -/
noncomputable def kLo : ℝ := sInf (range (Function.uncurry D.k))

/-- `\overline k`. -/
noncomputable def kHi : ℝ := sSup (range (Function.uncurry D.k))

lemma isCompact_range : IsCompact (range (Function.uncurry D.k)) := _root_.isCompact_range D.k_cont

/-- **Equation `general_message_upper_bound`.** -/
lemma kLo_le (m y : I) : D.kLo ≤ D.k m y := csInf_le D.isCompact_range.bddBelow ⟨(m, y), rfl⟩

lemma le_kHi (m y : I) : D.k m y ≤ D.kHi := le_csSup D.isCompact_range.bddAbove ⟨(m, y), rfl⟩

lemma kLo_pos : 0 < D.kLo := by
  have hne : (range (Function.uncurry D.k)).Nonempty := range_nonempty _
  obtain ⟨⟨m, y⟩, hmy⟩ := D.isCompact_range.sInf_mem hne
  rw [kLo, ← hmy]
  exact D.k_pos m y

lemma kLo_le_kHi : D.kLo ≤ D.kHi := (D.kLo_le 0 0).trans (D.le_kHi 0 0)

lemma measurable_k : Measurable (Function.uncurry D.k) := D.k_cont.measurable

lemma bm_k (m : I) : BM (D.k m) :=
  BM.of_mem (D.measurable_k.comp (measurable_const.prodMk measurable_id)) fun y =>
    ⟨D.kLo_le m y, D.le_kHi m y⟩

/-- The law of `y_i` given `m_i = m`, on `[0,1]`. -/
noncomputable def recI (m : I) : Measure I :=
  (volume : Measure I).withDensity fun y => ENNReal.ofReal (D.k m y)

instance (m : I) : IsProbabilityMeasure (D.recI m) := by
  constructor
  rw [recI, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((D.bm_k m).integrable _)
      (ae_of_all _ fun y => (D.k_pos m y).le), D.k_int]
  simp

/-- The recording kernel: `y_i = ∅` if `m_i = ∅`, and `y_i` has density `k(· ∣ m)` if `m_i = m ∈ [0,1]`. -/
noncomputable def recordK : Kernel Msg Msg where
  toFun := Sum.elim (fun _ => Measure.dirac msgNull) fun m => (D.recI m).map Sum.inr
  measurable' := by
    refine measurable_fun_sum measurable_const ?_
    refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
    have hS' : MeasurableSet (Sum.inr ⁻¹' S : Set I) := measurable_inr hS
    simp only [Function.comp, Sum.elim_inr]
    simp_rw [Measure.map_apply measurable_inr hS, recI, withDensity_apply _ hS']
    have hf : Measurable fun z : I × I => ENNReal.ofReal (D.k z.1 z.2) :=
      ENNReal.measurable_ofReal.comp D.measurable_k
    exact hf.lintegral_prod_right'

instance : IsMarkovKernel D.recordK := ⟨fun x => by
  cases x with
  | inl u =>
    show IsProbabilityMeasure (Measure.dirac msgNull)
    infer_instance
  | inr m =>
    show IsProbabilityMeasure ((D.recI m).map Sum.inr)
    infer_instance⟩

lemma recordK_null : D.recordK msgNull = Measure.dirac msgNull := rfl

lemma recordK_inr (m : I) : D.recordK (Sum.inr m) = (D.recI m).map Sum.inr := rfl

/-- `Pr(y_i ∈ S ∣ m_i = m)` is pinned by the Lebesgue measure of `S ∩ [0,1]`. -/
lemma real_recordK_inr_mem (m : I) {S : Set Msg} (hS : MeasurableSet S) :
    (D.recordK (Sum.inr m)).real S ∈
      Icc (D.kLo * (volume : Measure I).real (Sum.inr ⁻¹' S))
        (D.kHi * (volume : Measure I).real (Sum.inr ⁻¹' S)) := by
  have hS' : MeasurableSet (Sum.inr ⁻¹' S : Set I) := measurable_inr hS
  have h1 : (D.recordK (Sum.inr m)).real S = ∫ y, (Sum.inr ⁻¹' S : Set I).indicator (D.k m) y := by
    rw [recordK_inr, measureReal_def, Measure.map_apply measurable_inr hS,
      setIntegral_density (ν := D.recI m) (D.bm_k m) (fun y => (D.k_pos m y).le) rfl hS',
      ENNReal.toReal_ofReal (integral_nonneg fun y =>
        indicator_nonneg (fun z _ => (D.k_pos m z).le) y)]
  have hint : Integrable ((Sum.inr ⁻¹' S : Set I).indicator (D.k m)) :=
    ((D.bm_k m).integrable _).indicator hS'
  rw [h1]
  constructor
  · have := integral_mono (μ := (volume : Measure I))
      ((integrable_const D.kLo).indicator hS') hint fun y => by
        by_cases hy : y ∈ (Sum.inr ⁻¹' S : Set I)
        · simp only [indicator_of_mem hy]
          exact D.kLo_le m y
        · simp only [indicator_of_notMem hy]
          exact le_rfl
    rw [integral_indicator_const _ hS'] at this
    simpa [mul_comm] using this
  · have := integral_mono (μ := (volume : Measure I)) hint
      ((integrable_const D.kHi).indicator hS') fun y => by
        by_cases hy : y ∈ (Sum.inr ⁻¹' S : Set I)
        · simp only [indicator_of_mem hy]
          exact D.le_kHi m y
        · simp only [indicator_of_notMem hy]
          exact le_rfl
    rw [integral_indicator_const _ hS'] at this
    simpa [mul_comm] using this

end RecordingData

/-- The parameters and primitives of the model of Subsection `subsec_general_message_spaces`. -/
structure NoisyModel (A Ω : Type*) [TopologicalSpace A] [TopologicalSpace Ω] [MeasurableSpace Ω] where
  /-- `u^p`, the prior and the distribution `F` of costs of rational individuals. -/
  env : Env A Ω
  /-- The recording density. -/
  D : RecordingData
  /-- The probability of being mechanical. -/
  ε : ℝ
  ε_pos : 0 < ε
  ε_lt : ε < 1
  /-- The probability that a mechanical individual sends `∅`. -/
  η : ℝ
  η_pos : 0 < η
  η_lt : η < 1
  /-- `ν_i ≥ 0`. -/
  cost_nonneg : (env.cost : Measure ℝ) (Iio 0) = 0

namespace NoisyModel

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

variable (N : NoisyModel A Ω)

/-- The game. -/
noncomputable def game : MsgGame A Ω Msg where
  env := N.env
  nullMsg := msgNull
  record := N.D.recordK
  record_markov := inferInstance
  mech := mechMsg N.η
  mech_prob := isProb_mix N.η_pos.le N.η_lt.le _ _
  ε := N.ε
  ε_pos := N.ε_pos
  ε_lt := N.ε_lt
  cost_nonneg := N.cost_nonneg

/-- The constant `Λ = max {1/(εη), \overline k/(ε(1-η)\underline k)}` of the paper. -/
noncomputable def Lam : ℝ :=
  max (1 / (N.ε * N.η)) (N.D.kHi / (N.ε * (1 - N.η) * N.D.kLo))

lemma integral_mech {f : Msg → ℝ} (hf : BM f) :
    ∫ z, f z ∂(mechMsg N.η) = N.η * f msgNull + (1 - N.η) * ∫ t : I, f (Sum.inr t) := by
  have hη := N.η_pos
  have hη1 := N.η_lt
  unfold mechMsg mix
  rw [integral_add_measure ((hf.integrable _).smul_measure (by finiteness))
      ((hf.integrable _).smul_measure (by finiteness)),
    integral_smul_measure, integral_smul_measure, integral_dirac, unifMsg,
    integral_map measurable_inr.aemeasurable hf.1.aestronglyMeasurable,
    ENNReal.toReal_ofReal hη.le, ENNReal.toReal_ofReal (by linarith)]
  simp

/-- **Equation `eq_background_bounds`**, as a bound on the law of the noise: it gives probability at least
`η` times the recorded law of `∅`, and at least `(1-η) \underline k` times Lebesgue measure on `[0,1]`. -/
theorem noise_lower {S : Set Msg} (hS : MeasurableSet S) :
    N.η * (N.D.recordK msgNull).real S ≤ N.game.noiseObs.real S ∧
      (1 - N.η) * (N.D.kLo * (volume : Measure I).real (Sum.inr ⁻¹' S)) ≤ N.game.noiseObs.real S := by
  have hη := N.η_pos
  have hη1 := N.η_lt
  set leb := (volume : Measure I).real (Sum.inr ⁻¹' S) with hleb
  have hBM : BM fun z => (N.D.recordK z).real S := by
    refine BM.of_mem ?_ fun z => ⟨measureReal_nonneg, measureReal_le_one⟩
    simp only [measureReal_def]
    exact (N.D.recordK.measurable_coe hS).ennreal_toReal
  -- the law of the noise
  have hnoise : N.game.noiseObs.real S = N.η * (N.D.recordK msgNull).real S
      + (1 - N.η) * ∫ t : I, (N.D.recordK (Sum.inr t)).real S := by
    show ((N.D.recordK) ∘ₘ (mechMsg N.η)).real S = _
    have : IsProbabilityMeasure (mechMsg N.η) := isProb_mix N.η_pos.le N.η_lt.le _ _
    rw [real_bind _ hS, N.integral_mech hBM]
  have hintlow : N.D.kLo * leb ≤ ∫ t : I, (N.D.recordK (Sum.inr t)).real S := by
    have hBMt : BM fun t : I => (N.D.recordK (Sum.inr t)).real S := by
      refine BM.of_mem (hBM.1.comp measurable_inr) fun z => ⟨measureReal_nonneg, measureReal_le_one⟩
    have := integral_mono (μ := (volume : Measure I)) (integrable_const (N.D.kLo * leb))
      (hBMt.integrable _) fun t => (N.D.real_recordK_inr_mem t hS).1
    simpa using this
  have hnullnn : 0 ≤ (N.D.recordK msgNull).real S := measureReal_nonneg
  have hinttnn : 0 ≤ ∫ t : I, (N.D.recordK (Sum.inr t)).real S :=
    integral_nonneg fun t => measureReal_nonneg
  have hnoise1 : N.η * (N.D.recordK msgNull).real S ≤ N.game.noiseObs.real S := by
    rw [hnoise]
    have := mul_nonneg (by linarith : 0 ≤ 1 - N.η) hinttnn
    linarith
  have hnoise2 : (1 - N.η) * (N.D.kLo * leb) ≤ N.game.noiseObs.real S := by
    rw [hnoise]
    have h1 := mul_nonneg hη.le hnullnn
    have h2 := mul_le_mul_of_nonneg_left hintlow (by linarith : 0 ≤ 1 - N.η)
    linarith
  exact ⟨hnoise1, hnoise2⟩

/-- **The domination condition holds with the paper's `Λ`.** -/
theorem dom : N.game.Dom N.Lam := by
  intro m S hS
  have hε := N.ε_pos
  have hη := N.η_pos
  have hη1 := N.η_lt
  have hk := N.D.kLo_pos
  set leb := (volume : Measure I).real (Sum.inr ⁻¹' S) with hleb
  have hleb0 : 0 ≤ leb := measureReal_nonneg
  obtain ⟨hnoise1, hnoise2⟩ := N.noise_lower hS
  have hnoise0 : 0 ≤ N.game.noiseObs.real S := measureReal_nonneg
  have hgε : N.game.ε = N.ε := rfl
  rw [hgε]
  show (N.D.recordK m).real S ≤ N.Lam * (N.ε * N.game.noiseObs.real S)
  cases m with
  | inl u =>
    have hu : (Sum.inl u : Msg) = msgNull := rfl
    rw [hu]
    have h1 : 1 / (N.ε * N.η) ≤ N.Lam := le_max_left _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hε.le hnoise0)
    refine le_trans ?_ h2
    have e : 1 / (N.ε * N.η) * (N.ε * N.game.noiseObs.real S) = N.game.noiseObs.real S / N.η := by
      field_simp
    rw [e, le_div_iff₀ hη]
    linarith
  | inr t =>
    have h1 : N.D.kHi / (N.ε * (1 - N.η) * N.D.kLo) ≤ N.Lam := le_max_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hε.le hnoise0)
    refine le_trans ?_ h2
    have hpos : 0 < (1 - N.η) * N.D.kLo := mul_pos (by linarith) hk
    have e : N.D.kHi / (N.ε * (1 - N.η) * N.D.kLo) * (N.ε * N.game.noiseObs.real S)
        = N.D.kHi * (N.game.noiseObs.real S / ((1 - N.η) * N.D.kLo)) := by
      have h1' : (1 - N.η) ≠ 0 := by linarith
      have h3 := hk.ne'
      field_simp
    rw [e]
    have h3 : leb ≤ N.game.noiseObs.real S / ((1 - N.η) * N.D.kLo) := by
      rw [le_div_iff₀ hpos]
      linarith
    have h4 := (N.D.real_recordK_inr_mem t hS).2
    have hkHi : 0 ≤ N.D.kHi := hk.le.trans N.D.kLo_le_kHi
    exact h4.trans (mul_le_mul_of_nonneg_left h3 hkHi)

/-! ### The likelihood ratios `w_m` of the paper -/

section LikelihoodRatio

variable (σ : MStrat Ω Msg) (ω : Ω)

lemma measurableEmbedding_inr : MeasurableEmbedding (Sum.inr : I → Msg) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs => MeasurableSet.inr_image hs⟩

/-- `q_ω = P_ω({∅})`. -/
noncomputable def nullObs : ℝ := (N.game.obs σ ω).real {msgNull}

/-- The law of an observed message on `[0,1]`. -/
noncomputable def obsI : Measure I := (N.game.obs σ ω).comap Sum.inr

lemma obsI_apply (S : Set I) : N.obsI σ ω S = N.game.obs σ ω (Sum.inr '' S) :=
  measurableEmbedding_inr.comap_apply _ S

instance : IsFiniteMeasure (N.obsI σ ω) :=
  ⟨by
    rw [obsI_apply]
    exact measure_lt_top _ _⟩

/-- The first part of equation `eq_background_bounds`: `q_ω ≥ εη`. -/
theorem eps_eta_le_nullObs : N.ε * N.η ≤ N.nullObs σ ω := by
  have h1 := (N.noise_lower (measurableSet_singleton msgNull)).1
  have h2 := MsgGame.noise_le_obs (g := N.game) σ ω {msgNull}
  have h3 : (N.D.recordK msgNull).real {msgNull} = 1 := by
    rw [N.D.recordK_null]
    simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [h3, mul_one] at h1
  have h4 : N.ε * N.η ≤ N.ε * N.game.noiseObs.real {msgNull} :=
    mul_le_mul_of_nonneg_left h1 N.ε_pos.le
  exact h4.trans h2

lemma nullObs_pos : 0 < N.nullObs σ ω :=
  lt_of_lt_of_le (mul_pos N.ε_pos N.η_pos) (N.eps_eta_le_nullObs σ ω)

/-- Averaging a bound on recorded laws over any law of intended messages. -/
lemma real_bind_le {μ : Measure Msg} [IsProbabilityMeasure μ] {T : Set Msg} (hT : MeasurableSet T) {C : ℝ}
    (hC : ∀ m, (N.D.recordK m).real T ≤ C) : (N.D.recordK ∘ₘ μ).real T ≤ C := by
  rw [real_bind _ hT]
  have hb : BM fun m => (N.D.recordK m).real T := by
    refine BM.of_mem (a := 0) (b := 1) ?_ fun z => ⟨measureReal_nonneg, measureReal_le_one⟩
    simp only [measureReal_def]
    exact (N.D.recordK.measurable_coe hT).ennreal_toReal
  have := integral_mono (μ := μ) (hb.integrable _) (integrable_const C) hC
  simpa using this

/-- Each recorded law on `[0,1]` is at most `\overline k` times Lebesgue measure. -/
lemma real_recordK_image_le (m : Msg) {S : Set I} (hS : MeasurableSet S) :
    (N.D.recordK m).real (Sum.inr '' S) ≤ N.D.kHi * (volume : Measure I).real S := by
  have hkHi : 0 ≤ N.D.kHi := N.D.kLo_pos.le.trans N.D.kLo_le_kHi
  have hT : MeasurableSet (Sum.inr '' S : Set Msg) := measurableEmbedding_inr.measurableSet_image.2 hS
  have hpre : (Sum.inr ⁻¹' (Sum.inr '' S : Set Msg) : Set I) = S :=
    Set.preimage_image_eq _ Sum.inr_injective
  cases m with
  | inl u =>
    have hu : (Sum.inl u : Msg) = msgNull := rfl
    rw [hu, N.D.recordK_null]
    have h0 : (Measure.dirac msgNull).real (Sum.inr '' S : Set Msg) = 0 := by
      simp [measureReal_def, Measure.dirac_apply' _ hT, msgNull]
    rw [h0]
    exact mul_nonneg hkHi measureReal_nonneg
  | inr t =>
    have := (N.D.real_recordK_inr_mem t hT).2
    rwa [hpre] at this

/-- The density `p_ω` of `P_ω` on `[0,1]` exists, and it satisfies the second part of equation
`eq_background_bounds`: `p_ω(y) ≥ ε(1-η) \underline k` for every `y`. -/
theorem exists_obs_density : ∃ p : I → ℝ, Measurable p ∧
    (∀ y, p y ∈ Icc (N.ε * (1 - N.η) * N.D.kLo) N.D.kHi) ∧
    N.obsI σ ω = (volume : Measure I).withDensity fun y => ENNReal.ofReal (p y) := by
  have hε := N.ε_pos
  have hε1 := N.ε_lt
  have hη := N.η_pos
  have hη1 := N.η_lt
  have hk := N.D.kLo_pos
  have hreal : ∀ S : Set I, MeasurableSet S →
      (N.obsI σ ω).real S = (N.game.obs σ ω).real (Sum.inr '' S) := fun S hS => by
    rw [measureReal_def, obsI_apply, measureReal_def]
  refine exists_density ?_ ?_ (fun S hS => ?_) (fun S hS => ?_)
  · have : 0 < 1 - N.η := by linarith
    positivity
  · have h1 : N.ε * (1 - N.η) ≤ 1 := by nlinarith
    have h2 := N.D.kLo_le_kHi
    nlinarith
  · -- the lower bound comes from mechanical individuals
    have hT : MeasurableSet (Sum.inr '' S : Set Msg) := measurableEmbedding_inr.measurableSet_image.2 hS
    have hpre : (Sum.inr ⁻¹' (Sum.inr '' S : Set Msg) : Set I) = S :=
      Set.preimage_image_eq _ Sum.inr_injective
    have h1 := (N.noise_lower hT).2
    rw [hpre] at h1
    have h2 := MsgGame.noise_le_obs (g := N.game) σ ω (Sum.inr '' S)
    rw [hreal S hS]
    have h3 := mul_le_mul_of_nonneg_left h1 hε.le
    calc N.ε * (1 - N.η) * N.D.kLo * (volume : Measure I).real S
        = N.ε * ((1 - N.η) * (N.D.kLo * (volume : Measure I).real S)) := by ring
      _ ≤ N.ε * N.game.noiseObs.real (Sum.inr '' S) := h3
      _ ≤ _ := h2
  · -- the upper bound holds for each recorded law
    have hT : MeasurableSet (Sum.inr '' S : Set Msg) := measurableEmbedding_inr.measurableSet_image.2 hS
    rw [hreal S hS]
    set C := N.D.kHi * (volume : Measure I).real S with hC
    have hrec := fun m => N.real_recordK_image_le m hS
    have hm : IsProbabilityMeasure (mechMsg N.η) := isProb_mix hη.le hη1.le _ _
    have hnoise : N.game.noiseObs.real (Sum.inr '' S) ≤ C := N.real_bind_le hT hrec
    have hrat : (N.game.ratObs σ ω).real (Sum.inr '' S) ≤ C := by
      unfold MsgGame.ratObs
      rw [real_bind _ hT]
      have hb : BM fun x => (N.game.ratKernel σ ω x).real (Sum.inr '' S) := by
        refine BM.of_mem (a := 0) (b := 1) ?_ fun z => ⟨measureReal_nonneg, measureReal_le_one⟩
        simp only [measureReal_def]
        exact ((N.game.ratKernel σ ω).measurable_coe hT).ennreal_toReal
      have hle : ∀ x, (N.game.ratKernel σ ω x).real (Sum.inr '' S) ≤ C := fun x => by
        rw [MsgGame.ratKernel_apply]
        exact N.real_bind_le hT hrec
      have := integral_mono (μ := (N.game.env.cost : Measure ℝ)) (hb.integrable _) (integrable_const C) hle
      simpa using this
    have hgε : N.game.ε = N.ε := rfl
    unfold MsgGame.obs
    rw [mix_real N.game.ε_pos.le N.game.ε_lt.le, hgε]
    nlinarith

/-- The likelihood ratio `w_m = dQ_m/dP_ω` of the paper: for `m = ∅`, it is `1/q_ω` at `∅` and `0` on
`[0,1]`; for `m ∈ [0,1]`, it is `0` at `∅` and `k(z ∣ m)/p_ω(z)` on `[0,1]`. -/
noncomputable def wRatio (q : ℝ) (p : I → ℝ) (D : RecordingData) : Msg → Msg → ℝ :=
  Sum.elim (fun _ => Sum.elim (fun _ => 1 / q) fun _ => 0)
    fun t => Sum.elim (fun _ => 0) fun y => D.k t y / p y

/-- `P_ω` is its atom at `∅` plus its part on `[0,1]`. -/
lemma obs_decomp : N.game.obs σ ω = ENNReal.ofReal (N.nullObs σ ω) • Measure.dirac msgNull
    + (N.obsI σ ω).map Sum.inr := by
  refine Measure.ext fun S hS => ?_
  have hpart : ((N.obsI σ ω).map Sum.inr) S = N.game.obs σ ω (S \ {msgNull}) := by
    rw [Measure.map_apply measurable_inr hS, obsI_apply, Set.image_preimage_eq_inter_range]
    congr 1
    ext z
    cases z with
    | inl u =>
      simp [msgNull]
    | inr t =>
      simp [msgNull]
  have hsing : (ENNReal.ofReal (N.nullObs σ ω) • Measure.dirac msgNull) S
      = N.game.obs σ ω (S ∩ {msgNull}) := by
    have hq : ENNReal.ofReal (N.nullObs σ ω) = N.game.obs σ ω {msgNull} := by
      unfold nullObs
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hS]
    rw [hq]
    by_cases h : msgNull ∈ S
    · simp [h, Set.inter_singleton_of_mem h]
    · simp [h, Set.inter_singleton_of_notMem h]
  rw [Measure.add_apply, hsing, hpart]
  exact (measure_inter_add_sdiff S (measurableSet_singleton _)).symm

/-- **`Q_m` has density `w_m` with respect to `P_ω`**, and `0 ≤ w_m ≤ Λ`. -/
theorem record_eq_withDensity {p : I → ℝ} (hpm : Measurable p)
    (hp : ∀ y, p y ∈ Icc (N.ε * (1 - N.η) * N.D.kLo) N.D.kHi)
    (hobs : N.obsI σ ω = (volume : Measure I).withDensity fun y => ENNReal.ofReal (p y)) (m : Msg) :
    (∀ z, wRatio (N.nullObs σ ω) p N.D m z ∈ Icc 0 N.Lam) ∧
      N.D.recordK m = (N.game.obs σ ω).withDensity
        fun z => ENNReal.ofReal (wRatio (N.nullObs σ ω) p N.D m z) := by
  have hε := N.ε_pos
  have hη := N.η_pos
  have hη1 := N.η_lt
  have hk := N.D.kLo_pos
  have hq := N.nullObs_pos σ ω
  have hLam0 : 0 ≤ N.Lam :=
    (by positivity : (0 : ℝ) ≤ 1 / (N.ε * N.η)).trans (le_max_left _ _)
  have hplow : ∀ y, 0 < p y := fun y =>
    lt_of_lt_of_le (mul_pos (mul_pos hε (by linarith)) hk) (hp y).1
  constructor
  · intro z
    cases m with
    | inl u =>
      cases z with
      | inl v =>
        refine ⟨by simp only [wRatio, Sum.elim_inl]; positivity, ?_⟩
        simp only [wRatio, Sum.elim_inl]
        refine le_trans ?_ (le_max_left _ _)
        exact one_div_le_one_div_of_le (mul_pos hε hη) (N.eps_eta_le_nullObs σ ω)
      | inr y =>
        simpa [wRatio] using hLam0
    | inr t =>
      cases z with
      | inl v =>
        simpa [wRatio] using hLam0
      | inr y =>
        simp only [wRatio, Sum.elim_inr]
        refine ⟨div_nonneg (N.D.k_pos t y).le (hplow y).le, ?_⟩
        refine le_trans ?_ (le_max_right _ _)
        exact div_le_div₀ (hk.le.trans N.D.kLo_le_kHi) (N.D.le_kHi t y)
          (mul_pos (mul_pos hε (by linarith)) hk) (hp y).1
  · -- integrate against the decomposition of `P_ω`
    set f : Msg → ENNReal := fun z => ENNReal.ofReal (wRatio (N.nullObs σ ω) p N.D m z) with hf
    have hfm : Measurable f := by
      refine ENNReal.measurable_ofReal.comp ?_
      cases m with
      | inl u => exact measurable_fun_sum measurable_const measurable_const
      | inr t =>
        refine measurable_fun_sum measurable_const ?_
        exact ((N.D.bm_k t).1).div hpm
    refine Measure.ext fun S hS => ?_
    have hS' : MeasurableSet (Sum.inr ⁻¹' S : Set I) := measurable_inr hS
    have hdirac : ∫⁻ z in S, f z ∂(Measure.dirac msgNull) = S.indicator f msgNull := by
      rw [← lintegral_indicator hS, lintegral_dirac' _ (hfm.indicator hS)]
    have hval : (N.game.obs σ ω).withDensity f S
        = ENNReal.ofReal (N.nullObs σ ω) * S.indicator f msgNull
          + ∫⁻ y in Sum.inr ⁻¹' S, ENNReal.ofReal (p y) * f (Sum.inr y) := by
      rw [withDensity_apply _ hS]
      conv_lhs => rw [N.obs_decomp σ ω]
      rw [Measure.restrict_add, lintegral_add_measure, Measure.restrict_smul, lintegral_smul_measure,
        hdirac, setLIntegral_map hS hfm measurable_inr, hobs]
      congr 1
      exact setLIntegral_withDensity_eq_setLIntegral_mul _ (ENNReal.measurable_ofReal.comp hpm)
        (hfm.comp measurable_inr) hS'
    rw [hval]
    cases m with
    | inl u =>
      have hu : (Sum.inl u : Msg) = msgNull := rfl
      have hfnull : f msgNull = ENNReal.ofReal (1 / N.nullObs σ ω) := rfl
      have hfinr : ∀ y, f (Sum.inr y) = 0 := fun y => by
        have : wRatio (N.nullObs σ ω) p N.D (Sum.inl u) (Sum.inr y) = 0 := rfl
        simp only [hf, this, ENNReal.ofReal_zero]
      simp only [hfinr, mul_zero, lintegral_zero, add_zero]
      rw [hu, N.D.recordK_null, Measure.dirac_apply' _ hS]
      by_cases h : msgNull ∈ S
      · rw [indicator_of_mem h, indicator_of_mem h, hfnull, ← ENNReal.ofReal_mul hq.le,
          mul_one_div_cancel hq.ne']
        simp
      · rw [indicator_of_notMem h, indicator_of_notMem h]
        simp
    | inr t =>
      have hfnull : f msgNull = 0 := by
        have : wRatio (N.nullObs σ ω) p N.D (Sum.inr t) msgNull = 0 := rfl
        simp only [hf, this, ENNReal.ofReal_zero]
      have hfinr : ∀ y, ENNReal.ofReal (p y) * f (Sum.inr y) = ENNReal.ofReal (N.D.k t y) := fun y => by
        have : wRatio (N.nullObs σ ω) p N.D (Sum.inr t) (Sum.inr y) = N.D.k t y / p y := rfl
        simp only [hf, this]
        rw [← ENNReal.ofReal_mul (hplow y).le, mul_div_cancel₀ _ (hplow y).ne']
      have hind : S.indicator f msgNull = 0 := by
        by_cases h : msgNull ∈ S
        · rw [indicator_of_mem h, hfnull]
        · rw [indicator_of_notMem h]
      rw [hind, mul_zero, zero_add]
      simp only [hfinr]
      rw [N.D.recordK_inr, Measure.map_apply measurable_inr hS, RecordingData.recI,
        withDensity_apply _ hS']

end LikelihoodRatio

/-- `M_G = B √(Λ-1)`. -/
noncomputable def MG : ℝ := N.env.B * √(N.Lam - 1)

/-- `|U_{n,ω}(m) - E[V_ω]| ≤ B√(Λ-1)/(2√n)`, the paper's bound, through the explicit ratios `w_m`. -/
theorem abs_U_sub_W {n : ℕ} (hn : 0 < n) (d : MRule A Msg n) (σ : MStrat Ω Msg) (ω : Ω) (i : Fin n)
    (m : Msg) :
    |N.game.U d σ ω i m - N.game.W d σ ω| ≤ (N.env.B / 2) * √((N.Lam - 1) / n) := by
  obtain ⟨p, hpm, hp, hobs⟩ := N.exists_obs_density σ ω
  obtain ⟨hw, hQ⟩ := N.record_eq_withDensity σ ω hpm hp hobs m
  have hk := N.D
  have hwm : Measurable (wRatio (N.nullObs σ ω) p N.D m) := by
    cases m with
    | inl u => exact measurable_fun_sum measurable_const measurable_const
    | inr t =>
      refine measurable_fun_sum measurable_const ?_
      exact ((N.D.bm_k t).1).div hpm
  have : IsProbabilityMeasure (N.game.record m) := inferInstance
  exact anon_bound_of_density hn hwm hw hQ (MsgGame.measurable_V d ω) (MsgGame.V_mem d ω)
    (MsgGame.V_symm d ω) i

/-- **Lemma `lemma_anonymous_influence`.**  As in the paper, `|U_{n,ω}(m) - U_{n,ω}(m')|` is bounded by
applying `abs_U_sub_W` to `m` and to `m'` and using the triangle inequality. -/
theorem anonymous_influence {n : ℕ} (hn : 0 < n) (d : MRule A Msg n) (σ : MStrat Ω Msg) (ω : Ω)
    (i : Fin n) (m m' : Msg) :
    |N.game.U d σ ω i m - N.game.U d σ ω i m'| ≤ N.env.B * √(N.Lam - 1) / √(n : ℝ) := by
  have h1 := N.abs_U_sub_W hn d σ ω i m
  have h2 := N.abs_U_sub_W hn d σ ω i m'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have e : N.env.B * √(N.Lam - 1) / √(n : ℝ) = 2 * ((N.env.B / 2) * √((N.Lam - 1) / n)) := by
    rw [Real.sqrt_div' _ hnr.le]
    ring
  rw [e]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Equation `eq_rational_nonnull_message_bound`.** -/
theorem rational_nonnull_bound {n : ℕ} (hn : 0 < n) {d : MRule A Msg n} {σ : MStrat Ω Msg}
    (he : N.game.IsEq d σ) (ω : Ω) : N.game.q σ ω ≤ N.env.F (N.MG / √(n : ℝ)) :=
  MsgGame.q_le N.dom hn he ω

/-- **Proposition `prop_general_message_upper_bounds`.** -/
theorem prop_general_message (hFB : N.env.PiSQ < N.env.PiFB) :
    (∀ δ > 0, N.env.F δ = 0 → ∃ nStar : ℕ, ∀ n > nStar, N.game.Pi n = N.env.PiSQ) ∧
    (N.env.F 0 = 0 → HasDerivWithinAt N.env.F 0 (Ici 0) 0 → Tendsto N.game.Pi atTop (𝓝 N.env.PiSQ)) ∧
    (∀ t > 0, N.env.F 0 = 0 → HasDerivWithinAt N.env.F t (Ici 0) 0 →
      limsup N.game.Pi atTop < N.env.PiFB) :=
  MsgGame.prop_upper N.dom hFB

end NoisyModel

end OA

end NoisyVD
