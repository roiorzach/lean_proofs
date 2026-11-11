import WhoVsWhen.Lemma3
import WhoVsWhen.Lemma4
import WhoVsWhen.Remark1
import WhoVsWhen.Prop1
import WhoVsWhen.Prop2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The paper's environment: the results are not vacuous

The paper's environment has independent states `θᵢ ∼ U[-θ̄ᵢ, θ̄ᵢ]`. It is built here as the product
measure `unif θ̄₁ ⊗ unif θ̄₂` on `ℝ × ℝ` with `θ₁ = fst`, `θ₂ = snd` (`uniformEnv`). It satisfies every
assumption of the model `Env`, with `σᵢ² = θ̄ᵢ²/3`. It serves as the environment for Lemmas 3 and 4.

The `example_*` theorems show that the hypotheses of the other results can be met:
* `example_belief`: a posterior belief as in Lemmas 1 and 2 (uniform on `[-1, 1]`).
* `example_lemma2_seq`, `example_lemma2_conc`: truthful limit partitions for Lemma 2.
* `example_remark1_public`, `example_remark1_noComm`: Remark 1 on the paper's environment.
* `example_prop1_i`, `example_prop1_ii`, `example_prop2`: Propositions 1 and 2 with concrete
  parameters.
-/

namespace WhoVsWhen

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- The uniform distribution on `[-a, a]`. -/
noncomputable def unif (a : ℝ) : Measure ℝ :=
  (volume (Icc (-a) a))⁻¹ • volume.restrict (Icc (-a) a)

lemma volume_Icc_sym (a : ℝ) : volume (Icc (-a) a) = ENNReal.ofReal (2 * a) := by
  rw [Real.volume_Icc]; ring_nf

section Unif

variable (a : ℝ) [ha : Fact (0 < a)]

instance unif_isProb : IsProbabilityMeasure (unif a) := by
  constructor
  have h0 : volume (Icc (-a) a) ≠ 0 := by
    rw [volume_Icc_sym]; exact (ENNReal.ofReal_pos.mpr (by linarith [ha.out])).ne'
  have h1 : volume (Icc (-a) a) ≠ ⊤ := by rw [volume_Icc_sym]; exact ENNReal.ofReal_ne_top
  simp only [unif, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 h1

lemma integral_unif (f : ℝ → ℝ) :
    ∫ x, f x ∂(unif a) = 1 / (2 * a) * ∫ x in (-a)..a, f x := by
  have hpos := ha.out
  unfold unif
  rw [integral_smul_measure, volume_Icc_sym, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith)]
  simp [smul_eq_mul, one_div]

lemma integral_unif_id : ∫ x, x ∂(unif a) = 0 := by
  rw [integral_unif a (fun x => x), integral_id]; ring

lemma integral_unif_sq : ∫ x, x ^ 2 ∂(unif a) = uniformVar a := by
  rw [integral_unif a (fun x => x ^ 2)]; rfl

lemma memLp_unif : MemLp (fun x : ℝ => x) 2 (unif a) := by
  refine MemLp.of_bound (by fun_prop) a ?_
  have h : ∀ᵐ x ∂(volume.restrict (Icc (-a) a)), x ∈ Icc (-a) a :=
    ae_restrict_mem measurableSet_Icc
  have h' : ∀ᵐ x ∂(unif a), x ∈ Icc (-a) a := Measure.ae_smul_measure h _
  filter_upwards [h'] with x hx
  simp only [Real.norm_eq_abs]; exact abs_le.mpr ⟨hx.1, hx.2⟩

lemma integrable_unif_id : Integrable (fun x : ℝ => x) (unif a) :=
  (memLp_unif a).integrable one_le_two

lemma integrable_unif_sq : Integrable (fun x : ℝ => x ^ 2) (unif a) := (memLp_unif a).integrable_sq

end Unif

section Product

variable (a₁ a₂ : ℝ) [Fact (0 < a₁)] [Fact (0 < a₂)]

/-- The paper's environment as a probability space: `(θ₁, θ₂) ∼ U[-θ̄₁, θ̄₁] ⊗ U[-θ̄₂, θ̄₂]`. -/
noncomputable abbrev Pu : Measure (ℝ × ℝ) := (unif a₁).prod (unif a₂)

lemma indep_fst_snd : IndepFun Prod.fst Prod.snd (Pu a₁ a₂) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  simp only [Pu, Prod.mk.eta, Measure.map_id', Measure.map_fst_prod, Measure.map_snd_prod,
    measure_univ, one_smul]

/-- A pair of message σ-algebras on `ℝ × ℝ`, each coarser than its sender's state. (Bundled so that
the σ-algebras are not mistaken for the ambient one.) -/
structure MsgPair where
  F₁ : MeasurableSpace (ℝ × ℝ)
  F₂ : MeasurableSpace (ℝ × ℝ)
  hF₁ : F₁ ≤ MeasurableSpace.comap Prod.fst inferInstance
  hF₂ : F₂ ≤ MeasurableSpace.comap Prod.snd inferInstance

/-- The paper's environment with the messages `M`. -/
noncomputable def uniformEnv (M : MsgPair) : Env (ℝ × ℝ) (Pu a₁ a₂) where
  θ₁ := Prod.fst
  θ₂ := Prod.snd
  F₁ := M.F₁
  F₂ := M.F₂
  meas₁ := measurable_fst
  meas₂ := measurable_snd
  hF₁ := M.hF₁
  hF₂ := M.hF₂
  indep := indep_fst_snd a₁ a₂
  L2₁ := (memLp_unif a₁).comp_fst (unif a₂)
  L2₂ := (memLp_unif a₂).comp_snd (unif a₁)
  mean₁ := by
    have := integral_fun_fst (μ := unif a₁) (ν := unif a₂) (fun x : ℝ => x)
    simp only [probReal_univ, one_smul] at this
    rw [this, integral_unif_id]
  mean₂ := by
    have := integral_fun_snd (μ := unif a₁) (ν := unif a₂) (fun x : ℝ => x)
    simp only [probReal_univ, one_smul] at this
    rw [this, integral_unif_id]

variable {a₁ a₂}

lemma uniformEnv_s₁ (M : MsgPair) : (uniformEnv a₁ a₂ M).s₁ = uniformVar a₁ := by
  show ∫ ω, ω.1 ^ 2 ∂(Pu a₁ a₂) = uniformVar a₁
  have := integral_fun_fst (μ := unif a₁) (ν := unif a₂) (fun x : ℝ => x ^ 2)
  simp only [probReal_univ, one_smul] at this
  rw [this, integral_unif_sq]

lemma uniformEnv_s₂ (M : MsgPair) : (uniformEnv a₁ a₂ M).s₂ = uniformVar a₂ := by
  show ∫ ω, ω.2 ^ 2 ∂(Pu a₁ a₂) = uniformVar a₂
  have := integral_fun_snd (μ := unif a₁) (ν := unif a₂) (fun x : ℝ => x ^ 2)
  simp only [probReal_univ, one_smul] at this
  rw [this, integral_unif_sq]

end Product

lemma half_unit : Unit01 (1 / 2 : ℝ) := ⟨by norm_num, by norm_num⟩
lemma quarter_unit : Unit01 (1 / 4 : ℝ) := ⟨by norm_num, by norm_num⟩
lemma threeQuarter_unit : Unit01 (3 / 4 : ℝ) := ⟨by norm_num, by norm_num⟩

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
instance : Fact ((0 : ℝ) < 2) := ⟨two_pos⟩

/-- The uniform environment with `θ̄₁ = θ̄₂ = 1` and no communication. -/
noncomputable def envNoComm : Env (ℝ × ℝ) (Pu 1 1) := uniformEnv 1 1 ⟨⊥, ⊥, bot_le, bot_le⟩

/-- The uniform environment with `θ̄₁ = θ̄₂ = 1` where each message reveals its sender's state. -/
noncomputable def envFull : Env (ℝ × ℝ) (Pu 1 1) :=
  uniformEnv 1 1 ⟨MeasurableSpace.comap Prod.fst inferInstance,
    MeasurableSpace.comap Prod.snd inferInstance, le_rfl, le_rfl⟩

lemma uniformVar_one_pos : 0 < uniformVar 1 := by rw [uniformVar_eq one_pos]; norm_num

/-- A posterior belief satisfying the hypotheses of Lemmas 1 and 2: uniform on `[-1, 1]`. -/
theorem example_belief :
    IsProbabilityMeasure (unif 1) ∧ Integrable (fun x : ℝ => x) (unif 1) ∧
      Integrable (fun x : ℝ => x ^ 2) (unif 1) ∧ ∫ x, x ∂(unif 1) = 0 :=
  ⟨inferInstance, integrable_unif_id 1, integrable_unif_sq 1, integral_unif_id 1⟩

/-- Lemma 2, sequential case: with the leader's state uniform on `[-1, 1]`, `r₁ = 1/2` and
`r₂ = 1/4`, the geometric partition of `[-2, 2]` is a truthful limit partition of the follower's
state. -/
theorem example_lemma2_seq :
    TruthfulLimitPartition (followerMsgLoss (1 / 2) (1 / 4) (unif 1)) 2
      (geomPartition 2 (φSeq (1 / 2) (1 / 4))) (geomPartition 2 (φSeq (1 / 2) (1 / 4))) :=
  geom_truthful (φSeq_pos half_unit quarter_unit) two_pos
    (fun _ _ _ hl hu hlu => follower_indiff_iff (integrable_unif_id 1) (integrable_unif_sq 1)
      (integral_unif_id 1) half_unit quarter_unit hl hu hlu)

/-- The law of `(θ₂, μ₂)` when `θ₂` is uniform on `[-1, 1]` and unit 2's message is
uninformative. -/
noncomputable def rhoBabble : Measure (ℝ × ℝ) := (unif 1).map (fun x => (x, 0))

instance : IsProbabilityMeasure rhoBabble := by unfold rhoBabble; infer_instance

/-- Lemma 2, concurrent case: against `rhoBabble`, the geometric partition of `[-1, 1]` is a
truthful limit partition of unit 1's state when `r₁ = 1/2`, `r₂ = 1/4`. -/
theorem example_lemma2_conc :
    TruthfulLimitPartition (concMsgLoss (1 / 2) (1 / 4) rhoBabble) 1
      (geomPartition 1 (φConc (1 / 2) (1 / 4))) (geomPartition 1 (φConc (1 / 2) (1 / 4))) := by
  have hmeas : Measurable (fun x : ℝ => (x, (0 : ℝ))) := by fun_prop
  have hx : MemLp (fun p : ℝ × ℝ => p.1) 2 rhoBabble := by
    rw [rhoBabble, memLp_map_measure_iff (by fun_prop) hmeas.aemeasurable]; exact memLp_unif 1
  have hy : MemLp (fun p : ℝ × ℝ => p.2) 2 rhoBabble := by
    rw [rhoBabble, memLp_map_measure_iff (by fun_prop) hmeas.aemeasurable]; exact memLp_const 0
  have hm1 : ∫ p, p.1 ∂rhoBabble = 0 := by
    rw [rhoBabble, integral_map hmeas.aemeasurable (by fun_prop)]; exact integral_unif_id 1
  have hm2 : ∫ p, p.2 ∂rhoBabble = 0 := by
    rw [rhoBabble, integral_map hmeas.aemeasurable (by fun_prop)]; simp
  exact geom_truthful (φConc_pos half_unit quarter_unit) one_pos
    (fun _ _ _ hl hu hlu => conc_indiff_iff hx hy hm1 hm2 half_unit quarter_unit hl hu hlu)

/-- Remark 1, public information, on the paper's environment with `θ̄₁ = θ̄₂ = 1`. -/
theorem example_remark1_public :
    envFull.totConc (1 / 2) (1 / 4) < envFull.totSeq₁ (1 / 2) (1 / 4) ∧
      envFull.totConc (1 / 2) (1 / 4) < envFull.totSeq₂ (1 / 2) (1 / 4) := by
  have h1 : envFull.s₁ = uniformVar 1 := uniformEnv_s₁ _
  have h2 : envFull.s₂ = uniformVar 1 := uniformEnv_s₂ _
  exact (remark1 half_unit quarter_unit).1 envFull rfl rfl
    (by rw [h1, h2]; linarith [uniformVar_one_pos])

/-- Remark 1, no communication and equal volatilities, on the paper's environment: with
`r₁ = 1/2 < r₂ = 3/4`, unit 1 should lead. -/
theorem example_remark1_noComm :
    envNoComm.totSeq₁ (1 / 2) (3 / 4) < envNoComm.totSeq₂ (1 / 2) (3 / 4) ∧
      envNoComm.totSeq₁ (1 / 2) (3 / 4) < envNoComm.totConc (1 / 2) (3 / 4) := by
  have h1 : envNoComm.s₁ = uniformVar 1 := uniformEnv_s₁ _
  have h2 : envNoComm.s₂ = uniformVar 1 := uniformEnv_s₂ _
  exact ((remark1 half_unit threeQuarter_unit).2.2 envNoComm rfl rfl
    (by rw [h1]; exact uniformVar_one_pos) (by rw [h1, h2])).1 (by norm_num)

/-- Proposition 1(i) with a uniform posterior about the follower's state and a leader's state
(`1`) that differs from its mean (`0`). -/
theorem example_prop1_i :
    coordConcPost (1 / 2) (1 / 4) 1 (unif 1) < coordSeqPost (1 / 2) (1 / 4) 1 (unif 1) :=
  (((prop1 (Ω := ℝ × ℝ) (P := Pu 1 1)).1 (1 / 2) (1 / 4) half_unit quarter_unit (unif 1)
    (integrable_unif_id 1) (integrable_unif_sq 1) 1).2).mpr (by rw [integral_unif_id]; norm_num)

/-- Proposition 1(ii) on the paper's environment without communication (so `c₁ = c₂`): with
`r₁ = 1/4 < r₂ = 1/2`, unit 1 leading has the lower coordination loss. -/
theorem example_prop1_ii :
    ∫ ω, (envNoComm.seqD₁ (1 / 4) (1 / 2) ω - envNoComm.seqD₂ (1 / 4) (1 / 2) ω) ^ 2 ∂(Pu 1 1) <
      ∫ ω, (envNoComm.swap.seqD₁ (1 / 2) (1 / 4) ω - envNoComm.swap.seqD₂ (1 / 2) (1 / 4) ω) ^ 2
        ∂(Pu 1 1) := by
  have h1 : envNoComm.s₁ = uniformVar 1 := uniformEnv_s₁ _
  have h2 : envNoComm.s₂ = uniformVar 1 := uniformEnv_s₂ _
  have hc : envNoComm.c₁ = envNoComm.c₂ := by
    rw [envNoComm.c₁_eq_of_bot rfl, envNoComm.c₂_eq_of_bot rfl, h1, h2]
  exact ((prop1 (Ω := ℝ × ℝ) (P := Pu 1 1)).2 envNoComm (1 / 4) (1 / 2) quarter_unit half_unit hc
    (by rw [h1, h2]; linarith [uniformVar_one_pos])).mpr (by norm_num)

/-- Proposition 2(ii) with concrete parameters: with `θ̄₁ = θ̄₂ = 1` and `r₁ = 1/2 > r₂ = 1/4`,
unit 1 leading induces less aggregate information loss. -/
theorem example_prop2 : aggSeq₁ 1 1 (1 / 2) (1 / 4) < aggSeq₂ 1 1 (1 / 2) (1 / 4) :=
  ((prop2 half_unit quarter_unit one_pos one_pos).2.1 rfl).mpr (by norm_num)

end WhoVsWhen
