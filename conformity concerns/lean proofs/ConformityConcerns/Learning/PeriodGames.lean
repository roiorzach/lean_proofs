import ConformityConcerns.Learning.NoLearning
import ConformityConcerns.LearnTheta.GaussianFilter
import ConformityConcerns.Examples.General

/-!
# Propositions A4 and A6: the period game at each realized history

`Learning/Assembly.lean` shows that the revealing rule is an equilibrium of every period game with
the right losses, and separately that social learning occurs when every period plays it. Here the
two are joined on the model's own objects: at a realized history `h^t`, the period game has the
conditional law of `v_t` given `h^t` as type distribution and `μ(h^t) = E(μ | h^t)` as norm.

* `RegularAt`: the paper's assumption at a realized history: the law of `v_t` given `h^t` has an
  everywhere-positive continuous density and the expected conformity loss is finite.
* `propA4_period_games`, `propA6_period_games`: at every realized history satisfying `RegularAt`,
  the revealing rule is an equilibrium satisfying `D1^∞` of that period game.
* `typeLaw_regular`: if `ν_t` has a bounded, continuous, everywhere-positive density and `μ`, `ν_t`
  have finite variances, the density assumption holds at almost every realized history, since the
  law of `v_t = μ + ν_t` given `h^t` is the convolution of the posterior about `μ` with the law of
  `ν_t`. This covers the log-concave and Gaussian cases that the paper mentions.
* `propA4_exists_density`, `propA4_exists_gaussian`: Proposition A4's equilibrium with no
  assumption left on the conditional laws.
-/

namespace CC.Learning

open MeasureTheory ProbabilityTheory Filter Topology
open CC.General
open CC.LearnTheta (vLaw psiN vLaw_psiN)
open scoped NNReal ENNReal

/-- The realized public history `h^t` of the actions `act`. -/
def histOf (act : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin t → ℝ := fun i => act i ω

/-- The public's conditional law of `v_t` given `h^t`. -/
noncomputable def typeLaw (P : Measure Ω) [IsFiniteMeasure P] (act : ℕ → Ω → ℝ) (t : ℕ) :
    Kernel (Fin t → ℝ) ℝ :=
  condDistrib (vt t) (histOf act t) P

/-- The revealing profile: `a_t = μ(h^t) + Φ(v_t - μ(h^t))`, with `μ(h^t)` the posterior mean given
the past types (which `learning_revealing` shows is the posterior mean given the history). -/
noncomputable abbrev revealProfile (Lμ Lν : Measure ℝ) (Φ : ℝ → ℝ) : ℕ → Ω → ℝ :=
  revealAct Φ (fun t => (law Lμ Lν)[muV | typeSigma t])

/-- The paper's assumption at a realized history: `v_t` given `h^t` has an everywhere-positive
continuous density and the expected conformity loss `E(f(v_t - μ(h^t)) | h^t)` is finite. -/
def RegularAt (f : ℝ → ℝ) (P : Measure Ω) [IsFiniteMeasure P] (act : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Prop :=
  TypeDist (typeLaw P act t (histOf act t ω)) ∧
    Integrable (fun b => f (b - postMean P act t ω)) (typeLaw P act t (histOf act t ω))

/-- At a realized history, the action is the revealing rule's, and the rule is an equilibrium
satisfying `D1^∞` of the period game with losses `g`, `f`, type distribution the law of `v_t`
given `h^t` and norm `μ(h^t)`. -/
def PeriodEqAt (g f Φ : ℝ → ℝ) (P : Measure Ω) [IsFiniteMeasure P] (act : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : Prop :=
  ∃ S : Setting, S.g = g ∧ S.F = typeLaw P act t (histOf act t ω) ∧ S.μ = postMean P act t ω ∧
    S.ℓ = (fun b => f (b - S.μ)) ∧ act t ω = S.μ + Φ (vt t ω - S.μ) ∧
    ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
      S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ

lemma adaptLoss_pos {f : ℝ → ℝ} (hf : AdaptLoss f) {z : ℝ} (hz : z ≠ 0) : 0 < f z := by
  have h := hf.strictConvex.2 (Set.mem_univ z) (Set.mem_univ (-z))
    (fun e => hz (by linarith)) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have e : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • -z = 0 := by simp
  rw [e, hf.zero, hf.even] at h
  simp only [smul_eq_mul] at h
  linarith

/-- A type distribution under which the conformity loss is integrable gives a period game. -/
lemma exists_setting {g f : ℝ → ℝ} (hg : AdaptLoss g) (hf : AdaptLoss f) {F : Measure ℝ}
    (hF : TypeDist F) (m : ℝ) (hint : Integrable (fun b => f (b - m)) F) :
    ∃ S : Setting, S.g = g ∧ S.F = F ∧ S.μ = m ∧ S.ℓ = fun b => f (b - m) := by
  have := hF.prob
  have hpos : 0 < ∫ b, f (b - m) ∂F := by
    have hnn : 0 ≤ fun b => f (b - m) := fun b => by
      rcases eq_or_ne b m with rfl | h
      · simp [hf.zero]
      · exact (adaptLoss_pos hf (sub_ne_zero.2 h)).le
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hs : Function.support (fun b => f (b - m)) = {m}ᶜ := by
      ext b
      simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro h rfl
        simp [hf.zero] at h
      · exact fun h => (adaptLoss_pos hf (sub_ne_zero.2 h)).ne'
    rw [hs, measure_compl (measurableSet_singleton m) (measure_ne_top _ _), measure_univ,
      hF.singleton_eq_zero m]
    simp
  exact ⟨⟨g, fun b => f (b - m), m, F, hg, confLoss_of_even hf m, hF, hint, hpos⟩, rfl, rfl, rfl,
    rfl⟩

/-- A rule that is an equilibrium of every period game is one at each regular realized history. -/
lemma periodEq_of_regular {g f Φ : ℝ → ℝ} (hg : AdaptLoss g) (hf : AdaptLoss f)
    (hΦ : ∀ S : Setting, S.g = g → S.ℓ = (fun b => f (b - S.μ)) →
      ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
        S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ)
    {P : Measure Ω} [IsFiniteMeasure P] {act : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hact : act t ω = postMean P act t ω + Φ (vt t ω - postMean P act t ω))
    (hr : RegularAt f P act t ω) : PeriodEqAt g f Φ P act t ω := by
  obtain ⟨S, hSg, hSF, hSμ, hSℓ⟩ := exists_setting hg hf hr.1 _ hr.2
  obtain ⟨φ, hE, hD⟩ := hΦ S hSg (by rw [hSℓ, hSμ])
  exact ⟨S, hSg, hSF, hSμ, by rw [hSℓ, hSμ], by rw [hSμ]; exact hact, φ, hE, hD⟩

/-- **Proposition A4, at each realized history.** If `κ ≤ κck`, there is a strictly increasing `Φ`
such that, when every period plays `μ(h^t) + Φ(v_t - μ(h^t))`, the rule is at every realized history
satisfying the paper's assumption an equilibrium satisfying `D1^∞` of the period game at that
history, and social learning about preferences occurs. -/
theorem propA4_period_games (κ : ℝ) (hκ : 0 < κ) (hκ' : κ ≤ κck) (Lμ Lν : Measure ℝ)
    [IsProbabilityMeasure Lμ] [IsProbabilityMeasure Lν] (hμ : Integrable id Lμ)
    (hν : Integrable id Lν) (hν0 : ∫ x, x ∂Lν = 0) :
    ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
      let P := law Lμ Lν
      let act := revealProfile Lμ Lν Φ
      (∀ t ω, RegularAt (fun z => κ * z ^ 2) P act t ω →
        PeriodEqAt (fun z => z ^ 2) (fun z => κ * z ^ 2) Φ P act t ω) ∧
      SocialLearningOccurs Lμ Lν (postMean P act) := by
  obtain ⟨Φ, hΦ, hΦc, -, hΦeq⟩ := propA4_revealing κ hκ hκ'
  obtain ⟨-, h2, -, h4⟩ := learning_revealing Lμ Lν hμ hν hν0 Φ hΦ hΦc
  exact ⟨Φ, hΦ, fun t ω hr => periodEq_of_regular CC.Examples.adaptLoss_sq
    (CC.Examples.adaptLoss_const_sq κ hκ) hΦeq (by rw [h2 t]; rfl) hr, h4⟩

/-- **Proposition A6 (ii), at each realized history.** Under the revelation condition, there is a
strictly increasing `Φ` such that, when every period plays `μ(h^t) + Φ(v_t - μ(h^t))`, the rule is
at every realized history satisfying the paper's assumption an equilibrium satisfying `D1^∞` of the
period game at that history, and `μ(h^t) → μ` almost surely. -/
theorem propA6_period_games (g f : ℝ → ℝ) (hg : AdaptLoss g) (hf : AdaptLoss f) (Lμ Lν : Measure ℝ)
    [IsProbabilityMeasure Lμ] [IsProbabilityMeasure Lν] (hμ : Integrable id Lμ)
    (hν : Integrable id Lν) (hν0 : ∫ x, x ∂Lν = 0) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcond : ∀ x, 0 < x → deriv f x ≤ (1 - β) * deriv g (β * x)) :
    ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
      let P := law Lμ Lν
      let act := revealProfile Lμ Lν Φ
      (∀ t ω, RegularAt f P act t ω → PeriodEqAt g f Φ P act t ω) ∧
      ∀ᵐ ω ∂P, Tendsto (fun t => postMean P act t ω) atTop (𝓝 (muV ω)) := by
  obtain ⟨Φ, hΦ, hΦc, -, hΦeq⟩ := propA6_ii_period g f hg hf β hβ0 hβ1 hcond
  obtain ⟨-, h2, h3, -⟩ := learning_revealing Lμ Lν hμ hν hν0 Φ hΦ hΦc
  exact ⟨Φ, hΦ, fun t ω hr => periodEq_of_regular hg hf hΦeq (by rw [h2 t]; rfl) hr, h3⟩

/-- `ν_t` is independent of `μ` and the earlier noises. -/
lemma indep_past_noise (Lμ Lν : Measure ℝ) [IsProbabilityMeasure Lμ] [IsProbabilityMeasure Lν]
    (t : ℕ) :
    IndepFun (fun ω : Ω => (ω.1, fun i : Fin t => ω.2 i)) (fun ω : Ω => ω.2 t) (law Lμ Lν) := by
  set Q := Measure.infinitePi fun _ : ℕ => Lν with hQ
  let r : (ℕ → ℝ) → Fin t → ℝ := fun n i => n i
  let e : (ℕ → ℝ) → ℝ := fun n => n t
  have hr : Measurable r := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have he : Measurable e := measurable_pi_apply _
  have hre : IndepFun r e Q := by
    have h := (iIndepFun_infinitePi (P := fun _ : ℕ => Lν) (X := fun _ x => x)
      (fun _ => measurable_id)).indepFun_finset (Finset.range t) {t} (by simp)
      (fun _ => measurable_pi_apply _)
    exact h.comp (φ := fun (x : Finset.range t → ℝ) (i : Fin t) => x ⟨i, Finset.mem_range.2 i.2⟩)
      (ψ := fun x : ({t} : Finset ℕ) → ℝ => x ⟨t, Finset.mem_singleton_self t⟩)
      (measurable_pi_iff.2 fun i => measurable_pi_apply _) (measurable_pi_apply _)
  have hj : (Q.map r).prod (Q.map e) = Q.map (fun n => (r n, e n)) :=
    ((indepFun_iff_map_prod_eq_prod_map_map hr.aemeasurable he.aemeasurable).1 hre).symm
  have h1 : (law Lμ Lν).map (fun ω : Ω => (ω.1, r ω.2)) = Lμ.prod (Q.map r) := by
    rw [← Measure.map_id (μ := Lμ), Measure.map_prod_map _ _ measurable_id hr]
    simp [law, Prod.map_def, hQ]
  have h2 : (law Lμ Lν).map (fun ω : Ω => e ω.2) = Q.map e := by
    rw [show (fun ω : Ω => e ω.2) = e ∘ Prod.snd from rfl, ← Measure.map_map he measurable_snd]
    simp [law, hQ]
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  change (law Lμ Lν).map (fun ω : Ω => ((ω.1, r ω.2), e ω.2)) =
    ((law Lμ Lν).map (fun ω : Ω => (ω.1, r ω.2))).prod ((law Lμ Lν).map (fun ω : Ω => e ω.2))
  rw [h1, h2]
  apply (MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin t → ℝ) (γ := ℝ)).map_measurableEquiv_injective
  rw [Measure.prodAssoc_prod, hj, Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  have hmap : Lμ.prod (Q.map (fun n => (r n, e n))) =
      (Lμ.prod Q).map (Prod.map id (fun n => (r n, e n))) := by
    rw [← Measure.map_prod_map _ _ measurable_id (hr.prodMk he), Measure.map_id]
  rw [hmap]
  rfl

/-- **The density assumption, from primitives.** If `ν_t` has a bounded, continuous,
everywhere-positive density and `μ`, `ν_t` have finite variances, then at almost every realized
history of any profile whose history depends only on past types, the law of `v_t` given `h^t` has
an everywhere-positive continuous density and a finite variance. -/
theorem typeLaw_regular (ψ : ℝ → ℝ) (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x)
    (hψb : ∃ C, ∀ x, ψ x ≤ C) (Lμ Lν : Measure ℝ) [IsProbabilityMeasure Lμ]
    [IsProbabilityMeasure Lν] (hLν : Lν = vLaw ψ) (hμ2 : Integrable (fun x => x ^ 2) Lμ)
    (hν2 : Integrable (fun x => x ^ 2) Lν) (act : ℕ → Ω → ℝ) (hact : ∀ i, Measurable (act i))
    (t : ℕ) (hle : histSigma act t ≤ typeSigma t) :
    ∀ᵐ ω ∂(law Lμ Lν), TypeDist (typeLaw (law Lμ Lν) act t (histOf act t ω)) ∧
      Integrable (fun b => b ^ 2) (typeLaw (law Lμ Lν) act t (histOf act t ω)) := by
  subst hLν
  set P := law Lμ (vLaw ψ) with hP
  obtain ⟨C, hC⟩ := hψb
  have hX : Measurable (histOf act t) := measurable_pi_iff.2 fun i => hact i
  have hV : Measurable (fun ω : Ω => ω.2 t) := (measurable_pi_apply t).comp measurable_snd
  let A : Ω → ℝ × (Fin t → ℝ) := fun ω => (ω.1, fun i => ω.2 i)
  have hT : typeSigma t ≤ MeasurableSpace.comap A inferInstance :=
    comap_le_of_coord fun i hi =>
      (show Measurable (fun p : ℝ × (Fin t → ℝ) => p.1 + p.2 ⟨i, hi⟩) by fun_prop).comp
        (comap_measurable A)
  have hμA : Measurable[MeasurableSpace.comap A inferInstance] muV :=
    (measurable_fst : Measurable (Prod.fst : ℝ × (Fin t → ℝ) → ℝ)).comp (comap_measurable A)
  have hXY : Measurable[MeasurableSpace.comap A inferInstance]
      (fun ω => (histOf act t ω, muV ω)) :=
    ((comap_measurable (histOf act t)).mono (hle.trans hT) le_rfl).prodMk hμA
  have hind : IndepFun (fun ω => (histOf act t ω, muV ω)) (fun ω : Ω => ω.2 t) P := by
    have h := indep_past_noise Lμ (vLaw ψ) t
    rw [IndepFun_iff_Indep] at h ⊢
    exact indep_of_indep_of_le_left h hXY.comap_le
  have hmapV : P.map (fun ω : Ω => ω.2 t) = vLaw ψ := by
    rw [show (fun ω : Ω => ω.2 t) = (fun n : ℕ → ℝ => n t) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_apply t) measurable_snd, hP]
    simp only [law, Measure.map_snd_prod, measure_univ, one_smul]
    exact Measure.infinitePi_map_eval _ t
  have h := LearnTheta.condDistrib_add_of_indep P hX measurable_muV hV hind
  rw [hmapV] at h
  have hint : Integrable (fun p : (Fin t → ℝ) × ℝ => p.2 ^ 2)
      (P.map fun ω => (histOf act t ω, muV ω)) :=
    (integrable_map_measure (measurable_snd.pow_const 2).aestronglyMeasurable
      (hX.prodMk measurable_muV).aemeasurable).2 (hμ2.comp_fst _)
  filter_upwards [h, hint.condDistrib_ae hX.aemeasurable measurable_muV.aemeasurable] with ω h1 h2
  have hF : typeLaw P act t (histOf act t ω) =
      (condDistrib muV (histOf act t) P (histOf act t ω)).conv (vLaw ψ) := by
    unfold typeLaw
    rw [show vt t = fun ω : Ω => ω.2 t + muV ω from funext fun ω => add_comm _ _]
    exact h1
  rw [hF]
  set η := condDistrib muV (histOf act t) P (histOf act t ω)
  refine ⟨⟨by unfold Measure.conv; infer_instance, LearnTheta.ExAux.convDens ψ η,
    LearnTheta.ExAux.continuous_convDens hψc hψpos hC η,
    LearnTheta.ExAux.convDens_pos hψc.measurable hψpos hC η,
    LearnTheta.ExAux.conv_vLaw_eq hψc.measurable hψpos hC η⟩, ?_⟩
  rw [← lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall fun x => sq_nonneg x)]
  refine ne_top_of_le_ne_top ?_ (LearnTheta.AsmAux.lintegral_sq_conv_le η (vLaw ψ))
  rw [LearnTheta.AsmAux.lintegral_sq_eq _ h2, LearnTheta.AsmAux.lintegral_sq_eq _ hν2]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top⟩

lemma integrable_quad_loss {F : Measure ℝ} [IsProbabilityMeasure F] (κ m : ℝ)
    (h : Integrable (fun b => b ^ 2) F) : Integrable (fun b => κ * (b - m) ^ 2) F := by
  have hL : MemLp id 2 F := (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h
  exact (hL.sub (memLp_const m)).integrable_sq.const_mul κ

lemma integrable_of_sq {L : Measure ℝ} [IsProbabilityMeasure L]
    (h : Integrable (fun x => x ^ 2) L) : Integrable id L :=
  ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h).integrable one_le_two

/-- **Proposition A4, `κ ≤ κck`, from primitives.** If `ν_t` has mean zero and a bounded,
continuous, everywhere-positive density, and `μ`, `ν_t` have finite variances, there is an
equilibrium that at almost every realized history is a fully revealing equilibrium satisfying
`D1^∞` of the period game at that history, and social learning about preferences occurs in it. -/
theorem propA4_exists_density (κ : ℝ) (hκ : 0 < κ) (hκ' : κ ≤ κck) (ψ : ℝ → ℝ)
    (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x) (hψb : ∃ C, ∀ x, ψ x ≤ C) (Lμ Lν : Measure ℝ)
    [IsProbabilityMeasure Lμ] [IsProbabilityMeasure Lν] (hLν : Lν = vLaw ψ)
    (hμ2 : Integrable (fun x => x ^ 2) Lμ) (hν2 : Integrable (fun x => x ^ 2) Lν)
    (hν0 : ∫ x, x ∂Lν = 0) :
    ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
      let P := law Lμ Lν
      let act := revealProfile Lμ Lν Φ
      (∀ t, ∀ᵐ ω ∂P, PeriodEqAt (fun z => z ^ 2) (fun z => κ * z ^ 2) Φ P act t ω) ∧
      SocialLearningOccurs Lμ Lν (postMean P act) := by
  obtain ⟨Φ, hΦ, hΦc, -, hΦeq⟩ := propA4_revealing κ hκ hκ'
  obtain ⟨h1, h2, -, h4⟩ :=
    learning_revealing Lμ Lν (integrable_of_sq hμ2) (integrable_of_sq hν2) hν0 Φ hΦ hΦc
  refine ⟨Φ, hΦ, fun t => ?_, h4⟩
  have hpm : ∀ i, Measurable ((law Lμ Lν)[muV | typeSigma i]) := fun i =>
    (stronglyMeasurable_condExp.measurable).mono (typeSigma_le i) le_rfl
  have hact : ∀ i, Measurable (revealProfile Lμ Lν Φ i) := fun i =>
    (hpm i).add (hΦc.measurable.comp ((measurable_vt i).sub (hpm i)))
  filter_upwards [typeLaw_regular ψ hψc hψpos hψb Lμ Lν hLν hμ2 hν2 _ hact t (h1 t).le] with ω hr
  have := hr.1.prob
  exact periodEq_of_regular CC.Examples.adaptLoss_sq (CC.Examples.adaptLoss_const_sq κ hκ) hΦeq
    (by rw [h2 t]; rfl) ⟨hr.1, integrable_quad_loss κ _ hr.2⟩

/-- **Proposition A4, `κ ≤ κck`, in the Linear-Gaussian model** (`μ ~ N(0, σ²)`, `ν_t ~ N(0, 1)`):
all the assumptions on the conditional laws hold. -/
theorem propA4_exists_gaussian (σ2 : ℝ≥0) (κ : ℝ) (hκ : 0 < κ) (hκ' : κ ≤ κck) :
    ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
      let P := law (gaussianReal 0 σ2) (gaussianReal 0 1)
      let act := revealProfile (gaussianReal 0 σ2) (gaussianReal 0 1) Φ
      (∀ t, ∀ᵐ ω ∂P, PeriodEqAt (fun z => z ^ 2) (fun z => κ * z ^ 2) Φ P act t ω) ∧
      SocialLearningOccurs (gaussianReal 0 σ2) (gaussianReal 0 1) (postMean P act) :=
  propA4_exists_density κ hκ hκ' psiN LearnTheta.psiN_continuous
    (fun _ => gaussianPDFReal_pos _ _ _ one_ne_zero) LearnTheta.psiN_bdd _ _ vLaw_psiN.symm
    (memLp_id_gaussianReal (μ := 0) (v := σ2) 2).integrable_sq
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq (integral_id_gaussianReal)

end CC.Learning
