import ConformityConcerns.LinearPaths.Beliefs
import ConformityConcerns.Bridge.Asymptotic
import ConformityConcerns.Dynamics.Unbounded

/-!
# The signaling equilibrium of the dynamic game

Definition 1 of the paper: a signaling equilibrium is a perfect Bayesian equilibrium satisfying
Linearity and Social Optimality at each history. Here `IsSignalingProfile κ S₁ G σ` says that a
measurable strategy profile `σ` is, at almost every on-path history with public beliefs `N(m, S)`,
a signaling equilibrium of the period game at that history.

* `exists_signalingProfile`: such a profile exists.
* `signalingProfile_act`: in every such profile, almost surely each action is `eqAct`, the action
  used in `Bridge/` (`eqAct` is the rule `eqFormR` at the current public beliefs).
* `signalingProfile_post_ae`: the posterior means given the realised history of `σ` are almost surely
  the posterior means `postTheta`, `postMu` used in `Bridge/`.
* `prop2_signalingProfile`, `corollaryA2_signalingProfile`, `corollaryA3_signalingProfile`,
  `corollaryA2_asymptotic_profile`, `corollaryA3_asymptotic_profile`: Proposition 2 and
  Corollaries A2 and A3 (social learning and asymptotic payoffs) hold in every such profile.
-/

namespace CC.LinearPaths

open MeasureTheory ProbabilityTheory Filter Topology
open CC.Bridge

set_option warn.classDefReducibility false

/-! ### The period signaling equilibrium as an explicit rule -/

/-- The action of the signaling equilibrium at a history with public means `(m0, m1)`, public
covariance `S`, weight `γ` and conformity concern `κ`, for private information `x = (s, v)`. -/
noncomputable def eqFormR (κ m0 m1 : ℝ) (S : M2) (γ : ℝ) (x : E2) : ℝ :=
  haveI := Classical.propDecidable (revCrit κ S γ)
  if revCrit κ S γ then
    γ * m0 + m1 + LG.lplus κ (sens S γ) *
      (loadA S γ 0 * x 0 + loadA S γ 1 * x 1 - (loadA S γ 0 * m0 + loadA S γ 1 * m1))
  else γ * m0 + m1

/-- The rule `eqFormR` at public beliefs with mean `m`. -/
noncomputable def eqForm (κ : ℝ) (m : E2) (S : M2) (γ : ℝ) : E2 → ℝ := eqFormR κ (m 0) (m 1) S γ

/-- The slope of `eqForm` on `Z`. -/
noncomputable def kE (κ : ℝ) (S : M2) (γ : ℝ) : ℝ :=
  haveI := Classical.propDecidable (revCrit κ S γ)
  if revCrit κ S γ then LG.lplus κ (sens S γ) else 0

/-- The intercept of `eqForm`. -/
noncomputable def bE (κ : ℝ) (m : E2) (S : M2) (γ : ℝ) : ℝ :=
  haveI := Classical.propDecidable (revCrit κ S γ)
  if revCrit κ S γ then (1 - LG.lplus κ (sens S γ)) * (γ * m 0 + m 1) else γ * m 0 + m 1

section Period

variable {κ : ℝ} {m : E2} {S : M2} {γ : ℝ}

lemma integrable_coord' (m : E2) (S : M2) (i : Fin 2) :
    Integrable (fun x : E2 => x i) (multivariateGaussian m S) := by
  rw [← EuclideanSpace.coe_proj]
  exact IsGaussian.integrable_dual _ _

lemma Zg_sub (m : E2) (S : M2) (γ : ℝ) (x : E2) :
    Zg m S γ x = γ * m 0 + m 1 +
      (loadA S γ 0 * x 0 + loadA S γ 1 * x 1 - (loadA S γ 0 * m 0 + loadA S γ 1 * m 1)) := by
  simp only [Zg, loadA, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma integral_affine_coord (hS1 : (S + 1).PosSemidef) (a b c : ℝ) :
    ∫ x : E2, a * x 0 + b * x 1 + c ∂(multivariateGaussian m (S + 1)) =
      a * m 0 + b * m 1 + c := by
  have h0 := integrable_coord' m (S + 1) 0
  have h1 := integrable_coord' m (S + 1) 1
  have hadd : Integrable (fun x : E2 => a * x 0 + b * x 1) (multivariateGaussian m (S + 1)) :=
    (h0.const_mul a).add (h1.const_mul b)
  rw [integral_add hadd (integrable_const c), integral_add (h0.const_mul a) (h1.const_mul b),
    integral_const_mul, integral_const_mul, integral_coord_mvG hS1 0, integral_coord_mvG hS1 1,
    integral_const, probReal_univ, one_smul]

lemma EZ_eq (hS : S.PosSemidef) (γ : ℝ) : EZ m S γ = γ * m 0 + m 1 := by
  have hS1 : (S + 1).PosSemidef := hS.add Matrix.PosDef.one.posSemidef
  have e : Zg m S γ = fun x : E2 =>
      (γ * gainK S 0 0) * x 0 + (1 + γ * gainK S 0 1) * x 1 +
        γ * (m 0 - gainK S 0 0 * m 0 - gainK S 0 1 * m 1) := by
    funext x; simp only [Zg]; ring
  unfold EZ
  rw [e, integral_affine_coord hS1]
  ring

lemma eqForm_eq_affine (κ : ℝ) (m : E2) (S : M2) (γ : ℝ) :
    eqForm κ m S γ = fun x => kE κ S γ * Zg m S γ x + bE κ m S γ := by
  funext x
  unfold eqForm eqFormR kE bE
  by_cases h : revCrit κ S γ
  · simp only [h, ↓reduceIte]
    rw [Zg_sub]
    ring
  · simp only [h, ↓reduceIte]
    ring

lemma kE_pos_iff (hc : revCrit κ S γ) : 0 < kE κ S γ := by
  unfold kE
  simp only [hc, ↓reduceIte]
  exact LG.lplus_pos _ _

lemma kE_of_not (hc : ¬ revCrit κ S γ) : kE κ S γ = 0 := by
  unfold kE
  simp only [hc, ↓reduceIte]

/-- Two affine functions of `Z` that agree almost surely have the same coefficients. -/
lemma affine_unique (hS : S.PosSemidef) {k b k' b' : ℝ}
    (h : (fun x => k * Zg m S γ x + b) =ᵐ[multivariateGaussian m (S + 1)]
      fun x => k' * Zg m S γ x + b') : k = k' ∧ b = b' := by
  have hk : k = k' := by
    by_contra hne
    have hd : k - k' ≠ 0 := sub_ne_zero.2 hne
    have hZ : Zg m S γ =ᵐ[multivariateGaussian m (S + 1)] fun _ => (b' - b) / (k - k') := by
      filter_upwards [h] with x hx
      have hx' : k * Zg m S γ x + b = k' * Zg m S γ x + b' := hx
      field_simp
      linarith
    have hE : EZ m S γ = (b' - b) / (k - k') := by
      unfold EZ
      rw [integral_congr_ae hZ, integral_const, probReal_univ, one_smul]
    have h0 := integral_Zg_sub_sq (m := m) hS γ
    have hzero : (fun x => (Zg m S γ x - EZ m S γ) ^ 2) =ᵐ[multivariateGaussian m (S + 1)]
        fun _ => 0 := by
      filter_upwards [hZ] with x hx
      rw [hx, hE, sub_self, zero_pow two_ne_zero]
    rw [integral_congr_ae hzero, integral_zero] at h0
    exact (cm_varZ_pos hS γ).ne h0
  refine ⟨hk, ?_⟩
  subst hk
  obtain ⟨x, hx⟩ := h.exists
  have hx' : k * Zg m S γ x + b = k * Zg m S γ x + b' := hx
  linarith

lemma kco_congr {a a' : E2 → ℝ} (h : a =ᵐ[multivariateGaussian m (S + 1)] a') :
    kco m S γ a = kco m S γ a' ∧ bco m S γ a = bco m S γ a' := by
  have hs : slope m S γ a = slope m S γ a' := by
    unfold slope
    congr 1
    refine integral_congr_ae (h.mono fun x hx => ?_)
    simp [hx]
  refine ⟨by rw [kco, kco, hs], ?_⟩
  rw [bco, bco, hs, integral_congr_ae h]

/-- The regression coefficients of `eqForm`. -/
lemma kco_bco_eqForm (hS : S.PosSemidef) :
    kco m S γ (eqForm κ m S γ) = kE κ S γ ∧ bco m S γ (eqForm κ m S γ) = bE κ m S γ := by
  have haff := eqForm_eq_affine κ m S γ
  by_cases hc : revCrit κ S γ
  · have hrev : (gameAt m S γ κ).IsRevealing (eqForm κ m S γ) :=
      ⟨kE κ S γ, bE κ m S γ, kE_pos_iff hc, Eventually.of_forall fun x => congrFun haff x⟩
    obtain ⟨-, -, hform⟩ := coef_reveal hS hrev
    have hae : (fun x => kE κ S γ * Zg m S γ x + bE κ m S γ) =ᵐ[multivariateGaussian m (S + 1)]
        fun x => kco m S γ (eqForm κ m S γ) * Zg m S γ x + bco m S γ (eqForm κ m S γ) := by
      filter_upwards [hform] with x hx
      rw [← hx, haff]
    obtain ⟨h1, h2⟩ := affine_unique hS hae
    exact ⟨h1.symm, h2.symm⟩
  · have hk := kE_of_not (κ := κ) (S := S) (γ := γ) hc
    have hpool : (gameAt m S γ κ).IsPooling (eqForm κ m S γ) :=
      ⟨bE κ m S γ, Eventually.of_forall fun x => by rw [haff]; simp [hk]⟩
    obtain ⟨-, hkco, hform⟩ := coef_pool hpool
    have hae : (fun x => kE κ S γ * Zg m S γ x + bE κ m S γ) =ᵐ[multivariateGaussian m (S + 1)]
        fun x => kco m S γ (eqForm κ m S γ) * Zg m S γ x + bco m S γ (eqForm κ m S γ) := by
      filter_upwards [hform] with x hx
      rw [← hx, haff]
    obtain ⟨h1, h2⟩ := affine_unique hS hae
    exact ⟨h1.symm, h2.symm⟩

/-- **The explicit rule is a signaling equilibrium of the period game.** -/
theorem eqForm_signaling (hS : S.PosSemidef) (hκ : 0 < κ) :
    ∃ φ : Kernel ℝ ℝ, (gameAt m S γ κ).IsSignalingEq (eqForm κ m S γ) φ := by
  set Γ := gameAt m S γ κ with hΓ
  have hG : Γ.Std := gameAt_std hS hκ
  have hZ : Measurable Γ.Z := gameAt_measurable_Z
  have hsens : Γ.sens = sens S γ := gameAt_sens hS
  have hκ' : Γ.κ = κ := rfl
  have hmean : Γ.meanZ = γ * m 0 + m 1 := EZ_eq hS γ
  by_cases hc : revCrit κ S γ
  · have h : Γ.κ * Γ.sens ^ 2 ≤ κck := by rw [hsens, hκ']; exact hc
    have h4 := LG.le_kck_iff_four.1 h
    have hE := hG.rev_isLinearEq hZ (LG.lplus_pos Γ.κ Γ.sens) (LG.lplus_root h4)
    have hform : (fun ω => Γ.meanZ + LG.lplus Γ.κ Γ.sens * (Γ.Z ω - Γ.meanZ)) =
        eqForm κ m S γ := by
      funext x
      have hzx : Γ.Z x = Zg m S γ x := rfl
      rw [hzx, hmean, hsens, hκ', eqForm, eqFormR]
      simp only [hc, ↓reduceIte]
      rw [Zg_sub]
      ring
    rw [hform] at hE
    refine ⟨_, hE, fun a' φ' hE' => ?_⟩
    have hloss := hG.exLoss_affine hE.1 (l := LG.lplus Γ.κ Γ.sens)
      (ae_of_all _ fun x => (congrFun hform x).symm)
    rw [hloss]
    have hb := hG.lower_bound hE'
    unfold LG.minCoef at hb
    simp only [h, ↓reduceIte, ← LG.one_sub_lplus] at hb
    exact hb
  · have h : ¬ Γ.κ * Γ.sens ^ 2 ≤ κck := by rw [hsens, hκ']; exact hc
    have hE := hG.pool_isLinearEq Γ.meanZ
    have hform : (fun _ : E2 => Γ.meanZ) = eqForm κ m S γ := by
      funext x
      rw [hmean, eqForm, eqFormR]
      simp only [hc, ↓reduceIte]
    rw [hform] at hE
    refine ⟨_, hE, fun a' φ' hE' => ?_⟩
    have hloss := hG.exLoss_pool Γ.meanZ hE.1 (ae_of_all _ fun x => (congrFun hform x).symm)
    rw [hloss]
    have hb := hG.lower_bound hE'
    unfold LG.minCoef at hb
    simp only [h, ↓reduceIte, one_mul] at hb
    simpa using hb

/-- **Every signaling equilibrium of the period game plays the explicit rule**, for almost every
private information. -/
theorem signaling_ae_eqForm (hS : S.PosSemidef) (hκ : 0 < κ) {a : E2 → ℝ} {φ : Kernel ℝ ℝ}
    (hE : (gameAt m S γ κ).IsSignalingEq a φ) :
    a =ᵐ[(gameAt m S γ κ).P] eqForm κ m S γ := by
  set Γ := gameAt m S γ κ with hΓ
  have hG : Γ.Std := gameAt_std hS hκ
  have hsens : Γ.sens = sens S γ := gameAt_sens hS
  have hκ' : Γ.κ = κ := rfl
  have hmean : Γ.meanZ = γ * m 0 + m 1 := EZ_eq hS γ
  obtain ⟨h1, h2, -⟩ := LG.signalingEq_char Γ hG hE
  by_cases hc : revCrit κ S γ
  · have h : Γ.κ * Γ.sens ^ 2 ≤ κck := by rw [hsens, hκ']; exact hc
    filter_upwards [h1 h] with x hx
    rw [hx]
    have hzx : Γ.Z x = Zg m S γ x := rfl
    rw [hzx, hmean, hsens, hκ', eqForm, eqFormR]
    simp only [hc, ↓reduceIte]
    rw [Zg_sub]
    unfold LG.lplus
    ring
  · have h : κck < Γ.κ * Γ.sens ^ 2 := not_le.1 (by rw [hsens, hκ']; exact hc)
    filter_upwards [h2 h] with x hx
    rw [hx, hmean, eqForm, eqFormR]
    simp only [hc, ↓reduceIte]

end Period

/-- **`eqAct` is the explicit rule at the current public beliefs.** -/
lemma eqAct_eq_form (κ : ℝ) (S₁ : M2) (G : Measure ℝ) (t : ℕ) (ω : Ωg) :
    eqAct κ S₁ G t ω = eqFormR κ (postTheta κ S₁ G t ω) (postMu κ S₁ G t ω) (Sig κ S₁ ω t)
      (gam ω t) (priv t ω) := by
  unfold eqAct eqFormR obs
  by_cases h : rev κ S₁ t ω
  · have h' : revCrit κ (Sig κ S₁ ω t) (gam ω t) := h
    simp only [h, h', ↓reduceIte]
    rfl
  · have h' : ¬ revCrit κ (Sig κ S₁ ω t) (gam ω t) := h
    simp only [h, h', ↓reduceIte]

/-! ### Signaling profiles -/

/-- At the history `h` of date `t`: if public beliefs are `N(m, S)`, the period strategy is a
signaling equilibrium of the period game at `h`. -/
def SignalingAt (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G] (σ : Profile) (t : ℕ)
    (h : Hist t) : Prop :=
  ∀ (m : E2) (S : M2), S.PosSemidef → post S₁ G σ t h = multivariateGaussian m S →
    ∃ φ : Kernel ℝ ℝ, (gameAt m S (h.1 (Fin.last t)) κ).IsSignalingEq (σ t h) φ

/-- A **signaling equilibrium of the dynamic game**: at almost every on-path history, the period
strategy is a signaling equilibrium of the period game given the public beliefs. -/
def IsSignalingProfile (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]
    (σ : Profile) : Prop :=
  ∀ t, ∀ᵐ ω ∂(lawG S₁ G), SignalingAt κ S₁ G σ t (hist σ t ω)

variable {κ : ℝ} {S₁ : M2} {G : Measure ℝ} [IsProbabilityMeasure G] {σ : Profile}

lemma linearAt_of_signalingAt {t : ℕ} {h : Hist t} (hs : SignalingAt κ S₁ G σ t h) :
    LinearAt κ S₁ G σ t h := fun m S hS hp => by
  obtain ⟨φ, hE⟩ := hs m S hS hp
  exact ⟨φ, hE.1, fun _ => hE⟩

lemma IsSignalingProfile.linear (hE : IsSignalingProfile κ S₁ G σ) : IsLinearProfile κ S₁ G σ :=
  fun t => (hE t).mono fun _ h => linearAt_of_signalingAt h

/-! ### Conditional expectations given almost surely equal vectors -/

lemma condExp_comap_congr {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    (h : X =ᵐ[P] Y) {f : Ω → ℝ} (hf : Integrable f P) :
    P[f | MeasurableSpace.comap X inferInstance] =ᵐ[P] P[f | MeasurableSpace.comap Y inferInstance] := by
  have hXm : MeasurableSpace.comap X inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hX.comap_le
  have hYm : MeasurableSpace.comap Y inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hY.comap_le
  have hs : ∀ B : Set E, MeasurableSet B → X ⁻¹' B =ᵐ[P] Y ⁻¹' B := fun B _ => by
    filter_upwards [h] with ω hω
    exact propext (by simp [Set.mem_preimage, hω])
  have hsm : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (P[f | MeasurableSpace.comap X inferInstance]) := stronglyMeasurable_condExp
  obtain ⟨g, hg, hgX⟩ := hsm.exists_eq_measurable_comp
  refine ae_eq_condExp_of_forall_setIntegral_eq hYm hf
    (fun s _ _ => integrable_condExp.integrableOn) ?_ ?_
  · rintro s ⟨B, hB, rfl⟩ -
    rw [← setIntegral_congr_set (hs B hB), setIntegral_condExp hXm hf ⟨B, hB, rfl⟩,
      setIntegral_congr_set (hs B hB)]
  · have hc : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] (g ∘ Y) :=
      hg.comp_measurable (Measurable.of_comap_le le_rfl)
    refine hc.aestronglyMeasurable.congr ?_
    filter_upwards [h] with ω hω
    rw [hgX]
    simp only [Function.comp, hω]

/-! ### Every signaling profile plays `eqAct` -/

/-- The history of the actions `eqAct`. -/
noncomputable def histE (κ : ℝ) (S₁ : M2) (G : Measure ℝ) (t : ℕ) (ω : Ωg) : Hist t :=
  ((fun i : Fin (t + 1) => gam ω i), fun i : Fin t => eqAct κ S₁ G i ω)

omit [IsProbabilityMeasure G] in
lemma measurable_eqAct (t : ℕ) : Measurable (eqAct κ S₁ G t) :=
  (meas_info_eqAct κ S₁ G t).mono (infoSigma_le κ S₁ (t + 1)) le_rfl

omit [IsProbabilityMeasure G] in
lemma measurable_histE (t : ℕ) : Measurable (histE κ S₁ G t) :=
  (measurable_gams t).prodMk (measurable_pi_iff.2 fun i => measurable_eqAct i)

lemma acts_apply (σ : Profile) : ∀ (t : ℕ) (ω : Ωg) (i : Fin t), acts σ t ω i = act σ i ω
  | 0, _, i => i.elim0
  | t + 1, ω, i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [acts, Fin.snoc_last]; rfl
    · simp only [acts, Fin.snoc_castSucc]
      exact acts_apply σ t ω j

omit [IsProbabilityMeasure G] in
lemma hist_eq_histE {t : ℕ} {ω : Ωg} (h : ∀ i : Fin t, act σ i ω = eqAct κ S₁ G i ω) :
    hist σ t ω = histE κ S₁ G t ω := by
  refine Prod.ext rfl ?_
  funext i
  exact (acts_apply σ t ω i).trans (h i)

variable (hκ : 0 < κ) (hS₁ : S₁.PosSemidef) (hσ : ∀ t, Measurable (Function.uncurry (σ t)))

include hS₁ in
/-- The mean of the posterior given the history. -/
lemma mean_par {t : ℕ} (hinv : Inv hσ S₁ G t) (i : Fin 2) :
    (lawG S₁ G)[fun ω => ω.1 i | MeasurableSpace.comap (hist σ t) inferInstance] =ᵐ[lawG S₁ G]
      fun ω => (par σ S₁ t (hist σ t ω)).1 i := by
  have h1 := condExp_ae_eq_integral_condDistrib (μ := lawG S₁ G) (X := hist σ t)
    (Y := fun ω : Ωg => ω.1) (measurable_hist hσ t) measurable_fst.aemeasurable
    (f := fun y : E2 => y i) (br_meas_coord measurable_id i).stronglyMeasurable
    (integrable_coord_lawG S₁ G i)
  filter_upwards [h1, post_ae_of_inv hσ hinv] with ω a b
  refine a.trans ?_
  have e : condDistrib (fun ω : Ωg => ω.1) (hist σ t) (lawG S₁ G) (hist σ t ω) =
      post S₁ G σ t (hist σ t ω) := rfl
  rw [e, b, integral_coord_mvG (par_psd (σ := σ) hS₁ t (hist σ t ω)) i]

include hκ hS₁ hσ in
/-- The induction behind `signalingProfile_act`. -/
theorem sig_invariant (hE : IsSignalingProfile κ S₁ G σ) : ∀ t,
    (∀ᵐ ω ∂(lawG S₁ G), ∀ i : Fin t, act σ i ω = eqAct κ S₁ G i ω) ∧
      ∀ᵐ ω ∂(lawG S₁ G), (par σ S₁ t (hist σ t ω)).2 = Sig κ S₁ ω t
  | 0 => ⟨ae_of_all _ fun _ i => i.elim0, ae_of_all _ fun _ => rfl⟩
  | t + 1 => by
    obtain ⟨hA, hB⟩ := sig_invariant hE t
    have hinv := inv_all hκ hS₁ hσ hE.linear t
    have hhist : hist σ t =ᵐ[lawG S₁ G] histE κ S₁ G t := hA.mono fun ω h => hist_eq_histE h
    have hmean : ∀ i : Fin 2, ∀ᵐ ω ∂(lawG S₁ G), (par σ S₁ t (hist σ t ω)).1 i =
        (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ t] ω := by
      intro i
      have h1 := mean_par hS₁ hσ hinv i
      have h2 := condExp_comap_congr (measurable_hist hσ t) (measurable_histE (κ := κ) (S₁ := S₁)
        (G := G) t) hhist (integrable_coord_lawG S₁ G i)
      have h3 : MeasurableSpace.comap (histE κ S₁ G t) inferInstance = infoSigma κ S₁ t :=
        histSigma_eq_info κ S₁ G t
      rw [h3] at h2
      filter_upwards [h1, h2] with ω a b
      rw [← a, b]
    have key : ∀ᵐ ω ∂(lawG S₁ G), act σ t ω = eqAct κ S₁ G t ω ∧
        (par σ S₁ (t + 1) (hist σ (t + 1) ω)).2 = Sig κ S₁ ω (t + 1) := by
      filter_upwards [hB, post_ae_of_inv hσ hinv, hE t, act_ae hκ hS₁ hσ (hE.linear t) hinv,
        hmean 0, hmean 1] with ω hb hpost hsig hact h0 h1
      set h := hist σ t ω with hh
      set m := (par σ S₁ t h).1 with hm
      set S := (par σ S₁ t h).2 with hSdef
      have hγ : lastγ h = gam ω t := rfl
      have hpsd : S.PosSemidef := par_psd (σ := σ) hS₁ t h
      obtain ⟨φ, hEq⟩ := hsig m S hpsd hpost
      have hform := signaling_ae_eqForm hpsd hκ hEq
      obtain ⟨hk1, hb1⟩ := kco_congr (m := m) (S := S) (γ := gam ω t) hform
      obtain ⟨hk2, hb2⟩ := kco_bco_eqForm (κ := κ) (m := m) (S := S) (γ := gam ω t) hpsd
      have hkt : kt σ S₁ t h = kE κ S (gam ω t) := hk1.trans hk2
      have hbt : bt σ S₁ t h = bE κ m S (gam ω t) := hb1.trans hb2
      have hactE : act σ t ω = eqForm κ m S (gam ω t) (priv t ω) := by
        rw [hact, hkt, hbt, hγ, eqForm_eq_affine]
      have hSig : S = Sig κ S₁ ω t := hb
      have hsucc : par σ S₁ (t + 1) (hist σ (t + 1) ω) =
          nextPar m S (gam ω t) (kE κ S (gam ω t)) (bE κ m S (gam ω t)) (act σ t ω) := by
        rw [hist_succ, par_extH, ← hkt, ← hbt]
        rfl
      refine ⟨?_, ?_⟩
      · have h0' : m 0 = postTheta κ S₁ G t ω := h0
        have h1' : m 1 = postMu κ S₁ G t ω := h1
        rw [hactE, eqAct_eq_form, ← h0', ← h1', ← hSig]
        rfl
      · rw [hsucc]
        by_cases hc : revCrit κ S (gam ω t)
        · rw [nextPar_pos (kE_pos_iff hc)]
          have hc' : revCrit κ (Sig κ S₁ ω t) (gam ω t) := hSig ▸ hc
          change kalman S (gam ω t) = SigmaC (fun _ => κ) S₁ (gam ω) (t + 1)
          rw [SigmaC_succ_rev (fun _ => κ) (gam ω) S₁ hc']
          exact congrArg (fun A => kalman A (gam ω t)) hSig
        · rw [nextPar_of_not_pos (by rw [kE_of_not hc]; exact lt_irrefl 0)]
          have hc' : ¬ revCrit κ (Sig κ S₁ ω t) (gam ω t) := hSig ▸ hc
          change S = SigmaC (fun _ => κ) S₁ (gam ω) (t + 1)
          rw [SigmaC_succ_pool (fun _ => κ) (gam ω) S₁ hc']
          exact hSig
    refine ⟨?_, key.mono fun ω h => h.2⟩
    filter_upwards [hA, key] with ω a b i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact b.1
    · exact a j

include hκ hS₁ hσ in
/-- **In every signaling profile, almost surely each action is `eqAct`.** -/
theorem signalingProfile_act (hE : IsSignalingProfile κ S₁ G σ) (t : ℕ) :
    act σ t =ᵐ[lawG S₁ G] eqAct κ S₁ G t := by
  filter_upwards [(sig_invariant hκ hS₁ hσ hE (t + 1)).1] with ω h
  exact h (Fin.last t)

include hκ hS₁ hσ in
/-- **In every signaling profile the posterior means given the realised history are those used in
`Bridge/`.** -/
theorem signalingProfile_post_ae (hE : IsSignalingProfile κ S₁ G σ) (i : Fin 2) (t : ℕ) :
    (lawG S₁ G)[fun ω => ω.1 i | MeasurableSpace.comap (hist σ t) inferInstance] =ᵐ[lawG S₁ G]
      (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ t] := by
  have hhist : hist σ t =ᵐ[lawG S₁ G] histE κ S₁ G t :=
    (sig_invariant hκ hS₁ hσ hE t).1.mono fun ω h => hist_eq_histE h
  have h2 := condExp_comap_congr (measurable_hist hσ t) (measurable_histE (κ := κ) (S₁ := S₁)
    (G := G) t) hhist (integrable_coord_lawG S₁ G i)
  have h3 : MeasurableSpace.comap (histE κ S₁ G t) inferInstance = infoSigma κ S₁ t :=
    histSigma_eq_info κ S₁ G t
  rwa [h3] at h2

/-! ### Gaussian laws determine their parameters -/

lemma mvG_inj {m m' : E2} {S S' : M2} (hS : S.PosSemidef) (hS' : S'.PosSemidef)
    (h : multivariateGaussian m S = multivariateGaussian m' S') : m = m' ∧ S = S' := by
  refine ⟨?_, ?_⟩
  · have h1 := integral_id_multivariateGaussian (μ := m) (S := S)
    rw [h, integral_id_multivariateGaussian] at h1
    exact h1.symm
  · ext i j
    rw [← covariance_eval_multivariateGaussian (μ := m) hS i j, h,
      covariance_eval_multivariateGaussian hS' i j]

/-! ### Existence of a signaling profile -/

section Exists

variable (κ S₁)

/-- The posterior parameters along histories when every period plays `eqForm`. -/
noncomputable def parE : (t : ℕ) → Hist t → E2 × M2
  | 0 => fun _ => (0, S₁)
  | t + 1 => fun h' =>
      nextPar (parE t (restr h')).1 (parE t (restr h')).2 (lastγ (restr h'))
        (kE κ (parE t (restr h')).2 (lastγ (restr h')))
        (bE κ (parE t (restr h')).1 (parE t (restr h')).2 (lastγ (restr h')))
        (h'.2 (Fin.last t))

/-- The profile that plays `eqForm` at the public beliefs of every history. -/
noncomputable def sigE : Profile :=
  fun t h => eqForm κ (parE κ S₁ t h).1 (parE κ S₁ t h).2 (lastγ h)

variable {κ S₁}

section Meas

variable {β : Type*} [MeasurableSpace β] {m : β → E2} {S : β → M2} {γ : β → ℝ}

lemma measurable_kE (κ : ℝ) (hS : Measurable S) (hγ : Measurable γ) :
    Measurable (fun x => kE κ (S x) (γ x)) := by
  have hl : Measurable (fun x => LG.lplus κ (sens (S x) (γ x))) := by
    have hs := br_meas_sens hS hγ
    unfold LG.lplus
    fun_prop
  unfold kE
  exact br_ite (br_meas_revCrit κ hS hγ) hl measurable_const

lemma measurable_bE (κ : ℝ) (hm : Measurable m) (hS : Measurable S) (hγ : Measurable γ) :
    Measurable (fun x => bE κ (m x) (S x) (γ x)) := by
  have hl : Measurable (fun x => LG.lplus κ (sens (S x) (γ x))) := by
    have hs := br_meas_sens hS hγ
    unfold LG.lplus
    fun_prop
  have hc : Measurable (fun x => γ x * m x 0 + m x 1) :=
    (hγ.mul (br_meas_coord hm 0)).add (br_meas_coord hm 1)
  unfold bE
  exact br_ite (br_meas_revCrit κ hS hγ) ((measurable_const.sub hl).mul hc) hc

end Meas

theorem measurable_parE : ∀ t, Measurable (parE κ S₁ t)
  | 0 => measurable_const
  | t + 1 => by
    have ih := measurable_parE t
    have hr := measurable_restr t
    have hp := ih.comp hr
    have hγ := (measurable_lastγ t).comp hr
    have h1 : Measurable (fun h' : Hist (t + 1) => (parE κ S₁ t (restr h')).1) :=
      measurable_fst.comp hp
    have h2 : Measurable (fun h' : Hist (t + 1) => (parE κ S₁ t (restr h')).2) :=
      measurable_snd.comp hp
    exact measurable_nextPar h1 h2 hγ (measurable_kE κ h2 hγ) (measurable_bE κ h1 h2 hγ)
      ((measurable_pi_apply _).comp measurable_snd)

theorem parE_psd (hS₁ : S₁.PosSemidef) : ∀ t (h : Hist t), (parE κ S₁ t h).2.PosSemidef
  | 0, _ => hS₁
  | t + 1, h' => nextPar_psd (parE_psd hS₁ t (restr h')) _ _ _ _

theorem measurable_sigE (t : ℕ) : Measurable (Function.uncurry (sigE κ S₁ t)) := by
  have hp := measurable_parE (κ := κ) (S₁ := S₁) t
  have h1 : Measurable (fun q : Hist t × E2 => (parE κ S₁ t q.1).1) :=
    measurable_fst.comp (hp.comp measurable_fst)
  have h2 : Measurable (fun q : Hist t × E2 => (parE κ S₁ t q.1).2) :=
    measurable_snd.comp (hp.comp measurable_fst)
  have hγ : Measurable (fun q : Hist t × E2 => lastγ q.1) :=
    (measurable_lastγ t).comp measurable_fst
  have e : Function.uncurry (sigE κ S₁ t) = fun q : Hist t × E2 =>
      kE κ (parE κ S₁ t q.1).2 (lastγ q.1) *
        Zg (parE κ S₁ t q.1).1 (parE κ S₁ t q.1).2 (lastγ q.1) q.2 +
      bE κ (parE κ S₁ t q.1).1 (parE κ S₁ t q.1).2 (lastγ q.1) := by
    funext q
    show eqForm κ (parE κ S₁ t q.1).1 (parE κ S₁ t q.1).2 (lastγ q.1) q.2 = _
    rw [eqForm_eq_affine]
  rw [e]
  exact ((measurable_kE κ h2 hγ).mul (measurable_Zg h1 h2 hγ measurable_snd)).add
    (measurable_bE κ h1 h2 hγ)

/-- Under `sigE`, the posterior parameters are `parE` at every history. -/
theorem par_sigE (hS₁ : S₁.PosSemidef) : ∀ t (h : Hist t), par (sigE κ S₁) S₁ t h = parE κ S₁ t h
  | 0, _ => rfl
  | t + 1, h' => by
    have ih := par_sigE hS₁ t (restr h')
    obtain ⟨hk, hb⟩ := kco_bco_eqForm (κ := κ) (m := (parE κ S₁ t (restr h')).1)
      (γ := lastγ (restr h')) (parE_psd hS₁ t (restr h'))
    show nextPar (par (sigE κ S₁) S₁ t (restr h')).1 (par (sigE κ S₁) S₁ t (restr h')).2
        (lastγ (restr h'))
        (kco (par (sigE κ S₁) S₁ t (restr h')).1 (par (sigE κ S₁) S₁ t (restr h')).2
          (lastγ (restr h')) (sigE κ S₁ t (restr h')))
        (bco (par (sigE κ S₁) S₁ t (restr h')).1 (par (sigE κ S₁) S₁ t (restr h')).2
          (lastγ (restr h')) (sigE κ S₁ t (restr h')))
        (h'.2 (Fin.last t)) = _
    rw [ih]
    show nextPar _ _ _ (kco _ _ _ (eqForm κ (parE κ S₁ t (restr h')).1 (parE κ S₁ t (restr h')).2
        (lastγ (restr h')))) (bco _ _ _ (eqForm κ (parE κ S₁ t (restr h')).1
          (parE κ S₁ t (restr h')).2 (lastγ (restr h')))) _ = _
    rw [hk, hb]
    rfl

include hκ hS₁ in
/-- **A signaling equilibrium of the dynamic game exists.** -/
theorem exists_signalingProfile :
    ∃ σ : Profile, (∀ t, Measurable (Function.uncurry (σ t))) ∧ IsSignalingProfile κ S₁ G σ := by
  have hm : ∀ t, Measurable (Function.uncurry (sigE κ S₁ t)) := measurable_sigE
  have hsig : ∀ t, Inv hm S₁ G t →
      ∀ᵐ ω ∂(lawG S₁ G), SignalingAt κ S₁ G (sigE κ S₁) t (hist (sigE κ S₁) t ω) := by
    intro t hinv
    filter_upwards [post_ae_of_inv hm hinv] with ω hpost m S hS hN
    set h := hist (sigE κ S₁) t ω
    rw [par_sigE hS₁ t h] at hpost
    obtain ⟨rfl, rfl⟩ := mvG_inj hS (parE_psd hS₁ t h) (hN.symm.trans hpost)
    exact eqForm_signaling hS hκ
  have hinv := inv_all_of_step hκ hS₁ hm
    (fun t h => (hsig t h).mono fun _ hs => linearAt_of_signalingAt hs)
  exact ⟨_, hm, fun t => hsig t (hinv t)⟩

end Exists

/-! ### The results in every signaling profile -/

/-- The posterior mean of `x_i` given the realised history of the profile `σ`. -/
noncomputable def postProf (S₁ : M2) (G : Measure ℝ) (σ : Profile) (i : Fin 2) (t : ℕ) : Ωg → ℝ :=
  (lawG S₁ G)[fun ω => ω.1 i | MeasurableSpace.comap (hist σ t) inferInstance]

section Congr

variable {P : Measure Ωg} [IsProbabilityMeasure P] {X : Ωg → ℝ}

lemma slOccurs_congr (hX : Measurable X) {p q : ℕ → Ωg → ℝ} (h : ∀ n, p n =ᵐ[P] q n)
    (hp : SLOccurs P X p) : SLOccurs P X q := by
  unfold SLOccurs at *
  filter_upwards [hp, br_ae_condDistrib hX (ae_all_iff.2 h)] with r hr hae
  exact hr.congr_left (fun n => hae.mono fun ω hω => hω n)

lemma slFails_congr (hX : Measurable X) {p q : ℕ → Ωg → ℝ} (h : ∀ n, p n =ᵐ[P] q n)
    (hp : SLFails P X p) : SLFails P X q := by
  unfold SLFails at *
  filter_upwards [hp, br_ae_condDistrib hX (ae_all_iff.2 h)] with r hr hae hq
  exact hr (hq.congr_left (fun n => hae.mono fun ω hω => (hω n).symm))

end Congr

include hκ hS₁ hσ in
lemma postProf_ae (hE : IsSignalingProfile κ S₁ G σ) (i : Fin 2) (t : ℕ) :
    (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ t] =ᵐ[lawG S₁ G] postProf S₁ G σ i t :=
  (signalingProfile_post_ae hκ hS₁ hσ hE i t).symm

/-- **Proposition 2 in every signaling equilibrium of the dynamic game.** Suppose `Σ₁ ≻ 0` and
`γ_t` is i.i.d. with full support on `[0,1]`. If `κ < κck`, social learning about preferences and
fundamentals occurs. If `κ > κck`, almost surely there is a finite time after which the signaling
equilibrium is pooling in every period, and social learning about preferences and fundamentals
fails. Posterior means are given the realised history of the profile. -/
theorem prop2_signalingProfile (hS : S₁.PosDef) (hG : FullSupportUnit G) (hκ : 0 < κ)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (hE : IsSignalingProfile κ S₁ G σ) :
    (κ < κck → SLOccurs (lawG S₁ G) thetaV (postProf S₁ G σ 0) ∧
        SLOccurs (lawG S₁ G) muV (postProf S₁ G σ 1)) ∧
    (κck < κ → SLFails (lawG S₁ G) thetaV (postProf S₁ G σ 0) ∧
        SLFails (lawG S₁ G) muV (postProf S₁ G σ 1) ∧
        ∀ᵐ ω ∂(lawG S₁ G), ∃ T, ∀ t, T ≤ t → ∀ (m : E2) (S : M2), S.PosSemidef →
          post S₁ G σ t (hist σ t ω) = multivariateGaussian m S →
          (gameAt m S (gam ω t) κ).IsPooling (σ t (hist σ t ω))) := by
  have hpsd := hS.posSemidef
  have hθ : Measurable thetaV := br_meas_coord measurable_fst 0
  have hμ : Measurable muV := br_meas_coord measurable_fst 1
  obtain ⟨h1, h2⟩ := prop2_socialLearning S₁ hS G hG κ hκ
  have e0 := postProf_ae hκ hpsd hσ hE 0
  have e1 := postProf_ae hκ hpsd hσ hE 1
  refine ⟨fun hk => ⟨slOccurs_congr hθ e0 (h1 hk).1, slOccurs_congr hμ e1 (h1 hk).2⟩,
    fun hk => ⟨slFails_congr hθ e0 (h2 hk).1, slFails_congr hμ e1 (h2 hk).2, ?_⟩⟩
  have hfin := ae_lawG_of_ae_gam S₁ G ((CC.prop2_beliefs S₁ hS G hG).2 κ hk)
  have hinv := inv_all hκ hpsd hσ hE.linear
  filter_upwards [hfin, ae_all_iff.2 hE, ae_all_iff.2 fun t => (sig_invariant hκ hpsd hσ hE t).2,
    ae_all_iff.2 fun t => post_ae_of_inv hσ (hinv t)] with ω ⟨T, _, _, hT⟩ hsig hSig hpost
  refine ⟨T, fun t ht m S hS' hN => ?_⟩
  have hP := par_psd (σ := σ) hpsd t (hist σ t ω)
  obtain ⟨rfl, rfl⟩ := mvG_inj hS' hP (hN.symm.trans (hpost t))
  obtain ⟨φ, hEq⟩ := hsig t _ _ hS' hN
  have hc : ¬ revCrit κ (par σ S₁ t (hist σ t ω)).2 (gam ω t) := by
    rw [hSig t]
    exact (hT t ht).1
  have hform := signaling_ae_eqForm hS' hκ hEq
  refine ⟨gam ω t * (par σ S₁ t (hist σ t ω)).1 0 + (par σ S₁ t (hist σ t ω)).1 1,
    hform.mono fun x hx => ?_⟩
  rw [hx]
  have hc' : ¬ revCrit κ (par σ S₁ t (hist σ t ω)).2 ((hist σ t ω).1 (Fin.last t)) := hc
  unfold eqForm eqFormR
  simp only [hc', ↓reduceIte]
  rfl

/-- **Corollary A2 (social learning) in every signaling equilibrium of the dynamic game.** -/
theorem corollaryA2_signalingProfile {σμ2 : ℝ} (hσμ : 0 < σμ2) (hκ : 0 < κ)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t)))
    (hE : IsSignalingProfile κ !![0, 0; 0, σμ2] G σ) :
    (κ ≤ κck → SLOccurs (lawG !![0, 0; 0, σμ2] G) muV (postProf !![0, 0; 0, σμ2] G σ 1)) ∧
    (κck < κ → SLFails (lawG !![0, 0; 0, σμ2] G) muV (postProf !![0, 0; 0, σμ2] G σ 1)) := by
  have hμ : Measurable muV := br_meas_coord measurable_fst 1
  have e1 := postProf_ae hκ (psd_diag 0 σμ2 le_rfl hσμ.le) hσ hE 1
  obtain ⟨h1, h2⟩ := corollaryA2_socialLearning σμ2 hσμ G κ hκ
  exact ⟨fun hk => slOccurs_congr hμ e1 (h1 hk), fun hk => slFails_congr hμ e1 (h2 hk)⟩

/-- **Corollary A3 (social learning) in every signaling equilibrium of the dynamic game.** -/
theorem corollaryA3_signalingProfile {σθ2 : ℝ} (hσθ : 0 < σθ2) (hκ : 0 < κ)
    {σ : Profile} (hσ : ∀ t, Measurable (Function.uncurry (σ t)))
    (hE : IsSignalingProfile κ !![σθ2, 0; 0, 0] (Measure.dirac 1) σ) :
    (κ ≤ κck → SLOccurs (lawG !![σθ2, 0; 0, 0] (Measure.dirac 1)) thetaV
      (postProf !![σθ2, 0; 0, 0] (Measure.dirac 1) σ 0)) ∧
    (κck < κ → SLFails (lawG !![σθ2, 0; 0, 0] (Measure.dirac 1)) thetaV
      (postProf !![σθ2, 0; 0, 0] (Measure.dirac 1) σ 0)) := by
  have hθ : Measurable thetaV := br_meas_coord measurable_fst 0
  have e0 := postProf_ae hκ (psd_diag σθ2 0 hσθ.le le_rfl) hσ hE 0
  obtain ⟨h1, h2⟩ := corollaryA3_socialLearning σθ2 hσθ κ hκ
  exact ⟨fun hk => slOccurs_congr hθ e0 (h1 hk), fun hk => slFails_congr hθ e0 (h2 hk)⟩

/-! ### Asymptotic payoffs in every signaling profile -/

/-- Expected adaptation payoff at date `t` in the profile `σ`. -/
noncomputable def expAdaptProf (S₁ : M2) (G : Measure ℝ) (σ : Profile) (t : ℕ) : ℝ :=
  ∫ ω, -(act σ t ω - gam ω t * thetaV ω - vType t ω) ^ 2 ∂(lawG S₁ G)

/-- Expected utility at date `t` in the profile `σ`: the expected adaptation payoff minus `κ` times
the expected conformity term, with the public's posterior about `v_t` given `(h^t, a_t)`. -/
noncomputable def expUtilityProf (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]
    (σ : Profile) (t : ℕ) : ℝ :=
  expAdaptProf S₁ G σ t - κ * ∫ ω, (∫ b, (b - postProf S₁ G σ 1 t ω) ^ 2 ∂(condDistrib (vType t)
    (fun ω => (hist σ t ω, act σ t ω)) (lawG S₁ G) (hist σ t ω, act σ t ω))) ∂(lawG S₁ G)

include hκ hS₁ hσ in
theorem expAdaptProf_eq (hE : IsSignalingProfile κ S₁ G σ) (t : ℕ) :
    expAdaptProf S₁ G σ t = expAdapt κ S₁ G t := by
  refine integral_congr_ae ?_
  filter_upwards [signalingProfile_act hκ hS₁ hσ hE t] with ω h
  simp only [h]

include hκ hS₁ hσ in
theorem expUtilityProf_eq (hE : IsSignalingProfile κ S₁ G σ) (t : ℕ) :
    expUtilityProf κ S₁ G σ t = expUtility κ S₁ G t := by
  have hA := expAdaptProf_eq hκ hS₁ hσ hE t
  have hhist : hist σ t =ᵐ[lawG S₁ G] histVecB κ S₁ G t :=
    (sig_invariant hκ hS₁ hσ hE t).1.mono fun ω h => hist_eq_histE h
  have hact := signalingProfile_act hκ hS₁ hσ hE t
  have hpost := postProf_ae hκ hS₁ hσ hE 1 t
  let W : Ωg → Hist t × ℝ := fun ω => (hist σ t ω, act σ t ω)
  let W' : Ωg → Hist t × ℝ := fun ω => (histVecB κ S₁ G t ω, eqAct κ S₁ G t ω)
  have hWe : W =ᵐ[lawG S₁ G] W' := by
    filter_upwards [hhist, hact] with ω h1 h2
    simp only [W, W', h1, h2]
  have hW : Measurable W := (measurable_hist hσ t).prodMk (measurable_act hσ t)
  have hW' : Measurable W' :=
    (measurable_histE (κ := κ) (S₁ := S₁) (G := G) t).prodMk (measurable_eqAct t)
  have hY : Measurable (vType t) := br_meas_coord (measurable_priv t) 1
  have hmap : (lawG S₁ G).map W = (lawG S₁ G).map W' := Measure.map_congr hWe
  have hjoint : (lawG S₁ G).map (fun ω => (W' ω, vType t ω)) =
      ((lawG S₁ G).map W') ⊗ₘ condDistrib (vType t) W (lawG S₁ G) := by
    have h1 : (lawG S₁ G).map (fun ω => (W' ω, vType t ω)) =
        (lawG S₁ G).map (fun ω => (W ω, vType t ω)) :=
      Measure.map_congr (hWe.mono fun ω h => by simp only [h])
    rw [h1, ← hmap]
    exact (compProd_map_condDistrib (μ := lawG S₁ G) (Y := vType t) hW.aemeasurable
      hY.aemeasurable).symm
  have hcd := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := lawG S₁ G) hW' hY hjoint
  have hcd' := ae_of_ae_map hW'.aemeasurable hcd
  unfold expUtilityProf expUtility
  rw [hA]
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hWe, hcd', hpost] with ω h1 h2 h3
  have e1 : condDistrib (vType t) (fun ω => (hist σ t ω, act σ t ω)) (lawG S₁ G)
      (hist σ t ω, act σ t ω) = condDistrib (vType t) W' (lawG S₁ G) (W' ω) := by
    have : (hist σ t ω, act σ t ω) = W' ω := h1
    show condDistrib (vType t) W (lawG S₁ G) (W ω) = _
    rw [show W ω = W' ω from h1, h2]
  show (∫ b, (b - postProf S₁ G σ 1 t ω) ^ 2 ∂(condDistrib (vType t)
      (fun ω => (hist σ t ω, act σ t ω)) (lawG S₁ G) (hist σ t ω, act σ t ω))) = _
  rw [e1, ← h3]
  rfl

/-- **Corollary A2, asymptotic payoffs, in every signaling equilibrium of the dynamic game.** -/
theorem corollaryA2_asymptotic_profile {σμ2 : ℝ} (hσμ : 0 < σμ2) (hκ : 0 < κ)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t)))
    (hE : IsSignalingProfile κ !![0, 0; 0, σμ2] G σ) :
    Tendsto (fun t => expAdaptProf !![0, 0; 0, σμ2] G σ t) atTop
        (𝓝 (if κ ≤ κck then -((1 - √(1 - 4 * κ)) / 2) ^ 2 else -(1 + σμ2))) ∧
      Tendsto (fun t => expUtilityProf κ !![0, 0; 0, σμ2] G σ t) atTop
        (𝓝 (if κ ≤ κck then -((1 - √(1 - 4 * κ)) / 2) else -((1 + κ) * (1 + σμ2)))) := by
  have hpsd := psd_diag 0 σμ2 le_rfl hσμ.le
  obtain ⟨h1, h2⟩ := corollaryA2_asymptotic σμ2 hσμ G κ hκ
  exact ⟨h1.congr fun t => (expAdaptProf_eq hκ hpsd hσ hE t).symm,
    h2.congr fun t => (expUtilityProf_eq hκ hpsd hσ hE t).symm⟩

/-- **Corollary A3, asymptotic payoffs, in every signaling equilibrium of the dynamic game.** -/
theorem corollaryA3_asymptotic_profile {σθ2 : ℝ} (hσθ : 0 < σθ2) :
    ∃ AAL AU : ℝ → ℝ, AntitoneOn AAL (Set.Ioi 0) ∧ StrictAntiOn AU (Set.Ioi 0) ∧
      ∀ κ : ℝ, 0 < κ → ∀ σ : Profile, (∀ t, Measurable (Function.uncurry (σ t))) →
        IsSignalingProfile κ !![σθ2, 0; 0, 0] (Measure.dirac 1) σ →
        Tendsto (fun t => expAdaptProf !![σθ2, 0; 0, 0] (Measure.dirac 1) σ t) atTop (𝓝 (AAL κ)) ∧
        Tendsto (fun t => expUtilityProf κ !![σθ2, 0; 0, 0] (Measure.dirac 1) σ t) atTop
          (𝓝 (AU κ)) := by
  obtain ⟨AAL, AU, hA, hU, h⟩ := corollaryA3_asymptotic σθ2 hσθ
  refine ⟨AAL, AU, hA, hU, fun κ hκ σ hσ hE => ?_⟩
  have hpsd := psd_diag σθ2 0 hσθ.le le_rfl
  obtain ⟨h1, h2⟩ := h κ hκ
  exact ⟨h1.congr fun t => (expAdaptProf_eq hκ hpsd hσ hE t).symm,
    h2.congr fun t => (expUtilityProf_eq hκ hpsd hσ hE t).symm⟩

/-- **Proposition A2 in every signaling equilibrium of the dynamic game.** `(par σ S₁ t h).2` is the
posterior covariance at the history `h` (`post_ae_of_inv`). -/
theorem propA2_signalingProfile (hκ : κck < κ) (hS : S₁.PosDef) (hG0 : G (Set.Iio 0) = 0)
    (hunb : ∀ M : ℝ, 0 < G (Set.Ioi M)) (γbar : ℝ) (hγbar : 0 < γbar)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (hE : IsSignalingProfile κ S₁ G σ) :
    ∀ᵐ ω ∂(lawG S₁ G), ∀ c < 1, ∀ᶠ t : ℕ in atTop,
      c ≤ (G (Set.Ioi γbar)).toReal * t *
        min ((par σ S₁ t (hist σ t ω)).2 0 0) ((par σ S₁ t (hist σ t ω)).2 1 1) := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  have h := ae_lawG_of_ae_gam S₁ G (CC.propA2 κ hκ S₁ hS G hG0 hunb γbar hγbar)
  filter_upwards [h, ae_all_iff.2 fun t => (sig_invariant hκ0 hS.posSemidef hσ hE t).2]
    with ω h1 h2 c hc
  filter_upwards [h1 c hc] with t ht
  rw [h2 t]
  exact ht

end CC.LinearPaths
