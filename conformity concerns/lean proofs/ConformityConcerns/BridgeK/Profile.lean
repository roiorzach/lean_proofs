import ConformityConcerns.BridgeK.Signaling
import ConformityConcerns.BridgeK.PropA1
import ConformityConcerns.BridgeK.Prop3Prior

/-!
# Signaling equilibria of the dynamic game with heterogeneous `κ_t` and public disclosures

`IsSignalingProfileK` says that a measurable strategy profile is, at almost every on-path history
with public beliefs `N(m, S)`, a signaling equilibrium of the period game at that history. The public
history is `h^t = (w_0, …, w_t; d_0, …, d_t; a_0, …, a_{t-1})`, where `w_s = (κ_s, γ_s)` and `d_s` is
the value disclosed at date `s`.

* `exists_signalingProfileK`: such a profile exists.
* `signalingProfileK_act`: in every such profile, almost surely each action is `eqActK`.
* `signalingProfileK_post_ae`: the posterior means given the realised history are those of
  `BridgeK/`.
* `propA1_signalingProfile`, `prop3_1_signalingProfile`: Propositions A1 and 3 (1) hold in every
  such profile.

The proof is by induction on `t`. If the actions before `t` are almost surely `eqActK`, the history
is almost surely the equilibrium history, so the public posterior is the Gaussian law of
`beliefsK_gaussian`; hence the period strategy is the period signaling equilibrium, whose action
at the realised private information is `eqActK`.
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open CC.LinearPaths (eqFormR eqForm eqForm_signaling signaling_ae_eqForm eqForm_eq_affine mvG_inj
  measurable_kE measurable_bE condExp_comap_congr gaussK gaussK_apply)
open scoped ENNReal

set_option warn.classDefReducibility false

/-- A public history at date `t`: the weights, the disclosures, and the actions. -/
abbrev HistK (t : ℕ) := (Fin (t + 1) → ℝ × ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ)

/-- A pure strategy profile: `σ t h x` is player `t`'s action at public history `h` with private
information `x = (s_t, v_t)`. -/
abbrev ProfileK := ∀ t : ℕ, HistK t → E2 → ℝ

variable (S₁ : M2) (G Gγ : Measure ℝ) (D : Sched) (σ : ProfileK)

/-- The realised actions. -/
noncomputable def actsK : (t : ℕ) → Ωk → (Fin t → ℝ)
  | 0 => fun _ => Fin.elim0
  | t + 1 => fun ω => Fin.snoc (actsK t ω)
      (σ t ((fun i : Fin (t + 1) => wts ω i), (fun i : Fin (t + 1) => discVal D i ω), actsK t ω)
        (priv t ω))

/-- The realised public history. -/
noncomputable def histK (t : ℕ) (ω : Ωk) : HistK t :=
  ((fun i : Fin (t + 1) => wts ω i), (fun i : Fin (t + 1) => discVal D i ω), actsK D σ t ω)

/-- The realised action. -/
noncomputable def actK (t : ℕ) (ω : Ωk) : ℝ := σ t (histK D σ t ω) (priv t ω)

/-- The weights `(κ_t, γ_t)` recorded in a history of date `t`. -/
def lastW {t : ℕ} (h : HistK t) : ℝ × ℝ := h.1 (Fin.last t)

/-- The public posterior of `(θ, μ)` given the history. -/
noncomputable def postK [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ] (t : ℕ) :
    Kernel (HistK t) E2 :=
  condDistrib (fun ω : Ωk => ω.1) (histK D σ t) (lawK S₁ G Gγ)

/-- If public beliefs at `h` are `N(m, S)`, the period strategy is a signaling equilibrium of the
period game at `h`. -/
def SignalingAtK [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ] (t : ℕ) (h : HistK t) : Prop :=
  ∀ (m : E2) (S : M2), S.PosSemidef → postK S₁ G Gγ D σ t h = multivariateGaussian m S →
    ∃ φ : Kernel ℝ ℝ, (gameAt m S (lastW h).2 (lastW h).1).IsSignalingEq (σ t h) φ

/-- A **signaling equilibrium of the dynamic game**, with heterogeneous `κ_t` and disclosures. -/
def IsSignalingProfileK [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ] : Prop :=
  ∀ t, ∀ᵐ ω ∂(lawK S₁ G Gγ), SignalingAtK S₁ G Gγ D σ t (histK D σ t ω)

/-- The history of the actions `eqActK`. -/
noncomputable def histEK (t : ℕ) (ω : Ωk) : HistK t :=
  ((fun i : Fin (t + 1) => wts ω i), (fun i : Fin (t + 1) => discVal D i ω),
    fun i : Fin t => eqActK S₁ G Gγ D i ω)

variable {S₁ G Gγ D σ}

lemma actsK_apply : ∀ (t : ℕ) (ω : Ωk) (i : Fin t), actsK D σ t ω i = actK D σ i ω
  | 0, _, i => i.elim0
  | t + 1, ω, i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [actsK, Fin.snoc_last]; rfl
    · simp only [actsK, Fin.snoc_castSucc]
      exact actsK_apply t ω j

lemma histK_eq {t : ℕ} {ω : Ωk} (h : ∀ i : Fin t, actK D σ i ω = eqActK S₁ G Gγ D i ω) :
    histK D σ t ω = histEK S₁ G Gγ D t ω := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext i
  exact (actsK_apply t ω i).trans (h i)

lemma measurable_privK (t : ℕ) : Measurable (priv t) :=
  measurable_fst.add ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd))

lemma measurable_wgams (t : ℕ) : Measurable (fun ω : Ωk => fun i : Fin (t + 1) => wts ω i) :=
  measurable_pi_iff.2 fun i => measurable_wts_apply i

lemma measurable_discs (t : ℕ) : Measurable (fun ω : Ωk => fun i : Fin (t + 1) => discVal D i ω) :=
  measurable_pi_iff.2 fun i => measurable_discVal D i

lemma measurable_actsK (hσ : ∀ t, Measurable (Function.uncurry (σ t))) :
    ∀ t, Measurable (actsK D σ t)
  | 0 => measurable_const
  | t + 1 => by
    have ih := measurable_actsK hσ t
    have ha : Measurable (fun ω => σ t ((fun i : Fin (t + 1) => wts ω i),
        (fun i : Fin (t + 1) => discVal D i ω), actsK D σ t ω) (priv t ω)) :=
      (hσ t).comp (((measurable_wgams t).prodMk ((measurable_discs t).prodMk ih)).prodMk
        (measurable_privK t))
    refine measurable_pi_iff.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have e : (fun ω => actsK D σ (t + 1) ω (Fin.last t)) = fun ω =>
          σ t ((fun i : Fin (t + 1) => wts ω i), (fun i : Fin (t + 1) => discVal D i ω),
            actsK D σ t ω) (priv t ω) := by
        funext ω; simp only [actsK, Fin.snoc_last]
      rw [e]; exact ha
    · have e : (fun ω => actsK D σ (t + 1) ω j.castSucc) = fun ω => actsK D σ t ω j := by
        funext ω; simp only [actsK, Fin.snoc_castSucc]
      rw [e]; exact (measurable_pi_apply j).comp ih

lemma measurable_histK (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (t : ℕ) :
    Measurable (histK D σ t) :=
  (measurable_wgams t).prodMk ((measurable_discs t).prodMk (measurable_actsK hσ t))

lemma measurable_actK (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (t : ℕ) :
    Measurable (actK D σ t) :=
  (hσ t).comp ((measurable_histK hσ t).prodMk (measurable_privK t))

lemma measurable_eqActK (t : ℕ) : Measurable (eqActK S₁ G Gγ D t) :=
  (meas_info_eqActK S₁ G Gγ D t).mono (infoSigmaK_le S₁ D (t + 1)) le_rfl

lemma measurable_histEK (t : ℕ) : Measurable (histEK S₁ G Gγ D t) :=
  (measurable_wgams t).prodMk ((measurable_discs t).prodMk
    (measurable_pi_iff.2 fun i => measurable_eqActK i))

/-! ### The public beliefs along the equilibrium history -/

/-- The point `(a, b)` of `ℝ²`. -/
noncomputable def mkE (a b : ℝ) : E2 := WithLp.toLp 2 ![a, b]

@[simp] lemma mkE_zero (a b : ℝ) : mkE a b 0 = a := by simp [mkE]
@[simp] lemma mkE_one (a b : ℝ) : mkE a b 1 = b := by simp [mkE]

lemma measurable_mkE {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun a => mkE (f a) (g a)) := by
  have h : Measurable (fun a => (![f a, g a] : Fin 2 → ℝ)) := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · simpa using hf
    · simpa using hg
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp h

lemma mkE_coords (m : E2) : mkE (m 0) (m 1) = m := by
  ext i; fin_cases i <;> simp

section Beliefs

variable (S₁ G Gγ D) (t : ℕ)

lemma exists_postFun (i : Fin 2) : ∃ g : HistK t → ℝ, Measurable g ∧
    (lawK S₁ G Gγ)[fun ω => ω.1 i | histSigmaK S₁ G Gγ D t] = g ∘ histEK S₁ G Gγ D t := by
  have hsm : StronglyMeasurable[MeasurableSpace.comap (histEK S₁ G Gγ D t) inferInstance]
      ((lawK S₁ G Gγ)[fun ω => ω.1 i | histSigmaK S₁ G Gγ D t]) := stronglyMeasurable_condExp
  obtain ⟨g, hg, hc⟩ := hsm.exists_eq_measurable_comp
  exact ⟨g, hg.measurable, hc⟩

/-- A measurable version of the posterior mean of `x_i` as a function of the history. -/
noncomputable def gPost (i : Fin 2) : HistK t → ℝ := (exists_postFun S₁ G Gγ D t i).choose

lemma measurable_gPost (i : Fin 2) : Measurable (gPost S₁ G Gγ D t i) :=
  (exists_postFun S₁ G Gγ D t i).choose_spec.1

lemma gPost_spec (i : Fin 2) (ω : Ωk) :
    (lawK S₁ G Gγ)[fun ω => ω.1 i | histSigmaK S₁ G Gγ D t] ω =
      gPost S₁ G Gγ D t i (histEK S₁ G Gγ D t ω) :=
  congrFun (exists_postFun S₁ G Gγ D t i).choose_spec.2 ω

/-- The public beliefs as a function of the history. -/
noncomputable def parK (h : HistK t) : E2 × M2 :=
  (mkE (gPost S₁ G Gγ D t 0 h) (gPost S₁ G Gγ D t 1 h), SigK S₁ D (extW (t + 1) h.1) t)

lemma measurable_parK : Measurable (parK S₁ G Gγ D t) :=
  (measurable_mkE (measurable_gPost S₁ G Gγ D t 0) (measurable_gPost S₁ G Gγ D t 1)).prodMk
    ((measurable_SigK S₁ D t).comp ((measurable_extW _).comp measurable_fst))

variable (hS : S₁.PosSemidef) (hD : SchedOK D)

include hS hD in
lemma parK_psd (h : HistK t) : (parK S₁ G Gγ D t h).2.PosSemidef :=
  SigK_psd S₁ D hD hS _ t

/-- On the equilibrium path, the parameters are the Gaussian posterior's. -/
lemma parK_histE (ω : Ωk) :
    (parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).2 = SigK S₁ D (wts ω) t :=
  SigK_congr S₁ D (fun _ hs => extW_apply_lt _ (Nat.lt_succ_of_lt hs))

variable [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ]

include hS hD in
lemma parK_mean_ae :
    ∀ᵐ ω ∂(lawK S₁ G Gγ), (parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).1 =
      mtF S₁ D t (infoMap S₁ D t ω) := by
  have hbel := beliefs_coreK S₁ D t G Gγ hS hD
  have hV : Measurable (infoMap S₁ D t) := measurable_infoMap S₁ D t
  have hmean : ∀ i : Fin 2, (lawK S₁ G Gγ)[fun ω => ω.1 i | infoSigmaK S₁ D t] =ᵐ[lawK S₁ G Gγ]
      fun ω => mtF S₁ D t (infoMap S₁ D t ω) i := by
    intro i
    have h1 := condExp_ae_eq_integral_condDistrib (μ := lawK S₁ G Gγ) (X := infoMap S₁ D t)
      (Y := fun ω : Ωk => ω.1) hV measurable_fst.aemeasurable (f := fun y : E2 => y i)
      (Bridge.br_meas_coord measurable_id i).stronglyMeasurable (integrable_coord_lawK S₁ G Gγ i)
    filter_upwards [h1, hbel] with ω a b
    refine a.trans ?_
    rw [b, Bridge.integral_coord_mvG (SigK_psd S₁ D hD hS (wts ω) t) i]
  have hK : histSigmaK S₁ G Gγ D t = infoSigmaK S₁ D t := histSigmaK_eq_info S₁ G Gγ D t
  filter_upwards [hmean 0, hmean 1] with ω h0 h1
  have g0 := gPost_spec S₁ G Gγ D t 0 ω
  have g1 := gPost_spec S₁ G Gγ D t 1 ω
  rw [hK, h0] at g0
  rw [hK, h1] at g1
  show mkE _ _ = _
  rw [← g0, ← g1, mkE_coords]

include hS hD in
/-- The joint law of the equilibrium history and `(θ, μ)`. -/
theorem joint_histE :
    (lawK S₁ G Gγ).map (fun ω => (histEK S₁ G Gγ D t ω, ω.1)) =
      ((lawK S₁ G Gγ).map (histEK S₁ G Gγ D t)) ⊗ₘ
        gaussK (parK S₁ G Gγ D t) (measurable_parK S₁ G Gγ D t) := by
  set P := lawK S₁ G Gγ with hP
  have hH : Measurable (histEK S₁ G Gγ D t) := measurable_histEK t
  have hI : Measurable (infoMap S₁ D t) := measurable_infoMap S₁ D t
  have hj := joint_eq_compProdK S₁ D t G Gγ hS hD
  have hK : MeasurableSpace.comap (histEK S₁ G Gγ D t) inferInstance =
      MeasurableSpace.comap (infoMap S₁ D t) inferInstance :=
    (histSigmaK_eq_info S₁ G Gγ D t).trans (infoSigmaK_eq_comap S₁ D t)
  refine Measure.ext_prod fun {B C} hB hC => ?_
  obtain ⟨B', hB', hBB'⟩ : ∃ B', MeasurableSet B' ∧ infoMap S₁ D t ⁻¹' B' = histEK S₁ G Gγ D t ⁻¹' B := by
    have : MeasurableSet[MeasurableSpace.comap (infoMap S₁ D t) inferInstance]
        (histEK S₁ G Gγ D t ⁻¹' B) := hK ▸ ⟨B, hB, rfl⟩
    exact this
  have hset : (fun ω : Ωk => (histEK S₁ G Gγ D t ω, ω.1)) ⁻¹' (B ×ˢ C) =
      (fun ω : Ωk => (infoMap S₁ D t ω, ω.1)) ⁻¹' (B' ×ˢ C) := by
    ext ω
    have : ω ∈ infoMap S₁ D t ⁻¹' B' ↔ ω ∈ histEK S₁ G Gγ D t ⁻¹' B := by rw [hBB']
    simp only [Set.mem_preimage, Set.mem_prod] at this ⊢
    tauto
  rw [Measure.map_apply (hH.prodMk measurable_fst) (hB.prod hC), hset,
    ← Measure.map_apply (hI.prodMk measurable_fst) (hB'.prod hC), hj,
    Measure.compProd_apply_prod hB' hC, Measure.compProd_apply_prod hB hC,
    Measure.restrict_map hI hB', Measure.restrict_map hH hB,
    lintegral_map (Kernel.measurable_coe _ hC) hI,
    lintegral_map (Kernel.measurable_coe _ hC) hH, hBB']
  refine lintegral_congr_ae ?_
  have hmean := parK_mean_ae S₁ G Gγ D t hS hD
  refine (ae_restrict_of_ae hmean).mono fun ω hω => ?_
  show postKK S₁ D t (infoMap S₁ D t ω) C = gaussK (parK S₁ G Gγ D t) (measurable_parK S₁ G Gγ D t)
    (histEK S₁ G Gγ D t ω) C
  rw [gaussK_apply, hω, parK_histE, postKK_apply, SgF_infoMap]

/-- The noise of period `t`'s private information is independent of the equilibrium history and
`(θ, μ)`. -/
lemma indep_noise_info :
    IndepFun (fun ω => (histEK S₁ G Gγ D t ω, ω.1)) (fun ω : Ωk => noise (2 * t + 1) ω)
      (lawK S₁ G Gγ) := by
  set P := lawK S₁ G Gγ with hP
  set k := 2 * t + 1 with hk
  have hx : Measurable (fun ω : Ωk => ω.1) := measurable_fst
  have hn : Measurable (fun ω : Ωk => ω.2.1) := measurable_fst.comp measurable_snd
  have hw : Measurable (fun ω : Ωk => ω.2.2) := measurable_snd.comp measurable_snd
  have h1 : IndepFun (fun ω : Ωk => ω.1) (fun ω : Ωk => (ω.2.1, ω.2.2)) P :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have h2 : IndepFun (fun ω : Ωk => ω.2.1) (fun ω : Ωk => ω.2.2) P := by
    refine Bridge.br_indep_of_map (P := P) (h := Prod.snd) measurable_snd measurable_fst
      measurable_snd ?_
    rw [hP]
    unfold lawK
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have h3 := Bridge.br_indep_assoc' hx hn hw h1 h2
  have hxn : IndepFun (fun ω : Ωk => ω.1) (fun ω : Ωk => ω.2.1) P :=
    h1.comp (φ := id) (ψ := Prod.fst) measurable_id measurable_fst
  have h4 := Bridge.br_indep_regroup hx hn hw h3 hxn
  have hT := Bridge.measurable_truncE k
  have hE : Measurable (fun ε : ℕ → E2 => ε k) := measurable_pi_apply k
  have h5 : IndepFun (fun ω : Ωk => (ω.1, ω.2.2))
      (fun ω : Ωk => (Bridge.truncE k ω.2.1, ω.2.1 k)) P :=
    h4.comp (φ := id) (ψ := fun ε => (Bridge.truncE k ε, ε k)) measurable_id (hT.prodMk hE)
  have h6 : IndepFun (fun ω : Ωk => Bridge.truncE k ω.2.1) (fun ω : Ωk => ω.2.1 k) P := by
    refine Bridge.br_indep_of_map (P := P) (h := fun ω : Ωk => ω.2.1) hn hT hE ?_
    have hmap : P.map (fun ω : Ωk => ω.2.1) = Measure.infinitePi fun _ : ℕ => stdGaussian E2 := by
      have e : (fun ω : Ωk => ω.2.1) = Prod.fst ∘ Prod.snd := rfl
      rw [e, ← Measure.map_map measurable_fst measurable_snd, hP]
      unfold lawK
      rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_fst_prod, measure_univ, one_smul]
    rw [hmap]
    exact Bridge.indep_noise k
  have h7 := Bridge.br_indep_assoc' (hx.prodMk hw) (hT.comp hn) ((measurable_pi_apply k).comp hn)
    h5 h6
  let τ : Ωk → (E2 × (ℕ → ℝ × ℝ)) × (ℕ → E2) := fun ω => ((ω.1, ω.2.2), Bridge.truncE k ω.2.1)
  have hτ : Measurable[MeasurableSpace.comap τ inferInstance] τ := comap_measurable τ
  have hinfo : MeasurableSpace.comap (infoMap S₁ D t) inferInstance ≤
      MeasurableSpace.comap τ inferInstance := by
    have e : infoMap S₁ D t = (fun q : (E2 × (ℕ → ℝ × ℝ)) × (ℕ → E2) =>
        infoMap S₁ D t ((q.1.1, (q.2, q.1.2)) : Ωk)) ∘ τ := by
      funext ω
      simp only [Function.comp, τ]
      rw [infoMap_fiber S₁ D t ω.2.2 (ω.1, Bridge.truncE k ω.2.1)]
      have h8 := infoMap_fiber S₁ D t ω.2.2 (ω.1, ω.2.1)
      rw [YS_truncE]
      exact h8
    rw [e, ← MeasurableSpace.comap_comp]
    refine MeasurableSpace.comap_mono (Measurable.comap_le ?_)
    exact (measurable_infoMap S₁ D t).comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hH : Measurable[MeasurableSpace.comap τ inferInstance] (histEK S₁ G Gγ D t) := by
    have h0 : MeasurableSpace.comap (histEK S₁ G Gγ D t) inferInstance ≤
        MeasurableSpace.comap τ inferInstance :=
      ((histSigmaK_eq_info S₁ G Gγ D t).trans (infoSigmaK_eq_comap S₁ D t)).le.trans hinfo
    exact Measurable.of_comap_le h0
  have hX : Measurable[MeasurableSpace.comap τ inferInstance] (fun ω : Ωk => ω.1) :=
    (measurable_fst.comp measurable_fst).comp hτ
  rw [IndepFun_iff_Indep] at h7 ⊢
  exact indep_of_indep_of_le_left h7 (hH.prodMk hX).comap_le

include hS hD in
/-- If almost every period-game law gives probability zero to the bad set, the realised outcome
avoids it almost surely. -/
lemma ae_of_period {T : Set (HistK t × E2)} (hT : MeasurableSet T)
    (h : ∀ᵐ ω ∂(lawK S₁ G Gγ), multivariateGaussian (parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).1
      ((parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).2 + 1)
        (Prod.mk (histEK S₁ G Gγ D t ω) ⁻¹' T) = 0) :
    ∀ᵐ ω ∂(lawK S₁ G Gγ), (histEK S₁ G Gγ D t ω, priv t ω) ∉ T := by
  set P := lawK S₁ G Gγ with hP
  set p := parK S₁ G Gγ D t with hpdef
  have hp : Measurable p := measurable_parK S₁ G Gγ D t
  have hH : Measurable (histEK S₁ G Gγ D t) := measurable_histEK t
  have hA : Measurable (fun ω : Ωk => (histEK S₁ G Gγ D t ω, ω.1)) := hH.prodMk measurable_fst
  have hξ : Measurable (fun ω : Ωk => noise (2 * t + 1) ω) :=
    (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  have hlawξ : P.map (fun ω : Ωk => noise (2 * t + 1) ω) = stdGaussian E2 := by
    have e : (fun ω : Ωk => noise (2 * t + 1) ω) =
        (fun ε : ℕ → E2 => ε (2 * t + 1)) ∘ Prod.fst ∘ Prod.snd := rfl
    rw [e, ← Measure.map_map (measurable_pi_apply _) (measurable_fst.comp measurable_snd),
      ← Measure.map_map measurable_fst measurable_snd, hP]
    unfold lawK
    rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_fst_prod, measure_univ, one_smul,
      Measure.infinitePi_map_eval]
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hξ.aemeasurable).1
    (indep_noise_info S₁ G Gγ D t)
  rw [hlawξ, joint_histE S₁ G Gγ D t hS hD] at hprod
  set B : Set ((HistK t × E2) × E2) := {q | (q.1.1, q.1.2 + q.2) ∈ T} with hB
  have hBm : MeasurableSet B :=
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).add measurable_snd)) hT
  rw [ae_iff]
  simp only [not_not]
  have hset : {ω | (histEK S₁ G Gγ D t ω, priv t ω) ∈ T} =
      (fun ω : Ωk => ((histEK S₁ G Gγ D t ω, ω.1), noise (2 * t + 1) ω)) ⁻¹' B := rfl
  rw [hset, ← Measure.map_apply (hA.prodMk hξ) hBm, hprod, Measure.prod_apply hBm,
    Measure.lintegral_compProd (measurable_measure_prodMk_left hBm)]
  have hGm : MeasurableSet {h : HistK t | LinearPaths.typeK p hp h (Prod.mk h ⁻¹' T) = 0} :=
    Kernel.measurable_kernel_prodMk_left hT (measurableSet_singleton 0)
  have hgood : ∀ᵐ h ∂(P.map (histEK S₁ G Gγ D t)), LinearPaths.typeK p hp h (Prod.mk h ⁻¹' T) = 0 :=
    (ae_map_iff hH.aemeasurable hGm).2 h
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hgood] with h' hh'
  have hP' : (p h').2.PosSemidef := parK_psd S₁ G Gγ D t hS hD h'
  have hBs : MeasurableSet ((fun w : E2 × E2 => (h', w.1 + w.2)) ⁻¹' T) :=
    (measurable_const.prodMk (measurable_fst.add measurable_snd)) hT
  have e : ∫⁻ x, stdGaussian E2 (Prod.mk (h', x) ⁻¹' B) ∂(gaussK p hp h') =
      periodLaw (p h').1 (p h').2 (privInfo ⁻¹' (Prod.mk h' ⁻¹' T)) := by
    rw [gaussK_apply]
    unfold periodLaw
    rw [Measure.prod_apply (measurable_privInfo (measurable_prodMk_left hT))]
    rfl
  simp only []
  rw [e, ← Measure.map_apply measurable_privInfo (measurable_prodMk_left hT), privInfo_law hP']
  exact hh'

variable {t}

lemma post_ae_of_hist {D : Sched} (hS : S₁.PosSemidef) (hD : SchedOK D) {σ : ProfileK}
    (hσ : ∀ t, Measurable (Function.uncurry (σ t)))
    (hh : histK D σ t =ᵐ[lawK S₁ G Gγ] histEK S₁ G Gγ D t) :
    ∀ᵐ ω ∂(lawK S₁ G Gγ), postK S₁ G Gγ D σ t (histK D σ t ω) =
      multivariateGaussian (parK S₁ G Gγ D t (histK D σ t ω)).1
        (parK S₁ G Gγ D t (histK D σ t ω)).2 := by
  have hX := measurable_histK (D := D) hσ t
  have hjoint : (lawK S₁ G Gγ).map (fun ω => (histK D σ t ω, ω.1)) =
      ((lawK S₁ G Gγ).map (histK D σ t)) ⊗ₘ
        gaussK (parK S₁ G Gγ D t) (measurable_parK S₁ G Gγ D t) := by
    have e1 : (lawK S₁ G Gγ).map (fun ω => (histK D σ t ω, ω.1)) =
        (lawK S₁ G Gγ).map (fun ω => (histEK S₁ G Gγ D t ω, ω.1)) :=
      Measure.map_congr (hh.mono fun ω h => by simp only [h])
    rw [e1, Measure.map_congr hh]
    exact joint_histE S₁ G Gγ D t hS hD
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := lawK S₁ G Gγ) hX
    measurable_fst hjoint
  filter_upwards [ae_of_ae_map hX.aemeasurable h] with ω hω
  exact hω

omit [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ] in
/-- `eqActK` is the explicit rule at the parameters of the history. -/
lemma eqActK_eq_parK (ω : Ωk) :
    eqActK S₁ G Gγ D t ω = eqForm (kap ω t) (parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).1
      (parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).2 (gam ω t) (priv t ω) := by
  rw [eqActK_eq_form, parK_histE]
  have g0 := gPost_spec S₁ G Gγ D t 0 ω
  have g1 := gPost_spec S₁ G Gγ D t 1 ω
  have hK : histSigmaK S₁ G Gγ D t = infoSigmaK S₁ D t := histSigmaK_eq_info S₁ G Gγ D t
  rw [hK] at g0 g1
  have e0 : postThetaI S₁ G Gγ D t ω = gPost S₁ G Gγ D t 0 (histEK S₁ G Gγ D t ω) := g0
  have e1 : postMuI S₁ G Gγ D t ω = gPost S₁ G Gγ D t 1 (histEK S₁ G Gγ D t ω) := g1
  rw [e0, e1]
  simp only [eqForm, parK, mkE_zero, mkE_one]

end Beliefs

/-! ### Every signaling profile plays `eqActK`, and one exists -/

section Meas

variable {β : Type*} [MeasurableSpace β] {κ γ : β → ℝ} {m : β → E2} {S : β → M2}

lemma measurableSet_revCrit' (hκ : Measurable κ) (hS : Measurable S) (hγ : Measurable γ) :
    MeasurableSet {x | revCrit (κ x) (S x) (γ x)} := by
  unfold revCrit
  exact measurableSet_le (hκ.mul ((Bridge.br_meas_sens hS hγ).pow_const 2)) measurable_const

lemma measurable_lplus' (hκ : Measurable κ) (hS : Measurable S) (hγ : Measurable γ) :
    Measurable (fun x => LG.lplus (κ x) (sens (S x) (γ x))) := by
  have hs := Bridge.br_meas_sens hS hγ
  unfold LG.lplus
  fun_prop

lemma measurable_kE' (hκ : Measurable κ) (hS : Measurable S) (hγ : Measurable γ) :
    Measurable (fun x => LinearPaths.kE (κ x) (S x) (γ x)) := by
  unfold LinearPaths.kE
  exact Bridge.br_ite (measurableSet_revCrit' hκ hS hγ) (measurable_lplus' hκ hS hγ) measurable_const

lemma measurable_bE' (hκ : Measurable κ) (hm : Measurable m) (hS : Measurable S)
    (hγ : Measurable γ) : Measurable (fun x => LinearPaths.bE (κ x) (m x) (S x) (γ x)) := by
  have hc : Measurable (fun x => γ x * m x 0 + m x 1) :=
    (hγ.mul (Bridge.br_meas_coord hm 0)).add (Bridge.br_meas_coord hm 1)
  unfold LinearPaths.bE
  exact Bridge.br_ite (measurableSet_revCrit' hκ hS hγ)
    ((measurable_const.sub (measurable_lplus' hκ hS hγ)).mul hc) hc

lemma measurable_eqForm' {z : β → E2} (hκ : Measurable κ) (hm : Measurable m) (hS : Measurable S)
    (hγ : Measurable γ) (hz : Measurable z) :
    Measurable (fun x => eqForm (κ x) (m x) (S x) (γ x) (z x)) := by
  have e : (fun x => eqForm (κ x) (m x) (S x) (γ x) (z x)) = fun x =>
      LinearPaths.kE (κ x) (S x) (γ x) * LinearPaths.Zg (m x) (S x) (γ x) (z x) +
        LinearPaths.bE (κ x) (m x) (S x) (γ x) := by
    funext x
    rw [eqForm_eq_affine]
  rw [e]
  exact ((measurable_kE' hκ hS hγ).mul (LinearPaths.measurable_Zg hm hS hγ hz)).add
    (measurable_bE' hκ hm hS hγ)

end Meas

section Main

variable [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ]

lemma measurable_lastW1 (t : ℕ) : Measurable (fun h : HistK t => (lastW h).1) :=
  measurable_fst.comp ((measurable_pi_apply _).comp measurable_fst)

lemma measurable_lastW2 (t : ℕ) : Measurable (fun h : HistK t => (lastW h).2) :=
  measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)

/-- The set where the period strategy differs from the explicit rule. -/
lemma measurableSet_bad (S₁ G Gγ D) [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ]
    {σ : ProfileK} (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (t : ℕ) :
    MeasurableSet {q : HistK t × E2 | σ t q.1 q.2 ≠ eqForm (lastW q.1).1
      (parK S₁ G Gγ D t q.1).1 (parK S₁ G Gγ D t q.1).2 (lastW q.1).2 q.2} := by
  have hp := measurable_parK S₁ G Gγ D t
  have h := measurable_eqForm' (β := HistK t × E2) (z := fun q => q.2)
    (κ := fun q => (lastW q.1).1) (m := fun q => (parK S₁ G Gγ D t q.1).1)
    (S := fun q => (parK S₁ G Gγ D t q.1).2) (γ := fun q => (lastW q.1).2)
    ((measurable_lastW1 t).comp measurable_fst)
    (measurable_fst.comp (hp.comp measurable_fst))
    (measurable_snd.comp (hp.comp measurable_fst))
    ((measurable_lastW2 t).comp measurable_fst) measurable_snd
  exact (measurableSet_eq_fun (hσ t) h).compl

variable (hS : S₁.PosSemidef) (hD : SchedOK D) (hpos : G (Set.Iic 0) = 0)

include hS hD hpos in
/-- The induction behind `signalingProfileK_act`. -/
theorem sigK_invariant (hσ : ∀ t, Measurable (Function.uncurry (σ t)))
    (hE : IsSignalingProfileK S₁ G Gγ D σ) :
    ∀ t, ∀ᵐ ω ∂(lawK S₁ G Gγ), ∀ i : Fin t, actK D σ i ω = eqActK S₁ G Gγ D i ω
  | 0 => ae_of_all _ fun _ i => i.elim0
  | t + 1 => by
    have hA := sigK_invariant hσ hE t
    have hh : histK D σ t =ᵐ[lawK S₁ G Gγ] histEK S₁ G Gγ D t := hA.mono fun ω h => histK_eq h
    have hT := measurableSet_bad S₁ G Gγ D hσ t
    have hperiod : ∀ᵐ ω ∂(lawK S₁ G Gγ),
        multivariateGaussian (parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).1
          ((parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).2 + 1)
          (Prod.mk (histEK S₁ G Gγ D t ω) ⁻¹' {q : HistK t × E2 | σ t q.1 q.2 ≠ eqForm (lastW q.1).1
            (parK S₁ G Gγ D t q.1).1 (parK S₁ G Gγ D t q.1).2 (lastW q.1).2 q.2}) = 0 := by
      filter_upwards [hh, post_ae_of_hist S₁ G Gγ hS hD hσ hh, hE t, ae_kap_pos S₁ G Gγ hpos t]
        with ω h1 h2 h3 hk
      have hp := parK_psd S₁ G Gγ D t hS hD (histK D σ t ω)
      obtain ⟨φ, hEq⟩ := h3 _ _ hp h2
      have hk' : 0 < (lastW (histK D σ t ω)).1 := hk
      have hform := signaling_ae_eqForm hp hk' hEq
      rw [← h1]
      exact ae_iff.1 hform
    have hout := ae_of_period S₁ G Gγ D t hS hD hT hperiod
    have key : ∀ᵐ ω ∂(lawK S₁ G Gγ), actK D σ t ω = eqActK S₁ G Gγ D t ω := by
      filter_upwards [hh, hout] with ω h1 h2
      have h3 : σ t (histEK S₁ G Gγ D t ω) (priv t ω) = eqForm (kap ω t)
          (parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).1 (parK S₁ G Gγ D t (histEK S₁ G Gγ D t ω)).2
          (gam ω t) (priv t ω) := by
        by_contra hne
        exact h2 hne
      rw [actK, h1, h3, ← eqActK_eq_parK]
    filter_upwards [hA, key] with ω a b i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact b
    · exact a j

include hS hD hpos in
/-- **In every signaling profile, almost surely each action is `eqActK`.** -/
theorem signalingProfileK_act (hσ : ∀ t, Measurable (Function.uncurry (σ t)))
    (hE : IsSignalingProfileK S₁ G Gγ D σ) (t : ℕ) :
    actK D σ t =ᵐ[lawK S₁ G Gγ] eqActK S₁ G Gγ D t := by
  filter_upwards [sigK_invariant hS hD hpos hσ hE (t + 1)] with ω h
  exact h (Fin.last t)

/-- The posterior mean of `x_i` given the realised history of the profile. -/
noncomputable def postProfK (S₁ : M2) (G Gγ : Measure ℝ) [IsProbabilityMeasure G]
    [IsProbabilityMeasure Gγ] (D : Sched) (σ : ProfileK) (i : Fin 2) (t : ℕ) : Ωk → ℝ :=
  (lawK S₁ G Gγ)[fun ω => ω.1 i | MeasurableSpace.comap (histK D σ t) inferInstance]

include hS hD hpos in
/-- **The posterior means given the realised history are those of `BridgeK/`.** -/
theorem signalingProfileK_post_ae (hσ : ∀ t, Measurable (Function.uncurry (σ t)))
    (hE : IsSignalingProfileK S₁ G Gγ D σ) (i : Fin 2) (t : ℕ) :
    (lawK S₁ G Gγ)[fun ω => ω.1 i | histSigmaK S₁ G Gγ D t] =ᵐ[lawK S₁ G Gγ]
      postProfK S₁ G Gγ D σ i t := by
  have hh : histK D σ t =ᵐ[lawK S₁ G Gγ] histEK S₁ G Gγ D t :=
    (sigK_invariant hS hD hpos hσ hE t).mono fun ω h => histK_eq h
  exact (condExp_comap_congr (measurable_histK hσ t) (measurable_histEK t) hh
    (integrable_coord_lawK S₁ G Gγ i)).symm

/-- The profile that plays the explicit rule at the public beliefs of every history. -/
noncomputable def sigEK (S₁ : M2) (G Gγ : Measure ℝ) [IsProbabilityMeasure G]
    [IsProbabilityMeasure Gγ] (D : Sched) : ProfileK :=
  fun t h => eqForm (lastW h).1 (parK S₁ G Gγ D t h).1 (parK S₁ G Gγ D t h).2 (lastW h).2

lemma measurable_sigEK (S₁ : M2) (G Gγ : Measure ℝ) [IsProbabilityMeasure G]
    [IsProbabilityMeasure Gγ] (D : Sched) (t : ℕ) :
    Measurable (Function.uncurry (sigEK S₁ G Gγ D t)) := by
  have hp := measurable_parK S₁ G Gγ D t
  exact measurable_eqForm' (β := HistK t × E2) (z := fun q => q.2)
    ((measurable_lastW1 t).comp measurable_fst)
    (measurable_fst.comp (hp.comp measurable_fst))
    (measurable_snd.comp (hp.comp measurable_fst))
    ((measurable_lastW2 t).comp measurable_fst) measurable_snd

/-- `sigEK` plays `eqActK`. -/
theorem sigEK_invariant :
    ∀ t, ∀ᵐ ω ∂(lawK S₁ G Gγ), ∀ i : Fin t, actK D (sigEK S₁ G Gγ D) i ω = eqActK S₁ G Gγ D i ω
  | 0 => ae_of_all _ fun _ i => i.elim0
  | t + 1 => by
    have hA := sigEK_invariant t
    have key : ∀ᵐ ω ∂(lawK S₁ G Gγ), actK D (sigEK S₁ G Gγ D) t ω = eqActK S₁ G Gγ D t ω := by
      filter_upwards [hA] with ω a
      rw [actK, histK_eq a, eqActK_eq_parK]
      rfl
    filter_upwards [hA, key] with ω a b i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact b
    · exact a j

include hS hD hpos in
/-- **A signaling equilibrium of the dynamic game exists** (heterogeneous `κ_t`, disclosures). -/
theorem exists_signalingProfileK :
    ∃ σ : ProfileK, (∀ t, Measurable (Function.uncurry (σ t))) ∧
      IsSignalingProfileK S₁ G Gγ D σ := by
  refine ⟨sigEK S₁ G Gγ D, measurable_sigEK S₁ G Gγ D, fun t => ?_⟩
  have hh : histK D (sigEK S₁ G Gγ D) t =ᵐ[lawK S₁ G Gγ] histEK S₁ G Gγ D t :=
    (sigEK_invariant t).mono fun ω h => histK_eq h
  filter_upwards [post_ae_of_hist S₁ G Gγ hS hD (measurable_sigEK S₁ G Gγ D) hh,
    ae_kap_pos S₁ G Gγ hpos t] with ω h2 hk m S hPSD hN
  have hp := parK_psd S₁ G Gγ D t hS hD (histK D (sigEK S₁ G Gγ D) t ω)
  obtain ⟨rfl, rfl⟩ := mvG_inj hPSD hp (hN.symm.trans h2)
  have hk' : 0 < (lastW (histK D (sigEK S₁ G Gγ D) t ω)).1 := hk
  exact eqForm_signaling hPSD hk'

section Congr

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : Ω → ℝ}

lemma slOccursK_congr (hX : Measurable X) {p q : ℕ → Ω → ℝ} (h : ∀ n, p n =ᵐ[P] q n)
    (hp : SLOccurs P X p) : SLOccurs P X q := by
  unfold SLOccurs at *
  filter_upwards [hp, k_ae_condDistrib hX (ae_all_iff.2 h)] with r hr hae
  exact hr.congr_left (fun n => hae.mono fun ω hω => hω n)

lemma slFailsK_congr (hX : Measurable X) {p q : ℕ → Ω → ℝ} (h : ∀ n, p n =ᵐ[P] q n)
    (hp : SLFails P X p) : SLFails P X q := by
  unfold SLFails at *
  filter_upwards [hp, k_ae_condDistrib hX (ae_all_iff.2 h)] with r hr hae hq
  exact hr (hq.congr_left (fun n => hae.mono fun ω hω => (hω n).symm))

end Congr

end Main

/-- **Proposition A1 in every signaling equilibrium of the dynamic game.** -/
theorem propA1_signalingProfile (G Gγ : Measure ℝ) [IsProbabilityMeasure G]
    [IsProbabilityMeasure Gγ] (hpos : G (Set.Iic 0) = 0) (hatom : G {κck} = 0)
    (hGγ : FullSupportUnit Gγ) (S₁ : M2) (hS : S₁.PosDef) {σ : ProfileK}
    (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (hE : IsSignalingProfileK S₁ G Gγ noDisc σ) :
    (0 < G (Set.Iio κck) →
      SLOccurs (lawK S₁ G Gγ) thetaV (postProfK S₁ G Gγ noDisc σ 0) ∧
        SLOccurs (lawK S₁ G Gγ) muV (postProfK S₁ G Gγ noDisc σ 1)) ∧
    ((∃ κ₀, κck < κ₀ ∧ G (Set.Iio κ₀) = 0) →
      SLFails (lawK S₁ G Gγ) thetaV (postProfK S₁ G Gγ noDisc σ 0) ∧
        SLFails (lawK S₁ G Gγ) muV (postProfK S₁ G Gγ noDisc σ 1)) := by
  have hpsd := hS.posSemidef
  have hθ : Measurable thetaV := Bridge.br_meas_coord measurable_fst 0
  have hμ : Measurable muV := Bridge.br_meas_coord measurable_fst 1
  have e0 := signalingProfileK_post_ae hpsd schedOK_noDisc hpos hσ hE 0
  have e1 := signalingProfileK_post_ae hpsd schedOK_noDisc hpos hσ hE 1
  obtain ⟨h1, h2⟩ := propA1_socialLearning G Gγ hpos hatom hGγ S₁ hS
  exact ⟨fun h => ⟨slOccursK_congr hθ e0 (h1 h).1, slOccursK_congr hμ e1 (h1 h).2⟩,
    fun h => ⟨slFailsK_congr hθ e0 (h2 h).1, slFailsK_congr hμ e1 (h2 h).2⟩⟩

/-- **Proposition A1, the rates: in every signaling profile the covariance process is the one
of `CC.propA1`.** Almost surely, at every date the public posterior at the realised history is
`N(m, SigmaH)`, with `SigmaH` along the realised `(κ_t, γ_t)`, and the period strategy is revealing
if and only if the criterion of Corollary 1 holds. -/
theorem propA1_path_signalingProfile {G Gγ : Measure ℝ} [IsProbabilityMeasure G]
    [IsProbabilityMeasure Gγ] (hpos : G (Set.Iic 0) = 0) {S₁ : M2} (hS : S₁.PosSemidef)
    {σ : ProfileK} (hσ : ∀ t, Measurable (Function.uncurry (σ t)))
    (hE : IsSignalingProfileK S₁ G Gγ noDisc σ) :
    ∀ᵐ ω ∂(lawK S₁ G Gγ), ∀ t, ∃ m : E2,
      postK S₁ G Gγ noDisc σ t (histK noDisc σ t ω) =
        multivariateGaussian m (SigmaH S₁ (wts ω) t) ∧
      ((gameAt m (SigmaH S₁ (wts ω) t) (gam ω t) (kap ω t)).IsRevealing (σ t (histK noDisc σ t ω)) ↔
        revCrit (kap ω t) (SigmaH S₁ (wts ω) t) (gam ω t)) := by
  have hD : SchedOK noDisc := schedOK_noDisc
  have hstep : ∀ t, ∀ᵐ ω ∂(lawK S₁ G Gγ), ∃ m : E2,
      postK S₁ G Gγ noDisc σ t (histK noDisc σ t ω) =
        multivariateGaussian m (SigmaH S₁ (wts ω) t) ∧
      ((gameAt m (SigmaH S₁ (wts ω) t) (gam ω t) (kap ω t)).IsRevealing (σ t (histK noDisc σ t ω)) ↔
        revCrit (kap ω t) (SigmaH S₁ (wts ω) t) (gam ω t)) := by
    intro t
    have hh : histK noDisc σ t =ᵐ[lawK S₁ G Gγ] histEK S₁ G Gγ noDisc t :=
      (sigK_invariant hS hD hpos hσ hE t).mono fun ω h => histK_eq h
    filter_upwards [hh, post_ae_of_hist S₁ G Gγ hS hD hσ hh, hE t, ae_kap_pos S₁ G Gγ hpos t]
      with ω h1 h2 h3 hk
    have hp := parK_psd S₁ G Gγ noDisc t hS hD (histK noDisc σ t ω)
    have hcov : (parK S₁ G Gγ noDisc t (histK noDisc σ t ω)).2 = SigmaH S₁ (wts ω) t := by
      rw [h1, parK_histE, SigK_noDisc]
      rfl
    refine ⟨_, by rw [h2, hcov], ?_⟩
    obtain ⟨φ, hEq⟩ := h3 _ _ hp h2
    have hk' : 0 < (lastW (histK noDisc σ t ω)).1 := hk
    have hG := gameAt_std (m := (parK S₁ G Gγ noDisc t (histK noDisc σ t ω)).1)
      (γ := gam ω t) hp hk'
    have hcor := LG.corollary1 _ hG hEq
    rw [← hcov]
    refine hcor.trans ?_
    have hs := gameAt_sens (m := (parK S₁ G Gγ noDisc t (histK noDisc σ t ω)).1)
      (γ := gam ω t) (κ := (lastW (histK noDisc σ t ω)).1) hp
    rw [hs]
    exact gameAt_revCrit_iff hk'
  exact ae_all_iff.2 hstep

/-- **Proposition 3 (1) in every signaling equilibrium of the dynamic game, for every prior of the
model.** -/
theorem prop3_1_signalingProfile (κ : ℝ) (hκ : κck < κ) {σθ σμ ρ : ℝ} (hθ : 0 ≤ σθ) (hμ : 0 ≤ σμ)
    (hρ : |ρ| < 1) (Gγ : Measure ℝ) [IsProbabilityMeasure Gγ] (hGγ : FullSupportUnit Gγ) (τ : ℕ)
    (n : ℝ) (hn : 0 ≤ n) (σ₁ σ₂ : ProfileK)
    (hσ₁ : ∀ t, Measurable (Function.uncurry (σ₁ t)))
    (hσ₂ : ∀ t, Measurable (Function.uncurry (σ₂ t)))
    (hE₁ : IsSignalingProfileK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ (individualAt τ n) σ₁)
    (hE₂ : IsSignalingProfileK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ (peerAt τ n) σ₂) :
    (0 < σμ → SLFails (lawK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ) muV
      (postProfK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ (individualAt τ n) σ₁ 1)) ∧
    (0 < σθ → SLFails (lawK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ) thetaV
      (postProfK (priorCov σθ σμ ρ) (Measure.dirac κ) Gγ (peerAt τ n) σ₂ 0)) := by
  have hpsd := priorCov_psd (σθ := σθ) (σμ := σμ) hρ
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  have hpos : (Measure.dirac κ) (Set.Iic (0 : ℝ)) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic]
    simp [hκ0]
  have hθm : Measurable thetaV := Bridge.br_meas_coord measurable_fst 0
  have hμm : Measurable muV := Bridge.br_meas_coord measurable_fst 1
  have e1 := signalingProfileK_post_ae hpsd (schedOK_interventionAt τ 0 hn) hpos hσ₁ hE₁ 1
  have e2 := signalingProfileK_post_ae hpsd (schedOK_interventionAt τ 1 hn) hpos hσ₂ hE₂ 0
  obtain ⟨h1, h2⟩ := prop3_1_socialLearning_prior κ hκ hθ hμ hρ Gγ hGγ τ n hn
  exact ⟨fun h => slFailsK_congr hμm e1 (h1 h), fun h => slFailsK_congr hθm e2 (h2 h)⟩

end CC.BridgeK
