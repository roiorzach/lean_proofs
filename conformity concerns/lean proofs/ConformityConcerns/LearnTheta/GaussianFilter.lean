import ConformityConcerns.LearnTheta.Exists
import ConformityConcerns.LearnTheta.GaussianM
import ConformityConcerns.Bridge.Kalman
import ConformityConcerns.Corollaries.KnownMu

/-!
# The assumption of Proposition A5 holds in the Linear-Gaussian model

Take `θ ~ N(0, σ²)`, `ε_t, v_t ~ N(0, 1)`. In every measurable profile that is fully revealing up to
date `t`, the public's conditional law of `Y_t = E(θ | h^t, s_t)` given `h^t` is Gaussian
(`beliefY_gaussian`). So `m(· | h^t)` is the quadratic of `mfun_gaussian`, and the assumption that
`m(· | h^t)` is `C²` with `0 < m'' ≤ 2` holds at the histories that fully revealing play reaches
(`hm_gaussian`). Hence all the hypotheses of `propA5_exists` hold (`propA5_exists_gaussian`).

The proof is the Kalman filter: along revealing play, the error `θ - b_t(h^t)` is independent of
`h^t` and `N(0, q_t)`, with `q_t` deterministic.
-/

namespace CC.LearnTheta

open MeasureTheory ProbabilityTheory Filter Topology
open CC.Bridge (E2 kstep br_indep_regroup br_indep_assoc br_indep_of_map br_meas_coord)
open scoped NNReal

set_option warn.classDefReducibility false

/-! ### Preliminaries -/

/-- The point `(a, b)` of `ℝ²`. -/
noncomputable def mk2 (a b : ℝ) : E2 := WithLp.toLp 2 ![a, b]

@[simp] lemma mk2_zero (a b : ℝ) : mk2 a b 0 = a := by simp [mk2]
@[simp] lemma mk2_one (a b : ℝ) : mk2 a b 1 = b := by simp [mk2]

lemma measurable_mk2 {α : Type*} {mα : MeasurableSpace α} {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun a => mk2 (f a) (g a)) := by
  have h : Measurable (fun a => (![f a, g a] : Fin 2 → ℝ)) := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · simpa using hf
    · simpa using hg
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp h

/-- A measurable inverse of a strictly increasing function. -/
noncomputable def invS (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (⨆ q : ℚ, if f q ≤ y then (((q : ℝ) : EReal)) else ⊥).toReal

lemma invS_apply {f : ℝ → ℝ} (hf : StrictMono f) (x : ℝ) : invS f (f x) = x := by
  unfold invS
  have h : (⨆ q : ℚ, if f q ≤ f x then (((q : ℝ) : EReal)) else ⊥) = (x : EReal) := by
    refine le_antisymm (iSup_le fun q => ?_) (le_of_forall_lt fun r hr => ?_)
    · split_ifs with hq
      · exact EReal.coe_le_coe_iff.2 (hf.le_iff_le.1 hq)
      · exact bot_le
    · obtain ⟨y, hry, hyx⟩ := EReal.lt_iff_exists_real_btwn.1 hr
      have hyx' : y < x := EReal.coe_lt_coe_iff.1 hyx
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hyx'
      have hle : f q ≤ f x := hf.monotone hq2.le
      refine lt_of_lt_of_le (hry.trans (EReal.coe_lt_coe_iff.2 hq1)) ?_
      refine le_trans (le_of_eq ?_) (le_iSup _ q)
      simp only [hle, ↓reduceIte]
  rw [h, EReal.toReal_coe]

lemma measurable_invS {α : Type*} [MeasurableSpace α] {F : α → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) {y : α → ℝ} (hy : Measurable y) :
    Measurable (fun a => invS (F a) (y a)) := by
  unfold invS
  refine Measurable.ereal_toReal (Measurable.iSup fun q => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (hF.comp (measurable_id.prodMk measurable_const)) hy

/-- If `W` is independent of `X` and Gaussian, the conditional law of `b(X) + W` given `X` is
Gaussian. -/
lemma condDistrib_affine_gauss {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [StandardBorelSpace Ω] [Nonempty Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → β}
    {W Y : Ω → ℝ} {b : β → ℝ} {τ : ℝ≥0} (hX : Measurable X) (hW : Measurable W) (hY : Measurable Y)
    (hb : Measurable b) (hind : IndepFun X W P) (hlaw : P.map W = gaussianReal 0 τ)
    (hYe : Y =ᵐ[P] fun ω => b (X ω) + W ω) :
    ∀ᵐ ω ∂P, condDistrib Y X P (X ω) = gaussianReal (b (X ω)) τ := by
  let K : Kernel β ℝ :=
    ⟨fun x => gaussianReal (b x) τ, measurable_gaussianReal.comp (hb.prodMk measurable_const)⟩
  have : IsMarkovKernel K := ⟨fun x => by
    change IsProbabilityMeasure (gaussianReal (b x) τ)
    infer_instance⟩
  have hjoint : P.map (fun ω => (X ω, Y ω)) = (P.map X) ⊗ₘ K := by
    have e1 : P.map (fun ω => (X ω, Y ω)) = P.map (fun ω => (X ω, b (X ω) + W ω)) :=
      Measure.map_congr (hYe.mono fun ω h => by simp only [h])
    have hprod := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hW.aemeasurable).1 hind
    rw [hlaw] at hprod
    rw [e1]
    refine Measure.ext_prod fun {A C} hA hC => ?_
    have hset : MeasurableSet {p : β × ℝ | p.1 ∈ A ∧ b p.1 + p.2 ∈ C} :=
      (measurable_fst hA).inter (((hb.comp measurable_fst).add measurable_snd) hC)
    have hm : Measurable (fun ω => (X ω, b (X ω) + W ω)) := hX.prodMk ((hb.comp hX).add hW)
    rw [Measure.map_apply hm (hA.prod hC), Measure.compProd_apply_prod hA hC]
    have e2 : (fun ω => (X ω, b (X ω) + W ω)) ⁻¹' (A ×ˢ C) =
        (fun ω => (X ω, W ω)) ⁻¹' {p : β × ℝ | p.1 ∈ A ∧ b p.1 + p.2 ∈ C} := rfl
    rw [e2, ← Measure.map_apply (hX.prodMk hW) hset, hprod, Measure.prod_apply hset,
      ← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      change _ = gaussianReal (b x) τ C
      have hm := gaussianReal_map_const_add (μ := 0) (v := τ) (b x)
      rw [zero_add] at hm
      rw [← hm, Measure.map_apply (measurable_const_add (b x)) hC]
      congr 1
      ext w
      simp [hx]
    · rw [Set.indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' {p : β × ℝ | p.1 ∈ A ∧ b p.1 + p.2 ∈ C} = ∅ := by
        ext w; simp [hx]
      rw [this, measure_empty]
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := P) hX hY hjoint
  filter_upwards [ae_of_ae_map hX.aemeasurable h] with ω hω
  exact hω

/-! ### The Gaussian model -/

/-- The density of `N(0, 1)`. -/
noncomputable abbrev psiN : ℝ → ℝ := gaussianPDFReal 0 1

lemma vLaw_psiN : vLaw psiN = gaussianReal 0 1 := by
  unfold vLaw
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  rfl

instance : IsProbabilityMeasure (vLaw psiN) := by rw [vLaw_psiN]; infer_instance

lemma psiN_continuous : Continuous psiN := by
  unfold psiN gaussianPDFReal
  fun_prop

lemma psiN_bdd : ∃ C, ∀ x, psiN x ≤ C := by
  refine ⟨(√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹, fun x => ?_⟩
  unfold psiN gaussianPDFReal
  have h1 : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (x - 0) ^ 2 := sq_nonneg _
    simp only [NNReal.coe_one]
    linarith
  have h0 : 0 ≤ (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ := by positivity
  nlinarith

variable (q0 : ℝ≥0)

/-- The law of the primitives with `θ ~ N(0, q0)`, `ε_t, v_t ~ N(0, 1)`. -/
noncomputable abbrev PG : Measure Ω := law (gaussianReal 0 q0) (gaussianReal 0 1) (vLaw psiN)

/-- The variance of `θ` given the history, along revealing play. -/
noncomputable def qG : ℕ → ℝ
  | 0 => q0
  | t + 1 => CorA3.fA (qG t)

lemma qG_nonneg : ∀ t, 0 ≤ qG q0 t
  | 0 => q0.2
  | t + 1 => CorA3.fA_nonneg _ (qG_nonneg t)

/-- The covariance of `(θ, μ)` given the history, with `μ` known. -/
noncomputable abbrev SG (t : ℕ) : M2 := !![qG q0 t, 0; 0, 0]

lemma SG_psd (t : ℕ) : (SG q0 t).PosSemidef := psd_diag _ _ (qG_nonneg q0 t) le_rfl

lemma SG_succ (t : ℕ) : SG q0 (t + 1) = kalman (SG q0 t) 1 :=
  (CorA3.kalman_eq3 _ (qG_nonneg q0 t)).symm

/-- The law of `(x, 0)` for `x ~ N(0, q)`. -/
lemma map_mk2_gaussian {q : ℝ} (hq : 0 ≤ q) :
    (gaussianReal 0 q.toNNReal).map (fun x => mk2 x 0) =
      multivariateGaussian 0 (!![q, 0; 0, 0] : M2) := by
  set S : M2 := !![q, 0; 0, 0] with hS
  have hpsd : S.PosSemidef := psd_diag q 0 hq le_rfl
  have h0 := (measurePreserving_eval_multivariateGaussian (μ := (0 : E2)) hpsd (i := 0)).map_eq
  have h1 := (measurePreserving_eval_multivariateGaussian (μ := (0 : E2)) hpsd (i := 1)).map_eq
  have hS0 : S 0 0 = q := by simp [hS]
  have hS1 : S 1 1 = 0 := by simp [hS]
  rw [hS0] at h0
  rw [hS1] at h1
  simp only [Real.toNNReal_zero, gaussianReal_zero_var, PiLp.zero_apply] at h0 h1
  have hm0 : Measurable (fun u : E2 => u 0) := br_meas_coord measurable_id 0
  have hm1 : Measurable (fun u : E2 => u 1) := br_meas_coord measurable_id 1
  have hae : ∀ᵐ u ∂(multivariateGaussian (0 : E2) S), u 1 = 0 := by
    have : ∀ᵐ x ∂((multivariateGaussian (0 : E2) S).map (fun u : E2 => u 1)), x = 0 := by
      rw [h1, ae_dirac_eq]
      exact Filter.eventually_pure.2 rfl
    exact ae_of_ae_map hm1.aemeasurable this
  have hm2 : Measurable (fun x : ℝ => mk2 x 0) := measurable_mk2 measurable_id measurable_const
  rw [← h0, Measure.map_map hm2 hm0]
  conv_rhs => rw [← Measure.map_id (μ := multivariateGaussian (0 : E2) S)]
  refine Measure.map_congr ?_
  filter_upwards [hae] with u hu
  ext i
  fin_cases i
  · simp
  · simp [hu]

section Noise

/-- The noise of period `t` is `N(0, I)`. -/
lemma law_xi (t : ℕ) : (PG q0).map (fun ω => mk2 (epsV t ω) (vV t ω)) = stdGaussian E2 := by
  have hε : Measurable (epsV t) := measurable_pi_apply _
  have hv : Measurable (vV t) := measurable_pi_apply _
  have hind : IndepFun (epsV t) (vV t) (PG q0) := by
    have h := indep_v (gaussianReal 0 q0) (gaussianReal 0 1) (vLaw psiN) t
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right h le_sup_right).symm
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hε.aemeasurable hv.aemeasurable).1 hind
  rw [map_epsV, map_vV, vLaw_psiN] at hprod
  have hfin := (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  have e : (fun ω => mk2 (epsV t ω) (vV t ω)) =
      (WithLp.toLp 2) ∘ (MeasurableEquiv.finTwoArrow.symm) ∘ (fun ω => (epsV t ω, vV t ω)) := by
    funext ω
    simp [mk2, MeasurableEquiv.finTwoArrow, Function.comp]
  have hsymm : Measurable (MeasurableEquiv.finTwoArrow (α := ℝ)).symm :=
    MeasurableEquiv.measurable _
  have hto : Measurable (WithLp.toLp 2 : (Fin 2 → ℝ) → E2) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable
  rw [e, ← Measure.map_map hto (hsymm.comp (hε.prodMk hv)),
    ← Measure.map_map hsymm (hε.prodMk hv), hprod, ← hfin,
    Measure.map_map hsymm (MeasurableEquiv.measurable _),
    MeasurableEquiv.symm_comp_self, Measure.map_id]
  exact map_pi_eq_stdGaussian

/-- The noise of period `t` is independent of everything realised before `t`. -/
lemma indep_xi_past (t : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : Ω => mk2 (epsV t ω) (vV t ω)) inferInstance)
      (pastSigma t) (PG q0) := by
  have h := (iIndepFun_coords (gaussianReal 0 q0) (gaussianReal 0 1) (vLaw psiN)).indepFun_finset
    {2 * t + 1, 2 * t + 2} (Finset.range (2 * t + 1)) (by
      rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      have := Finset.mem_range.1 hi'
      omega) (fun i => measurable_pi_apply i)
  rw [IndepFun_iff_Indep] at h
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · have h1 : Measurable (fun f : ({2 * t + 1, 2 * t + 2} : Finset ℕ) → ℝ =>
        mk2 (f ⟨2 * t + 1, by simp⟩) (f ⟨2 * t + 2, by simp⟩)) :=
      measurable_mk2 (measurable_pi_apply _) (measurable_pi_apply _)
    exact Measurable.comap_le (h1.comp (comap_measurable
      (fun (ω : Ω) (i : ({2 * t + 1, 2 * t + 2} : Finset ℕ)) => ω i)))
  · refine Measurable.comap_le (measurable_pi_of fun j => ?_)
    have h1 : Measurable (fun f : (Finset.range (2 * t + 1)) → ℝ =>
        f ⟨j, Finset.mem_range.2 j.isLt⟩) := measurable_pi_apply _
    exact h1.comp (comap_measurable (fun (ω : Ω) (i : Finset.range (2 * t + 1)) => ω i))

end Noise

/-! ### The filter -/

/-- The filter invariant at date `t`: `θ - b(h^t)` is independent of `h^t` and `N(0, q_t)`. -/
structure GInv (q0 : ℝ≥0) (c : Profile) (t : ℕ) (b : (Fin t → ℝ) → ℝ) : Prop where
  hb : Measurable b
  indep : IndepFun (fun ω => mk2 (thetaV ω - b (hist (PG q0) c t ω)) 0) (hist (PG q0) c t) (PG q0)
  law : (PG q0).map (fun ω => mk2 (thetaV ω - b (hist (PG q0) c t ω)) 0) =
    multivariateGaussian 0 (SG q0 t)

variable {q0} {c : Profile}

lemma ginv_zero (q0 : ℝ≥0) (c : Profile) : GInv q0 c 0 (fun _ => 0) := by
  refine ⟨measurable_const, ?_, ?_⟩
  · have e : hist (PG q0) c 0 = fun _ => Fin.elim0 := rfl
    rw [e]
    exact indepFun_const_right _ _
  · have hθ : Measurable thetaV := measurable_pi_apply _
    have hm : Measurable (fun x : ℝ => mk2 x 0) := measurable_mk2 measurable_id measurable_const
    have e : (fun ω => mk2 (thetaV ω - 0) 0) = (fun x : ℝ => mk2 x 0) ∘ thetaV := by
      funext ω; simp
    rw [e, ← Measure.map_map hm hθ, map_thetaV]
    have := map_mk2_gaussian (q := (q0 : ℝ)) q0.2
    simpa [SG, qG] using this

/-- The gain at `diag(q, 0)`. -/
lemma gain_SG (t : ℕ) : gainK (SG q0 t) 0 0 = qG q0 t / (1 + qG q0 t) ∧ gainK (SG q0 t) 0 1 = 0 := by
  rw [SG, gainK_diag _ 0 (qG_nonneg q0 t) le_rfl]
  simp

/-- The information of player `t`: the history and the signal. -/
noncomputable def Fs (P : Measure Ω) (c : Profile) (t : ℕ) : MeasurableSpace Ω :=
  histSigma P c t ⊔ MeasurableSpace.comap (fun ω => thetaV ω + epsV t ω) inferInstance

section Step

variable (hc : ∀ t, Measurable (Function.uncurry (c t))) {t : ℕ} {b : (Fin t → ℝ) → ℝ}
  (h : GInv q0 c t b)

include hc h

/-- All the independence facts of one step of the filter. -/
lemma step_facts :
    let P := PG q0
    let H := hist P c t
    let e : Ω → E2 := fun ω => mk2 (thetaV ω - b (H ω)) 0
    let ξ : Ω → E2 := fun ω => mk2 (epsV t ω) (vV t ω)
    Measurable H ∧ Measurable e ∧ Measurable ξ ∧ IndepFun (fun ω => (e ω, H ω)) ξ P ∧
      IndepFun (fun ω => (e ω, ξ ω)) H P ∧ P.map (fun ω => (e ω, ξ ω)) = periodLaw 0 (SG q0 t) := by
  intro P H e ξ
  have hH : Measurable H := measurable_hist (PG q0) c hc t
  have hθ : Measurable thetaV := measurable_pi_apply _
  have he : Measurable e :=
    measurable_mk2 (hθ.sub (h.hb.comp hH)) measurable_const
  have hξ : Measurable ξ :=
    measurable_mk2 (measurable_pi_apply _) (measurable_pi_apply _)
  have hHp : Measurable[pastSigma t] H := measurable_hist_past (PG q0) c hc t
  have hθp : Measurable[pastSigma t] thetaV := measurable_coord_past (by omega)
  have hep : Measurable[pastSigma t] e :=
    measurable_mk2 (hθp.sub (h.hb.comp hHp)) measurable_const
  have hind1 : IndepFun (fun ω => (e ω, H ω)) ξ P := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right (indep_xi_past q0 t) (hep.prodMk hHp).comap_le).symm
  have hind2 : IndepFun (fun ω => (e ω, ξ ω)) H P :=
    br_indep_regroup he hH hξ hind1 h.indep
  have heξ : IndepFun e ξ P :=
    hind1.comp (φ := Prod.fst) (ψ := id) measurable_fst measurable_id
  have hlaw : P.map (fun ω => (e ω, ξ ω)) = periodLaw 0 (SG q0 t) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map he.aemeasurable hξ.aemeasurable).1 heξ, h.law,
      law_xi q0 t]
    rfl
  exact ⟨hH, he, hξ, hind1, hind2, hlaw⟩

/-- `Y_t = b(h^t) + K₀₀ (s_t - b(h^t))`. -/
lemma Ycond_eq :
    Ycond (PG q0) c t =ᵐ[PG q0] fun ω => b (hist (PG q0) c t ω) +
      gainK (SG q0 t) 0 0 * (thetaV ω - b (hist (PG q0) c t ω) + epsV t ω) := by
  obtain ⟨hH, he, hξ, hind1, hind2, hlaw⟩ := step_facts hc h
  set P := PG q0 with hP
  set H := hist P c t with hHdef
  set S := SG q0 t with hSdef
  have hS : S.PosSemidef := SG_psd q0 t
  have hθ : Measurable thetaV := measurable_pi_apply _
  have hε : Measurable (epsV t) := measurable_pi_apply _
  have hΨ : Measurable (fun ω => (mk2 (thetaV ω - b (H ω)) 0, mk2 (epsV t ω) (vV t ω))) :=
    he.prodMk hξ
  obtain ⟨hk, hk01⟩ := gain_SG (q0 := q0) t
  set k := gainK S 0 0 with hkdef
  let R : Ω → ℝ := fun ω => resθ 0 S (mk2 (thetaV ω - b (H ω)) 0, mk2 (epsV t ω) (vV t ω))
  let Pr : Ω → E2 := fun ω => privInfo (mk2 (thetaV ω - b (H ω)) 0, mk2 (epsV t ω) (vV t ω))
  have hR : Measurable R := measurable_resθ.comp hΨ
  have hPr : Measurable Pr := measurable_privInfo.comp hΨ
  have hPr0 : ∀ ω, Pr ω 0 = thetaV ω - b (H ω) + epsV t ω := fun ω => by simp [Pr, privInfo]
  have hindRP : IndepFun R Pr P :=
    br_indep_of_map hΨ measurable_resθ measurable_privInfo (by rw [hlaw]; exact indep_resθ hS)
  have hind3 : IndepFun (fun ω => (R ω, Pr ω)) H P :=
    hind2.comp (φ := fun p => (resθ 0 S p, privInfo p)) (ψ := id)
      (measurable_resθ.prodMk measurable_privInfo) measurable_id
  have hfinal : IndepFun R (fun ω => (Pr ω, H ω)) P := br_indep_assoc hR hPr hH hind3 hindRP
  -- the decomposition `θ = A + R`
  let A : Ω → ℝ := fun ω => b (H ω) + k * (thetaV ω - b (H ω) + epsV t ω)
  have hdec : ∀ ω, thetaV ω = A ω + R ω := by
    intro ω
    have h00 : gainK S 0 0 = k := rfl
    have h01 : gainK S 0 1 = 0 := hk01
    simp [A, R, resθ, privInfo, h00, h01]
  have hs : Measurable (fun ω => thetaV ω + epsV t ω) := hθ.add hε
  have hFle : Fs P c t ≤ (inferInstance : MeasurableSpace Ω) := sup_le hH.comap_le hs.comap_le
  -- integrability
  have hRint : Integrable R P := by
    have h1 : Integrable (resθ 0 S) (periodLaw 0 S) := cond_integrable (resθ_coord)
    rw [← hlaw] at h1
    exact (integrable_map_measure measurable_resθ.aestronglyMeasurable hΨ.aemeasurable).1 h1
  have hθint : Integrable thetaV P := by
    have h1 : Integrable (fun x : ℝ => x) (P.map thetaV) := by
      rw [hP, map_thetaV]
      exact (memLp_id_gaussianReal (μ := 0) (v := q0) 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id hθ.aemeasurable).1 h1
  have hAint : Integrable A P := (hθint.sub hRint).congr (ae_of_all _ fun ω => by
    simp only [Pi.sub_apply]
    rw [hdec ω]
    ring)
  have hAm : StronglyMeasurable[Fs P c t] A := by
    have h1 : Measurable[Fs P c t] H := (comap_measurable H).mono le_sup_left le_rfl
    have h2 : Measurable[Fs P c t] (fun ω => thetaV ω + epsV t ω) :=
      (comap_measurable (fun ω => thetaV ω + epsV t ω)).mono le_sup_right le_rfl
    have h3 : Measurable[Fs P c t] (fun ω => b (H ω)) := h.hb.comp h1
    have e : A = fun ω => b (H ω) + k * ((thetaV ω + epsV t ω) - b (H ω)) := by
      funext ω; simp only [A]; ring
    rw [e]
    exact (h3.add (measurable_const.mul (h2.sub h3))).stronglyMeasurable
  -- `R` is independent of the conditioning information
  have hFcomap : Fs P c t ≤ MeasurableSpace.comap (fun ω => (Pr ω, H ω)) inferInstance := by
    have hm1 : Measurable[MeasurableSpace.comap (fun ω => (Pr ω, H ω)) inferInstance] H :=
      measurable_snd.comp (comap_measurable _)
    have hm2 : Measurable[MeasurableSpace.comap (fun ω => (Pr ω, H ω)) inferInstance] Pr :=
      measurable_fst.comp (comap_measurable _)
    refine sup_le hm1.comap_le ?_
    have e : (fun ω => thetaV ω + epsV t ω) = fun ω => Pr ω 0 + b (H ω) := by
      funext ω; rw [hPr0]; ring
    rw [e]
    have hc0 : Measurable (fun u : E2 => u 0) := br_meas_coord measurable_id 0
    exact ((hc0.comp hm2).add (h.hb.comp hm1)).comap_le
  have hRcond : P[R | Fs P c t] =ᵐ[P] fun _ => ∫ ω, R ω ∂P := by
    refine condExp_indep_eq hR.comap_le hFle (comap_measurable R).stronglyMeasurable ?_
    rw [IndepFun_iff_Indep] at hfinal
    exact indep_of_indep_of_le_right hfinal hFcomap
  have hR0 : ∫ ω, R ω ∂P = 0 := by
    have h1 : ∫ ω, R ω ∂P = ∫ y, resθ 0 S y ∂(P.map _) :=
      (integral_map hΨ.aemeasurable measurable_resθ.aestronglyMeasurable).symm
    rw [h1, hlaw]
    exact integral_resθ
  have hsum : Ycond P c t =ᵐ[P] P[A | Fs P c t] + P[R | Fs P c t] := by
    have e : thetaV = A + R := funext hdec
    have hY : Ycond P c t = P[thetaV | Fs P c t] := rfl
    rw [hY, e]
    exact condExp_add hAint hRint (Fs P c t)
  have hA : P[A | Fs P c t] = A := condExp_of_stronglyMeasurable hFle hAm hAint
  filter_upwards [hsum, hRcond] with ω a1 a2
  rw [a1, Pi.add_apply, hA, a2, hR0, add_zero]

/-- Under the invariant, the public's conditional law of `Y_t` given `h^t` is Gaussian. -/
theorem beliefY_of_inv :
    ∀ᵐ ω ∂(PG q0), beliefY (PG q0) c t (hist (PG q0) c t ω) =
      gaussianReal (b (hist (PG q0) c t ω)) (tauOf (qG q0 t).toNNReal) := by
  obtain ⟨hH, he, hξ, hind1, hind2, hlaw⟩ := step_facts hc h
  set P := PG q0 with hP
  set H := hist P c t with hHdef
  set S := SG q0 t with hSdef
  have hS : S.PosSemidef := SG_psd q0 t
  obtain ⟨hk, -⟩ := gain_SG (q0 := q0) t
  have hq := qG_nonneg q0 t
  set q := qG q0 t with hqdef
  have hΨ : Measurable (fun ω => (mk2 (thetaV ω - b (H ω)) 0, mk2 (epsV t ω) (vV t ω))) :=
    he.prodMk hξ
  set k := gainK S 0 0 with hkdef
  let Pr : Ω → E2 := fun ω => privInfo (mk2 (thetaV ω - b (H ω)) 0, mk2 (epsV t ω) (vV t ω))
  have hPr : Measurable Pr := measurable_privInfo.comp hΨ
  have hc0 : Measurable (fun u : E2 => u 0) := br_meas_coord measurable_id 0
  let W : Ω → ℝ := fun ω => k * Pr ω 0
  have hW : Measurable W := (hc0.comp hPr).const_mul k
  have hind : IndepFun H W P := by
    have := hind2.symm.comp (φ := id) (ψ := fun p : E2 × E2 => k * privInfo p 0) measurable_id
      ((hc0.comp measurable_privInfo).const_mul k)
    exact this
  have hS1 : (S + 1).PosSemidef := hS.add Matrix.PosDef.one.posSemidef
  have hlawW : P.map W = gaussianReal 0 (tauOf q.toNNReal) := by
    have h1 : P.map Pr = multivariateGaussian 0 (S + 1) := by
      have e : Pr = privInfo ∘ fun ω => (mk2 (thetaV ω - b (H ω)) 0, mk2 (epsV t ω) (vV t ω)) := rfl
      rw [e, ← Measure.map_map measurable_privInfo hΨ, hlaw, privInfo_law hS]
    have h2 := (measurePreserving_eval_multivariateGaussian (μ := (0 : E2)) hS1 (i := 0)).map_eq
    have h3 := gaussianReal_map_const_mul (μ := 0) (v := ((S + 1) 0 0).toNNReal) k
    rw [mul_zero] at h3
    have e : W = (fun x => k * x) ∘ (fun u : E2 => u 0) ∘ Pr := rfl
    rw [e, ← Measure.map_map (measurable_const_mul k) (hc0.comp hPr),
      ← Measure.map_map hc0 hPr, h1, h2]
    simp only [PiLp.zero_apply]
    rw [h3]
    congr 1
    apply NNReal.eq
    have hS00 : (S + 1) 0 0 = 1 + q := by
      simp only [hSdef, SG, hqdef, Matrix.add_apply, Matrix.one_apply_eq]
      simp [add_comm]
    have h1q : (1 + q) ≠ 0 := by positivity
    rw [hS00]
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (by positivity : 0 ≤ 1 + q), tauOf,
      NNReal.coe_div, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal _ hq, hk]
    field_simp
  have hYe : Ycond P c t =ᵐ[P] fun ω => b (H ω) + W ω := by
    filter_upwards [Ycond_eq hc h] with ω hω
    have hW0 : W ω = k * (thetaV ω - b (H ω) + epsV t ω) := by simp [W, Pr, privInfo]
    rw [hW0]
    exact hω
  exact condDistrib_affine_gauss hH hW (measurable_Ycond (PG q0) c hc t) h.hb hind hlawW hYe

/-- One step of the filter along fully revealing play. -/
theorem ginv_succ (hmono : ∀ᵐ ω ∂(PG q0), StrictMono (c t (hist (PG q0) c t ω))) :
    ∃ b' : (Fin (t + 1) → ℝ) → ℝ, GInv q0 c (t + 1) b' := by
  obtain ⟨hH, he, hξ, hind1, hind2, hlaw⟩ := step_facts hc h
  set P := PG q0 with hP
  set H := hist P c t with hHdef
  set S := SG q0 t with hSdef
  have hS : S.PosSemidef := SG_psd q0 t
  have key := kstep hS 1 he hξ hH hind1 h.indep h.law (law_xi q0 t)
  obtain ⟨-, hk01⟩ := gain_SG (q0 := q0) t
  set ρ := regK S 1 0 with hρ
  let Zf : Ω → ℝ := fun ω => Zof 0 S 1 (mk2 (thetaV ω - b (H ω)) 0, mk2 (epsV t ω) (vV t ω))
  have hΨ : Measurable (fun ω => (mk2 (thetaV ω - b (H ω)) 0, mk2 (epsV t ω) (vV t ω))) :=
    he.prodMk hξ
  have hZf : Measurable Zf := (CC.Bridge.measurable_Zof S 1).comp hΨ
  let b' : (Fin (t + 1) → ℝ) → ℝ := fun h' => b (Fin.init h') +
    ρ * (invS (c t (Fin.init h')) (h' (Fin.last t)) - b (Fin.init h'))
  have hinit : Measurable (fun h' : Fin (t + 1) → ℝ => (Fin.init h' : Fin t → ℝ)) :=
    measurable_fin_init
  have hb' : Measurable b' := by
    have hF : Measurable (Function.uncurry (fun h' : Fin (t + 1) → ℝ => c t (Fin.init h'))) :=
      (hc t).comp ((hinit.comp measurable_fst).prodMk measurable_snd)
    have hinv : Measurable (fun h' : Fin (t + 1) → ℝ =>
        invS (c t (Fin.init h')) (h' (Fin.last t))) :=
      measurable_invS hF (measurable_pi_apply _)
    exact (h.hb.comp hinit).add (measurable_const.mul (hinv.sub (h.hb.comp hinit)))
  -- the realised type
  have hvt : ∀ᵐ ω ∂P, vtil P c t ω = b (H ω) + Zf ω := by
    filter_upwards [Ycond_eq hc h] with ω hω
    have h01 : gainK S 0 1 = 0 := hk01
    have hY : Ycond P c t ω = b (H ω) + gainK S 0 0 * (thetaV ω - b (H ω) + epsV t ω) := hω
    simp only [vtil, hY, Zf, Zof, privInfo, h01]
    simp
    ring
  -- `b'` at the next history
  have hb'H : ∀ᵐ ω ∂P, b' (hist P c (t + 1) ω) = b (H ω) + ρ * Zf ω := by
    filter_upwards [hvt, hmono] with ω hv hm
    have h1 : Fin.init (hist P c (t + 1) ω) = H ω := hist_eq_init P c t ω
    have h2 : hist P c (t + 1) ω (Fin.last t) = c t (H ω) (vtil P c t ω) := hist_last P c t ω
    simp only [b', h1, h2]
    rw [invS_apply hm, hv]
    ring
  have hRe : ∀ᵐ ω ∂P, resZ 0 S 1 (mk2 (thetaV ω - b (H ω)) 0, mk2 (epsV t ω) (vV t ω)) =
      mk2 (thetaV ω - b' (hist P c (t + 1) ω)) 0 := by
    filter_upwards [hb'H] with ω hω
    have hreg1 : regK S 1 1 = 0 := by
      rw [regK_apply1]
      simp [hSdef, SG]
    ext i
    fin_cases i
    · simp [resZ, regC, hω, ← hρ, Zf]
      ring
    · simp [resZ, regC, hreg1]
  let G : ℝ × (Fin t → ℝ) → (Fin (t + 1) → ℝ) := fun p => Fin.snoc p.2 (c t p.2 (b p.2 + p.1))
  have hG : Measurable G := measurable_snoc_aux measurable_snd
    ((hc t).comp (measurable_snd.prodMk ((h.hb.comp measurable_snd).add measurable_fst)))
  have hHe : ∀ᵐ ω ∂P, G (Zf ω, H ω) = hist P c (t + 1) ω := by
    filter_upwards [hvt] with ω hv
    rw [hist_succ]
    simp only [G, act]
    rw [hv]
  refine ⟨b', hb', ?_, ?_⟩
  · have h1 := key.1.comp (φ := id) (ψ := G) measurable_id hG
    exact h1.congr hRe hHe
  · have h1 := key.2
    rw [Measure.map_congr hRe] at h1
    rw [SG_succ]
    exact h1

end Step

/-- Along fully revealing play the invariant holds at every date. -/
theorem ginv_exists (hc : ∀ t, Measurable (Function.uncurry (c t))) : ∀ t,
    (∀ s, s < t → ∀ᵐ ω ∂(PG q0), StrictMono (c s (hist (PG q0) c s ω))) →
    ∃ b : (Fin t → ℝ) → ℝ, GInv q0 c t b
  | 0, _ => ⟨_, ginv_zero q0 c⟩
  | t + 1, hrev => by
    obtain ⟨b, hb⟩ := ginv_exists hc t fun s hs => hrev s (hs.trans (Nat.lt_succ_self t))
    exact ginv_succ hc hb (hrev t (Nat.lt_succ_self t))

/-- **The public's belief about `Y_t` is Gaussian along fully revealing play.** With
`q_t = σ²_{θ,t}` and `τ_t = q_t²/(1 + q_t)`. -/
theorem beliefY_gaussian (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ)
    (hrev : ∀ s, s < t → ∀ᵐ ω ∂(PG q0), StrictMono (c s (hist (PG q0) c s ω))) :
    ∃ b : (Fin t → ℝ) → ℝ, ∀ᵐ ω ∂(PG q0), beliefY (PG q0) c t (hist (PG q0) c t ω) =
      gaussianReal (b (hist (PG q0) c t ω)) (tauOf (qG q0 t).toNNReal) := by
  obtain ⟨b, hb⟩ := ginv_exists hc t hrev
  exact ⟨b, beliefY_of_inv hc hb⟩

/-- **The assumption of Proposition A5 holds in the Linear-Gaussian model** at the histories that
fully revealing play reaches. -/
theorem hm_gaussian (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ)
    (hrev : ∀ s, s < t → ∀ᵐ ω ∂(PG q0), StrictMono (c s (hist (PG q0) c s ω))) :
    ∀ᵐ ω ∂(PG q0), ContDiff ℝ 2 (mfun psiN (beliefY (PG q0) c t (hist (PG q0) c t ω))) ∧
      ∀ x, 0 < iteratedDeriv 2 (mfun psiN (beliefY (PG q0) c t (hist (PG q0) c t ω))) x ∧
        iteratedDeriv 2 (mfun psiN (beliefY (PG q0) c t (hist (PG q0) c t ω))) x ≤ 2 := by
  obtain ⟨b, hb⟩ := beliefY_gaussian hc t hrev
  filter_upwards [hb] with ω hω
  rw [hω]
  obtain ⟨h1, h2⟩ := mfun_gaussian_regular (s := 1) one_ne_zero (tauOf (qG q0 t).toNNReal)
    (b (hist (PG q0) c t ω))
  exact ⟨h1, fun x => (h2 x).2⟩

/-- Under the invariant, `b(h^t)` is the posterior mean of `θ`. -/
theorem post_of_inv (hc : ∀ t, Measurable (Function.uncurry (c t))) {t : ℕ}
    {b : (Fin t → ℝ) → ℝ} (h : GInv q0 c t b) :
    (PG q0)[thetaV | histSigma (PG q0) c t] =ᵐ[PG q0] fun ω => b (hist (PG q0) c t ω) := by
  obtain ⟨hH, he, -, -, -, -⟩ := step_facts hc h
  set P := PG q0 with hP
  set H := hist P c t with hHdef
  have hθ : Measurable thetaV := measurable_pi_apply _
  have hc0 : Measurable (fun u : E2 => u 0) := br_meas_coord measurable_id 0
  let e0 : Ω → ℝ := fun ω => thetaV ω - b (H ω)
  have he0 : Measurable e0 := hθ.sub (h.hb.comp hH)
  have hind : IndepFun e0 H P := by
    have := h.indep.comp (φ := fun u : E2 => u 0) (ψ := id) hc0 measurable_id
    have e : (fun ω => ((fun u : E2 => u 0) ∘ fun ω => mk2 (thetaV ω - b (H ω)) 0) ω) = e0 := by
      funext ω; simp [e0]
    exact (by simpa [Function.comp_def, e0] using this : IndepFun e0 H P)
  have hSpsd := SG_psd q0 t
  have hmapl : P.map e0 = gaussianReal 0 ((SG q0 t) 0 0).toNNReal := by
    have e : e0 = (fun u : E2 => u 0) ∘ fun ω => mk2 (thetaV ω - b (H ω)) 0 := by
      funext ω; simp [e0]
    rw [e, ← Measure.map_map hc0 he, h.law]
    simpa using (measurePreserving_eval_multivariateGaussian (μ := (0 : E2)) hSpsd (i := 0)).map_eq
  have he0int : Integrable e0 P := by
    have h1 : Integrable (fun x : ℝ => x) (P.map e0) := by
      rw [hmapl]
      exact (memLp_id_gaussianReal 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id he0.aemeasurable).1 h1
  have he0zero : ∫ ω, e0 ω ∂P = 0 := by
    have h1 := integral_map (μ := P) he0.aemeasurable (f := fun x : ℝ => x) aestronglyMeasurable_id
    rw [hmapl, integral_id_gaussianReal] at h1
    exact h1.symm
  have hθint : Integrable thetaV P := by
    have h1 : Integrable (fun x : ℝ => x) (P.map thetaV) := by
      rw [hP, map_thetaV]
      exact (memLp_id_gaussianReal (μ := 0) (v := q0) 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id hθ.aemeasurable).1 h1
  have hbint : Integrable (fun ω => b (H ω)) P :=
    (hθint.sub he0int).congr (ae_of_all _ fun ω => by simp [e0])
  have hdec : thetaV = (fun ω => b (H ω)) + e0 := by
    funext ω; simp [e0]
  have hle : histSigma P c t ≤ (inferInstance : MeasurableSpace Ω) := hH.comap_le
  have hbm : StronglyMeasurable[histSigma P c t] (fun ω => b (H ω)) :=
    (h.hb.comp (comap_measurable H)).stronglyMeasurable
  have hsum : P[thetaV | histSigma P c t] =ᵐ[P]
      P[fun ω => b (H ω) | histSigma P c t] + P[e0 | histSigma P c t] := by
    rw [hdec]
    exact condExp_add hbint he0int _
  have hb0 : P[fun ω => b (H ω) | histSigma P c t] = fun ω => b (H ω) :=
    condExp_of_stronglyMeasurable hle hbm hbint
  have hzero : P[e0 | histSigma P c t] =ᵐ[P] fun _ => ∫ ω, e0 ω ∂P := by
    refine condExp_indep_eq he0.comap_le hle (comap_measurable e0).stronglyMeasurable ?_
    rw [IndepFun_iff_Indep] at hind
    exact hind
  filter_upwards [hsum, hzero] with ω a1 a2
  rw [a1, Pi.add_apply, hb0, a2, he0zero, add_zero]

/-- **The closed form of `m` in the model (proof of Corollary A3).** Along fully revealing play,
with `q_t = σ²_{θ,t}` and `τ_t = q_t²/(1 + q_t)`, at almost every history
`m(x | h^t) = τ_t/(1 + τ_t) + (1/(1 + τ_t))² (x - θ(h^t))²`. -/
theorem m_closed_form (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ)
    (hrev : ∀ s, s < t → ∀ᵐ ω ∂(PG q0), StrictMono (c s (hist (PG q0) c s ω))) :
    ∀ᵐ ω ∂(PG q0), ∀ x,
      mfun psiN (beliefY (PG q0) c t (hist (PG q0) c t ω)) x =
        (tauOf (qG q0 t).toNNReal : ℝ) / (1 + tauOf (qG q0 t).toNNReal) +
          (1 / (1 + (tauOf (qG q0 t).toNNReal : ℝ))) ^ 2 *
            (x - ((PG q0)[thetaV | histSigma (PG q0) c t]) ω) ^ 2 := by
  obtain ⟨b, hb⟩ := ginv_exists hc t hrev
  filter_upwards [beliefY_of_inv hc hb, post_of_inv hc hb] with ω h1 h2 x
  rw [h1, h2, mfun_gaussian (s := 1) one_ne_zero]
  simp

/-- **Proposition A5 in the Linear-Gaussian model, `κ ≤ κck`.** With `θ ~ N(0, q0)` and
`ε_t, v_t ~ N(0, 1)`, all the hypotheses of `propA5_exists` hold, so there is a measurable profile
that at almost every realised history is a fully revealing equilibrium satisfying `D1^∞`, with
social learning about fundamentals. -/
theorem propA5_exists_gaussian (q0 : ℝ≥0) (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ κck) :
    ∃ c : Profile, (∀ t, Measurable (Function.uncurry (c t))) ∧
      (∀ t, ∀ᵐ ω ∂(PG q0), StrictMono (c t (hist (PG q0) c t ω)) ∧
        ∃ S : CC.General.Setting, S.g = (fun z => z ^ 2) ∧ S.F = typeLaw (PG q0) c t (hist (PG q0) c t ω) ∧
          S.ℓ = (fun x => κ * (mfun psiN (beliefY (PG q0) c t (hist (PG q0) c t ω)) x -
            mfun psiN (beliefY (PG q0) c t (hist (PG q0) c t ω)) S.μ)) ∧
          ∃ φ : ℝ → Measure EReal, S.IsCPBE (c t (hist (PG q0) c t ω)) φ ∧
            S.D1Inf (c t (hist (PG q0) c t ω)) φ) ∧
      ∀ᵐ r ∂((PG q0).map thetaV), TendstoInMeasure (condDistrib id thetaV (PG q0) r)
        (fun t => (PG q0)[thetaV | histSigma (PG q0) c t]) atTop (fun _ => r) := by
  have hN2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  refine propA5_exists (gaussianReal 0 q0) (gaussianReal 0 1) psiN κ hκ0 hκ
    (memLp_id_gaussianReal (μ := 0) (v := q0) 2).integrable_sq ?_
    (fun x => gaussianPDFReal_pos _ _ _ one_ne_zero) ?_ (by rw [vLaw_psiN]; exact hN2) ?_ ?_
    (PG q0) rfl (fun c hc t hrev => hm_gaussian hc t hrev)
  · exact psiN_continuous
  · exact psiN_bdd
  · intro x
    unfold psiN gaussianPDFReal
    simp
  · rw [vLaw_psiN]
    have := (memLp_id_gaussianReal (μ := 0) (v := 1) 3).integrable_norm_pow (by norm_num)
    simpa [Real.norm_eq_abs] using this

end CC.LearnTheta
