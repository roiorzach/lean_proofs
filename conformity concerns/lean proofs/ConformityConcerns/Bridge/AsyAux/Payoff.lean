import ConformityConcerns.Bridge.AsyAux.Fiber
import ConformityConcerns.Bridge.Hist

/-!
# Expected adaptation payoff and expected conformity term at date `t`

* The adaptation error `a_t - γ_t θ - v_t` is (a.s.) a linear form in `(x - m_t, ε_t)` with
  coefficients depending on the weights (`adapt_err_eq`), so its second moment is the integral
  over the weights of `adaptQ` (`integral_adapt`).
* The conformity term: `∫ (b - p)² dφ(b | W)` integrates to `E(Y - p)²` when `p` is a function
  of `W` (`integral_condDistrib_sq`), and `E(v_t - μ(h^t))² = E(1 + σ²_{μ,t})`
  (`integral_conf`).
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

set_option warn.classDefReducibility false

/-- If `p` is a function of `W`, then `E ∫ (b - p)² dφ(b | W) = E (Y - p)²` with `φ(· | W)` the
conditional law of `Y` given `W`. -/
lemma integral_condDistrib_sq {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → β} {Y : Ω → ℝ} {p : Ω → ℝ}
    (hW : Measurable W) (hY : Measurable Y)
    (hp : StronglyMeasurable[MeasurableSpace.comap W inferInstance] p)
    (hint : Integrable (fun ω => (Y ω - p ω) ^ 2) μ) :
    ∫ ω, (∫ b, (b - p ω) ^ 2 ∂(condDistrib Y W μ (W ω))) ∂μ = ∫ ω, (Y ω - p ω) ^ 2 ∂μ := by
  obtain ⟨g, hg, hpg⟩ := hp.exists_eq_measurable_comp
  have hf : StronglyMeasurable (fun z : β × ℝ => (z.2 - g z.1) ^ 2) :=
    ((measurable_snd.sub (hg.measurable.comp measurable_fst)).pow_const 2).stronglyMeasurable
  have hfW : (fun ω => (fun z : β × ℝ => (z.2 - g z.1) ^ 2) (W ω, Y ω)) =
      fun ω => (Y ω - p ω) ^ 2 := by
    funext ω
    simp only [hpg, Function.comp_apply]
  have hint' : Integrable (fun ω => (fun z : β × ℝ => (z.2 - g z.1) ^ 2) (W ω, Y ω)) μ := by
    rw [hfW]; exact hint
  have h1 := condExp_prod_ae_eq_integral_condDistrib (μ := μ) hW hY.aemeasurable hf hint'
  have h2 : ∀ ω, ∫ y, (fun z : β × ℝ => (z.2 - g z.1) ^ 2) (W ω, y) ∂(condDistrib Y W μ (W ω)) =
      ∫ b, (b - p ω) ^ 2 ∂(condDistrib Y W μ (W ω)) := by
    intro ω
    simp only [hpg, Function.comp_apply]
  calc ∫ ω, (∫ b, (b - p ω) ^ 2 ∂(condDistrib Y W μ (W ω))) ∂μ
      = ∫ ω, (μ[fun ω => (fun z : β × ℝ => (z.2 - g z.1) ^ 2) (W ω, Y ω) |
          MeasurableSpace.comap W inferInstance]) ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h1] with ω hω
        rw [hω, h2]
    _ = ∫ ω, (fun z : β × ℝ => (z.2 - g z.1) ^ 2) (W ω, Y ω) ∂μ := integral_condExp hW.comap_le
    _ = ∫ ω, (Y ω - p ω) ^ 2 ∂μ := by rw [hfW]

variable (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]

/-- `λ_t` at a revealing date, `0` at a pooling date. -/
noncomputable def rlam (γ : ℕ → ℝ) (t : ℕ) : ℝ :=
  haveI := Classical.propDecidable (revP κ S₁ γ t)
  if revP κ S₁ γ t then lamF κ (SigP κ S₁ γ t) (γ t) else 0

lemma measurable_rlam (t : ℕ) : Measurable (fun γ => rlam κ S₁ γ t) := by
  have h1 : Measurable (fun γ : ℕ → ℝ => (SigP κ S₁ γ t, γ t)) :=
    (measurable_SigP κ S₁ t).prodMk (measurable_pi_apply t)
  have hf : Measurable (fun γ : ℕ → ℝ => lamF κ (SigP κ S₁ γ t) (γ t)) :=
    Measurable.comp (g := fun p : M2 × ℝ => lamF κ p.1 p.2)
      (f := fun γ : ℕ → ℝ => (SigP κ S₁ γ t, γ t)) (meas_lamF κ) h1
  have e : (fun γ => rlam κ S₁ γ t) = fun γ =>
      haveI := Classical.propDecidable (revP κ S₁ γ t)
      if revP κ S₁ γ t then lamF κ (SigP κ S₁ γ t) (γ t) else 0 := rfl
  rw [e]
  exact br_ite (p := fun γ => revP κ S₁ γ t) (f := fun γ => lamF κ (SigP κ S₁ γ t) (γ t))
    (g := fun _ => 0) (measurableSet_revP κ S₁ t) hf measurable_const

lemma measurable_loadA_t (t : ℕ) (i : Fin 2) :
    Measurable (fun γ : ℕ → ℝ => loadA (SigP κ S₁ γ t) (γ t) i) :=
  br_meas_loadA (measurable_SigP κ S₁ t) (measurable_pi_apply t) i

/-- The second moment of the adaptation error along the weight path `γ`. -/
noncomputable def adaptQ (γ : ℕ → ℝ) (t : ℕ) : ℝ :=
  qf (SigP κ S₁ γ t) (rlam κ S₁ γ t * loadA (SigP κ S₁ γ t) (γ t) 0 - γ t)
    (rlam κ S₁ γ t * loadA (SigP κ S₁ γ t) (γ t) 1 - 1)
    (rlam κ S₁ γ t * loadA (SigP κ S₁ γ t) (γ t) 0)
    (rlam κ S₁ γ t * loadA (SigP κ S₁ γ t) (γ t) 1 - 1)

lemma priv_apply (t : ℕ) (ω : Ωg) (i : Fin 2) : priv t ω i = ω.1 i + ω.2.1 t i := by
  simp [priv]

omit [IsProbabilityMeasure G] in
/-- The adaptation error as a linear form in `(x - m_t, ε_t)`. -/
lemma adapt_err_eq (t : ℕ) (ω : Ωg)
    (hθ : postTheta κ S₁ G t ω = kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t 0)
    (hμ : postMu κ S₁ G t ω = kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t 1) :
    eqAct κ S₁ G t ω - gam ω t * thetaV ω - priv t ω 1 =
      (rlam κ S₁ (gam ω) t * loadA (SigP κ S₁ (gam ω) t) (gam ω t) 0 - gam ω t) *
          (ω.1 0 - kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t 0) +
        (rlam κ S₁ (gam ω) t * loadA (SigP κ S₁ (gam ω) t) (gam ω t) 1 - 1) *
          (ω.1 1 - kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t 1) +
        (rlam κ S₁ (gam ω) t * loadA (SigP κ S₁ (gam ω) t) (gam ω t) 0 * ω.2.1 t 0 +
          (rlam κ S₁ (gam ω) t * loadA (SigP κ S₁ (gam ω) t) (gam ω t) 1 - 1) * ω.2.1 t 1) := by
  rw [eqAct_eq κ S₁ G t ω, hθ, hμ]
  have hp0 := priv_apply t ω 0
  have hp1 := priv_apply t ω 1
  by_cases h : rev κ S₁ t ω
  · have h' : revP κ S₁ (gam ω) t := h
    have hobs : obs κ S₁ t ω = loadA (SigP κ S₁ (gam ω) t) (gam ω t) 0 * priv t ω 0 +
        loadA (SigP κ S₁ (gam ω) t) (gam ω t) 1 * priv t ω 1 := by
      rw [obs_eq, obsF_rev κ S₁ h']
      rfl
    have hr : rlam κ S₁ (gam ω) t = lamF κ (SigP κ S₁ (gam ω) t) (gam ω t) := by
      unfold rlam; exact ite_eq_left h'
    rw [ite_eq_left h, hobs, hr, hp0, hp1]
    simp only [thetaV]
    ring
  · have h' : ¬ revP κ S₁ (gam ω) t := h
    have hr : rlam κ S₁ (gam ω) t = 0 := by
      unfold rlam; exact ite_eq_right h'
    rw [ite_eq_right h, hr, hp1]
    simp only [thetaV]
    ring

omit [IsProbabilityMeasure G] in
lemma measurable_eqAct (t : ℕ) : Measurable (eqAct κ S₁ G t) :=
  (meas_info_eqAct κ S₁ G t).mono (infoSigma_le κ S₁ (t + 1)) le_rfl

lemma measurable_priv1 (t : ℕ) : Measurable (fun ω : Ωg => priv t ω 1) :=
  br_meas_coord (measurable_fst.add ((measurable_pi_apply t).comp
    (measurable_fst.comp measurable_snd))) 1

omit [IsProbabilityMeasure G] in
lemma measurable_postMu (t : ℕ) : Measurable (postMu κ S₁ G t) :=
  (meas_info_postMu κ S₁ G t).mono (infoSigma_le κ S₁ t) le_rfl

/-- **Expected squared adaptation error.** -/
theorem integral_adapt (hS₁ : S₁.PosSemidef) (t : ℕ) :
    ∫ ω, (eqAct κ S₁ G t ω - gam ω t * thetaV ω - priv t ω 1) ^ 2 ∂(lawG S₁ G) =
      (∫⁻ γ, ENNReal.ofReal (adaptQ κ S₁ γ t) ∂(Measure.infinitePi fun _ : ℕ => G)).toReal := by
  have hm : Measurable (fun ω => (eqAct κ S₁ G t ω - gam ω t * thetaV ω - priv t ω 1) ^ 2) :=
    (((measurable_eqAct κ S₁ G t).sub ((measurable_gam_apply t).mul
      (br_meas_coord measurable_fst 0))).sub (measurable_priv1 t)).pow_const 2
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hm.aestronglyMeasurable]
  congr 1
  refine (lintegral_congr_ae ?_).trans (lintegral_sq_lin κ S₁ G hS₁ t
    (a0 := fun γ => rlam κ S₁ γ t * loadA (SigP κ S₁ γ t) (γ t) 0 - γ t)
    (a1 := fun γ => rlam κ S₁ γ t * loadA (SigP κ S₁ γ t) (γ t) 1 - 1)
    (b0 := fun γ => rlam κ S₁ γ t * loadA (SigP κ S₁ γ t) (γ t) 0)
    (b1 := fun γ => rlam κ S₁ γ t * loadA (SigP κ S₁ γ t) (γ t) 1 - 1)
    (((measurable_rlam κ S₁ t).mul (measurable_loadA_t κ S₁ t 0)).sub (measurable_pi_apply t))
    (((measurable_rlam κ S₁ t).mul (measurable_loadA_t κ S₁ t 1)).sub measurable_const)
    ((measurable_rlam κ S₁ t).mul (measurable_loadA_t κ S₁ t 0))
    (((measurable_rlam κ S₁ t).mul (measurable_loadA_t κ S₁ t 1)).sub measurable_const))
  filter_upwards [post_ae κ S₁ G hS₁ 0 t, post_ae κ S₁ G hS₁ 1 t] with ω h0 h1
  rw [adapt_err_eq κ S₁ G t ω h0 h1]

/-- The conformity error `v_t - μ(h^t)` has second moment `E(1 + σ²_{μ,t})`. -/
theorem lintegral_conf (hS₁ : S₁.PosSemidef) (t : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((priv t ω 1 - postMu κ S₁ G t ω) ^ 2) ∂(lawG S₁ G) =
      ∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t 1 1 + 1) ∂(Measure.infinitePi fun _ : ℕ => G) := by
  refine (lintegral_congr_ae ?_).trans ((lintegral_sq_lin κ S₁ G hS₁ t
    (a0 := fun _ => 0) (a1 := fun _ => 1) (b0 := fun _ => 0) (b1 := fun _ => 1)
    measurable_const measurable_const measurable_const measurable_const).trans
      (lintegral_congr fun γ => ?_))
  · filter_upwards [post_ae κ S₁ G hS₁ 1 t] with ω h1
    have h1' : postMu κ S₁ G t ω = kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t 1 := h1
    rw [h1', priv_apply]
    congr 2
    ring
  · congr 1
    simp only [qf]
    ring

lemma integrable_conf (hS₁ : S₁.PosSemidef) (t : ℕ) :
    Integrable (fun ω => (priv t ω 1 - postMu κ S₁ G t ω) ^ 2) (lawG S₁ G) := by
  have hm : Measurable (fun ω => (priv t ω 1 - postMu κ S₁ G t ω) ^ 2) :=
    ((measurable_priv1 t).sub (measurable_postMu κ S₁ G t)).pow_const 2
  refine ⟨hm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).2 ?_⟩
  rw [lintegral_conf κ S₁ G hS₁ t]
  calc ∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t 1 1 + 1) ∂(Measure.infinitePi fun _ : ℕ => G)
      ≤ ∫⁻ _, ENNReal.ofReal (S₁ 1 1 + 1) ∂(Measure.infinitePi fun _ : ℕ => G) :=
        lintegral_mono fun γ => ENNReal.ofReal_le_ofReal (by
          have : SigP κ S₁ γ t 1 1 ≤ S₁ 1 1 :=
            SigmaC_anti11 (κ := fun _ => κ) (γ := γ) hS₁ (Nat.zero_le t)
          linarith)
    _ < ∞ := by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_lt_top

theorem integral_conf (hS₁ : S₁.PosSemidef) (t : ℕ) :
    ∫ ω, (priv t ω 1 - postMu κ S₁ G t ω) ^ 2 ∂(lawG S₁ G) =
      (∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t 1 1 + 1) ∂(Measure.infinitePi fun _ : ℕ => G)).toReal := by
  have hm : Measurable (fun ω => (priv t ω 1 - postMu κ S₁ G t ω) ^ 2) :=
    ((measurable_priv1 t).sub (measurable_postMu κ S₁ G t)).pow_const 2
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
    hm.aestronglyMeasurable, lintegral_conf κ S₁ G hS₁ t]

omit [IsProbabilityMeasure G] in
/-- The posterior mean `μ(h^t)` is a function of `(h^t, a_t)`. -/
lemma sm_postMu_hist (t : ℕ) :
    StronglyMeasurable[MeasurableSpace.comap (fun ω => (((fun i : Fin (t + 1) => gam ω i),
      (fun i : Fin t => eqAct κ S₁ G i ω)), eqAct κ S₁ G t ω)) inferInstance]
      (postMu κ S₁ G t) := by
  have h1 : StronglyMeasurable[histSigma κ S₁ G t] (postMu κ S₁ G t) := by
    rw [histSigma_eq_info κ S₁ G t]; exact stronglyMeasurable_condExp
  refine h1.mono (Measurable.comap_le ?_)
  exact measurable_fst.comp (comap_measurable _)

omit [IsProbabilityMeasure G] in
lemma measurable_histAct (t : ℕ) :
    Measurable (fun ω => (((fun i : Fin (t + 1) => gam ω i),
      (fun i : Fin t => eqAct κ S₁ G i ω)), eqAct κ S₁ G t ω)) := by
  have h1 : Measurable (fun ω => (fun i : Fin (t + 1) => gam ω i)) :=
    Measurable.of_eval fun (i : Fin (t + 1)) => measurable_gam_apply i
  have h2 : Measurable (fun ω => (fun i : Fin t => eqAct κ S₁ G i ω)) :=
    Measurable.of_eval fun (i : Fin t) => measurable_eqAct κ S₁ G i
  exact (h1.prodMk h2).prodMk (measurable_eqAct κ S₁ G t)

end CC.Bridge
