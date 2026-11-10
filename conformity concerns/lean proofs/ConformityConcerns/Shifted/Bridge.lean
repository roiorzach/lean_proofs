import ConformityConcerns.Shifted.Dynamics
import ConformityConcerns.Bridge.Prop2

/-!
# Shifted preferences: Proposition 2 with the paper's definition of social learning, under the
alternative selection

The primitives and notation are those of `Bridge/Defs.lean`. By `periodRevealingAlt_iff` and
`SigmaSeqAlt_eq`, under the alternative selection with shift `c` a date is revealing iff
`κ s̃(h^t)² ≤ κck` (`Bridge.rev`) and the covariance process is `Bridge.Sig`. By `altEq_char`,
at a revealing date the action is
`a_t = E(Z_t | h^t) + λ_t (Z_t - E(Z_t | h^t)) + κ (s̃/λ_t) c`, with
`λ_t = (1 + √(1 - 4κ s̃²))/2`, `E(Z_t | h^t) = γ_t θ(h^t) + μ(h^t)` and
`Z_t - E(Z_t | h^t) = A_t · ((s_t, v_t) - (θ(h^t), μ(h^t)))`; at a pooling date
`a_t = γ_t θ(h^t) + μ(h^t)`. This is `Bridge.eqAct` plus `κ (s̃/λ_t) c` at revealing dates.
-/

namespace CC.Shifted

open MeasureTheory ProbabilityTheory Filter Topology
open CC.Bridge

set_option warn.classDefReducibility false

/-- The equilibrium action `a_t` under the alternative selection with shift `c`. -/
noncomputable def eqActAlt (κ c : ℝ) (S₁ : M2) (G : Measure ℝ) (t : ℕ) (ω : Ωg) : ℝ :=
  haveI := Classical.propDecidable (rev κ S₁ t ω)
  let S := Sig κ S₁ ω t
  let γ := gam ω t
  let mθ := postTheta κ S₁ G t ω
  let mμ := postMu κ S₁ G t ω
  let l := (1 + √(1 - 4 * κ * sens S γ ^ 2)) / 2
  if rev κ S₁ t ω then
    γ * mθ + mμ + l * (obs κ S₁ t ω - (loadA S γ 0 * mθ + loadA S γ 1 * mμ)) +
      κ * (sens S γ / l) * c
  else γ * mθ + mμ

/-- σ-algebra of the public history `h^t = (γ_0, a_0, …, a_{t-1}, γ_t)` under the alternative
selection with shift `c`. -/
noncomputable def histSigmaAlt (κ c : ℝ) (S₁ : M2) (G : Measure ℝ) (t : ℕ) :
    MeasurableSpace Ωg :=
  MeasurableSpace.comap
    (fun ω => ((fun i : Fin (t + 1) => gam ω i), (fun i : Fin t => eqActAlt κ c S₁ G i ω)))
    inferInstance

/-- Posterior mean `θ(h^t)` given the public history under the alternative selection. -/
noncomputable def postThetaAlt (κ c : ℝ) (S₁ : M2) (G : Measure ℝ) (t : ℕ) : Ωg → ℝ :=
  (lawG S₁ G)[thetaV | histSigmaAlt κ c S₁ G t]

/-- Posterior mean `μ(h^t)` given the public history under the alternative selection. -/
noncomputable def postMuAlt (κ c : ℝ) (S₁ : M2) (G : Measure ℝ) (t : ℕ) : Ωg → ℝ :=
  (lawG S₁ G)[muV | histSigmaAlt κ c S₁ G t]

/-! ### The public history under the alternative selection -/

section Hist

variable (κ c : ℝ) (S₁ : M2) (G : Measure ℝ)

lemma eqActAlt_eq (t : ℕ) (ω : Ωg) : eqActAlt κ c S₁ G t ω =
    haveI := Classical.propDecidable (rev κ S₁ t ω)
    if rev κ S₁ t ω then
      gam ω t * postTheta κ S₁ G t ω + postMu κ S₁ G t ω +
        lamF κ (SigP κ S₁ (gam ω) t) (gam ω t) * (obs κ S₁ t ω -
          (loadA (SigP κ S₁ (gam ω) t) (gam ω t) 0 * postTheta κ S₁ G t ω +
            loadA (SigP κ S₁ (gam ω) t) (gam ω t) 1 * postMu κ S₁ G t ω)) +
        κ * (sens (SigP κ S₁ (gam ω) t) (gam ω t) / lamF κ (SigP κ S₁ (gam ω) t) (gam ω t)) * c
    else gam ω t * postTheta κ S₁ G t ω + postMu κ S₁ G t ω := rfl

/-- The observation recovered from the action. -/
lemma obs_eq_of_eqActAlt (t : ℕ) (ω : Ωg) : obs κ S₁ t ω =
    haveI := Classical.propDecidable (rev κ S₁ t ω)
    if rev κ S₁ t ω then
      (eqActAlt κ c S₁ G t ω - gam ω t * postTheta κ S₁ G t ω - postMu κ S₁ G t ω -
          κ * (sens (SigP κ S₁ (gam ω) t) (gam ω t) /
            lamF κ (SigP κ S₁ (gam ω) t) (gam ω t)) * c) /
          lamF κ (SigP κ S₁ (gam ω) t) (gam ω t) +
        (loadA (SigP κ S₁ (gam ω) t) (gam ω t) 0 * postTheta κ S₁ G t ω +
            loadA (SigP κ S₁ (gam ω) t) (gam ω t) 1 * postMu κ S₁ G t ω)
    else 0 := by
  rw [eqActAlt_eq]
  by_cases h : rev κ S₁ t ω
  · simp only [h, ite_true]
    have hl := (lamF_pos κ (SigP κ S₁ (gam ω) t) (gam ω t)).ne'
    field_simp
    ring
  · simp only [h, ite_false]
    show obsF κ S₁ (gam ω) ω.1 ω.2.1 t = 0
    exact obsF_pool κ S₁ h

lemma meas_shiftTerm : Measurable (fun p : M2 × ℝ => κ * (sens p.1 p.2 / lamF κ p.1 p.2) * c) := by
  have h1 := br_meas_sens (f := fun p : M2 × ℝ => p.1) (g := fun p => p.2) measurable_fst
    measurable_snd
  exact (measurable_const.mul (h1.div (meas_lamF κ))).mul measurable_const

/-- The action at date `t` is a function of the information at `t + 1`. -/
lemma meas_info_eqActAlt (t : ℕ) : Measurable[infoSigma κ S₁ (t + 1)] (eqActAlt κ c S₁ G t) := by
  have hle := infoSigma_mono κ S₁ (Nat.le_succ t)
  have hθ := (meas_info_postTheta κ S₁ G t).mono hle le_rfl
  have hμ := (meas_info_postMu κ S₁ G t).mono hle le_rfl
  have hγ := meas_info_gam κ S₁ (t := t + 1) (i := t) (Nat.le_succ t)
  have hl := (meas_info_sigfun κ S₁ t (lamF κ) (meas_lamF κ)).mono hle le_rfl
  have h0 := (meas_info_sigfun κ S₁ t (fun S γ => loadA S γ 0) (meas_loadA_pair 0)).mono hle le_rfl
  have h1 := (meas_info_sigfun κ S₁ t (fun S γ => loadA S γ 1) (meas_loadA_pair 1)).mono hle le_rfl
  have hc := (meas_info_sigfun κ S₁ t (fun S γ => κ * (sens S γ / lamF κ S γ) * c)
    (meas_shiftTerm κ c)).mono hle le_rfl
  have ho := meas_info_obs κ S₁ (t := t + 1) (i := t) (Nat.lt_succ_self t)
  have hr : MeasurableSet[infoSigma κ S₁ (t + 1)] {ω | rev κ S₁ t ω} :=
    hle _ (measSet_info_rev κ S₁ t)
  have e : eqActAlt κ c S₁ G t = fun ω => eqActAlt κ c S₁ G t ω := rfl
  rw [e]
  simp_rw [eqActAlt_eq]
  exact br_ite hr (((hγ.mul hθ).add hμ |>.add (hl.mul (ho.sub ((h0.mul hθ).add (h1.mul hμ))))).add hc)
    ((hγ.mul hθ).add hμ)

lemma meas_histAlt_gam {t i : ℕ} (hi : i ≤ t) :
    Measurable[histSigmaAlt κ c S₁ G t] (fun ω => gam ω i) := by
  have h : (fun ω => gam ω i) = (fun q : (Fin (t + 1) → ℝ) × (Fin t → ℝ) =>
      q.1 ⟨i, Nat.lt_succ_of_le hi⟩) ∘
      (fun ω => ((fun i : Fin (t + 1) => gam ω i), (fun i : Fin t => eqActAlt κ c S₁ G i ω))) :=
    rfl
  rw [h]
  exact ((measurable_pi_apply _).comp measurable_fst).comp (comap_measurable _)

lemma meas_histAlt_eqAct {t i : ℕ} (hi : i < t) :
    Measurable[histSigmaAlt κ c S₁ G t] (fun ω => eqActAlt κ c S₁ G i ω) := by
  have h : (fun ω => eqActAlt κ c S₁ G i ω) = (fun q : (Fin (t + 1) → ℝ) × (Fin t → ℝ) =>
      q.2 ⟨i, hi⟩) ∘
      (fun ω => ((fun i : Fin (t + 1) => gam ω i), (fun i : Fin t => eqActAlt κ c S₁ G i ω))) :=
    rfl
  rw [h]
  exact ((measurable_pi_apply _).comp measurable_snd).comp (comap_measurable _)

lemma histSigmaAlt_le_info (t : ℕ) : histSigmaAlt κ c S₁ G t ≤ infoSigma κ S₁ t :=
  Measurable.comap_le ((br_of_eval fun (i : Fin (t + 1)) =>
    meas_info_gam κ S₁ (Nat.lt_succ_iff.1 i.2)).prodMk
    (br_of_eval fun (i : Fin t) => (meas_info_eqActAlt κ c S₁ G i).mono
      (infoSigma_mono κ S₁ (Nat.succ_le_of_lt i.2)) le_rfl))

lemma histSigmaAlt_mono_succ (t : ℕ) :
    histSigmaAlt κ c S₁ G t ≤ histSigmaAlt κ c S₁ G (t + 1) :=
  Measurable.comap_le ((br_of_eval fun (i : Fin (t + 1)) =>
    meas_histAlt_gam κ c S₁ G (Nat.le_succ_of_le (Nat.lt_succ_iff.1 i.2))).prodMk
    (br_of_eval fun (i : Fin t) => meas_histAlt_eqAct κ c S₁ G (Nat.lt_succ_of_lt i.2)))

lemma histSigmaAlt_eq_info (t : ℕ) : histSigmaAlt κ c S₁ G t = infoSigma κ S₁ t := by
  induction t with
  | zero =>
    unfold histSigmaAlt infoSigma
    congr 1
    funext ω
    congr 1
    funext i
    exact i.elim0
  | succ t ih =>
    refine le_antisymm (histSigmaAlt_le_info κ c S₁ G (t + 1)) ?_
    have hI : infoSigma κ S₁ t ≤ histSigmaAlt κ c S₁ G (t + 1) :=
      ih ▸ histSigmaAlt_mono_succ κ c S₁ G t
    have hobs : ∀ i : Fin (t + 1), Measurable[histSigmaAlt κ c S₁ G (t + 1)]
        (fun ω => obs κ S₁ i ω) := by
      intro i
      rcases Nat.lt_succ_iff_lt_or_eq.1 i.2 with hi | hi
      · exact (meas_info_obs κ S₁ hi).mono hI le_rfl
      · have hiv : (i : ℕ) = t := hi
        rw [hiv]
        have hθ := (meas_info_postTheta κ S₁ G t).mono hI le_rfl
        have hμ := (meas_info_postMu κ S₁ G t).mono hI le_rfl
        have hγ := (meas_info_gam κ S₁ (t := t) (i := t) le_rfl).mono hI le_rfl
        have hl := (meas_info_sigfun κ S₁ t (lamF κ) (meas_lamF κ)).mono hI le_rfl
        have h0 := (meas_info_sigfun κ S₁ t (fun S γ => loadA S γ 0)
          (meas_loadA_pair 0)).mono hI le_rfl
        have h1 := (meas_info_sigfun κ S₁ t (fun S γ => loadA S γ 1)
          (meas_loadA_pair 1)).mono hI le_rfl
        have hc := (meas_info_sigfun κ S₁ t (fun S γ => κ * (sens S γ / lamF κ S γ) * c)
          (meas_shiftTerm κ c)).mono hI le_rfl
        have ha := meas_histAlt_eqAct κ c S₁ G (t := t + 1) (i := t) (Nat.lt_succ_self t)
        have hr : MeasurableSet[histSigmaAlt κ c S₁ G (t + 1)] {ω | rev κ S₁ t ω} :=
          hI _ (measSet_info_rev κ S₁ t)
        simp_rw [obs_eq_of_eqActAlt κ c S₁ G t]
        exact br_ite hr (((((ha.sub (hγ.mul hθ)).sub hμ).sub hc).div hl).add
          ((h0.mul hθ).add (h1.mul hμ))) measurable_const
    exact Measurable.comap_le ((br_of_eval fun (i : Fin (t + 1 + 1)) =>
      meas_histAlt_gam κ c S₁ G (Nat.lt_succ_iff.1 i.2)).prodMk (br_of_eval hobs))

end Hist

/-- The public history under the alternative selection carries the same information as the
weights and the observations, hence as the baseline public history. -/
theorem histSigmaAlt_eq (κ c : ℝ) (S₁ : M2) (G : Measure ℝ) (t : ℕ) :
    histSigmaAlt κ c S₁ G t = infoSigma κ S₁ t ∧
      histSigmaAlt κ c S₁ G t = histSigma κ S₁ G t := by
  exact ⟨histSigmaAlt_eq_info κ c S₁ G t,
    (histSigmaAlt_eq_info κ c S₁ G t).trans (histSigma_eq_info κ S₁ G t).symm⟩

/-- **Proposition 2 under the alternative selection (paper's definition of social
learning).** Suppose `Σ₁ ≻ 0` and `γ_t` is i.i.d. with full support on `[0,1]`. For every `c`:
if `κ < κck`, social learning about preferences and fundamentals occurs; if `κ > κck`, it
fails. -/
theorem prop2_socialLearning_alt (S₁ : M2) (hS : S₁.PosDef) (G : Measure ℝ)
    [IsProbabilityMeasure G] (hG : FullSupportUnit G) (κ : ℝ) (hκ : 0 < κ) (c : ℝ) :
    (κ < κck → SLOccurs (lawG S₁ G) thetaV (postThetaAlt κ c S₁ G) ∧
        SLOccurs (lawG S₁ G) muV (postMuAlt κ c S₁ G)) ∧
    (κck < κ → SLFails (lawG S₁ G) thetaV (postThetaAlt κ c S₁ G) ∧
        SLFails (lawG S₁ G) muV (postMuAlt κ c S₁ G)) := by
  have hθ : postThetaAlt κ c S₁ G = postTheta κ S₁ G := by
    funext t
    unfold postThetaAlt postTheta
    rw [(histSigmaAlt_eq κ c S₁ G t).1]
  have hμ : postMuAlt κ c S₁ G = postMu κ S₁ G := by
    funext t
    unfold postMuAlt postMu
    rw [(histSigmaAlt_eq κ c S₁ G t).1]
  rw [hθ, hμ]
  exact prop2_socialLearning S₁ hS G hG κ hκ

end CC.Shifted
