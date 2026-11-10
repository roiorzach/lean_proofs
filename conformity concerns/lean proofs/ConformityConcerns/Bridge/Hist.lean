import ConformityConcerns.Bridge.Info

/-!
# The public history generates the same information as the weights and the observations

`histSigma t = infoSigma t`: the equilibrium action at a revealing date is an affine function of
the observation with `infoSigma t`-measurable coefficients and slope `λ_t ≥ 1/2`, and at a pooling
date it is `infoSigma t`-measurable.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix

set_option warn.classDefReducibility false

lemma br_ite {α : Type*} {m : MeasurableSpace α} {p : α → Prop} {f g : α → ℝ}
    (hp : MeasurableSet[m] {x | p x}) (hf : Measurable[m] f) (hg : Measurable[m] g) :
    Measurable[m] (fun x => haveI := Classical.propDecidable (p x); if p x then f x else g x) := by
  let _ := m
  classical
  exact Measurable.ite hp hf hg

variable (κ : ℝ) (S₁ : M2) (G : Measure ℝ)

/-- The slope `λ_t = (1 + √(1 - 4 κ s̃²))/2` of the action on `Z_t`. -/
noncomputable def lamF (S : M2) (γ : ℝ) : ℝ := (1 + √(1 - 4 * κ * sens S γ ^ 2)) / 2

lemma lamF_pos (S : M2) (γ : ℝ) : 0 < lamF κ S γ := by
  unfold lamF; positivity

lemma eqAct_eq (t : ℕ) (ω : Ωg) : eqAct κ S₁ G t ω =
    haveI := Classical.propDecidable (rev κ S₁ t ω)
    if rev κ S₁ t ω then
      gam ω t * postTheta κ S₁ G t ω + postMu κ S₁ G t ω +
        lamF κ (SigP κ S₁ (gam ω) t) (gam ω t) * (obs κ S₁ t ω -
          (loadA (SigP κ S₁ (gam ω) t) (gam ω t) 0 * postTheta κ S₁ G t ω +
            loadA (SigP κ S₁ (gam ω) t) (gam ω t) 1 * postMu κ S₁ G t ω))
    else gam ω t * postTheta κ S₁ G t ω + postMu κ S₁ G t ω := rfl

/-- The observation recovered from the action. -/
lemma obs_eq_of_eqAct (t : ℕ) (ω : Ωg) : obs κ S₁ t ω =
    haveI := Classical.propDecidable (rev κ S₁ t ω)
    if rev κ S₁ t ω then
      (eqAct κ S₁ G t ω - gam ω t * postTheta κ S₁ G t ω - postMu κ S₁ G t ω) /
          lamF κ (SigP κ S₁ (gam ω) t) (gam ω t) +
        (loadA (SigP κ S₁ (gam ω) t) (gam ω t) 0 * postTheta κ S₁ G t ω +
            loadA (SigP κ S₁ (gam ω) t) (gam ω t) 1 * postMu κ S₁ G t ω)
    else 0 := by
  rw [eqAct_eq]
  by_cases h : rev κ S₁ t ω
  · simp only [h, ite_true]
    have hl := (lamF_pos κ (SigP κ S₁ (gam ω) t) (gam ω t)).ne'
    field_simp
    ring
  · simp only [h, ite_false]
    show obsF κ S₁ (gam ω) ω.1 ω.2.1 t = 0
    exact obsF_pool κ S₁ h

lemma meas_info_postTheta (t : ℕ) :
    Measurable[infoSigma κ S₁ t] (postTheta κ S₁ G t) :=
  stronglyMeasurable_condExp.measurable

lemma meas_info_postMu (t : ℕ) :
    Measurable[infoSigma κ S₁ t] (postMu κ S₁ G t) :=
  stronglyMeasurable_condExp.measurable

lemma meas_info_sigfun (t : ℕ) (F : M2 → ℝ → ℝ) (hF : Measurable (fun p : M2 × ℝ => F p.1 p.2)) :
    Measurable[infoSigma κ S₁ t] (fun ω => F (SigP κ S₁ (gam ω) t) (gam ω t)) :=
  meas_info_of_dep κ S₁ t (fun p => F (SigP κ S₁ p.1 t) (p.1 t))
    (hF.comp (((measurable_SigP κ S₁ t).comp measurable_fst).prodMk
      ((measurable_pi_apply t).comp measurable_fst)))
    (fun _ _ _ _ h1 _ => by
      simp only
      rw [SigP_congr κ S₁ (fun s hs => h1 s hs.le), h1 t le_rfl])

lemma meas_lamF : Measurable (fun p : M2 × ℝ => lamF κ p.1 p.2) := by
  have h := br_meas_sens (f := fun p : M2 × ℝ => p.1) (g := fun p => p.2) measurable_fst
    measurable_snd
  unfold lamF
  fun_prop

lemma meas_loadA_pair (i : Fin 2) : Measurable (fun p : M2 × ℝ => loadA p.1 p.2 i) :=
  br_meas_loadA (f := fun p : M2 × ℝ => p.1) (g := fun p => p.2) measurable_fst measurable_snd i

/-- The action at date `t` is a function of the information at `t + 1`. -/
lemma meas_info_eqAct (t : ℕ) : Measurable[infoSigma κ S₁ (t + 1)] (eqAct κ S₁ G t) := by
  have hle := infoSigma_mono κ S₁ (Nat.le_succ t)
  have hθ := (meas_info_postTheta κ S₁ G t).mono hle le_rfl
  have hμ := (meas_info_postMu κ S₁ G t).mono hle le_rfl
  have hγ := meas_info_gam κ S₁ (t := t + 1) (i := t) (Nat.le_succ t)
  have hl := (meas_info_sigfun κ S₁ t (lamF κ) (meas_lamF κ)).mono hle le_rfl
  have h0 := (meas_info_sigfun κ S₁ t (fun S γ => loadA S γ 0) (meas_loadA_pair 0)).mono hle le_rfl
  have h1 := (meas_info_sigfun κ S₁ t (fun S γ => loadA S γ 1) (meas_loadA_pair 1)).mono hle le_rfl
  have ho := meas_info_obs κ S₁ (t := t + 1) (i := t) (Nat.lt_succ_self t)
  have hr : MeasurableSet[infoSigma κ S₁ (t + 1)] {ω | rev κ S₁ t ω} :=
    hle _ (measSet_info_rev κ S₁ t)
  have e : eqAct κ S₁ G t = fun ω => eqAct κ S₁ G t ω := rfl
  rw [e]
  simp_rw [eqAct_eq]
  exact br_ite hr ((hγ.mul hθ).add hμ |>.add (hl.mul (ho.sub ((h0.mul hθ).add (h1.mul hμ)))))
    ((hγ.mul hθ).add hμ)

lemma meas_hist_gam {t i : ℕ} (hi : i ≤ t) :
    Measurable[histSigma κ S₁ G t] (fun ω => gam ω i) := by
  have h : (fun ω => gam ω i) = (fun q : (Fin (t + 1) → ℝ) × (Fin t → ℝ) =>
      q.1 ⟨i, Nat.lt_succ_of_le hi⟩) ∘
      (fun ω => ((fun i : Fin (t + 1) => gam ω i), (fun i : Fin t => eqAct κ S₁ G i ω))) := rfl
  rw [h]
  exact ((measurable_pi_apply _).comp measurable_fst).comp (comap_measurable _)

lemma meas_hist_eqAct {t i : ℕ} (hi : i < t) :
    Measurable[histSigma κ S₁ G t] (fun ω => eqAct κ S₁ G i ω) := by
  have h : (fun ω => eqAct κ S₁ G i ω) = (fun q : (Fin (t + 1) → ℝ) × (Fin t → ℝ) =>
      q.2 ⟨i, hi⟩) ∘
      (fun ω => ((fun i : Fin (t + 1) => gam ω i), (fun i : Fin t => eqAct κ S₁ G i ω))) := rfl
  rw [h]
  exact ((measurable_pi_apply _).comp measurable_snd).comp (comap_measurable _)

lemma histSigma_le_info (t : ℕ) : histSigma κ S₁ G t ≤ infoSigma κ S₁ t :=
  Measurable.comap_le ((br_of_eval fun (i : Fin (t + 1)) =>
    meas_info_gam κ S₁ (Nat.lt_succ_iff.1 i.2)).prodMk
    (br_of_eval fun (i : Fin t) => (meas_info_eqAct κ S₁ G i).mono
      (infoSigma_mono κ S₁ (Nat.succ_le_of_lt i.2)) le_rfl))

lemma histSigma_mono_succ (t : ℕ) : histSigma κ S₁ G t ≤ histSigma κ S₁ G (t + 1) :=
  Measurable.comap_le ((br_of_eval fun (i : Fin (t + 1)) =>
    meas_hist_gam κ S₁ G (Nat.le_succ_of_le (Nat.lt_succ_iff.1 i.2))).prodMk
    (br_of_eval fun (i : Fin t) => meas_hist_eqAct κ S₁ G (Nat.lt_succ_of_lt i.2)))

theorem histSigma_eq_info (t : ℕ) : histSigma κ S₁ G t = infoSigma κ S₁ t := by
  induction t with
  | zero =>
    unfold histSigma infoSigma
    congr 1
    funext ω
    congr 1
    funext i
    exact i.elim0
  | succ t ih =>
    refine le_antisymm (histSigma_le_info κ S₁ G (t + 1)) ?_
    have hI : infoSigma κ S₁ t ≤ histSigma κ S₁ G (t + 1) :=
      ih ▸ histSigma_mono_succ κ S₁ G t
    have hobs : ∀ i : Fin (t + 1), Measurable[histSigma κ S₁ G (t + 1)]
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
        have ha := meas_hist_eqAct κ S₁ G (t := t + 1) (i := t) (Nat.lt_succ_self t)
        have hr : MeasurableSet[histSigma κ S₁ G (t + 1)] {ω | rev κ S₁ t ω} :=
          hI _ (measSet_info_rev κ S₁ t)
        simp_rw [obs_eq_of_eqAct κ S₁ G t]
        exact br_ite hr ((((ha.sub (hγ.mul hθ)).sub hμ).div hl).add
          ((h0.mul hθ).add (h1.mul hμ))) measurable_const
    exact Measurable.comap_le ((br_of_eval fun (i : Fin (t + 1 + 1)) =>
      meas_hist_gam κ S₁ G (Nat.lt_succ_iff.1 i.2)).prodMk (br_of_eval hobs))

end CC.Bridge
