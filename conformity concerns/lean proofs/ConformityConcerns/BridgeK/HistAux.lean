import ConformityConcerns.BridgeK.Info

/-!
# Auxiliary lemmas for `histSigmaK = infoSigmaK`

The equilibrium action at date `t` is `infoSigmaK (t + 1)`-measurable, and the observation at date
`t` is recovered from the action and `infoSigmaK t`-measurable quantities (the slope
`λ_t ≥ 1/2` is positive).
-/

namespace CC.BridgeK

open MeasureTheory

set_option warn.classDefReducibility false

lemma k_ite {α : Type*} {m : MeasurableSpace α} {p : α → Prop} {f g : α → ℝ}
    (hp : MeasurableSet[m] {x | p x}) (hf : Measurable[m] f) (hg : Measurable[m] g) :
    Measurable[m] (fun x => haveI := Classical.propDecidable (p x); if p x then f x else g x) := by
  let _ := m
  classical
  exact Measurable.ite hp hf hg

/-- The slope `λ = (1 + √(1 - 4 κ s̃²))/2` of the action on `Z_t`. -/
noncomputable def lamK (κ : ℝ) (S : M2) (γ : ℝ) : ℝ := (1 + √(1 - 4 * κ * sens S γ ^ 2)) / 2

lemma lamK_pos (κ : ℝ) (S : M2) (γ : ℝ) : 0 < lamK κ S γ := by
  unfold lamK; positivity

variable (S₁ : M2) (G Gγ : Measure ℝ) (D : Sched)

lemma eqActK_eq (t : ℕ) (ω : Ωk) : eqActK S₁ G Gγ D t ω =
    haveI := Classical.propDecidable (revK S₁ D t ω)
    if revK S₁ D t ω then
      gam ω t * postThetaI S₁ G Gγ D t ω + postMuI S₁ G Gγ D t ω +
        lamK (kap ω t) (SigK S₁ D (wts ω) t) (gam ω t) * (obsK S₁ D t ω -
          (loadA (SigK S₁ D (wts ω) t) (gam ω t) 0 * postThetaI S₁ G Gγ D t ω +
            loadA (SigK S₁ D (wts ω) t) (gam ω t) 1 * postMuI S₁ G Gγ D t ω))
    else gam ω t * postThetaI S₁ G Gγ D t ω + postMuI S₁ G Gγ D t ω := rfl

/-- The observation recovered from the action. -/
lemma obsK_eq_of_eqActK (t : ℕ) (ω : Ωk) : obsK S₁ D t ω =
    haveI := Classical.propDecidable (revK S₁ D t ω)
    if revK S₁ D t ω then
      (eqActK S₁ G Gγ D t ω - gam ω t * postThetaI S₁ G Gγ D t ω - postMuI S₁ G Gγ D t ω) /
          lamK (kap ω t) (SigK S₁ D (wts ω) t) (gam ω t) +
        (loadA (SigK S₁ D (wts ω) t) (gam ω t) 0 * postThetaI S₁ G Gγ D t ω +
            loadA (SigK S₁ D (wts ω) t) (gam ω t) 1 * postMuI S₁ G Gγ D t ω)
    else 0 := by
  rw [eqActK_eq]
  by_cases h : revK S₁ D t ω
  · simp only [h, ite_true]
    have hl := (lamK_pos (kap ω t) (SigK S₁ D (wts ω) t) (gam ω t)).ne'
    field_simp
    ring
  · simp only [h, ite_false]
    unfold obsK
    rw [ite_eq_right h]

lemma meas_info_postThetaI (t : ℕ) :
    Measurable[infoSigmaK S₁ D t] (postThetaI S₁ G Gγ D t) :=
  stronglyMeasurable_condExp.measurable

lemma meas_info_postMuI (t : ℕ) :
    Measurable[infoSigmaK S₁ D t] (postMuI S₁ G Gγ D t) :=
  stronglyMeasurable_condExp.measurable

/-- A measurable function of `w_0, …, w_t` is `infoSigmaK t`-measurable. -/
lemma meas_info_wfun (t : ℕ) (F : (ℕ → ℝ × ℝ) → ℝ) (hF : Measurable F)
    (hdep : ∀ w w' : ℕ → ℝ × ℝ, (∀ s ≤ t, w s = w' s) → F w = F w') :
    Measurable[infoSigmaK S₁ D t] (fun ω => F (wts ω)) :=
  meas_info_of_dep S₁ D t (fun p => F p.1) (hF.comp measurable_fst)
    (fun w w' _ _ h _ => hdep w w' h)

lemma measSet_info_revK (t : ℕ) : MeasurableSet[infoSigmaK S₁ D t] {ω | revK S₁ D t ω} := by
  have hm : Measurable (fun p : (ℕ → ℝ × ℝ) × (ℕ → ℝ) => revW S₁ D p.1 t) :=
    measurableSet_setOfPred.1 ((measurableSet_revW S₁ D t).preimage measurable_fst)
  have h := meas_info_of_dep S₁ D t (fun p => revW S₁ D p.1 t) hm
    (fun w w' _ _ h1 _ => propext (revW_congr S₁ D h1))
  have e : {ω | revK S₁ D t ω} = (fun ω => revW S₁ D (wts ω) t) ⁻¹' {True} := by
    ext ω; simp [revK_eq]
  rw [e]
  exact h (measurableSet_singleton _)

lemma meas_lamK_w (t : ℕ) :
    Measurable (fun w : ℕ → ℝ × ℝ => lamK (w t).1 (SigK S₁ D w t) (w t).2) := by
  have hS := measurable_SigK S₁ D t
  have hk : Measurable (fun w : ℕ → ℝ × ℝ => (w t).1) := measurable_fst.comp (measurable_pi_apply t)
  have hg : Measurable (fun w : ℕ → ℝ × ℝ => (w t).2) := measurable_snd.comp (measurable_pi_apply t)
  have h := Bridge.br_meas_sens hS hg
  unfold lamK
  fun_prop

lemma meas_info_lam (t : ℕ) :
    Measurable[infoSigmaK S₁ D t] (fun ω => lamK (kap ω t) (SigK S₁ D (wts ω) t) (gam ω t)) :=
  meas_info_wfun S₁ D t _ (meas_lamK_w S₁ D t) (fun w w' h => by
    rw [SigK_congr S₁ D (fun s hs => h s hs.le), h t le_rfl])

lemma meas_info_loadA (t : ℕ) (j : Fin 2) :
    Measurable[infoSigmaK S₁ D t] (fun ω => loadA (SigK S₁ D (wts ω) t) (gam ω t) j) :=
  meas_info_wfun S₁ D t (fun w => loadA (SigK S₁ D w t) (w t).2 j)
    (Bridge.br_meas_loadA (measurable_SigK S₁ D t) (measurable_snd.comp (measurable_pi_apply t)) j)
    (fun w w' h => by
      rw [SigK_congr S₁ D (fun s hs => h s hs.le), h t le_rfl])

lemma meas_info_gam {t i : ℕ} (hi : i ≤ t) :
    Measurable[infoSigmaK S₁ D t] (fun ω => gam ω i) :=
  meas_info_wfun S₁ D t (fun w => (w i).2) (measurable_snd.comp (measurable_pi_apply i))
    (fun w w' h => by rw [h i hi])

/-- The action at date `t` is a function of the information at `t + 1`. -/
lemma meas_info_eqActK (t : ℕ) : Measurable[infoSigmaK S₁ D (t + 1)] (eqActK S₁ G Gγ D t) := by
  have hle := infoSigmaK_mono S₁ D (Nat.le_succ t)
  have hθ := (meas_info_postThetaI S₁ G Gγ D t).mono hle le_rfl
  have hμ := (meas_info_postMuI S₁ G Gγ D t).mono hle le_rfl
  have hγ := meas_info_gam S₁ D (t := t + 1) (i := t) (Nat.le_succ t)
  have hl := (meas_info_lam S₁ D t).mono hle le_rfl
  have h0 := (meas_info_loadA S₁ D t 0).mono hle le_rfl
  have h1 := (meas_info_loadA S₁ D t 1).mono hle le_rfl
  have ho := meas_info_obsK S₁ D (t := t + 1) (i := t) (Nat.lt_succ_self t)
  have hr : MeasurableSet[infoSigmaK S₁ D (t + 1)] {ω | revK S₁ D t ω} :=
    hle _ (measSet_info_revK S₁ D t)
  have e : eqActK S₁ G Gγ D t = fun ω => eqActK S₁ G Gγ D t ω := rfl
  rw [e]
  simp_rw [eqActK_eq]
  exact k_ite hr ((hγ.mul hθ).add hμ |>.add (hl.mul (ho.sub ((h0.mul hθ).add (h1.mul hμ)))))
    ((hγ.mul hθ).add hμ)

lemma meas_hist_wts {t i : ℕ} (hi : i ≤ t) :
    Measurable[histSigmaK S₁ G Gγ D t] (fun ω => wts ω i) := by
  have h : (fun ω => wts ω i) = (fun q : (Fin (t + 1) → ℝ × ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ) =>
      q.1 ⟨i, Nat.lt_succ_of_le hi⟩) ∘
      (fun ω => ((fun i : Fin (t + 1) => wts ω i), (fun i : Fin (t + 1) => discVal D i ω),
        (fun i : Fin t => eqActK S₁ G Gγ D i ω))) := rfl
  rw [h]
  exact ((measurable_pi_apply _).comp measurable_fst).comp (comap_measurable _)

lemma meas_hist_discVal {t i : ℕ} (hi : i ≤ t) :
    Measurable[histSigmaK S₁ G Gγ D t] (discVal D i) := by
  have h : discVal D i = (fun q : (Fin (t + 1) → ℝ × ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ) =>
      q.2.1 ⟨i, Nat.lt_succ_of_le hi⟩) ∘
      (fun ω => ((fun i : Fin (t + 1) => wts ω i), (fun i : Fin (t + 1) => discVal D i ω),
        (fun i : Fin t => eqActK S₁ G Gγ D i ω))) := rfl
  rw [h]
  exact ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)).comp
    (comap_measurable _)

lemma meas_hist_eqActK {t i : ℕ} (hi : i < t) :
    Measurable[histSigmaK S₁ G Gγ D t] (eqActK S₁ G Gγ D i) := by
  have h : eqActK S₁ G Gγ D i = (fun q : (Fin (t + 1) → ℝ × ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ) =>
      q.2.2 ⟨i, hi⟩) ∘
      (fun ω => ((fun i : Fin (t + 1) => wts ω i), (fun i : Fin (t + 1) => discVal D i ω),
        (fun i : Fin t => eqActK S₁ G Gγ D i ω))) := rfl
  rw [h]
  exact ((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)).comp
    (comap_measurable _)

lemma histSigmaK_le_info (t : ℕ) : histSigmaK S₁ G Gγ D t ≤ infoSigmaK S₁ D t :=
  Measurable.comap_le ((k_of_eval fun (i : Fin (t + 1)) =>
    meas_info_wts S₁ D (Nat.lt_succ_iff.1 i.2)).prodMk
    ((k_of_eval fun (i : Fin (t + 1)) => meas_info_discVal S₁ D (Nat.lt_succ_iff.1 i.2)).prodMk
      (k_of_eval fun (i : Fin t) => (meas_info_eqActK S₁ G Gγ D i).mono
        (infoSigmaK_mono S₁ D (Nat.succ_le_of_lt i.2)) le_rfl)))

lemma histSigmaK_mono_succ (t : ℕ) : histSigmaK S₁ G Gγ D t ≤ histSigmaK S₁ G Gγ D (t + 1) :=
  Measurable.comap_le ((k_of_eval fun (i : Fin (t + 1)) =>
    meas_hist_wts S₁ G Gγ D (Nat.le_succ_of_le (Nat.lt_succ_iff.1 i.2))).prodMk
    ((k_of_eval fun (i : Fin (t + 1)) =>
      meas_hist_discVal S₁ G Gγ D (Nat.le_succ_of_le (Nat.lt_succ_iff.1 i.2))).prodMk
      (k_of_eval fun (i : Fin t) => meas_hist_eqActK S₁ G Gγ D (Nat.lt_succ_of_lt i.2))))

end CC.BridgeK
