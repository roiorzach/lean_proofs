import ConformityConcerns.BridgeK.HistAux

/-!
# The public history generates the same information as the weights, the disclosures and the
observations

`histSigmaK t = infoSigmaK t`: the equilibrium action at a revealing date is an affine function of
the observation with `infoSigmaK t`-measurable coefficients and slope `λ_t ≥ 1/2`, and at a
pooling date it is `infoSigmaK t`-measurable (as in `Bridge/Hist.lean`). Hence the posterior means
used inside `eqActK` are the posterior means given the public history.
-/

namespace CC.BridgeK

open MeasureTheory

/-- The public history generates the same σ-algebra as the weights, the disclosures and the
informative parts of past actions. -/
theorem histSigmaK_eq_info (S₁ : M2) (G Gγ : Measure ℝ) (D : Sched) (t : ℕ) :
    histSigmaK S₁ G Gγ D t = infoSigmaK S₁ D t := by
  induction t with
  | zero =>
    unfold histSigmaK infoSigmaK
    congr 1
    funext ω
    simp only [Prod.mk.injEq, true_and]
    funext i
    exact i.elim0
  | succ t ih =>
    refine le_antisymm (histSigmaK_le_info S₁ G Gγ D (t + 1)) ?_
    have hI : infoSigmaK S₁ D t ≤ histSigmaK S₁ G Gγ D (t + 1) :=
      ih ▸ histSigmaK_mono_succ S₁ G Gγ D t
    have hobs : ∀ i : Fin (t + 1), Measurable[histSigmaK S₁ G Gγ D (t + 1)]
        (fun ω => obsK S₁ D i ω) := by
      intro i
      rcases Nat.lt_succ_iff_lt_or_eq.1 i.2 with hi | hi
      · exact (meas_info_obsK S₁ D hi).mono hI le_rfl
      · have hiv : (i : ℕ) = t := hi
        rw [hiv]
        have hθ := (meas_info_postThetaI S₁ G Gγ D t).mono hI le_rfl
        have hμ := (meas_info_postMuI S₁ G Gγ D t).mono hI le_rfl
        have hγ := (meas_info_gam S₁ D (t := t) (i := t) le_rfl).mono hI le_rfl
        have hl := (meas_info_lam S₁ D t).mono hI le_rfl
        have h0 := (meas_info_loadA S₁ D t 0).mono hI le_rfl
        have h1 := (meas_info_loadA S₁ D t 1).mono hI le_rfl
        have ha := meas_hist_eqActK S₁ G Gγ D (t := t + 1) (i := t) (Nat.lt_succ_self t)
        have hr : MeasurableSet[histSigmaK S₁ G Gγ D (t + 1)] {ω | revK S₁ D t ω} :=
          hI _ (measSet_info_revK S₁ D t)
        simp_rw [obsK_eq_of_eqActK S₁ G Gγ D t]
        exact k_ite hr ((((ha.sub (hγ.mul hθ)).sub hμ).div hl).add
          ((h0.mul hθ).add (h1.mul hμ))) measurable_const
    exact Measurable.comap_le ((k_of_eval fun (i : Fin (t + 1 + 1)) =>
      meas_hist_wts S₁ G Gγ D (Nat.lt_succ_iff.1 i.2)).prodMk
      ((k_of_eval fun (i : Fin (t + 1 + 1)) =>
        meas_hist_discVal S₁ G Gγ D (Nat.lt_succ_iff.1 i.2)).prodMk (k_of_eval hobs)))

/-- `θ(h^t)` is the posterior mean used inside the equilibrium actions. -/
theorem postThetaK_eq (S₁ : M2) (G Gγ : Measure ℝ) (D : Sched) (t : ℕ) :
    postThetaK S₁ G Gγ D t = postThetaI S₁ G Gγ D t := by
  unfold postThetaK postThetaI
  rw [histSigmaK_eq_info]

/-- `μ(h^t)` is the posterior mean used inside the equilibrium actions. -/
theorem postMuK_eq (S₁ : M2) (G Gγ : Measure ℝ) (D : Sched) (t : ℕ) :
    postMuK S₁ G Gγ D t = postMuI S₁ G Gγ D t := by
  unfold postMuK postMuI
  rw [histSigmaK_eq_info]

end CC.BridgeK
