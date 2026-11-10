import ConformityConcerns.BridgeK.Hist
import ConformityConcerns.BridgeK.Fails
import ConformityConcerns.BridgeK.SL
import ConformityConcerns.BridgeK.Cov
import ConformityConcerns.Dynamics.LongRun
import ConformityConcerns.Dynamics.LemmasProb
import ConformityConcerns.Interventions.DiagFacts
import ConformityConcerns.Corollaries.KnownTheta

/-!
# Proposition 3 (1) (Fragility) with the paper's definition of social learning

Constant conformity concern `κ > κck` (`κ_t ~ δ_κ`), `Σ₁ ≻ 0`, `γ_t` i.i.d. with full support on
`[0,1]`. An intervention at an arbitrary date `τ` publicly discloses, after `a_{τ-1}` and before
`a_τ`, the signal `θ + √n ξ` (individual-oriented, `individualAt τ n`) or `μ + √n ξ`
(peer-oriented, `peerAt τ n`), with `ξ ~ N(0,1)` independent of everything else. The paper's
signal "distributed identically to `s_t`" (resp. `v_t`) is `n = 1`; any `n ≥ 0` is allowed
(`n = 0`: perfect revelation). From date `τ` on the signal is part of the public history and play
is the signaling equilibrium given the current public beliefs.
-/

namespace CC.BridgeK

open MeasureTheory Set Filter Topology

set_option warn.classDefReducibility false

lemma SigK_eq_SigPre_of_none (S₁ : M2) {D : Sched} (w : ℕ → ℝ × ℝ) {t : ℕ} (h : D t = none) :
    SigK S₁ D w t = SigPre S₁ D w t := by
  unfold SigK; rw [h]; rfl

/-- The core of Proposition 3 (1): after a disclosure about coordinate `i` at date `τ`, if the
disclosure keeps a positive posterior variance of coordinate `j`, social learning about `x_j`
fails (with posterior means given `infoSigmaK`). -/
lemma prop3_core (κ : ℝ) (hκ : κck < κ) (S₁ : M2) (hS : S₁.PosSemidef)
    (Gγ : Measure ℝ) [IsProbabilityMeasure Gγ] (hGγ : FullSupportUnit Gγ)
    (τ : ℕ) (n : ℝ) (hn : 0 ≤ n) (i j : Fin 2)
    (hdisc : ∀ κs γs : ℕ → ℝ, (discCov (some (i, n)) (SigmaC κs S₁ γs τ)).PosSemidef ∧
      0 < discCov (some (i, n)) (SigmaC κs S₁ γs τ) j j) :
    SLFails (lawK S₁ (Measure.dirac κ) Gγ) (fun ω => ω.1 j)
      (fun m => (lawK S₁ (Measure.dirac κ) Gγ)[fun ω => ω.1 j |
        infoSigmaK S₁ (interventionAt τ i n) m]) := by
  set D := interventionAt τ i n with hDdef
  set μw := (Measure.dirac κ).prod Gγ with hμw
  have hD : SchedOK D := schedOK_interventionAt τ i hn
  have hfst : ∀ A : Set ℝ, μw (Prod.fst ⁻¹' A) = Measure.dirac κ A := fun A => by
    rw [← Set.prod_univ, hμw, Measure.prod_prod, measure_univ, mul_one]
  have hsnd : ∀ A : Set ℝ, μw (Prod.snd ⁻¹' A) = Gγ A := fun A => by
    rw [← Set.univ_prod, hμw, Measure.prod_prod, measure_univ, one_mul]
  have hγae : ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => μw), ∀ t, (w t).2 ∈ Icc (0 : ℝ) 1 :=
    ae_forall_mem μw (s := Prod.snd ⁻¹' Icc 0 1) (measurable_snd measurableSet_Icc)
      (by rw [← preimage_compl, hsnd, hGγ.supp])
  have hκae : ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => μw), ∀ t, (w t).1 ∈ ({κ} : Set ℝ) :=
    ae_forall_mem μw (s := Prod.fst ⁻¹' {κ}) (measurable_fst (measurableSet_singleton κ))
      (by rw [← preimage_compl, hfst, Measure.dirac_apply' _ (measurableSet_singleton κ).compl]
          simp)
  have hfin : ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => μw), ∃ K,
      (∀ k, K ≤ k → ld S₁ D w k = (0, 0)) ∧ 0 < Cs S₁ D w K j j := by
    filter_upwards [hκae, hγae] with w hκw hγw
    set S0 := SigK S₁ D w τ with hS0def
    have hS0 : S0 = discCov (some (i, n))
        (SigmaC (fun s => (w s).1) S₁ (fun s => (w s).2) τ) := by
      rw [hS0def]
      unfold SigK
      rw [SigPre_interventionAt_le S₁ w τ i n le_rfl]
      simp [hDdef, interventionAt]
    obtain ⟨hpsd0, hpos0⟩ := hdisc (fun s => (w s).1) (fun s => (w s).2)
    rw [← hS0] at hpsd0 hpos0
    set γ' : ℕ → ℝ := fun s => (w (τ + s)).2 with hγ'
    have hκ' : (fun s => (w (τ + s)).1) = fun _ => κ := funext fun s => hκw (τ + s)
    have hafter : ∀ t, SigK S₁ D w (τ + t) = SigmaC (fun _ => κ) S0 γ' t := by
      intro t
      rw [hDdef, SigK_interventionAt_after S₁ w τ i n t, ← hκ']
    -- Corollary A2 when the disclosure leaves zero variance about `θ`; otherwise the first step of
    -- Case 1 of Proposition 2, which does not use `Σ₁ ≻ 0`
    obtain ⟨T, hT⟩ : ∃ T, ∀ t, T ≤ t → ¬ revCrit κ (SigmaC (fun _ => κ) S0 γ' t) (γ' t) ∧
        SigmaC (fun _ => κ) S0 γ' t = SigmaC (fun _ => κ) S0 γ' T := by
      by_cases h0 : S0 0 0 = 0
      · refine ⟨0, fun t _ => ?_⟩
        obtain ⟨h1, h2⟩ := CorA2.pool_of_theta_known hκ hpsd0 h0 γ' t
        exact ⟨h1, by rw [h2]; rfl⟩
      · exact prop2_high_core κ hκ S0 hpsd0 γ' (fun s => hγw (τ + s))
    have hnone : ∀ s, τ < s → D s = none := fun s hs => by
      simp only [hDdef, interventionAt]; rw [ite_eq_right (by omega)]
    refine ⟨2 * (τ + T + 1), fun k hk => ?_, ?_⟩
    · obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [ld_even, hnone s (by omega)]; rfl
      · rw [ld_odd]
        unfold ldA
        have hs : s = τ + (s - τ) := by omega
        have hn' : ¬ revCrit (w s).1 (SigK S₁ D w s) (w s).2 := by
          rw [hs, hafter (s - τ), hκw (τ + (s - τ))]
          exact (hT (s - τ) (by omega)).1
        rw [ite_eq_right hn']
    · rw [Cs_even, ← SigK_eq_SigPre_of_none S₁ w (hnone _ (by omega)),
        show τ + T + 1 = τ + (T + 1) by ring, hafter]
      exact SigmaC_diag_pos _ γ' S0 hpsd0 (T + 1) j hpos0
  have hX : Measurable (fun ω : Ωk => ω.1 j) := Bridge.br_meas_coord measurable_fst j
  exact slFails_of hX (tendsto_ae_condExp (ℱ := infoFiltK S₁ D) _)
    (fails_coreK S₁ D (Measure.dirac κ) Gγ hS hD j hfin)

/-- **Proposition 3 (1) (paper's definition of social learning).** When `κ > κck`, after an
individual-oriented intervention at any date `τ` social learning about preferences fails, and
after a peer-oriented intervention at any date `τ` social learning about fundamentals fails. -/
theorem prop3_1_socialLearning (κ : ℝ) (hκ : κck < κ) (S₁ : M2) (hS : S₁.PosDef)
    (Gγ : Measure ℝ) [IsProbabilityMeasure Gγ] (hGγ : FullSupportUnit Gγ)
    (τ : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    SLFails (lawK S₁ (Measure.dirac κ) Gγ) muV
        (postMuK S₁ (Measure.dirac κ) Gγ (individualAt τ n)) ∧
      SLFails (lawK S₁ (Measure.dirac κ) Gγ) thetaV
        (postThetaK S₁ (Measure.dirac κ) Gγ (peerAt τ n)) := by
  have h1 := prop3_core κ hκ S₁ hS.posSemidef Gγ hGγ τ n hn 0 1 (fun κs γs => by
    simpa [discCov] using observeTheta_props (SigmaC_pd κs γs S₁ hS τ) hn)
  have h2 := prop3_core κ hκ S₁ hS.posSemidef Gγ hGγ τ n hn 1 0 (fun κs γs => by
    simpa [discCov] using observeMu_props (SigmaC_pd κs γs S₁ hS τ) hn)
  have e1 : postMuK S₁ (Measure.dirac κ) Gγ (individualAt τ n) = fun m =>
      (lawK S₁ (Measure.dirac κ) Gγ)[fun ω => ω.1 1 | infoSigmaK S₁ (interventionAt τ 0 n) m] :=
    funext fun m => postMuK_eq _ _ _ _ m
  have e2 : postThetaK S₁ (Measure.dirac κ) Gγ (peerAt τ n) = fun m =>
      (lawK S₁ (Measure.dirac κ) Gγ)[fun ω => ω.1 0 | infoSigmaK S₁ (interventionAt τ 1 n) m] :=
    funext fun m => postThetaK_eq _ _ _ _ m
  rw [e1, e2]
  exact ⟨h1, h2⟩

/-- **Proposition 3 (1), as worded in the paper.** When `κ > κck`, an individual-oriented
intervention (respectively, peer-oriented intervention) never results in social learning about
`μ` (respectively, `θ`). -/
theorem prop3_1_never (κ : ℝ) (hκ : κck < κ) (S₁ : M2) (hS : S₁.PosDef)
    (Gγ : Measure ℝ) [IsProbabilityMeasure Gγ] (hGγ : FullSupportUnit Gγ)
    (τ : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    ¬ SLOccurs (lawK S₁ (Measure.dirac κ) Gγ) muV
        (postMuK S₁ (Measure.dirac κ) Gγ (individualAt τ n)) ∧
      ¬ SLOccurs (lawK S₁ (Measure.dirac κ) Gγ) thetaV
        (postThetaK S₁ (Measure.dirac κ) Gγ (peerAt τ n)) := by
  obtain ⟨h1, h2⟩ := prop3_1_socialLearning κ hκ S₁ hS Gγ hGγ τ n hn
  exact ⟨not_slOccurs_of_slFails (Bridge.br_meas_coord measurable_fst 1) h1,
    not_slOccurs_of_slFails (Bridge.br_meas_coord measurable_fst 0) h2⟩

end CC.BridgeK
