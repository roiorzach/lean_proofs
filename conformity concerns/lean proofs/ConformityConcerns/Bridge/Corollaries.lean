import ConformityConcerns.Bridge.Prop2
import ConformityConcerns.Corollaries.KnownTheta
import ConformityConcerns.Corollaries.KnownMu

/-!
# Corollaries A2 and A3 with the paper's definition of social learning

The primitives are those of `Bridge/Defs.lean`: `(θ, μ) ~ N(0, Σ₁)`, `(ε_t, ν_t)` i.i.d.
`N(0, I)`, weights `γ_t` i.i.d. `~ G`, all independent; play is the signaling equilibrium, and the
posterior means are conditional expectations given the public information (which is the public
history, `histSigma_eq_info`).

* Corollary A2: `θ` known (`Σ₁ = diag(0, σ²_μ)`), any law of the weights.
* Corollary A3: `μ` known (`Σ₁ = diag(σ²_θ, 0)`) and `γ_t = 1`.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology

/-- A diagonal covariance matrix whose diagonal entries tend to `0` tends to `0`. -/
lemma tendsto_diag_zero {f g : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun t => (!![f t, 0; 0, g t] : M2)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa using hf
  · simp
  · simp
  · simpa using hg

/-- Under `∏ δ₁`, almost every weight path is the constant path `1`. -/
lemma ae_eq_one_dirac :
    ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => Measure.dirac (1 : ℝ)), γ = fun _ => 1 := by
  have h : (Measure.infinitePi fun _ : ℕ => Measure.dirac (1 : ℝ)) =
      Measure.dirac (fun _ : ℕ => (1 : ℝ)) := Measure.infinitePi_dirac _
  rw [h, ae_dirac_eq]
  exact Filter.eventually_pure.2 rfl

/-- **Corollary A2 (social learning, paper's definition).** With `θ` known, social learning about
preferences occurs if `κ ≤ κck` and fails if `κ > κck`. -/
theorem corollaryA2_socialLearning (σμ2 : ℝ) (hσ : 0 < σμ2) (G : Measure ℝ)
    [IsProbabilityMeasure G] (κ : ℝ) (hκ : 0 < κ) :
    (κ ≤ κck → SLOccurs (lawG !![0, 0; 0, σμ2] G) muV (postMu κ !![0, 0; 0, σμ2] G)) ∧
    (κck < κ → SLFails (lawG !![0, 0; 0, σμ2] G) muV (postMu κ !![0, 0; 0, σμ2] G)) := by
  set S₁ : M2 := !![0, 0; 0, σμ2] with hS₁def
  have hS : S₁.PosSemidef := psd_diag 0 σμ2 le_rfl hσ.le
  have hseq : ∀ γ t, SigP κ S₁ γ t =
      !![0, 0; 0, if κ ≤ κck then σμ2 / (1 + t * σμ2) else σμ2] := fun γ t => by
    show SigmaC (fun _ => κ) S₁ γ t = _
    rw [← SigmaSeq_eq_SigmaC (fun _ => κ) (fun _ => hκ) S₁ hS γ]
    exact CorA2.seq_eq σμ2 hσ κ hκ γ t
  have hμ : Measurable muV := br_meas_coord measurable_fst 1
  have hpostμ : ∀ n, Measurable (postMu κ S₁ G n) := fun n =>
    (meas_info_postMu κ S₁ G n).mono (infoSigma_le κ S₁ n) le_rfl
  refine ⟨fun hκ' => ?_, fun hκ' => ?_⟩
  · have hlim : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G),
        Tendsto (fun t => SigP κ S₁ γ t) atTop (𝓝 0) := by
      refine ae_of_all _ fun γ => ?_
      refine (tendsto_diag_zero (f := fun _ => 0) tendsto_const_nhds
        (CorA2.tendsto_seq σμ2 hσ)).congr fun t => ?_
      rw [hseq, ite_eq_left hκ']
    exact slOccurs_of_ae hμ hpostμ (occurs_core κ S₁ G hS 1 hlim)
  · have hnot : ¬ κ ≤ κck := not_le.2 hκ'
    have hdiag : ∀ γ t, 0 < SigP κ S₁ γ t 1 1 := fun γ t => by
      rw [hseq, ite_eq_right hnot]; simpa using hσ
    have hfin : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G),
        ∃ T, ∀ t, T ≤ t → ¬ revP κ S₁ γ t := by
      refine ae_of_all _ fun γ => ⟨0, fun t _ => ?_⟩
      show ¬ revCrit κ (SigP κ S₁ γ t) (γ t)
      rw [hseq, ite_eq_right hnot, revCrit, CorA2.sens_eq_one _ _ hσ.le, one_pow, mul_one]
      exact hnot
    have hlev : ∀ᵐ ω ∂(lawG S₁ G),
        Tendsto (fun n => (lawG S₁ G)[fun ω => ω.1 1 | infoSigma κ S₁ n] ω) atTop
          (𝓝 ((lawG S₁ G)[fun ω => ω.1 1 | ⨆ n, infoSigma κ S₁ n] ω)) :=
      tendsto_ae_condExp (ℱ := infoFilt κ S₁) _
    exact slFails_of hμ hlev (fails_core κ S₁ G hS 1 hdiag hfin)

/-- **Corollary A3 (social learning, paper's definition).** With `μ` known and `γ_t = 1`, social
learning about fundamentals occurs if `κ ≤ κck` and fails if `κ > κck`. -/
theorem corollaryA3_socialLearning (σθ2 : ℝ) (hσ : 0 < σθ2) (κ : ℝ) (hκ : 0 < κ) :
    (κ ≤ κck → SLOccurs (lawG !![σθ2, 0; 0, 0] (Measure.dirac 1)) thetaV
      (postTheta κ !![σθ2, 0; 0, 0] (Measure.dirac 1))) ∧
    (κck < κ → SLFails (lawG !![σθ2, 0; 0, 0] (Measure.dirac 1)) thetaV
      (postTheta κ !![σθ2, 0; 0, 0] (Measure.dirac 1))) := by
  set S₁ : M2 := !![σθ2, 0; 0, 0] with hS₁def
  have hS : S₁.PosSemidef := psd_diag σθ2 0 hσ.le le_rfl
  have hseq : ∀ t, SigP κ S₁ (fun _ => 1) t = !![(CorA3.stepA κ)^[t] σθ2, 0; 0, 0] := fun t => by
    show SigmaC (fun _ => κ) S₁ (fun _ => 1) t = _
    rw [← SigmaSeq_eq_SigmaC (fun _ => κ) (fun _ => hκ) S₁ hS (fun _ => 1)]
    exact CorA3.seq_eq σθ2 hσ κ hκ t
  have hθ : Measurable thetaV := br_meas_coord measurable_fst 0
  have hpostθ : ∀ n, Measurable (postTheta κ S₁ (Measure.dirac 1) n) := fun n =>
    (meas_info_postTheta κ S₁ _ n).mono (infoSigma_le κ S₁ n) le_rfl
  refine ⟨fun hκ' => ?_, fun hκ' => ?_⟩
  · have hlim : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => Measure.dirac (1 : ℝ)),
        Tendsto (fun t => SigP κ S₁ γ t) atTop (𝓝 0) := by
      filter_upwards [ae_eq_one_dirac] with γ hγ
      subst hγ
      have h1 : Tendsto (fun t => (CorA3.stepA κ)^[t] σθ2) atTop (𝓝 0) :=
        (CorA3.tendsto_iterate_fA σθ2 hσ.le).congr fun t =>
          (CorA3.iterate_stepA_of_le κ hκ hκ' σθ2 hσ.le t).symm
      exact (tendsto_diag_zero (g := fun _ => 0) h1 tendsto_const_nhds).congr fun t =>
        (hseq t).symm
    exact slOccurs_of_ae hθ hpostθ (occurs_core κ S₁ _ hS 0 hlim)
  · have hdiag : ∀ γ t, 0 < SigP κ S₁ γ t 0 0 := fun γ t =>
      SigmaC_diag_pos _ γ S₁ hS t 0 (by simpa [hS₁def] using hσ)
    have hfin : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => Measure.dirac (1 : ℝ)),
        ∃ T, ∀ t, T ≤ t → ¬ revP κ S₁ γ t := by
      filter_upwards [ae_eq_one_dirac] with γ hγ
      subst hγ
      obtain ⟨T, hT⟩ := CorA3.eventually_pool σθ2 hσ κ hκ'
      refine ⟨T, fun t ht => ?_⟩
      show ¬ revCrit κ (SigP κ S₁ (fun _ => 1) t) 1
      rw [hseq, revCrit, CorA3.sens_eq _ (CorA3.iterate_stepA_pos κ σθ2 hσ t).le]
      exact (hT t ht).1
    have hlev : ∀ᵐ ω ∂(lawG S₁ (Measure.dirac 1)),
        Tendsto (fun n => (lawG S₁ (Measure.dirac 1))[fun ω => ω.1 0 | infoSigma κ S₁ n] ω)
          atTop (𝓝 ((lawG S₁ (Measure.dirac 1))[fun ω => ω.1 0 | ⨆ n, infoSigma κ S₁ n] ω)) :=
      tendsto_ae_condExp (ℱ := infoFilt κ S₁) _
    exact slFails_of hθ hlev (fails_core κ S₁ _ hS 0 hdiag hfin)

end CC.Bridge
