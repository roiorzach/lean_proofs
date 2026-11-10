import ConformityConcerns.Learning.Assembly

/-!
# Proposition A4 as stated: no social learning when `κ > κck`

Proposition A4 concludes that an equilibrium satisfying `D1^∞` with social learning about
preferences exists if and only if `κ ≤ κck`. For `κ > κck` this needs only that social learning
does not occur in a fully pooling profile, which holds as soon as `μ` is not almost surely
constant (the paper assumes a positive prior variance). No atomlessness is needed.
-/

namespace CC.Learning

open MeasureTheory ProbabilityTheory Filter Topology
open CC.General

/-- In a profile that pools at every history, social learning about preferences does not occur,
provided `μ` is not almost surely constant. -/
theorem not_learning_pooling (Lμ Lν : Measure ℝ) [IsProbabilityMeasure Lμ]
    [IsProbabilityMeasure Lν] (hnd : ∀ x, Lμ {x} < 1) (c : Profile)
    (hpool : ∀ t (h : Fin t → ℝ) (v w : ℝ), c t h v = c t h w) :
    ¬ SocialLearningOccurs Lμ Lν (postMean (law Lμ Lν) (play c)) := by
  intro hocc
  set P := law Lμ Lν with hPdef
  have hint : ∫ ω, muV ω ∂P = ∫ x, x ∂Lμ := by
    have hmap : P.map Prod.fst = Lμ := by
      rw [hPdef]; unfold law; rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [← hmap, integral_map (f := fun x : ℝ => x) measurable_fst.aemeasurable
      aestronglyMeasurable_id]
    rfl
  have hpm : ∀ t, postMean P (play c) t = fun _ => ∫ x, x ∂Lμ := by
    intro t
    unfold postMean
    rw [histSigma_play_bot c hpool t, condExp_bot, hint]
  have hae : ∀ᵐ m ∂Lμ, m = ∫ x, x ∂Lμ := by
    filter_upwards [hocc] with m hT
    by_contra hm
    have hε : 0 < edist (∫ x, x ∂Lμ) m := edist_pos.2 (Ne.symm hm)
    have := hT _ hε
    simp only [hpm, le_refl, Set.ofPred_true, measure_univ] at this
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)
  have hc : Lμ {∫ x, x ∂Lμ}ᶜ = 0 := by
    rw [ae_iff] at hae
    simpa [Set.compl_def] using hae
  have h1 : Lμ {∫ x, x ∂Lμ} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton _)).1 hc
  exact (hnd _).ne h1

/-- **Proposition A4 (social learning), as stated.** Suppose `μ` is not almost surely constant
(the paper's positive prior variance) and has a finite mean, and `ν_t` has mean zero. If
`κ ≤ κck` there is an equilibrium satisfying `D1^∞` (fully revealing at every history) with
social learning about preferences. If `κ > κck`, every equilibrium satisfying `D1^∞` is fully
pooling at every history and social learning about preferences does not occur. Hence an
equilibrium satisfying `D1^∞` with social learning exists if and only if `κ ≤ κck`. -/
theorem propA4_learning_exact (κ : ℝ) (hκ : 0 < κ) (Lμ Lν : Measure ℝ)
    [IsProbabilityMeasure Lμ] [IsProbabilityMeasure Lν] (hμ : Integrable id Lμ)
    (hnd : ∀ x, Lμ {x} < 1) (hν : Integrable id Lν) (hν0 : ∫ x, x ∂Lν = 0) :
    let P := law Lμ Lν
    (κ ≤ κck → ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
      (∀ S : Setting, S.g = (fun z => z ^ 2) → S.ℓ = (fun b => κ * (b - S.μ) ^ 2) →
        ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
          S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ) ∧
      SocialLearningOccurs Lμ Lν (postMean P (revealAct Φ (fun t => P[muV | typeSigma t])))) ∧
    (κck < κ → ∀ c : Profile,
      (∀ t (h : Fin t → ℝ), ∃ S : Setting, S.g = (fun z => z ^ 2) ∧
        S.ℓ = (fun b => κ * (b - S.μ) ^ 2) ∧ ∃ φ : ℝ → Measure EReal, S.IsCPBE (c t h) φ ∧
          S.D1Inf (c t h) φ) →
      (∀ t (h : Fin t → ℝ) (v w : ℝ), c t h v = c t h w) ∧
        ¬ SocialLearningOccurs Lμ Lν (postMean P (play c))) := by
  intro P
  refine ⟨fun hκ' => ?_, fun hκ' c hc => ?_⟩
  · obtain ⟨Φ, hΦ, hΦc, -, hΦeq⟩ := propA4_revealing κ hκ hκ'
    exact ⟨Φ, hΦ, hΦeq, (learning_revealing Lμ Lν hμ hν hν0 Φ hΦ hΦc).2.2.2⟩
  · have hpool : ∀ t (h : Fin t → ℝ) (v w : ℝ), c t h v = c t h w := by
      intro t h v w
      obtain ⟨S, hg, hℓ, φ, hE, hD⟩ := hc t h
      obtain ⟨k, hk⟩ := propA4_pooling κ hκ' S hg hℓ (c t h) φ hE hD
      rw [hk v, hk w]
    exact ⟨hpool, not_learning_pooling Lμ Lν hnd c hpool⟩

end CC.Learning
