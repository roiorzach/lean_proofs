import ConformityConcerns.Shifted.Dynamics
import ConformityConcerns.Interventions.Fragility
import ConformityConcerns.Interventions.PriorCov
import ConformityConcerns.Corollaries.KnownTheta
import ConformityConcerns.Corollaries.KnownMu

/-!
# Shifted preferences: Proposition 3 and Corollaries A2, A3 under the alternative selection

Under the alternative selection with shift `c` the revealing dates and the covariance process
coincide with those of the baseline signaling equilibrium (`periodRevealingAlt_iff`,
`SigmaSeqAlt_eq`), so Proposition 3 (at the variance level) and the social-learning parts of
Corollaries A2 and A3 hold as before.
-/

namespace CC.Shifted

open Set Filter Topology Matrix

/-- **Proposition 3 (1) under the alternative selection.** When `κ > κck`, for every `c`, an
individual-oriented intervention (any noise variance, including perfect revelation of `θ`)
never results in social learning about `μ`, and a peer-oriented intervention never results in
social learning about `θ`, whatever the later weights `γ_t ∈ [0,1]`. -/
theorem prop3_1_alt (κ : ℝ) (hκ : κck < κ) (S : M2) (hS : S.PosDef) (n : ℝ) (hn : 0 ≤ n)
    (γ : ℕ → ℝ) (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) (c : ℝ) :
    ¬ Tendsto (fun t => SigmaSeqAlt (fun _ => κ) c (observeTheta S n) γ t 1 1) atTop (𝓝 0) ∧
    ¬ Tendsto (fun t => SigmaSeqAlt (fun _ => κ) c (observeMu S n) γ t 0 0) atTop (𝓝 0) := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  rw [(SigmaSeqAlt_eq (fun _ => κ) (fun _ => hκ0) c _ (observeTheta_props hS hn).1 γ).1,
    (SigmaSeqAlt_eq (fun _ => κ) (fun _ => hκ0) c _ (observeMu_props hS hn).1 γ).1]
  exact prop3_1 κ hκ S hS n hn γ hγ

/-- **Proposition 3 (1) under the alternative selection, for every prior of the model.** -/
theorem prop3_1_prior_alt (κ : ℝ) (hκ : κck < κ) {σθ σμ ρ : ℝ} (hθ : 0 ≤ σθ) (hμ : 0 ≤ σμ)
    (hρ : |ρ| < 1) (n : ℝ) (hn : 0 ≤ n) (γ : ℕ → ℝ) (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) (c : ℝ) :
    (0 < σμ → ¬ Tendsto (fun t => SigmaSeqAlt (fun _ => κ) c
      (observeTheta (priorCov σθ σμ ρ) n) γ t 1 1) atTop (𝓝 0)) ∧
    (0 < σθ → ¬ Tendsto (fun t => SigmaSeqAlt (fun _ => κ) c
      (observeMu (priorCov σθ σμ ρ) n) γ t 0 0) atTop (𝓝 0)) := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  have hpsd := priorCov_psd (σθ := σθ) (σμ := σμ) hρ
  obtain ⟨h1, h2⟩ := prop3_1_prior κ hκ hθ hμ hρ n hn γ hγ
  refine ⟨fun hμ' => ?_, fun hθ' => ?_⟩
  · have hP : (observeTheta (priorCov σθ σμ ρ) n).PosSemidef := by
      rcases hθ.eq_or_lt with h | h
      · rw [observeTheta_of_zero hpsd (by simp [← h]) n]; exact hpsd
      · exact (observeTheta_props (priorCov_posDef h hμ' hρ) hn).1
    rw [(SigmaSeqAlt_eq (fun _ => κ) (fun _ => hκ0) c _ hP γ).1]
    exact h1 hμ'
  · have hP : (observeMu (priorCov σθ σμ ρ) n).PosSemidef := by
      rcases hμ.eq_or_lt with h | h
      · rw [observeMu_of_zero hpsd (by simp [← h]) n]; exact hpsd
      · exact (observeMu_props (priorCov_posDef hθ' h hρ) hn).1
    rw [(SigmaSeqAlt_eq (fun _ => κ) (fun _ => hκ0) c _ hP γ).1]
    exact h2 hθ'

/-- **Proposition 3 (2), individual-oriented, under the alternative selection.** At zero
correlation and `κ > κck`, for every `c`, a pooling period is never made revealing by an
individual-oriented intervention. -/
theorem prop3_2_individual_alt (κ : ℝ) (hκ : κck < κ) (x y γ : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (c : ℝ) :
    ¬ periodRevealingAlt κ c !![x, 0; 0, y] γ →
      ¬ periodRevealingAlt κ c (observeTheta !![x, 0; 0, y] 1) γ := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  have hpsd : (observeTheta !![x, 0; 0, y] 1).PosSemidef := by
    rw [observeTheta_diag x y hx]
    exact psd_diag _ y (by positivity) hy
  rw [((periodRevealingAlt_iff (psd_diag x y hx hy) hκ0 c γ).2),
    ((periodRevealingAlt_iff hpsd hκ0 c γ).2)]
  exact prop3_2_individual κ hκ x y γ hx hy

/-- **Proposition 3 (2), peer-oriented, under the alternative selection.** At zero correlation
and `κ > κck`, for every `c`, `σ²_μ > 0` and `γ > 0` there is `σ²_θ > 0` such that the
period is pooling before and revealing after a peer-oriented intervention. -/
theorem prop3_2_peer_alt (κ : ℝ) (hκ : κck < κ) (y γ : ℝ) (hy : 0 < y) (hγ : 0 < γ) (c : ℝ) :
    ∃ x : ℝ, 0 < x ∧ ¬ periodRevealingAlt κ c !![x, 0; 0, y] γ ∧
      periodRevealingAlt κ c (observeMu !![x, 0; 0, y] 1) γ := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  obtain ⟨x, hx, h1, h2⟩ := prop3_2_peer κ hκ y γ hy hγ
  have hpsd : (observeMu !![x, 0; 0, y] 1).PosSemidef := by
    rw [observeMu_diag x y hy.le]
    exact psd_diag x _ hx.le (by positivity)
  refine ⟨x, hx, ?_, ?_⟩
  · rw [(periodRevealingAlt_iff (psd_diag x y hx.le hy.le) hκ0 c γ).2]
    exact h1
  · rw [(periodRevealingAlt_iff hpsd hκ0 c γ).2]
    exact h2

/-- **Corollary A2 under the alternative selection (social learning).** With `θ` known
(`Σ₁ = diag(0, σ²_μ)`), for every `c` and all weights: social learning about preferences occurs
iff `κ ≤ κck`; when `κ > κck`, `σ²_{μ,t} = σ²_μ` at every date. -/
theorem corollaryA2_alt (σμ2 : ℝ) (hσ : 0 < σμ2) (c : ℝ) :
    let S₁ : M2 := !![0, 0; 0, σμ2]
    (∀ κ, 0 < κ → ∀ γ : ℕ → ℝ,
      (Tendsto (fun t => SigmaSeqAlt (fun _ => κ) c S₁ γ t 1 1) atTop (𝓝 0) ↔ κ ≤ κck)) ∧
    (∀ κ, κck < κ → ∀ γ : ℕ → ℝ, ∀ t, SigmaSeqAlt (fun _ => κ) c S₁ γ t 1 1 = σμ2) := by
  intro S₁
  have h := corollaryA2 σμ2 hσ
  dsimp only at h
  have hpsd : S₁.PosSemidef := psd_diag 0 σμ2 le_rfl hσ.le
  have hEq : ∀ κ, 0 < κ → ∀ γ, SigmaSeqAlt (fun _ => κ) c S₁ γ = SigmaSeq (fun _ => κ) S₁ γ :=
    fun κ hκ γ => (SigmaSeqAlt_eq (fun _ => κ) (fun _ => hκ) c S₁ hpsd γ).1
  refine ⟨fun κ hκ γ => ?_, fun κ hκ γ t => ?_⟩
  · rw [hEq κ hκ γ]
    exact h.1 κ hκ γ
  · rw [hEq κ (lt_trans κck_pos hκ) γ]
    exact h.2.1 κ hκ γ t

/-- **Corollary A3 under the alternative selection (social learning).** With `μ` known
(`Σ₁ = diag(σ²_θ, 0)`) and `γ_t = 1`, for every `c`: social learning about fundamentals occurs
iff `κ ≤ κck`; when `κ > κck` the limit `q(κ) = lim σ²_{θ,t}` is positive and weakly
increasing in `κ`. -/
theorem corollaryA3_alt (σθ2 : ℝ) (hσ : 0 < σθ2) (c : ℝ) :
    let S₁ : M2 := !![σθ2, 0; 0, 0]
    let Sg : ℝ → ℕ → M2 := fun κ => SigmaSeqAlt (fun _ => κ) c S₁ (fun _ => 1)
    (∀ κ, 0 < κ → (Tendsto (fun t => Sg κ t 0 0) atTop (𝓝 0) ↔ κ ≤ κck)) ∧
    (∃ q : ℝ → ℝ, MonotoneOn q (Ioi κck) ∧
      ∀ κ, κck < κ → 0 < q κ ∧ Tendsto (fun t => Sg κ t 0 0) atTop (𝓝 (q κ))) := by
  intro S₁ Sg
  have h := corollaryA3 σθ2 hσ
  dsimp only at h
  have hpsd : S₁.PosSemidef := psd_diag σθ2 0 hσ.le le_rfl
  have hEq : ∀ κ, 0 < κ → Sg κ = SigmaSeq (fun _ => κ) S₁ (fun _ => 1) :=
    fun κ hκ => (SigmaSeqAlt_eq (fun _ => κ) (fun _ => hκ) c S₁ hpsd _).1
  obtain ⟨h1, ⟨q, hq, hq'⟩, -⟩ := h
  refine ⟨fun κ hκ => ?_, q, hq, fun κ hκ => ?_⟩
  · rw [hEq κ hκ]
    exact h1 κ hκ
  · rw [hEq κ (lt_trans κck_pos hκ)]
    exact hq' κ hκ

end CC.Shifted
