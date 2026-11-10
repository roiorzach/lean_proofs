import ConformityConcerns.Dynamics.Defs
import ConformityConcerns.Dynamics.LemmasLearn
import ConformityConcerns.Dynamics.LemmasProb

/-!
# Proposition 2 (Characterization of Social Learning) — belief dynamics

Social learning about fundamentals (resp. preferences) is formalized at the level of posterior
variances: `σ²_{θ,t} = Σ_t 0 0 → 0` (resp. `σ²_{μ,t} = Σ_t 1 1 → 0`).
-/

namespace CC

open Matrix Filter Topology Set MeasureTheory

/-- Kalman updates preserve positive semidefiniteness (for any real `γ_t`, `κ_t`). -/
theorem SigmaC_posSemidef (κ γ : ℕ → ℝ) (S₁ : M2) (hS : S₁.PosSemidef) (t : ℕ) :
    (SigmaC κ S₁ γ t).PosSemidef :=
  SigmaC_psd' κ γ S₁ hS t

/-- A positive prior variance stays positive (observations are noisy). -/
theorem SigmaC_diag_pos (κ γ : ℕ → ℝ) (S₁ : M2) (hS : S₁.PosSemidef) (t : ℕ) (i : Fin 2)
    (hi : 0 < S₁ i i) : 0 < SigmaC κ S₁ γ t i i := by
  induction t with
  | zero => exact hi
  | succ t ih =>
    by_cases h : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)
    · rw [SigmaC_succ_rev κ γ S₁ h]; exact kalman_diag_pos (SigmaC_psd' κ γ S₁ hS t) _ i ih
    · rw [SigmaC_succ_pool κ γ S₁ h]; exact ih

/-- **Proposition 2, case `κ > κck` (deterministic core).** For every sequence of weights in
`[0,1]` and every positive semidefinite prior, there is a finite time after which every period is
pooling, so `Σ_t` is eventually constant. -/
theorem prop2_high_core (κ : ℝ) (hκ : κck < κ) (S₁ : M2) (hS : S₁.PosSemidef) (γ : ℕ → ℝ)
    (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) :
    ∃ T, ∀ t, T ≤ t → ¬ revCrit κ (SigmaC (fun _ => κ) S₁ γ t) (γ t) ∧
      SigmaC (fun _ => κ) S₁ γ t = SigmaC (fun _ => κ) S₁ γ T :=
  high_core_gen hS hκ (fun _ => le_rfl) hγ

/-- **Proposition 2, case `κ < κck` (deterministic core).** If every open subinterval of
`[0,1]` is visited infinitely often by the weights, then `Σ_t → 0`. -/
theorem prop2_low_core (κ : ℝ) (_hκ0 : 0 < κ) (hκ : κ < κck) (S₁ : M2) (hS : S₁.PosDef)
    (γ : ℕ → ℝ) (_hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1)
    (hvisit : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ᶠ t in atTop, γ t ∈ Ioo a b) :
    Tendsto (SigmaC (fun _ => κ) S₁ γ) atTop (𝓝 0) :=
  learning_core hS.posSemidef hκ fun a b ha hab hb =>
    (hvisit a b ha.le hab hb).mono fun _ ht => ⟨le_rfl, ht⟩

/-- Almost surely, an i.i.d. sequence with full support on `[0,1]` stays in `[0,1]` and visits
every open subinterval infinitely often. -/
theorem fullSupport_visits (G : Measure ℝ) (hG : FullSupportUnit G) :
    ∀ᵐ γ ∂(iidSeq G), (∀ t, γ t ∈ Icc (0 : ℝ) 1) ∧
      ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ᶠ t in atTop, γ t ∈ Ioo a b := by
  have := hG.prob
  simp only [iidSeq]
  have h1 := ae_forall_mem G measurableSet_Icc hG.supp
  have h2 : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G), ∀ p q : ℚ, (0 : ℝ) ≤ p → (p : ℝ) < q →
      (q : ℝ) ≤ 1 → ∃ᶠ t in atTop, True ∧ γ t ∈ Ioo (p : ℝ) q := by
    rw [ae_all_iff]; intro p; rw [ae_all_iff]; intro q
    by_cases hpq : (0 : ℝ) ≤ p ∧ (p : ℝ) < q ∧ (q : ℝ) ≤ 1
    · filter_upwards [ae_frequently_mem G measurableSet_Ioo
        (hG.pos p q hpq.1 hpq.2.1 hpq.2.2)] with γ hγ
      intro _ _ _
      exact hγ.mono fun t ht => ⟨trivial, ht⟩
    · exact ae_of_all _ fun γ h0 h1 h2 => absurd ⟨h0, h1, h2⟩ hpq
  filter_upwards [h1, h2] with γ hγ1 hγ2
  exact ⟨hγ1, fun a b ha hab hb => (visits_of_rat hγ2 a b ha hab hb).mono fun t ht => ht.2⟩

/-- **Proposition 2 (belief dynamics).** Suppose `Σ₁ ≻ 0` and `γ_t` is i.i.d. with full support on
`[0,1]`. If `κ < κck`, almost surely `σ²_{θ,t} → 0` and `σ²_{μ,t} → 0`. If `κ > κck`, almost surely
there is a finite time after which every period is pooling, and `Σ_t` is then constant and
positive definite, so neither variance converges to zero. -/
theorem prop2_beliefs (S₁ : M2) (hS : S₁.PosDef) (G : Measure ℝ) (hG : FullSupportUnit G) :
    (∀ κ, 0 < κ → κ < κck → ∀ᵐ γ ∂(iidSeq G),
        Tendsto (fun t => SigmaC (fun _ => κ) S₁ γ t 0 0) atTop (𝓝 0) ∧
        Tendsto (fun t => SigmaC (fun _ => κ) S₁ γ t 1 1) atTop (𝓝 0)) ∧
    (∀ κ, κck < κ → ∀ᵐ γ ∂(iidSeq G), ∃ T, ∃ Sinf : M2, Sinf.PosDef ∧
        ∀ t, T ≤ t → ¬ revCrit κ (SigmaC (fun _ => κ) S₁ γ t) (γ t) ∧
          SigmaC (fun _ => κ) S₁ γ t = Sinf) := by
  refine ⟨fun κ hκ0 hκ => ?_, fun κ hκ => ?_⟩
  · filter_upwards [fullSupport_visits G hG] with γ hγ
    have h := prop2_low_core κ hκ0 hκ S₁ hS γ hγ.1 hγ.2
    exact ⟨by simpa [Function.comp_def] using ((continuous_id.matrix_elem 0 0).tendsto 0).comp h,
      by simpa [Function.comp_def] using ((continuous_id.matrix_elem 1 1).tendsto 0).comp h⟩
  · filter_upwards [fullSupport_visits G hG] with γ hγ
    obtain ⟨T, hT⟩ := prop2_high_core κ hκ S₁ hS.posSemidef γ hγ.1
    exact ⟨T, SigmaC (fun _ => κ) S₁ γ T, SigmaC_pd _ _ _ hS T, hT⟩

end CC
