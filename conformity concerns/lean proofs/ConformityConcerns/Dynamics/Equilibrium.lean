import ConformityConcerns.PeriodGame.Instance
import ConformityConcerns.Dynamics.LongRun
import ConformityConcerns.Dynamics.Heterogeneous
import ConformityConcerns.Dynamics.Unbounded

/-!
# Proposition 2, Proposition A1 and Proposition A2 for the signaling-equilibrium process

`SigmaSeq` is defined from the period games (a date is revealing iff the signaling equilibrium of
the period game is revealing); by Corollary 1 it coincides with `SigmaC`, so the belief-dynamics
theorems transfer.
-/

namespace CC

open Matrix Filter Topology Set MeasureTheory

/-- Along the signaling-equilibrium process, a date is revealing iff `κ s̃² ≤ κck`. -/
lemma periodRevealing_iff_along (κ γ : ℕ → ℝ) (hκ : ∀ t, 0 < κ t) (S₁ : M2)
    (hS : S₁.PosSemidef) (t : ℕ) :
    periodRevealing (κ t) (SigmaSeq κ S₁ γ t) (γ t) ↔ revCrit (κ t) (SigmaSeq κ S₁ γ t) (γ t) := by
  rw [SigmaSeq_eq_SigmaC κ hκ S₁ hS γ]
  exact periodRevealing_iff (SigmaC_posSemidef κ γ S₁ hS t) (hκ t)

/-- **Proposition 2 (Characterization of Social Learning).** Suppose `Σ₁ ≻ 0` and `γ_t` is i.i.d.
with full support on `[0,1]`. If `κ < κck`, almost surely `σ²_{θ,t} → 0` and `σ²_{μ,t} → 0`
(social learning about fundamentals and preferences occurs). If `κ > κck`, almost surely there is
a finite time after which the signaling equilibrium is pooling in every period; `Σ_t` is then
constant and positive definite, so neither posterior variance tends to zero (social learning
fails). -/
theorem prop2 (S₁ : M2) (hS : S₁.PosDef) (G : Measure ℝ) (hG : FullSupportUnit G) :
    (∀ κ, 0 < κ → κ < κck → ∀ᵐ γ ∂(iidSeq G),
        Tendsto (fun t => SigmaSeq (fun _ => κ) S₁ γ t 0 0) atTop (𝓝 0) ∧
        Tendsto (fun t => SigmaSeq (fun _ => κ) S₁ γ t 1 1) atTop (𝓝 0)) ∧
    (∀ κ, κck < κ → ∀ᵐ γ ∂(iidSeq G), ∃ T, ∃ Sinf : M2, Sinf.PosDef ∧
        (∀ t, T ≤ t → ¬ periodRevealing κ (SigmaSeq (fun _ => κ) S₁ γ t) (γ t) ∧
          SigmaSeq (fun _ => κ) S₁ γ t = Sinf) ∧
        ¬ Tendsto (fun t => SigmaSeq (fun _ => κ) S₁ γ t 0 0) atTop (𝓝 0) ∧
        ¬ Tendsto (fun t => SigmaSeq (fun _ => κ) S₁ γ t 1 1) atTop (𝓝 0)) := by
  obtain ⟨hlow, hhigh⟩ := prop2_beliefs S₁ hS G hG
  refine ⟨fun κ hκ0 hκ => ?_, fun κ hκ => ?_⟩
  · have hpos : ∀ _ : ℕ, 0 < κ := fun _ => hκ0
    filter_upwards [hlow κ hκ0 hκ] with γ hγ
    rw [SigmaSeq_eq_SigmaC (fun _ => κ) hpos S₁ hS.posSemidef γ]
    exact hγ
  · have hκ0 : 0 < κ := lt_trans κck_pos hκ
    have hpos : ∀ _ : ℕ, 0 < κ := fun _ => hκ0
    filter_upwards [hhigh κ hκ] with γ ⟨T, Sinf, hSinf, hT⟩
    have hEq := SigmaSeq_eq_SigmaC (fun _ => κ) hpos S₁ hS.posSemidef γ
    refine ⟨T, Sinf, hSinf, fun t ht => ?_, ?_, ?_⟩
    · rw [periodRevealing_iff_along (fun _ => κ) γ hpos S₁ hS.posSemidef t, hEq]
      exact hT t ht
    all_goals
      intro hlim
      have hev : ∀ᶠ t in atTop, SigmaSeq (fun _ => κ) S₁ γ t = Sinf :=
        eventually_atTop.2 ⟨T, fun t ht => by rw [hEq]; exact (hT t ht).2⟩
    · have h0 : Tendsto (fun t => SigmaSeq (fun _ => κ) S₁ γ t 0 0) atTop (𝓝 (Sinf 0 0)) :=
        tendsto_const_nhds.congr' (hev.mono fun t ht => by dsimp only; rw [ht])
      exact (hSinf.diag_pos (i := 0)).ne' (tendsto_nhds_unique h0 hlim)
    · have h1 : Tendsto (fun t => SigmaSeq (fun _ => κ) S₁ γ t 1 1) atTop (𝓝 (Sinf 1 1)) :=
        tendsto_const_nhds.congr' (hev.mono fun t ht => by dsimp only; rw [ht])
      exact (hSinf.diag_pos (i := 1)).ne' (tendsto_nhds_unique h1 hlim)

/-- **Proposition A2 (Unbounded Stakes)**, for the signaling-equilibrium process. -/
theorem propA2_equilibrium (κ : ℝ) (hκ : κck < κ) (S₁ : M2) (hS : S₁.PosDef) (G : Measure ℝ)
    [IsProbabilityMeasure G] (hG0 : G (Iio 0) = 0) (hunb : ∀ M : ℝ, 0 < G (Ioi M))
    (γbar : ℝ) (hγbar : 0 < γbar) :
    ∀ᵐ γ ∂(iidSeq G), ∀ c < 1, ∀ᶠ t : ℕ in atTop,
      c ≤ (G (Ioi γbar)).toReal * t *
        min (SigmaSeq (fun _ => κ) S₁ γ t 0 0) (SigmaSeq (fun _ => κ) S₁ γ t 1 1) := by
  have hpos : ∀ _ : ℕ, 0 < κ := fun _ => lt_trans κck_pos hκ
  filter_upwards [propA2 κ hκ S₁ hS G hG0 hunb γbar hγbar] with γ hγ
  rw [SigmaSeq_eq_SigmaC (fun _ => κ) hpos S₁ hS.posSemidef γ]
  exact hγ

/-- **Proposition A1**, transfer to the signaling-equilibrium process: almost surely (all
`κ_t > 0`) the equilibrium process is `SigmaH`, and its revealing dates are those counted by
`revCountH`. -/
theorem propA1_equilibrium (Gκ Gγ : Measure ℝ) [IsProbabilityMeasure Gκ] [IsProbabilityMeasure Gγ]
    (hκpos : Gκ (Iic 0) = 0) (S₁ : M2) (hS : S₁.PosDef) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => Gκ.prod Gγ),
      SigmaSeq (fun t => (ω t).1) S₁ (fun t => (ω t).2) = SigmaH S₁ ω ∧
      ∀ t, (periodRevealing (ω t).1 (SigmaH S₁ ω t) (ω t).2 ↔
        revCrit (ω t).1 (SigmaH S₁ ω t) (ω t).2) := by
  have hall : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => Gκ.prod Gγ), ∀ t, 0 < (ω t).1 := by
    rw [ae_all_iff]
    intro t
    have hmap := (measurePreserving_eval_infinitePi (fun _ : ℕ => Gκ.prod Gγ) t)
    have : ∀ᵐ p ∂(Gκ.prod Gγ), 0 < p.1 := by
      rw [ae_iff]
      have hset : {p : ℝ × ℝ | ¬ 0 < p.1} = Iic 0 ×ˢ univ := by ext p; simp
      rw [hset, Measure.prod_prod, hκpos, zero_mul]
    exact hmap.quasiMeasurePreserving.ae this
  filter_upwards [hall] with ω hω
  refine ⟨SigmaSeq_eq_SigmaC _ hω S₁ hS.posSemidef _, fun t => ?_⟩
  exact periodRevealing_iff (SigmaC_posSemidef _ _ S₁ hS.posSemidef t) (hω t)

end CC
