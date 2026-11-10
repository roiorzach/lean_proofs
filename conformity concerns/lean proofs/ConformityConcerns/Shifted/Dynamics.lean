import ConformityConcerns.Shifted.Period
import ConformityConcerns.PeriodGame.Instance
import ConformityConcerns.Dynamics.Equilibrium

/-!
# Shifted preferences in the dynamic model

* The sensitivity at a history with beliefs `N(m, Σ)` depends on `Σ` and `γ` only, not on the
  means `m = (θ(h^t), μ(h^t))` (first sentence of the section).
* (ii) in the model: at every history where a revealing equilibrium exists and `s̃ ≠ 0` (for
  instance every history with `γ_t = 0` when `κ ≤ κck`), Social Optimality with shift `c`
  selects pooling once `|c|` is large enough.
* (iii) Under the alternative selection (`Game.IsShAltEq`), a date is revealing iff
  `κ s̃² ≤ κck`, for every `c`; so the covariance process `SigmaSeqAlt` and the revealing dates
  coincide with the baseline (`SigmaSeq`, `SigmaC`), and Propositions 2, A1 and A2 hold as
  before.
-/

namespace CC.Shifted

open MeasureTheory ProbabilityTheory Set Matrix Filter Topology
open scoped ENNReal
open CC.LG

/-! ### The sensitivity does not depend on the public means -/

/-- The sensitivity at a history with beliefs `N(m, Σ)` does not depend on the means
`m = (θ(h^t), μ(h^t))`. -/
theorem sens_indep_means (m m' : EuclideanSpace ℝ (Fin 2)) {S : M2} (hS : S.PosSemidef)
    (γ κ : ℝ) : (gameAt m S γ κ).sens = (gameAt m' S γ κ).sens := by
  rw [gameAt_sens hS, gameAt_sens hS]

/-! ### (ii) in the model -/

/-- With `γ_t = 0` the sensitivity is `1`. -/
theorem sens_gamma_zero {S : M2} (hS : S.PosSemidef) : sens S 0 = 1 := by
  have h : 0 < Vt S := by
    unfold Vt
    have := hS.diag_nonneg (i := 1)
    linarith
  unfold sens
  rw [show Vt S + 0 * Ct S = Vt S by ring, show Vt S + 2 * 0 * Ct S + 0 ^ 2 * Ht S = Vt S by ring]
  exact div_self h.ne'

/-- **(ii) in the model.** At every history where a revealing equilibrium exists
(`κ s̃² ≤ κck`) and `s̃ ≠ 0`, there is `c₀ > 0` such that for `|c| > c₀` a revealing linear
equilibrium exists but Social Optimality with shift `c` selects pooling. -/
theorem large_c_gameAt (m : EuclideanSpace ℝ (Fin 2)) {S : M2} (hS : S.PosSemidef) {γ κ : ℝ}
    (hκ : 0 < κ) (hrev : revCrit κ S γ) (hs : sens S γ ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < |c| →
      (gameAt m S γ κ).HasShRevealingEq c ∧
      ∀ (a : EuclideanSpace ℝ (Fin 2) → ℝ) (φ : Kernel ℝ ℝ),
        (gameAt m S γ κ).IsShSignalingEq c a φ → (gameAt m S γ κ).IsPooling a := by
  have hG := gameAt_std (m := m) (γ := γ) hS hκ
  have hsens : (gameAt m S γ κ).sens = sens S γ := gameAt_sens hS
  have hκG : (gameAt m S γ κ).κ = κ := rfl
  have hrev' : (gameAt m S γ κ).κ * (gameAt m S γ κ).sens ^ 2 ≤ κck := by
    rw [hsens, hκG]
    exact hrev
  have hs' : (gameAt m S γ κ).sens ≠ 0 := by
    rw [hsens]
    exact hs
  obtain ⟨hpos, h⟩ := large_c_threshold _ hG hrev' hs'
  exact ⟨_, hpos, fun c hc => ⟨(h c).1, (h c).2.2 hc⟩⟩

/-- The hypotheses of `large_c_gameAt` hold, for instance, at every history with `γ_t = 0`
when `0 < κ ≤ κck`. -/
theorem large_c_model (m : EuclideanSpace ℝ (Fin 2)) {S : M2} (hS : S.PosSemidef) {κ : ℝ}
    (hκ : 0 < κ) (hκ' : κ ≤ κck) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < |c| →
      (gameAt m S 0 κ).HasShRevealingEq c ∧
      ∀ (a : EuclideanSpace ℝ (Fin 2) → ℝ) (φ : Kernel ℝ ℝ),
        (gameAt m S 0 κ).IsShSignalingEq c a φ → (gameAt m S 0 κ).IsPooling a := by
  have h1 := sens_gamma_zero hS
  refine large_c_gameAt m hS hκ ?_ (by rw [h1]; norm_num)
  show κ * sens S 0 ^ 2 ≤ κck
  rw [h1]
  simpa using hκ'

/-! ### (iii) The covariance process under the alternative selection -/

/-- Under the alternative selection with shift `c`, the period at every history with covariance
`Σ` (any means) is revealing. -/
def periodRevealingAlt (κ c : ℝ) (S : M2) (γ : ℝ) : Prop :=
  ∀ (m : EuclideanSpace ℝ (Fin 2)) (a : EuclideanSpace ℝ (Fin 2) → ℝ) (φ : Kernel ℝ ℝ),
    (gameAt m S γ κ).IsShAltEq c a φ → (gameAt m S γ κ).IsRevealing a

/-- The posterior covariance process under the alternative selection with shift `c`: after a
revealing period the public observes `Z_t` (an affine bijection of `a_t`) and updates by
`kalman`. -/
noncomputable def SigmaSeqAlt (κ : ℕ → ℝ) (c : ℝ) (S₁ : M2) (γ : ℕ → ℝ) : ℕ → M2
  | 0 => S₁
  | t + 1 =>
    haveI := Classical.propDecidable
      (periodRevealingAlt (κ t) c (SigmaSeqAlt κ c S₁ γ t) (γ t))
    if periodRevealingAlt (κ t) c (SigmaSeqAlt κ c S₁ γ t) (γ t) then
      kalman (SigmaSeqAlt κ c S₁ γ t) (γ t)
    else SigmaSeqAlt κ c S₁ γ t

/-- `N_t` under the alternative selection: the number of revealing dates `s < t`. -/
noncomputable def revCountAlt (κ : ℕ → ℝ) (c : ℝ) (S₁ : M2) (γ : ℕ → ℝ) (t : ℕ) : ℕ :=
  haveI := Classical.decPred
    (fun s => periodRevealingAlt (κ s) c (SigmaSeqAlt κ c S₁ γ s) (γ s))
  ((Finset.range t).filter
    fun s => periodRevealingAlt (κ s) c (SigmaSeqAlt κ c S₁ γ s) (γ s)).card

/-- **(iii), revealing dates.** Under the alternative selection a period is revealing iff
`κ s̃² ≤ κck`, for every `c`; that is, iff the baseline signaling equilibrium is revealing. -/
theorem periodRevealingAlt_iff {S : M2} (hS : S.PosSemidef) {κ : ℝ} (hκ : 0 < κ) (c γ : ℝ) :
    (periodRevealingAlt κ c S γ ↔ revCrit κ S γ) ∧
    (periodRevealingAlt κ c S γ ↔ periodRevealing κ S γ) := by
  have key : ∀ m : EuclideanSpace ℝ (Fin 2),
      |(gameAt m S γ κ).sens| ≤ √(κck / (gameAt m S γ κ).κ) ↔ revCrit κ S γ := fun m => by
    rw [gameAt_sens hS, show (gameAt m S γ κ).κ = κ from rfl, gameAt_revCrit_iff hκ]
  have h1 : periodRevealingAlt κ c S γ ↔ revCrit κ S γ := by
    constructor
    · intro h
      have hG := gameAt_std (m := 0) (γ := γ) hS hκ
      obtain ⟨a, φ, hE⟩ := altEq_exists _ hG c
      exact (key 0).1 ((altEq_revealing_iff _ hG c hE).1.1 (h 0 a φ hE))
    · intro h m a φ hE
      exact (altEq_revealing_iff _ (gameAt_std hS hκ) c hE).1.2 ((key m).2 h)
  exact ⟨h1, h1.trans (periodRevealing_iff hS hκ).symm⟩

/-- **(iii), covariance process.** For every `c`, the covariance process and the revealing-date
count under the alternative selection coincide with those of the baseline signaling
equilibrium. -/
theorem SigmaSeqAlt_eq (κ : ℕ → ℝ) (hκ : ∀ t, 0 < κ t) (c : ℝ) (S₁ : M2)
    (hS : S₁.PosSemidef) (γ : ℕ → ℝ) :
    SigmaSeqAlt κ c S₁ γ = SigmaSeq κ S₁ γ ∧ SigmaSeqAlt κ c S₁ γ = SigmaC κ S₁ γ ∧
      ∀ t, revCountAlt κ c S₁ γ t = revCount κ S₁ γ t := by
  have key : ∀ t, SigmaSeqAlt κ c S₁ γ t = SigmaC κ S₁ γ t ∧ (SigmaC κ S₁ γ t).PosSemidef := by
    intro t
    induction t with
    | zero => exact ⟨rfl, hS⟩
    | succ t ih =>
      obtain ⟨h1, h2⟩ := ih
      have hiff := (periodRevealingAlt_iff h2 (hκ t) c (γ t)).1
      simp only [SigmaSeqAlt, SigmaC, h1]
      by_cases hc : revCrit (κ t) (SigmaC κ S₁ γ t) (γ t)
      · have hp : periodRevealingAlt (κ t) c (SigmaSeqAlt κ c S₁ γ t) (γ t) := by
          rw [h1]; exact hiff.2 hc
        exact ⟨by simp only [hp, hc, ↓reduceIte],
          by simp only [hc, ↓reduceIte]; exact kalman_psd h2 _⟩
      · have hp : ¬ periodRevealingAlt (κ t) c (SigmaSeqAlt κ c S₁ γ t) (γ t) := by
          rw [h1]; exact mt hiff.1 hc
        exact ⟨by simp only [hp, hc, ↓reduceIte], by simp only [hc, ↓reduceIte]; exact h2⟩
  have hfun : SigmaSeqAlt κ c S₁ γ = SigmaC κ S₁ γ := funext fun t => (key t).1
  refine ⟨hfun.trans (SigmaSeq_eq_SigmaC κ hκ S₁ hS γ).symm, hfun, fun t => ?_⟩
  unfold revCountAlt revCount
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_range, hfun]
  exact and_congr_right fun _ =>
    (periodRevealingAlt_iff (SigmaC_posSemidef κ γ S₁ hS s) (hκ s) c (γ s)).1

/-- **Proposition 2 under the alternative selection** (posterior variances). Suppose `Σ₁ ≻ 0`
and `γ_t` is i.i.d. with full support on `[0,1]`. For every `c`: if `κ < κck`, almost surely
`σ²_{θ,t} → 0` and `σ²_{μ,t} → 0`; if `κ > κck`, almost surely there is a finite time after
which every period is pooling, `Σ_t` is then constant and positive definite, and neither
posterior variance tends to zero. -/
theorem prop2_alt (S₁ : M2) (hS : S₁.PosDef) (G : Measure ℝ) (hG : FullSupportUnit G) (c : ℝ) :
    (∀ κ, 0 < κ → κ < κck → ∀ᵐ γ ∂(iidSeq G),
        Tendsto (fun t => SigmaSeqAlt (fun _ => κ) c S₁ γ t 0 0) atTop (𝓝 0) ∧
        Tendsto (fun t => SigmaSeqAlt (fun _ => κ) c S₁ γ t 1 1) atTop (𝓝 0)) ∧
    (∀ κ, κck < κ → ∀ᵐ γ ∂(iidSeq G), ∃ T, ∃ Sinf : M2, Sinf.PosDef ∧
        (∀ t, T ≤ t → ¬ periodRevealingAlt κ c (SigmaSeqAlt (fun _ => κ) c S₁ γ t) (γ t) ∧
          SigmaSeqAlt (fun _ => κ) c S₁ γ t = Sinf) ∧
        ¬ Tendsto (fun t => SigmaSeqAlt (fun _ => κ) c S₁ γ t 0 0) atTop (𝓝 0) ∧
        ¬ Tendsto (fun t => SigmaSeqAlt (fun _ => κ) c S₁ γ t 1 1) atTop (𝓝 0)) := by
  obtain ⟨hlow, hhigh⟩ := prop2 S₁ hS G hG
  have hEq : ∀ κ, 0 < κ → ∀ γ, SigmaSeqAlt (fun _ => κ) c S₁ γ = SigmaSeq (fun _ => κ) S₁ γ :=
    fun κ hκ γ => (SigmaSeqAlt_eq (fun _ => κ) (fun _ => hκ) c S₁ hS.posSemidef γ).1
  refine ⟨fun κ hκ0 hκ => ?_, fun κ hκ => ?_⟩
  · filter_upwards [hlow κ hκ0 hκ] with γ hγ
    rw [hEq κ hκ0 γ]
    exact hγ
  · have hκ0 : 0 < κ := lt_trans κck_pos hκ
    filter_upwards [hhigh κ hκ] with γ ⟨T, Sinf, hSinf, hT, h0, h1⟩
    rw [hEq κ hκ0 γ]
    refine ⟨T, Sinf, hSinf, fun t ht => ⟨?_, (hT t ht).2⟩, h0, h1⟩
    have hpsd : (SigmaSeq (fun _ => κ) S₁ γ t).PosSemidef := by
      rw [SigmaSeq_eq_SigmaC _ (fun _ => hκ0) S₁ hS.posSemidef γ]
      exact SigmaC_posSemidef _ _ S₁ hS.posSemidef t
    rw [(periodRevealingAlt_iff hpsd hκ0 c (γ t)).2]
    exact (hT t ht).1

/-- **Proposition A1 under the alternative selection.** `κ_t` i.i.d. with law `Gκ` on `(0,∞)`
with no atom at `κck`, independent of the i.i.d. weights (full support on `[0,1]`), and
`ε = Pr(κ_t < κck)`. For every `c`: if `ε > 0`, almost surely `Σ_t → 0`, `N_t/t → ε`, and
`liminf ε t min{σ²_{θ,t}, σ²_{μ,t}} ≥ 1`; if `inf Supp(κ_t) > κck`, almost surely after a finite
time every period is pooling and `Σ_t` is constant and positive definite. -/
theorem propA1_alt (Gκ Gγ : Measure ℝ) [IsProbabilityMeasure Gκ] (hκpos : Gκ (Iic 0) = 0)
    (hatom : Gκ {κck} = 0) (hGγ : FullSupportUnit Gγ) (S₁ : M2) (hS : S₁.PosDef) (c : ℝ) :
    let P := Measure.infinitePi fun _ : ℕ => Gκ.prod Gγ
    let ε := (Gκ (Iio κck)).toReal
    let Sig := fun ω : ℕ → ℝ × ℝ => SigmaSeqAlt (fun t => (ω t).1) c S₁ (fun t => (ω t).2)
    (0 < ε → ∀ᵐ ω ∂P,
        Tendsto (Sig ω) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ =>
          (revCountAlt (fun t => (ω t).1) c S₁ (fun t => (ω t).2) t : ℝ) / t) atTop (𝓝 ε) ∧
        ∀ q < 1, ∀ᶠ t : ℕ in atTop, q ≤ ε * t * min (Sig ω t 0 0) (Sig ω t 1 1)) ∧
    ((∃ κ₀, κck < κ₀ ∧ Gκ (Iio κ₀) = 0) → ∀ᵐ ω ∂P, ∃ T, ∃ Sinf : M2, Sinf.PosDef ∧
        ∀ t, T ≤ t → ¬ periodRevealingAlt (ω t).1 c (Sig ω t) (ω t).2 ∧ Sig ω t = Sinf) := by
  have h := propA1 Gκ Gγ hκpos hatom hGγ S₁ hS
  have hall : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => Gκ.prod Gγ), ∀ t, 0 < (ω t).1 := by
    have := hGγ.prob
    rw [ae_all_iff]
    intro t
    have hmap := (measurePreserving_eval_infinitePi (fun _ : ℕ => Gκ.prod Gγ) t)
    have : ∀ᵐ p ∂(Gκ.prod Gγ), 0 < p.1 := by
      rw [ae_iff]
      have hset : {p : ℝ × ℝ | ¬ 0 < p.1} = Iic 0 ×ˢ univ := by ext p; simp
      rw [hset, Measure.prod_prod, hκpos, zero_mul]
    exact hmap.quasiMeasurePreserving.ae this
  have hEq : ∀ ω : ℕ → ℝ × ℝ, (∀ t, 0 < (ω t).1) →
      SigmaSeqAlt (fun t => (ω t).1) c S₁ (fun t => (ω t).2) = SigmaH S₁ ω ∧
      ∀ t, revCountAlt (fun t => (ω t).1) c S₁ (fun t => (ω t).2) t = revCountH S₁ ω t := by
    intro ω hω
    obtain ⟨-, h2, h3⟩ := SigmaSeqAlt_eq _ hω c S₁ hS.posSemidef (fun t => (ω t).2)
    exact ⟨h2, h3⟩
  dsimp only at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hε => ?_, fun hκ0 => ?_⟩
  · filter_upwards [h1 hε, hall] with ω hω hpos
    obtain ⟨e1, e2⟩ := hEq ω hpos
    simp only [e1, e2]
    exact hω
  · filter_upwards [h2 hκ0, hall] with ω ⟨T, Sinf, hSinf, hT⟩ hpos
    obtain ⟨e1, -⟩ := hEq ω hpos
    refine ⟨T, Sinf, hSinf, fun t ht => ?_⟩
    rw [e1]
    refine ⟨?_, (hT t ht).2⟩
    rw [(periodRevealingAlt_iff (S := SigmaH S₁ ω t) (SigmaC_posSemidef _ _ S₁ hS.posSemidef t)
      (hpos t) c _).1]
    exact (hT t ht).1

/-- **Proposition A2 (Unbounded Stakes) under the alternative selection.** For every `c`, with
`κ > κck` and `γ_t` i.i.d. on `[0,∞)` and unbounded above, almost surely
`liminf Pr(γ_t > γ̄) t min{σ²_{θ,t}, σ²_{μ,t}} ≥ 1` for every `γ̄ > 0`. -/
theorem propA2_alt (κ : ℝ) (hκ : κck < κ) (S₁ : M2) (hS : S₁.PosDef) (G : Measure ℝ)
    [IsProbabilityMeasure G] (hG0 : G (Iio 0) = 0) (hunb : ∀ M : ℝ, 0 < G (Ioi M))
    (γbar : ℝ) (hγbar : 0 < γbar) (c : ℝ) :
    ∀ᵐ γ ∂(iidSeq G), ∀ q < 1, ∀ᶠ t : ℕ in atTop,
      q ≤ (G (Ioi γbar)).toReal * t *
        min (SigmaSeqAlt (fun _ => κ) c S₁ γ t 0 0) (SigmaSeqAlt (fun _ => κ) c S₁ γ t 1 1) := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  filter_upwards [propA2_equilibrium κ hκ S₁ hS G hG0 hunb γbar hγbar] with γ hγ
  rw [(SigmaSeqAlt_eq (fun _ => κ) (fun _ => hκ0) c S₁ hS.posSemidef γ).1]
  exact hγ

end CC.Shifted
