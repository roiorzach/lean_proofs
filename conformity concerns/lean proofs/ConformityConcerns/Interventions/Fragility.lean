import ConformityConcerns.Interventions.Sensitivity
import ConformityConcerns.Interventions.DiagFacts
import ConformityConcerns.PeriodGame.Instance
import ConformityConcerns.Dynamics.LongRun
import ConformityConcerns.Corollaries.KnownTheta
import Mathlib.Topology.Order.IntermediateValue

/-!
# Proposition 3 (Fragility)

An individual-oriented (resp. peer-oriented) intervention publicly discloses a signal `θ + η`
(resp. `μ + η`); `observeTheta S n` / `observeMu S n` is the posterior covariance when
`Var η = n` (`n = 1`: a signal distributed like `s_t` / `v_t`; `n = 0`: perfect revelation).
After the intervention, play continues in the signaling equilibrium (`SigmaSeq`).
-/

namespace CC

open Set Filter Topology Matrix

/-- When `κ > κck`, from a PSD prior with a positive variance `S₁ i i`, that variance does not
converge to zero along the signaling-equilibrium process. -/
lemma not_tendsto_zero_of_pos (κ : ℝ) (hκ : κck < κ) (S₁ : M2) (hS : S₁.PosSemidef)
    (γ : ℕ → ℝ) (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) (i : Fin 2) (hi : 0 < S₁ i i) :
    ¬ Tendsto (fun t => SigmaSeq (fun _ => κ) S₁ γ t i i) atTop (𝓝 0) := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  rw [SigmaSeq_eq_SigmaC (fun _ => κ) (fun _ => hκ0) S₁ hS γ]
  obtain ⟨T, hT⟩ := prop2_high_core κ hκ S₁ hS γ hγ
  have hpos := SigmaC_diag_pos (fun _ => κ) γ S₁ hS T i hi
  intro h
  have h2 : Tendsto (fun t => SigmaC (fun _ => κ) S₁ γ t i i) atTop
      (𝓝 (SigmaC (fun _ => κ) S₁ γ T i i)) := by
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    exact ⟨T, fun t ht => by rw [(hT t ht).2]⟩
  exact hpos.ne' (tendsto_nhds_unique h2 h)

/-- Zero variance about `θ`: by Corollary A2, `σ²_{μ,t}` does not converge to zero. -/
lemma not_tendsto_of_theta_known (κ : ℝ) (hκ : κck < κ) (S₁ : M2) (hS : S₁.PosSemidef)
    (γ : ℕ → ℝ) (h0 : S₁ 0 0 = 0) (h1 : 0 < S₁ 1 1) :
    ¬ Tendsto (fun t => SigmaSeq (fun _ => κ) S₁ γ t 1 1) atTop (𝓝 0) := by
  have h01 := off_zero_of_left hS h0
  have h10 : S₁ 1 0 = 0 := (sym_of_psd hS).trans h01
  have hS' : S₁ = !![0, 0; 0, S₁ 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h0, h01, h10]
  rw [hS']
  have h := (corollaryA2 (S₁ 1 1) h1).1 κ (lt_trans κck_pos hκ) γ
  rw [h]
  exact not_le.2 hκ

/-- **Proposition 3 (1).** When `κ > κck`, an individual-oriented intervention (any noise
variance, including perfect revelation of `θ`) never results in social learning about `μ`, and a
peer-oriented intervention never results in social learning about `θ`, whatever the later
weights `γ_t ∈ [0,1]`. When the post-intervention beliefs are nondegenerate this is Proposition 2
from the intervention date onward. If an individual-oriented intervention leaves zero variance
about `θ`, it is Corollary A2. A peer-oriented intervention that leaves zero variance about `μ` is
covered by the first step of Case 1 of Proposition 2, which does not use `Σ₁ ≻ 0`. -/
theorem prop3_1 (κ : ℝ) (hκ : κck < κ) (S : M2) (hS : S.PosDef) (n : ℝ) (hn : 0 ≤ n)
    (γ : ℕ → ℝ) (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) :
    ¬ Tendsto (fun t => SigmaSeq (fun _ => κ) (observeTheta S n) γ t 1 1) atTop (𝓝 0) ∧
    ¬ Tendsto (fun t => SigmaSeq (fun _ => κ) (observeMu S n) γ t 0 0) atTop (𝓝 0) := by
  obtain ⟨h1, h1'⟩ := observeTheta_props hS hn
  obtain ⟨h2, h2'⟩ := observeMu_props hS hn
  refine ⟨?_, not_tendsto_zero_of_pos κ hκ _ h2 γ hγ 0 h2'⟩
  rcases hn.eq_or_lt with rfl | hn'
  · obtain ⟨-, h0, -, -⟩ := entries_of_posDef hS
    refine not_tendsto_of_theta_known κ hκ _ h1 γ ?_ h1'
    rw [observeTheta_apply, add_zero]
    field_simp
    ring
  · exact not_tendsto_zero_of_pos κ hκ _ h1 γ hγ 1 h1'

lemma sensDiag_nonneg (γ x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ sensDiag γ x y :=
  div_nonneg (by linarith) (sensDiag_den_pos γ x y hx hy).le

/-- **Proposition 3 (2), individual-oriented.** At zero correlation and `κ > κck`, a pooling
equilibrium is never fragile to an individual-oriented intervention. -/
theorem prop3_2_individual (κ : ℝ) (hκ : κck < κ) (x y γ : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ¬ periodRevealing κ !![x, 0; 0, y] γ →
      ¬ periodRevealing κ (observeTheta !![x, 0; 0, y] 1) γ := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  have hx' : 0 ≤ x / (1 + x) := by positivity
  rw [periodRevealing_iff (psd_diag x y hx hy) hκ0, observeTheta_diag x y hx,
    periodRevealing_iff (psd_diag _ y hx' hy) hκ0, revCrit, revCrit,
    sens_diag γ x y hx hy, sens_diag γ _ y hx' hy]
  intro hpre hpost
  apply hpre
  have hle : x / (1 + x) ≤ x := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hmono := sensDiag_anti_x γ y hy hx' hle
  have h0 := sensDiag_nonneg γ x y hx hy
  have : sensDiag γ x y ^ 2 ≤ sensDiag γ (x / (1 + x)) y ^ 2 := pow_le_pow_left₀ h0 hmono 2
  nlinarith [mul_le_mul_of_nonneg_left this hκ0.le]

/-- **Proposition 3 (2), peer-oriented.** At zero correlation and `κ > κck`, the equilibrium may be
fragile to a peer-oriented intervention: for every `σ²_μ > 0` and `γ > 0` there is `σ²_θ > 0`
such that the period is pooling before and revealing after the intervention. As `σ²_θ` rises from
`0` to `∞`, the sensitivities fall continuously from `1` to `0`, and the sensitivity after the
intervention is strictly lower (Lemma 2), so `σ²_θ` can be chosen with
`s̃_post ≤ c_κ < s̃_pre`. -/
theorem prop3_2_peer (κ : ℝ) (hκ : κck < κ) (y γ : ℝ) (hy : 0 < y) (hγ : 0 < γ) :
    ∃ x : ℝ, 0 < x ∧ ¬ periodRevealing κ !![x, 0; 0, y] γ ∧
      periodRevealing κ (observeMu !![x, 0; 0, y] 1) γ := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  -- `c_κ = √(κck/κ) ∈ (0,1)`
  set c := √(κck / κ) with hc
  have hq0 : 0 < κck / κ := div_pos κck_pos hκ0
  have hq1 : κck / κ < 1 := (div_lt_one hκ0).2 hκ
  have hc0 : 0 < c := Real.sqrt_pos.2 hq0
  have hc1 : c < 1 := by
    rw [hc, Real.sqrt_lt' one_pos]; simpa using hq1
  have hcsq : c ^ 2 = κck / κ := Real.sq_sqrt hq0.le
  set y' := y / (1 + y) with hy'
  have hy'0 : 0 ≤ y' := by positivity
  have hy'y : y' < y := by
    rw [hy', div_lt_iff₀ (by positivity)]; nlinarith
  -- the post-intervention sensitivity falls continuously from `1` to `0`
  have hcont : ContinuousOn (fun x => sensDiag γ x y') (Ici 0) := fun x hx =>
    (sensDiag_hasDerivAt γ x y' hx hy'0).2.continuousAt.continuousWithinAt
  obtain ⟨X, hXc, hX0⟩ := ((sensDiag_tendsto_zero γ y' hγ.ne' hy'0).eventually
    (gt_mem_nhds hc0) |>.and (eventually_ge_atTop (0 : ℝ))).exists
  obtain ⟨x, hx, hxc'⟩ := intermediate_value_Icc' hX0 (hcont.mono Icc_subset_Ici_self)
    (show c ∈ Icc (sensDiag γ X y') (sensDiag γ 0 y') from
      ⟨hXc.le, by rw [sensDiag_zero γ y' hy'0]; exact hc1.le⟩)
  have hxc : sensDiag γ x y' = c := hxc'
  have hx0 : 0 < x := by
    rcases hx.1.eq_or_lt with h | h
    · rw [← h, sensDiag_zero γ y' hy'0] at hxc
      linarith
    · exact h
  -- by Lemma 2 the sensitivity before the intervention is strictly larger
  have hgt : c < sensDiag γ x y := by
    rw [← hxc]
    exact sensDiag_strictMono_y γ x hγ.ne' hx0 hy'0 hy'y
  refine ⟨x, hx0, ?_, ?_⟩
  · rw [periodRevealing_iff (psd_diag x y hx0.le hy.le) hκ0, revCrit,
      sens_diag γ x y hx0.le hy.le]
    intro hle
    have : c ^ 2 < sensDiag γ x y ^ 2 := pow_lt_pow_left₀ hgt hc0.le two_ne_zero
    rw [hcsq] at this
    have := mul_lt_mul_of_pos_left this hκ0
    rw [mul_div_cancel₀ _ hκ0.ne'] at this
    linarith
  · rw [observeMu_diag x y hy.le, ← hy',
      periodRevealing_iff (psd_diag x y' hx0.le hy'0) hκ0, revCrit,
      sens_diag γ x y' hx0.le hy'0, hxc, hcsq, mul_div_cancel₀ _ hκ0.ne']

end CC
