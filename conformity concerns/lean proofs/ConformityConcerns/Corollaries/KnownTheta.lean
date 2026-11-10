import ConformityConcerns.PeriodGame.Instance
import ConformityConcerns.Interventions.DiagFacts
import ConformityConcerns.Dynamics.Lemmas

/-!
# Corollary A2 (Signaling equilibrium with `θ` known, `σ_θ = 0`)

The core model with `Σ₁ = diag(0, σ²_μ)`. At date `t` the expected adaptation payoff
`E(-(a_t - γ_t θ - v_t)²)` and expected utility `E(u_t)` of the signaling equilibrium are those of
the period game `gameAt m_t Σ_t γ_t κ` (they depend on the history only through `Σ_t`, so any
means `m_t` may be used). Social learning about preferences: `σ²_{μ,t} → 0`.
-/

namespace CC

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix

namespace CorA2

/-! ### Values of a signaling equilibrium of the period game -/

/-- The expected adaptation payoff of a signaling equilibrium (from `signalingEq_char`). -/
lemma exAdapt_eq {Ω : Type*} [MeasurableSpace Ω] (G : LG.Game Ω) (hG : G.Std)
    {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsSignalingEq a φ) :
    G.exAdapt a = -((if G.κ * G.sens ^ 2 ≤ κck then ((1 - √(1 - 4 * G.κ * G.sens ^ 2)) / 2) ^ 2
      else 1) * variance G.Z G.P) - G.c0 := by
  obtain ⟨h1, h2, -⟩ := LG.signalingEq_char G hG hE
  have hZ : AEMeasurable G.Z G.P := hG.gauss.fst.aemeasurable
  unfold LG.Game.exAdapt
  rw [variance_eq_integral hZ]
  split_ifs with h
  · have hae := h1 h
    have key : ∫ ω, (a ω - G.Z ω) ^ 2 ∂G.P =
        ((1 - √(1 - 4 * G.κ * G.sens ^ 2)) / 2) ^ 2 * ∫ ω, (G.Z ω - ∫ ω', G.Z ω' ∂G.P) ^ 2 ∂G.P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hae] with ω hω
      rw [hω]; simp only [LG.Game.meanZ]; ring
    rw [key]
  · have hae := h2 (lt_of_not_ge h)
    have key : ∫ ω, (a ω - G.Z ω) ^ 2 ∂G.P = ∫ ω, (G.Z ω - ∫ ω', G.Z ω' ∂G.P) ^ 2 ∂G.P := by
      apply integral_congr_ae
      filter_upwards [hae] with ω hω
      rw [hω]; simp only [LG.Game.meanZ]; ring
    rw [key, one_mul]

/-- The expected utility of a signaling equilibrium (from `signalingEq_char`). -/
lemma exUtility_eq {Ω : Type*} [MeasurableSpace Ω] (G : LG.Game Ω) (hG : G.Std)
    {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsSignalingEq a φ) :
    G.exUtility a φ = -((if G.κ * G.sens ^ 2 ≤ κck then ((1 - √(1 - 4 * G.κ * G.sens ^ 2)) / 2) ^ 2
      else 1) * variance G.Z G.P + G.κ * variance G.v G.P) - G.c0 := by
  obtain ⟨-, -, h3⟩ := LG.signalingEq_char G hG hE
  unfold LG.Game.exUtility
  rw [h3, ENNReal.toReal_ofReal]
  refine add_nonneg (mul_nonneg ?_ (variance_nonneg _ _))
    (mul_nonneg hG.κ_pos.le (variance_nonneg _ _))
  split_ifs <;> positivity

/-! ### The period game at `Σ = diag(0, y)` -/

lemma sens_eq_one (y γ : ℝ) (hy : 0 ≤ y) : sens !![0, 0; 0, y] γ = 1 := by
  rw [sens_diag γ 0 y le_rfl hy, sensDiag]
  have : (1 + y) ≠ 0 := by positivity
  simp [this]

lemma varZ_eq' (y γ : ℝ) (hy : 0 ≤ y) : varZ !![0, 0; 0, y] γ = 1 + y := by
  rw [varZ_eq (psd_diag 0 y le_rfl hy), Vt_diag, Ct_diag, Ht_diag 0 y le_rfl hy]
  simp

lemma postVar_eq (y : ℝ) (hy : 0 ≤ y) : postVarθ !![0, 0; 0, y] = 0 := by
  rw [postVarθ, gainK_diag 0 y le_rfl hy]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma kalman_eq (y γ : ℝ) (hy : 0 ≤ y) :
    kalman !![0, 0; 0, y] γ = !![0, 0; 0, y / (1 + y)] := by
  have hy' : (1 + y) ≠ 0 := by positivity
  rw [kalman, varZ_eq' y γ hy]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [loadA, gainK_diag 0 y le_rfl hy, vecMulVec_apply]
  field_simp; ring

/-- The covariance process from `diag(0, σ)`. -/
lemma seq_eq (σ : ℝ) (hσ : 0 < σ) (κ : ℝ) (hκ : 0 < κ) (γ : ℕ → ℝ) (t : ℕ) :
    SigmaSeq (fun _ => κ) !![0, 0; 0, σ] γ t =
      !![0, 0; 0, if κ ≤ κck then σ / (1 + t * σ) else σ] := by
  induction t with
  | zero => split_ifs <;> simp [SigmaSeq]
  | succ t ih =>
    have hy : 0 ≤ (if κ ≤ κck then σ / (1 + t * σ) else σ) := by split_ifs <;> positivity
    rw [SigmaSeq, ih]
    rw [periodRevealing_iff (psd_diag 0 _ le_rfl hy) hκ, revCrit, sens_eq_one _ _ hy, one_pow,
      mul_one]
    by_cases h : κ ≤ κck
    · rw [ite_eq_left h, kalman_eq _ _ hy]
      simp only [ite_eq_left h]
      have h1 : (1 + t * σ) ≠ 0 := by positivity
      have h2 : (1 + (t + 1 : ℕ) * σ) ≠ 0 := by positivity
      ext i j; fin_cases i <;> fin_cases j <;> simp
      field_simp; ring
    · rw [ite_eq_right h]
      simp only [ite_eq_right h]

lemma tendsto_seq (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun t : ℕ => σ / (1 + t * σ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_left _ 1 (tendsto_natCast_atTop_atTop.atTop_mul_const hσ))

lemma sqrt_facts {κ : ℝ} (hκ : 0 < κ) (h : κ ≤ κck) :
    0 ≤ √(1 - 4 * κ) ∧ √(1 - 4 * κ) ≤ 1 ∧ √(1 - 4 * κ) ^ 2 = 1 - 4 * κ := by
  rw [κck_eq] at h
  refine ⟨Real.sqrt_nonneg _, ?_, Real.sq_sqrt (by linarith)⟩
  rw [Real.sqrt_le_one]; linarith

/-- With zero variance about `θ` and `κ > κck`, `s̃(h^t) = 1`, so no period is revealing and
`Σ_t` is constant (proof of Corollary A2). -/
lemma pool_of_theta_known {κ : ℝ} (hκ : κck < κ) {S₁ : M2} (hS : S₁.PosSemidef) (h0 : S₁ 0 0 = 0)
    (γ : ℕ → ℝ) (t : ℕ) :
    ¬ revCrit κ (SigmaC (fun _ => κ) S₁ γ t) (γ t) ∧ SigmaC (fun _ => κ) S₁ γ t = S₁ := by
  have h01 := off_zero_of_left hS h0
  have h10 : S₁ 1 0 = 0 := (sym_of_psd hS).trans h01
  have hS' : S₁ = !![0, 0; 0, S₁ 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h0, h01, h10]
  have hy : 0 ≤ S₁ 1 1 := (psd_PSDE hS).2.1
  have hnot : ∀ g, ¬ revCrit κ S₁ g := fun g h => by
    have h1 : κ * sens S₁ g ^ 2 ≤ κck := h
    rw [hS', sens_eq_one _ _ hy, one_pow, mul_one] at h1
    exact absurd h1 (not_le.2 hκ)
  induction t with
  | zero => exact ⟨hnot _, rfl⟩
  | succ t ih =>
    have heq : SigmaC (fun _ => κ) S₁ γ (t + 1) = S₁ := by
      rw [SigmaC_succ_pool _ _ _ ih.1, ih.2]
    exact ⟨by rw [heq]; exact hnot _, heq⟩

end CorA2

open CorA2 in
/-- **Corollary A2.** Social learning about preferences occurs iff `κ ≤ κck`. When `κ > κck`,
`lim σ²_{μ,t} = σ²_μ > 0`, independent of `κ`. The asymptotic adaptation loss
`AAL(κ) = -((1 - √(1-4κ))/2)²` (`κ ≤ κck`), `-(1 + σ²_μ)` (`κ > κck`) is weakly decreasing in
`κ`, and the asymptotic utility `AU(κ) = -(1 - √(1-4κ))/2` (`κ ≤ κck`),
`-(1 + κ)(1 + σ²_μ)` (`κ > κck`) is decreasing in `κ`. -/
theorem corollaryA2 (σμ2 : ℝ) (hσ : 0 < σμ2) :
    let S₁ : M2 := !![0, 0; 0, σμ2]
    let AAL : ℝ → ℝ := fun κ =>
      if κ ≤ κck then -((1 - √(1 - 4 * κ)) / 2) ^ 2 else -(1 + σμ2)
    let AU : ℝ → ℝ := fun κ =>
      if κ ≤ κck then -((1 - √(1 - 4 * κ)) / 2) else -((1 + κ) * (1 + σμ2))
    (∀ κ, 0 < κ → ∀ γ : ℕ → ℝ,
      (Tendsto (fun t => SigmaSeq (fun _ => κ) S₁ γ t 1 1) atTop (𝓝 0) ↔ κ ≤ κck)) ∧
    (∀ κ, κck < κ → ∀ γ : ℕ → ℝ, ∀ t, SigmaSeq (fun _ => κ) S₁ γ t 1 1 = σμ2) ∧
    AntitoneOn AAL (Ioi 0) ∧ StrictAntiOn AU (Ioi 0) ∧
    ∀ κ, 0 < κ → ∀ (γ : ℕ → ℝ) (m : ℕ → EuclideanSpace ℝ (Fin 2))
      (a : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ) (φ : ℕ → Kernel ℝ ℝ),
      (∀ t, (gameAt (m t) (SigmaSeq (fun _ => κ) S₁ γ t) (γ t) κ).IsSignalingEq (a t) (φ t)) →
      Tendsto (fun t => (gameAt (m t) (SigmaSeq (fun _ => κ) S₁ γ t) (γ t) κ).exAdapt (a t))
          atTop (𝓝 (AAL κ)) ∧
      Tendsto (fun t => (gameAt (m t) (SigmaSeq (fun _ => κ) S₁ γ t) (γ t) κ).exUtility (a t) (φ t))
          atTop (𝓝 (AU κ)) := by
  intro S₁ AAL AU
  -- the variance of `μ` at date `t`
  set y : ℝ → ℕ → ℝ := fun κ t => if κ ≤ κck then σμ2 / (1 + t * σμ2) else σμ2 with hydef
  have hy0 : ∀ κ t, 0 ≤ y κ t := fun κ t => by
    simp only [hydef]; split_ifs <;> positivity
  have hseq : ∀ κ, 0 < κ → ∀ γ t, SigmaSeq (fun _ => κ) S₁ γ t = !![0, 0; 0, y κ t] :=
    fun κ hκ γ t => seq_eq σμ2 hσ κ hκ γ t
  have hlim : ∀ κ, κ ≤ κck → Tendsto (y κ) atTop (𝓝 0) := fun κ h => by
    simpa [hydef, h] using tendsto_seq σμ2 hσ
  have hconst : ∀ κ, κck < κ → ∀ t, y κ t = σμ2 := fun κ h t => by
    simp [hydef, not_le.2 h]
  refine ⟨fun κ hκ γ => ?_, fun κ hκ γ t => ?_, ?_, ?_, ?_⟩
  · -- social learning iff `κ ≤ κck`
    have e : (fun t => SigmaSeq (fun _ => κ) S₁ γ t 1 1) = y κ := by
      funext t; rw [hseq κ hκ γ t]; simp
    rw [e]
    by_cases h : κ ≤ κck
    · exact iff_of_true (hlim κ h) h
    · refine iff_of_false (fun hc => ?_) h
      have e' : y κ = fun _ => σμ2 := funext (hconst κ (lt_of_not_ge h))
      rw [e'] at hc
      exact hσ.ne' (tendsto_nhds_unique tendsto_const_nhds hc)
  · have hκ0 : 0 < κ := lt_trans κck_pos hκ
    rw [hseq κ hκ0 γ t]; simp [hconst κ hκ t]
  · -- the asymptotic adaptation loss is weakly decreasing
    intro a ha b hb hab
    simp only [mem_Ioi] at ha hb
    simp only [AAL]
    by_cases hb' : b ≤ κck
    · have ha' : a ≤ κck := hab.trans hb'
      rw [ite_eq_left ha', ite_eq_left hb']
      obtain ⟨sa0, sa1, -⟩ := sqrt_facts ha ha'
      obtain ⟨sb0, sb1, -⟩ := sqrt_facts hb hb'
      have : √(1 - 4 * b) ≤ √(1 - 4 * a) := Real.sqrt_le_sqrt (by linarith)
      nlinarith
    · rw [ite_eq_right hb']
      by_cases ha' : a ≤ κck
      · rw [ite_eq_left ha']
        obtain ⟨sa0, sa1, -⟩ := sqrt_facts ha ha'
        nlinarith
      · rw [ite_eq_right ha']
  · -- the asymptotic utility is decreasing
    intro a ha b hb hab
    simp only [mem_Ioi] at ha hb
    simp only [AU]
    by_cases hb' : b ≤ κck
    · have ha' : a ≤ κck := hab.le.trans hb'
      rw [ite_eq_left ha', ite_eq_left hb']
      have : √(1 - 4 * b) < √(1 - 4 * a) := by
        rw [κck_eq] at hb'
        exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
      linarith
    · rw [ite_eq_right hb']
      by_cases ha' : a ≤ κck
      · rw [ite_eq_left ha']
        obtain ⟨sa0, sa1, -⟩ := sqrt_facts ha ha'
        nlinarith
      · rw [ite_eq_right ha']
        nlinarith
  · -- the asymptotic values
    intro κ hκ γ m a φ hE
    have hS : ∀ t, (SigmaSeq (fun _ => κ) S₁ γ t).PosSemidef := fun t => by
      rw [hseq κ hκ γ t]; exact psd_diag 0 _ le_rfl (hy0 κ t)
    have hA : ∀ t, (gameAt (m t) (SigmaSeq (fun _ => κ) S₁ γ t) (γ t) κ).exAdapt (a t) =
        -((if κ ≤ κck then ((1 - √(1 - 4 * κ)) / 2) ^ 2 else 1) * (1 + y κ t)) := fun t => by
      rw [exAdapt_eq _ (gameAt_std (hS t) hκ) (hE t), gameAt_sens (hS t),
        gameAt_variance_Z (hS t)]
      simp only [gameAt]
      rw [hseq κ hκ γ t, sens_eq_one _ _ (hy0 κ t), varZ_eq' _ _ (hy0 κ t),
        postVar_eq _ (hy0 κ t)]
      simp
    have hU : ∀ t, (gameAt (m t) (SigmaSeq (fun _ => κ) S₁ γ t) (γ t) κ).exUtility (a t) (φ t) =
        -((if κ ≤ κck then ((1 - √(1 - 4 * κ)) / 2) ^ 2 else 1) * (1 + y κ t) +
          κ * (1 + y κ t)) := fun t => by
      rw [exUtility_eq _ (gameAt_std (hS t) hκ) (hE t), gameAt_sens (hS t),
        gameAt_variance_Z (hS t), gameAt_variance_v (hS t)]
      simp only [gameAt]
      rw [hseq κ hκ γ t, sens_eq_one _ _ (hy0 κ t), varZ_eq' _ _ (hy0 κ t),
        postVar_eq _ (hy0 κ t), Vt_diag]
      simp
    simp only [hA, hU, AAL, AU]
    by_cases h : κ ≤ κck
    · simp only [ite_eq_left h]
      obtain ⟨-, -, s2⟩ := sqrt_facts hκ h
      have l1 := hlim κ h
      constructor
      · have := ((tendsto_const_nhds (x := (1 : ℝ))).add l1).const_mul
          (((1 - √(1 - 4 * κ)) / 2) ^ 2)
        simpa using this.neg
      · have := (((tendsto_const_nhds (x := (1 : ℝ))).add l1).const_mul
          (((1 - √(1 - 4 * κ)) / 2) ^ 2)).add
          (((tendsto_const_nhds (x := (1 : ℝ))).add l1).const_mul κ)
        convert this.neg using 2
        nlinarith
    · simp only [ite_eq_right h, hconst κ (lt_of_not_ge h)]
      constructor
      · simp
      · convert (tendsto_const_nhds (x := -((1 + κ) * (1 + σμ2)))) using 2; ring

end CC
