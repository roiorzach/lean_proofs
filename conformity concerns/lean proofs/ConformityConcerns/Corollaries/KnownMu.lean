import ConformityConcerns.PeriodGame.Instance
import ConformityConcerns.Interventions.DiagFacts
import ConformityConcerns.LearnTheta.GaussianM

/-!
# Corollary A3 (Signaling equilibrium with `μ` known, `σ_μ = 0`, and `γ_t = 1`)

The core model with `Σ₁ = diag(σ²_θ, 0)` and `γ_t = 1` for all `t`. Social learning about
fundamentals: `σ²_{θ,t} → 0`. As in the proof in the paper, the argument uses the closed form of
`m` (`LearnTheta/GaussianM.lean`) and Corollary 1: `m'' = 2 s̃²` is constant in `ṽ_t`, independent
of `θ(h^t)` and decreasing in `σ²_{θ,t}`.
-/

namespace CC

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix

namespace CorA3

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

/-! ### The period game at `Σ = diag(x, 0)` with `γ = 1` -/

/-- The sensitivity at `diag(x, 0)`, `γ = 1`. -/
noncomputable def s3 (x : ℝ) : ℝ := 1 / (1 + x ^ 2 / (1 + x))

/-- The variance of `θ` after a revealing period at `diag(x, 0)`, `γ = 1`. -/
noncomputable def fA (x : ℝ) : ℝ := x * (1 + 2 * x + 2 * x ^ 2) / (1 + 2 * x + 2 * x ^ 2 + x ^ 3)

/-- One step of the signaling-equilibrium dynamics of `σ²_θ` with concern `κ`. -/
noncomputable def stepA (κ x : ℝ) : ℝ := if κ * s3 x ^ 2 ≤ κck then fA x else x

lemma stepA_of_rev {κ x : ℝ} (h : κ * s3 x ^ 2 ≤ κck) : stepA κ x = fA x := by
  unfold stepA; exact ite_eq_left h

lemma stepA_of_pool {κ x : ℝ} (h : ¬ κ * s3 x ^ 2 ≤ κck) : stepA κ x = x := by
  unfold stepA; exact ite_eq_right h

lemma s3_pos (x : ℝ) (hx : 0 ≤ x) : 0 < s3 x := by unfold s3; positivity

lemma s3_le_one (x : ℝ) (hx : 0 ≤ x) : s3 x ≤ 1 := by
  unfold s3
  rw [div_le_one (by positivity)]
  have : 0 ≤ x ^ 2 / (1 + x) := by positivity
  linarith

lemma s3_zero : s3 0 = 1 := by simp [s3]

lemma sens_eq (x : ℝ) (hx : 0 ≤ x) : sens !![x, 0; 0, 0] 1 = s3 x := by
  rw [sens_diag 1 x 0 hx le_rfl, sensDiag, s3]; simp

/-- The closed form of `m` (with `σ_v² = 1`) has second derivative `2 s̃²`, constant in the type and
independent of the public mean of `θ`. -/
lemma second_deriv_m (x : ℝ) (hx : 0 ≤ x) (b z : ℝ) :
    iteratedDeriv 2 (LearnTheta.mfun (gaussianPDFReal 0 1)
      (gaussianReal b (LearnTheta.tauOf x.toNNReal))) z = 2 * s3 x ^ 2 := by
  rw [LearnTheta.mfun_gaussian_sens, Real.coe_toNNReal x hx, sens_eq x hx]

/-- By Corollary 1 and the closed form of `m`, the period is revealing iff `κ m''/2 ≤ κck`. -/
lemma rev_iff_m (κ : ℝ) (hκ : 0 < κ) (x : ℝ) (hx : 0 ≤ x) (b z : ℝ) :
    periodRevealing κ !![x, 0; 0, 0] 1 ↔
      κ * (iteratedDeriv 2 (LearnTheta.mfun (gaussianPDFReal 0 1)
        (gaussianReal b (LearnTheta.tauOf x.toNNReal))) z / 2) ≤ κck := by
  rw [periodRevealing_iff (psd_diag x 0 hx le_rfl) hκ, revCrit, second_deriv_m x hx b z,
    sens_eq x hx, mul_div_cancel_left₀ _ two_ne_zero]

lemma varZ_eq3 (x : ℝ) (hx : 0 ≤ x) : varZ !![x, 0; 0, 0] 1 = 1 + x ^ 2 / (1 + x) := by
  rw [varZ_eq (psd_diag x 0 hx le_rfl), Vt_diag, Ct_diag, Ht_diag x 0 hx le_rfl]; ring

lemma postVar_eq3 (x : ℝ) (hx : 0 ≤ x) : postVarθ !![x, 0; 0, 0] = x / (1 + x) := by
  have : (1 + x) ≠ 0 := by positivity
  rw [postVarθ, gainK_diag x 0 hx le_rfl]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp; ring

lemma kalman_eq3 (x : ℝ) (hx : 0 ≤ x) : kalman !![x, 0; 0, 0] 1 = !![fA x, 0; 0, 0] := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (1 + x ^ 2 / (1 + x)) ≠ 0 := by positivity
  have h3 : (1 + 2 * x + 2 * x ^ 2 + x ^ 3) ≠ 0 := by positivity
  have h4 : (1 + x + x ^ 2) ≠ 0 := by positivity
  rw [kalman, varZ_eq3 x hx]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [loadA, gainK_diag x 0 hx le_rfl, vecMulVec_apply, fA]
  field_simp; ring

lemma fA_pos (x : ℝ) (hx : 0 < x) : 0 < fA x := by unfold fA; positivity

lemma fA_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ fA x := by unfold fA; positivity

lemma fA_le (x : ℝ) (hx : 0 ≤ x) : fA x ≤ x := by
  unfold fA
  rw [div_le_iff₀ (by positivity)]
  nlinarith [pow_nonneg hx 4]

lemma fA_fixed (x : ℝ) (hx : 0 ≤ x) (h : fA x = x) : x = 0 := by
  unfold fA at h
  rw [div_eq_iff (by positivity)] at h
  have : x ^ 4 = 0 := by nlinarith
  exact pow_eq_zero_iff (n := 4) (by norm_num) |>.1 this

lemma fA_continuousAt (x : ℝ) (hx : 0 ≤ x) : ContinuousAt fA x := by
  have : (1 + 2 * x + 2 * x ^ 2 + x ^ 3) ≠ 0 := by positivity
  unfold fA
  fun_prop (disch := assumption)

lemma iterate_fA_nonneg (σ : ℝ) (hσ : 0 ≤ σ) (n : ℕ) : 0 ≤ fA^[n] σ := by
  induction n with
  | zero => simpa using hσ
  | succ n ih => rw [Function.iterate_succ_apply']; exact fA_nonneg _ ih

lemma iterate_fA_anti (σ : ℝ) (hσ : 0 ≤ σ) : Antitone (fun n => fA^[n] σ) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [Function.iterate_succ_apply']
  exact fA_le _ (iterate_fA_nonneg σ hσ n)

/-- Under revelation at every date, `σ²_θ → 0`. -/
lemma tendsto_iterate_fA (σ : ℝ) (hσ : 0 ≤ σ) : Tendsto (fun n => fA^[n] σ) atTop (𝓝 0) := by
  have hanti := iterate_fA_anti σ hσ
  have hbdd : BddBelow (range fun n => fA^[n] σ) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact iterate_fA_nonneg σ hσ n⟩
  have hT := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ n, fA^[n] σ
  have hL : 0 ≤ L := ge_of_tendsto' hT (fun n => iterate_fA_nonneg σ hσ n)
  have h1 : Tendsto (fun n => fA^[n + 1] σ) atTop (𝓝 L) := hT.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => fA^[n + 1] σ) atTop (𝓝 (fA L)) := by
    have := ((fA_continuousAt L hL).tendsto).comp hT
    refine this.congr fun n => ?_
    simp [Function.iterate_succ_apply']
  have := fA_fixed L hL (tendsto_nhds_unique h2 h1)
  rwa [this] at hT

lemma stepA_eq_of_le (κ : ℝ) (hκ : 0 < κ) (h : κ ≤ κck) (x : ℝ) (hx : 0 ≤ x) :
    stepA κ x = fA x := by
  apply stepA_of_rev
  have h0 := s3_pos x hx
  have h1 := s3_le_one x hx
  have : s3 x ^ 2 ≤ 1 := by nlinarith
  nlinarith

lemma iterate_stepA_of_le (κ : ℝ) (hκ : 0 < κ) (h : κ ≤ κck) (σ : ℝ) (hσ : 0 ≤ σ) (n : ℕ) :
    (stepA κ)^[n] σ = fA^[n] σ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      stepA_eq_of_le κ hκ h _ (iterate_fA_nonneg σ hσ n)]

lemma stepA_pos (κ x : ℝ) (hx : 0 < x) : 0 < stepA κ x := by
  by_cases h : κ * s3 x ^ 2 ≤ κck
  · rw [stepA_of_rev h]; exact fA_pos x hx
  · rw [stepA_of_pool h]; exact hx

lemma iterate_stepA_pos (κ σ : ℝ) (hσ : 0 < σ) (n : ℕ) : 0 < (stepA κ)^[n] σ := by
  induction n with
  | zero => simpa using hσ
  | succ n ih => rw [Function.iterate_succ_apply']; exact stepA_pos κ _ ih

/-- The covariance process from `diag(σ, 0)` with `γ_t = 1`. -/
lemma seq_eq (σ : ℝ) (hσ : 0 < σ) (κ : ℝ) (hκ : 0 < κ) (t : ℕ) :
    SigmaSeq (fun _ => κ) !![σ, 0; 0, 0] (fun _ => 1) t = !![(stepA κ)^[t] σ, 0; 0, 0] := by
  induction t with
  | zero => simp [SigmaSeq]
  | succ t ih =>
    have hx := iterate_stepA_pos κ σ hσ t
    rw [SigmaSeq, ih, rev_iff_m κ hκ _ hx.le 0 0, second_deriv_m _ hx.le,
      mul_div_cancel_left₀ _ two_ne_zero, Function.iterate_succ_apply']
    by_cases h : κ * s3 ((stepA κ)^[t] σ) ^ 2 ≤ κck
    · rw [ite_eq_left h, stepA_of_rev h, kalman_eq3 _ hx.le]
    · rw [ite_eq_right h, stepA_of_pool h]

/-- Comparison of the dynamics for two concerns `a ≤ b`: both are iterates of `fA`, with weakly
fewer revealing dates for `b`. -/
lemma compare (σ : ℝ) (a b : ℝ) (hab : a ≤ b) (t : ℕ) :
    ∃ n m : ℕ, m ≤ n ∧ (stepA a)^[t] σ = fA^[n] σ ∧ (stepA b)^[t] σ = fA^[m] σ := by
  induction t with
  | zero => exact ⟨0, 0, le_rfl, rfl, rfl⟩
  | succ t ih =>
    obtain ⟨n, m, hmn, ha, hb⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ha, hb]
    have fs : ∀ k, fA (fA^[k] σ) = fA^[k + 1] σ := fun k => (Function.iterate_succ_apply' _ _ _).symm
    by_cases hbR : b * s3 (fA^[m] σ) ^ 2 ≤ κck
    · rw [stepA_of_rev hbR]
      rcases eq_or_lt_of_le hmn with heq | hlt
      · subst heq
        have haR : a * s3 (fA^[m] σ) ^ 2 ≤ κck :=
          le_trans (mul_le_mul_of_nonneg_right hab (sq_nonneg _)) hbR
        rw [stepA_of_rev haR]
        exact ⟨m + 1, m + 1, le_rfl, fs m, fs m⟩
      · by_cases haR : a * s3 (fA^[n] σ) ^ 2 ≤ κck
        · rw [stepA_of_rev haR]; exact ⟨n + 1, m + 1, by omega, fs n, fs m⟩
        · rw [stepA_of_pool haR]; exact ⟨n, m + 1, hlt, rfl, fs m⟩
    · rw [stepA_of_pool hbR]
      by_cases haR : a * s3 (fA^[n] σ) ^ 2 ≤ κck
      · rw [stepA_of_rev haR]; exact ⟨n + 1, m, by omega, fs n, rfl⟩
      · rw [stepA_of_pool haR]; exact ⟨n, m, hmn, rfl, rfl⟩

lemma iterate_stepA_mono (σ : ℝ) (hσ : 0 ≤ σ) (a b : ℝ) (hab : a ≤ b) (t : ℕ) :
    (stepA a)^[t] σ ≤ (stepA b)^[t] σ := by
  obtain ⟨n, m, hmn, ha, hb⟩ := compare σ a b hab t
  rw [ha, hb]
  exact iterate_fA_anti σ hσ hmn

/-- For `κ > κck` the dynamics is eventually pooling and constant: if every date were revealing,
`σ²_θ → 0` and the sensitivity would tend to `1`, violating the revealing criterion; and once a date
pools, the state and hence the criterion stay the same. -/
lemma eventually_pool (σ : ℝ) (hσ : 0 < σ) (κ : ℝ) (hκ : κck < κ) :
    ∃ T, ∀ t, T ≤ t → ¬ (κ * s3 ((stepA κ)^[t] σ) ^ 2 ≤ κck) ∧
      (stepA κ)^[t] σ = (stepA κ)^[T] σ := by
  have hB : ∃ T, ¬ (κ * s3 ((stepA κ)^[T] σ) ^ 2 ≤ κck) := by
    by_contra hcon
    push Not at hcon
    have he : ∀ t, (stepA κ)^[t] σ = fA^[t] σ := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
          stepA_of_rev (hcon t)]
    have hl : Tendsto (fun t => (stepA κ)^[t] σ) atTop (𝓝 0) := by
      simp_rw [he]; exact tendsto_iterate_fA σ hσ.le
    have hc : ContinuousAt (fun x : ℝ => κ * (1 / (1 + x ^ 2 / (1 + x))) ^ 2) 0 := by
      fun_prop (disch := norm_num)
    have hl2 := hc.tendsto.comp hl
    have hval : κ * (1 / (1 + (0 : ℝ) ^ 2 / (1 + 0))) ^ 2 = κ := by norm_num
    rw [hval] at hl2
    obtain ⟨t, ht⟩ := (hl2.eventually (lt_mem_nhds hκ)).exists
    exact absurd (hcon t) (not_le.2 (by simpa [Function.comp_def, s3] using ht))
  obtain ⟨T, hT⟩ := hB
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact ⟨hT, rfl⟩
  | succ t hle ih =>
    have hstep : (stepA κ)^[t + 1] σ = (stepA κ)^[t] σ := by
      rw [Function.iterate_succ_apply', stepA_of_pool ih.1]
    rw [hstep]; exact ih

/-- The period values at `diag(x, 0)` with `γ = 1`. -/
lemma values (κ : ℝ) (hκ : 0 < κ) (m : EuclideanSpace ℝ (Fin 2)) (x : ℝ) (hx : 0 ≤ x)
    (a : EuclideanSpace ℝ (Fin 2) → ℝ) (φ : Kernel ℝ ℝ)
    (hE : (gameAt m !![x, 0; 0, 0] 1 κ).IsSignalingEq a φ) :
    (gameAt m !![x, 0; 0, 0] 1 κ).exAdapt a =
      -((if κ * s3 x ^ 2 ≤ κck then ((1 - √(1 - 4 * κ * s3 x ^ 2)) / 2) ^ 2 else 1) *
        (1 + x ^ 2 / (1 + x))) - x / (1 + x) ∧
    (gameAt m !![x, 0; 0, 0] 1 κ).exUtility a φ =
      -((if κ * s3 x ^ 2 ≤ κck then ((1 - √(1 - 4 * κ * s3 x ^ 2)) / 2) ^ 2 else 1) *
        (1 + x ^ 2 / (1 + x)) + κ) - x / (1 + x) := by
  have hS := psd_diag x 0 hx le_rfl
  constructor
  · rw [exAdapt_eq _ (gameAt_std hS hκ) hE, gameAt_sens hS, gameAt_variance_Z hS]
    simp only [gameAt]
    rw [sens_eq x hx, varZ_eq3 x hx, postVar_eq3 x hx, one_pow, one_mul]
    congr
  · rw [exUtility_eq _ (gameAt_std hS hκ) hE, gameAt_sens hS, gameAt_variance_Z hS,
      gameAt_variance_v hS]
    simp only [gameAt]
    rw [sens_eq x hx, varZ_eq3 x hx, postVar_eq3 x hx, Vt_diag, one_pow, one_mul, add_zero,
      mul_one]
    congr

lemma sqrt_facts {κ : ℝ} (hκ : 0 < κ) (h : κ ≤ κck) :
    0 ≤ √(1 - 4 * κ) ∧ √(1 - 4 * κ) ≤ 1 ∧ √(1 - 4 * κ) ^ 2 = 1 - 4 * κ := by
  rw [κck_eq] at h
  refine ⟨Real.sqrt_nonneg _, ?_, Real.sq_sqrt (by linarith)⟩
  rw [Real.sqrt_le_one]; linarith

/-- The date-`t` loss `E((a_t - θ - v_t)²)` at posterior variance `x` of `θ`. -/
noncomputable def adLoss (κ x : ℝ) : ℝ :=
  (if κ * s3 x ^ 2 ≤ κck then ((1 - √(1 - 4 * κ * s3 x ^ 2)) / 2) ^ 2 else 1) *
    (1 + x ^ 2 / (1 + x)) + x / (1 + x)

lemma stepA_le (κ x : ℝ) (hx : 0 ≤ x) : stepA κ x ≤ x := by
  by_cases h : κ * s3 x ^ 2 ≤ κck
  · rw [stepA_of_rev h]; exact fA_le x hx
  · rw [stepA_of_pool h]

lemma coef_le_one (κ x : ℝ) (hκ : 0 < κ) :
    (if κ * s3 x ^ 2 ≤ κck then ((1 - √(1 - 4 * κ * s3 x ^ 2)) / 2) ^ 2 else 1) ≤ 1 := by
  split_ifs with h
  · have h0 := Real.sqrt_nonneg (1 - 4 * κ * s3 x ^ 2)
    have h1 : √(1 - 4 * κ * s3 x ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith [mul_nonneg hκ.le (sq_nonneg (s3 x))]
    nlinarith
  · exact le_rfl

/-- At the same posterior variance, a higher `κ` gives a weakly higher date-`t` loss. -/
lemma adLoss_mono_kappa {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 ≤ x) :
    adLoss a x ≤ adLoss b x := by
  unfold adLoss
  have hτ : 0 ≤ 1 + x ^ 2 / (1 + x) := by positivity
  refine add_le_add_left (mul_le_mul_of_nonneg_right ?_ hτ) _
  have hs := sq_nonneg (s3 x)
  by_cases hb : b * s3 x ^ 2 ≤ κck
  · have ha' : a * s3 x ^ 2 ≤ κck := (mul_le_mul_of_nonneg_right hab hs).trans hb
    rw [ite_eq_left hb, ite_eq_left ha']
    have h1 : √(1 - 4 * b * s3 x ^ 2) ≤ √(1 - 4 * a * s3 x ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have h0 := Real.sqrt_nonneg (1 - 4 * b * s3 x ^ 2)
    have h2 : √(1 - 4 * a * s3 x ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith [mul_nonneg ha.le hs]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  · rw [ite_eq_right hb]
    exact coef_le_one a x ha

/-- Monotonicity of `x ↦ 1 + x²/(1+x)` and of `x ↦ x/(1+x)`. -/
lemma pool_loss_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (1 + x ^ 2 / (1 + x)) + x / (1 + x) ≤ (1 + y ^ 2 / (1 + y)) + y / (1 + y) := by
  have hy : 0 ≤ y := hx.trans hxy
  have e : ∀ z : ℝ, 0 ≤ z → (1 + z ^ 2 / (1 + z)) + z / (1 + z) = 1 + z := fun z hz => by
    have : (1 + z) ≠ 0 := by positivity
    field_simp
    ring
  rw [e x hx, e y hy]
  linarith

/-- Pooling is absorbing, so for `a ≤ b` the two paths of `σ²_θ` agree until `b` first pools. After
that date `b` pools at every date and its variance is weakly higher. -/
lemma path_compare (σ : ℝ) (hσ : 0 < σ) {a b : ℝ} (hab : a ≤ b) (t : ℕ) :
    (stepA a)^[t] σ = (stepA b)^[t] σ ∨
      ((stepA a)^[t] σ ≤ (stepA b)^[t] σ ∧ ¬ (b * s3 ((stepA b)^[t] σ) ^ 2 ≤ κck)) := by
  induction t with
  | zero => exact Or.inl rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hxa := iterate_stepA_pos a σ hσ t
    rcases ih with heq | ⟨hle, hpool⟩
    · by_cases hb : b * s3 ((stepA b)^[t] σ) ^ 2 ≤ κck
      · have ha : a * s3 ((stepA a)^[t] σ) ^ 2 ≤ κck := by
          rw [heq]
          exact (mul_le_mul_of_nonneg_right hab (sq_nonneg _)).trans hb
        left
        rw [stepA_of_rev ha, stepA_of_rev hb, heq]
      · right
        rw [stepA_of_pool hb, ← heq]
        exact ⟨stepA_le a _ hxa.le, by rwa [heq]⟩
    · right
      rw [stepA_of_pool hpool]
      exact ⟨(stepA_le a _ hxa.le).trans hle, hpool⟩

/-- A higher `κ` implies weakly fewer periods of revelation and a weakly higher
`E((a_t - θ - v_t)²)` in every period. -/
lemma adLoss_mono_path (σ : ℝ) (hσ : 0 < σ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℕ) :
    adLoss a ((stepA a)^[t] σ) ≤ adLoss b ((stepA b)^[t] σ) := by
  rcases path_compare σ hσ hab t with heq | ⟨hle, hpool⟩
  · rw [heq]
    exact adLoss_mono_kappa ha hab (iterate_stepA_pos b σ hσ t).le
  · have hxa := iterate_stepA_pos a σ hσ t
    have hτ : 0 ≤ 1 + ((stepA a)^[t] σ) ^ 2 / (1 + (stepA a)^[t] σ) := by positivity
    calc adLoss a ((stepA a)^[t] σ)
        ≤ 1 * (1 + ((stepA a)^[t] σ) ^ 2 / (1 + (stepA a)^[t] σ)) +
            (stepA a)^[t] σ / (1 + (stepA a)^[t] σ) := by
          unfold adLoss
          exact add_le_add_left (mul_le_mul_of_nonneg_right (coef_le_one a _ ha) hτ) _
      _ ≤ adLoss b ((stepA b)^[t] σ) := by
          unfold adLoss
          rw [ite_eq_right hpool, one_mul, one_mul]
          exact pool_loss_mono hxa.le hle

end CorA3

open CorA3 in
/-- **Corollary A3.** Suppose `γ_t = 1` for all `t`. Social learning about fundamentals occurs iff
`κ ≤ κck`. When `κ > κck` the asymptotic variance `lim σ²_{θ,t} > 0` is weakly increasing in `κ`.
The asymptotic adaptation loss is weakly decreasing in `κ` and the asymptotic utility is
decreasing in `κ`. -/
theorem corollaryA3 (σθ2 : ℝ) (hσ : 0 < σθ2) :
    let S₁ : M2 := !![σθ2, 0; 0, 0]
    let Sg : ℝ → ℕ → M2 := fun κ => SigmaSeq (fun _ => κ) S₁ (fun _ => 1)
    (∀ κ, 0 < κ → (Tendsto (fun t => Sg κ t 0 0) atTop (𝓝 0) ↔ κ ≤ κck)) ∧
    (∃ q : ℝ → ℝ, MonotoneOn q (Ioi κck) ∧
      ∀ κ, κck < κ → 0 < q κ ∧ Tendsto (fun t => Sg κ t 0 0) atTop (𝓝 (q κ))) ∧
    ∃ AAL AU : ℝ → ℝ, AntitoneOn AAL (Ioi 0) ∧ StrictAntiOn AU (Ioi 0) ∧
      ∀ κ, 0 < κ → ∀ (m : ℕ → EuclideanSpace ℝ (Fin 2))
        (a : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ) (φ : ℕ → Kernel ℝ ℝ),
        (∀ t, (gameAt (m t) (Sg κ t) 1 κ).IsSignalingEq (a t) (φ t)) →
        Tendsto (fun t => (gameAt (m t) (Sg κ t) 1 κ).exAdapt (a t)) atTop (𝓝 (AAL κ)) ∧
        Tendsto (fun t => (gameAt (m t) (Sg κ t) 1 κ).exUtility (a t) (φ t)) atTop (𝓝 (AU κ)) := by
  intro S₁ Sg
  -- the variance of `θ` at date `t`
  set xs : ℝ → ℕ → ℝ := fun κ t => (stepA κ)^[t] σθ2 with hxs
  have hxpos : ∀ κ t, 0 < xs κ t := fun κ t => iterate_stepA_pos κ σθ2 hσ t
  have hseq : ∀ κ, 0 < κ → ∀ t, Sg κ t = !![xs κ t, 0; 0, 0] :=
    fun κ hκ t => seq_eq σθ2 hσ κ hκ t
  have hentry : ∀ κ, 0 < κ → (fun t => Sg κ t 0 0) = xs κ := fun κ hκ => by
    funext t; rw [hseq κ hκ t]; simp
  have hlow : ∀ κ, 0 < κ → κ ≤ κck → Tendsto (xs κ) atTop (𝓝 0) := fun κ hκ h => by
    have e : xs κ = fun t => fA^[t] σθ2 :=
      funext fun t => iterate_stepA_of_le κ hκ h σθ2 hσ.le t
    rw [e]; exact tendsto_iterate_fA σθ2 hσ.le
  -- the limit for `κ > κck`
  have hhigh : ∀ κ, κck < κ → ∃ T, (∀ t, T ≤ t → ¬ (κ * s3 (xs κ t) ^ 2 ≤ κck) ∧
      xs κ t = xs κ T) ∧ Tendsto (xs κ) atTop (𝓝 (xs κ T)) := fun κ h => by
    obtain ⟨T, hT⟩ := eventually_pool σθ2 hσ κ h
    refine ⟨T, hT, tendsto_const_nhds.congr' ?_⟩
    rw [EventuallyEq, eventually_atTop]
    exact ⟨T, fun t ht => (hT t ht).2.symm⟩
  set q : ℝ → ℝ := fun κ => limUnder atTop (xs κ) with hqdef
  have hq : ∀ κ, κck < κ → 0 < q κ ∧ Tendsto (xs κ) atTop (𝓝 (q κ)) := fun κ h => by
    obtain ⟨T, -, hT⟩ := hhigh κ h
    have hl : Tendsto (xs κ) atTop (𝓝 (q κ)) := tendsto_nhds_limUnder ⟨_, hT⟩
    refine ⟨?_, hl⟩
    rw [tendsto_nhds_unique hl hT]; exact hxpos κ T
  have hqmono : MonotoneOn q (Ioi κck) := by
    intro a ha b hb hab
    exact le_of_tendsto_of_tendsto' (hq a ha).2 (hq b hb).2
      (fun t => iterate_stepA_mono σθ2 hσ.le a b hab t)
  refine ⟨fun κ hκ => ?_, ⟨q, hqmono, fun κ h => ?_⟩, ?_⟩
  · -- social learning iff `κ ≤ κck`
    rw [hentry κ hκ]
    by_cases h : κ ≤ κck
    · exact iff_of_true (hlow κ hκ h) h
    · refine iff_of_false (fun hc => ?_) h
      have := (hq κ (lt_of_not_ge h))
      exact this.1.ne' (tendsto_nhds_unique this.2 hc)
  · rw [hentry κ (lt_trans κck_pos h)]; exact hq κ h
  -- the asymptotic values
  set r : ℝ → ℝ := fun κ => (1 - √(1 - 4 * κ)) / 2 with hr
  set AAL : ℝ → ℝ := fun κ => if κ ≤ κck then -(r κ ^ 2) else -(1 + q κ) with hAAL
  -- the date-`t` loss converges to the asymptotic adaptation loss
  have hAL : ∀ κ, 0 < κ → Tendsto (fun t => -adLoss κ (xs κ t)) atTop (𝓝 (AAL κ)) := by
    intro κ hκ
    by_cases h : κ ≤ κck
    · simp only [hAAL, ite_eq_left h]
      -- revealing at every date
      have hrev : ∀ t, κ * s3 (xs κ t) ^ 2 ≤ κck := fun t => by
        have h0 := s3_pos _ (hxpos κ t).le
        have h1 := s3_le_one _ (hxpos κ t).le
        have : s3 (xs κ t) ^ 2 ≤ 1 := by nlinarith
        nlinarith
      have hl := hlow κ hκ h
      have hcA : ContinuousAt (fun x : ℝ => -(((1 - √(1 - 4 * κ * (1 / (1 + x ^ 2 / (1 + x))) ^ 2))
          / 2) ^ 2 * (1 + x ^ 2 / (1 + x))) - x / (1 + x)) 0 := by
        fun_prop (disch := norm_num)
      have := hcA.tendsto.comp hl
      simp only [Function.comp_def] at this
      convert this using 1
      · funext t
        unfold adLoss
        rw [ite_eq_left (hrev t), neg_add']
        rfl
      · simp [hr]
    · simp only [hAAL, ite_eq_right h]
      obtain ⟨T, hT, hT'⟩ := hhigh κ (lt_of_not_ge h)
      have hqT : q κ = xs κ T := tendsto_nhds_unique (hq κ (lt_of_not_ge h)).2 hT'
      have hpos := hxpos κ T
      have h1x : (1 + xs κ T) ≠ 0 := by positivity
      refine tendsto_const_nhds.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      refine ⟨T, fun t ht => ?_⟩
      unfold adLoss
      rw [ite_eq_right (hT t ht).1, (hT t ht).2, hqT]
      field_simp
      ring
  -- the asymptotic utility differs from the asymptotic adaptation loss by the conformity loss
  have hAU : ∀ κ, 0 < κ → (if κ ≤ κck then -(r κ) else -(1 + q κ + κ)) = AAL κ - κ := by
    intro κ hκ
    by_cases h : κ ≤ κck
    · simp only [hAAL, ite_eq_left h, hr]
      obtain ⟨-, -, s2⟩ := sqrt_facts hκ h
      nlinarith
    · simp only [hAAL, ite_eq_right h]
      ring
  have hanti : AntitoneOn AAL (Ioi 0) := fun a ha b hb hab =>
    le_of_tendsto_of_tendsto' (hAL b hb) (hAL a ha) fun t =>
      neg_le_neg (adLoss_mono_path σθ2 hσ ha hab t)
  refine ⟨AAL, fun κ => if κ ≤ κck then -(r κ) else -(1 + q κ + κ), hanti, ?_, ?_⟩
  · -- the asymptotic utility is decreasing
    intro a ha b hb hab
    simp only
    rw [hAU a ha, hAU b hb]
    have := hanti ha hb hab.le
    linarith
  · intro κ hκ m a φ hE
    have hV : ∀ t, (gameAt (m t) (Sg κ t) 1 κ).exAdapt (a t) = -adLoss κ (xs κ t) ∧
        (gameAt (m t) (Sg κ t) 1 κ).exUtility (a t) (φ t) = -adLoss κ (xs κ t) - κ := by
      intro t
      have hEt := hE t
      rw [hseq κ hκ t] at hEt ⊢
      have := values κ hκ (m t) (xs κ t) (hxpos κ t).le (a t) (φ t) hEt
      unfold adLoss
      exact ⟨by rw [this.1]; ring, by rw [this.2]; ring⟩
    refine ⟨?_, ?_⟩
    · simp only [(hV _).1]
      exact hAL κ hκ
    · simp only [(hV _).2]
      rw [hAU κ hκ]
      exact (hAL κ hκ).sub_const κ

end CC
