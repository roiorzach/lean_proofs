import ConformityConcerns.PeriodGame.Revealing

/-!
# Proposition 1 (Commonly Known Environment)

With `θ` and `μ` common knowledge (both `0`), the type is `v ~ N(0,1)`, `Z = v` and `c0 = 0`.
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The common-knowledge period game: `v ~ N(0,1)`, `Z = v`, `c0 = 0`. -/
noncomputable def ckGame (κ : ℝ) : Game ℝ where
  P := gaussianReal 0 1
  Z := id
  v := id
  κ := κ
  c0 := 0


namespace Game

variable {Ω : Type*} [MeasurableSpace Ω] {G : Game Ω}

/-- In a pooling equilibrium on `c`, the belief after `c` is the prior law of `v`. -/
lemma Std.pool_belief (hG : G.Std) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsPBE a φ) {c : ℝ}
    (ha : a =ᵐ[G.P] fun _ => c) : φ c = G.P.map G.v := by
  have := hG.prob
  have := hE.markov
  have h1 : G.P.map a = Measure.dirac c := by
    rw [Measure.map_congr ha, Measure.map_const, measure_univ, one_smul]
  have h2 : G.P.map (fun ω => (a ω, G.v ω)) = G.P.map (fun ω => (c, G.v ω)) :=
    Measure.map_congr (ha.mono fun ω hω => by simp only at hω ⊢; rw [hω])
  have hb := hE.bayes
  rw [h1, h2] at hb
  ext B hB
  have := congrArg (fun μ : Measure (ℝ × ℝ) => μ (univ ×ˢ B)) hb
  rw [Measure.dirac_compProd_apply (MeasurableSet.univ.prod hB),
    Measure.map_apply_of_aemeasurable (aemeasurable_const.prodMk hG.aemv)
      (MeasurableSet.univ.prod hB)] at this
  rw [show Prod.mk c ⁻¹' (univ ×ˢ B) = B by ext; simp,
    show (fun ω => (c, G.v ω)) ⁻¹' (univ ×ˢ B) = G.v ⁻¹' B by ext; simp] at this
  rw [Measure.map_apply_of_aemeasurable hG.aemv hB]
  exact this

end Game

lemma ckGame_P (κ : ℝ) : (ckGame κ).P = gaussianReal 0 1 := rfl
lemma ckGame_Z (κ : ℝ) : (ckGame κ).Z = id := rfl
lemma ckGame_v (κ : ℝ) : (ckGame κ).v = id := rfl

lemma ckGame_var : variance id (gaussianReal 0 1) = 1 := by
  rw [variance_id_gaussianReal]
  simp

lemma ckGame_std {κ : ℝ} (hκ : 0 < κ) : (ckGame κ).Std := by
  refine ⟨inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1)), ?_, ?_, hκ,
    by simp [ckGame], measurable_id⟩
  · let L : ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
    have h := (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 1)).map_fun L
    have e : (fun ω => L (id ω)) = fun ω => ((ckGame κ).Z ω, (ckGame κ).v ω) := by
      funext ω
      simp [L, ckGame]
    rw [e] at h
    exact h
  · have : variance (ckGame κ).Z (ckGame κ).P = 1 := ckGame_var
    rw [this]
    norm_num

lemma ckGame_meanZ (κ : ℝ) : (ckGame κ).meanZ = 0 := by
  have : (ckGame κ).meanZ = ∫ x, x ∂(gaussianReal 0 1) := rfl
  rw [this, integral_id_gaussianReal]

lemma ckGame_norm (κ : ℝ) : (ckGame κ).norm = 0 := by
  have : (ckGame κ).norm = ∫ x, x ∂(gaussianReal 0 1) := rfl
  rw [this, integral_id_gaussianReal]

lemma ckGame_sens (κ : ℝ) : (ckGame κ).sens = 1 := by
  unfold Game.sens
  have e : (ckGame κ).v = (ckGame κ).Z := rfl
  have hv : variance (ckGame κ).Z (ckGame κ).P = 1 := ckGame_var
  rw [e, covariance_self (X := (ckGame κ).Z) (measurable_id.aemeasurable), hv]
  norm_num

lemma ckGame_condVar (κ : ℝ) : (ckGame κ).condVar = 0 := by
  have e : (ckGame κ).resid = fun _ => 0 := by
    funext ω
    have : (ckGame κ).resid ω = ω - (ckGame κ).sens * ω := rfl
    rw [this, ckGame_sens]
    ring
  unfold Game.condVar
  rw [e, variance_eq_integral aemeasurable_const]
  simp

lemma ckGame_varv (κ : ℝ) : variance (ckGame κ).v (ckGame κ).P = 1 := ckGame_var

/-- **Proposition 1** with the threshold identified, `κck = 1/4`. -/
theorem prop1_threshold' (κ : ℝ) (hκ : 0 < κ) :
    (∃ (a : ℝ → ℝ) (φ : Kernel ℝ ℝ), (ckGame κ).IsSignalingEq a φ) ∧
    ∀ (a : ℝ → ℝ) (φ : Kernel ℝ ℝ), (ckGame κ).IsSignalingEq a φ →
      (κ ≤ κck →
        (∀ᵐ v ∂(gaussianReal 0 1), a v = (1 + √(1 - 4 * κ)) / 2 * v) ∧
        ∀ᵐ v ∂(gaussianReal 0 1), (ckGame κ).utility a φ v = -((1 - √(1 - 4 * κ)) / 2) * v ^ 2) ∧
      (κck < κ →
        (∀ᵐ v ∂(gaussianReal 0 1), a v = 0) ∧
        ∀ᵐ v ∂(gaussianReal 0 1), (ckGame κ).utility a φ v = -v ^ 2 - κ) := by
  have hG := ckGame_std hκ
  have hZ : Measurable (ckGame κ).Z := measurable_id
  have hs := ckGame_sens κ
  have hm := ckGame_meanZ κ
  have hn := ckGame_norm κ
  have hcv := ckGame_condVar κ
  have hκeq : (ckGame κ).κ = κ := rfl
  refine ⟨(hG.lemma1 hZ).1, fun a φ hE => ?_⟩
  have := hE.1.1.markov
  have hl : lplus κ 1 = (1 + √(1 - 4 * κ)) / 2 := by unfold lplus; ring_nf
  rcases hG.signaling_cases hZ hE with ⟨h, hr⟩ | ⟨h, hp⟩
  · rw [hs, hκeq] at h
    simp only [one_pow, mul_one] at h
    refine ⟨fun _ => ?_, fun h' => absurd h (not_le.2 h')⟩
    obtain ⟨hl0, hroot, ha, -, hall, -⟩ := hr
    rw [hs, hκeq, hl] at hl0 hroot ha hall
    rw [hm] at ha
    simp only [one_pow, mul_one] at hroot
    have ha' : ∀ᵐ v ∂(gaussianReal 0 1), a v = (1 + √(1 - 4 * κ)) / 2 * v := by
      filter_upwards [ha] with v hv
      rw [hv]
      simp [ckGame]
    refine ⟨ha', ?_⟩
    filter_upwards [ha'] with v hv
    set l := (1 + √(1 - 4 * κ)) / 2 with hldef
    obtain ⟨hi, hmean, hvar⟩ := hall (a v)
    unfold Game.utility Game.loss
    rw [Game.confLoss_eq hi, hmean, hvar, hcv, hn, hm, hv]
    have e1 : ((ckGame κ).Z v) = v := rfl
    have e2 : ((ckGame κ).c0) = 0 := rfl
    rw [e1, e2, hκeq, ← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_add (sq_nonneg _)
      (mul_nonneg hκ.le (by positivity)), ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _)
      (mul_nonneg hκ.le (by positivity)))]
    have hl0' : l ≠ 0 := hl0.ne'
    have key : (l * v - v) ^ 2 + κ * (0 + (1 / l * (l * v) + (0 - 1 / l * 0) - 0) ^ 2) =
        (1 - l) * v ^ 2 := by
      rw [one_div, inv_mul_cancel_left₀ hl0']
      linear_combination v ^ 2 * hroot
    rw [key, hldef]
    ring
  · rw [hs, hκeq] at h
    simp only [one_pow, mul_one] at h
    refine ⟨fun h' => absurd h' (not_le.2 h), fun _ => ?_⟩
    rw [hm] at hp
    refine ⟨hp, ?_⟩
    have hφ := hG.pool_belief hE.1.1 hp
    filter_upwards [hp] with v hv
    unfold Game.utility Game.loss
    rw [hv]
    have hi : Integrable (fun b : ℝ => b ^ 2) (φ 0) := by
      rw [hφ, integrable_map_measure (by fun_prop) hG.aemv]
      exact hG.memLpv.integrable_sq
    have hmean0 : ∫ b, b ∂(φ 0) = 0 := by
      have e : ∫ b, b ∂((ckGame κ).P.map (ckGame κ).v) = ∫ ω, (ckGame κ).v ω ∂(ckGame κ).P :=
        integral_map hG.aemv aestronglyMeasurable_id
      rw [hφ, e]
      exact hn
    have hvar0 : variance id (φ 0) = 1 := by
      rw [hφ]
      exact (variance_id_map hG.aemv).trans (ckGame_varv κ)
    rw [Game.confLoss_eq hi, hmean0, hvar0, hn]
    have e1 : ((ckGame κ).Z v) = v := rfl
    have e2 : ((ckGame κ).c0) = 0 := rfl
    rw [e1, e2, hκeq, ← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_add (sq_nonneg _)
      (mul_nonneg hκ.le (by positivity)), ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _)
      (mul_nonneg hκ.le (by positivity)))]
    ring

/-- **Proposition 1.** There is a threshold `κck` such that the unique signaling equilibrium has
`a(v) = (1 + √(1-4κ))/2 · v` and `u(v) = -(1 - √(1-4κ))/2 · v²` if `κ ≤ κck`, and `a(v) = 0`,
`u(v) = -v² - κ` if `κ > κck` (for almost every type `v`). -/
theorem prop1 : ∃ κc : ℝ, ∀ κ : ℝ, 0 < κ →
    (∃ (a : ℝ → ℝ) (φ : Kernel ℝ ℝ), (ckGame κ).IsSignalingEq a φ) ∧
    ∀ (a : ℝ → ℝ) (φ : Kernel ℝ ℝ), (ckGame κ).IsSignalingEq a φ →
      (κ ≤ κc →
        (∀ᵐ v ∂(gaussianReal 0 1), a v = (1 + √(1 - 4 * κ)) / 2 * v) ∧
        ∀ᵐ v ∂(gaussianReal 0 1), (ckGame κ).utility a φ v = -((1 - √(1 - 4 * κ)) / 2) * v ^ 2) ∧
      (κc < κ →
        (∀ᵐ v ∂(gaussianReal 0 1), a v = 0) ∧
        ∀ᵐ v ∂(gaussianReal 0 1), (ckGame κ).utility a φ v = -v ^ 2 - κ) :=
  ⟨κck, prop1_threshold'⟩

/-- Proposition 1 with the threshold identified: `κck = 1/4`. -/
theorem prop1_threshold (κ : ℝ) (hκ : 0 < κ) :
    (∃ (a : ℝ → ℝ) (φ : Kernel ℝ ℝ), (ckGame κ).IsSignalingEq a φ) ∧
    ∀ (a : ℝ → ℝ) (φ : Kernel ℝ ℝ), (ckGame κ).IsSignalingEq a φ →
      (κ ≤ κck →
        (∀ᵐ v ∂(gaussianReal 0 1), a v = (1 + √(1 - 4 * κ)) / 2 * v) ∧
        ∀ᵐ v ∂(gaussianReal 0 1), (ckGame κ).utility a φ v = -((1 - √(1 - 4 * κ)) / 2) * v ^ 2) ∧
      (κck < κ →
        (∀ᵐ v ∂(gaussianReal 0 1), a v = 0) ∧
        ∀ᵐ v ∂(gaussianReal 0 1), (ckGame κ).utility a φ v = -v ^ 2 - κ) :=
  prop1_threshold' κ hκ

end CC.LG
