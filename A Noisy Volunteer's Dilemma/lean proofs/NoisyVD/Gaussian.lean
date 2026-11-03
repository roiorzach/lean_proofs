import Mathlib

/-!
# The standard normal density and distribution function
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

/-- The standard normal density `φ`. -/
noncomputable def phi (x : ℝ) : ℝ := (√(2 * π))⁻¹ * exp (-x ^ 2 / 2)

/-- The standard normal distribution function `Φ`. -/
noncomputable def Phi (x : ℝ) : ℝ := ∫ y in Iic x, phi y

lemma sqrt_two_pi_pos : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)

lemma phi_pos (x : ℝ) : 0 < phi x := by
  unfold phi
  have := sqrt_two_pi_pos
  positivity

lemma phi_neg (x : ℝ) : phi (-x) = phi x := by simp [phi]

lemma phi_zero : phi 0 = (√(2 * π))⁻¹ := by simp [phi]

lemma phi_le (x : ℝ) : phi x ≤ phi 0 := by
  rw [phi_zero]
  unfold phi
  have h := sqrt_two_pi_pos
  have : exp (-x ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg x]
  have h2 : 0 < (√(2 * π))⁻¹ := by positivity
  nlinarith

lemma continuous_phi : Continuous phi := by
  unfold phi
  fun_prop

lemma hasDerivAt_phi (x : ℝ) : HasDerivAt phi (-x * phi x) x := by
  unfold phi
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert this using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h2 := h1.exp.const_mul (√(2 * π))⁻¹
  convert h2 using 1
  ring

lemma differentiable_phi : Differentiable ℝ phi := fun x => (hasDerivAt_phi x).differentiableAt

lemma exp_form (x : ℝ) : exp (-x ^ 2 / 2) = exp (-(1 / 2) * x ^ 2) := by
  congr 1; ring

lemma integrable_phi : Integrable phi := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul (√(2 * π))⁻¹
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [phi]
  rw [exp_form]

lemma integral_phi : ∫ x, phi x = 1 := by
  have h : ∀ x, phi x = (√(2 * π))⁻¹ * exp (-(1 / 2) * x ^ 2) := fun x => by
    simp only [phi]; rw [exp_form]
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, integral_gaussian]
  have : π / (1 / 2) = 2 * π := by ring
  rw [this]
  exact inv_mul_cancel₀ sqrt_two_pi_pos.ne'

lemma Phi_add_Ioi (x : ℝ) : Phi x + ∫ y in Ioi x, phi y = 1 := by
  unfold Phi
  rw [← integral_phi, ← compl_Iic]
  exact MeasureTheory.integral_add_compl measurableSet_Iic integrable_phi

lemma Phi_sub (a b : ℝ) : Phi b - Phi a = ∫ y in a..b, phi y := by
  unfold Phi
  exact intervalIntegral.integral_Iic_sub_Iic integrable_phi.integrableOn integrable_phi.integrableOn

lemma hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (phi x) x := by
  have h1 : Phi = fun y => Phi 0 + ∫ t in (0 : ℝ)..y, phi t := by
    funext y
    rw [← Phi_sub]; ring
  rw [h1]
  have h2 : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, phi t) (phi x) x :=
    intervalIntegral.integral_hasDerivAt_right (continuous_phi.intervalIntegrable _ _)
      (continuous_phi.stronglyMeasurableAtFilter _ _) continuous_phi.continuousAt
  exact h2.const_add _

lemma continuous_Phi : Continuous Phi :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_Phi x).continuousAt

lemma Phi_strictMono : StrictMono Phi :=
  strictMono_of_deriv_pos fun x => by rw [(hasDerivAt_Phi x).deriv]; exact phi_pos x

lemma Phi_mono : Monotone Phi := Phi_strictMono.monotone

lemma Phi_nonneg (x : ℝ) : 0 ≤ Phi x :=
  setIntegral_nonneg measurableSet_Iic fun y _ => (phi_pos y).le

lemma Phi_pos (x : ℝ) : 0 < Phi x := by
  have h := Phi_strictMono (show x - 1 < x by linarith)
  linarith [Phi_nonneg (x - 1)]

lemma Phi_lt_one (x : ℝ) : Phi x < 1 := by
  have h := Phi_strictMono (show x < x + 1 by linarith)
  have h2 := Phi_add_Ioi (x + 1)
  have h3 : 0 ≤ ∫ y in Ioi (x + 1), phi y :=
    setIntegral_nonneg measurableSet_Ioi fun y _ => (phi_pos y).le
  linarith

lemma Phi_le_one (x : ℝ) : Phi x ≤ 1 := (Phi_lt_one x).le

lemma Phi_neg (x : ℝ) : Phi (-x) = 1 - Phi x := by
  have h1 : ∫ y in Ioi x, phi y = Phi (-x) := by
    unfold Phi
    have := integral_comp_neg_Iic (-x) phi
    rw [neg_neg] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
    simp [phi_neg]
  have h2 := Phi_add_Ioi x
  linarith

lemma Phi_zero : Phi 0 = 1 / 2 := by
  have := Phi_neg 0
  simp only [neg_zero] at this
  linarith

lemma tendsto_Phi_atTop : Tendsto Phi atTop (𝓝 1) := by
  have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (f := phi) (0 : ℝ)
    integrable_phi.integrableOn tendsto_id
  have h1 : Phi = fun y => Phi 0 + ∫ t in (0 : ℝ)..id y, phi t := by
    funext y
    simp only [id]
    rw [← Phi_sub]; ring
  rw [h1, ← Phi_add_Ioi 0]
  exact h.const_add _

lemma tendsto_Phi_atBot : Tendsto Phi atBot (𝓝 0) := by
  have h1 : Phi = fun x => 1 - Phi (-x) := by
    funext x
    rw [Phi_neg]; ring
  rw [h1]
  have h2 := (tendsto_Phi_atTop.comp tendsto_neg_atBot_atTop).const_sub 1
  simpa using h2

/-- `Φ` is Lipschitz with constant `φ(0)`. -/
lemma abs_Phi_sub_le (a b : ℝ) : |Phi a - Phi b| ≤ phi 0 * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Phi) (f' := phi)
    (s := univ) (C := phi 0) (x := b) (y := a)
    (fun x _ => (hasDerivAt_Phi x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs, abs_of_pos (phi_pos x)]; exact phi_le x)
    convex_univ (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using h

lemma u_mul_phi_le {u : ℝ} (_hu : 0 ≤ u) : u * phi u ≤ phi 0 := by
  rw [phi_zero]
  unfold phi
  have h := sqrt_two_pi_pos
  have h2 : u * exp (-u ^ 2 / 2) ≤ 1 := by
    have h3 : u ≤ exp (u ^ 2 / 2) := by
      have := Real.add_one_le_exp (u ^ 2 / 2)
      nlinarith [sq_nonneg (u - 1)]
    have h4 : exp (-u ^ 2 / 2) = (exp (u ^ 2 / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [h4]
    have h5 := exp_pos (u ^ 2 / 2)
    rw [← div_eq_mul_inv, div_le_one h5]
    exact h3
  have h6 : 0 < (√(2 * π))⁻¹ := by positivity
  calc u * ((√(2 * π))⁻¹ * exp (-u ^ 2 / 2)) = (√(2 * π))⁻¹ * (u * exp (-u ^ 2 / 2)) := by ring
    _ ≤ (√(2 * π))⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 h6.le
    _ = _ := by ring

/-- `φ` is Lipschitz with constant `φ(0)`. -/
lemma abs_phi_sub_le (a b : ℝ) : |phi a - phi b| ≤ phi 0 * |a - b| := by
  have hd : ∀ x, ‖-x * phi x‖ ≤ phi 0 := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (phi_pos x)]
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; exact u_mul_phi_le h
    · rw [abs_of_nonpos h]
      have := u_mul_phi_le (u := -x) (by linarith)
      rwa [phi_neg] at this
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := phi)
    (f' := fun x => -x * phi x) (s := univ) (C := phi 0) (x := b) (y := a)
    (fun x _ => (hasDerivAt_phi x).hasDerivWithinAt) (fun x _ => hd x)
    convex_univ (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using h

end NoisyVD
