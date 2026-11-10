import ConformityConcerns.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The deterministic ODE argument on the upper tail (proof of Proposition A5, last paragraph)

Along the separating upper tail, with `w = x - a x` and `V = w² + κ (m x - m μ)`, the ODE
`a' = κ m' / (2 w)` gives `V' = 2 w`. Hence `√V - x` is nonincreasing and, where
`κ (m x - m μ) ≥ (κ + κck) (x - μ)² / 2`, so is `V / (x - μ)² + (κ - κck) log (x - μ)`.
Starting from a point `x₁ ≤ μ + K` with bounded `w(x₁)²` this forces `V < 0` far out.
-/

namespace CC.LearnTheta.PoolTailAux

open Set Real

lemma w_ne_zero {κ : ℝ} {m a : ℝ → ℝ} {x : ℝ} (hpos : 0 < κ * deriv m x / (2 * (x - a x))) :
    x - a x ≠ 0 := by
  intro h; rw [h, mul_zero, div_zero] at hpos; exact lt_irrefl _ hpos

lemma hasDerivAt_V {κ : ℝ} {m a : ℝ → ℝ} {mμ x : ℝ} (hm : DifferentiableAt ℝ m x)
    (hpos : 0 < κ * deriv m x / (2 * (x - a x)))
    (ha : HasDerivAt a (κ * deriv m x / (2 * (x - a x))) x) :
    HasDerivAt (fun y => (y - a y) ^ 2 + κ * (m y - mμ)) (2 * (x - a x)) x := by
  have hw : x - a x ≠ 0 := w_ne_zero hpos
  have h1 : HasDerivAt (fun y => y - a y) (1 - κ * deriv m x / (2 * (x - a x))) x :=
    (hasDerivAt_id' x).sub ha
  have h2 := (h1.pow 2).add ((hm.hasDerivAt.sub_const mμ).const_mul κ)
  convert h2 using 1
  field_simp
  ring

/-- The ODE contradiction on the upper tail. -/
theorem tail_ode_false {κ : ℝ} (hκ : κck < κ) {m a : ℝ → ℝ} {μ : ℝ} {v : EReal}
    (hμv : ((μ : ℝ) : EReal) ≤ v)
    (hdiff : Differentiable ℝ m) (hmin : ∀ x, m μ ≤ m x)
    (hode : ∀ x : ℝ, v < (x : EReal) →
      0 < κ * deriv m x / (2 * (x - a x)) ∧ HasDerivAt a (κ * deriv m x / (2 * (x - a x))) x)
    {K C' M : ℝ} (hK : 0 < K) {x₁ : ℝ} (hx₁ : v < (x₁ : EReal)) (hx₁K : x₁ ≤ μ + K)
    (hw₁ : (a x₁ - x₁) ^ 2 ≤ C') (hL₁ : κ * (m x₁ - m μ) ≤ M)
    (hlow : ∀ x ∈ Icc (μ + K) (μ + K * exp (((√(C' + M) + K) / K) ^ 2 / (κ - κck))),
      (κ + κck) * (x - μ) ^ 2 / 2 ≤ κ * (m x - m μ)) : False := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  have hκd : 0 < κ - κck := sub_pos.2 hκ
  set C : ℝ := ((√(C' + M) + K) / K) ^ 2 with hC
  set Z : ℝ := K * exp (C / (κ - κck)) with hZ
  set V : ℝ → ℝ := fun y => (y - a y) ^ 2 + κ * (m y - m μ) with hV
  have hμx₁ : μ < x₁ := by
    have := lt_of_le_of_lt hμv hx₁; exact_mod_cast this
  have htail : ∀ x, x₁ ≤ x → v < (x : EReal) := fun x hx =>
    lt_of_lt_of_le hx₁ (by exact_mod_cast hx)
  have hVd : ∀ x, x₁ ≤ x → HasDerivAt V (2 * (x - a x)) x := fun x hx =>
    hasDerivAt_V (hdiff x) (hode x (htail x hx)).1 (hode x (htail x hx)).2
  have hL0 : ∀ x, 0 ≤ κ * (m x - m μ) := fun x => mul_nonneg hκ0.le (sub_nonneg.2 (hmin x))
  have hVpos : ∀ x, x₁ ≤ x → 0 < V x := by
    intro x hx
    have hw := w_ne_zero (hode x (htail x hx)).1
    have h1 : 0 < (x - a x) ^ 2 := by positivity
    have h2 := hL0 x
    simp only [hV]; linarith
  -- Phase 1: `√V - x` is nonincreasing.
  have hph1 : √(V (μ + K)) - (μ + K) ≤ √(V x₁) - x₁ := by
    have hder : ∀ y, x₁ ≤ y → HasDerivAt (fun y => √(V y) - y)
        (2 * (y - a y) / (2 * √(V y)) - 1) y := fun y hy =>
      ((hVd y hy).sqrt (hVpos y hy).ne').sub (hasDerivAt_id' y)
    have hanti : AntitoneOn (fun y => √(V y) - y) (Icc x₁ (μ + K)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · intro y hy
        exact (hder y hy.1).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact (hder y hy.1.le).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hder y hy.1.le).deriv]
        have hsq : 0 < √(V y) := Real.sqrt_pos.2 (hVpos y hy.1.le)
        have hle : y - a y ≤ √(V y) := by
          refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
          have := hL0 y
          simp only [hV]; linarith
        rw [sub_nonpos, div_le_one (by positivity)]
        linarith
    exact hanti ⟨le_refl _, hx₁K⟩ ⟨hx₁K, le_refl _⟩ hx₁K
  have hV1 : V x₁ ≤ C' + M := by
    simp only [hV]
    have : (x₁ - a x₁) ^ 2 = (a x₁ - x₁) ^ 2 := by ring
    linarith
  have hsK : √(V (μ + K)) ≤ √(C' + M) + K := by
    have := Real.sqrt_le_sqrt hV1
    linarith
  have hVK : V (μ + K) / K ^ 2 ≤ C := by
    rw [hC, div_pow, div_le_div_iff_of_pos_right (by positivity)]
    have h0 : 0 ≤ √(V (μ + K)) := Real.sqrt_nonneg _
    calc V (μ + K) = √(V (μ + K)) ^ 2 := (Real.sq_sqrt (hVpos _ (by linarith)).le).symm
      _ ≤ (√(C' + M) + K) ^ 2 := pow_le_pow_left₀ h0 hsK 2
  -- Phase 2: `V / (x - μ)² + (κ - κck) log (x - μ)` is nonincreasing on `[μ + K, μ + Z]`.
  have hKZ : K ≤ Z := by
    rw [hZ]; exact le_mul_of_one_le_right hK.le (one_le_exp (by positivity))
  have hph2 : V (μ + Z) / Z ^ 2 + (κ - κck) * log Z ≤
      V (μ + K) / K ^ 2 + (κ - κck) * log K := by
    have hder : ∀ y, μ + K ≤ y → HasDerivAt
        (fun y => V y / (y - μ) ^ 2 + (κ - κck) * log (y - μ))
        ((2 * (y - a y) * (y - μ) ^ 2 - V y * (2 * (y - μ))) / ((y - μ) ^ 2) ^ 2
          + (κ - κck) * (1 / (y - μ))) y := by
      intro y hy
      have hy1 : x₁ ≤ y := by linarith
      have hz : 0 < y - μ := by linarith
      have h1 : HasDerivAt (fun y => y - μ) 1 y := (hasDerivAt_id' y).sub_const μ
      have h2 : HasDerivAt (fun y => (y - μ) ^ 2) (2 * (y - μ)) y := by
        convert h1.pow 2 using 1; ring
      have h3 := (hVd y hy1).div h2 (by positivity)
      have h4 := (h1.log hz.ne').const_mul (κ - κck)
      exact h3.add h4
    have hanti : AntitoneOn (fun y => V y / (y - μ) ^ 2 + (κ - κck) * log (y - μ))
        (Icc (μ + K) (μ + Z)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · intro y hy
        exact (hder y hy.1).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact (hder y hy.1.le).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hder y hy.1.le).deriv]
        have hz : 0 < y - μ := by linarith [hy.1]
        have hlo := hlow y ⟨hy.1.le, hy.2.le⟩
        set z := y - μ with hzdef
        set w := y - a y with hwdef
        have hVy : V y = w ^ 2 + κ * (m y - m μ) := rfl
        have key : (2 * w * z ^ 2 - V y * (2 * z)) / (z ^ 2) ^ 2 + (κ - κck) * (1 / z)
            = (2 * w * z - 2 * V y + (κ - κck) * z ^ 2) / z ^ 3 := by
          field_simp
        rw [key]
        apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
        rw [hVy]
        have hck := κck_eq
        nlinarith [sq_nonneg (z - 2 * w)]
    have := hanti ⟨le_refl _, by linarith⟩ ⟨by linarith, le_refl _⟩ (by linarith)
    simpa only [add_sub_cancel_left] using this
  have hlogZ : (κ - κck) * log Z = (κ - κck) * log K + C := by
    rw [hZ, Real.log_mul hK.ne' (exp_pos _).ne', Real.log_exp]
    field_simp
  have hfin : V (μ + Z) / Z ^ 2 ≤ 0 := by linarith
  have hpos : 0 < V (μ + Z) / Z ^ 2 := by
    have := hVpos (μ + Z) (by linarith)
    have hZ0 : 0 < Z := lt_of_lt_of_le hK hKZ
    positivity
  linarith

end CC.LearnTheta.PoolTailAux
