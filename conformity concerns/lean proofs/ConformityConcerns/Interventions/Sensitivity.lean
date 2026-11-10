import ConformityConcerns.Gaussian.Belief
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Lemma 2 (comparative statics of the sensitivity at zero correlation)

At a history with uncorrelated beliefs, `Σ = diag(σ²_θ, σ²_μ)`, the sensitivity is
`s̃ = (1 + σ²_μ)/(1 + σ²_μ + γ² σ⁴_θ/(1 + σ²_θ))` (the closed form in the proof of Lemma 2).
-/

namespace CC

open Set Filter Topology Matrix

/-- The zero-correlation closed form of the sensitivity (proof of Lemma 2), with `x = σ²_θ`, `y = σ²_μ`. -/
noncomputable def sensDiag (γ x y : ℝ) : ℝ := (1 + y) / (1 + y + γ ^ 2 * (x ^ 2 / (1 + x)))

/-! ### Diagonal 2×2 matrices -/

lemma diag_add_one (x y : ℝ) : (!![x, 0; 0, y] : M2) + 1 = !![1 + x, 0; 0, 1 + y] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]

lemma inv_diag (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (!![a, 0; 0, b] : M2)⁻¹ = !![a⁻¹, 0; 0, b⁻¹] := by
  apply Matrix.inv_eq_right_inv
  ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb]

lemma gainK_diag (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    gainK !![x, 0; 0, y] = !![x / (1 + x), 0; 0, y / (1 + y)] := by
  have hx' : (1 + x) ≠ 0 := by positivity
  have hy' : (1 + y) ≠ 0 := by positivity
  rw [gainK, diag_add_one, inv_diag _ _ hx' hy']
  ext i j; fin_cases i <;> fin_cases j <;> simp [div_eq_mul_inv]

lemma Vt_diag (x y : ℝ) : Vt !![x, 0; 0, y] = 1 + y := by simp [Vt]

lemma Ct_diag (x y : ℝ) : Ct !![x, 0; 0, y] = 0 := by simp [Ct]

lemma Ht_diag (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Ht !![x, 0; 0, y] = x ^ 2 / (1 + x) := by
  have hx' : (1 + x) ≠ 0 := by positivity
  rw [Ht, gainK_diag x y hx hy, diag_add_one]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

lemma sensDiag_den_pos (γ x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 < 1 + y + γ ^ 2 * (x ^ 2 / (1 + x)) := by positivity

/-- The proof of Lemma 2: at zero correlation the sensitivity has the closed form `sensDiag`. -/
theorem sens_diag (γ x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    sens !![x, 0; 0, y] γ = sensDiag γ x y := by
  rw [sens, Vt_diag, Ct_diag, Ht_diag x y hx hy, sensDiag]
  congr 1 <;> ring

/-- The derivatives displayed in the proof of Lemma 2. -/
theorem sensDiag_hasDerivAt (γ x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    HasDerivAt (fun y' => sensDiag γ x y')
      ((γ ^ 2 * (x ^ 2 / (1 + x))) / (1 + y + γ ^ 2 * (x ^ 2 / (1 + x))) ^ 2) y ∧
    HasDerivAt (fun x' => sensDiag γ x' y)
      (-((1 + y) * γ ^ 2 * x * (2 + x)) / ((1 + x) ^ 2 * (1 + y + γ ^ 2 * (x ^ 2 / (1 + x))) ^ 2)) x := by
  have hD := sensDiag_den_pos γ x y hx hy
  have hx1 : (1 + x) ≠ 0 := by positivity
  constructor
  · have h1 : HasDerivAt (fun y' : ℝ => 1 + y') 1 y := by
      simpa using HasDerivAt.const_add 1 (hasDerivAt_id y)
    have h2 : HasDerivAt (fun y' : ℝ => 1 + y' + γ ^ 2 * (x ^ 2 / (1 + x))) 1 y := by
      simpa using HasDerivAt.add_const (γ ^ 2 * (x ^ 2 / (1 + x))) h1
    have := HasDerivAt.div h1 h2 hD.ne'
    convert this using 1
    · funext t; simp [sensDiag]
    · field_simp
      ring
  · have hg1 : HasDerivAt (fun x' : ℝ => x' ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hg2 : HasDerivAt (fun x' : ℝ => 1 + x') 1 x := by
      simpa using HasDerivAt.const_add 1 (hasDerivAt_id x)
    have hg := HasDerivAt.div hg1 hg2 hx1
    have hd := HasDerivAt.const_add (1 + y) (HasDerivAt.const_mul (γ ^ 2) hg)
    have := HasDerivAt.div (hasDerivAt_const x (1 + y)) hd (by simpa using hD.ne')
    convert this using 1
    · funext t; simp [sensDiag]
    · simp only [Pi.div_apply]
      field_simp
      ring

/-- By the derivative above, the sensitivity is decreasing in `σ²_θ`. -/
lemma sensDiag_antitoneOn_x (γ y : ℝ) (hy : 0 ≤ y) :
    AntitoneOn (fun x => sensDiag γ x y) (Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (f' := fun x => -((1 + y) * γ ^ 2 * x * (2 + x)) /
      ((1 + x) ^ 2 * (1 + y + γ ^ 2 * (x ^ 2 / (1 + x))) ^ 2))
    (fun x hx => (sensDiag_hasDerivAt γ x y hx hy).2.continuousAt.continuousWithinAt)
    (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ici] at hx ⊢
    exact (sensDiag_hasDerivAt γ x y (le_of_lt hx) hy).2.hasDerivWithinAt
  · rw [interior_Ici] at hx
    have hx0 : 0 < x := hx
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by positivity)

/-- By the derivative above, the sensitivity is strictly decreasing in `σ²_θ` when `γ ≠ 0`. -/
lemma sensDiag_strictAntiOn_x (γ y : ℝ) (hγ : γ ≠ 0) (hy : 0 ≤ y) :
    StrictAntiOn (fun x => sensDiag γ x y) (Ici 0) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0)
    (f' := fun x => -((1 + y) * γ ^ 2 * x * (2 + x)) /
      ((1 + x) ^ 2 * (1 + y + γ ^ 2 * (x ^ 2 / (1 + x))) ^ 2))
    (fun x hx => (sensDiag_hasDerivAt γ x y hx hy).2.continuousAt.continuousWithinAt)
    (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ici] at hx ⊢
    exact (sensDiag_hasDerivAt γ x y (le_of_lt hx) hy).2.hasDerivWithinAt
  · rw [interior_Ici] at hx
    have hx0 : 0 < x := hx
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)

/-- By the derivative above, the sensitivity is increasing in `σ²_μ`. -/
lemma sensDiag_monotoneOn_y (γ x : ℝ) (hx : 0 ≤ x) :
    MonotoneOn (fun y => sensDiag γ x y) (Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (f' := fun y => (γ ^ 2 * (x ^ 2 / (1 + x))) / (1 + y + γ ^ 2 * (x ^ 2 / (1 + x))) ^ 2)
    (fun y hy => (sensDiag_hasDerivAt γ x y hx hy).1.continuousAt.continuousWithinAt)
    (fun y hy => ?_) (fun y _ => ?_)
  · rw [interior_Ici] at hy ⊢
    exact (sensDiag_hasDerivAt γ x y hx (le_of_lt hy)).1.hasDerivWithinAt
  · positivity

/-- By the derivative above, the sensitivity is strictly increasing in `σ²_μ` when
`γ σ_θ ≠ 0`. -/
lemma sensDiag_strictMonoOn_y (γ x : ℝ) (hγ : γ ≠ 0) (hx : 0 < x) :
    StrictMonoOn (fun y => sensDiag γ x y) (Ici 0) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
    (f' := fun y => (γ ^ 2 * (x ^ 2 / (1 + x))) / (1 + y + γ ^ 2 * (x ^ 2 / (1 + x))) ^ 2)
    (fun y hy => (sensDiag_hasDerivAt γ x y hx.le hy).1.continuousAt.continuousWithinAt)
    (fun y hy => ?_) (fun y hy => ?_)
  · rw [interior_Ici] at hy ⊢
    exact (sensDiag_hasDerivAt γ x y hx.le (le_of_lt hy)).1.hasDerivWithinAt
  · rw [interior_Ici] at hy
    have hy0 : 0 < y := hy
    positivity

lemma sensDiag_anti_x (γ y : ℝ) (hy : 0 ≤ y) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    sensDiag γ b y ≤ sensDiag γ a y :=
  sensDiag_antitoneOn_x γ y hy ha (ha.trans hab) hab

lemma sensDiag_strictAnti_x (γ y : ℝ) (hγ : γ ≠ 0) (hy : 0 ≤ y) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) : sensDiag γ b y < sensDiag γ a y :=
  sensDiag_strictAntiOn_x γ y hγ hy ha (ha.trans hab.le) hab

lemma sensDiag_mono_y (γ x : ℝ) (hx : 0 ≤ x) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    sensDiag γ x a ≤ sensDiag γ x b :=
  sensDiag_monotoneOn_y γ x hx ha (ha.trans hab) hab

lemma sensDiag_strictMono_y (γ x : ℝ) (hγ : γ ≠ 0) (hx : 0 < x) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) : sensDiag γ x a < sensDiag γ x b :=
  sensDiag_strictMonoOn_y γ x hγ hx ha (ha.trans hab.le) hab

/-- At `σ²_θ = 0` the sensitivity is `1`. -/
lemma sensDiag_zero (γ y : ℝ) (hy : 0 ≤ y) : sensDiag γ 0 y = 1 := by
  have : (1 + y) ≠ 0 := by positivity
  simp [sensDiag, this]

/-- As `σ²_θ → ∞` the sensitivity falls to `0`. -/
lemma sensDiag_tendsto_zero (γ y : ℝ) (hγ : γ ≠ 0) (_hy : 0 ≤ y) :
    Tendsto (fun x => sensDiag γ x y) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ 2 / (1 + x)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-1 : ℝ) tendsto_id)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [le_div_iff₀ (by positivity)]
    simp only [id]
    nlinarith
  have h2 : Tendsto (fun x : ℝ => 1 + y + γ ^ 2 * (x ^ 2 / (1 + x))) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (h1.const_mul_atTop (by positivity))
  exact tendsto_const_nhds.div_atTop h2

/-- **Lemma 2.** At zero correlation, the sensitivity is decreasing in `σ²_θ` and increasing in
`σ²_μ`, strictly so when `γ_t σ_{θ,t} > 0`. -/
theorem lemma2 (γ : ℝ) :
    (∀ y, 0 ≤ y → AntitoneOn (fun x => sens !![x, 0; 0, y] γ) (Ici 0)) ∧
    (∀ x, 0 ≤ x → MonotoneOn (fun y => sens !![x, 0; 0, y] γ) (Ici 0)) ∧
    (γ ≠ 0 → ∀ y, 0 ≤ y → StrictAntiOn (fun x => sens !![x, 0; 0, y] γ) (Ici 0)) ∧
    (γ ≠ 0 → ∀ x, 0 < x → StrictMonoOn (fun y => sens !![x, 0; 0, y] γ) (Ici 0)) := by
  refine ⟨fun y hy a ha b hb hab => ?_, fun x hx a ha b hb hab => ?_,
    fun hγ y hy a ha b hb hab => ?_, fun hγ x hx a ha b hb hab => ?_⟩
  · simp only [mem_Ici] at ha hb
    simp only [sens_diag γ _ _ ha hy, sens_diag γ _ _ hb hy]
    exact sensDiag_anti_x γ y hy ha hab
  · simp only [mem_Ici] at ha hb
    simp only [sens_diag γ _ _ hx ha, sens_diag γ _ _ hx hb]
    exact sensDiag_mono_y γ x hx ha hab
  · simp only [mem_Ici] at ha hb
    simp only [sens_diag γ _ _ ha hy, sens_diag γ _ _ hb hy]
    exact sensDiag_strictAnti_x γ y hγ hy ha hab
  · simp only [mem_Ici] at ha hb
    simp only [sens_diag γ _ _ hx.le ha, sens_diag γ _ _ hx.le hb]
    exact sensDiag_strictMono_y γ x hγ hx ha hab

end CC
