import ConformityConcerns.General.Defs
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Examples: the general-loss environment of Section A3 is non-empty

Quadratic losses `g(z) = z²`, `ℓ(b) = κ (b - μ)²` and standard normal types satisfy every standing
assumption, so `Setting` (and hence the hypotheses of Lemma A2, Propositions A3, A4, A6 and
Remark A1) is satisfiable.
-/

namespace CC.Examples

open MeasureTheory ProbabilityTheory Set General Filter
open scoped ENNReal NNReal

lemma adaptLoss_sq : AdaptLoss (fun z : ℝ => z ^ 2) where
  smooth := by fun_prop
  even := fun z => by ring
  strictConvex := Even.strictConvexOn_pow (by decide) (by norm_num)
  zero := by norm_num

lemma confLoss_quad (κ μ : ℝ) (hκ : 0 < κ) : ConfLoss (fun b => κ * (b - μ) ^ 2) μ where
  smooth := by fun_prop
  strictConvex := by
    have h := (Even.strictConvexOn_pow (n := 2) (by decide) (by norm_num))
    have h2 : StrictConvexOn ℝ univ (fun b : ℝ => (b - μ) ^ 2) := by
      refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
      have := h.2 (mem_univ (x - μ)) (mem_univ (y - μ)) (by intro h'; apply hxy; linarith) ha hb hab
      simp only [smul_eq_mul] at this ⊢
      have e : a * x + b * y - μ = a * (x - μ) + b * (y - μ) := by
        have : μ = (a + b) * μ := by rw [hab, one_mul]
        linear_combination (-1 : ℝ) * this
      rw [e]; exact this
    refine ⟨convex_univ, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have h3 := mul_lt_mul_of_pos_left (h2.2 hx hy hxy ha hb hab) hκ
    simp only [smul_eq_mul] at h3 ⊢
    linarith
  zero := by simp
  isMin := fun b => by simp only [sub_self]; norm_num; positivity

lemma typeDist_gaussian : TypeDist (gaussianReal 0 1) where
  prob := inferInstance
  density := ⟨gaussianPDFReal 0 1, by unfold gaussianPDFReal; fun_prop,
    fun x => gaussianPDFReal_pos 0 1 x one_ne_zero, gaussianReal_of_var_ne_zero 0 one_ne_zero⟩

lemma integrable_quad (κ μ : ℝ) : Integrable (fun b : ℝ => κ * (b - μ) ^ 2) (gaussianReal 0 1) := by
  have h : MemLp (fun b : ℝ => b - μ) 2 (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).sub (memLp_const μ)
  exact (h.integrable_sq).const_mul κ

lemma quad_pos (κ μ : ℝ) (hκ : 0 < κ) : 0 < ∫ b, κ * (b - μ) ^ 2 ∂(gaussianReal 0 1) := by
  have hnn : 0 ≤ᵐ[gaussianReal 0 1] fun b : ℝ => κ * (b - μ) ^ 2 :=
    Filter.Eventually.of_forall fun b => by positivity
  rw [integral_pos_iff_support_of_nonneg_ae hnn (integrable_quad κ μ)]
  have hsupp : Function.support (fun b : ℝ => κ * (b - μ) ^ 2) = {μ}ᶜ := by
    ext b; simp [hκ.ne', sub_eq_zero]
  rw [hsupp, measure_compl (measurableSet_singleton μ) (measure_ne_top _ _), measure_univ]
  have : (gaussianReal 0 1) {μ} = 0 := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
    exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  simp [this]

/-- The quadratic environment with standard normal types. -/
noncomputable def quadSetting (κ μ : ℝ) (hκ : 0 < κ) : Setting where
  g := fun z => z ^ 2
  ℓ := fun b => κ * (b - μ) ^ 2
  μ := μ
  F := gaussianReal 0 1
  hg := adaptLoss_sq
  hℓ := confLoss_quad κ μ hκ
  hF := typeDist_gaussian
  integrable := integrable_quad κ μ
  Mpos := quad_pos κ μ hκ

/-- The environment of Proposition A3 with an even conformity loss `f(z) = κ z²` exists. -/
example (κ μ : ℝ) (hκ : 0 < κ) :
    (quadSetting κ μ hκ).ℓ = fun b => κ * (b - (quadSetting κ μ hκ).μ) ^ 2 := rfl

lemma adaptLoss_const_sq (κ : ℝ) (hκ : 0 < κ) : AdaptLoss (fun z : ℝ => κ * z ^ 2) where
  smooth := by fun_prop
  even := fun z => by ring
  strictConvex := by simpa using (confLoss_quad κ 0 hκ).strictConvex
  zero := by norm_num

lemma deriv_const_sq (κ x : ℝ) : deriv (fun z : ℝ => κ * z ^ 2) x = κ * (2 * x) := by
  simp

lemma deriv_sq (x : ℝ) : deriv (fun z : ℝ => z ^ 2) x = 2 * x := by
  simp

/-- The hypothesis of Proposition A6 (i) holds for `g(z) = z²` and `f(z) = 2z²`. -/
lemma propA6_pooling_example :
    AdaptLoss (fun z : ℝ => z ^ 2) ∧ AdaptLoss (fun z : ℝ => 2 * z ^ 2) ∧
      ∀ C : ℝ, ∃ ε > 0, ∀ᶠ x in atTop,
        1 + ε ≤ deriv (fun z : ℝ => 2 * z ^ 2) x / deriv (fun z : ℝ => z ^ 2) (x + C) := by
  refine ⟨adaptLoss_sq, adaptLoss_const_sq 2 two_pos, fun C => ⟨1 / 2, by norm_num, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (max (3 * C) (1 - C))] with x hx
  have h1 : 3 * C ≤ x := le_trans (le_max_left _ _) hx
  have h2 : 1 - C ≤ x := le_trans (le_max_right _ _) hx
  have hpos : 0 < 2 * (x + C) := by linarith
  rw [deriv_const_sq, deriv_sq, le_div_iff₀ hpos]
  nlinarith

/-- The hypothesis of Proposition A6 (ii) holds for `g(z) = z²` and `f(z) = z²/8`, with
`β = 1/2`. -/
lemma propA6_revealing_example :
    AdaptLoss (fun z : ℝ => z ^ 2) ∧ AdaptLoss (fun z : ℝ => (1 / 8) * z ^ 2) ∧
      ∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ x, 0 < x →
        deriv (fun z : ℝ => (1 / 8) * z ^ 2) x ≤ (1 - β) * deriv (fun z : ℝ => z ^ 2) (β * x) := by
  refine ⟨adaptLoss_sq, adaptLoss_const_sq _ (by norm_num), 1 / 2, by norm_num, by norm_num,
    fun x hx => ?_⟩
  rw [deriv_const_sq, deriv_sq]
  linarith

end CC.Examples
