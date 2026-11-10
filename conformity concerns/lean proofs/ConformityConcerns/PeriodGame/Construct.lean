import ConformityConcerns.PeriodGame.NearestPoint
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Candidate equilibria of the period game

* **Pooling on `c`**: every type plays `c`; the belief after `c` is the prior law of `v` and
  after any other action a probability law with infinite second moment, so deviations cost an
  infinite conformity loss.
* **Revealing with slope `λ`** (requires `Z` measurable, so that the strategy is measurable):
  `a = E Z + λ (Z - E Z)` with `λ > 0`, `λ² - λ + κ s̃² = 0`, beliefs `postK`.
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A probability law on `ℝ` with infinite second moment about `μ`. -/
noncomputable def heavy (μ : ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ => ((2 : ℝ≥0∞)⁻¹ ^ (n + 1)) • Measure.dirac (μ + √(2 ^ (n + 1)))

instance (μ : ℝ) : IsProbabilityMeasure (heavy μ) := by
  constructor
  rw [heavy, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma lintegral_heavy (μ : ℝ) :
    ∫⁻ b, ENNReal.ofReal ((b - μ) ^ 2) ∂(heavy μ) = ∞ := by
  rw [heavy, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, add_sub_cancel_left]
  have e : ∀ n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + 1) * ENNReal.ofReal (√(2 ^ (n + 1)) ^ 2) = 1 := by
    intro n
    rw [Real.sq_sqrt (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  simp only [smul_eq_mul, e]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

namespace Game

variable {G : Game Ω}

/-- Beliefs of the pooling equilibrium on `c`. -/
noncomputable def poolK (G : Game Ω) (c : ℝ) : Kernel ℝ ℝ :=
  Kernel.piecewise (measurableSet_singleton c) (Kernel.const ℝ (G.P.map G.v))
    (Kernel.const ℝ (heavy G.norm))

instance [IsProbabilityMeasure G.P] (c : ℝ) : IsMarkovKernel (G.poolK c) := by
  unfold poolK
  infer_instance

lemma poolK_self (c : ℝ) : G.poolK c c = G.P.map G.v := by
  simp [poolK, Kernel.piecewise_apply]

lemma poolK_ne {c x : ℝ} (hx : x ≠ c) : G.poolK c x = heavy G.norm := by
  simp [poolK, Kernel.piecewise_apply, hx]

lemma actionHull_const (c : ℝ) [IsProbabilityMeasure G.P] :
    G.actionHull (fun _ => c) ⊆ {c} := by
  unfold actionHull
  rw [Measure.map_const, measure_univ, one_smul]
  exact convexHull_min (Measure.support_subset_of_isClosed isClosed_singleton
    (by simp [ae_dirac_eq])) (convex_singleton c)

section Std

variable (hG : G.Std)
include hG

/-- Pooling on any `c` is a linear equilibrium. -/
lemma Std.pool_isLinearEq (c : ℝ) : G.IsLinearEq (fun _ => c) (G.poolK c) := by
  have := hG.prob
  refine ⟨⟨measurable_const, inferInstance, fun ω x => ?_, ?_⟩, ?_⟩
  · by_cases hx : x = c
    · rw [hx]
    · unfold loss confLoss
      rw [poolK_ne hx, lintegral_heavy, ENNReal.mul_top (by simpa using hG.κ_pos), add_top]
      exact le_top
  · rw [Measure.map_const, measure_univ, one_smul]
    ext C hC
    rw [Measure.dirac_compProd_apply hC, poolK_self,
      Measure.map_apply_of_aemeasurable hG.aemv (measurable_prodMk_left hC),
      Measure.map_apply_of_aemeasurable (aemeasurable_const.prodMk hG.aemv) hC]
    rfl
  · refine ⟨0, G.norm, 0, variance G.v G.P, fun x hx => ?_⟩
    rw [actionHull_const c hx, poolK_self]
    refine ⟨?_, ?_, ?_⟩
    · rw [integrable_map_measure (by fun_prop) hG.aemv]
      exact hG.memLpv.integrable_sq
    · rw [show (∫ b, b ∂(G.P.map G.v)) = ∫ ω, G.v ω ∂G.P from
        integral_map hG.aemv aestronglyMeasurable_id]
      simp [Game.norm]
    · rw [variance_id_map hG.aemv]
      ring

/-- Ex-ante loss of pooling on `c`. -/
lemma Std.exLoss_pool (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsPBE a φ)
    (ha : a =ᵐ[G.P] fun _ => c) :
    G.exLoss a φ = ENNReal.ofReal ((c - G.meanZ) ^ 2 + variance G.Z G.P) +
      ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P) := by
  rw [hG.exLoss_eq hE, hG.adapt_const ha]

/-- Ex-ante loss of the affine rule `E Z + λ (Z - E Z)`. -/
lemma Std.exLoss_affine {l : ℝ} {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsPBE a φ)
    (ha : a =ᵐ[G.P] fun ω => G.meanZ + l * (G.Z ω - G.meanZ)) :
    G.exLoss a φ = ENNReal.ofReal ((1 - l) ^ 2 * variance G.Z G.P) +
      ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P) := by
  rw [hG.exLoss_eq hE, hG.adapt_affine ha]

/-- Beliefs of the revealing equilibrium with slope `λ`. -/
noncomputable def revK (G : Game Ω) (l : ℝ) : Kernel ℝ ℝ :=
  G.postK (fun x => (x - (1 - l) * G.meanZ) / l) (by fun_prop)

instance (l : ℝ) : IsMarkovKernel (G.revK l) := by
  unfold revK
  infer_instance

/-- The revealing rule with slope `λ > 0` solving `λ² - λ + κ s̃² = 0` is a linear equilibrium. -/
lemma Std.rev_isLinearEq (hZ : Measurable G.Z) {l : ℝ} (hl : 0 < l)
    (hroot : l ^ 2 - l + G.κ * G.sens ^ 2 = 0) :
    G.IsLinearEq (fun ω => G.meanZ + l * (G.Z ω - G.meanZ)) (G.revK l) := by
  have := hG.prob
  set c := (1 - l) * G.meanZ with hc
  have e : (fun ω => G.meanZ + l * (G.Z ω - G.meanZ)) = fun ω => l * G.Z ω + c := by
    funext ω; rw [hc]; ring
  have hmean : ∀ x, ∫ b, b ∂(G.revK l x) - G.norm = G.sens / l * (x - G.meanZ) := by
    intro x
    rw [revK, postK_mean, hG.residMean_eq]
    field_simp
    ring
  have hA : G.κ * (G.sens / l) ^ 2 = 1 / l - 1 := by
    field_simp
    linear_combination hroot
  refine ⟨⟨by fun_prop, inferInstance, fun ω x => ?_, ?_⟩, ?_⟩
  · have hloss : ∀ y, G.loss (G.revK l) ω y = ENNReal.ofReal ((y - G.Z ω) ^ 2 +
        G.κ * (G.condVar + (G.sens / l * (y - G.meanZ)) ^ 2)) := by
      intro y
      unfold loss
      rw [confLoss_eq (by rw [revK]; exact G.postK_sq_integrable _ _ _), hmean,
        show variance id (G.revK l y) = G.condVar from G.postK_var _ _ _,
        ← ENNReal.ofReal_mul hG.κ_pos.le, ← ENNReal.ofReal_add (sq_nonneg _)
          (mul_nonneg hG.κ_pos.le (add_nonneg G.condVar_nonneg (sq_nonneg _)))]
    rw [hloss, hloss]
    refine ENNReal.ofReal_le_ofReal ?_
    have key : ((x - G.Z ω) ^ 2 + G.κ * (G.condVar + (G.sens / l * (x - G.meanZ)) ^ 2)) -
        (((G.meanZ + l * (G.Z ω - G.meanZ)) - G.Z ω) ^ 2 + G.κ * (G.condVar +
          (G.sens / l * ((G.meanZ + l * (G.Z ω - G.meanZ)) - G.meanZ)) ^ 2)) =
        (1 / l) * (x - (G.meanZ + l * (G.Z ω - G.meanZ))) ^ 2 := by
      have : G.κ * (G.sens / l * (x - G.meanZ)) ^ 2 = (1 / l - 1) * (x - G.meanZ) ^ 2 := by
        rw [mul_pow, ← mul_assoc, hA]
      have h2 : G.κ * (G.sens / l * ((G.meanZ + l * (G.Z ω - G.meanZ)) - G.meanZ)) ^ 2 =
          (1 / l - 1) * ((G.meanZ + l * (G.Z ω - G.meanZ)) - G.meanZ) ^ 2 := by
        rw [mul_pow, ← mul_assoc, hA]
      rw [mul_add, mul_add, this, h2]
      field_simp
      ring
    have : 0 ≤ (1 / l) * (x - (G.meanZ + l * (G.Z ω - G.meanZ))) ^ 2 := by positivity
    linarith
  · have e2 : (fun ω => (G.meanZ + l * (G.Z ω - G.meanZ), G.v ω)) =
        fun ω => (l * G.Z ω + c, G.v ω) := by
      funext ω
      exact Prod.ext (by simp only; rw [hc]; ring) rfl
    rw [e, e2, revK]
    exact (hG.map_comp_v (g := fun z => l * z + c) (h := fun x => (x - c) / l) (by fun_prop)
      (by fun_prop)
      (fun z => by field_simp; ring)).symm
  · refine ⟨G.sens / l, G.norm - G.sens / l * G.meanZ, 0, G.condVar, fun x _ => ?_⟩
    refine ⟨by rw [revK]; exact G.postK_sq_integrable _ _ _, ?_, ?_⟩
    · have := hmean x
      linarith
    · rw [revK, postK_var]
      ring

end Std

end Game

end CC.LG
