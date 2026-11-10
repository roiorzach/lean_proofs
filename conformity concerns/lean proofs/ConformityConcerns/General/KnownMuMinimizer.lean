import ConformityConcerns.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# The minimiser `x*` of `m` (proof of Proposition A5), under a nondegeneracy assumption

Here we prove it when `ṽ = v + Y` is not almost surely constant (the paper's density assumption
on `v_t` gives this). The argument is the paper's: if `m'` had no zero,
`m` would be strictly monotone, so `E[(X - EX)(m(X) - m(EX))]` would be nonzero, while the law
of iterated expectations, independence and symmetry give `Cov(X, m(X)) = Cov(v, v²) = 0`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter

lemma sq_le_one_add_cube {t : ℝ} (ht : 0 ≤ t) : t ^ 2 ≤ 1 + t ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg (t - 1)) (by linarith : 0 ≤ t + 1)]

lemma le_one_add_cube {t : ℝ} (ht : 0 ≤ t) : t ≤ 1 + t ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg (t - 1)) (by linarith : 0 ≤ t + 1), sq_nonneg t]

/-- If `φ` is strictly increasing and `E[(X - c)(φ(X) - φ(c))] = 0`, then `X = c` a.s. -/
lemma ae_eq_of_integral_mono_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {φ : ℝ → ℝ} (hφ : StrictMono φ) (c : ℝ)
    (hint : Integrable (fun ω => (X ω - c) * (φ (X ω) - φ c)) P)
    (h0 : ∫ ω, (X ω - c) * (φ (X ω) - φ c) ∂P = 0) : ∀ᵐ ω ∂P, X ω = c := by
  have hnn : 0 ≤ fun ω => (X ω - c) * (φ (X ω) - φ c) := by
    intro ω
    rcases lt_trichotomy (X ω) c with h | h | h
    · exact (mul_pos_of_neg_of_neg (by linarith) (sub_neg.2 (hφ h))).le
    · simp [h]
    · exact (mul_pos (by linarith) (sub_pos.2 (hφ h))).le
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 h0
  filter_upwards [hae] with ω hω
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (mul_pos_of_neg_of_neg (by linarith) (sub_neg.2 (hφ h))).ne' hω
  · exact (mul_pos (by linarith) (sub_pos.2 (hφ h))).ne' hω

/-- **The minimiser of `m` (proof of Proposition A5)**, assuming `ṽ = v + Y` is not a.s.
constant: `m'` has a unique zero. -/
theorem propA5_minimizer_of_nondegenerate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (v Y : Ω → ℝ) (hv : Measurable v) (hY : Measurable Y) (hind : IndepFun v Y P)
    (hsymm : P.map v = P.map (fun ω => -v ω)) (h3 : Integrable (fun ω => |v ω| ^ 3) P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) (m : ℝ → ℝ) (hm : ContDiff ℝ 2 m)
    (hm2 : ∀ x, 0 < iteratedDeriv 2 m x ∧ iteratedDeriv 2 m x ≤ 2)
    (hcond : (fun ω => m (v ω + Y ω)) =ᵐ[P]
      P[fun ω => v ω ^ 2 | MeasurableSpace.comap (fun ω => v ω + Y ω) inferInstance])
    (hnd : ∀ c : ℝ, ¬ ∀ᵐ ω ∂P, v ω + Y ω = c) :
    ∃! xs : ℝ, deriv m xs = 0 := by
  have h2 : ∀ x, iteratedDeriv 2 m x = deriv (deriv m) x := fun x => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hdm : StrictMono (deriv m) :=
    strictMono_of_deriv_pos (fun x => by rw [← h2]; exact (hm2 x).1)
  have hdmc : Continuous (deriv m) := hm.continuous_deriv (by norm_num)
  refine existsUnique_of_exists_of_unique ?_ (fun y₁ y₂ h₁ h₂ => hdm.injective (h₁.trans h₂.symm))
  by_contra hne
  have hne' : ∀ x, deriv m x ≠ 0 := fun x hx => hne ⟨x, hx⟩
  -- integrability
  have hX : Measurable (fun ω => v ω + Y ω) := hv.add hY
  have hv3' : Integrable (fun ω => v ω ^ 3) P := by
    refine h3.mono' (hv.pow_const 3).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
  have hv2 : Integrable (fun ω => v ω ^ 2) P := by
    refine (integrable_const (1 : ℝ)).add h3 |>.mono' (hv.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact sq_le_one_add_cube (abs_nonneg _)
  have hv1 : Integrable v P := by
    refine (integrable_const (1 : ℝ)).add h3 |>.mono' hv.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact le_one_add_cube (abs_nonneg _)
  have hY1 : Integrable Y P := by
    refine (integrable_const (1 : ℝ)).add hY2 |>.mono' hY.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    show |Y ω| ≤ 1 + Y ω ^ 2
    nlinarith [sq_abs (Y ω), sq_nonneg (|Y ω| - 1), abs_nonneg (Y ω)]
  have hindY : IndepFun Y (fun ω => v ω ^ 2) P :=
    hind.symm.comp measurable_id (measurable_id.pow_const 2)
  have hYv2 : Integrable (fun ω => Y ω * v ω ^ 2) P := hindY.integrable_mul hY1 hv2
  have hX1 : Integrable (fun ω => v ω + Y ω) P := hv1.add hY1
  have hXv2 : Integrable ((fun ω => v ω + Y ω) * fun ω => v ω ^ 2) P := by
    refine (hv3'.add hYv2).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply, Pi.add_apply]; ring
  -- moments
  have hodd : ∀ k : ℕ, Odd k → ∫ ω, v ω ^ k ∂P = 0 := by
    intro k hk
    have e1 : ∫ ω, v ω ^ k ∂P = ∫ x, x ^ k ∂(P.map v) :=
      (integral_map hv.aemeasurable (continuous_pow k).aestronglyMeasurable).symm
    have e2 : ∫ x, x ^ k ∂(P.map (fun ω => -v ω)) = ∫ ω, (-v ω) ^ k ∂P :=
      integral_map hv.neg.aemeasurable (continuous_pow k).aestronglyMeasurable
    rw [hsymm, e2] at e1
    simp only [hk.neg_pow, integral_neg] at e1
    linarith
  have hEv : ∫ ω, v ω ∂P = 0 := by simpa using hodd 1 odd_one
  have hEv3 : ∫ ω, v ω ^ 3 ∂P = 0 := hodd 3 (by decide)
  have hEYv2 : ∫ ω, Y ω * v ω ^ 2 ∂P = (∫ ω, Y ω ∂P) * ∫ ω, v ω ^ 2 ∂P :=
    hindY.integral_fun_mul_eq_mul_integral hY.aestronglyMeasurable
      (hv.pow_const 2).aestronglyMeasurable
  have hEXv2 : ∫ ω, (v ω + Y ω) * v ω ^ 2 ∂P = (∫ ω, Y ω ∂P) * ∫ ω, v ω ^ 2 ∂P := by
    have e : (fun ω => (v ω + Y ω) * v ω ^ 2) = fun ω => v ω ^ 3 + Y ω * v ω ^ 2 := by
      funext ω; ring
    rw [e, integral_add hv3' hYv2, hEv3, hEYv2, zero_add]
  -- the conditional expectation
  have hle : MeasurableSpace.comap (fun ω => v ω + Y ω) inferInstance ≤ ‹MeasurableSpace Ω› :=
    hX.comap_le
  have hmXi : Integrable (fun ω => m (v ω + Y ω)) P := integrable_condExp.congr hcond.symm
  have hEm : ∫ ω, m (v ω + Y ω) ∂P = ∫ ω, v ω ^ 2 ∂P := by
    rw [integral_congr_ae hcond, integral_condExp hle]
  have hpo := condExp_mul_of_stronglyMeasurable_left
    (m := MeasurableSpace.comap (fun ω => v ω + Y ω) inferInstance)
    (comap_measurable (fun ω => v ω + Y ω)).stronglyMeasurable hXv2 hv2
  have hXm : (fun ω => (v ω + Y ω) * m (v ω + Y ω)) =ᵐ[P]
      P[(fun ω => v ω + Y ω) * fun ω => v ω ^ 2 |
        MeasurableSpace.comap (fun ω => v ω + Y ω) inferInstance] := by
    filter_upwards [hcond, hpo] with ω h1 h2
    rw [h2, Pi.mul_apply, h1]
  have hXmi : Integrable (fun ω => (v ω + Y ω) * m (v ω + Y ω)) P :=
    integrable_condExp.congr hXm.symm
  have hEXm : ∫ ω, (v ω + Y ω) * m (v ω + Y ω) ∂P = (∫ ω, Y ω ∂P) * ∫ ω, v ω ^ 2 ∂P := by
    rw [integral_congr_ae hXm, integral_condExp hle, ← hEXv2]
    rfl
  -- the covariance identity
  set c := ∫ ω, v ω + Y ω ∂P with hc
  have hcY : c = ∫ ω, Y ω ∂P := by rw [hc, integral_add hv1 hY1, hEv, zero_add]
  have hcov : ∀ φ : ℝ → ℝ, Integrable (fun ω => φ (v ω + Y ω)) P →
      Integrable (fun ω => (v ω + Y ω) * φ (v ω + Y ω)) P →
      Integrable (fun ω => (v ω + Y ω - c) * (φ (v ω + Y ω) - φ c)) P ∧
      ∫ ω, (v ω + Y ω - c) * (φ (v ω + Y ω) - φ c) ∂P =
        ∫ ω, (v ω + Y ω) * φ (v ω + Y ω) ∂P - c * ∫ ω, φ (v ω + Y ω) ∂P := by
    intro φ hφ hXφ
    have e : (fun ω => (v ω + Y ω - c) * (φ (v ω + Y ω) - φ c)) = fun ω =>
        ((v ω + Y ω) * φ (v ω + Y ω) - c * φ (v ω + Y ω)) - (φ c * (v ω + Y ω) - c * φ c) := by
      funext ω; ring
    have hA : Integrable (fun ω => (v ω + Y ω) * φ (v ω + Y ω) - c * φ (v ω + Y ω)) P :=
      hXφ.sub (hφ.const_mul c)
    have hB : Integrable (fun ω => φ c * (v ω + Y ω) - c * φ c) P :=
      (hX1.const_mul (φ c)).sub (integrable_const (c * φ c))
    have hC : Integrable (fun ω => c * φ (v ω + Y ω)) P := hφ.const_mul c
    have hD : Integrable (fun ω => φ c * (v ω + Y ω)) P := hX1.const_mul (φ c)
    refine ⟨by rw [e]; exact hA.sub hB, ?_⟩
    rw [e, integral_sub hA hB, integral_sub hXφ hC,
      integral_sub hD (integrable_const _), integral_const_mul,
      integral_const_mul, integral_const, ← hc]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  -- `m'` has constant sign
  have hsign : (∀ x, 0 < deriv m x) ∨ (∀ x, deriv m x < 0) := by
    by_cases hp : ∀ x, 0 < deriv m x
    · exact Or.inl hp
    · right
      obtain ⟨a, ha⟩ := not_forall.1 hp
      have ha' : deriv m a < 0 := lt_of_le_of_ne (not_lt.1 ha) (hne' a)
      intro x
      by_contra hx
      have hx' : 0 < deriv m x := lt_of_le_of_ne (not_lt.1 hx) (hne' x).symm
      obtain ⟨z, hz⟩ := intermediate_value_univ a x hdmc ⟨ha'.le, hx'.le⟩
      exact hne' z hz
  rcases hsign with hpos | hneg
  · have hmono : StrictMono m := strictMono_of_deriv_pos hpos
    obtain ⟨hDi, hD⟩ := hcov m hmXi hXmi
    rw [hEXm, hEm, ← hcY, sub_self] at hD
    exact hnd c (ae_eq_of_integral_mono_zero hmono c hDi hD)
  · have hmono : StrictMono (fun x => -m x) := (strictAnti_of_deriv_neg hneg).neg
    obtain ⟨hDi, hD⟩ := hcov (fun x => -m x) hmXi.neg (by simpa using hXmi.neg)
    have e1 : ∫ ω, (v ω + Y ω) * -m (v ω + Y ω) ∂P = -((∫ ω, Y ω ∂P) * ∫ ω, v ω ^ 2 ∂P) := by
      rw [← hEXm, ← integral_neg]; congr 1; funext ω; ring
    have e2 : ∫ ω, -m (v ω + Y ω) ∂P = -∫ ω, v ω ^ 2 ∂P := by rw [integral_neg, hEm]
    rw [e1, e2, ← hcY] at hD
    have hD' : ∫ ω, (v ω + Y ω - c) * (-m (v ω + Y ω) - -m c) ∂P = 0 := by rw [hD]; ring
    exact hnd c (ae_eq_of_integral_mono_zero hmono c hDi hD')

end CC.General
