import ConformityConcerns.LearnTheta.Defs
import ConformityConcerns.Interventions.Sensitivity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The conformity loss `m` in the Linear-Gaussian model

The proof of Corollary A3 uses the closed form of `m(ṽ_t | h^t) = E(v_t² | ṽ_t, h^t)` when
`v_t ~ N(0, σ_v²)` and `Y_t = E(θ | s_t, h^t) ~ N(θ(h^t), τ)` given `h^t`, where
`τ = σ⁴_{θ,t}/(1 + σ²_{θ,t})`:

`m(x) = σ_v² τ/(σ_v² + τ) + (σ_v²/(σ_v² + τ))² (x - θ(h^t))²` (`mfun_gaussian`).

So `m` is quadratic, with `0 < m'' ≤ 2` (`mfun_gaussian_regular`), the assumption of
Proposition A5, and when `σ_v² = 1` the second derivative is `2 s̃(h^t)²`
(`mfun_gaussian_sens`), which is decreasing in `σ²_{θ,t}`.
-/

namespace CC.LearnTheta

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

section Product

variable {s τ : ℝ≥0}

/-- The posterior variance `s τ/(s + τ)`. -/
noncomputable def pv (s τ : ℝ≥0) : ℝ≥0 := s * τ / (s + τ)

/-- The posterior mean `(s b + τ x)/(s + τ)`. -/
noncomputable def pm (s τ : ℝ≥0) (b x : ℝ) : ℝ := ((s : ℝ) * b + τ * x) / (s + τ)

lemma pv_ne (hs : s ≠ 0) (hτ : τ ≠ 0) : pv s τ ≠ 0 := by
  unfold pv
  exact div_ne_zero (mul_ne_zero hs hτ) (add_ne_zero.2 (Or.inl hs))

/-- The product of two Gaussian densities. -/
lemma gaussian_pdf_mul (hs : s ≠ 0) (hτ : τ ≠ 0) (b x y : ℝ) :
    gaussianPDFReal 0 s (x - y) * gaussianPDFReal b τ y =
      gaussianPDFReal b (s + τ) x * gaussianPDFReal (pm s τ b x) (pv s τ) y := by
  have hs' : (0 : ℝ) < s := by positivity
  have hτ' : (0 : ℝ) < τ := by positivity
  have hsum : (0 : ℝ) < (s : ℝ) + τ := by positivity
  have hpv : ((pv s τ : ℝ≥0) : ℝ) = (s : ℝ) * τ / ((s : ℝ) + τ) := by
    simp [pv]
  unfold gaussianPDFReal
  rw [hpv, NNReal.coe_add]
  have hsq : √(2 * π * (s : ℝ)) * √(2 * π * (τ : ℝ)) =
      √(2 * π * ((s : ℝ) + τ)) * √(2 * π * ((s : ℝ) * τ / ((s : ℝ) + τ))) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hexp : -(x - y - 0) ^ 2 / (2 * (s : ℝ)) + -(y - b) ^ 2 / (2 * (τ : ℝ)) =
      -(x - b) ^ 2 / (2 * ((s : ℝ) + τ)) +
        -(y - pm s τ b x) ^ 2 / (2 * ((s : ℝ) * τ / ((s : ℝ) + τ))) := by
    unfold pm
    field_simp
    ring
  calc (√(2 * π * (s : ℝ)))⁻¹ * rexp (-(x - y - 0) ^ 2 / (2 * (s : ℝ))) *
        ((√(2 * π * (τ : ℝ)))⁻¹ * rexp (-(y - b) ^ 2 / (2 * (τ : ℝ))))
      = (√(2 * π * (s : ℝ)) * √(2 * π * (τ : ℝ)))⁻¹ *
          rexp (-(x - y - 0) ^ 2 / (2 * (s : ℝ)) + -(y - b) ^ 2 / (2 * (τ : ℝ))) := by
        rw [Real.exp_add, mul_inv]; ring
    _ = _ := by
        rw [hsq, hexp, Real.exp_add, mul_inv]; ring

/-- The second moment around `x` of `N(m, v)`. -/
lemma integral_sub_sq_gaussian (x m : ℝ) (v : ℝ≥0) :
    ∫ y, (x - y) ^ 2 ∂(gaussianReal m v) = v + (x - m) ^ 2 := by
  have h2 : Integrable (fun y : ℝ => y ^ 2) (gaussianReal m v) :=
    (memLp_id_gaussianReal (μ := m) (v := v) 2).integrable_sq
  have h1 : Integrable (fun y : ℝ => y) (gaussianReal m v) :=
    (memLp_id_gaussianReal (μ := m) (v := v) 1).integrable le_rfl
  have hm : ∫ y, y ∂(gaussianReal m v) = m := integral_id_gaussianReal
  have hv : ∫ y, (y - m) ^ 2 ∂(gaussianReal m v) = v := by
    have := variance_id_gaussianReal (μ := m) (v := v)
    rw [variance_eq_integral aemeasurable_id] at this
    simpa [integral_id_gaussianReal] using this
  have e : ∀ y : ℝ, (x - y) ^ 2 = (y - m) ^ 2 + (2 * (m - x)) * y + (x ^ 2 - m ^ 2) := by
    intro y; ring
  have hi2 : Integrable (fun y : ℝ => (y - m) ^ 2) (gaussianReal m v) := by
    have : (fun y : ℝ => (y - m) ^ 2) =
        fun y => y ^ 2 + (-(2 * m)) * y + m ^ 2 := by funext y; ring
    rw [this]
    exact (h2.add (h1.const_mul _)).add (integrable_const _)
  have e' : (fun y : ℝ => (x - y) ^ 2) =
      fun y => ((y - m) ^ 2 + (2 * (m - x)) * y) + (x ^ 2 - m ^ 2) := funext e
  have hadd : Integrable (fun y : ℝ => (y - m) ^ 2 + (2 * (m - x)) * y) (gaussianReal m v) :=
    hi2.add (h1.const_mul _)
  rw [e', integral_add hadd (integrable_const _),
    integral_add hi2 (h1.const_mul _), integral_const_mul, hm, hv]
  simp only [integral_const, probReal_univ, smul_eq_mul]
  ring

/-- `m` in closed form when `τ > 0`. -/
lemma mfun_gaussian_pos (hs : s ≠ 0) (hτ : τ ≠ 0) (b x : ℝ) :
    mfun (gaussianPDFReal 0 s) (gaussianReal b τ) x =
      (s : ℝ) * τ / (s + τ) + ((s : ℝ) / (s + τ)) ^ 2 * (x - b) ^ 2 := by
  have hs' : (0 : ℝ) < s := by positivity
  have hτ' : (0 : ℝ) < τ := by positivity
  have hsum : (0 : ℝ) < (s : ℝ) + τ := by positivity
  set C := gaussianPDFReal b (s + τ) x with hC
  have hCpos : 0 < C := gaussianPDFReal_pos _ _ _ (add_ne_zero.2 (Or.inl hs))
  have hnum : ∫ y, (x - y) ^ 2 * gaussianPDFReal 0 s (x - y) ∂(gaussianReal b τ) =
      C * ((pv s τ : ℝ) + (x - pm s τ b x) ^ 2) := by
    rw [integral_gaussianReal_eq_integral_smul hτ, ← integral_sub_sq_gaussian,
      integral_gaussianReal_eq_integral_smul (pv_ne hs hτ), ← integral_const_mul]
    congr 1
    funext y
    have := gaussian_pdf_mul hs hτ b x y
    simp only [smul_eq_mul]
    calc gaussianPDFReal b τ y * ((x - y) ^ 2 * gaussianPDFReal 0 s (x - y))
        = (gaussianPDFReal 0 s (x - y) * gaussianPDFReal b τ y) * (x - y) ^ 2 := by ring
      _ = _ := by rw [this, ← hC]; ring
  have hden : ∫ y, gaussianPDFReal 0 s (x - y) ∂(gaussianReal b τ) = C := by
    rw [integral_gaussianReal_eq_integral_smul hτ]
    have e : ∀ y, gaussianPDFReal b τ y • gaussianPDFReal 0 s (x - y) =
        C * gaussianPDFReal (pm s τ b x) (pv s τ) y := by
      intro y
      have := gaussian_pdf_mul hs hτ b x y
      rw [smul_eq_mul, mul_comm, this, ← hC]
    simp_rw [e]
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ (pv_ne hs hτ), mul_one]
  unfold mfun
  rw [hnum, hden, mul_div_cancel_left₀ _ hCpos.ne']
  have hpv : ((pv s τ : ℝ≥0) : ℝ) = (s : ℝ) * τ / ((s : ℝ) + τ) := by simp [pv]
  rw [hpv]
  unfold pm
  field_simp
  ring

/-- **The closed form of `m`** (proof of Corollary A3). With `v_t ~ N(0, s)` and
`Y_t ~ N(b, τ)` given the history, `m(x) = s τ/(s + τ) + (s/(s + τ))² (x - b)²`. -/
theorem mfun_gaussian (hs : s ≠ 0) (τ : ℝ≥0) (b x : ℝ) :
    mfun (gaussianPDFReal 0 s) (gaussianReal b τ) x =
      (s : ℝ) * τ / (s + τ) + ((s : ℝ) / (s + τ)) ^ 2 * (x - b) ^ 2 := by
  by_cases hτ : τ = 0
  · subst hτ
    have hs' : (0 : ℝ) < s := by positivity
    have hp : gaussianPDFReal 0 s (x - b) ≠ 0 := (gaussianPDFReal_pos _ _ _ hs).ne'
    simp only [mfun, gaussianReal_zero_var, integral_dirac, NNReal.coe_zero, mul_zero, zero_div,
      add_zero, zero_add]
    rw [mul_div_assoc, div_self hp, div_self hs'.ne']
    ring
  · exact mfun_gaussian_pos hs hτ b x

end Product

variable {s : ℝ≥0}

/-- `m` is quadratic, so `C²` with `m'' = 2 (s/(s + τ))² ∈ (0, 2]`: the assumption of
Proposition A5 holds at every history with Gaussian beliefs. -/
theorem mfun_gaussian_regular (hs : s ≠ 0) (τ : ℝ≥0) (b : ℝ) :
    ContDiff ℝ 2 (mfun (gaussianPDFReal 0 s) (gaussianReal b τ)) ∧
      ∀ x, iteratedDeriv 2 (mfun (gaussianPDFReal 0 s) (gaussianReal b τ)) x =
          2 * ((s : ℝ) / (s + τ)) ^ 2 ∧
        0 < iteratedDeriv 2 (mfun (gaussianPDFReal 0 s) (gaussianReal b τ)) x ∧
        iteratedDeriv 2 (mfun (gaussianPDFReal 0 s) (gaussianReal b τ)) x ≤ 2 := by
  have hs' : (0 : ℝ) < s := by positivity
  have hsum : (0 : ℝ) < (s : ℝ) + τ := by positivity
  have hF : mfun (gaussianPDFReal 0 s) (gaussianReal b τ) =
      fun x => (s : ℝ) * τ / (s + τ) + ((s : ℝ) / (s + τ)) ^ 2 * (x - b) ^ 2 :=
    funext fun x => mfun_gaussian hs τ b x
  rw [hF]
  have hd : deriv (fun x : ℝ => (s : ℝ) * τ / (s + τ) + ((s : ℝ) / (s + τ)) ^ 2 * (x - b) ^ 2) =
      fun x => ((s : ℝ) / (s + τ)) ^ 2 * (2 * (x - b)) := by
    funext x
    have h1 : HasDerivAt (fun x : ℝ => (x - b) ^ 2) (2 * (x - b)) x := by
      simpa using ((hasDerivAt_id x).sub_const b).fun_pow 2
    exact ((h1.const_mul _).const_add _).deriv
  have h2 : ∀ x, iteratedDeriv 2
      (fun x : ℝ => (s : ℝ) * τ / (s + τ) + ((s : ℝ) / (s + τ)) ^ 2 * (x - b) ^ 2) x =
      2 * ((s : ℝ) / (s + τ)) ^ 2 := by
    intro x
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
    have h1 : HasDerivAt (fun x : ℝ => ((s : ℝ) / (s + τ)) ^ 2 * (2 * (x - b)))
        (((s : ℝ) / (s + τ)) ^ 2 * (2 * 1)) x :=
      (((hasDerivAt_id x).sub_const b).const_mul 2).const_mul _
    rw [h1.deriv]
    ring
  refine ⟨by fun_prop, fun x => ⟨h2 x, ?_, ?_⟩⟩
  · rw [h2]; positivity
  · rw [h2]
    have hle : (s : ℝ) / (s + τ) ≤ 1 := by
      rw [div_le_one hsum]
      have : (0 : ℝ) ≤ τ := τ.2
      linarith
    have h0 : 0 ≤ (s : ℝ) / (s + τ) := by positivity
    nlinarith [pow_le_one₀ h0 hle (n := 2)]

/-- `τ = σ⁴/(1 + σ²)`, the variance of `E(θ | s_t, h^t)` given `h^t`. -/
noncomputable def tauOf (q : ℝ≥0) : ℝ≥0 := q ^ 2 / (1 + q)

/-- **Proof of Corollary A3.** With `σ_v² = 1` and `τ = σ⁴_{θ,t}/(1 + σ²_{θ,t})`,
the second derivative of `m` is `2 s̃(h^t)²`, constant in `x` and independent of `θ(h^t)`. -/
theorem mfun_gaussian_sens (q : ℝ≥0) (b x : ℝ) :
    iteratedDeriv 2 (mfun (gaussianPDFReal 0 1) (gaussianReal b (tauOf q))) x =
      2 * sens !![(q : ℝ), 0; 0, 0] 1 ^ 2 := by
  rw [((mfun_gaussian_regular one_ne_zero (tauOf q) b).2 x).1,
    sens_diag 1 q 0 q.2 le_rfl]
  have hq : (0 : ℝ) ≤ q := q.2
  have h1 : (1 : ℝ) + q ≠ 0 := by positivity
  simp only [sensDiag, tauOf, NNReal.coe_one, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_add]
  field_simp
  try ring

/-- The second derivative of `m` is decreasing in `σ²_{θ,t}` (proof of Corollary A3). -/
theorem secondDeriv_antitone :
    AntitoneOn (fun q : ℝ => 2 * sens !![q, 0; 0, 0] 1 ^ 2) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hanti := (lemma2 (1 : ℝ)).1 0 le_rfl hx hy hxy
  have h0 : 0 ≤ sens !![y, 0; 0, 0] 1 := by
    rw [sens_diag 1 y 0 hy le_rfl]
    have : (0 : ℝ) ≤ y := hy
    unfold sensDiag
    positivity
  simp only at hanti
  have := pow_le_pow_left₀ h0 hanti 2
  linarith

end CC.LearnTheta
