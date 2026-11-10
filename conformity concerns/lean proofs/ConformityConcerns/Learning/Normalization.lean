import ConformityConcerns.Learning.Assembly

/-!
# Proposition A6 without normalizing the losses at zero

Subsection "Generalized Loss Functions" assumes that `g` and `f` are twice continuously
differentiable, strictly convex and symmetric, with a unique minimum at zero, without fixing their
value at zero. The value at zero is irrelevant: subtracting `g 0` and `f 0` from the losses changes
every payoff by a constant and leaves the derivatives unchanged. `propA6_unnormalized` is
Proposition A6 stated that way, for the losses `g - g 0` and `f - f 0`.
-/

namespace CC.Learning

open MeasureTheory ProbabilityTheory Filter Topology
open CC.General

/-- A `C²`, even, strictly convex function, with its value at zero subtracted. -/
lemma adaptLoss_sub_zero {g : ℝ → ℝ} (h2 : ContDiff ℝ 2 g) (he : ∀ z, g (-z) = g z)
    (hc : StrictConvexOn ℝ Set.univ g) : AdaptLoss (fun z => g z - g 0) where
  smooth := h2.sub contDiff_const
  even z := by simp only [he]
  strictConvex := by
    refine ⟨convex_univ, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := hc.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    have e : a * (g x - g 0) + b * (g y - g 0) = a * g x + b * g y - (a + b) * g 0 := by ring
    rw [e, hab, one_mul]
    linarith
  zero := sub_self _

lemma deriv_sub_zero (g : ℝ → ℝ) : deriv (fun z => g z - g 0) = deriv g := by
  funext x
  simp

/-- **Proposition A6, without normalizing the losses at zero.** -/
theorem propA6_unnormalized (g f : ℝ → ℝ) (hg2 : ContDiff ℝ 2 g) (hge : ∀ z, g (-z) = g z)
    (hgc : StrictConvexOn ℝ Set.univ g) (hf2 : ContDiff ℝ 2 f) (hfe : ∀ z, f (-z) = f z)
    (hfc : StrictConvexOn ℝ Set.univ f) (Lμ Lν : Measure ℝ) [IsProbabilityMeasure Lμ]
    [IsProbabilityMeasure Lν] (hμ : Integrable id Lμ) (hatom : ∀ x, Lμ {x} = 0)
    (hν : Integrable id Lν) (hν0 : ∫ x, x ∂Lν = 0) :
    let P := law Lμ Lν
    ((∀ C : ℝ, ∃ ε > 0, ∀ᶠ x in atTop, 1 + ε ≤ deriv f x / deriv g (x + C)) →
      ∀ c : Profile,
        (∀ t (h : Fin t → ℝ), ∃ S : Setting, S.g = (fun z => g z - g 0) ∧
          S.ℓ = (fun b => f (b - S.μ) - f 0) ∧
          ∃ φ : ℝ → Measure EReal, S.IsCPBE (c t h) φ ∧ S.D1Inf (c t h) φ) →
        (∀ t (h : Fin t → ℝ) (v w : ℝ), c t h v = c t h w) ∧
          SocialLearningFails Lμ Lν (postMean P (play c))) ∧
    ((∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ x, 0 < x → deriv f x ≤ (1 - β) * deriv g (β * x)) →
      ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
        (∀ S : Setting, S.g = (fun z => g z - g 0) → S.ℓ = (fun b => f (b - S.μ) - f 0) →
          ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
            S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ) ∧
        ∀ᵐ ω ∂P, Tendsto (fun t => postMean P (revealAct Φ (fun t => P[muV | typeSigma t])) t ω)
          atTop (𝓝 (muV ω))) := by
  have h := propA6 (fun z => g z - g 0) (fun z => f z - f 0) (adaptLoss_sub_zero hg2 hge hgc)
    (adaptLoss_sub_zero hf2 hfe hfc) Lμ Lν hμ hatom hν hν0
  simpa only [deriv_sub_zero] using h

end CC.Learning
