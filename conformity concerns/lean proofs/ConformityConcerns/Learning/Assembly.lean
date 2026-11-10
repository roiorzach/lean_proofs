import ConformityConcerns.Learning.Basic
import ConformityConcerns.General.Quadratic
import ConformityConcerns.General.GeneralLoss

/-!
# Propositions A4 and A6: equilibria across histories and social learning about preferences

A profile `c` is an equilibrium satisfying `D1^∞` if at every history `h` the period strategy
`c t h` is (with some beliefs) a compactified PBE satisfying `D1^∞` of the period environment at
`h` — whose norm is `μ(h)` and whose type distribution is the law of `v_t` given `h`. The
statements below only require this for *some* environment with the right losses at each
history, which makes the pooling conclusions stronger.
-/

namespace CC.Learning

open MeasureTheory ProbabilityTheory Filter Topology
open CC.General

/-- **Proposition A4 (social learning).** If `κ ≤ κck` there is an equilibrium satisfying `D1^∞`
(fully revealing at every history) with social learning about preferences; if `κ > κck` every
equilibrium satisfying `D1^∞` is fully pooling at every history and social learning fails.
Hence an equilibrium satisfying `D1^∞` with social learning exists iff `κ ≤ κck`. -/
theorem propA4_learning (κ : ℝ) (hκ : 0 < κ) (Lμ Lν : Measure ℝ) [IsProbabilityMeasure Lμ]
    [IsProbabilityMeasure Lν] (hμ : Integrable id Lμ) (hatom : ∀ x, Lμ {x} = 0)
    (hν : Integrable id Lν) (hν0 : ∫ x, x ∂Lν = 0) :
    let P := law Lμ Lν
    (κ ≤ κck → ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
      (∀ S : Setting, S.g = (fun z => z ^ 2) → S.ℓ = (fun b => κ * (b - S.μ) ^ 2) →
        ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
          S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ) ∧
      SocialLearningOccurs Lμ Lν (postMean P (revealAct Φ (fun t => P[muV | typeSigma t])))) ∧
    (κck < κ → ∀ c : Profile,
      (∀ t (h : Fin t → ℝ), ∃ S : Setting, S.g = (fun z => z ^ 2) ∧
        S.ℓ = (fun b => κ * (b - S.μ) ^ 2) ∧ ∃ φ : ℝ → Measure EReal, S.IsCPBE (c t h) φ ∧
          S.D1Inf (c t h) φ) →
      (∀ t (h : Fin t → ℝ) (v w : ℝ), c t h v = c t h w) ∧
        SocialLearningFails Lμ Lν (postMean P (play c))) := by
  intro P
  refine ⟨fun hκ' => ?_, fun hκ' c hc => ?_⟩
  · obtain ⟨Φ, hΦ, hΦc, -, hΦeq⟩ := propA4_revealing κ hκ hκ'
    exact ⟨Φ, hΦ, hΦeq, (learning_revealing Lμ Lν hμ hν hν0 Φ hΦ hΦc).2.2.2⟩
  · have hpool : ∀ t (h : Fin t → ℝ) (v w : ℝ), c t h v = c t h w := by
      intro t h v w
      obtain ⟨S, hg, hℓ, φ, hE, hD⟩ := hc t h
      obtain ⟨k, hk⟩ := propA4_pooling κ hκ' S hg hℓ (c t h) φ hE hD
      rw [hk v, hk w]
    exact ⟨hpool, (learning_pooling Lμ Lν hμ hatom c hpool).2⟩

/-- **Proposition A6.** Suppose `μ` has an atomless distribution with finite mean (finite variance
in the paper) and `ν_t` has mean zero. (i) If `liminf f'(x)/g'(x+C) > 1` for every `C`, every
equilibrium satisfying `D1^∞` is fully pooling at every history and social learning about
preferences fails. (ii) If `f'(x) ≤ (1-β) g'(βx)` for all `x > 0` and some `β ∈ (0,1)`, there is
an equilibrium satisfying `D1^∞` with `μ(h^t) → μ` almost surely. -/
theorem propA6 (g f : ℝ → ℝ) (hg : AdaptLoss g) (hf : AdaptLoss f) (Lμ Lν : Measure ℝ)
    [IsProbabilityMeasure Lμ] [IsProbabilityMeasure Lν] (hμ : Integrable id Lμ)
    (hatom : ∀ x, Lμ {x} = 0) (hν : Integrable id Lν) (hν0 : ∫ x, x ∂Lν = 0) :
    let P := law Lμ Lν
    ((∀ C : ℝ, ∃ ε > 0, ∀ᶠ x in atTop, 1 + ε ≤ deriv f x / deriv g (x + C)) →
      ∀ c : Profile,
        (∀ t (h : Fin t → ℝ), ∃ S : Setting, S.g = g ∧ S.ℓ = (fun b => f (b - S.μ)) ∧
          ∃ φ : ℝ → Measure EReal, S.IsCPBE (c t h) φ ∧ S.D1Inf (c t h) φ) →
        (∀ t (h : Fin t → ℝ) (v w : ℝ), c t h v = c t h w) ∧
          SocialLearningFails Lμ Lν (postMean P (play c))) ∧
    ((∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ x, 0 < x → deriv f x ≤ (1 - β) * deriv g (β * x)) →
      ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
        (∀ S : Setting, S.g = g → S.ℓ = (fun b => f (b - S.μ)) →
          ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
            S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ) ∧
        ∀ᵐ ω ∂P, Tendsto (fun t => postMean P (revealAct Φ (fun t => P[muV | typeSigma t])) t ω)
          atTop (𝓝 (muV ω))) := by
  intro P
  refine ⟨fun hcond c hc => ?_, fun ⟨β, hβ0, hβ1, hcond⟩ => ?_⟩
  · have hpool : ∀ t (h : Fin t → ℝ) (v w : ℝ), c t h v = c t h w := by
      intro t h v w
      obtain ⟨S, hgS, hℓ, φ, hE, hD⟩ := hc t h
      have hcond' : ∀ C : ℝ, ∃ ε > 0, ∀ᶠ x in atTop, 1 + ε ≤ deriv f x / deriv S.g (x + C) := by
        rw [hgS]; exact hcond
      obtain ⟨k, hk⟩ := propA6_i_period f hf S hℓ hcond' (c t h) φ hE hD
      rw [hk v, hk w]
    exact ⟨hpool, (learning_pooling Lμ Lν hμ hatom c hpool).2⟩
  · obtain ⟨Φ, hΦ, hΦc, -, hΦeq⟩ := propA6_ii_period g f hg hf β hβ0 hβ1 hcond
    exact ⟨Φ, hΦ, hΦeq, (learning_revealing Lμ Lν hμ hν hν0 Φ hΦ hΦc).2.2.1⟩

end CC.Learning
