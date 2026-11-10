import ConformityConcerns.General.PayoffContinuity
import ConformityConcerns.General.CP.FullPool
import ConformityConcerns.General.CP.Structure
import ConformityConcerns.General.CP.Envelope
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Proposition A3 (central pooling)

Stated for a general conformity loss `ℓ` (`C²`, strictly convex, minimised at the norm `μ`);
the paper's statement is the case `ℓ b = f (b - μ)` with `f` even (`propA3_i_even`).
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- The paper's case: the conformity loss `ℓ b = f (b - μ)` with `f` even, strictly convex,
`C²`, `f 0 = 0` satisfies the standing assumptions on `ℓ`. -/
lemma confLoss_of_even {f : ℝ → ℝ} (hf : AdaptLoss f) (μ : ℝ) :
    ConfLoss (fun b => f (b - μ)) μ := by
  have hsub : ContDiff ℝ 2 (fun b : ℝ => b - μ) := by fun_prop
  refine ⟨hf.smooth.comp hsub, ⟨convex_univ, ?_⟩,
    by simp [hf.zero], fun b => by simp only [sub_self]; exact hf.isMin _⟩
  intro x _ y _ hxy s t hs ht hst
  have hne : x - μ ≠ y - μ := fun h => hxy (by linarith)
  have := hf.strictConvex.2 (mem_univ (x - μ)) (mem_univ (y - μ)) hne hs ht hst
  simp only [smul_eq_mul] at this ⊢
  have e : s * x + t * y - μ = s * (x - μ) + t * (y - μ) := by linear_combination μ * hst
  rw [e]; exact this

/-- **Proposition A3 (i).** Every pure compactified perfect Bayesian equilibrium satisfying
`D1^∞` is a central pooling equilibrium, and on each nonempty separating tail the action rule is
continuously differentiable and satisfies `a'(v) = ℓ'(v)/g'(v - a(v)) > 0`. -/
theorem propA3_i (S : Setting) {a : ℝ → ℝ} {φ : ℝ → Measure EReal} (h : S.IsCPBE a φ)
    (hD : S.D1Inf a φ) :
    ∃ vlo vhi : EReal, ∃ c : ℝ, S.IsCentralPoolingWith a vlo vhi c ∧ S.TailODE a vlo vhi := by
  obtain ⟨vlo, vhi, c, hcp⟩ := h.centralPooling hD
  refine ⟨vlo, vhi, c, hcp, ?_⟩
  have hOhi : IsOpen {v : ℝ | vhi < (v : EReal)} :=
    isOpen_lt continuous_const continuous_coe_real_ereal
  have hOlo : IsOpen {v : ℝ | (v : EReal) < vlo} :=
    isOpen_lt continuous_coe_real_ereal continuous_const
  have hi := h.tail_ode hD hOhi (fun v hv => Setting.sep_of_centralPooling hcp (Or.inr hv))
    (fun v hv heq => by
      have h1 : vhi < (v : EReal) := hv
      rw [heq] at h1
      exact absurd hcp.2.1 (not_le.2 h1))
  have lo := h.tail_ode hD hOlo (fun v hv => Setting.sep_of_centralPooling hcp (Or.inl hv))
    (fun v hv heq => by
      have h1 : (v : EReal) < vlo := hv
      rw [heq] at h1
      exact absurd hcp.1 (not_le.2 h1))
  refine ⟨hi.1, lo.1, fun v hv => ?_⟩
  rcases hv with hv | hv
  · exact lo.2 v hv
  · exact hi.2 v hv

/-- **Proposition A3 (ii).** For every `c ∈ ℝ`, the fully pooling strategy `a(v) = c` with
on-path posterior `F`, posterior `δ_{+∞}` after `x > c` and `δ_{-∞}` after `x < c`, is a
compactified perfect Bayesian equilibrium satisfying `D1^∞`. -/
theorem propA3_ii (S : Setting) (c : ℝ) :
    S.IsCPBE (fun _ => c) (S.poolBelief c) ∧ S.D1Inf (fun _ => c) (S.poolBelief c) :=
  ⟨S.fullPool_isCPBE c, S.fullPool_D1Inf c⟩

end CC.General

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- **Proposition A3 (i), the paper's form.** With conformity loss `ℓ(b) = f(b - μ)` for an even,
strictly convex, `C²` function `f` with `f 0 = 0`, every pure compactified PBE satisfying `D1^∞`
is central pooling, and on each separating tail `a'(v) = f'(v - μ)/g'(v - a(v)) > 0`. -/
theorem propA3_i_even (S : Setting) {f : ℝ → ℝ} (_hf : AdaptLoss f)
    (hℓ : S.ℓ = fun b => f (b - S.μ)) {a : ℝ → ℝ} {φ : ℝ → Measure EReal} (h : S.IsCPBE a φ)
    (hD : S.D1Inf a φ) :
    ∃ vlo vhi : EReal, ∃ c : ℝ, S.IsCentralPoolingWith a vlo vhi c ∧
      ContDiffOn ℝ 1 a {v : ℝ | vhi < (v : EReal)} ∧ ContDiffOn ℝ 1 a {v : ℝ | (v : EReal) < vlo} ∧
      ∀ v : ℝ, ((v : EReal) < vlo ∨ vhi < (v : EReal)) →
        0 < deriv f (v - S.μ) / deriv S.g (v - a v) ∧
          HasDerivAt a (deriv f (v - S.μ) / deriv S.g (v - a v)) v := by
  obtain ⟨vlo, vhi, c, hcp, h1, h2, h3⟩ := propA3_i S h hD
  have hder : ∀ v, deriv S.ℓ v = deriv f (v - S.μ) := fun v => by
    rw [hℓ]; exact deriv_comp_sub_const (f := f) (a := S.μ) (x := v)
  refine ⟨vlo, vhi, c, hcp, h1, h2, fun v hv => ?_⟩
  rw [← hder v]
  exact h3 v hv

end CC.General
