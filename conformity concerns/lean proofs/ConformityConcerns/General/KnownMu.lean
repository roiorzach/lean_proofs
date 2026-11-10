import ConformityConcerns.General.Defs
import ConformityConcerns.General.Revealing
import ConformityConcerns.General.Pooling
import ConformityConcerns.General.KnownMuMinimizer
import ConformityConcerns.ODE.LeftTail
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Proposition A5 (General Distributions with `μ` known) — the fixed-history statements

At a fixed history `h^t` (`μ = 0` known, `γ_t = 1`), the one-dimensional type is
`ṽ = v + Y` with `Y = E(θ | s_t, h^t)` independent of `v`, and
`m(x) = E(v² | ṽ = x)`, assumed `C²` with `0 < m'' ≤ 2`. Being perceived as type `ṽ` costs
`κ m(ṽ)`; net of its minimum (which does not affect incentives) the conformity loss is
`ℓ(x) = κ (m(x) - m(x*))` where `m'(x*) = 0`. The adaptation loss is `(a - ṽ)²` (up to the
constant `Var(θ | s_t, h^t)`). We assume directly that `ṽ` has an everywhere-positive continuous
density (the paper derives this from its density assumption on `v_t`).
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- `m'` has a unique zero `x*` (proof of Proposition A5: `Cov(ṽ, m(ṽ)) = Cov(v, v²) = 0` by
symmetry of `v`). The type `ṽ = v + Y` has a density (the paper's footnote: its density
assumption on `v_t` implies that `ṽ_t` has a continuous density). -/
theorem propA5_minimizer {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (v Y : Ω → ℝ) (hv : Measurable v) (hY : Measurable Y) (hind : IndepFun v Y P)
    (hsymm : P.map v = P.map (fun ω => -v ω)) (h3 : Integrable (fun ω => |v ω| ^ 3) P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P)
    (hac : P.map (fun ω => v ω + Y ω) ≪ volume) (m : ℝ → ℝ) (hm : ContDiff ℝ 2 m)
    (hm2 : ∀ x, 0 < iteratedDeriv 2 m x ∧ iteratedDeriv 2 m x ≤ 2)
    (hcond : (fun ω => m (v ω + Y ω)) =ᵐ[P]
      P[fun ω => v ω ^ 2 | MeasurableSpace.comap (fun ω => v ω + Y ω) inferInstance]) :
    ∃! xs : ℝ, deriv m xs = 0 := by
  refine propA5_minimizer_of_nondegenerate v Y hv hY hind hsymm h3 hY2 m hm hm2 hcond ?_
  intro c hc
  have hmap : P.map (fun ω => v ω + Y ω) = Measure.dirac c := by
    rw [Measure.map_congr hc, Measure.map_const, measure_univ, one_smul]
  have h0 : P.map (fun ω => v ω + Y ω) {c} = 0 := hac (Real.volume_singleton)
  rw [hmap, Measure.dirac_apply_of_mem (Set.mem_singleton c)] at h0
  exact one_ne_zero h0

/-- **Proposition A5 (fixed history).** With `m̲ = inf m''/2 ≤ sup m''/2 = m̄`: a fully revealing
equilibrium satisfying `D1^∞` exists if `κ ≤ κck/m̄`, and no equilibrium with revelation satisfies
`D1^∞` if `κ > κck/m̲` (every one is fully pooling). Here `S.μ = x*` and `S.F` is the law of `ṽ`. -/
theorem propA5_period (κ : ℝ) (hκ : 0 < κ) (m : ℝ → ℝ) (hm : ContDiff ℝ 2 m)
    (hm2 : ∀ x, 0 < iteratedDeriv 2 m x ∧ iteratedDeriv 2 m x ≤ 2) (S : Setting)
    (hx : deriv m S.μ = 0) (hg : S.g = fun z => z ^ 2) (hℓ : S.ℓ = fun x => κ * (m x - m S.μ)) :
    ((∀ x, κ * (iteratedDeriv 2 m x / 2) ≤ κck) →
      ∃ (a : ℝ → ℝ) (φ : ℝ → Measure EReal), S.IsCPBE a φ ∧ S.D1Inf a φ ∧ StrictMono a) ∧
    ((∃ c, κck < c ∧ ∀ x, c ≤ κ * (iteratedDeriv 2 m x / 2)) →
      ∀ (a : ℝ → ℝ) (φ : ℝ → Measure EReal), S.IsCPBE a φ → S.D1Inf a φ → ∃ c : ℝ, ∀ v, a v = c) := by
  have hmd : Differentiable ℝ m := hm.differentiable (by norm_num)
  have hm1 : ContDiff ℝ 1 (deriv m) := hm.deriv'
  have h2 : ∀ x, iteratedDeriv 2 m x = deriv (deriv m) x := fun x => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hdm : StrictMono (deriv m) :=
    strictMono_of_deriv_pos (fun x => by rw [← h2]; exact (hm2 x).1)
  set f : ℝ → ℝ := fun x => deriv m x / 2 with hfdef
  have hfm : StrictMono f := fun x y hxy => by
    simp only [hfdef]; linarith [hdm hxy]
  have hf1 : ContDiff ℝ 1 f := hm1.div_const 2
  have hfc : f S.μ = 0 := by simp only [hfdef, hx, zero_div]
  have hfd : ∀ x, deriv f x = iteratedDeriv 2 m x / 2 := fun x => by
    simp only [hfdef]; rw [deriv_div_const, h2]
  have hℓ' : ∀ v, deriv S.ℓ v = κ * deriv m v := fun v => by
    rw [hℓ]; exact (((hmd v).hasDerivAt.sub_const (m S.μ)).const_mul κ).deriv
  have hg' : ∀ z, deriv S.g z = 2 * z := fun z => by rw [hg]; exact Rev.deriv_sq_fun z
  have hval : ∀ v w, deriv S.ℓ v / deriv S.g (v - w) = κ * f v / (v - w) := by
    intro v w; rw [hℓ', hg']; simp only [hfdef]; rw [mul_div_assoc', div_div]
  constructor
  · intro hsup
    obtain ⟨a, hac, ha0, ham, hd⟩ := Rev.exists_solution hκ hfm hf1 hfc
      (fun v => by rw [hfd]; exact hsup v)
    -- there are no off-path actions
    have hs := Rev.surjective_of_ode hκ hfm hfc hac ha0 ham hd
    obtain ⟨hmono, φ, hE, hD⟩ := Rev.exists_revealing_surjective S hac
      (fun r hr => by rw [hval]; exact (hd r hr).1) (fun r hr => by rw [hval]; exact (hd r hr).2) hs
    exact ⟨a, φ, hE, hD, hmono⟩
  · rintro ⟨c₀, hc₀, hle⟩ a φ h hD
    have hinf : ∀ P : ℝ → Prop, ∃ m₀ : ℝ, κck < κ * m₀ ∧ ∀ v, P v → m₀ ≤ deriv f v := fun P =>
      ⟨c₀ / κ, by rw [mul_div_cancel₀ _ hκ.ne']; exact hc₀, fun v _ => by
        rw [hfd, div_le_iff₀ hκ]; linarith [hle v]⟩
    apply Rev.const_of_noTails S h hD
    · rintro d hd ⟨hc, hC1, hlt, hder⟩
      apply CC.ODE.lemmaA3_iv κ hκ f hfm hf1 hfc d hd.le (hinf _) a
      refine ⟨⟨hc, hC1, fun v hv => hlt v hv.le, fun v hv => (hder v hv.le).congr_deriv ?_⟩,
        (hlt d le_rfl).le⟩
      rw [hval]; simp only [id, add_sub_cancel]
    · rintro d hd ⟨hc, hC1, hlt, hder⟩
      apply CC.ODE.corollaryA1_iv κ hκ f hfm hf1 hfc d hd.le (hinf _) a
      refine ⟨⟨hc, hC1, fun v hv => hlt v hv.le, fun v hv => (hder v hv.le).congr_deriv ?_⟩,
        (hlt d le_rfl).le⟩
      rw [hval]; simp only [id]
      rw [show S.μ - (S.μ - v) = v by ring, show a v - v = -(v - a v) by ring, div_neg,
        neg_mul, neg_div, neg_neg]

end CC.General
