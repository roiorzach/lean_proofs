import ConformityConcerns.General.Defs
import ConformityConcerns.General.Revealing
import ConformityConcerns.General.Pooling
import ConformityConcerns.ODE.LeftTail
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proposition A4 (General Distributions with `θ` known) — the fixed-history statements — and
# Remark A1

At a fixed history `h^t`, `θ` is known, the type `v_t` has distribution `F` (everywhere-positive
continuous density, finite variance), and the losses are quadratic: `g(z) = z²`,
`ℓ(b) = κ (b - μ(h^t))²`. The across-history ("social learning") part of Proposition A4 is in
`Learning/Assembly.lean`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set


/-- **Proposition A4 (existence).** If `κ ≤ κck` there is a fully revealing equilibrium satisfying
`D1^∞`. It has the form `a(v) = μ(h) + Φ(v - μ(h))` for one strictly increasing `Φ` that works at
every history (every norm `μ(h)` and every type distribution `F`). -/
theorem propA4_revealing (κ : ℝ) (hκ : 0 < κ) (hκ' : κ ≤ κck) :
    ∃ Φ : ℝ → ℝ, StrictMono Φ ∧ Continuous Φ ∧ Φ 0 = 0 ∧
      ∀ S : Setting, S.g = (fun z => z ^ 2) → S.ℓ = (fun b => κ * (b - S.μ) ^ 2) →
        ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
          S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ := by
  -- Lemma A3 and Corollary A1, applied to `f(x) = x`, the translate of `f(v) = v - μ(h^t)`
  have hfd : ∀ x : ℝ, deriv (id : ℝ → ℝ) x = 1 := fun x => deriv_id x
  obtain ⟨Φ, hΦc, hΦ0, hΦm, hΦd⟩ := Rev.exists_solution hκ strictMono_id contDiff_id (c := 0) rfl
    (fun x => by rw [hfd, mul_one]; exact hκ')
  -- there are no off-path actions
  have hΦs := Rev.surjective_of_ode hκ strictMono_id (c := 0) rfl hΦc hΦ0 hΦm hΦd
  refine ⟨Φ, hΦm, hΦc, hΦ0, fun S hg hℓ => ?_⟩
  have hc : Continuous (fun v => S.μ + Φ (v - S.μ)) := by fun_prop
  have hval : ∀ r, deriv S.ℓ r / deriv S.g (r - (S.μ + Φ (r - S.μ))) =
      κ * id (r - S.μ) / (r - S.μ - Φ (r - S.μ)) := by
    intro r
    rw [hℓ, hg, Rev.deriv_quad, Rev.deriv_sq_fun,
      show r - (S.μ + Φ (r - S.μ)) = r - S.μ - Φ (r - S.μ) by ring, mul_assoc,
      mul_div_mul_left _ _ two_ne_zero]
    rfl
  have hder : ∀ r, r ≠ S.μ → HasDerivAt (fun v => S.μ + Φ (v - S.μ))
      (deriv S.ℓ r / deriv S.g (r - (S.μ + Φ (r - S.μ)))) r := fun r hr => by
    rw [hval]
    exact Rev.hasDerivAt_translate (hΦd (r - S.μ) (sub_ne_zero.2 hr)).1
  have hpos : ∀ r, r ≠ S.μ → 0 < deriv S.ℓ r / deriv S.g (r - (S.μ + Φ (r - S.μ))) :=
    fun r hr => by rw [hval]; exact (hΦd (r - S.μ) (sub_ne_zero.2 hr)).2
  have hs : Function.Surjective fun v => S.μ + Φ (v - S.μ) := fun y => by
    obtain ⟨x, hx⟩ := hΦs (y - S.μ)
    exact ⟨x + S.μ, by simp [hx]⟩
  exact (Rev.exists_revealing_surjective S hc hder hpos hs).2

/-- **Proposition A4 (pooling).** If `κ > κck`, every equilibrium satisfying `D1^∞` is fully
pooling. -/
theorem propA4_pooling (κ : ℝ) (hκ : κck < κ) (S : Setting) (hg : S.g = fun z => z ^ 2)
    (hℓ : S.ℓ = fun b => κ * (b - S.μ) ^ 2) :
    ∀ (a : ℝ → ℝ) (φ : ℝ → Measure EReal), S.IsCPBE a φ → S.D1Inf a φ → ∃ c : ℝ, ∀ v, a v = c := by
  intro a φ h hD
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  have hfm : StrictMono (fun v : ℝ => v - S.μ) := fun x y hxy => by simp only; linarith
  have hf1 : ContDiff ℝ 1 (fun v : ℝ => v - S.μ) := by fun_prop
  have hfc : (fun v : ℝ => v - S.μ) S.μ = 0 := sub_self _
  have hfd : ∀ v, deriv (fun v : ℝ => v - S.μ) v = 1 := fun v => by
    rw [((hasDerivAt_id' v).sub_const S.μ).deriv]
  have hinf : ∀ P : ℝ → Prop, ∃ m : ℝ, κck < κ * m ∧ ∀ v, P v → m ≤ deriv (fun v : ℝ => v - S.μ) v :=
    fun P => ⟨1, by rw [mul_one]; exact hκ, fun v _ => (hfd v).ge⟩
  have hval : ∀ v, κ * (v - S.μ) / (v - a v) = deriv S.ℓ v / deriv S.g (v - a v) := by
    intro v
    rw [hℓ, hg, Rev.deriv_quad, Rev.deriv_sq_fun, mul_assoc, mul_div_mul_left _ _ two_ne_zero]
  apply Rev.const_of_noTails S h hD
  · rintro d hd ⟨hc, hC1, hlt, hder⟩
    apply CC.ODE.lemmaA3_iv κ hκ0 _ hfm hf1 hfc d hd.le (hinf _) a
    refine ⟨⟨hc, hC1, fun v hv => hlt v hv.le, fun v hv => ?_⟩, (hlt d le_rfl).le⟩
    have e : (fun x => κ * (fun v : ℝ => v - S.μ) (S.μ + x)) (v - S.μ) / id (v - a v) =
        deriv S.ℓ v / deriv S.g (v - a v) := by
      rw [← hval v]; simp only [id]; ring_nf
    rw [e]; exact hder v hv.le
  · rintro d hd ⟨hc, hC1, hlt, hder⟩
    apply CC.ODE.corollaryA1_iv κ hκ0 _ hfm hf1 hfc d hd.le (hinf _) a
    refine ⟨⟨hc, hC1, fun v hv => hlt v hv.le, fun v hv => ?_⟩, (hlt d le_rfl).le⟩
    have e : (fun x => -κ * (fun v : ℝ => v - S.μ) (S.μ - x)) (S.μ - v) / id (a v - v) =
        deriv S.ℓ v / deriv S.g (v - a v) := by
      rw [← hval v]; simp only [id]
      rw [show a v - v = -(v - a v) by ring, div_neg, ← neg_div]
      congr 1; ring
    rw [e]; exact hder v hv.le

/-- **Remark A1.** In the common-knowledge benchmark (`μ = 0` known, any type distribution with an
everywhere-positive continuous density), when `κ > κck`, every equilibrium satisfying `D1^∞` is
fully pooling. -/
theorem remarkA1 (κ : ℝ) (hκ : κck < κ) (S : Setting) (hg : S.g = fun z => z ^ 2)
    (hμ : S.μ = 0) (hℓ : S.ℓ = fun b => κ * b ^ 2) :
    ∀ (a : ℝ → ℝ) (φ : ℝ → Measure EReal), S.IsCPBE a φ → S.D1Inf a φ → ∃ c : ℝ, ∀ v, a v = c := by
  refine propA4_pooling κ hκ S hg ?_
  rw [hℓ, hμ]
  funext b
  rw [sub_zero]

end CC.General
