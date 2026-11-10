import ConformityConcerns.General.Defs
import ConformityConcerns.General.Revealing
import ConformityConcerns.General.Pooling
import ConformityConcerns.ODE.LeftTail

/-!
# Proposition A6 (Generalized Learning) — the fixed-history statements

`θ` is known; the adaptation loss `g` and the conformity loss `f` are `C²`, even, strictly
convex with `g 0 = f 0 = 0`; the conformity loss at history `h` is `ℓ(b) = f(b - μ(h))`. The
across-history (learning) parts are in `Learning/Assembly.lean`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Rev

/-- `Ψ = f'`, `Γ = g'` satisfy the standing hypotheses of Lemma A3. -/
lemma tailData_deriv {f g : ℝ → ℝ} (hf : AdaptLoss f) (hg : AdaptLoss g) :
    CC.ODE.TailData (deriv f) (deriv g) :=
  ⟨(g_deriv_strictMono hf).monotone.monotoneOn _, (g_deriv_strictMono hg).monotone.monotoneOn _,
    (g_deriv_contDiff hf).contDiffOn, (g_deriv_contDiff hg).contDiffOn,
    fun _ hx => g_deriv_pos hf hx, fun _ hx => g_deriv_pos hg hx⟩

end Rev

/-- **Proposition A6 (i), fixed history.** If `liminf_{x→∞} f'(x)/g'(x + C) > 1` for every `C`,
every equilibrium satisfying `D1^∞` is fully pooling. -/
theorem propA6_i_period (f : ℝ → ℝ) (hf : AdaptLoss f) (S : Setting)
    (hℓ : S.ℓ = fun b => f (b - S.μ))
    (hcond : ∀ C : ℝ, ∃ ε > 0, ∀ᶠ x in atTop, 1 + ε ≤ deriv f x / deriv S.g (x + C)) :
    ∀ (a : ℝ → ℝ) (φ : ℝ → Measure EReal), S.IsCPBE a φ → S.D1Inf a φ → ∃ c : ℝ, ∀ v, a v = c := by
  intro a φ h hD
  have hT := Rev.tailData_deriv hf S.hg
  have hℓ' : ∀ v, deriv S.ℓ v = deriv f (v - S.μ) := fun v => by
    rw [hℓ, deriv_comp_sub_const]
  apply Rev.const_of_noTails S h hD
  · rintro d hd ⟨hc, hC1, hlt, hder⟩
    refine CC.ODE.lemmaA3_i hT hcond d hd.le a ⟨hc, hC1, fun v hv => hlt v hv.le, fun v hv => ?_⟩
    rw [← hℓ']
    exact hder v hv.le
  · rintro d hd ⟨hc, hC1, hlt, hder⟩
    refine CC.ODE.corollaryA1_i hT hcond d hd.le a
      ⟨hc, hC1, fun v hv => hlt v hv.le, fun v hv => ?_⟩
    have e : deriv f (S.μ - v) / deriv S.g (a v - v) = deriv S.ℓ v / deriv S.g (v - a v) := by
      rw [hℓ', show S.μ - v = -(v - S.μ) by ring, show a v - v = -(v - a v) by ring,
        Rev.g_deriv_neg hf, Rev.g_deriv_neg S.hg, neg_div_neg_eq]
    rw [e]
    exact hder v hv.le

/-- **Proposition A6 (ii), fixed history.** If `f'(x) ≤ (1-β) g'(βx)` for all `x > 0` and some
`β ∈ (0,1)`, there is an equilibrium satisfying `D1^∞` that is fully revealing; it has the form
`a(v) = μ(h) + Φ(v - μ(h))` for one strictly increasing `Φ` that works at every history. -/
theorem propA6_ii_period (g f : ℝ → ℝ) (hg : AdaptLoss g) (hf : AdaptLoss f) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hcond : ∀ x, 0 < x → deriv f x ≤ (1 - β) * deriv g (β * x)) :
    ∃ Φ : ℝ → ℝ, StrictMono Φ ∧ Continuous Φ ∧ Φ 0 = 0 ∧
      ∀ S : Setting, S.g = g → S.ℓ = (fun b => f (b - S.μ)) →
        ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
          S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ := by
  have hT := Rev.tailData_deriv hf hg
  obtain ⟨aR, ⟨hRc, -, hRlt, hRd⟩, hR0, -⟩ := CC.ODE.lemmaA3_ii (c := 0) hT β hβ0 hβ1 hcond
  obtain ⟨aL, ⟨hLc, -, hLgt, hLd⟩, hL0, -⟩ := CC.ODE.corollaryA1_ii (c := 0) hT β hβ0 hβ1 hcond
  set Φ := Rev.glue 0 aR aL with hΦ
  have hΦc : Continuous Φ := Rev.glue_continuous hRc hLc (by rw [hR0, hL0])
  have hΦ0 : Φ 0 = 0 := by rw [hΦ, Rev.glue_of_le le_rfl, hR0]
  have hΦd : ∀ x, x ≠ 0 → HasDerivAt Φ (deriv f x / deriv g (x - Φ x)) x ∧
      0 < deriv f x / deriv g (x - Φ x) := by
    intro x hx
    rcases hx.lt_or_gt with hx | hx
    · have hd := (hLd x hx).congr_of_eventuallyEq (Rev.glue_eventuallyEq_L (aR := aR) hx)
      have hΦx : Φ x = aL x := Rev.glue_of_lt hx
      have e : deriv f (0 - x) / deriv g (aL x - x) = deriv f x / deriv g (x - Φ x) := by
        rw [hΦx, zero_sub, show aL x - x = -(x - aL x) by ring, Rev.g_deriv_neg hf,
          Rev.g_deriv_neg hg, neg_div_neg_eq]
      rw [← e]
      refine ⟨hd, ?_⟩
      rw [e, hΦx]
      exact div_pos_of_neg_of_neg (Rev.g_deriv_neg_of_neg hf hx)
        (Rev.g_deriv_neg_of_neg hg (by linarith [hLgt x hx]))
    · have hd := (hRd x hx).congr_of_eventuallyEq (Rev.glue_eventuallyEq_R (aL := aL) hx)
      have hΦx : Φ x = aR x := Rev.glue_of_le hx.le
      have e : deriv f (x - 0) / deriv g (x - aR x) = deriv f x / deriv g (x - Φ x) := by
        rw [hΦx, sub_zero]
      rw [← e]
      refine ⟨hd, ?_⟩
      rw [e, hΦx]
      exact div_pos (Rev.g_deriv_pos hf hx) (Rev.g_deriv_pos hg (by linarith [hRlt x hx]))
  refine ⟨Φ, Rev.strictMono_of_hasDerivAt_pos_off 0 hΦc (fun x hx => (hΦd x hx).1)
    (fun x hx => (hΦd x hx).2), hΦc, hΦ0, fun S hgS hℓ => ?_⟩
  have hc : Continuous (fun v => S.μ + Φ (v - S.μ)) :=
    continuous_const.add (hΦc.comp (continuous_id.sub continuous_const))
  have hval : ∀ r, deriv S.ℓ r / deriv S.g (r - (S.μ + Φ (r - S.μ))) =
      deriv f (r - S.μ) / deriv g (r - S.μ - Φ (r - S.μ)) := by
    intro r
    rw [hℓ, hgS, deriv_comp_sub_const, show r - (S.μ + Φ (r - S.μ)) = r - S.μ - Φ (r - S.μ) by ring]
  have hder : ∀ r, r ≠ S.μ → HasDerivAt (fun v => S.μ + Φ (v - S.μ))
      (deriv S.ℓ r / deriv S.g (r - (S.μ + Φ (r - S.μ)))) r := by
    intro r hr
    rw [hval]
    exact Rev.hasDerivAt_translate (hΦd (r - S.μ) (sub_ne_zero.2 hr)).1
  have hpos : ∀ r, r ≠ S.μ → 0 < deriv S.ℓ r / deriv S.g (r - (S.μ + Φ (r - S.μ))) :=
    fun r hr => by rw [hval]; exact (hΦd (r - S.μ) (sub_ne_zero.2 hr)).2
  exact (Rev.exists_revealing S hc hder hpos).2

end CC.General
