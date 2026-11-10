import ConformityConcerns.General.CP.Survivor

/-!
# No nondegenerate pool lies (weakly) below the norm

If the pooling set `T(c)` is nondegenerate and bounded above by `μ`, let `hb = sup T(c)`.
Then `ℓ(hb)` is strictly below the pool's conformity loss, the right limit `ĉ` of `a` at `hb`
exceeds `c`, and type `hb` profits from an off-path action `x ∈ (c, ĉ)` close to `c`, after which
`D1^∞` forces the belief `δ_hb`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- For `c < d` and any `y`, some point of `(c, d)` differs from `y`. -/
lemma exists_mem_Ioo_ne {c d : ℝ} (hcd : c < d) (y : ℝ) : ∃ x, c < x ∧ x < d ∧ x ≠ y := by
  by_cases hy : y = (c + d) / 2
  · exact ⟨(3 * c + d) / 4, by linarith, by linarith, by rw [hy]; intro h; linarith⟩
  · exact ⟨(c + d) / 2, by linarith, by linarith, fun h => hy h.symm⟩

namespace Setting.IsCPBE

variable {S : Setting} {a : ℝ → ℝ} {φ : ℝ → Measure EReal} (h : S.IsCPBE a φ)
  (hD : S.D1Inf a φ)
include h hD

/-- No nondegenerate pool is bounded above by the norm `μ`. -/
lemma no_pool_below {v : ℝ} (hT : (a ⁻¹' {a v}).Nontrivial)
    (hbdd : ∀ w, a w = a v → w ≤ S.μ) : False := by
  set c := a v with hc
  set T := a ⁻¹' {c} with hTdef
  set K := (S.confLoss φ c).toReal with hK
  have hmem : ∀ w, w ∈ T ↔ a w = c := fun w => Iff.rfl
  have hTne : T.Nonempty := ⟨v, rfl⟩
  have hTbdd : BddAbove T := ⟨S.μ, fun w hw => hbdd w hw⟩
  set hb := sSup T with hhb
  have hle : ∀ w, a w = c → w ≤ hb := fun w hw => le_csSup hTbdd hw
  have hbμ : hb ≤ S.μ := csSup_le hTne fun w hw => hbdd w hw
  have hlt_of : ∀ w, w < hb → a w ≤ c := by
    intro w hw
    obtain ⟨w', hw', hww'⟩ := exists_lt_of_lt_csSup hTne hw
    exact (hmem w').1 hw' ▸ h.monotone hww'.le
  have hgt_of : ∀ w, hb < w → c < a w := by
    intro w hw
    have h1 : c ≤ a w := h.monotone ((hle v rfl).trans hw.le)
    refine lt_of_le_of_ne h1 fun h2 => ?_
    have := hle w h2.symm
    linarith
  -- the pool's conformity loss exceeds `ℓ hb`
  have hpos := h.F_pos_of_nontrivial hT
  have hHP : S.ℓ hb < K := by
    apply h.ℓ_lt_confLoss hpos
    intro w hw hne
    exact S.hℓ.strictAntiOn (mem_Iic.2 ((hle w hw).trans hbμ)) (mem_Iic.2 hbμ)
      (lt_of_le_of_ne (hle w hw) hne)
  -- payoffs in the pool and at the endpoint
  have hUT : ∀ w, a w = c → S.U a φ w = -S.g (c - w) - K := by
    intro w hw; unfold Setting.U; rw [hw]; ring
  have hgc : Continuous S.g := S.hg.smooth.continuous
  have hUh : S.U a φ hb = -S.g (c - hb) - K := by
    have heq : EqOn (S.U a φ) (fun w => -S.g (c - w) - K) T := fun w hw => hUT w hw
    have hcont : Continuous (fun w => -S.g (c - w) - K) := by fun_prop
    exact heq.closure h.U_continuous hcont (csSup_mem_closure hTne hTbdd)
  have hU : ∀ w, -S.g (c - w) - K ≤ S.U a φ w := by
    intro w
    have := h.ic w v
    rw [hUT v rfl] at this
    linarith
  -- the right limit `ĉ` of `a` at `hb`
  set ĉ := sInf (a '' Ioi hb) with hĉdef
  have hbddb : BddBelow (a '' Ioi hb) := ⟨c, by rintro _ ⟨w, hw, rfl⟩; exact (hgt_of w hw).le⟩
  have hĉle : ∀ w, hb < w → ĉ ≤ a w := fun w hw => csInf_le hbddb ⟨w, hw, rfl⟩
  have hcĉ : c ≤ ĉ := le_csInf ⟨a (hb + 1), hb + 1, by simp, rfl⟩
    (by rintro _ ⟨w, hw, rfl⟩; exact (hgt_of w hw).le)
  have hlim : Tendsto a (𝓝[>] hb) (𝓝 ĉ) := h.monotone.tendsto_nhdsGT hb
  -- `ĉ > c`
  have hĉ : c < ĉ := by
    by_contra hcon
    have hĉc : ĉ = c := le_antisymm (not_lt.1 hcon) hcĉ
    have hah : a hb ≤ c := by
      rw [← hĉc]
      exact le_csInf ⟨a (hb + 1), hb + 1, by simp, rfl⟩
        (by rintro _ ⟨w, hw, rfl⟩; exact h.monotone (le_of_lt hw))
    set ε := (K - S.ℓ hb) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    obtain ⟨δ, hδ, hℓδ⟩ := Metric.continuousAt_iff.1 S.hℓ.continuous.continuousAt ε hε0
    set v₂ := hb + δ / 2 with hv₂def
    have hv₂ : c < a v₂ := hgt_of v₂ (by rw [hv₂def]; linarith)
    have hev1 : ∀ᶠ v' in 𝓝[>] hb, a v' < a v₂ := hlim.eventually_lt_const (hĉc ▸ hv₂)
    have hev2 : ∀ᶠ v' in 𝓝[>] hb, hb < v' := self_mem_nhdsWithin
    have hbound : ∀ᶠ v' in 𝓝[>] hb, K + S.g (c - hb) ≤ S.ℓ hb + ε + S.g (a v' - hb) := by
      filter_upwards [hev1, hev2] with v' h1 h2
      have hcv' := hgt_of v' h2
      have hC : (S.confLoss φ (a v')).toReal ≤ S.ℓ hb + ε := by
        apply h.confLoss_toReal_le
        intro w hw
        have hw1 : hb < w := by
          by_contra hw1
          rcases (not_lt.1 hw1).lt_or_eq with hw1 | hw1
          · have := hlt_of w hw1; linarith
          · rw [hw1] at hw; linarith
        have hw2 : w < v₂ := by
          by_contra hw2
          have := h.monotone (not_lt.1 hw2)
          linarith
        have := hℓδ (show dist w hb < δ by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.2]
      have hic := h.ic hb v'
      have hUv' : S.U a φ v' + S.g (a v' - v') = -(S.confLoss φ (a v')).toReal := by
        unfold Setting.U; ring
      rw [hUh] at hic
      linarith
    have hT2 : Tendsto (fun v' => S.ℓ hb + ε + S.g (a v' - hb)) (𝓝[>] hb)
        (𝓝 (S.ℓ hb + ε + S.g (c - hb))) := by
      apply tendsto_const_nhds.add
      rw [← hĉc]
      exact (hgc.tendsto _).comp (hlim.sub_const hb)
    have := ge_of_tendsto hT2 hbound
    linarith
  -- choose the off-path action `x`
  have hη : 0 < K - S.ℓ hb := by linarith
  have hgx : Continuous (fun x => S.g (x - hb)) := by fun_prop
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuousAt_iff.1 (hgx.continuousAt (x := c)) (K - S.ℓ hb) hη
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_mem_Ioo_ne (lt_min hĉ (by linarith : c < c + δ)) (a hb)
  have hxĉ : x < ĉ := lt_of_lt_of_le hx2 (min_le_left _ _)
  have hxδ : x < c + δ := lt_of_lt_of_le hx2 (min_le_right _ _)
  have hoff : x ∉ range a := by
    rintro ⟨w, hw⟩
    rcases lt_trichotomy w hb with hw' | hw' | hw'
    · have := hlt_of w hw'; linarith
    · subst hw'; exact hx3 hw.symm
    · have := hĉle w hw'; linarith
  have hright : ∀ r, hb < r → x < a r := fun r hr => lt_of_lt_of_le hxĉ (hĉle r hr)
  have hdev : S.g (x - hb) + S.ℓ hb < -S.U a φ hb := by
    have := hgδ (show dist x c < δ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    simp only [Real.dist_eq, abs_lt] at this
    rw [hUh]
    linarith [this.2]
  exact h.d1_contra_up hD hx1 hoff hU hUh hright hdev

end Setting.IsCPBE

end CC.General
