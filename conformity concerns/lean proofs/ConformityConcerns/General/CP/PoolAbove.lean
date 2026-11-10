import ConformityConcerns.General.CP.PoolBelow

/-!
# No nondegenerate pool lies (weakly) above the norm

The reflection of `no_pool_below`: with `hb = inf T(c) ≥ μ`, the left limit `ĉ` of `a` at `hb`
is below `c`, and type `hb` profits from an off-path action `x ∈ (ĉ, c)` close to `c`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Setting.IsCPBE

variable {S : Setting} {a : ℝ → ℝ} {φ : ℝ → Measure EReal} (h : S.IsCPBE a φ)
  (hD : S.D1Inf a φ)
include h hD

/-- No nondegenerate pool is bounded below by the norm `μ`. -/
lemma no_pool_above {v : ℝ} (hT : (a ⁻¹' {a v}).Nontrivial)
    (hbdd : ∀ w, a w = a v → S.μ ≤ w) : False := by
  set c := a v with hc
  set T := a ⁻¹' {c} with hTdef
  set K := (S.confLoss φ c).toReal with hK
  have hmem : ∀ w, w ∈ T ↔ a w = c := fun w => Iff.rfl
  have hTne : T.Nonempty := ⟨v, rfl⟩
  have hTbdd : BddBelow T := ⟨S.μ, fun w hw => hbdd w hw⟩
  set hb := sInf T with hhb
  have hle : ∀ w, a w = c → hb ≤ w := fun w hw => csInf_le hTbdd hw
  have hbμ : S.μ ≤ hb := le_csInf hTne fun w hw => hbdd w hw
  have hgt_of : ∀ w, hb < w → c ≤ a w := by
    intro w hw
    obtain ⟨w', hw', hww'⟩ := exists_lt_of_csInf_lt hTne hw
    exact (hmem w').1 hw' ▸ h.monotone hww'.le
  have hlt_of : ∀ w, w < hb → a w < c := by
    intro w hw
    have h1 : a w ≤ c := h.monotone (hw.le.trans (hle v rfl))
    refine lt_of_le_of_ne h1 fun h2 => ?_
    have := hle w h2
    linarith
  -- the pool's conformity loss exceeds `ℓ hb`
  have hpos := h.F_pos_of_nontrivial hT
  have hHP : S.ℓ hb < K := by
    apply h.ℓ_lt_confLoss hpos
    intro w hw hne
    exact S.hℓ.strictMonoOn (mem_Ici.2 hbμ) (mem_Ici.2 (hbμ.trans (hle w hw)))
      (lt_of_le_of_ne (hle w hw) (Ne.symm hne))
  -- payoffs in the pool and at the endpoint
  have hUT : ∀ w, a w = c → S.U a φ w = -S.g (c - w) - K := by
    intro w hw; unfold Setting.U; rw [hw]; ring
  have hgc : Continuous S.g := S.hg.smooth.continuous
  have hUh : S.U a φ hb = -S.g (c - hb) - K := by
    have heq : EqOn (S.U a φ) (fun w => -S.g (c - w) - K) T := fun w hw => hUT w hw
    have hcont : Continuous (fun w => -S.g (c - w) - K) := by fun_prop
    exact heq.closure h.U_continuous hcont (csInf_mem_closure hTne hTbdd)
  have hU : ∀ w, -S.g (c - w) - K ≤ S.U a φ w := by
    intro w
    have := h.ic w v
    rw [hUT v rfl] at this
    linarith
  -- the left limit `ĉ` of `a` at `hb`
  set ĉ := sSup (a '' Iio hb) with hĉdef
  have hbdda : BddAbove (a '' Iio hb) := ⟨c, by rintro _ ⟨w, hw, rfl⟩; exact (hlt_of w hw).le⟩
  have hleĉ : ∀ w, w < hb → a w ≤ ĉ := fun w hw => le_csSup hbdda ⟨w, hw, rfl⟩
  have hĉc' : ĉ ≤ c := csSup_le ⟨a (hb - 1), hb - 1, by simp, rfl⟩
    (by rintro _ ⟨w, hw, rfl⟩; exact (hlt_of w hw).le)
  have hlim : Tendsto a (𝓝[<] hb) (𝓝 ĉ) := h.monotone.tendsto_nhdsLT hb
  -- `ĉ < c`
  have hĉ : ĉ < c := by
    by_contra hcon
    have hĉc : ĉ = c := le_antisymm hĉc' (not_lt.1 hcon)
    have hah : c ≤ a hb := by
      rw [← hĉc]
      exact csSup_le ⟨a (hb - 1), hb - 1, by simp, rfl⟩
        (by rintro _ ⟨w, hw, rfl⟩; exact h.monotone (le_of_lt hw))
    set ε := (K - S.ℓ hb) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    obtain ⟨δ, hδ, hℓδ⟩ := Metric.continuousAt_iff.1 S.hℓ.continuous.continuousAt ε hε0
    set v₂ := hb - δ / 2 with hv₂def
    have hv₂ : a v₂ < c := hlt_of v₂ (by rw [hv₂def]; linarith)
    have hev1 : ∀ᶠ v' in 𝓝[<] hb, a v₂ < a v' := hlim.eventually_const_lt (hĉc ▸ hv₂)
    have hev2 : ∀ᶠ v' in 𝓝[<] hb, v' < hb := self_mem_nhdsWithin
    have hbound : ∀ᶠ v' in 𝓝[<] hb, K + S.g (c - hb) ≤ S.ℓ hb + ε + S.g (a v' - hb) := by
      filter_upwards [hev1, hev2] with v' h1 h2
      have hcv' := hlt_of v' h2
      have hC : (S.confLoss φ (a v')).toReal ≤ S.ℓ hb + ε := by
        apply h.confLoss_toReal_le
        intro w hw
        have hw1 : w < hb := by
          by_contra hw1
          rcases (not_lt.1 hw1).lt_or_eq with hw1 | hw1
          · have := hgt_of w hw1; linarith
          · rw [← hw1] at hw; linarith
        have hw2 : v₂ < w := by
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
    have hT2 : Tendsto (fun v' => S.ℓ hb + ε + S.g (a v' - hb)) (𝓝[<] hb)
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
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_mem_Ioo_ne (max_lt hĉ (by linarith : c - δ < c)) (a hb)
  have hxĉ : ĉ < x := lt_of_le_of_lt (le_max_left _ _) hx1
  have hxδ : c - δ < x := lt_of_le_of_lt (le_max_right _ _) hx1
  have hoff : x ∉ range a := by
    rintro ⟨w, hw⟩
    rcases lt_trichotomy w hb with hw' | hw' | hw'
    · have := hleĉ w hw'; linarith
    · subst hw'; exact hx3 hw.symm
    · have := hgt_of w hw'; linarith
  have hleft : ∀ r, r < hb → a r < x := fun r hr => lt_of_le_of_lt (hleĉ r hr) hxĉ
  have hdev : S.g (x - hb) + S.ℓ hb < -S.U a φ hb := by
    have := hgδ (show dist x c < δ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    simp only [Real.dist_eq, abs_lt] at this
    rw [hUh]
    linarith [this.2]
  exact h.d1_contra_down hD hx2 hoff hU hUh hleft hdev

/-- Every nondegenerate pool contains the norm type `μ`. -/
lemma pool_contains_mu {v : ℝ} (hT : (a ⁻¹' {a v}).Nontrivial) : a S.μ = a v := by
  have h1 : ∃ w₁, a w₁ = a v ∧ w₁ ≤ S.μ := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    exact h.no_pool_above hD hT fun w hw => (hcon w hw).le
  have h2 : ∃ w₂, a w₂ = a v ∧ S.μ ≤ w₂ := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    exact h.no_pool_below hD hT fun w hw => (hcon w hw).le
  obtain ⟨w₁, hw₁, hw₁μ⟩ := h1
  obtain ⟨w₂, hw₂, hw₂μ⟩ := h2
  exact h.mem_of_between hw₁ hw₂ hw₁μ hw₂μ

end Setting.IsCPBE

end CC.General
