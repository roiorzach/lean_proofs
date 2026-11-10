import ConformityConcerns.General.CP.Index

/-!
# The unique `D1^∞` survivor and the profitable deviation

Bernheim's two incentive comparisons: if type `hb` is indifferent between its equilibrium
action and imitating an on-path action `y₀`, and every type on the far side of `hb` chooses an
action beyond the off-path action `x`, then `S^∞(x) ⊆ {hb}`. Under `D1^∞` the belief after `x`
is then `δ_hb`, which gives a profitable deviation whenever `g(x - hb) + ℓ(hb) < -U(hb)`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Setting.IsCPBE

variable {S : Setting} {a : ℝ → ℝ} {φ : ℝ → Measure EReal} (h : S.IsCPBE a φ)
include h

lemma indiff_continuous (x : ℝ) : Continuous (S.indiff a φ x) := by
  unfold Setting.indiff
  exact h.U_continuous.add (S.hg.smooth.continuous.comp (continuous_const.sub continuous_id))

/-- Types above `hb` all choose actions above `x`: the index is strictly increasing there. -/
lemma indiff_lt_right {x hb : ℝ} (hright : ∀ r, hb < r → x < a r) {r v : ℝ} (hr : hb < r)
    (hrv : r < v) : S.indiff a φ x r < S.indiff a φ x v := by
  unfold Setting.indiff
  have h1 := h.ic v r
  have h2 := sc_incr_diff S.hg.strictConvex (hright r hr) hrv
  linarith

/-- Types below `hb` all choose actions below `x`: the index is strictly decreasing there. -/
lemma indiff_lt_left {x hb : ℝ} (hleft : ∀ r, r < hb → a r < x) {r v : ℝ} (hr : r < hb)
    (hvr : v < r) : S.indiff a φ x r < S.indiff a φ x v := by
  unfold Setting.indiff
  have h1 := h.ic v r
  have h2 := sc_incr_diff S.hg.strictConvex (hleft r hr) hvr
  linarith

/-- Upward deviation: `S^∞(x) ⊆ {hb}`. -/
lemma survivors_subset_up {x y₀ K hb : ℝ} (hx : y₀ < x)
    (hU : ∀ v, -S.g (y₀ - v) - K ≤ S.U a φ v)
    (hUh : S.U a φ hb = -S.g (y₀ - hb) - K)
    (hright : ∀ r, hb < r → x < a r)
    (hneg : S.indiff a φ x hb < 0) :
    S.survivors a φ x ⊆ {(hb : EReal)} := by
  set I := S.indiff a φ x with hI
  have hIv : ∀ v, I v = S.U a φ v + S.g (x - v) := fun v => rfl
  -- left of `hb`: imitation of `y₀`
  have hleftlt : ∀ v, v < hb → I hb + (S.g (x - v) - S.g (y₀ - v) - (S.g (x - hb) - S.g (y₀ - hb)))
      ≤ I v := by
    intro v _
    rw [hIv, hIv, hUh]
    have := hU v
    linarith
  have hD : ∀ v w, v < w → S.g (x - w) - S.g (y₀ - w) < S.g (x - v) - S.g (y₀ - v) := by
    intro v w hvw
    have := sc_incr_diff S.hg.strictConvex hx hvw
    linarith
  -- right of `hb`
  have hcont := h.indiff_continuous x
  have hle : ∀ r, hb < r → I hb ≤ I r := by
    intro r hr
    have hT : Tendsto I (𝓝[>] hb) (𝓝 (I hb)) := (hcont.tendsto hb).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hT
    filter_upwards [Ioo_mem_nhdsGT hr] with r' hr'
    exact (h.indiff_lt_right hright hr'.1 hr'.2).le
  have hgt : ∀ v, hb < v → I hb < I v := by
    intro v hv
    have hm : hb < (hb + v) / 2 := by linarith
    exact lt_of_le_of_lt (hle _ hm) (h.indiff_lt_right hright hm (by linarith))
  apply survivors_subset_singleton hneg
  · intro v hv
    rcases hv.lt_or_gt with hv | hv
    · have := hleftlt v hv
      have := hD v hb hv
      linarith
    · exact hgt v hv
  · refine ⟨I (hb + 1), hgt _ (by linarith), ?_⟩
    filter_upwards [eventually_gt_atTop (hb + 1)] with v hv
    exact (h.indiff_lt_right hright (by linarith) hv).le
  · -- the left boundary: `lim_{v → -∞} [g(x - v) - g(y₀ - v)] = d L_g > g(x - hb) - g(y₀ - hb)`
    obtain ⟨K, hK1, hK2⟩ := S.hg.exists_margin_atBot hx hb
    refine ⟨I hb + (K - (S.g (x - hb) - S.g (y₀ - hb))), by linarith, ?_⟩
    filter_upwards [hK2, eventually_lt_atBot hb] with v hv hvb
    have := hleftlt v hvb
    linarith

/-- Downward deviation: `S^∞(x) ⊆ {hb}`. -/
lemma survivors_subset_down {x y₀ K hb : ℝ} (hx : x < y₀)
    (hU : ∀ v, -S.g (y₀ - v) - K ≤ S.U a φ v)
    (hUh : S.U a φ hb = -S.g (y₀ - hb) - K)
    (hleft : ∀ r, r < hb → a r < x)
    (hneg : S.indiff a φ x hb < 0) :
    S.survivors a φ x ⊆ {(hb : EReal)} := by
  set I := S.indiff a φ x with hI
  have hIv : ∀ v, I v = S.U a φ v + S.g (x - v) := fun v => rfl
  have hrightlt : ∀ v, I hb + (S.g (x - v) - S.g (y₀ - v) - (S.g (x - hb) - S.g (y₀ - hb)))
      ≤ I v := by
    intro v
    rw [hIv, hIv, hUh]
    have := hU v
    linarith
  have hD : ∀ v w, v < w → S.g (x - v) - S.g (y₀ - v) < S.g (x - w) - S.g (y₀ - w) := by
    intro v w hvw
    have := sc_incr_diff S.hg.strictConvex hx hvw
    linarith
  have hcont := h.indiff_continuous x
  have hle : ∀ r, r < hb → I hb ≤ I r := by
    intro r hr
    have hT : Tendsto I (𝓝[<] hb) (𝓝 (I hb)) := (hcont.tendsto hb).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hT
    filter_upwards [Ioo_mem_nhdsLT hr] with r' hr'
    exact (h.indiff_lt_left hleft hr'.2 hr'.1).le
  have hgt : ∀ v, v < hb → I hb < I v := by
    intro v hv
    have hm : (v + hb) / 2 < hb := by linarith
    exact lt_of_le_of_lt (hle _ hm) (h.indiff_lt_left hleft hm (by linarith))
  apply survivors_subset_singleton hneg
  · intro v hv
    rcases hv.lt_or_gt with hv | hv
    · exact hgt v hv
    · have := hrightlt v
      have := hD hb v hv
      linarith
  · -- the reflected boundary
    obtain ⟨K, hK1, hK2⟩ := S.hg.exists_margin_atTop hx hb
    refine ⟨I hb + (K - (S.g (x - hb) - S.g (y₀ - hb))), by linarith, ?_⟩
    filter_upwards [hK2] with v hv
    have := hrightlt v
    linarith
  · refine ⟨I (hb - 1), hgt _ (by linarith), ?_⟩
    filter_upwards [eventually_lt_atBot (hb - 1)] with v hv
    exact (h.indiff_lt_left hleft (by linarith) hv).le

variable (hD : S.D1Inf a φ)
include hD

/-- The `D1^∞` contradiction for an upward deviation. -/
lemma d1_contra_up {x y₀ K hb : ℝ} (hx : y₀ < x) (hoff : x ∉ range a)
    (hU : ∀ v, -S.g (y₀ - v) - K ≤ S.U a φ v)
    (hUh : S.U a φ hb = -S.g (y₀ - hb) - K)
    (hright : ∀ r, hb < r → x < a r)
    (hdev : S.g (x - hb) + S.ℓ hb < -S.U a φ hb) : False := by
  have hneg : S.indiff a φ x hb < 0 := by
    unfold Setting.indiff
    have := S.hℓ.nonneg hb
    linarith
  have hs := (hD x hoff).trans (h.survivors_subset_up hx hU hUh hright hneg)
  have hc := confLoss_of_support_subset (S := S) h.prob hs
  refine h.not_dev hb x (by rw [hc]; exact ENNReal.ofReal_ne_top) ?_
  rw [hc, ENNReal.toReal_ofReal (S.hℓ.nonneg hb)]
  exact hdev

/-- The `D1^∞` contradiction for a downward deviation. -/
lemma d1_contra_down {x y₀ K hb : ℝ} (hx : x < y₀) (hoff : x ∉ range a)
    (hU : ∀ v, -S.g (y₀ - v) - K ≤ S.U a φ v)
    (hUh : S.U a φ hb = -S.g (y₀ - hb) - K)
    (hleft : ∀ r, r < hb → a r < x)
    (hdev : S.g (x - hb) + S.ℓ hb < -S.U a φ hb) : False := by
  have hneg : S.indiff a φ x hb < 0 := by
    unfold Setting.indiff
    have := S.hℓ.nonneg hb
    linarith
  have hs := (hD x hoff).trans (h.survivors_subset_down hx hU hUh hleft hneg)
  have hc := confLoss_of_support_subset (S := S) h.prob hs
  refine h.not_dev hb x (by rw [hc]; exact ENNReal.ofReal_ne_top) ?_
  rw [hc, ENNReal.toReal_ofReal (S.hℓ.nonneg hb)]
  exact hdev

end Setting.IsCPBE

end CC.General
