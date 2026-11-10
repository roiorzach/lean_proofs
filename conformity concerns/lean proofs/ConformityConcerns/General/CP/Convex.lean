import ConformityConcerns.General.Defs
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Elementary facts about the losses `g` and `ℓ`

Strict convexity inequalities (increasing differences), monotonicity on half-lines around the
minimiser, coercivity of `g`, and the derivative facts `g' 0 = 0`, `g'` odd and strictly
increasing, `ℓ' μ = 0`, `ℓ' v ≠ 0` for `v ≠ μ`.
-/

namespace CC.General

open Set Filter Topology

section StrictConvex

variable {f : ℝ → ℝ}

/-- Core strict convexity inequality: if `x < u < y` and `u + w = x + y`, then
`f u + f w < f x + f y`. -/
lemma sc_sum_lt (hf : StrictConvexOn ℝ univ f) {x y u w : ℝ}
    (hxu : x < u) (huy : u < y) (hsum : u + w = x + y) : f u + f w < f x + f y := by
  have hxy : x < y := hxu.trans huy
  have hyx : 0 < y - x := by linarith
  set t := (y - u) / (y - x) with ht
  have htm : t * (y - x) = y - u := by rw [ht]; field_simp
  have ht0 : 0 < t := div_pos (by linarith) hyx
  have ht1 : 0 < 1 - t := by
    have : t < 1 := by rw [ht, div_lt_one hyx]; linarith
    linarith
  have hu : t • x + (1 - t) • y = u := by
    simp only [smul_eq_mul]; linear_combination (-1 : ℝ) * htm
  have hw : (1 - t) • x + t • y = w := by
    simp only [smul_eq_mul]; linear_combination htm - hsum
  have h1 := hf.2 (mem_univ x) (mem_univ y) hxy.ne ht0 ht1 (by ring)
  have h2 := hf.2 (mem_univ x) (mem_univ y) hxy.ne ht1 ht0 (by ring)
  rw [hu] at h1
  rw [hw] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- Strict increasing differences: for `p < q` and `z₁ < z₂`,
`f (q - z₂) + f (p - z₁) < f (q - z₁) + f (p - z₂)`. -/
lemma sc_incr_diff (hf : StrictConvexOn ℝ univ f) {p q z₁ z₂ : ℝ} (hpq : p < q)
    (hz : z₁ < z₂) : f (q - z₂) + f (p - z₁) < f (q - z₁) + f (p - z₂) := by
  have := sc_sum_lt hf (x := p - z₂) (y := q - z₁) (u := q - z₂) (w := p - z₁)
    (by linarith) (by linarith) (by ring)
  linarith

/-- A strictly convex function with a global minimum at `m` is strictly larger elsewhere. -/
lemma sc_min_lt (hf : StrictConvexOn ℝ univ f) {m : ℝ} (hm : ∀ b, f m ≤ f b) {b : ℝ}
    (hb : b ≠ m) : f m < f b := by
  have h := hf.2 (mem_univ b) (mem_univ m) hb (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have h2 := hm ((1 / 2 : ℝ) • b + (1 / 2 : ℝ) • m)
  simp only [smul_eq_mul] at h h2
  linarith

lemma sc_strictAntiOn (hf : StrictConvexOn ℝ univ f) {m : ℝ} (hm : ∀ b, f m ≤ f b) :
    StrictAntiOn f (Iic m) := by
  intro v hv w hw hvw
  simp only [mem_Iic] at hv hw
  rcases hw.lt_or_eq with hw | hw
  · have := sc_sum_lt hf (x := v) (y := m) (u := w) (w := v + m - w) hvw hw (by ring)
    have := hm (v + m - w)
    linarith
  · subst hw
    exact sc_min_lt hf hm hvw.ne

lemma sc_strictMonoOn (hf : StrictConvexOn ℝ univ f) {m : ℝ} (hm : ∀ b, f m ≤ f b) :
    StrictMonoOn f (Ici m) := by
  intro v hv w hw hvw
  simp only [mem_Ici] at hv hw
  rcases hv.lt_or_eq with hv | hv
  · have := sc_sum_lt hf (x := m) (y := w) (u := v) (w := m + w - v) hv hvw (by ring)
    have := hm (m + w - v)
    linarith
  · subst hv
    exact sc_min_lt hf hm hvw.ne'

lemma sc_deriv_strictMono (hf : StrictConvexOn ℝ univ f) (hd : Differentiable ℝ f) :
    StrictMono (deriv f) := by
  intro x y hxy
  exact hf.strictMonoOn_deriv (fun z _ => hd z) (mem_univ x) (mem_univ y) hxy

lemma sc_deriv_min (hm : ∀ b, f m ≤ f b) : deriv f m = 0 :=
  IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall hm)

lemma sc_deriv_ne_zero (hf : StrictConvexOn ℝ univ f) (hd : Differentiable ℝ f) {m : ℝ}
    (hm : ∀ b, f m ≤ f b) {b : ℝ} (hb : b ≠ m) : deriv f b ≠ 0 := by
  rw [← sc_deriv_min (m := m) hm]
  exact (sc_deriv_strictMono hf hd).injective.ne hb

end StrictConvex

namespace AdaptLoss

variable {g : ℝ → ℝ} (hg : AdaptLoss g)
include hg

lemma nonneg (z : ℝ) : 0 ≤ g z := by
  have h := hg.strictConvex.convexOn.2 (mem_univ z) (mem_univ (-z))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, hg.even] at h
  have h0 : (1 / 2 : ℝ) * z + 1 / 2 * -z = 0 := by ring
  rw [h0, hg.zero] at h
  linarith

lemma isMin (z : ℝ) : g 0 ≤ g z := by rw [hg.zero]; exact hg.nonneg z

lemma pos {z : ℝ} (hz : z ≠ 0) : 0 < g z := by
  have := sc_min_lt hg.strictConvex hg.isMin hz
  rwa [hg.zero] at this

lemma eq_abs (z : ℝ) : g z = g |z| := by
  rcases abs_choice z with h | h <;> rw [h]
  rw [hg.even]

lemma lt_of_abs_lt {s t : ℝ} (h : |s| < |t|) : g s < g t := by
  rw [hg.eq_abs s, hg.eq_abs t]
  exact sc_strictMonoOn hg.strictConvex hg.isMin (mem_Ici.2 (abs_nonneg s))
    (mem_Ici.2 (abs_nonneg t)) h

lemma le_of_abs_le {s t : ℝ} (h : |s| ≤ |t|) : g s ≤ g t := by
  rcases h.lt_or_eq with h | h
  · exact (hg.lt_of_abs_lt h).le
  · rw [hg.eq_abs s, hg.eq_abs t, h]

lemma eq_or_eq_neg {s t : ℝ} (h : g s = g t) : s = t ∨ s = -t := by
  have : |s| = |t| := by
    rcases lt_trichotomy |s| |t| with h' | h' | h'
    · exact absurd h (hg.lt_of_abs_lt h').ne
    · exact h'
    · exact absurd h (hg.lt_of_abs_lt h').ne'
  exact abs_eq_abs.1 this

/-- Coercivity: sublevel sets of `g` are bounded. -/
lemma abs_le_of_le (B : ℝ) : ∃ R : ℝ, ∀ z, g z ≤ B → |z| ≤ R := by
  have h1 : 0 < g 1 := hg.pos one_ne_zero
  refine ⟨max 1 (B / g 1), fun z hz => ?_⟩
  by_contra hcon
  replace hcon := not_le.1 hcon
  have hz1 : 1 < |z| := lt_of_le_of_lt (le_max_left _ _) hcon
  have hzB : B / g 1 < |z| := lt_of_le_of_lt (le_max_right _ _) hcon
  have hzpos : 0 < |z| := by linarith
  -- convexity: `g 1 ≤ |z|⁻¹ * g |z|`
  have hinv : |z|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz1.le
  have hc := hg.strictConvex.convexOn.2 (mem_univ |z|) (mem_univ (0 : ℝ))
    (le_of_lt (inv_pos.2 hzpos)) (sub_nonneg.2 hinv) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, hg.zero] at hc
  rw [inv_mul_cancel₀ hzpos.ne'] at hc
  have : |z| * g 1 ≤ g |z| := by
    calc |z| * g 1 ≤ |z| * (|z|⁻¹ * g |z|) := mul_le_mul_of_nonneg_left hc hzpos.le
      _ = g |z| := by field_simp
  rw [← hg.eq_abs z] at this
  have : B < |z| * g 1 := by rwa [div_lt_iff₀ h1] at hzB
  linarith

lemma differentiable : Differentiable ℝ g :=
  hg.smooth.differentiable (by norm_num)

lemma continuous_deriv : Continuous (deriv g) :=
  hg.smooth.continuous_deriv (by norm_num)

lemma hasStrictDerivAt (z : ℝ) : HasStrictDerivAt g (deriv g z) z :=
  hg.smooth.hasStrictDerivAt (by norm_num)

lemma hasDerivAt (z : ℝ) : HasDerivAt g (deriv g z) z :=
  (hg.differentiable z).hasDerivAt

lemma deriv_zero : deriv g 0 = 0 := sc_deriv_min hg.isMin

lemma deriv_strictMono : StrictMono (deriv g) :=
  sc_deriv_strictMono hg.strictConvex hg.differentiable

lemma deriv_ne_zero {z : ℝ} (hz : z ≠ 0) : deriv g z ≠ 0 :=
  sc_deriv_ne_zero hg.strictConvex hg.differentiable hg.isMin hz

lemma deriv_neg (z : ℝ) : deriv g (-z) = -deriv g z := by
  have h : (fun x => g (-x)) = g := funext hg.even
  have := deriv_comp_neg (f := g) (x := z)
  rw [h] at this
  rw [this, neg_neg]

lemma deriv_pos {z : ℝ} (hz : 0 < z) : 0 < deriv g z := by
  rw [← hg.deriv_zero]; exact hg.deriv_strictMono hz

lemma deriv_neg_of_neg {z : ℝ} (hz : z < 0) : deriv g z < 0 := by
  rw [← hg.deriv_zero]; exact hg.deriv_strictMono hz

end AdaptLoss

/-! ### The limit slope `L_g` -/

/-- `L_g = lim_{z → ∞} g'(z) ∈ (0, ∞]`. -/
noncomputable def Lg (g : ℝ → ℝ) : EReal := ⨆ z : ℝ, ((deriv g z : ℝ) : EReal)

namespace AdaptLoss

variable {g : ℝ → ℝ} (hg : AdaptLoss g)
include hg

lemma tendsto_Lg : Tendsto (fun z : ℝ => ((deriv g z : ℝ) : EReal)) atTop (𝓝 (Lg g)) :=
  tendsto_atTop_iSup fun _ _ hab => EReal.coe_le_coe_iff.2 (hg.deriv_strictMono.monotone hab)

lemma deriv_lt_Lg (z : ℝ) : ((deriv g z : ℝ) : EReal) < Lg g :=
  lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (hg.deriv_strictMono (lt_add_one z)))
    (le_iSup (fun z : ℝ => ((deriv g z : ℝ) : EReal)) (z + 1))

/-- `g(s + d) - g(s) = ∫₀^d g'(s + y) dy`. -/
lemma sub_eq_integral (s d : ℝ) : g (s + d) - g s = ∫ y in (0 : ℝ)..d, deriv g (s + y) := by
  rw [intervalIntegral.integral_comp_add_left (deriv g) s, add_zero,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hg.hasDerivAt z)
      (hg.continuous_deriv.intervalIntegrable _ _)]

/-- `d g'(s) ≤ ∫₀^d g'(s + y) dy ≤ d g'(s + d)`. -/
lemma mul_deriv_le_sub (s : ℝ) {d : ℝ} (hd : 0 < d) :
    d * deriv g s ≤ g (s + d) - g s ∧ g (s + d) - g s ≤ d * deriv g (s + d) := by
  have hc : Continuous fun y => deriv g (s + y) :=
    hg.continuous_deriv.comp (continuous_const.add continuous_id)
  have hI : IntervalIntegrable (fun y => deriv g (s + y)) MeasureTheory.volume 0 d :=
    hc.intervalIntegrable 0 d
  have hC : ∀ c : ℝ, IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume 0 d := fun c =>
    continuous_const.intervalIntegrable 0 d
  rw [sub_eq_integral hg]
  constructor
  · have := intervalIntegral.integral_mono_on hd.le (hC _) hI
      (fun y hy => hg.deriv_strictMono.monotone (by linarith [hy.1] : s ≤ s + y))
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hd.le hI (hC _)
      (fun y hy => hg.deriv_strictMono.monotone (by linarith [hy.2] : s + y ≤ s + d))
    simpa [mul_comm] using this

/-- `lim_{s → ∞} [g(s + d) - g(s)] = lim_{s → ∞} ∫₀^d g'(s + y) dy = d L_g`. -/
lemma tendsto_sub_Lg {d : ℝ} (hd : 0 < d) :
    Tendsto (fun s : ℝ => ((g (s + d) - g s : ℝ) : EReal)) atTop (𝓝 ((d : EReal) * Lg g)) := by
  have hL : Tendsto (fun z : ℝ => ((d : EReal) * ((deriv g z : ℝ) : EReal))) atTop
      (𝓝 ((d : EReal) * Lg g)) :=
    EReal.Tendsto.const_mul hg.tendsto_Lg (Or.inl (EReal.coe_ne_bot d))
      (Or.inl (EReal.coe_ne_top d))
  have hL2 := hL.comp (tendsto_atTop_add_const_right atTop d tendsto_id)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hL hL2 (fun s => ?_) (fun s => ?_)
  · simp only
    rw [← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.2 (hg.mul_deriv_le_sub s hd).1
  · simp only [Function.comp, id]
    rw [← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.2 (hg.mul_deriv_le_sub s hd).2

/-- `∫_{c-h}^{x-h} g' < d L_g`, as `g'` is strictly increasing and every point of the integral is
finite. -/
lemma sub_lt_mul_Lg (s : ℝ) {d : ℝ} (hd : 0 < d) :
    ((g (s + d) - g s : ℝ) : EReal) < (d : EReal) * Lg g := by
  have h1 := (hg.mul_deriv_le_sub s hd).2
  have h2 : d * deriv g (s + d) < d * deriv g (s + d + 1) :=
    mul_lt_mul_of_pos_left (hg.deriv_strictMono (lt_add_one _)) hd
  have h3 : ((deriv g (s + d + 1) : ℝ) : EReal) ≤ Lg g :=
    le_iSup (fun z : ℝ => ((deriv g z : ℝ) : EReal)) (s + d + 1)
  calc ((g (s + d) - g s : ℝ) : EReal) < ((d * deriv g (s + d + 1) : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.2 (lt_of_le_of_lt h1 h2)
    _ = (d : EReal) * ((deriv g (s + d + 1) : ℝ) : EReal) := EReal.coe_mul _ _
    _ ≤ (d : EReal) * Lg g := mul_le_mul_of_nonneg_left h3 (by exact_mod_cast hd.le)

/-- The left boundary in the proof of Proposition A3: `lim_{v → -∞} [g(x - v) - g(y₀ - v)] = d L_g`
exceeds `g(x - h) - g(y₀ - h)`, with `d = x - y₀ > 0`. -/
lemma exists_margin_atBot {x y₀ : ℝ} (hx : y₀ < x) (h : ℝ) :
    ∃ K, g (x - h) - g (y₀ - h) < K ∧ ∀ᶠ v in atBot, K ≤ g (x - v) - g (y₀ - v) := by
  have hd : 0 < x - y₀ := by linarith
  have hlt := hg.sub_lt_mul_Lg (y₀ - h) hd
  rw [show y₀ - h + (x - y₀) = x - h by ring] at hlt
  obtain ⟨K, hK1, hK2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hs : Tendsto (fun v : ℝ => y₀ - v) atBot atTop :=
    (tendsto_atTop_add_const_right atBot y₀ tendsto_neg_atBot_atTop).congr fun v => by ring
  refine ⟨K, EReal.coe_lt_coe_iff.1 hK1, ?_⟩
  filter_upwards [hs.eventually ((hg.tendsto_sub_Lg hd).eventually (lt_mem_nhds hK2))] with v hv
  rw [show y₀ - v + (x - y₀) = x - v by ring] at hv
  exact (EReal.coe_lt_coe_iff.1 hv).le

/-- The reflected version of `exists_margin_atBot`, with `x < y₀` and `v → +∞`. -/
lemma exists_margin_atTop {x y₀ : ℝ} (hx : x < y₀) (h : ℝ) :
    ∃ K, g (x - h) - g (y₀ - h) < K ∧ ∀ᶠ v in atTop, K ≤ g (x - v) - g (y₀ - v) := by
  obtain ⟨K, hK1, hK2⟩ := hg.exists_margin_atBot (x := -x) (y₀ := -y₀) (by linarith) (-h)
  have e : ∀ u w : ℝ, g (-u - -w) = g (u - w) := fun u w => by
    rw [show -u - -w = -(u - w) by ring, hg.even]
  rw [e, e] at hK1
  refine ⟨K, hK1, ?_⟩
  filter_upwards [tendsto_neg_atTop_atBot.eventually hK2] with v hv
  rwa [e, e] at hv

lemma Lg_pos : 0 < Lg g := by
  have := hg.deriv_lt_Lg 0
  rwa [hg.deriv_zero, EReal.coe_zero] at this

/-- In the fully pooling assessment, `I_x(v) → -d L_g - M_f < 0`, so the index is eventually
negative. -/
lemma eventually_neg_of_Lg {d M : ℝ} (hd : 0 < d) (hM : 0 ≤ M) :
    ∀ᶠ s in atTop, g s - g (s + d) - M < 0 := by
  have hpos : (0 : EReal) < (d : EReal) * Lg g :=
    EReal.mul_pos (by exact_mod_cast hd) hg.Lg_pos
  filter_upwards [(hg.tendsto_sub_Lg hd).eventually (lt_mem_nhds hpos)] with s hs
  have : 0 < g (s + d) - g s := by exact_mod_cast hs
  linarith

end AdaptLoss

namespace ConfLoss

variable {ℓ : ℝ → ℝ} {μ : ℝ} (hℓ : ConfLoss ℓ μ)
include hℓ

lemma nonneg (b : ℝ) : 0 ≤ ℓ b := by
  have := hℓ.isMin b; rw [hℓ.zero] at this; exact this

lemma continuous : Continuous ℓ := hℓ.smooth.continuous

lemma differentiable : Differentiable ℝ ℓ :=
  hℓ.smooth.differentiable (by norm_num)

lemma continuous_deriv : Continuous (deriv ℓ) :=
  hℓ.smooth.continuous_deriv (by norm_num)

lemma hasDerivAt (b : ℝ) : HasDerivAt ℓ (deriv ℓ b) b :=
  (hℓ.differentiable b).hasDerivAt

lemma strictAntiOn : StrictAntiOn ℓ (Iic μ) := sc_strictAntiOn hℓ.strictConvex hℓ.isMin

lemma strictMonoOn : StrictMonoOn ℓ (Ici μ) := sc_strictMonoOn hℓ.strictConvex hℓ.isMin

lemma deriv_ne_zero {b : ℝ} (hb : b ≠ μ) : deriv ℓ b ≠ 0 :=
  sc_deriv_ne_zero hℓ.strictConvex hℓ.differentiable hℓ.isMin hb

end ConfLoss

end CC.General
