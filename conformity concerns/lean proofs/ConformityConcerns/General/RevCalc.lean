import ConformityConcerns.General.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Calculus helpers for the revealing and pooling results of Section A4

Elementary facts used in the proofs of Propositions A4–A6 at a fixed history: increasing
differences for strictly convex functions, the signs of `g'` and `ℓ'`, monotonicity from the sign
of a derivative that may fail to exist at one point, and the gluing of two half-solutions.
-/

namespace CC.General.Rev

open Set Filter Topology

/-! ### Strict convexity -/

section StrictConvex

variable {f : ℝ → ℝ}

lemma sum_lt (hf : StrictConvexOn ℝ univ f) {x y u w : ℝ}
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
lemma incr_diff (hf : StrictConvexOn ℝ univ f) {p q z₁ z₂ : ℝ} (hpq : p < q)
    (hz : z₁ < z₂) : f (q - z₂) + f (p - z₁) < f (q - z₁) + f (p - z₂) := by
  have := sum_lt hf (x := p - z₂) (y := q - z₁) (u := q - z₂) (w := p - z₁)
    (by linarith) (by linarith) (by ring)
  linarith

lemma deriv_strictMono (hf : StrictConvexOn ℝ univ f) (hd : Differentiable ℝ f) :
    StrictMono (deriv f) := fun x y hxy =>
  hf.strictMonoOn_deriv (fun z _ => hd z) (mem_univ x) (mem_univ y) hxy

lemma deriv_min {m : ℝ} (hm : ∀ b, f m ≤ f b) : deriv f m = 0 :=
  IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall hm)

end StrictConvex

/-! ### The losses -/

section Losses

variable {g : ℝ → ℝ} (hg : AdaptLoss g)
include hg

lemma g_nonneg (z : ℝ) : 0 ≤ g z := by
  have h := hg.strictConvex.convexOn.2 (mem_univ z) (mem_univ (-z))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, hg.even] at h
  have h0 : (1 / 2 : ℝ) * z + 1 / 2 * -z = 0 := by ring
  rw [h0, hg.zero] at h
  linarith

lemma g_differentiable : Differentiable ℝ g := hg.smooth.differentiable (by norm_num)

lemma g_isMin (z : ℝ) : g 0 ≤ g z := by rw [hg.zero]; exact g_nonneg hg z

lemma g_deriv_zero : deriv g 0 = 0 := deriv_min (g_isMin hg)

lemma g_deriv_strictMono : StrictMono (deriv g) :=
  deriv_strictMono hg.strictConvex (g_differentiable hg)

lemma g_deriv_neg (z : ℝ) : deriv g (-z) = -deriv g z := by
  have h : (fun x => g (-x)) = g := funext hg.even
  have := deriv_comp_neg (f := g) (x := z)
  rw [h] at this
  rw [this, neg_neg]

lemma g_deriv_pos {z : ℝ} (hz : 0 < z) : 0 < deriv g z := by
  rw [← g_deriv_zero hg]; exact g_deriv_strictMono hg hz

lemma g_deriv_neg_of_neg {z : ℝ} (hz : z < 0) : deriv g z < 0 := by
  rw [← g_deriv_zero hg]; exact g_deriv_strictMono hg hz

lemma g_deriv_contDiff : ContDiff ℝ 1 (deriv g) := hg.smooth.deriv'

/-- `TailData` for `Ψ = f'`, `Γ = g'` (both adaptation-type losses). -/
lemma pos_of_deriv_pos {z : ℝ} (h : 0 < deriv g z) : 0 < z := by
  by_contra hz
  replace hz := not_lt.1 hz
  rcases hz.lt_or_eq with hz | hz
  · exact absurd h (not_lt.2 (g_deriv_neg_of_neg hg hz).le)
  · rw [hz, g_deriv_zero hg] at h; exact lt_irrefl _ h

lemma neg_of_deriv_neg {z : ℝ} (h : deriv g z < 0) : z < 0 := by
  by_contra hz
  replace hz := not_lt.1 hz
  rcases hz.lt_or_eq with hz | hz
  · exact absurd h (not_lt.2 (g_deriv_pos hg hz).le)
  · rw [← hz, g_deriv_zero hg] at h; exact lt_irrefl _ h

end Losses

section ConfLoss

variable {ℓ : ℝ → ℝ} {μ : ℝ} (hℓ : ConfLoss ℓ μ)
include hℓ

lemma ℓ_nonneg (b : ℝ) : 0 ≤ ℓ b := by
  have := hℓ.isMin b; rw [hℓ.zero] at this; exact this

lemma ℓ_differentiable : Differentiable ℝ ℓ := hℓ.smooth.differentiable (by norm_num)

lemma ℓ_deriv_pos {b : ℝ} (hb : μ < b) : 0 < deriv ℓ b := by
  rw [← deriv_min (f := ℓ) hℓ.isMin]
  exact deriv_strictMono hℓ.strictConvex (ℓ_differentiable hℓ) hb

lemma ℓ_deriv_neg {b : ℝ} (hb : b < μ) : deriv ℓ b < 0 := by
  rw [← deriv_min (f := ℓ) hℓ.isMin]
  exact deriv_strictMono hℓ.strictConvex (ℓ_differentiable hℓ) hb

end ConfLoss

/-! ### Monotonicity from the sign of the derivative, off one point -/

lemma le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hc : ContinuousOn f (Icc x y)) (hd : ∀ t ∈ Ioo x y, HasDerivAt f (f' t) t)
    (h0 : ∀ t ∈ Ioo x y, 0 ≤ f' t) : f x ≤ f y := by
  have hm : MonotoneOn f (Icc x y) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc x y) hc
      (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht ⊢
      exact (hd t ht).hasDerivWithinAt
    · rw [interior_Icc] at ht
      exact h0 t ht
  exact hm ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

lemma le_of_hasDerivAt_nonneg_off {f f' : ℝ → ℝ} {x y : ℝ} (p : ℝ) (hxy : x ≤ y)
    (hc : ContinuousOn f (Icc x y)) (hd : ∀ t ∈ Ioo x y, t ≠ p → HasDerivAt f (f' t) t)
    (h0 : ∀ t ∈ Ioo x y, t ≠ p → 0 ≤ f' t) : f x ≤ f y := by
  by_cases hp : p ∈ Ioo x y
  · have h1 : f x ≤ f p := le_of_hasDerivAt_nonneg hp.1.le
      (hc.mono (Icc_subset_Icc le_rfl hp.2.le))
      (fun t ht => hd t ⟨ht.1, ht.2.trans hp.2⟩ ht.2.ne)
      (fun t ht => h0 t ⟨ht.1, ht.2.trans hp.2⟩ ht.2.ne)
    have h2 : f p ≤ f y := le_of_hasDerivAt_nonneg hp.2.le
      (hc.mono (Icc_subset_Icc hp.1.le le_rfl))
      (fun t ht => hd t ⟨hp.1.trans ht.1, ht.2⟩ ht.1.ne')
      (fun t ht => h0 t ⟨hp.1.trans ht.1, ht.2⟩ ht.1.ne')
    exact h1.trans h2
  · exact le_of_hasDerivAt_nonneg hxy hc (fun t ht => hd t ht (fun h => hp (h ▸ ht)))
      (fun t ht => h0 t ht (fun h => hp (h ▸ ht)))

lemma lt_of_hasDerivAt_pos {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hc : ContinuousOn f (Icc x y)) (hd : ∀ t ∈ Ioo x y, HasDerivAt f (f' t) t)
    (h0 : ∀ t ∈ Ioo x y, 0 < f' t) : f x < f y := by
  have hm : StrictMonoOn f (Icc x y) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := f') (convex_Icc x y) hc
      (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht ⊢
      exact (hd t ht).hasDerivWithinAt
    · rw [interior_Icc] at ht
      exact h0 t ht
  exact hm ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy

lemma lt_of_hasDerivAt_pos_off {f f' : ℝ → ℝ} {x y : ℝ} (p : ℝ) (hxy : x < y)
    (hc : ContinuousOn f (Icc x y)) (hd : ∀ t ∈ Ioo x y, t ≠ p → HasDerivAt f (f' t) t)
    (h0 : ∀ t ∈ Ioo x y, t ≠ p → 0 < f' t) : f x < f y := by
  by_cases hp : p ∈ Ioo x y
  · have h1 : f x < f p := lt_of_hasDerivAt_pos hp.1
      (hc.mono (Icc_subset_Icc le_rfl hp.2.le))
      (fun t ht => hd t ⟨ht.1, ht.2.trans hp.2⟩ ht.2.ne)
      (fun t ht => h0 t ⟨ht.1, ht.2.trans hp.2⟩ ht.2.ne)
    have h2 : f p < f y := lt_of_hasDerivAt_pos hp.2
      (hc.mono (Icc_subset_Icc hp.1.le le_rfl))
      (fun t ht => hd t ⟨hp.1.trans ht.1, ht.2⟩ ht.1.ne')
      (fun t ht => h0 t ⟨hp.1.trans ht.1, ht.2⟩ ht.1.ne')
    exact h1.trans h2
  · exact lt_of_hasDerivAt_pos hxy hc (fun t ht => hd t ht (fun h => hp (h ▸ ht)))
      (fun t ht => h0 t ht (fun h => hp (h ▸ ht)))

lemma strictMono_of_hasDerivAt_pos_off {f f' : ℝ → ℝ} (p : ℝ) (hc : Continuous f)
    (hd : ∀ t, t ≠ p → HasDerivAt f (f' t) t) (h0 : ∀ t, t ≠ p → 0 < f' t) : StrictMono f :=
  fun _ _ hxy => lt_of_hasDerivAt_pos_off p hxy hc.continuousOn (fun t _ ht => hd t ht)
    (fun t _ ht => h0 t ht)

/-! ### Gluing two half-solutions at `c` -/

section Glue

variable (c : ℝ) (aR aL : ℝ → ℝ)

/-- The rule equal to `aR` on `[c, ∞)` and to `aL` on `(-∞, c)`. -/
noncomputable def glue : ℝ → ℝ := fun v => if c ≤ v then aR v else aL v

variable {c aR aL}

lemma glue_continuous (hR : ContinuousOn aR (Ici c)) (hL : ContinuousOn aL (Iic c))
    (hc : aR c = aL c) : Continuous (glue c aR aL) := by
  unfold glue
  refine continuous_if_le continuous_const continuous_id hR hL ?_
  intro x (hx : c = x)
  rw [← hx, hc]

lemma glue_of_le {v : ℝ} (hv : c ≤ v) : glue c aR aL v = aR v := by
  unfold glue; simp [hv]

lemma glue_of_lt {v : ℝ} (hv : v < c) : glue c aR aL v = aL v := by
  unfold glue; simp [not_le.2 hv]

lemma glue_eventuallyEq_R {v : ℝ} (hv : c < v) : glue c aR aL =ᶠ[𝓝 v] aR := by
  filter_upwards [Ioi_mem_nhds hv] with w hw
  exact glue_of_le (le_of_lt hw)

lemma glue_eventuallyEq_L {v : ℝ} (hv : v < c) : glue c aR aL =ᶠ[𝓝 v] aL := by
  filter_upwards [Iio_mem_nhds hv] with w hw
  exact glue_of_lt hw

end Glue

/-- Translating a shape: if `Φ` has derivative `Φ'` at `r - μ`, the rule `μ + Φ(· - μ)` has
derivative `Φ'` at `r`. -/
lemma hasDerivAt_translate {Φ : ℝ → ℝ} {μ r Φ' : ℝ} (h : HasDerivAt Φ Φ' (r - μ)) :
    HasDerivAt (fun v => μ + Φ (v - μ)) Φ' r :=
  (h.comp_sub_const r μ).const_add μ

/-! ### Quadratic losses -/

lemma deriv_sq_fun : ∀ z : ℝ, deriv (fun z : ℝ => z ^ 2) z = 2 * z := fun z => by
  have := (hasDerivAt_pow 2 z).deriv
  rw [this]; simp

lemma deriv_quad (κ μ : ℝ) : ∀ v : ℝ, deriv (fun b : ℝ => κ * (b - μ) ^ 2) v = 2 * κ * (v - μ) :=
  fun v => by
    have h0 := (hasDerivAt_id' v).sub_const μ
    have h1 : HasDerivAt (fun b : ℝ => κ * (b - μ) ^ 2) (κ * (1 * (v - μ) + (v - μ) * 1)) v := by
      convert (h0.mul h0).const_mul κ using 1
      funext b; simp only [Pi.mul_apply]; ring
    rw [h1.deriv]; ring


end CC.General.Rev
