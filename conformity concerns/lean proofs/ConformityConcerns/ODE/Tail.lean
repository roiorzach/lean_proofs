import ConformityConcerns.ODE.Defs
import ConformityConcerns.ODE.Existence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Lemma A3 (Tail Solutions of the Differential Equation)
-/

namespace CC.ODE

open Set Filter Topology

variable {Ψ Γ : ℝ → ℝ} {c : ℝ}

/-! ### Auxiliary calculus lemmas -/

lemma monotoneOn_Ici_of_hasDerivAt {f f' : ℝ → ℝ} {a : ℝ} (hc : ContinuousOn f (Ici a))
    (hd : ∀ x, a < x → HasDerivAt f (f' x) x) (h0 : ∀ x, a < x → 0 ≤ f' x) :
    MonotoneOn f (Ici a) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Ici a) hc (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ici] at hx ⊢
    exact (hd x hx).hasDerivWithinAt
  · rw [interior_Ici] at hx
    exact h0 x hx

lemma antitoneOn_Ici_of_hasDerivAt {f f' : ℝ → ℝ} {a : ℝ} (hc : ContinuousOn f (Ici a))
    (hd : ∀ x, a < x → HasDerivAt f (f' x) x) (h0 : ∀ x, a < x → f' x ≤ 0) :
    AntitoneOn f (Ici a) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Ici a) hc (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ici] at hx ⊢
    exact (hd x hx).hasDerivWithinAt
  · rw [interior_Ici] at hx
    exact h0 x hx

lemma continuousOn_Ici_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x, a < x → HasDerivAt f (f' x) x) : ContinuousOn f (Ici b) :=
  fun x hx => (hd x (lt_of_lt_of_le hab hx)).continuousAt.continuousWithinAt

lemma contDiffOn_one_of_hasDerivAt {f f' : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hd : ∀ x ∈ s, HasDerivAt f (f' x) x) (hc : ContinuousOn f' s) : ContDiffOn ℝ 1 f s := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hc.congr fun x hx => (hd x hx).deriv

/-- **Lemma A3 (i).** If `liminf_{x→∞} Ψ(x)/Γ(x+C) > 1` for every `C`, there is no right-tail
solution on `[d, ∞)` for any `d ≥ c`.  (`liminf > 1` is stated as: for some `ε > 0`, eventually
`Ψ(x)/Γ(x+C) ≥ 1 + ε`.) -/
theorem lemmaA3_i (h : TailData Ψ Γ)
    (hlim : ∀ C : ℝ, ∃ ε > 0, ∀ᶠ x in atTop, 1 + ε ≤ Ψ x / Γ (x + C)) :
    ∀ d, c ≤ d → ∀ a, ¬ IsRightTailSol Ψ Γ c d a := by
  rintro d hd a ⟨-, -, hlt, hder⟩
  have hwpos : ∀ v, d < v → 0 < v - a v := fun v hv => sub_pos.2 (hlt v hv)
  have hwder : ∀ v, d < v → HasDerivAt (fun v => v - a v) (1 - Ψ (v - c) / Γ (v - a v)) v :=
    fun v hv => (hasDerivAt_id' v).sub (hder v hv)
  have hrpos : ∀ v, d < v → 0 < Ψ (v - c) / Γ (v - a v) := fun v hv =>
    div_pos (h.Ψ_pos _ (by linarith)) (h.Γ_pos _ (hwpos v hv))
  -- Step 1: `w(v) - v` is nonincreasing on `[d+1, ∞)`, where `w(v) = v - a(v)`.
  have hd1 : d < d + 1 := by linarith
  have hanti1 : AntitoneOn (fun v => (v - a v) - v) (Ici (d + 1)) :=
    antitoneOn_Ici_of_hasDerivAt
      (continuousOn_Ici_of_hasDerivAt hd1 fun v hv => (hwder v hv).sub (hasDerivAt_id' v))
      (fun v hv => (hwder v (by linarith)).sub (hasDerivAt_id' v))
      (fun v hv => by have := hrpos v (by linarith); linarith)
  have hupper : ∀ v, d + 1 ≤ v →
      v - a v ≤ (v - c) + (((d + 1) - a (d + 1)) - (d + 1) + c) := by
    intro v hv
    have := hanti1 (self_mem_Ici) (show v ∈ Ici (d + 1) from hv) hv
    simp only at this
    linarith
  obtain ⟨ε, hε, hev⟩ := hlim (((d + 1) - a (d + 1)) - (d + 1) + c)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  -- Step 2: eventually `w' ≤ -ε`.
  have hderneg : ∀ v, max (d + 1) (X + c) ≤ v → 1 - Ψ (v - c) / Γ (v - a v) + ε ≤ 0 := by
    intro v hv
    have hv1 := le_trans (le_max_left _ _) hv
    have hv2 := le_trans (le_max_right _ _) hv
    have hvd : d < v := by linarith
    have hX' := hX (v - c) (by linarith)
    have hup := hupper v hv1
    have hw := hwpos v hvd
    have hΓle := h.Γ_mono hw (lt_of_lt_of_le hw hup) hup
    have : Ψ (v - c) / Γ (v - c + (((d + 1) - a (d + 1)) - (d + 1) + c)) ≤
        Ψ (v - c) / Γ (v - a v) :=
      div_le_div_of_nonneg_left (h.Ψ_pos _ (by linarith)).le (h.Γ_pos _ hw) hΓle
    linarith
  set v1 := max (d + 1) (X + c) with hv1
  have hv1d : d < v1 := by linarith [le_max_left (d + 1) (X + c)]
  -- Step 3: `w(v) + ε v` is nonincreasing on `[v1, ∞)`, so `w` becomes negative.
  have hanti2 : AntitoneOn (fun v => (v - a v) + ε * v) (Ici v1) :=
    antitoneOn_Ici_of_hasDerivAt
      (continuousOn_Ici_of_hasDerivAt hv1d fun v hv =>
        (hwder v hv).add ((hasDerivAt_id' v).const_mul ε))
      (fun v hv => (hwder v (by linarith)).add ((hasDerivAt_id' v).const_mul ε))
      (fun v hv => by have := hderneg v hv.le; linarith)
  have hw1 := hwpos v1 hv1d
  have hq : 0 ≤ (v1 - a v1) / ε := div_nonneg hw1.le hε.le
  have hvv1 : v1 ≤ v1 + (v1 - a v1) / ε + 1 := by linarith
  have key := hanti2 (self_mem_Ici) hvv1 hvv1
  simp only at key
  have hεv : ε * (v1 + (v1 - a v1) / ε + 1) = ε * v1 + (v1 - a v1) + ε := by
    field_simp
  have := hwpos (v1 + (v1 - a v1) / ε + 1) (by linarith)
  linarith

/-- **Lemma A3 (ii).** If `Ψ(x) ≤ (1-β) Γ(βx)` for all `x > 0` and some `β ∈ (0,1)`, there is a
right-tail solution on `[c, ∞)` with `a(c) = c` and `a'(v) > 0` for every `v > c`. -/
theorem lemmaA3_ii (h : TailData Ψ Γ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) :
    ∃ a, IsRightTailSol Ψ Γ c c a ∧ a c = c ∧ ∀ v, c < v → 0 < deriv a v := by
  obtain ⟨w, hw0, hwc, hwpos, hwd, hgc⟩ := Gap.exists_solution h hβ0 hβ1 hΨ
  have hmaps : MapsTo (fun v : ℝ => v - c) (Ioi c) (Ioi 0) := fun v (hv : c < v) =>
    show 0 < v - c from sub_pos.2 hv
  have hda : ∀ v, c < v → HasDerivAt (fun v => v - w (v - c))
      (1 - (1 - Ψ (v - c) / Γ (w (v - c)))) v := fun v hv =>
    (hasDerivAt_id' v).sub ((hwd (v - c) (sub_pos.2 hv)).comp_sub_const v c)
  have hder : ∀ v, c < v → HasDerivAt (fun v => v - w (v - c))
      (Ψ (v - c) / Γ (v - (v - w (v - c)))) v := fun v hv => by
    have := hda v hv
    rw [sub_sub_cancel] at this
    rw [sub_sub_cancel]
    exact this
  refine ⟨fun v => v - w (v - c), ⟨?_, ?_, fun v hv => ?_, hder⟩, ?_, fun v hv => ?_⟩
  · exact continuousOn_id.sub (hwc.comp (continuousOn_id.sub continuousOn_const)
      fun v (hv : c ≤ v) => mem_Ici.2 (sub_nonneg.2 hv))
  · exact contDiffOn_one_of_hasDerivAt isOpen_Ioi hda
      (continuousOn_const.sub (hgc.comp (continuousOn_id.sub continuousOn_const) hmaps))
  · have := hwpos (v - c) (sub_pos.2 hv)
    linarith
  · simp [hw0]
  · rw [(hder v hv).deriv, sub_sub_cancel]
    exact div_pos (h.Ψ_pos _ (sub_pos.2 hv)) (h.Γ_pos _ (hwpos _ (sub_pos.2 hv)))

/-- **Lemma A3 (iii).** With `Γ(x) = x` and `Ψ(x) = κ f(c + x)` (`κ > 0`, `f` strictly increasing
and `C¹`, `f c = 0`), there is a right-tail solution on `[c, ∞)` with `a(c) = c` whenever
`κ · sup_{v ≥ c} f'(v) ≤ κck`. -/
theorem lemmaA3_iii (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℝ) (hf : StrictMono f) (hf1 : ContDiff ℝ 1 f)
    (hfc : f c = 0) (hsup : ∀ v, c ≤ v → κ * deriv f v ≤ κck) :
    ∃ a, IsRightTailSol (fun x => κ * f (c + x)) id c c a ∧ a c = c := by
  have hdiff : Differentiable ℝ f := hf1.differentiable one_ne_zero
  have hT : TailData (fun x => κ * f (c + x)) id := by
    refine ⟨fun x _ y _ hxy => mul_le_mul_of_nonneg_left (hf.monotone (by linarith)) hκ.le,
      monotoneOn_id, ?_, contDiffOn_id, fun x hx => ?_, fun x hx => hx⟩
    · exact (contDiff_const.mul (hf1.comp (contDiff_const.add contDiff_id))).contDiffOn
    · have : f c < f (c + x) := hf (by linarith)
      rw [hfc] at this
      exact mul_pos hκ this
  have hderle : ∀ y ∈ interior (Ici c), deriv f y ≤ 1 / (4 * κ) := by
    intro y hy
    rw [interior_Ici] at hy
    have := hsup y (le_of_lt hy)
    rw [κck_eq] at this
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hΨ : ∀ x, 0 < x → (fun x => κ * f (c + x)) x ≤ (1 - 1 / 2) * id (1 / 2 * x) := by
    intro x hx
    have h1 := (convex_Ici c).image_sub_le_mul_sub_of_deriv_le hdiff.continuous.continuousOn
      hdiff.differentiableOn hderle c self_mem_Ici (c + x) (show c ≤ c + x by linarith)
      (by linarith)
    rw [hfc, sub_zero, add_sub_cancel_left] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hκ.le
    have h3 : κ * (1 / (4 * κ) * x) = (1 - 1 / 2) * (1 / 2 * x) := by
      field_simp
      ring
    simp only [id]
    linarith
  obtain ⟨a, ha, hac, -⟩ := lemmaA3_ii (c := c) hT (1 / 2) (by norm_num) (by norm_num) hΨ
  exact ⟨a, ha, hac⟩

/-- **Lemma A3 (iv).** With `Γ(x) = x` and `Ψ(x) = κ f(c + x)`, for every `d ≥ c` there is no
right-tail solution on `[d, ∞)` with `a(d) ≤ d` whenever `κ · inf_{v ≥ d} f'(v) > κck`. -/
theorem lemmaA3_iv (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℝ) (hf : StrictMono f) (hf1 : ContDiff ℝ 1 f)
    (hfc : f c = 0) (d : ℝ) (hd : c ≤ d)
    (hinf : ∃ m : ℝ, κck < κ * m ∧ ∀ v, d ≤ v → m ≤ deriv f v) :
    ∀ a, ¬ (IsRightTailSol (fun x => κ * f (c + x)) id c d a ∧ a d ≤ d) := by
  rintro a ⟨⟨hcont, -, hlt, hder⟩, had⟩
  obtain ⟨m, hm, hmf⟩ := hinf
  rw [κck_eq] at hm
  have hκm : 0 < κ * m := by linarith
  have hm0 : 0 < m := pos_of_mul_pos_right hκm hκ.le
  have hdiff : Differentiable ℝ f := hf1.differentiable one_ne_zero
  -- `f(v) ≥ m (v - d)` for `v ≥ d`.
  have hfv : ∀ v, d ≤ v → m * (v - d) ≤ f v := by
    intro v hv
    have h1 := (convex_Ici d).mul_sub_le_image_sub_of_le_deriv hdiff.continuous.continuousOn
      hdiff.differentiableOn (C := m)
      (fun x hx => hmf x (by rw [interior_Ici] at hx; exact le_of_lt hx))
      d self_mem_Ici v hv hv
    have h2 : f c ≤ f d := hf.monotone hd
    rw [hfc] at h2
    linarith
  have hder' : ∀ v, d < v → HasDerivAt a (κ * f v / (v - a v)) v := by
    intro v hv
    have := hder v hv
    simp only [id, add_sub_cancel] at this
    exact this
  have hfpos : ∀ v, d < v → 0 < f v := fun v hv => by
    have h1 := hfv v hv.le
    have h2 : 0 < m * (v - d) := mul_pos hm0 (by linarith)
    linarith
  have hApos : ∀ v, d < v → 0 < κ * f v / (v - a v) := fun v hv =>
    div_pos (mul_pos hκ (hfpos v hv)) (sub_pos.2 (hlt v hv))
  have hmono : MonotoneOn a (Ici d) :=
    monotoneOn_Ici_of_hasDerivAt hcont hder' (fun v hv => (hApos v hv).le)
  -- Step A: `a` exceeds `d` somewhere. If `a` were bounded above by `d`, the slope would stay
  -- bounded below by a positive constant for large `v`, so `a` would diverge.
  have hslope : ∀ v, d + (d - a d) + 1 ≤ v → κ * m / 2 ≤ κ * f v / (v - a v) := by
    intro v hv
    have hvd : d < v := by linarith
    have hav : a d ≤ a v := hmono self_mem_Ici (show v ∈ Ici d from hvd.le) hvd.le
    have hgap : 0 < v - a v := sub_pos.2 (hlt v hvd)
    rw [le_div_iff₀ hgap]
    have h1 : v - a v ≤ 2 * (v - d) := by linarith
    have h2 : κ * (m * (v - d)) ≤ κ * f v := mul_le_mul_of_nonneg_left (hfv v hvd.le) hκ.le
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ κ * m / 2)
    linarith
  obtain ⟨v'', hv''d, hu''⟩ : ∃ v'', d < v'' ∧ d < a v'' := by
    by_contra hbdd
    push Not at hbdd
    have hv1d : d < d + (d - a d) + 1 := by linarith
    have hψ : MonotoneOn (fun v => a v - κ * m / 2 * v) (Ici (d + (d - a d) + 1)) :=
      monotoneOn_Ici_of_hasDerivAt
        (continuousOn_Ici_of_hasDerivAt hv1d fun v hv =>
          (hder' v hv).sub ((hasDerivAt_id' v).const_mul (κ * m / 2)))
        (fun v hv => (hder' v (by linarith)).sub ((hasDerivAt_id' v).const_mul (κ * m / 2)))
        (fun v hv => by have := hslope v hv.le; linarith)
    set v1 := d + (d - a d) + 1 with hv1
    set v2 := v1 + 2 * (d - a d + 1) / (κ * m) with hv2
    have hq : 0 ≤ 2 * (d - a d + 1) / (κ * m) := by
      apply div_nonneg _ hκm.le
      linarith
    have hv12 : v1 ≤ v2 := by linarith
    have h1 := hψ self_mem_Ici hv12 hv12
    simp only at h1
    have h2 : κ * m / 2 * (v2 - v1) = d - a d + 1 := by
      rw [hv2]
      field_simp
      ring
    have h3 : a d ≤ a v1 := hmono self_mem_Ici (show v1 ∈ Ici d from hv1d.le) hv1d.le
    have := hbdd v2 (by linarith)
    nlinarith
  -- Step B: for `v ≥ v''`, `a'(v) ≥ (κ m/κck) (a(v) - d)/(v - d)`, using `x(1 - x) ≤ κck`
  set p := κ * m / κck with hp
  have hp1 : 1 < p := by
    rw [hp, one_lt_div κck_pos]
    rw [κck_eq]
    linarith
  have hkey : ∀ v, v'' ≤ v → p * ((a v - d) / (v - d)) ≤ κ * f v / (v - a v) := by
    intro v hv
    have hvd : d < v := by linarith
    have hs : 0 < v - d := sub_pos.2 hvd
    have hw : 0 < v - a v := sub_pos.2 (hlt v hvd)
    have hx : (v - a v) * (a v - d) ≤ κck * (v - d) ^ 2 := by
      rw [κck_eq]
      nlinarith [sq_nonneg ((v - a v) - (a v - d))]
    have hκck := κck_pos
    have h1 : κ * (m * (v - d)) ≤ κ * f v := mul_le_mul_of_nonneg_left (hfv v hvd.le) hκ.le
    rw [le_div_iff₀ hw]
    calc p * ((a v - d) / (v - d)) * (v - a v)
        = κ * m * (v - d) * (((v - a v) * (a v - d)) / (κck * (v - d) ^ 2)) := by
          rw [hp]; field_simp
      _ ≤ κ * m * (v - d) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 hx) (by positivity)
      _ ≤ κ * f v := by linarith
  -- Step C: comparison with the solution `ā` of the associated equality
  have hrp : ∀ v, d < v → HasDerivAt (fun v => (v - d) ^ p) (1 * p * (v - d) ^ (p - 1)) v :=
    fun v hv => ((hasDerivAt_id' v).sub_const d).rpow_const (Or.inl (sub_pos.2 hv).ne')
  have hhd : ∀ v, d < v → HasDerivAt (fun v => (a v - d) / (v - d) ^ p)
      (((κ * f v / (v - a v)) * (v - d) ^ p - (a v - d) * (1 * p * (v - d) ^ (p - 1))) /
        ((v - d) ^ p) ^ 2) v := fun v hv =>
    ((hder' v hv).sub_const d).div (hrp v hv) (Real.rpow_pos_of_pos (sub_pos.2 hv) p).ne'
  have hh : MonotoneOn (fun v => (a v - d) / (v - d) ^ p) (Ici v'') := by
    refine monotoneOn_Ici_of_hasDerivAt (continuousOn_Ici_of_hasDerivAt hv''d hhd)
      (fun v hv => hhd v (by linarith)) (fun v hv => ?_)
    have hs : 0 < v - d := by linarith
    have hP := Real.rpow_pos_of_pos hs p
    apply div_nonneg _ (sq_nonneg _)
    rw [Real.rpow_sub_one hs.ne']
    have h1 := hkey v hv.le
    have e : (κ * f v / (v - a v)) * (v - d) ^ p - (a v - d) * (1 * p * ((v - d) ^ p / (v - d))) =
        (v - d) ^ p * (κ * f v / (v - a v) - p * ((a v - d) / (v - d))) := by
      field_simp
    rw [e]
    exact mul_nonneg hP.le (by linarith)
  have hcomp : ∀ v, v'' ≤ v →
      (a v'' - d) * ((v - d) / (v'' - d)) ^ p ≤ a v - d := by
    intro v hv
    have hs : 0 < v - d := by linarith
    have hs'' : 0 < v'' - d := by linarith
    have hP := Real.rpow_pos_of_pos hs p
    have hP'' := Real.rpow_pos_of_pos hs'' p
    have h1 := hh self_mem_Ici (show v ∈ Ici v'' from hv) hv
    simp only at h1
    rw [div_le_div_iff₀ hP'' hP] at h1
    rw [Real.div_rpow hs.le hs''.le, ← mul_div_assoc, div_le_iff₀ hP'']
    linarith
  -- Since `κ m/κck > 1` and `a(v'') > d`, `ā(v̄) > v̄` for some `v̄`, whence `a(v̄) > v̄`.
  have hs'' : 0 < v'' - d := by linarith
  have hu0 : 0 < a v'' - d := by linarith
  set q := (a v'' - d) / (v'' - d) with hq
  have hq0 : 0 < q := div_pos hu0 hs''
  obtain ⟨Y, hY1, hY2⟩ := ((tendsto_rpow_atTop (by linarith : 0 < p - 1)).eventually_gt_atTop
    (1 / q) |>.and (eventually_ge_atTop (1 : ℝ))).exists
  have hY0 : 0 < Y := by linarith
  set vb := d + Y * (v'' - d) with hvb
  have hvbv : v'' ≤ vb := by rw [hvb]; nlinarith
  have hratio : (vb - d) / (v'' - d) = Y := by rw [hvb]; field_simp; ring
  have h1 := hcomp vb hvbv
  rw [hratio] at h1
  have hYp : Y ^ p = Y ^ (p - 1) * Y := by rw [Real.rpow_sub_one hY0.ne']; field_simp
  have hqY : 1 < q * Y ^ (p - 1) := by
    have := mul_lt_mul_of_pos_left hY1 hq0
    rwa [mul_one_div_cancel hq0.ne'] at this
  have hU : a v'' - d = q * (v'' - d) := by rw [hq]; field_simp
  have h2 : (vb - d) < a vb - d := by
    calc vb - d = Y * (v'' - d) := by rw [hvb]; ring
      _ < (q * Y ^ (p - 1)) * (Y * (v'' - d)) :=
          lt_mul_of_one_lt_left (mul_pos hY0 hs'') hqY
      _ = (a v'' - d) * Y ^ p := by rw [hU, hYp]; ring
      _ ≤ a vb - d := h1
  linarith [hlt vb (by linarith)]

end CC.ODE
