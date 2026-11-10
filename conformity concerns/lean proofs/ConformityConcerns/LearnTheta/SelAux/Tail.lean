import ConformityConcerns.ODE.LeftTail
import ConformityConcerns.General.RevCalc

/-!
# Explicit tail solutions for the measurable choice of a revealing equilibrium

`Gap.exists_solution`, `lemmaA3_ii`, `lemmaA3_iii` and `corollaryA1_iii` with their explicit
witnesses: the right tail `v ↦ v - wLim Ψ id (v - c)` and the reflected left tail
`v ↦ v + wLim Ψ̃ id (c - v)`, where `wLim` is the limit of the monotone iteration of
`ODE/Existence.lean`. `selRule κ f c` glues them at `c`.
-/

namespace CC.LearnTheta.SelAux

open Set Filter Topology CC.ODE

variable {Ψ Γ : ℝ → ℝ}

/-- `Gap.exists_solution` with the explicit witness `wLim`. -/
lemma wLim_solution (h : TailData Ψ Γ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) :
    Gap.wLim Ψ Γ 0 = 0 ∧ ContinuousOn (Gap.wLim Ψ Γ) (Ici 0) ∧
      (∀ x, 0 < x → 0 < Gap.wLim Ψ Γ x) ∧
      (∀ x, 0 < x → HasDerivAt (Gap.wLim Ψ Γ) (1 - Ψ x / Γ (Gap.wLim Ψ Γ x)) x) ∧
      ContinuousOn (fun x => 1 - Ψ x / Γ (Gap.wLim Ψ Γ x)) (Ioi 0) := by
  have hadm := Gap.wLim_adm h hβ0 hβ1 hΨ
  have hcont := hadm.rhs_continuousOn h hβ0
  refine ⟨hadm.zero, hadm.continuousOn hβ0.le, fun x hx => hadm.pos hβ0 hx,
    fun x hx => ?_, hcont⟩
  have hd : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, Gap.rhs Ψ Γ t (Gap.wLim Ψ Γ t))
      (Gap.rhs Ψ Γ x (Gap.wLim Ψ Γ x)) x :=
    intervalIntegral.integral_hasDerivAt_right (hadm.intervalIntegrable h hβ0 hΨ le_rfl hx.le)
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hcont.continuousAt (Ioi_mem_nhds hx))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with u hu
  exact Gap.wLim_eq h hβ0 hβ1 hΨ (le_of_lt hu)

lemma wIter_zero (Ψ Γ : ℝ → ℝ) : ∀ n, Gap.wIter Ψ Γ n 0 = 0
  | 0 => rfl
  | _ + 1 => intervalIntegral.integral_same

lemma wLim_zero (Ψ Γ : ℝ → ℝ) : Gap.wLim Ψ Γ 0 = 0 := by
  simp only [Gap.wLim, wIter_zero, ciInf_const]

/-- The proof of `lemmaA3_ii` for a given solution `w` of the gap equation. -/
lemma rightTail_of_gap {w : ℝ → ℝ} (c : ℝ) (hw0 : w 0 = 0) (hwc : ContinuousOn w (Ici 0))
    (hwpos : ∀ x, 0 < x → 0 < w x)
    (hwd : ∀ x, 0 < x → HasDerivAt w (1 - Ψ x / Γ (w x)) x)
    (hgc : ContinuousOn (fun x => 1 - Ψ x / Γ (w x)) (Ioi 0)) :
    IsRightTailSol Ψ Γ c c (fun v => v - w (v - c)) ∧ c - w (c - c) = c := by
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
  refine ⟨⟨?_, ?_, fun v hv => ?_, hder⟩, ?_⟩
  · exact continuousOn_id.sub (hwc.comp (continuousOn_id.sub continuousOn_const)
      fun v (hv : c ≤ v) => mem_Ici.2 (sub_nonneg.2 hv))
  · exact contDiffOn_one_of_hasDerivAt isOpen_Ioi hda
      (continuousOn_const.sub (hgc.comp (continuousOn_id.sub continuousOn_const) hmaps))
  · have := hwpos (v - c) (sub_pos.2 hv)
    linarith
  · simp [hw0]

/-- The explicit right tail `v ↦ v - wLim Ψ id (v - c)`, `Ψ(x) = κ f(c + x)`. -/
noncomputable def tailR (κ : ℝ) (f : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun v => v - Gap.wLim (fun x => κ * f (c + x)) id (v - c)

/-- The explicit left tail `v ↦ v + wLim Ψ̃ id (c - v)`, `Ψ̃(x) = -κ f(c - x)`. -/
noncomputable def tailL (κ : ℝ) (f : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun v => v + Gap.wLim (fun x => -κ * f (c - x)) id (c - v)

/-- `lemmaA3_iii` with the explicit witness `tailR`. -/
lemma tailR_sol (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℝ) (hf : StrictMono f) (hf1 : ContDiff ℝ 1 f)
    {c : ℝ} (hfc : f c = 0) (hsup : ∀ v, c ≤ v → κ * deriv f v ≤ κck) :
    IsRightTailSol (fun x => κ * f (c + x)) id c c (tailR κ f c) ∧ tailR κ f c c = c := by
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
  obtain ⟨hw0, hwc, hwpos, hwd, hgc⟩ :=
    wLim_solution (β := 1 / 2) hT (by norm_num) (by norm_num) hΨ
  exact rightTail_of_gap c hw0 hwc hwpos hwd hgc

/-- Transport of right-tail solutions along an equality of the `Ψ`'s. -/
lemma isRightTailSol_congr {Ψ₁ Ψ₂ : ℝ → ℝ} (c : ℝ) (hΨ : Ψ₁ = Ψ₂)
    (h : IsRightTailSol Ψ₁ id c c (fun v => v - Gap.wLim Ψ₁ id (v - c))) :
    IsRightTailSol Ψ₂ id c c (fun v => v - Gap.wLim Ψ₂ id (v - c)) := by
  subst hΨ; exact h

/-- `corollaryA1_iii` with the explicit witness `tailL`. -/
lemma tailL_sol (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℝ) (hf : StrictMono f) (hf1 : ContDiff ℝ 1 f)
    {c : ℝ} (hfc : f c = 0) (hsup : ∀ v, v ≤ c → κ * deriv f v ≤ κck) :
    IsLeftTailSol (fun x => -κ * f (c - x)) id c c (tailL κ f c) ∧ tailL κ f c c = c := by
  obtain ⟨hgm, hg1, hgc, hgd, hΨeq⟩ := reflect_props (c := c) κ f hf hf1 hfc
  obtain ⟨hb, -⟩ := tailR_sol κ hκ _ hgm hg1 hgc
    (fun v hv => by rw [hgd]; exact hsup _ (by linarith))
  have hb' := isRightTailSol_congr c hΨeq hb
  have hL := isLeftTailSol_of_right (d := c) (by ring) hb'
  have heq : (fun v => 2 * c - (fun v => v - Gap.wLim (fun x => -κ * f (c - x)) id (v - c))
      (2 * c - v)) = tailL κ f c := by
    funext v
    simp only [tailL]
    rw [show 2 * c - v - c = c - v by ring]
    ring
  rw [heq] at hL
  exact ⟨hL, by simp only [tailL, sub_self, wLim_zero, add_zero]⟩

/-- The explicit fully revealing rule: `tailR` on `[c, ∞)`, `tailL` on `(-∞, c)`. -/
noncomputable def selRule (κ : ℝ) (f : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  CC.General.Rev.glue c (tailR κ f c) (tailL κ f c)

/-- The glued rule is continuous and solves `a'(r) = κ f(r)/(r - a(r)) > 0` off `c`. -/
lemma selRule_ode (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℝ) (hfm : StrictMono f) (hf1 : ContDiff ℝ 1 f)
    {c : ℝ} (hfc : f c = 0) (hsup : ∀ v, κ * deriv f v ≤ κck) :
    Continuous (selRule κ f c) ∧ ∀ r, r ≠ c →
      HasDerivAt (selRule κ f c) (κ * f r / (r - selRule κ f c r)) r ∧
        0 < κ * f r / (r - selRule κ f c r) := by
  obtain ⟨⟨hRc, -, hRlt, hRd⟩, hR0⟩ := tailR_sol κ hκ f hfm hf1 hfc (fun v _ => hsup v)
  obtain ⟨⟨hLc, -, hLgt, hLd⟩, hL0⟩ := tailL_sol κ hκ f hfm hf1 hfc (fun v _ => hsup v)
  have hac : Continuous (selRule κ f c) :=
    CC.General.Rev.glue_continuous hRc hLc (hR0.trans hL0.symm)
  refine ⟨hac, fun r hr => ?_⟩
  rcases hr.lt_or_gt with hr | hr
  · have hd := (hLd r hr).congr_of_eventuallyEq
      (CC.General.Rev.glue_eventuallyEq_L (aR := tailR κ f c) hr)
    have har : selRule κ f c r = tailL κ f c r := CC.General.Rev.glue_of_lt hr
    rw [har]
    have hfr : f r < 0 := by rw [← hfc]; exact hfm hr
    exact ⟨hd.congr_deriv (corollaryA1_equation κ f (tailL κ f c) r),
      div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hκ hfr) (by linarith [hLgt r hr])⟩
  · have hd := (hRd r hr).congr_of_eventuallyEq
      (CC.General.Rev.glue_eventuallyEq_R (aL := tailL κ f c) hr)
    have har : selRule κ f c r = tailR κ f c r := CC.General.Rev.glue_of_le hr.le
    rw [har]
    have hfr : 0 < f r := by rw [← hfc]; exact hfm hr
    refine ⟨hd.congr_deriv ?_, div_pos (mul_pos hκ hfr) (by linarith [hRlt r hr])⟩
    simp only [id, add_sub_cancel]

/-- The glued rule takes the value `c` at `c`. -/
lemma selRule_self (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℝ) (hfm : StrictMono f) (hf1 : ContDiff ℝ 1 f)
    {c : ℝ} (hfc : f c = 0) (hsup : ∀ v, κ * deriv f v ≤ κck) : selRule κ f c c = c := by
  obtain ⟨-, hR0⟩ := tailR_sol κ hκ f hfm hf1 hfc (fun v _ => hsup v)
  rw [selRule, CC.General.Rev.glue_of_le le_rfl, hR0]

end CC.LearnTheta.SelAux
