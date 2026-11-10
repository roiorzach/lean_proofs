import ConformityConcerns.General.RevCalc
import ConformityConcerns.General.CP.Envelope
import ConformityConcerns.ODE.LeftTail
import Mathlib.Topology.Order.IntermediateValue

/-!
# Fully revealing equilibria (Section A4)

A continuous rule `a` that solves `a'(r) = ℓ'(r)/g'(r - a(r)) > 0` off the norm `μ` is globally
incentive compatible: the derivative of the loss `g(a(r) - v) + ℓ(r)` of type `v` mimicking type
`r` is `a'(r)[g'(a(r) - v) - g'(a(r) - r)]`, negative for `r < v` and positive for `r > v`. With
beliefs `δ_v` after `a(v)`, `δ_{+∞}` above the range of `a` and `δ_{-∞}` below it, the rule is a
compactified PBE. If the rule is surjective there are no off-path actions and `D1^∞` holds
vacuously. Otherwise, above the range, `I_x'(v) = g'(a(v) - v) - g'(x - v) < 0` and
`I_x(v) < -ℓ(v) ≤ 0` for `v > x`, so `S^∞(x) = {+∞}`; symmetrically below.
-/

namespace CC.General.Rev

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

variable (S : Setting)

open Classical in
/-- Beliefs for an injective rule `a`: `δ_v` after `a v`, `δ_{+∞}` above the range of `a`,
`δ_{-∞}` below it. -/
noncomputable def revBelief (a : ℝ → ℝ) (x : ℝ) : Measure EReal :=
  if x ∈ range a then Measure.dirac ((Function.invFun a x : ℝ) : EReal)
  else if ∀ r, a r < x then Measure.dirac ⊤ else Measure.dirac ⊥

lemma revBelief_self {a : ℝ → ℝ} (ha : Function.Injective a) (v : ℝ) :
    revBelief a (a v) = Measure.dirac (v : EReal) := by
  unfold revBelief
  rw [ite_eq_left (mem_range_self v), Function.leftInverse_invFun ha v]

lemma revBelief_top {a : ℝ → ℝ} {x : ℝ} (hx : x ∉ range a) (h : ∀ r, a r < x) :
    revBelief a x = Measure.dirac ⊤ := by
  unfold revBelief; rw [ite_eq_right hx, ite_eq_left h]

lemma revBelief_bot {a : ℝ → ℝ} {x : ℝ} (hx : x ∉ range a) (h : ¬ ∀ r, a r < x) :
    revBelief a x = Measure.dirac ⊥ := by
  unfold revBelief; rw [ite_eq_right hx, ite_eq_right h]

instance revBelief_prob (a : ℝ → ℝ) (x : ℝ) : IsProbabilityMeasure (revBelief a x) := by
  unfold revBelief; split_ifs <;> infer_instance

lemma ℓbar_coe' (v : ℝ) : S.ℓbar (v : EReal) = ENNReal.ofReal (S.ℓ v) := by
  unfold Setting.ℓbar; simp

lemma ℓbar_top' : S.ℓbar ⊤ = ∞ := by unfold Setting.ℓbar; simp

lemma ℓbar_bot' : S.ℓbar ⊥ = ∞ := by unfold Setting.ℓbar; simp

lemma confLoss_dirac_coe (φ : ℝ → Measure EReal) {x v : ℝ}
    (h : φ x = Measure.dirac (v : EReal)) : S.confLoss φ x = ENNReal.ofReal (S.ℓ v) := by
  unfold Setting.confLoss; rw [h, lintegral_dirac, ℓbar_coe']

lemma F_singleton (v : ℝ) : S.F {v} = 0 := by
  obtain ⟨ψ, -, -, hF⟩ := S.hF.density
  rw [hF]
  exact withDensity_absolutelyContinuous _ _ Real.volume_singleton

/-- A continuous strictly increasing rule that is globally incentive compatible under the
revealing beliefs is a compactified PBE. -/
theorem isCPBE_of_IC {a : ℝ → ℝ} (hc : Continuous a) (hm : StrictMono a)
    (hIC : ∀ v r, S.g (a v - v) + S.ℓ v ≤ S.g (a r - v) + S.ℓ r) :
    S.IsCPBE a (revBelief a) := by
  have hinj := hm.injective
  have hfib : ∀ v, a ⁻¹' {a v} = {v} := fun v => by
    ext w; simp [hinj.eq_iff]
  have hself := revBelief_self hinj
  have hconf : ∀ v, S.confLoss (revBelief a) (a v) = ENNReal.ofReal (S.ℓ v) :=
    fun v => confLoss_dirac_coe S _ (hself v)
  have hoff : ∀ x, x ∉ range a → S.confLoss (revBelief a) x = ∞ := by
    intro x hx
    unfold Setting.confLoss
    by_cases hup : ∀ r, a r < x
    · rw [revBelief_top hx hup, lintegral_dirac, ℓbar_top']
    · rw [revBelief_bot hx hup, lintegral_dirac, ℓbar_bot']
  have hℓ0 := ℓ_nonneg S.hℓ
  have hg0 := g_nonneg S.hg
  refine ⟨hc.measurable, revBelief_prob a, ?_, ?_, ?_, ?_, ?_⟩
  · -- optimality
    intro v x
    by_cases hx : x ∈ range a
    · obtain ⟨r, rfl⟩ := hx
      unfold Setting.loss
      rw [hconf v, hconf r, ← ENNReal.ofReal_add (hg0 _) (hℓ0 _),
        ← ENNReal.ofReal_add (hg0 _) (hℓ0 _)]
      exact ENNReal.ofReal_le_ofReal (hIC v r)
    · unfold Setting.loss
      rw [hoff x hx, add_top]
      exact le_top
  · intro v
    rw [hfib v, image_singleton, hself v]
    simp
  · intro v hpos
    rw [hfib v, F_singleton S v] at hpos
    exact absurd hpos (lt_irrefl 0)
  · intro v _
    exact hself v
  · intro v
    rw [hconf v]
    exact ENNReal.ofReal_lt_top

/-- `D1^∞` for a revealing rule that need not be surjective (proof of Proposition A6 (ii)). The
envelope formula gives `I_x'(v) = g'(a(v) - v) - g'(x - v) < 0` above the range of `a`, and
`I_x(v) < -ℓ(v) ≤ 0` for `v > x`, so `S^∞(x) = {+∞}`; symmetrically `S^∞(x) = {-∞}` below it. -/
theorem D1Inf_of_IC {a : ℝ → ℝ} (hc : Continuous a) (hm : StrictMono a)
    (hIC : ∀ v r, S.g (a v - v) + S.ℓ v ≤ S.g (a r - v) + S.ℓ r) :
    S.D1Inf a (revBelief a) := by
  have hE := isCPBE_of_IC S hc hm hIC
  have hU : ∀ v, S.U a (revBelief a) v = -(S.g (a v - v) + S.ℓ v) := by
    intro v
    unfold Setting.U
    rw [confLoss_dirac_coe S _ (revBelief_self hm.injective v),
      ENNReal.toReal_ofReal (ℓ_nonneg S.hℓ v)]
  have hI : ∀ x v, HasDerivAt (S.indiff a (revBelief a) x)
      (deriv S.g (a v - v) - deriv S.g (x - v)) v := by
    intro x v
    have h1 := hE.hasDerivAt_U (v := v) hc.continuousAt
    have hl : HasDerivAt (fun w => x - w) (-1) v := (hasDerivAt_id v).const_sub x
    have h2 := (S.hg.hasDerivAt (x - v)).comp v hl
    exact (h1.add h2).congr_deriv (by ring)
  intro x hx
  by_cases hup : ∀ r, a r < x
  · have hs : S.survivors a (revBelief a) x = {⊤} := Setting.survivors_eq_top
      (strictAnti_of_deriv_neg fun v => by
        rw [(hI x v).deriv]
        exact sub_neg.2 (S.hg.deriv_strictMono (sub_lt_sub_right (hup v) v)))
      ⟨x + 1, by
        unfold Setting.indiff
        rw [hU]
        have h1 := hup (x + 1)
        have h2 : S.g (x - (x + 1)) < S.g (a (x + 1) - (x + 1)) := S.hg.lt_of_abs_lt (by
          rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
          linarith)
        have h3 := ℓ_nonneg S.hℓ (x + 1)
        linarith⟩
    rw [revBelief_top hx hup, hs]
    exact Setting.support_dirac_subset ⊤
  · have hdown : ∀ r, x < a r := by
      intro r
      obtain ⟨r₀, hr₀⟩ := not_forall.1 hup
      have hr₀' : x < a r₀ :=
        lt_of_le_of_ne (not_lt.1 hr₀) (fun h => hx ⟨r₀, h.symm⟩)
      by_contra hr
      have hr' : a r < x := lt_of_le_of_ne (not_lt.1 hr) (fun h => hx ⟨r, h⟩)
      exact hx (intermediate_value_univ r r₀ hc ⟨hr'.le, hr₀'.le⟩)
    have hs : S.survivors a (revBelief a) x = {⊥} := Setting.survivors_eq_bot
      (strictMono_of_deriv_pos fun v => by
        rw [(hI x v).deriv]
        exact sub_pos.2 (S.hg.deriv_strictMono (sub_lt_sub_right (hdown v) v)))
      ⟨x - 1, by
        unfold Setting.indiff
        rw [hU]
        have h1 := hdown (x - 1)
        have h2 : S.g (x - (x - 1)) < S.g (a (x - 1) - (x - 1)) := S.hg.lt_of_abs_lt (by
          rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
          linarith)
        have h3 := ℓ_nonneg S.hℓ (x - 1)
        linarith⟩
    rw [revBelief_bot hx hup, hs]
    exact Setting.support_dirac_subset ⊥

/-- Global incentive compatibility of a solution of `a'(r) = ℓ'(r)/g'(r - a(r)) > 0` (off `μ`). -/
theorem IC_of_ODE {a : ℝ → ℝ} (hc : Continuous a)
    (hder : ∀ r, r ≠ S.μ → HasDerivAt a (deriv S.ℓ r / deriv S.g (r - a r)) r)
    (hpos : ∀ r, r ≠ S.μ → 0 < deriv S.ℓ r / deriv S.g (r - a r)) (v r : ℝ) :
    S.g (a v - v) + S.ℓ v ≤ S.g (a r - v) + S.ℓ r := by
  have hgd := g_differentiable S.hg
  have hℓd := ℓ_differentiable S.hℓ
  have hLc : Continuous (fun t => S.g (a t - v) + S.ℓ t) :=
    (hgd.continuous.comp (hc.sub continuous_const)).add hℓd.continuous
  have hLd : ∀ t, t ≠ S.μ → HasDerivAt (fun t => S.g (a t - v) + S.ℓ t)
      (deriv S.ℓ t / deriv S.g (t - a t) * (deriv S.g (a t - v) - deriv S.g (a t - t))) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => S.g (a t - v))
        (deriv S.g (a t - v) * (deriv S.ℓ t / deriv S.g (t - a t))) t :=
      (hgd (a t - v)).hasDerivAt.comp t ((hder t ht).sub_const v)
    have h2 : HasDerivAt S.ℓ (deriv S.ℓ t) t := (hℓd t).hasDerivAt
    have hne : deriv S.g (t - a t) ≠ 0 := by
      intro h0
      have := hpos t ht
      rw [h0, div_zero] at this
      exact lt_irrefl 0 this
    have hodd : deriv S.g (t - a t) = -deriv S.g (a t - t) := by
      rw [← g_deriv_neg S.hg, neg_sub]
    have := h1.add h2
    convert this using 1
    have e : deriv S.ℓ t = deriv S.ℓ t / deriv S.g (t - a t) * deriv S.g (t - a t) := by
      field_simp
    set A := deriv S.ℓ t / deriv S.g (t - a t) with hA
    rw [e, hodd]
    ring
  rcases lt_trichotomy r v with hrv | rfl | hrv
  · have key := le_of_hasDerivAt_nonneg_off (f := fun t => -(S.g (a t - v) + S.ℓ t))
      (f' := fun t => -(deriv S.ℓ t / deriv S.g (t - a t) *
        (deriv S.g (a t - v) - deriv S.g (a t - t)))) S.μ hrv.le hLc.neg.continuousOn
      (fun t _ ht => (hLd t ht).neg) (fun t htI ht => by
        have hA := hpos t ht
        have hlt : deriv S.g (a t - v) < deriv S.g (a t - t) :=
          g_deriv_strictMono S.hg (by linarith [htI.2])
        have := mul_neg_of_pos_of_neg hA (sub_neg.2 hlt)
        linarith)
    linarith
  · exact le_rfl
  · have key := le_of_hasDerivAt_nonneg_off (f := fun t => S.g (a t - v) + S.ℓ t)
      S.μ hrv.le hLc.continuousOn (fun t _ ht => hLd t ht) (fun t htI ht => by
        have hA := hpos t ht
        have hlt : deriv S.g (a t - t) < deriv S.g (a t - v) :=
          g_deriv_strictMono S.hg (by linarith [htI.1])
        exact (mul_pos hA (sub_pos.2 hlt)).le)
    exact key

/-- **Revealing equilibria.** A continuous rule solving `a'(r) = ℓ'(r)/g'(r - a(r)) > 0` for
every `r ≠ μ` is strictly increasing and, with the beliefs `revBelief a`, is a compactified PBE
satisfying `D1^∞`. -/
theorem exists_revealing {a : ℝ → ℝ} (hc : Continuous a)
    (hder : ∀ r, r ≠ S.μ → HasDerivAt a (deriv S.ℓ r / deriv S.g (r - a r)) r)
    (hpos : ∀ r, r ≠ S.μ → 0 < deriv S.ℓ r / deriv S.g (r - a r)) :
    StrictMono a ∧ ∃ φ, S.IsCPBE a φ ∧ S.D1Inf a φ := by
  have hm : StrictMono a := strictMono_of_hasDerivAt_pos_off S.μ hc hder hpos
  have hIC := IC_of_ODE S hc hder hpos
  exact ⟨hm, revBelief a, isCPBE_of_IC S hc hm hIC, D1Inf_of_IC S hc hm hIC⟩

/-- A surjective rule has no off-path actions, so `D1^∞` holds vacuously. -/
theorem exists_revealing_surjective {a : ℝ → ℝ} (hc : Continuous a)
    (hder : ∀ r, r ≠ S.μ → HasDerivAt a (deriv S.ℓ r / deriv S.g (r - a r)) r)
    (hpos : ∀ r, r ≠ S.μ → 0 < deriv S.ℓ r / deriv S.g (r - a r))
    (hs : Function.Surjective a) :
    StrictMono a ∧ ∃ φ, S.IsCPBE a φ ∧ S.D1Inf a φ := by
  have hm : StrictMono a := strictMono_of_hasDerivAt_pos_off S.μ hc hder hpos
  exact ⟨hm, revBelief a, isCPBE_of_IC S hc hm (IC_of_ODE S hc hder hpos),
    fun x hx => absurd (hs x) hx⟩

/-- The strictly increasing solution of `a' = κ f(v)/(v - a(v))` with `a(c) = c` given by Lemma A3
and Corollary A1 when `κ f' ≤ κck`. -/
theorem exists_solution {κ : ℝ} (hκ : 0 < κ) {f : ℝ → ℝ} (hfm : StrictMono f) (hf1 : ContDiff ℝ 1 f)
    {c : ℝ} (hfc : f c = 0) (hsup : ∀ x, κ * deriv f x ≤ κck) :
    ∃ a : ℝ → ℝ, Continuous a ∧ a c = c ∧ StrictMono a ∧
      ∀ r, r ≠ c → HasDerivAt a (κ * f r / (r - a r)) r ∧ 0 < κ * f r / (r - a r) := by
  obtain ⟨aR, ⟨hRc, -, hRlt, hRd⟩, hR0⟩ :=
    CC.ODE.lemmaA3_iii κ hκ f hfm hf1 hfc (fun v _ => hsup v)
  obtain ⟨aL, ⟨hLc, -, hLgt, hLd⟩, hL0⟩ :=
    CC.ODE.corollaryA1_iii κ hκ f hfm hf1 hfc (fun v _ => hsup v)
  set a := glue c aR aL with ha
  have hac : Continuous a := glue_continuous hRc hLc (by rw [hR0, hL0])
  have hd : ∀ r, r ≠ c → HasDerivAt a (κ * f r / (r - a r)) r ∧ 0 < κ * f r / (r - a r) := by
    intro r hr
    rcases hr.lt_or_gt with hr | hr
    · have hd := (hLd r hr).congr_of_eventuallyEq (glue_eventuallyEq_L (aR := aR) hr)
      have har : a r = aL r := glue_of_lt hr
      rw [har]
      have hfr : f r < 0 := by rw [← hfc]; exact hfm hr
      refine ⟨hd.congr_deriv ?_, div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hκ hfr)
        (by linarith [hLgt r hr])⟩
      simp only [id]
      rw [show c - (c - r) = r by ring, show aL r - r = -(r - aL r) by ring, div_neg,
        neg_mul, neg_div, neg_neg]
    · have hd := (hRd r hr).congr_of_eventuallyEq (glue_eventuallyEq_R (aL := aL) hr)
      have har : a r = aR r := glue_of_le hr.le
      rw [har]
      have hfr : 0 < f r := by rw [← hfc]; exact hfm hr
      refine ⟨hd.congr_deriv ?_, div_pos (mul_pos hκ hfr) (by linarith [hRlt r hr])⟩
      simp only [id, add_sub_cancel]
  exact ⟨a, hac, by rw [ha, glue_of_le le_rfl, hR0],
    strictMono_of_hasDerivAt_pos_off c hac (fun r hr => (hd r hr).1) (fun r hr => (hd r hr).2), hd⟩

/-- There are no off-path actions: a strictly increasing solution of `a' = κ f(v)/(v - a(v))` with
`a(c) = c` is surjective. For `v > c` we have `c ≤ a(v) < v`, so `a'(v) ≥ κ f(v)/(v - c)`, whose
integral diverges; symmetrically below `c`. -/
theorem surjective_of_ode {κ : ℝ} (hκ : 0 < κ) {f a : ℝ → ℝ} {c : ℝ} (hf : StrictMono f)
    (hfc : f c = 0) (hc : Continuous a) (hac : a c = c) (hm : StrictMono a)
    (hd : ∀ r, r ≠ c → HasDerivAt a (κ * f r / (r - a r)) r ∧ 0 < κ * f r / (r - a r)) :
    Function.Surjective a := by
  have hf1 : 0 < f (c + 1) := by rw [← hfc]; exact hf (by linarith)
  have hf2 : 0 < -f (c - 1) := by
    have : f (c - 1) < f c := hf (by linarith)
    rw [hfc] at this
    linarith
  set m := min (f (c + 1)) (-f (c - 1)) with hmdef
  have hm0 : 0 < m := lt_min hf1 hf2
  have hk : 0 < κ * m := mul_pos hκ hm0
  have hR : ∀ v, c + 1 ≤ v → κ * m / (v - c) ≤ κ * f v / (v - a v) := by
    intro v hv
    have hfv : f (c + 1) ≤ f v := hf.monotone hv
    have hfv0 : 0 < f v := lt_of_lt_of_le hf1 hfv
    have hpos := (hd v (by linarith : c < v).ne').2
    have hgap : 0 < v - a v := by
      rcases div_pos_iff.1 hpos with h | h
      · exact h.2
      · exact absurd h.1 (not_lt.2 (mul_pos hκ hfv0).le)
    have hac' : c ≤ a v := by
      have := hm.monotone (show c ≤ v by linarith)
      rwa [hac] at this
    calc κ * m / (v - c) ≤ κ * f v / (v - c) := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hfv) hκ.le
      _ ≤ κ * f v / (v - a v) :=
          div_le_div_of_nonneg_left (mul_pos hκ hfv0).le hgap (by linarith)
  have hL : ∀ v, v ≤ c - 1 → κ * m / (c - v) ≤ κ * f v / (v - a v) := by
    intro v hv
    have hfv : f v ≤ f (c - 1) := hf.monotone hv
    have hfv0 : 0 < -f v := by linarith
    have hpos := (hd v (by linarith : v < c).ne).2
    have hgap : 0 < a v - v := by
      rcases div_pos_iff.1 hpos with h | h
      · exact absurd h.1 (not_lt.2 (by nlinarith [mul_pos hκ hfv0]))
      · linarith [h.2]
    have hac' : a v ≤ c := by
      have := hm.monotone (show v ≤ c by linarith)
      rwa [hac] at this
    have e : κ * f v / (v - a v) = κ * -f v / (a v - v) := by
      rw [show a v - v = -(v - a v) by ring, div_neg, mul_neg, neg_div, neg_neg]
    rw [e]
    calc κ * m / (c - v) ≤ κ * -f v / (c - v) := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          refine mul_le_mul_of_nonneg_left ((min_le_right _ _).trans ?_) hκ.le
          linarith
      _ ≤ κ * -f v / (a v - v) :=
          div_le_div_of_nonneg_left (mul_pos hκ hfv0).le hgap (by linarith)
  refine hc.surjective ?_ ?_
  · -- the integral diverges at `+∞`
    have hlog : ∀ v, c + 1 ≤ v → a (c + 1) + κ * m * Real.log (v - c) ≤ a v := by
      intro v hv
      have hder : ∀ t, c + 1 ≤ t → HasDerivAt (fun w => a w - κ * m * Real.log (w - c))
          (κ * f t / (t - a t) - κ * m * (1 / (t - c))) t := fun t ht =>
        (hd t (by linarith : c < t).ne').1.sub
          ((((hasDerivAt_id' t).sub_const c).log (sub_pos.2 (by linarith : c < t)).ne').const_mul
            (κ * m))
      have key := le_of_hasDerivAt_nonneg (f := fun w => a w - κ * m * Real.log (w - c)) hv
        (fun t ht => (hder t ht.1).continuousAt.continuousWithinAt)
        (fun t ht => hder t ht.1.le)
        (fun t ht => by
          have := hR t ht.1.le
          rw [mul_one_div]
          linarith)
      simp only [add_sub_cancel_left, Real.log_one, mul_zero, sub_zero] at key
      linarith
    have hv : Tendsto (fun v : ℝ => v - c) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (-c) tendsto_id).congr fun v => by simp [sub_eq_add_neg]
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_left atTop (a (c + 1))
      ((Real.tendsto_log_atTop.comp hv).const_mul_atTop hk))
    filter_upwards [eventually_ge_atTop (c + 1)] with v hv
    exact hlog v hv
  · -- the integral diverges at `-∞`
    have hlog : ∀ v, v ≤ c - 1 → a v ≤ a (c - 1) - κ * m * Real.log (c - v) := by
      intro v hv
      have hder : ∀ t, t ≤ c - 1 → HasDerivAt (fun w => a w + κ * m * Real.log (c - w))
          (κ * f t / (t - a t) + κ * m * (-1 / (c - t))) t := fun t ht =>
        (hd t (by linarith : t < c).ne).1.add
          (((hasDerivAt_id' t).const_sub c |>.log (sub_pos.2 (by linarith : t < c)).ne').const_mul
            (κ * m))
      have key := le_of_hasDerivAt_nonneg (f := fun w => a w + κ * m * Real.log (c - w)) hv
        (fun t ht => (hder t ht.2).continuousAt.continuousWithinAt)
        (fun t ht => hder t ht.2.le)
        (fun t ht => by
          have := hL t ht.2.le
          have e : κ * m * (-1 / (c - t)) = -(κ * m / (c - t)) := by ring
          rw [e]
          linarith)
      simp only [sub_sub_cancel, Real.log_one, mul_zero, add_zero] at key
      linarith
    have hv : Tendsto (fun v : ℝ => c - v) atBot atTop :=
      (tendsto_atTop_add_const_right atBot c tendsto_neg_atBot_atTop).congr fun v => by ring
    have hT : Tendsto (fun v : ℝ => a (c - 1) - κ * m * Real.log (c - v)) atBot atBot := by
      have := (tendsto_neg_atTop_atBot.comp ((Real.tendsto_log_atTop.comp hv).const_mul_atTop hk))
      exact (tendsto_atBot_add_const_left atBot (a (c - 1)) this).congr fun v => by
        simp [sub_eq_add_neg]
    refine tendsto_atBot_mono' atBot ?_ hT
    filter_upwards [eventually_le_atBot (c - 1)] with v hv
    exact hlog v hv

end CC.General.Rev
