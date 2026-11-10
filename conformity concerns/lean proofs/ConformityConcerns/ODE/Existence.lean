import ConformityConcerns.ODE.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Existence for the gap equation (used in Lemma A3 (ii))

Let `Ψ, Γ` satisfy `TailData` and let `β ∈ (0,1)` with `Ψ(x) ≤ (1-β) Γ(βx)` for `x > 0`.
We construct `w` with `w(0) = 0`, `βx ≤ w(x) ≤ x` on `[0,∞)`, solving
`w'(x) = 1 - Ψ(x)/Γ(w(x))` on `(0,∞)`.

As in the proof of Lemma A3 (ii), we iterate the integral operator
`(T u)(x) = ∫₀ˣ (1 - Ψ(t)/Γ(u(t))) dt`, started at `w₀(x) = x`.
Since the integrand is increasing in `u`, `T` is monotone; it maps the class of functions whose
slopes lie in `[β, 1]` and which vanish at `0` into itself (this uses `Ψ(t) ≤ (1-β)Γ(βt)`), and
`T w₀ ≤ w₀`. Hence the iterates decrease to a limit `w`, which by dominated convergence is a fixed
point of `T`; the fundamental theorem of calculus then gives the differential equation.
-/

namespace CC.ODE.Gap

open Set Filter Topology MeasureTheory

/-- Right-hand side of the gap equation `w' = 1 - Ψ(x)/Γ(w)`. -/
noncomputable def rhs (Ψ Γ : ℝ → ℝ) (t w : ℝ) : ℝ := 1 - Ψ t / Γ w

/-- The integral operator `(T u)(x) = ∫₀ˣ (1 - Ψ(t)/Γ(u(t))) dt`. -/
noncomputable def T (Ψ Γ : ℝ → ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, rhs Ψ Γ t (u t)

/-- The iterates `w₀(x) = x`, `w_{n+1} = T w_n`. -/
noncomputable def wIter (Ψ Γ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => x
  | n + 1 => T Ψ Γ (wIter Ψ Γ n)

/-- The pointwise limit (infimum) of the iterates. -/
noncomputable def wLim (Ψ Γ : ℝ → ℝ) (x : ℝ) : ℝ := ⨅ n, wIter Ψ Γ n x

/-- Admissible functions: `u(0) = 0` and slopes in `[β, 1]` on `[0, ∞)`. -/
structure Adm (β : ℝ) (u : ℝ → ℝ) : Prop where
  zero : u 0 = 0
  slope : ∀ x y, 0 ≤ x → x ≤ y → β * (y - x) ≤ u y - u x ∧ u y - u x ≤ y - x

variable {Ψ Γ : ℝ → ℝ} {β : ℝ}

lemma Adm.lower {u : ℝ → ℝ} (hu : Adm β u) {x : ℝ} (hx : 0 ≤ x) : β * x ≤ u x := by
  have := (hu.slope 0 x le_rfl hx).1
  rw [hu.zero, sub_zero, sub_zero] at this
  exact this

lemma Adm.upper {u : ℝ → ℝ} (hu : Adm β u) {x : ℝ} (hx : 0 ≤ x) : u x ≤ x := by
  have := (hu.slope 0 x le_rfl hx).2
  rw [hu.zero, sub_zero, sub_zero] at this
  exact this

lemma Adm.pos (hβ0 : 0 < β) {u : ℝ → ℝ} (hu : Adm β u) {x : ℝ} (hx : 0 < x) : 0 < u x :=
  lt_of_lt_of_le (mul_pos hβ0 hx) (hu.lower hx.le)

lemma Adm.continuousOn (hβ0 : 0 ≤ β) {u : ℝ → ℝ} (hu : Adm β u) : ContinuousOn u (Ici 0) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx y hy => ?_).continuousOn
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total x y with hxy | hxy
  · obtain ⟨h1, h2⟩ := hu.slope x y hx hxy
    have : 0 ≤ β * (y - x) := mul_nonneg hβ0 (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h2
  · obtain ⟨h1, h2⟩ := hu.slope y x hy hxy
    have : 0 ≤ β * (x - y) := mul_nonneg hβ0 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact h2

lemma rhs_bounds (h : TailData Ψ Γ) (hβ0 : 0 < β)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) {t w : ℝ} (ht : 0 < t) (hw : β * t ≤ w) :
    β ≤ rhs Ψ Γ t w ∧ rhs Ψ Γ t w ≤ 1 := by
  have hbt : 0 < β * t := mul_pos hβ0 ht
  have hw0 : 0 < w := lt_of_lt_of_le hbt hw
  have hΓbt : 0 < Γ (β * t) := h.Γ_pos _ hbt
  have hΓw : 0 < Γ w := h.Γ_pos _ hw0
  have hΨt : 0 < Ψ t := h.Ψ_pos _ ht
  have h1 : Ψ t / Γ w ≤ Ψ t / Γ (β * t) :=
    div_le_div_of_nonneg_left hΨt.le hΓbt (h.Γ_mono hbt hw0 hw)
  have h2 : Ψ t / Γ (β * t) ≤ 1 - β := (div_le_iff₀ hΓbt).2 (hΨ t ht)
  have h3 : 0 < Ψ t / Γ w := div_pos hΨt hΓw
  unfold rhs
  constructor <;> linarith

lemma rhs_mono (h : TailData Ψ Γ) (hβ0 : 0 < β) {t u v : ℝ} (ht : 0 < t) (hu : β * t ≤ u)
    (huv : u ≤ v) : rhs Ψ Γ t u ≤ rhs Ψ Γ t v := by
  have hu0 : 0 < u := lt_of_lt_of_le (mul_pos hβ0 ht) hu
  have : Ψ t / Γ v ≤ Ψ t / Γ u :=
    div_le_div_of_nonneg_left (h.Ψ_pos _ ht).le (h.Γ_pos _ hu0)
      (h.Γ_mono hu0 (lt_of_lt_of_le hu0 huv) huv)
  unfold rhs
  linarith

lemma rhs_continuousOn (h : TailData Ψ Γ) {u : ℝ → ℝ} (hu : ContinuousOn u (Ioi 0))
    (hpos : ∀ t, 0 < t → 0 < u t) : ContinuousOn (fun t => rhs Ψ Γ t (u t)) (Ioi 0) := by
  unfold rhs
  exact continuousOn_const.sub (h.Ψ_C1.continuousOn.div
    (h.Γ_C1.continuousOn.comp hu fun t ht => hpos t ht) fun t ht => (h.Γ_pos _ (hpos t ht)).ne')

lemma intervalIntegrable_of_bdd {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    (hb : ∀ t, 0 < t → |g t| ≤ 1) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    IntervalIntegrable g volume x y := by
  have hsub : uIoc x y ⊆ Ioi 0 := fun t ht => lt_of_le_of_lt (le_min hx hy) ht.1
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    ((hg.mono hsub).aestronglyMeasurable measurableSet_uIoc) 1 ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun t ht => by rw [Real.norm_eq_abs]; exact hb t (hsub ht)

lemma Adm.rhs_continuousOn {u : ℝ → ℝ} (hu : Adm β u) (h : TailData Ψ Γ) (hβ0 : 0 < β) :
    ContinuousOn (fun t => rhs Ψ Γ t (u t)) (Ioi 0) :=
  Gap.rhs_continuousOn h ((hu.continuousOn hβ0.le).mono Ioi_subset_Ici_self)
    fun _ ht => hu.pos hβ0 ht

lemma Adm.rhs_abs_le {u : ℝ → ℝ} (hu : Adm β u) (h : TailData Ψ Γ) (hβ0 : 0 < β)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) {t : ℝ} (ht : 0 < t) :
    |rhs Ψ Γ t (u t)| ≤ 1 := by
  obtain ⟨h1, h2⟩ := rhs_bounds h hβ0 hΨ ht (hu.lower ht.le)
  rw [abs_le]
  constructor <;> linarith

lemma Adm.intervalIntegrable {u : ℝ → ℝ} (hu : Adm β u) (h : TailData Ψ Γ) (hβ0 : 0 < β)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    IntervalIntegrable (fun t => rhs Ψ Γ t (u t)) volume x y :=
  intervalIntegrable_of_bdd (hu.rhs_continuousOn h hβ0) (fun _ ht => hu.rhs_abs_le h hβ0 hΨ ht)
    hx hy

lemma T_adm (h : TailData Ψ Γ) (hβ0 : 0 < β) (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x))
    {u : ℝ → ℝ} (hu : Adm β u) : Adm β (T Ψ Γ u) := by
  refine ⟨intervalIntegral.integral_same, fun x y hx hxy => ?_⟩
  have hy : 0 ≤ y := hx.trans hxy
  have hdiff : T Ψ Γ u y - T Ψ Γ u x = ∫ t in x..y, rhs Ψ Γ t (u t) :=
    intervalIntegral.integral_interval_sub_left (hu.intervalIntegrable h hβ0 hΨ le_rfl hy)
      (hu.intervalIntegrable h hβ0 hΨ le_rfl hx)
  rw [hdiff]
  have hint := hu.intervalIntegrable h hβ0 hΨ hx hy
  constructor
  · have : ∫ _ in x..y, β ≤ ∫ t in x..y, rhs Ψ Γ t (u t) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hxy intervalIntegrable_const hint
        (fun t ht => (rhs_bounds h hβ0 hΨ (lt_of_le_of_lt hx ht.1)
          (hu.lower (le_of_lt (lt_of_le_of_lt hx ht.1)))).1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · have : ∫ t in x..y, rhs Ψ Γ t (u t) ≤ ∫ _ in x..y, (1 : ℝ) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hxy hint intervalIntegrable_const
        (fun t ht => (rhs_bounds h hβ0 hΨ (lt_of_le_of_lt hx ht.1)
          (hu.lower (le_of_lt (lt_of_le_of_lt hx ht.1)))).2)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
    exact this

lemma T_mono (h : TailData Ψ Γ) (hβ0 : 0 < β) (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x))
    {u v : ℝ → ℝ} (hu : Adm β u) (hv : Adm β v) (huv : ∀ x, 0 ≤ x → u x ≤ v x) {x : ℝ}
    (hx : 0 ≤ x) : T Ψ Γ u x ≤ T Ψ Γ v x :=
  intervalIntegral.integral_mono_on_of_le_Ioo hx (hu.intervalIntegrable h hβ0 hΨ le_rfl hx)
    (hv.intervalIntegrable h hβ0 hΨ le_rfl hx)
    (fun t ht => rhs_mono h hβ0 ht.1 (hu.lower ht.1.le) (huv t ht.1.le))

lemma wIter_adm (h : TailData Ψ Γ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) : ∀ n, Adm β (wIter Ψ Γ n)
  | 0 => ⟨rfl, fun x y _ hxy => by
      show β * (y - x) ≤ y - x ∧ y - x ≤ y - x
      have := mul_le_mul_of_nonneg_right hβ1.le (sub_nonneg.2 hxy)
      exact ⟨by linarith, le_rfl⟩⟩
  | n + 1 => T_adm h hβ0 hΨ (wIter_adm h hβ0 hβ1 hΨ n)

lemma wIter_anti (h : TailData Ψ Γ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) :
    ∀ n x, 0 ≤ x → wIter Ψ Γ (n + 1) x ≤ wIter Ψ Γ n x
  | 0, _, hx => (wIter_adm h hβ0 hβ1 hΨ 1).upper hx
  | n + 1, _, hx => T_mono h hβ0 hΨ (wIter_adm h hβ0 hβ1 hΨ (n + 1)) (wIter_adm h hβ0 hβ1 hΨ n)
      (fun y hy => wIter_anti h hβ0 hβ1 hΨ n y hy) hx

lemma tendsto_wIter (h : TailData Ψ Γ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => wIter Ψ Γ n x) atTop (𝓝 (wLim Ψ Γ x)) :=
  tendsto_atTop_ciInf (antitone_nat_of_succ_le fun n => wIter_anti h hβ0 hβ1 hΨ n x hx)
    ⟨β * x, by rintro _ ⟨n, rfl⟩; exact (wIter_adm h hβ0 hβ1 hΨ n).lower hx⟩

lemma wLim_adm (h : TailData Ψ Γ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) : Adm β (wLim Ψ Γ) := by
  refine ⟨?_, fun x y hx hxy => ?_⟩
  · have : ∀ n, wIter Ψ Γ n 0 = 0 := fun n => (wIter_adm h hβ0 hβ1 hΨ n).zero
    simp only [wLim, this, ciInf_const]
  · have hy := hx.trans hxy
    have ht := (tendsto_wIter h hβ0 hβ1 hΨ hy).sub (tendsto_wIter h hβ0 hβ1 hΨ hx)
    exact ⟨ge_of_tendsto' ht fun n => ((wIter_adm h hβ0 hβ1 hΨ n).slope x y hx hxy).1,
      le_of_tendsto' ht fun n => ((wIter_adm h hβ0 hβ1 hΨ n).slope x y hx hxy).2⟩

/-- The limit is a fixed point of `T` on `[0, ∞)`. -/
lemma wLim_eq (h : TailData Ψ Γ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) {x : ℝ} (hx : 0 ≤ x) :
    wLim Ψ Γ x = T Ψ Γ (wLim Ψ Γ) x := by
  have hadm := wLim_adm h hβ0 hβ1 hΨ
  have h1 : Tendsto (fun n => wIter Ψ Γ (n + 1) x) atTop (𝓝 (wLim Ψ Γ x)) :=
    (tendsto_wIter h hβ0 hβ1 hΨ hx).comp (tendsto_add_atTop_nat 1)
  have hsub : uIoc 0 x ⊆ Ioi 0 := fun t ht => lt_of_le_of_lt (le_min le_rfl hx) ht.1
  have h2 : Tendsto (fun n => ∫ t in (0 : ℝ)..x, rhs Ψ Γ t (wIter Ψ Γ n t)) atTop
      (𝓝 (∫ t in (0 : ℝ)..x, rhs Ψ Γ t (wLim Ψ Γ t))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (F := fun n t => rhs Ψ Γ t (wIter Ψ Γ n t)) (fun _ => (1 : ℝ)) ?_ ?_
      intervalIntegrable_const ?_
    · exact Eventually.of_forall fun n =>
        (((wIter_adm h hβ0 hβ1 hΨ n).rhs_continuousOn h hβ0).mono hsub).aestronglyMeasurable
          measurableSet_uIoc
    · exact Eventually.of_forall fun n => Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs]
        exact (wIter_adm h hβ0 hβ1 hΨ n).rhs_abs_le h hβ0 hΨ (hsub ht)
    · refine Eventually.of_forall fun t ht => ?_
      have ht0 : 0 < t := hsub ht
      have hw : 0 < wLim Ψ Γ t := hadm.pos hβ0 ht0
      have hΓc : ContinuousAt Γ (wLim Ψ Γ t) :=
        h.Γ_C1.continuousOn.continuousAt (Ioi_mem_nhds hw)
      unfold rhs
      exact tendsto_const_nhds.sub (tendsto_const_nhds.div
        (hΓc.tendsto.comp (tendsto_wIter h hβ0 hβ1 hΨ ht0.le)) (h.Γ_pos _ hw).ne')
  exact tendsto_nhds_unique h1 h2

/-- **Existence for the gap equation.** -/
theorem exists_solution (h : TailData Ψ Γ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) :
    ∃ w : ℝ → ℝ, w 0 = 0 ∧ ContinuousOn w (Ici 0) ∧ (∀ x, 0 < x → 0 < w x) ∧
      (∀ x, 0 < x → HasDerivAt w (1 - Ψ x / Γ (w x)) x) ∧
      ContinuousOn (fun x => 1 - Ψ x / Γ (w x)) (Ioi 0) := by
  have hadm := wLim_adm h hβ0 hβ1 hΨ
  have hcont := hadm.rhs_continuousOn h hβ0
  refine ⟨wLim Ψ Γ, hadm.zero, hadm.continuousOn hβ0.le, fun x hx => hadm.pos hβ0 hx,
    fun x hx => ?_, hcont⟩
  have hd : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, rhs Ψ Γ t (wLim Ψ Γ t))
      (rhs Ψ Γ x (wLim Ψ Γ x)) x :=
    intervalIntegral.integral_hasDerivAt_right (hadm.intervalIntegrable h hβ0 hΨ le_rfl hx.le)
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hcont.continuousAt (Ioi_mem_nhds hx))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with u hu
  exact wLim_eq h hβ0 hβ1 hΨ (le_of_lt hu)

end CC.ODE.Gap
