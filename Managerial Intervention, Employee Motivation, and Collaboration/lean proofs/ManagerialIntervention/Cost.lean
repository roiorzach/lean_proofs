import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Effort costs and the best-response map

The paper assumes `c(0) = 0`, `c' ≥ 0` with `c'(0) = 0`, and `c'' > 0`, and that `c(1)` is
large enough for the optimal effort to be a probability.  We model a cost as a function
`c : ℝ → ℝ` with derivative `d = c'` everywhere, `c 0 = 0`, `d 0 = 0`, and `d` strictly
increasing on `[0,1]` (which is what `c'' > 0` is used for).  Efforts are probabilities, so
every effort choice is made on `[0,1]`.

`br m` is the unique maximiser of `e ↦ e * m - c e` on `[0,1]`.  On `[0, c'(1)]` it is the
inverse `h = (c')⁻¹` of the marginal cost used in Proposition 3 of the paper
(`Cost.br_d`, `Cost.d_br`); for `m ≤ 0` it is `0` (`Cost.br_eq_zero_of_nonpos`), which is the
`max{0, ·}` appearing in the paper's first-order conditions.
-/

namespace MI

open Set Filter Topology

/-- A cost-of-effort function together with its derivative. -/
structure Cost where
  /-- the cost function `c` -/
  c : ℝ → ℝ
  /-- its derivative `c'` -/
  d : ℝ → ℝ
  hasDerivAt : ∀ x, HasDerivAt c (d x) x
  c_zero : c 0 = 0
  d_zero : d 0 = 0
  d_strictMonoOn : StrictMonoOn d (Icc 0 1)

/-- `e` maximises `f` over the effort levels `[0,1]`. -/
def IsBR (f : ℝ → ℝ) (e : ℝ) : Prop :=
  e ∈ Icc (0 : ℝ) 1 ∧ ∀ e' ∈ Icc (0 : ℝ) 1, f e' ≤ f e

lemma isBR_congr {f g : ℝ → ℝ} (h : ∀ x y, f x ≤ f y ↔ g x ≤ g y) {e : ℝ} :
    IsBR f e ↔ IsBR g e := by
  constructor
  · rintro ⟨he, hmax⟩; exact ⟨he, fun e' he' => (h e' e).1 (hmax e' he')⟩
  · rintro ⟨he, hmax⟩; exact ⟨he, fun e' he' => (h e' e).2 (hmax e' he')⟩

namespace Cost

variable (κ : Cost)

/-- The best response to a marginal benefit `m`: the maximiser of `e * m - c e` on `[0,1]`. -/
noncomputable def br (m : ℝ) : ℝ := sSup {e | e ∈ Icc (0 : ℝ) 1 ∧ κ.d e ≤ m}

/-- The value `max_{e ∈ [0,1]} e * m - c e`. -/
noncomputable def val (m : ℝ) : ℝ := κ.br m * m - κ.c (κ.br m)

lemma brSet_bdd (m : ℝ) : BddAbove {e | e ∈ Icc (0 : ℝ) 1 ∧ κ.d e ≤ m} :=
  ⟨1, fun _ he => he.1.2⟩

lemma br_mem (m : ℝ) : κ.br m ∈ Icc (0 : ℝ) 1 := by
  unfold br
  rcases Set.eq_empty_or_nonempty {e | e ∈ Icc (0 : ℝ) 1 ∧ κ.d e ≤ m} with h | h
  · rw [h, Real.sSup_empty]; exact ⟨le_rfl, zero_le_one⟩
  · obtain ⟨e, he⟩ := h
    exact ⟨le_trans he.1.1 (le_csSup (κ.brSet_bdd m) he), csSup_le ⟨e, he⟩ fun x hx => hx.1.2⟩

lemma br_nonneg (m : ℝ) : 0 ≤ κ.br m := (κ.br_mem m).1

lemma br_le_one (m : ℝ) : κ.br m ≤ 1 := (κ.br_mem m).2

lemma d_lt_of_lt_br {m e : ℝ} (he : e ∈ Icc (0 : ℝ) 1) (hlt : e < κ.br m) : κ.d e < m := by
  unfold br at hlt
  rcases Set.eq_empty_or_nonempty {e | e ∈ Icc (0 : ℝ) 1 ∧ κ.d e ≤ m} with h | h
  · rw [h, Real.sSup_empty] at hlt; linarith [he.1]
  · obtain ⟨s, hs, hes⟩ := exists_lt_of_lt_csSup h hlt
    exact lt_of_lt_of_le (κ.d_strictMonoOn he hs.1 hes) hs.2

lemma lt_d_of_br_lt {m e : ℝ} (he : e ∈ Icc (0 : ℝ) 1) (hlt : κ.br m < e) : m < κ.d e := by
  by_contra hcon
  push Not at hcon
  have : e ≤ κ.br m := le_csSup (κ.brSet_bdd m) ⟨he, hcon⟩
  linarith

lemma continuous_c : Continuous κ.c :=
  continuous_iff_continuousAt.2 fun x => (κ.hasDerivAt x).continuousAt

lemma hasDerivAt_obj (m x : ℝ) : HasDerivAt (fun e => e * m - κ.c e) (m - κ.d x) x := by
  have h1 : HasDerivAt (fun e : ℝ => e * m) m x := by
    simpa using (hasDerivAt_id x).mul_const m
  exact h1.sub (κ.hasDerivAt x)

/-- Any effort other than `br m` does strictly worse. -/
lemma obj_lt_of_ne {m e : ℝ} (he : e ∈ Icc (0 : ℝ) 1) (hne : e ≠ κ.br m) :
    e * m - κ.c e < κ.br m * m - κ.c (κ.br m) := by
  have hb := κ.br_mem m
  have hcont : Continuous (fun e => e * m - κ.c e) :=
    (continuous_id.mul continuous_const).sub κ.continuous_c
  rcases lt_or_gt_of_ne hne with h | h
  · have hmono : StrictMonoOn (fun e => e * m - κ.c e) (Icc 0 (κ.br m)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 _) hcont.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      rw [(κ.hasDerivAt_obj m x).deriv]
      have : κ.d x < m := κ.d_lt_of_lt_br ⟨hx.1.le, hx.2.le.trans hb.2⟩ hx.2
      linarith
    exact hmono ⟨he.1, h.le⟩ ⟨hb.1, le_rfl⟩ h
  · have hanti : StrictAntiOn (fun e => e * m - κ.c e) (Icc (κ.br m) 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ 1) hcont.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      rw [(κ.hasDerivAt_obj m x).deriv]
      have : m < κ.d x := κ.lt_d_of_br_lt ⟨hb.1.trans hx.1.le, hx.2.le⟩ hx.1
      linarith
    exact hanti ⟨le_rfl, hb.2⟩ ⟨h.le, he.2⟩ h

/-- **The effort problem.** `br m` is the unique maximiser of `e * m - c e` on `[0,1]`. -/
theorem isBR_iff {m e : ℝ} : IsBR (fun e => e * m - κ.c e) e ↔ e = κ.br m := by
  constructor
  · rintro ⟨he, hmax⟩
    by_contra hne
    have h1 := κ.obj_lt_of_ne he hne
    have h2 := hmax _ (κ.br_mem m)
    simp only at h2
    linarith
  · rintro rfl
    refine ⟨κ.br_mem m, fun e' he' => ?_⟩
    by_cases h : e' = κ.br m
    · rw [h]
    · exact (κ.obj_lt_of_ne he' h).le

/-- Same, for an objective `K + s * (e * m - c e)` with `s > 0`. -/
theorem isBR_affine_iff {K s m e : ℝ} (hs : 0 < s) :
    IsBR (fun e => K + s * (e * m - κ.c e)) e ↔ e = κ.br m := by
  rw [← κ.isBR_iff]
  apply isBR_congr
  intro x y
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma le_val {m e : ℝ} (he : e ∈ Icc (0 : ℝ) 1) : e * m - κ.c e ≤ κ.val m := by
  by_cases h : e = κ.br m
  · subst h; exact le_rfl
  · exact (κ.obj_lt_of_ne he h).le

lemma br_eq_zero_of_nonpos {m : ℝ} (hm : m ≤ 0) : κ.br m = 0 := by
  by_contra h
  have hpos : 0 < κ.br m := lt_of_le_of_ne (κ.br_nonneg m) (Ne.symm h)
  have := κ.d_lt_of_lt_br ⟨le_rfl, zero_le_one⟩ hpos
  rw [κ.d_zero] at this
  linarith

lemma br_mono : Monotone κ.br := by
  intro m m' hmm'
  show sSup _ ≤ sSup _
  rcases Set.eq_empty_or_nonempty {e | e ∈ Icc (0 : ℝ) 1 ∧ κ.d e ≤ m} with h | h
  · rw [h, Real.sSup_empty]; exact κ.br_nonneg m'
  · exact csSup_le_csSup (κ.brSet_bdd m') h fun e he => ⟨he.1, he.2.trans hmm'⟩

/-- `h(c'(e)) = e`: `br` is a left inverse of `c'` on `[0,1]`. -/
lemma br_d {e : ℝ} (he : e ∈ Icc (0 : ℝ) 1) : κ.br (κ.d e) = e := by
  rcases lt_trichotomy (κ.br (κ.d e)) e with h | h | h
  · exact absurd (κ.lt_d_of_br_lt he h) (lt_irrefl _)
  · exact h
  · exact absurd (κ.d_lt_of_lt_br he h) (lt_irrefl _)

lemma d_one_pos : 0 < κ.d 1 := by
  have := κ.d_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  rwa [κ.d_zero] at this

lemma d_nonneg {e : ℝ} (he : e ∈ Icc (0 : ℝ) 1) : 0 ≤ κ.d e := by
  rcases he.1.eq_or_lt with h | h
  · rw [← h, κ.d_zero]
  · have := κ.d_strictMonoOn ⟨le_rfl, zero_le_one⟩ he h
    rw [κ.d_zero] at this; exact this.le

/-- Darboux: `c'` maps `[0,1]` onto `[0, c'(1)]`. -/
lemma exists_d_eq {m : ℝ} (hm : m ∈ Icc 0 (κ.d 1)) : ∃ e ∈ Icc (0 : ℝ) 1, κ.d e = m := by
  obtain ⟨e, he, hde⟩ := exists_hasDerivWithinAt_eq_of_ge_of_le (f := κ.c) (f' := κ.d)
    zero_le_one (fun x _ => (κ.hasDerivAt x).hasDerivWithinAt)
    (by rw [κ.d_zero]; exact hm.1) hm.2
  exact ⟨e, he, hde⟩

/-- `c'(h(m)) = m` on `[0, c'(1)]`: `br` is the inverse `h = (c')⁻¹` there. -/
lemma d_br {m : ℝ} (hm : m ∈ Icc 0 (κ.d 1)) : κ.d (κ.br m) = m := by
  obtain ⟨e, he, rfl⟩ := κ.exists_d_eq hm
  rw [κ.br_d he]

lemma br_pos {m : ℝ} (hm : 0 < m) : 0 < κ.br m := by
  have hd1 := κ.d_one_pos
  have hm' : min m (κ.d 1) ∈ Icc 0 (κ.d 1) := ⟨le_min hm.le hd1.le, min_le_right _ _⟩
  have h1 : κ.br (min m (κ.d 1)) ≤ κ.br m := κ.br_mono (min_le_left _ _)
  have h2 : κ.d (κ.br (min m (κ.d 1))) = min m (κ.d 1) := κ.d_br hm'
  have h3 : κ.br (min m (κ.d 1)) ≠ 0 := by
    intro h; rw [h, κ.d_zero] at h2; have := lt_min hm hd1; linarith
  exact lt_of_lt_of_le (lt_of_le_of_ne (κ.br_nonneg _) (Ne.symm h3)) h1

lemma br_strictMonoOn : StrictMonoOn κ.br (Icc 0 (κ.d 1)) := by
  intro m hm m' hm' hlt
  rcases (κ.br_mono hlt.le).lt_or_eq with h | h
  · exact h
  · have := κ.d_br hm; rw [h, κ.d_br hm'] at this; linarith

lemma br_continuous : Continuous κ.br := by
  rw [continuous_iff_continuousAt]
  intro m0
  rw [ContinuousAt, tendsto_order]
  have hb0 := κ.br_mem m0
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · by_cases ha0 : a < 0
    · exact Filter.Eventually.of_forall fun m => lt_of_lt_of_le ha0 (κ.br_nonneg m)
    · push Not at ha0
      have he : (a + κ.br m0) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hb0.2]⟩
      have hde : κ.d ((a + κ.br m0) / 2) < m0 := κ.d_lt_of_lt_br he (by linarith)
      filter_upwards [Ioi_mem_nhds hde] with m hm
      have : (a + κ.br m0) / 2 ≤ κ.br m := le_csSup (κ.brSet_bdd m) ⟨he, le_of_lt hm⟩
      linarith
  · by_cases hb1 : 1 < b
    · exact Filter.Eventually.of_forall fun m => lt_of_le_of_lt (κ.br_le_one m) hb1
    · push Not at hb1
      have he : (κ.br m0 + b) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hb0.1], by linarith⟩
      have hde : m0 < κ.d ((κ.br m0 + b) / 2) := κ.lt_d_of_br_lt he (by linarith)
      filter_upwards [Iio_mem_nhds hde] with m hm
      have hm' : m < κ.d ((κ.br m0 + b) / 2) := hm
      by_contra hcon
      push Not at hcon
      have := κ.d_lt_of_lt_br he (lt_of_lt_of_le (by linarith : (κ.br m0 + b) / 2 < b) hcon)
      linarith

lemma c_strictMonoOn : StrictMonoOn κ.c (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) κ.continuous_c.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(κ.hasDerivAt x).deriv]
  have := κ.d_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
  rwa [κ.d_zero] at this

lemma c_pos {e : ℝ} (he : e ∈ Ioc (0 : ℝ) 1) : 0 < κ.c e := by
  have := κ.c_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨he.1.le, he.2⟩ he.1
  rwa [κ.c_zero] at this

lemma c_nonneg {e : ℝ} (he : e ∈ Icc (0 : ℝ) 1) : 0 ≤ κ.c e := by
  rcases he.1.eq_or_lt with h | h
  · rw [← h, κ.c_zero]
  · exact (κ.c_pos ⟨h, he.2⟩).le

/-! ### The value function -/

lemma val_nonneg (m : ℝ) : 0 ≤ κ.val m := by
  have := κ.le_val (m := m) (e := 0) ⟨le_rfl, zero_le_one⟩
  simpa [κ.c_zero] using this

lemma val_mono : Monotone κ.val := by
  intro m m' h
  have h1 := κ.le_val (m := m') (κ.br_mem m)
  have hb := κ.br_nonneg m
  have : κ.br m * m ≤ κ.br m * m' := mul_le_mul_of_nonneg_left h hb
  unfold val at *
  linarith

lemma val_eq_zero_of_nonpos {m : ℝ} (hm : m ≤ 0) : κ.val m = 0 := by
  simp [val, κ.br_eq_zero_of_nonpos hm, κ.c_zero]

lemma val_pos {m : ℝ} (hm : 0 < m) : 0 < κ.val m := by
  have hne : (0 : ℝ) ≠ κ.br m := (κ.br_pos hm).ne
  have := κ.obj_lt_of_ne (m := m) ⟨le_rfl, zero_le_one⟩ hne
  simpa [κ.c_zero, val] using this

lemma val_strict {m m' : ℝ} (h : m' < m) (hm : 0 < m) : κ.val m' < κ.val m := by
  by_cases hm' : m' ≤ 0
  · rw [κ.val_eq_zero_of_nonpos hm']; exact κ.val_pos hm
  · push Not at hm'
    have hb := κ.br_pos hm'
    have h1 := κ.le_val (m := m) (κ.br_mem m')
    have : κ.br m' * m' < κ.br m' * m := mul_lt_mul_of_pos_left h hb
    unfold val at *
    linarith

lemma val_continuous : Continuous κ.val :=
  (κ.br_continuous.mul continuous_id).sub (κ.continuous_c.comp κ.br_continuous)

/-! ### Quadratic costs -/

/-- The quadratic cost `c(e) = k e² / 2`, with `c'(e) = k e`. -/
noncomputable def quad (k : ℝ) (hk : 0 < k) : Cost where
  c e := k * e ^ 2 / 2
  d e := k * e
  hasDerivAt x := by
    have := ((hasDerivAt_pow 2 x).const_mul k).div_const 2
    convert this using 1
    push_cast
    ring
  c_zero := by simp
  d_zero := by simp
  d_strictMonoOn := fun x _ y _ h => by
    show k * x < k * y
    exact mul_lt_mul_of_pos_left h hk

lemma quad_br {k : ℝ} (hk : 0 < k) {m : ℝ} (hm : m ∈ Icc 0 k) : (quad k hk).br m = m / k := by
  have he : m / k ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hm.1 hk.le, (div_le_one hk).2 hm.2⟩
  have := (quad k hk).br_d he
  have hd : (quad k hk).d (m / k) = m := by
    show k * (m / k) = m
    field_simp
  rwa [hd] at this

lemma quad_d_one {k : ℝ} (hk : 0 < k) : (quad k hk).d 1 = k := by
  show k * 1 = k; ring

end Cost

end MI
