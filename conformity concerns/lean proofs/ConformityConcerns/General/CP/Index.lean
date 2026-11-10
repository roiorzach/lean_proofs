import ConformityConcerns.General.PayoffContinuity

/-!
# The indifference index and the `D1^∞` survivor set

Evaluation of the extended clipped index at finite and boundary points, beliefs supported in a
singleton, and the survivor sets of monotone indices.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Setting

variable {S : Setting} {a : ℝ → ℝ} {φ : ℝ → Measure EReal}

lemma extIndex_coe (x r : ℝ) :
    S.extIndex a φ x (r : EReal) = ((S.clipped a φ x r : ℝ) : EReal) := by
  unfold Setting.extIndex
  simp

lemma extIndex_top (x : ℝ) :
    S.extIndex a φ x ⊤ = liminf (fun v : ℝ => ((S.clipped a φ x v : ℝ) : EReal)) atTop := by
  unfold Setting.extIndex
  simp

lemma extIndex_bot (x : ℝ) :
    S.extIndex a φ x ⊥ = liminf (fun v : ℝ => ((S.clipped a φ x v : ℝ) : EReal)) atBot := by
  unfold Setting.extIndex
  simp

lemma mem_survivors {x : ℝ} {z : EReal} :
    z ∈ S.survivors a φ x ↔ ∀ z', S.extIndex a φ x z ≤ S.extIndex a φ x z' := Iff.rfl

/-- A probability measure on `EReal` whose support is contained in `{b}` gives conformity loss
`ℓ̄ b`. -/
lemma lintegral_of_support_subset {ν : Measure EReal} [IsProbabilityMeasure ν] {b : EReal}
    (hs : ν.support ⊆ {b}) (f : EReal → ℝ≥0∞) : ∫⁻ z, f z ∂ν = f b := by
  have hae : ∀ᵐ z ∂ν, z = b := by
    filter_upwards [Measure.support_mem_ae (μ := ν)] with z hz
    exact hs hz
  calc ∫⁻ z, f z ∂ν = ∫⁻ _z, f b ∂ν := lintegral_congr_ae (hae.mono fun z hz => by rw [hz])
    _ = f b := by rw [lintegral_const, measure_univ, mul_one]

lemma confLoss_of_support_subset (hp : ∀ x, IsProbabilityMeasure (φ x)) {x b : ℝ}
    (hs : (φ x).support ⊆ {(b : EReal)}) : S.confLoss φ x = ENNReal.ofReal (S.ℓ b) := by
  unfold Setting.confLoss
  rw [lintegral_of_support_subset hs, ℓbar_coe]

lemma support_dirac_subset (b : EReal) : (Measure.dirac b).support ⊆ {b} := by
  apply Measure.support_subset_of_isClosed isClosed_singleton
  rw [mem_ae_iff, Measure.dirac_apply]
  simp

/-- If the clipped index is antitone, `+∞` is a survivor. -/
lemma top_mem_survivors_of_antitone {x : ℝ} (hA : Antitone (S.clipped a φ x)) :
    (⊤ : EReal) ∈ S.survivors a φ x := by
  have key : ∀ v₀ : ℝ, S.extIndex a φ x ⊤ ≤ ((S.clipped a φ x v₀ : ℝ) : EReal) := by
    intro v₀
    rw [extIndex_top]
    apply liminf_le_of_frequently_le'
    exact ((eventually_ge_atTop v₀).mono fun v hv => EReal.coe_le_coe_iff.2 (hA hv)).frequently
  intro z
  induction z using EReal.rec with
  | bot =>
    refine (key 0).trans ?_
    rw [extIndex_bot]
    exact le_liminf_of_le (by isBoundedDefault)
      ((eventually_le_atBot 0).mono fun v hv => EReal.coe_le_coe_iff.2 (hA hv))
  | coe r => rw [extIndex_coe]; exact key r
  | top => exact le_rfl

/-- If the clipped index is monotone, `-∞` is a survivor. -/
lemma bot_mem_survivors_of_monotone {x : ℝ} (hM : Monotone (S.clipped a φ x)) :
    (⊥ : EReal) ∈ S.survivors a φ x := by
  have key : ∀ v₀ : ℝ, S.extIndex a φ x ⊥ ≤ ((S.clipped a φ x v₀ : ℝ) : EReal) := by
    intro v₀
    rw [extIndex_bot]
    apply liminf_le_of_frequently_le'
    exact ((eventually_le_atBot v₀).mono fun v hv => EReal.coe_le_coe_iff.2 (hM hv)).frequently
  intro z
  induction z using EReal.rec with
  | bot => exact le_rfl
  | coe r => rw [extIndex_coe]; exact key r
  | top =>
    refine (key 0).trans ?_
    rw [extIndex_top]
    exact le_liminf_of_le (by isBoundedDefault)
      ((eventually_ge_atTop 0).mono fun v hv => EReal.coe_le_coe_iff.2 (hM hv))

/-- If the index is strictly decreasing and negative somewhere, then `S^∞(x) = {+∞}`. -/
lemma survivors_eq_top {x : ℝ} (hA : StrictAnti (S.indiff a φ x))
    (hneg : ∃ v₀, S.indiff a φ x v₀ < 0) : S.survivors a φ x = {(⊤ : EReal)} := by
  have hJ : Antitone (S.clipped a φ x) := fun _ _ h => min_le_min_right 0 (hA.antitone h)
  refine Subset.antisymm (fun z hz => ?_)
    (singleton_subset_iff.2 (top_mem_survivors_of_antitone hJ))
  obtain ⟨v₀, hv₀⟩ := hneg
  have key : ∀ v, S.extIndex a φ x ⊤ ≤ ((S.clipped a φ x v : ℝ) : EReal) := fun v =>
    (show (⊤ : EReal) ∈ S.survivors a φ x from top_mem_survivors_of_antitone hJ) (v : EReal)
      |>.trans_eq (extIndex_coe x v)
  -- past `v₀`, the clipped index is strictly decreasing
  have hstrict : ∀ w, v₀ ≤ w → S.clipped a φ x (w + 1) < S.clipped a φ x w := fun w hw => by
    have h1 : S.indiff a φ x w < 0 := lt_of_le_of_lt (hA.antitone hw) hv₀
    have h2 : S.indiff a φ x (w + 1) < S.indiff a φ x w := hA (lt_add_one w)
    unfold Setting.clipped
    rw [min_eq_left h1.le, min_eq_left (h2.trans h1).le]
    exact h2
  rw [mem_singleton_iff]
  by_contra hne
  have hz' := hz ⊤
  induction z using EReal.rec with
  | bot =>
    rw [extIndex_bot] at hz'
    have h1 : ((S.clipped a φ x v₀ : ℝ) : EReal) ≤
        liminf (fun v : ℝ => ((S.clipped a φ x v : ℝ) : EReal)) atBot :=
      le_liminf_of_le (by isBoundedDefault)
        ((eventually_le_atBot v₀).mono fun v hv => EReal.coe_le_coe_iff.2 (hJ hv))
    have h2 := EReal.coe_lt_coe_iff.2 (hstrict v₀ le_rfl)
    exact absurd ((h1.trans hz').trans (key (v₀ + 1))) (not_le.2 h2)
  | coe r =>
    rw [extIndex_coe] at hz'
    have hw : v₀ ≤ max v₀ r := le_max_left _ _
    have h1 : S.clipped a φ x (max v₀ r) ≤ S.clipped a φ x r := hJ (le_max_right _ _)
    have h2 := EReal.coe_lt_coe_iff.2 (hstrict _ hw)
    have h3 := hz'.trans (key (max v₀ r + 1))
    exact absurd (h3.trans_lt h2) (not_lt.2 (EReal.coe_le_coe_iff.2 h1))
  | top => exact hne rfl

/-- If the index is strictly increasing and negative somewhere, then `S^∞(x) = {-∞}`. -/
lemma survivors_eq_bot {x : ℝ} (hM : StrictMono (S.indiff a φ x))
    (hneg : ∃ v₀, S.indiff a φ x v₀ < 0) : S.survivors a φ x = {(⊥ : EReal)} := by
  have hJ : Monotone (S.clipped a φ x) := fun _ _ h => min_le_min_right 0 (hM.monotone h)
  refine Subset.antisymm (fun z hz => ?_)
    (singleton_subset_iff.2 (bot_mem_survivors_of_monotone hJ))
  obtain ⟨v₀, hv₀⟩ := hneg
  have key : ∀ v, S.extIndex a φ x ⊥ ≤ ((S.clipped a φ x v : ℝ) : EReal) := fun v =>
    (show (⊥ : EReal) ∈ S.survivors a φ x from bot_mem_survivors_of_monotone hJ) (v : EReal)
      |>.trans_eq (extIndex_coe x v)
  have hstrict : ∀ w, w ≤ v₀ → S.clipped a φ x (w - 1) < S.clipped a φ x w := fun w hw => by
    have h1 : S.indiff a φ x w < 0 := lt_of_le_of_lt (hM.monotone hw) hv₀
    have h2 : S.indiff a φ x (w - 1) < S.indiff a φ x w := hM (sub_one_lt w)
    unfold Setting.clipped
    rw [min_eq_left h1.le, min_eq_left (h2.trans h1).le]
    exact h2
  rw [mem_singleton_iff]
  by_contra hne
  have hz' := hz ⊥
  induction z using EReal.rec with
  | bot => exact hne rfl
  | coe r =>
    rw [extIndex_coe] at hz'
    have hw : min v₀ r ≤ v₀ := min_le_left _ _
    have h1 : S.clipped a φ x (min v₀ r) ≤ S.clipped a φ x r := hJ (min_le_right _ _)
    have h2 := EReal.coe_lt_coe_iff.2 (hstrict _ hw)
    have h3 := hz'.trans (key (min v₀ r - 1))
    exact absurd (h3.trans_lt h2) (not_lt.2 (EReal.coe_le_coe_iff.2 h1))
  | top =>
    rw [extIndex_top] at hz'
    have h1 : ((S.clipped a φ x v₀ : ℝ) : EReal) ≤
        liminf (fun v : ℝ => ((S.clipped a φ x v : ℝ) : EReal)) atTop :=
      le_liminf_of_le (by isBoundedDefault)
        ((eventually_ge_atTop v₀).mono fun v hv => EReal.coe_le_coe_iff.2 (hJ hv))
    have h2 := EReal.coe_lt_coe_iff.2 (hstrict v₀ le_rfl)
    exact absurd ((h1.trans hz').trans (key (v₀ - 1))) (not_le.2 h2)

/-- Strict minimum of the index at a finite type `hb` (with uniform margins at `±∞`) makes `hb`
the only possible survivor. -/
lemma survivors_subset_singleton {x hb : ℝ} (hneg : S.indiff a φ x hb < 0)
    (hlt : ∀ v, v ≠ hb → S.indiff a φ x hb < S.indiff a φ x v)
    (htop : ∃ b, S.indiff a φ x hb < b ∧ ∀ᶠ v in atTop, b ≤ S.indiff a φ x v)
    (hbot : ∃ b, S.indiff a φ x hb < b ∧ ∀ᶠ v in atBot, b ≤ S.indiff a φ x v) :
    S.survivors a φ x ⊆ {(hb : EReal)} := by
  intro z hz
  have hz' := hz (hb : EReal)
  rw [extIndex_coe] at hz'
  have hcl : S.clipped a φ x hb = S.indiff a φ x hb := min_eq_left hneg.le
  rw [hcl] at hz'
  rw [mem_singleton_iff]
  by_contra hne
  have tail : ∀ (l : Filter ℝ) [l.NeBot], (∃ b, S.indiff a φ x hb < b ∧
      ∀ᶠ v in l, b ≤ S.indiff a φ x v) →
      ((S.indiff a φ x hb : ℝ) : EReal) < liminf (fun v : ℝ => ((S.clipped a φ x v : ℝ) : EReal)) l := by
    intro l _ ⟨b, hb1, hb2⟩
    have h1 : ((S.indiff a φ x hb : ℝ) : EReal) < ((min b 0 : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.2 (lt_min hb1 hneg)
    exact lt_of_lt_of_le h1 (le_liminf_of_le (by isBoundedDefault)
      (hb2.mono fun v hv => EReal.coe_le_coe_iff.2 (min_le_min_right 0 hv)))
  induction z using EReal.rec with
  | bot =>
    rw [extIndex_bot] at hz'
    exact absurd hz' (not_le.2 (tail atBot hbot))
  | coe r =>
    rw [extIndex_coe] at hz'
    have hr : r ≠ hb := fun h => hne (by rw [h])
    have : S.indiff a φ x hb < S.clipped a φ x r := lt_min (hlt r hr) hneg
    exact absurd (EReal.coe_le_coe_iff.1 hz') (not_le.2 this)
  | top =>
    rw [extIndex_top] at hz'
    exact absurd hz' (not_le.2 (tail atTop htop))

end Setting

end CC.General
