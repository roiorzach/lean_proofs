import ConformityConcerns.PeriodGame.Dichotomy

/-!
# Lemma 1, the signaling equilibrium, and Corollary 1 (assuming `Z` measurable)

The ex-ante loss of every linear equilibrium is at least `m(s̃) Var Z + κ Var v`, where
`m(s̃) = ((1 - √(1 - 4 κ s̃²))/2)²` if `κ s̃² ≤ κck` and `m(s̃) = 1` otherwise; the bound is
attained by the revealing rule with the larger root `λ₊ = (1 + √(1 - 4 κ s̃²))/2`, resp. by
pooling on `E Z`. Social Optimality therefore pins down the signaling equilibrium.
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The quadratic -/

lemma abs_le_sqrt_iff_four {κ s : ℝ} (hκ : 0 < κ) : |s| ≤ √(κck / κ) ↔ 4 * κ * s ^ 2 ≤ 1 := by
  rw [Real.le_sqrt (abs_nonneg _) (by unfold κck; positivity), sq_abs, le_div_iff₀ hκ, κck]
  constructor <;> intro h <;> nlinarith

lemma le_kck_iff_four {κ s : ℝ} : κ * s ^ 2 ≤ κck ↔ 4 * κ * s ^ 2 ≤ 1 := by
  rw [κck]
  constructor <;> intro h <;> linarith

theorem slope_root_iff_four (κ s : ℝ) :
    (∃ α : ℝ, (1 + κ * α ^ 2) * s = α) ↔ 4 * κ * s ^ 2 ≤ 1 := by
  constructor
  · rintro ⟨α, h⟩
    have e : (2 * κ * s * α - 1) ^ 2 = 1 - 4 * κ * s ^ 2 := by linear_combination (4 * κ * s) * h
    nlinarith [sq_nonneg (2 * κ * s * α - 1)]
  · intro h
    by_cases hs : s = 0
    · exact ⟨0, by simp [hs]⟩
    · by_cases hκ : κ = 0
      · exact ⟨s, by simp [hκ]⟩
      set r := √(1 - 4 * κ * s ^ 2) with hr
      have hr2 : r ^ 2 = 1 - 4 * κ * s ^ 2 := Real.sq_sqrt (by linarith)
      refine ⟨(1 - r) / (2 * κ * s), ?_⟩
      field_simp
      linear_combination hr2

/-- The two slopes: `λ` solves `λ² - λ + κ s² = 0` with `λ > 0` iff `α = s/λ` solves
`(1 + κ α²) s = α`. -/
lemma root_of_slope {κ s l : ℝ} (hl : 0 < l) (h : l ^ 2 - l + κ * s ^ 2 = 0) :
    ∃ α : ℝ, (1 + κ * α ^ 2) * s = α := by
  refine ⟨s / l, ?_⟩
  field_simp
  linear_combination s * h

/-- The larger root `λ₊ = (1 + √(1 - 4 κ s²))/2`. -/
noncomputable def lplus (κ s : ℝ) : ℝ := (1 + √(1 - 4 * κ * s ^ 2)) / 2

lemma lplus_pos (κ s : ℝ) : 0 < lplus κ s := by
  unfold lplus
  positivity

lemma lplus_root {κ s : ℝ} (h : 4 * κ * s ^ 2 ≤ 1) : lplus κ s ^ 2 - lplus κ s + κ * s ^ 2 = 0 := by
  unfold lplus
  have hr2 : √(1 - 4 * κ * s ^ 2) ^ 2 = 1 - 4 * κ * s ^ 2 := Real.sq_sqrt (by linarith)
  linear_combination hr2 / 4

lemma one_sub_lplus (κ s : ℝ) : 1 - lplus κ s = (1 - √(1 - 4 * κ * s ^ 2)) / 2 := by
  unfold lplus
  ring

/-- Among the roots, `λ₊` minimises `(1 - λ)²`, uniquely. -/
lemma lplus_best {κ s l : ℝ} (h : l ^ 2 - l + κ * s ^ 2 = 0) :
    (1 - lplus κ s) ^ 2 ≤ (1 - l) ^ 2 ∧ ((1 - l) ^ 2 ≤ (1 - lplus κ s) ^ 2 → l = lplus κ s) := by
  have e : 1 - 4 * κ * s ^ 2 = (2 * l - 1) ^ 2 := by linear_combination (-4) * h
  have hr : √(1 - 4 * κ * s ^ 2) = |2 * l - 1| := by rw [e, Real.sqrt_sq_eq_abs]
  rw [one_sub_lplus, hr]
  have h1 := le_abs_self (2 * l - 1)
  have h2 : (2 * l - 1) ^ 2 = |2 * l - 1| ^ 2 := (sq_abs _).symm
  constructor
  · nlinarith
  · intro h3
    have : |2 * l - 1| = 2 * l - 1 := by nlinarith
    unfold lplus
    rw [hr, this]
    ring

lemma lplus_sq_le {κ s : ℝ} (hκ : 0 ≤ κ) (_h : 4 * κ * s ^ 2 ≤ 1) :
    (1 - lplus κ s) ^ 2 ≤ 1 / 4 := by
  rw [one_sub_lplus]
  have h0 : 0 ≤ √(1 - 4 * κ * s ^ 2) := Real.sqrt_nonneg _
  have h1 : √(1 - 4 * κ * s ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith [mul_nonneg hκ (sq_nonneg s)]
  nlinarith

/-- The minimal adaptation coefficient `m(s̃)`. -/
noncomputable def minCoef (κ s : ℝ) : ℝ :=
  if κ * s ^ 2 ≤ κck then ((1 - √(1 - 4 * κ * s ^ 2)) / 2) ^ 2 else 1

lemma minCoef_le_one {κ : ℝ} (hκ : 0 ≤ κ) (s : ℝ) : minCoef κ s ≤ 1 := by
  unfold minCoef
  split_ifs with h
  · rw [← one_sub_lplus]
    have := lplus_sq_le hκ (le_kck_iff_four.1 h)
    linarith
  · exact le_rfl

lemma minCoef_nonneg (κ s : ℝ) : 0 ≤ minCoef κ s := by
  unfold minCoef
  split_ifs <;> positivity

namespace Game

variable {G : Game Ω}

lemma not_revealing_and_pooling (hG : G.Std) {a : Ω → ℝ} (hr : G.IsRevealing a)
    (hp : G.IsPooling a) : False := by
  have := hG.prob
  obtain ⟨k, b, hk, hkb⟩ := hr
  obtain ⟨c, hc⟩ := hp
  have hZ : G.Z =ᵐ[G.P] fun _ => (c - b) / k := by
    filter_upwards [hkb, hc] with ω h1 h2
    rw [h2] at h1
    field_simp
    linarith
  have h0 : variance G.Z G.P = 0 := by
    rw [variance_congr hZ, variance_eq_integral aemeasurable_const]
    simp
  exact hG.varZ_ne h0

section Std

variable (hG : G.Std)
include hG

omit hG in
lemma Std.K_ne_top : ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P) ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

omit hG in
lemma Std.cmp {A B : ℝ} (hB : 0 ≤ B)
    (h : ENNReal.ofReal A + ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P) ≤
      ENNReal.ofReal B + ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P)) : A ≤ B :=
  (ENNReal.ofReal_le_ofReal_iff hB).1 (ENNReal.le_of_add_le_add_right Std.K_ne_top h)

/-- **Lower bound.** Every linear equilibrium has ex-ante loss at least
`m(s̃) Var Z + κ Var v`. -/
lemma Std.lower_bound {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsLinearEq a φ) :
    ENNReal.ofReal (minCoef G.κ G.sens * variance G.Z G.P) +
        ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P) ≤ G.exLoss a φ := by
  have hV := hG.varZ_pos
  by_cases hs : G.sens = 0
  · have hm : minCoef G.κ G.sens = 0 := by
      unfold minCoef
      rw [hs, ite_eq_left (by simp [κck_pos.le])]
      simp
    rw [hm, zero_mul, ENNReal.ofReal_zero, zero_add, hG.exLoss_eq hE.1]
    exact le_add_self
  rcases hG.lemma3_ne hs hE with ⟨c, hc⟩ | ⟨l, hl⟩
  · rw [hG.exLoss_pool c hE.1 hc]
    gcongr
    have := minCoef_le_one hG.κ_pos.le G.sens
    nlinarith [sq_nonneg (c - G.meanZ)]
  · rw [hG.exLoss_affine hE.1 hl.2.2.1]
    gcongr
    have h4 := (slope_root_iff_four _ _).1 (root_of_slope hl.1 hl.2.1)
    have hm : minCoef G.κ G.sens = (1 - lplus G.κ G.sens) ^ 2 := by
      unfold minCoef
      rw [ite_eq_left (le_kck_iff_four.2 h4), one_sub_lplus]
    rw [hm]
    exact (lplus_best hl.2.1).1

/-- **The bound is attained** (requires `Z` measurable when a revealing rule is needed). -/
lemma Std.attained (hZ : Measurable G.Z) : ∃ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsLinearEq a φ ∧
    G.exLoss a φ = ENNReal.ofReal (minCoef G.κ G.sens * variance G.Z G.P) +
        ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P) := by
  by_cases h : G.κ * G.sens ^ 2 ≤ κck
  · have h4 := le_kck_iff_four.1 h
    have hE := hG.rev_isLinearEq hZ (lplus_pos G.κ G.sens) (lplus_root h4)
    refine ⟨_, _, hE, ?_⟩
    rw [hG.exLoss_affine hE.1 (ae_of_all _ fun _ => rfl)]
    unfold minCoef
    rw [ite_eq_left h, one_sub_lplus]
  · have hE := hG.pool_isLinearEq G.meanZ
    refine ⟨_, _, hE, ?_⟩
    rw [hG.exLoss_pool G.meanZ hE.1 (ae_of_all _ fun _ => rfl)]
    unfold minCoef
    rw [ite_eq_right h]
    simp

/-- **Classification of signaling equilibria** (assuming `Z` measurable). -/
theorem Std.signaling_cases (hZ : Measurable G.Z) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsSignalingEq a φ) :
    (G.κ * G.sens ^ 2 ≤ κck ∧ G.RevealingWith a φ (lplus G.κ G.sens)) ∨
      (κck < G.κ * G.sens ^ 2 ∧ a =ᵐ[G.P] fun _ => G.meanZ) := by
  have hV := hG.varZ_pos
  obtain ⟨a₀, φ₀, hE₀, hloss₀⟩ := hG.attained hZ
  have hbound := hE.2 a₀ φ₀ hE₀
  rw [hloss₀] at hbound
  rcases hG.lemma3_strong hZ hE.1 (fun _ => hE) with ⟨c, hc⟩ | ⟨l, hl⟩
  · rw [hG.exLoss_pool c hE.1.1 hc] at hbound
    have hle := Std.cmp (mul_nonneg (minCoef_nonneg _ _) hV.le) hbound
    by_cases h : G.κ * G.sens ^ 2 ≤ κck
    · exfalso
      have hm : minCoef G.κ G.sens ≤ 1 / 4 := by
        unfold minCoef
        rw [ite_eq_left h, ← one_sub_lplus]
        exact lplus_sq_le hG.κ_pos.le (le_kck_iff_four.1 h)
      nlinarith [sq_nonneg (c - G.meanZ)]
    · right
      refine ⟨lt_of_not_ge h, ?_⟩
      have hm : minCoef G.κ G.sens = 1 := by unfold minCoef; rw [ite_eq_right h]
      rw [hm, one_mul] at hle
      have : (c - G.meanZ) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
      have : c = G.meanZ := by nlinarith [sq_nonneg (c - G.meanZ)]
      rw [← this]
      exact hc
  · have h4 := (slope_root_iff_four _ _).1 (root_of_slope hl.1 hl.2.1)
    have h := le_kck_iff_four.2 h4
    left
    refine ⟨h, ?_⟩
    rw [hG.exLoss_affine hE.1.1 hl.2.2.1] at hbound
    have hm : minCoef G.κ G.sens = (1 - lplus G.κ G.sens) ^ 2 := by
      unfold minCoef
      rw [ite_eq_left h, one_sub_lplus]
    rw [hm] at hbound
    have hle := Std.cmp (mul_nonneg (sq_nonneg _) hV.le) hbound
    have hle' : (1 - l) ^ 2 ≤ (1 - lplus G.κ G.sens) ^ 2 := le_of_mul_le_mul_right hle hV
    have := (lplus_best hl.2.1).2 hle'
    rw [← this]
    exact hl

omit hG in
lemma Std.revealingWith_isRevealing {a : Ω → ℝ} {φ : Kernel ℝ ℝ} {l : ℝ}
    (h : G.RevealingWith a φ l) : G.IsRevealing a :=
  ⟨l, (1 - l) * G.meanZ, h.1, h.2.2.1.mono fun ω hω => by rw [hω]; ring⟩

/-- **Lemma 1** (assuming `Z` measurable). -/
theorem Std.lemma1 (hZ : Measurable G.Z) :
    (∃ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsSignalingEq a φ) ∧
    ∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsSignalingEq a φ →
      (G.IsRevealing a ↔ ∃ α : ℝ, (1 + G.κ * α ^ 2) * G.sens = α) ∧
      (G.IsPooling a ↔ ¬ ∃ α : ℝ, (1 + G.κ * α ^ 2) * G.sens = α) := by
  refine ⟨?_, fun a φ hE => ?_⟩
  · obtain ⟨a₀, φ₀, hE₀, hloss₀⟩ := hG.attained hZ
    exact ⟨a₀, φ₀, hE₀, fun a' φ' hE' => hloss₀ ▸ hG.lower_bound hE'⟩
  rw [slope_root_iff_four, ← le_kck_iff_four]
  rcases hG.signaling_cases hZ hE with ⟨h, hr⟩ | ⟨h, hp⟩
  · have hrev := Std.revealingWith_isRevealing hr
    exact ⟨⟨fun _ => h, fun _ => hrev⟩,
      ⟨fun hp => absurd (not_revealing_and_pooling hG hrev hp) id, fun h' => absurd h h'⟩⟩
  · have hpool : G.IsPooling a := ⟨_, hp⟩
    exact ⟨⟨fun hr => absurd (not_revealing_and_pooling hG hr hpool) id,
      fun h' => absurd h' (not_le.2 h)⟩, ⟨fun _ => not_le.2 h, fun _ => hpool⟩⟩

/-- **The signaling equilibrium explicitly** (assuming `Z` measurable). -/
theorem Std.signalingEq_char (hZ : Measurable G.Z) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsSignalingEq a φ) :
    (G.κ * G.sens ^ 2 ≤ κck →
      a =ᵐ[G.P] fun ω => G.meanZ + (1 + √(1 - 4 * G.κ * G.sens ^ 2)) / 2 * (G.Z ω - G.meanZ)) ∧
    (κck < G.κ * G.sens ^ 2 → a =ᵐ[G.P] fun _ => G.meanZ) ∧
    G.exLoss a φ = ENNReal.ofReal
      ((if G.κ * G.sens ^ 2 ≤ κck then ((1 - √(1 - 4 * G.κ * G.sens ^ 2)) / 2) ^ 2 else 1) *
        variance G.Z G.P + G.κ * variance G.v G.P) := by
  have hV := hG.varZ_pos
  have hκ := hG.κ_pos
  rw [ENNReal.ofReal_add (mul_nonneg (by split_ifs <;> positivity) hV.le)
    (mul_nonneg hκ.le (variance_nonneg _ _)), ENNReal.ofReal_mul hκ.le]
  rcases hG.signaling_cases hZ hE with ⟨h, hr⟩ | ⟨h, hp⟩
  · refine ⟨fun _ => hr.2.2.1, fun h' => absurd h (not_le.2 h'), ?_⟩
    rw [hG.exLoss_affine hE.1.1 hr.2.2.1, ite_eq_left h, one_sub_lplus]
  · refine ⟨fun h' => absurd h' (not_le.2 h), fun _ => hp, ?_⟩
    rw [hG.exLoss_pool _ hE.1.1 hp, ite_eq_right (not_le.2 h)]
    simp

/-- **Corollary 1** (assuming `Z` measurable). -/
theorem Std.corollary1 (hZ : Measurable G.Z) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsSignalingEq a φ) : G.IsRevealing a ↔ |G.sens| ≤ √(κck / G.κ) := by
  rw [((hG.lemma1 hZ).2 a φ hE).1, slope_root_iff_four, abs_le_sqrt_iff_four hG.κ_pos]

end Std

end Game

end CC.LG
