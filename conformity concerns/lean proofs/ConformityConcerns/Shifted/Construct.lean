import ConformityConcerns.Shifted.Dichotomy

/-!
# Shifted preferences: candidate equilibria, their ex-ante losses, and the minimal loss

* Pooling on `p` (beliefs `poolK p`) and the revealing rule with root `α`
  (`E Z + (Z - E Z)/(1 + κα²) + κ α c`, beliefs `shRevK c α`) are linear equilibria with shift
  `c`.
* Ex-ante losses: `(1 - λ)² Var Z + e² + κ (Var v + c²)` for `E Z + λ (Z - E Z) + e`, and
  `(p - E Z)² + Var Z + κ (Var v + c²)` for pooling on `p`.
* With `λ` a root of `λ² - λ + κ s̃²`, the revealing rule is `E Z + λ (Z - E Z) + κ (s̃/λ) c`;
  the larger root `λ₊ = lam` gives the smallest loss among revealing rules, uniquely.
* `shMin c`: the minimal ex-ante adaptation loss over linear equilibria (`Std.sh_lower_bound`,
  `Std.sh_attained`).
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Roots of the slope equation -/

/-- For a root `α` of `(1 + κα²) s = α`, `l = 1/(1 + κα²)` is a positive root of
`l² - l + κ s² = 0` and `α = s/l`. -/
lemma root_l {κ s α : ℝ} (hκ : 0 ≤ κ) (hα : (1 + κ * α ^ 2) * s = α) :
    0 < 1 / (1 + κ * α ^ 2) ∧ (1 / (1 + κ * α ^ 2)) ^ 2 - 1 / (1 + κ * α ^ 2) + κ * s ^ 2 = 0 ∧
      α = s / (1 / (1 + κ * α ^ 2)) := by
  have hD : 0 < 1 + κ * α ^ 2 := by positivity
  have hs : s = α / (1 + κ * α ^ 2) := by
    field_simp
    linarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [hs]
    field_simp
    ring
  · rw [div_div_eq_mul_div, div_one, mul_comm, hα]

/-- Conversely a positive root `l` gives the root `α = s/l`, with `1/(1 + κα²) = l`. -/
lemma alpha_of_l {κ s l : ℝ} (hl : 0 < l) (h : l ^ 2 - l + κ * s ^ 2 = 0) :
    (1 + κ * (s / l) ^ 2) * s = s / l ∧ 1 / (1 + κ * (s / l) ^ 2) = l := by
  have hD : 1 + κ * (s / l) ^ 2 = 1 / l := by
    field_simp
    linear_combination h
  refine ⟨?_, ?_⟩
  · rw [hD]
    field_simp
  · rw [hD]
    field_simp

/-- Every root is at most the larger root `λ₊`. -/
lemma le_lplus_of_root {κ s l : ℝ} (h : l ^ 2 - l + κ * s ^ 2 = 0) : l ≤ lplus κ s := by
  have e : 1 - 4 * κ * s ^ 2 = (2 * l - 1) ^ 2 := by linear_combination (-4) * h
  unfold lplus
  rw [e, Real.sqrt_sq_eq_abs]
  have := le_abs_self (2 * l - 1)
  linarith

/-- Among revealing rules, `λ₊` minimises `(1 - λ)² V + (κ s c/λ)²`, uniquely. -/
lemma rev_cmp {κ s l c V : ℝ} (hV : 0 < V) (hl : 0 < l) (h : l ^ 2 - l + κ * s ^ 2 = 0) :
    (1 - lplus κ s) ^ 2 * V + (κ * s * c / lplus κ s) ^ 2 ≤ (1 - l) ^ 2 * V + (κ * s * c / l) ^ 2 ∧
    ((1 - l) ^ 2 * V + (κ * s * c / l) ^ 2 ≤ (1 - lplus κ s) ^ 2 * V +
      (κ * s * c / lplus κ s) ^ 2 → l = lplus κ s) := by
  obtain ⟨h1, h2⟩ := lplus_best h
  have hle := le_lplus_of_root h
  have h3 : (κ * s * c / lplus κ s) ^ 2 ≤ (κ * s * c / l) ^ 2 := by
    rw [div_pow, div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ hl.le hle 2)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h1 hV.le]
  · intro h4
    apply h2
    by_contra h5
    have h6 := not_le.1 h5
    nlinarith [mul_lt_mul_of_pos_right h6 hV]

namespace Game

variable {G : Game Ω}

lemma lam_eq (G : Game Ω) : G.lam = lplus G.κ G.sens := rfl

/-- The beliefs of the revealing rule with root `α` and shift `c`. -/
noncomputable def shRevK (G : Game Ω) (c α : ℝ) : Kernel ℝ ℝ :=
  G.postK (fun x => (x - (G.meanZ - G.meanZ / (1 + G.κ * α ^ 2) + G.κ * α * c)) *
    (1 + G.κ * α ^ 2)) (by fun_prop)

instance (c α : ℝ) : IsMarkovKernel (G.shRevK c α) := by
  unfold shRevK
  infer_instance

/-- The minimal ex-ante adaptation loss over linear equilibria with shift `c`. -/
noncomputable def shMin (G : Game Ω) (c : ℝ) : ℝ :=
  if G.κ * G.sens ^ 2 ≤ κck then
    min ((1 - G.lam) ^ 2 * variance G.Z G.P + (G.κ * G.sens * c / G.lam) ^ 2) (variance G.Z G.P)
  else variance G.Z G.P

section Std

variable (hG : G.Std)
include hG

lemma Std.shK_nonneg (c : ℝ) : 0 ≤ G.κ * (variance G.v G.P + c ^ 2) :=
  mul_nonneg hG.κ_pos.le (add_nonneg (variance_nonneg _ _) (sq_nonneg _))

/-- Pooling on any `p` is a linear equilibrium with shift `c`. -/
lemma Std.sh_pool_isLinearEq (c p : ℝ) : G.IsShLinearEq c (fun _ => p) (G.poolK p) := by
  have := hG.prob
  have hE := hG.pool_isLinearEq p
  refine ⟨⟨measurable_const, inferInstance, fun ω x => ?_, hE.1.bayes⟩, hE.2⟩
  by_cases hx : x = p
  · rw [hx]
  · unfold shLoss shConfLoss
    rw [poolK_ne hx, lintegral_shift_top (lintegral_heavy G.norm) c,
      ENNReal.mul_top (by simpa using hG.κ_pos), add_top]
    exact le_top

/-- The revealing rule with root `α` is a linear equilibrium with shift `c`. -/
lemma Std.sh_rev_isLinearEq (c : ℝ) {α : ℝ} (hα : (1 + G.κ * α ^ 2) * G.sens = α) :
    G.IsShLinearEq c (fun ω => G.meanZ + (G.Z ω - G.meanZ) / (1 + G.κ * α ^ 2) + G.κ * α * c)
      (G.shRevK c α) := by
  have := hG.prob
  have hD : 0 < 1 + G.κ * α ^ 2 := by have := hG.κ_pos; positivity
  set D := 1 + G.κ * α ^ 2 with hDdef
  set b₀ := G.meanZ - G.meanZ / D + G.κ * α * c with hb₀
  have hsD : G.sens = α / D := by
    field_simp
    linarith
  have e : (fun ω => G.meanZ + (G.Z ω - G.meanZ) / D + G.κ * α * c) =
      fun ω => (1 / D) * G.Z ω + b₀ := by
    funext ω
    rw [hb₀]
    field_simp
    ring
  have hmean : ∀ x, ∫ b, b ∂(G.shRevK c α x) - G.norm - c =
      α * (x - b₀) - G.sens * G.meanZ - c := by
    intro x
    rw [shRevK, postK_mean, hG.residMean_eq, ← hDdef, ← hb₀, hsD]
    field_simp
    ring
  refine ⟨⟨by rw [e]; exact (hG.measZ.const_mul _).add_const _, inferInstance,
    fun ω x => ?_, ?_⟩, ?_⟩
  · have hloss : ∀ y, G.shLoss c (G.shRevK c α) ω y = ENNReal.ofReal ((y - G.Z ω) ^ 2 +
        G.κ * (G.condVar + (α * (y - b₀) - G.sens * G.meanZ - c) ^ 2)) := by
      intro y
      unfold shLoss
      rw [shConfLoss_eq c (by rw [shRevK]; exact G.postK_sq_integrable _ _ _), hmean,
        show variance id (G.shRevK c α y) = G.condVar from G.postK_var _ _ _,
        ← ENNReal.ofReal_mul hG.κ_pos.le, ← ENNReal.ofReal_add (sq_nonneg _)
          (mul_nonneg hG.κ_pos.le (add_nonneg G.condVar_nonneg (sq_nonneg _)))]
    rw [hloss, hloss]
    refine ENNReal.ofReal_le_ofReal ?_
    set a0 := G.meanZ + (G.Z ω - G.meanZ) / D + G.κ * α * c with ha0
    have key : ((x - G.Z ω) ^ 2 + G.κ * (G.condVar + (α * (x - b₀) - G.sens * G.meanZ - c) ^ 2)) -
        ((a0 - G.Z ω) ^ 2 + G.κ * (G.condVar + (α * (a0 - b₀) - G.sens * G.meanZ - c) ^ 2)) =
        D * (x - a0) ^ 2 := by
      rw [ha0, hb₀, hsD]
      field_simp
      rw [hDdef]
      ring
    have : 0 ≤ D * (x - a0) ^ 2 := by positivity
    linarith
  · have e2 : (fun ω => (G.meanZ + (G.Z ω - G.meanZ) / D + G.κ * α * c, G.v ω)) =
        fun ω => ((1 / D) * G.Z ω + b₀, G.v ω) := by
      funext ω
      exact Prod.ext (congrFun e ω) rfl
    rw [e, e2]
    exact (hG.map_comp_v (g := fun z => (1 / D) * z + b₀) (h := fun x => (x - b₀) * D)
      (by fun_prop) (by fun_prop) (fun z => by field_simp; ring)).symm
  · refine ⟨α, G.norm - G.sens * G.meanZ - α * b₀ + c - c, 0, G.condVar, fun x _ => ?_⟩
    refine ⟨by rw [shRevK]; exact G.postK_sq_integrable _ _ _, ?_, ?_⟩
    · have := hmean x
      linarith
    · rw [shRevK, postK_var]
      ring

/-- The revealing rule with a positive root `λ` of `λ² - λ + κ s̃² = 0`. -/
lemma Std.sh_rev_isLinearEq_l (c : ℝ) {l : ℝ} (hl : 0 < l) (h : l ^ 2 - l + G.κ * G.sens ^ 2 = 0) :
    ∃ φ : Kernel ℝ ℝ, G.IsShLinearEq c
      (fun ω => G.meanZ + l * (G.Z ω - G.meanZ) + G.κ * (G.sens / l) * c) φ := by
  obtain ⟨hα, hD⟩ := alpha_of_l hl h
  refine ⟨G.shRevK c (G.sens / l), ?_⟩
  have hE := hG.sh_rev_isLinearEq c hα
  have e : (fun ω => G.meanZ + (G.Z ω - G.meanZ) / (1 + G.κ * (G.sens / l) ^ 2) +
      G.κ * (G.sens / l) * c) = fun ω => G.meanZ + l * (G.Z ω - G.meanZ) + G.κ * (G.sens / l) * c := by
    funext ω
    rw [div_eq_mul_one_div (G.Z ω - G.meanZ), hD, mul_comm]
  rw [e] at hE
  exact hE

/-- Ex-ante loss of an affine rule `E Z + λ (Z - E Z) + e` in an equilibrium with shift `c`. -/
lemma Std.sh_exLoss_affine (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShPBE c a φ)
    {l e : ℝ} (ha : a =ᵐ[G.P] fun ω => G.meanZ + l * (G.Z ω - G.meanZ) + e) :
    G.shExLoss c a φ = ENNReal.ofReal ((1 - l) ^ 2 * variance G.Z G.P + e ^ 2 +
      G.κ * (variance G.v G.P + c ^ 2)) := by
  rw [hG.sh_exLoss_eq c hE, hG.adapt_affine_sh ha, ← ENNReal.ofReal_mul hG.κ_pos.le,
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (sq_nonneg _) (variance_nonneg _ _))
      (sq_nonneg _)) (hG.shK_nonneg c)]

/-- Ex-ante loss of pooling on `p` in an equilibrium with shift `c`. -/
lemma Std.sh_exLoss_pool (c p : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShPBE c a φ)
    (ha : a =ᵐ[G.P] fun _ => p) :
    G.shExLoss c a φ = ENNReal.ofReal ((p - G.meanZ) ^ 2 + variance G.Z G.P +
      G.κ * (variance G.v G.P + c ^ 2)) := by
  rw [hG.sh_exLoss_eq c hE, hG.adapt_const ha, ← ENNReal.ofReal_mul hG.κ_pos.le,
    ← ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (variance_nonneg _ _)) (hG.shK_nonneg c)]

/-- A revealing linear equilibrium with shift `c` in terms of its slope `λ` on `Z`. -/
lemma Std.sh_rev_loss (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShLinearEq c a φ)
    (hR : G.IsRevealing a) :
    ∃ l : ℝ, 0 < l ∧ l ^ 2 - l + G.κ * G.sens ^ 2 = 0 ∧
      a =ᵐ[G.P] (fun ω => G.meanZ + l * (G.Z ω - G.meanZ) + G.κ * (G.sens / l) * c) ∧
      G.shExLoss c a φ = ENNReal.ofReal ((1 - l) ^ 2 * variance G.Z G.P +
        (G.κ * G.sens * c / l) ^ 2 + G.κ * (variance G.v G.P + c ^ 2)) := by
  obtain ⟨α, hα, ha⟩ := hG.sh_rev_char c hE hR
  obtain ⟨hl0, hl, hαl⟩ := root_l hG.κ_pos.le hα
  set l := 1 / (1 + G.κ * α ^ 2) with hldef
  have ha' : a =ᵐ[G.P] (fun ω => G.meanZ + l * (G.Z ω - G.meanZ) + G.κ * (G.sens / l) * c) := by
    filter_upwards [ha] with ω hω
    rw [hω, ← hαl, hldef]
    field_simp
  refine ⟨l, hl0, hl, ha', ?_⟩
  rw [hG.sh_exLoss_affine c hE.1 ha']
  congr 2
  ring

/-- **Lower bound.** Every linear equilibrium with shift `c` has ex-ante loss at least
`shMin c + κ (Var v + c²)`. -/
lemma Std.sh_lower_bound (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShLinearEq c a φ) :
    ENNReal.ofReal (G.shMin c + G.κ * (variance G.v G.P + c ^ 2)) ≤ G.shExLoss c a φ := by
  have hV := hG.varZ_pos
  by_cases hs : G.sens = 0
  · have hm : G.shMin c = 0 := by
      unfold shMin lam
      rw [hs, ite_eq_left (by simp [κck_pos.le])]
      simp
    rw [hm, zero_add, hG.sh_exLoss_eq c hE.1, ENNReal.ofReal_mul hG.κ_pos.le]
    exact le_add_self
  have hmV : G.shMin c ≤ variance G.Z G.P := by
    unfold shMin
    split_ifs
    · exact min_le_right _ _
    · exact le_rfl
  rcases hG.sh_lemma3_ne c hs hE with ⟨p, hp⟩ | hR
  · rw [hG.sh_exLoss_pool c p hE.1 hp]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (p - G.meanZ)]
  · obtain ⟨l, hl0, hl, -, hloss⟩ := hG.sh_rev_loss c hE hR
    rw [hloss]
    apply ENNReal.ofReal_le_ofReal
    have h4 : G.κ * G.sens ^ 2 ≤ κck :=
      le_kck_iff_four.2 ((slope_root_iff_four _ _).1 (root_of_slope hl0 hl))
    have hm : G.shMin c ≤ (1 - G.lam) ^ 2 * variance G.Z G.P + (G.κ * G.sens * c / G.lam) ^ 2 := by
      unfold shMin
      rw [ite_eq_left h4]
      exact min_le_left _ _
    have := (rev_cmp (c := c) hV hl0 hl).1
    rw [← lam_eq] at this
    linarith

/-- The revealing rule with the larger root `λ₊` has ex-ante loss
`(1 - λ₊)² Var Z + (κ s̃ c/λ₊)² + κ (Var v + c²)`. -/
lemma Std.sh_rev_lam (c : ℝ) (h4 : G.κ * G.sens ^ 2 ≤ κck) :
    ∃ φ : Kernel ℝ ℝ, G.IsShLinearEq c
      (fun ω => G.meanZ + G.lam * (G.Z ω - G.meanZ) + G.κ * (G.sens / G.lam) * c) φ ∧
      G.shExLoss c (fun ω => G.meanZ + G.lam * (G.Z ω - G.meanZ) + G.κ * (G.sens / G.lam) * c) φ =
        ENNReal.ofReal ((1 - G.lam) ^ 2 * variance G.Z G.P + (G.κ * G.sens * c / G.lam) ^ 2 +
          G.κ * (variance G.v G.P + c ^ 2)) := by
  have hroot : G.lam ^ 2 - G.lam + G.κ * G.sens ^ 2 = 0 := lplus_root (le_kck_iff_four.1 h4)
  obtain ⟨φ, hE⟩ := hG.sh_rev_isLinearEq_l c (l := G.lam) (lplus_pos _ _) hroot
  refine ⟨φ, hE, ?_⟩
  rw [hG.sh_exLoss_affine c hE.1 (ae_of_all _ fun _ => rfl)]
  congr 2
  ring

/-- Pooling on `E Z` has ex-ante loss `Var Z + κ (Var v + c²)`. -/
lemma Std.sh_pool_meanZ (c : ℝ) :
    G.IsShLinearEq c (fun _ => G.meanZ) (G.poolK G.meanZ) ∧
      G.shExLoss c (fun _ => G.meanZ) (G.poolK G.meanZ) =
        ENNReal.ofReal (variance G.Z G.P + G.κ * (variance G.v G.P + c ^ 2)) := by
  have hE := hG.sh_pool_isLinearEq c G.meanZ
  refine ⟨hE, ?_⟩
  rw [hG.sh_exLoss_pool c G.meanZ hE.1 (ae_of_all _ fun _ => rfl), sub_self]
  congr 2
  ring

/-- **The bound is attained.** -/
lemma Std.sh_attained (c : ℝ) : ∃ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShLinearEq c a φ ∧
    G.shExLoss c a φ = ENNReal.ofReal (G.shMin c + G.κ * (variance G.v G.P + c ^ 2)) := by
  by_cases h4 : G.κ * G.sens ^ 2 ≤ κck
  · by_cases hr : (1 - G.lam) ^ 2 * variance G.Z G.P + (G.κ * G.sens * c / G.lam) ^ 2 ≤
        variance G.Z G.P
    · obtain ⟨φ, hE, hloss⟩ := hG.sh_rev_lam c h4
      refine ⟨_, φ, hE, ?_⟩
      rw [hloss]
      unfold shMin
      rw [ite_eq_left h4, min_eq_left hr]
    · obtain ⟨hE, hloss⟩ := hG.sh_pool_meanZ c
      refine ⟨_, _, hE, ?_⟩
      rw [hloss]
      unfold shMin
      rw [ite_eq_left h4, min_eq_right (le_of_not_ge hr)]
  · obtain ⟨hE, hloss⟩ := hG.sh_pool_meanZ c
    refine ⟨_, _, hE, ?_⟩
    rw [hloss]
    unfold shMin
    rw [ite_eq_right h4]

end Std

end Game

end CC.LG
