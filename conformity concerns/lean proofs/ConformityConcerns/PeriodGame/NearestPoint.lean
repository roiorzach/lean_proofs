import ConformityConcerns.PeriodGame.BayesFacts

/-!
# Best responses under Linearity, and identification of the linear coefficients

Under Linearity the objective of type `ω` on `I(h)` is the strictly convex quadratic
`(x - Z)² + κ (p x + q + (α x + β - μ)²)`, minimised over `ℝ` at
`g*(Z) = (Z - κ p/2 - κ α (β - μ))/(1 + κ α²)`. Hence almost every type plays the point of `I(h)`
nearest to `g*(Z)`.

Where the action reveals `Z` (it equals `k Z + c`), Bayes' rule pins the belief to the Gaussian
posterior, which identifies `α, β, p, q` (`Std.ident`), and if the action is a.s. `k Z + c`
everywhere we obtain the full description of the belief (`Std.tail`).
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Nearest points of an interval (pure real analysis) -/

section NP

variable {I : Set ℝ} {a g : ℝ}

lemma np_eq (hnp : ∀ y ∈ I, (a - g) ^ 2 ≤ (y - g) ^ 2) (hg : g ∈ I) : a = g := by
  have h1 := hnp g hg
  rw [sub_self] at h1
  have h2 : (a - g) ^ 2 = 0 := le_antisymm (by simpa using h1) (sq_nonneg _)
  have h3 : a - g = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  linarith

lemma np_Ioo (hnp : ∀ y ∈ I, (a - g) ^ 2 ≤ (y - g) ^ 2) {x1 x2 : ℝ} (hx1 : x1 ∈ I) (hx2 : x2 ∈ I)
    (hI : Icc x1 x2 ⊆ I) : a ∈ Ioo x1 x2 ↔ g ∈ Ioo x1 x2 := by
  constructor
  · rintro ⟨h1, h2⟩
    have e1 := hnp x1 hx1
    have e2 := hnp x2 hx2
    constructor
    · by_contra h
      push Not at h
      nlinarith
    · by_contra h
      push Not at h
      nlinarith
  · intro hg
    rw [np_eq hnp (hI (Ioo_subset_Icc_self hg))]
    exact hg

lemma np_top (hnp : ∀ y ∈ I, (a - g) ^ 2 ≤ (y - g) ^ 2) {x1 hi : ℝ} (hx1 : x1 ∈ I) (hhi : hi ∈ I)
    (hlt : x1 < hi) (hI : Icc x1 hi ⊆ I) (hub : ∀ y ∈ I, y ≤ hi) (ha : a ∈ I) : a = hi ↔ hi ≤ g := by
  have hle := hub a ha
  constructor
  · intro h
    by_contra hg
    push Not at hg
    by_cases hg1 : x1 ≤ g
    · have := np_eq hnp (hI ⟨hg1, hg.le⟩)
      linarith
    · push Not at hg1
      have e1 := hnp x1 hx1
      rw [h] at e1
      nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < hi + x1 - 2 * g)]
  · intro hg
    have e := hnp hi hhi
    nlinarith

lemma np_bot (hnp : ∀ y ∈ I, (a - g) ^ 2 ≤ (y - g) ^ 2) {lo x2 : ℝ} (hx2 : x2 ∈ I) (hlo : lo ∈ I)
    (hlt : lo < x2) (hI : Icc lo x2 ⊆ I) (hlb : ∀ y ∈ I, lo ≤ y) (ha : a ∈ I) : a = lo ↔ g ≤ lo := by
  have hle := hlb a ha
  constructor
  · intro h
    by_contra hg
    push Not at hg
    by_cases hg1 : g ≤ x2
    · have := np_eq hnp (hI ⟨hg.le, hg1⟩)
      linarith
    · push Not at hg1
      have e1 := hnp x2 hx2
      rw [h] at e1
      nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < 2 * g - lo - x2)]
  · intro hg
    have e := hnp lo hlo
    nlinarith

end NP

namespace Game

variable {G : Game Ω}

/-- The unconstrained optimum `g*(z)` given linear coefficients `α, β, p`. -/
noncomputable def gstar (G : Game Ω) (α β p z : ℝ) : ℝ :=
  (z - G.κ * p / 2 - G.κ * α * (β - G.norm)) / (1 + G.κ * α ^ 2)

/-- Linearity data on a set. -/
def LinOn (_G : Game Ω) (φ : Kernel ℝ ℝ) (U : Set ℝ) (α β p q : ℝ) : Prop :=
  ∀ x ∈ U, Integrable (fun b : ℝ => b ^ 2) (φ x) ∧ ∫ b, b ∂(φ x) = α * x + β ∧
    variance id (φ x) = p * x + q

section Std

variable (hG : G.Std)
include hG

/-- **Best responses.** Almost every type plays the point of `I(h)` nearest to `g*(Z)`. -/
lemma Std.nearest {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsPBE a φ) {α β p q : ℝ}
    (hlin : G.LinOn φ (G.actionHull a) α β p q) :
    ∀ᵐ ω ∂G.P, a ω ∈ G.actionHull a ∧ ∀ y ∈ G.actionHull a,
      (a ω - G.gstar α β p (G.Z ω)) ^ 2 ≤ (y - G.gstar α β p (G.Z ω)) ^ 2 := by
  have := hE.markov
  filter_upwards [ae_mem_support (G := G) hE.meas] with ω hω
  have hωI := support_subset_hull (G := G) a hω
  refine ⟨hωI, fun y hy => ?_⟩
  have hloss : ∀ x ∈ G.actionHull a, G.loss φ ω x =
      ENNReal.ofReal ((x - G.Z ω) ^ 2 + G.κ * (p * x + q + (α * x + β - G.norm) ^ 2)) := by
    intro x hx
    obtain ⟨hi, hm, hv⟩ := hlin x hx
    have hnn : 0 ≤ p * x + q + (α * x + β - G.norm) ^ 2 := by
      rw [← hv]
      exact add_nonneg (variance_nonneg _ _) (sq_nonneg _)
    unfold loss
    rw [confLoss_eq hi, hm, hv, ← ENNReal.ofReal_mul hG.κ_pos.le,
      ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hG.κ_pos.le hnn)]
  have h := hE.optimal ω y
  have hnn : ∀ x ∈ G.actionHull a, 0 ≤ (x - G.Z ω) ^ 2 + G.κ * (p * x + q + (α * x + β - G.norm) ^ 2) := by
    intro x hx
    obtain ⟨-, -, hv⟩ := hlin x hx
    have : 0 ≤ p * x + q + (α * x + β - G.norm) ^ 2 := by
      rw [← hv]
      exact add_nonneg (variance_nonneg _ _) (sq_nonneg _)
    exact add_nonneg (sq_nonneg _) (mul_nonneg hG.κ_pos.le this)
  rw [hloss _ hωI, hloss _ hy, ENNReal.ofReal_le_ofReal_iff (hnn y hy)] at h
  have hD : 0 < 1 + G.κ * α ^ 2 := by have := hG.κ_pos; positivity
  have key : ((a ω - G.Z ω) ^ 2 + G.κ * (p * a ω + q + (α * a ω + β - G.norm) ^ 2)) -
      ((y - G.Z ω) ^ 2 + G.κ * (p * y + q + (α * y + β - G.norm) ^ 2)) =
      (1 + G.κ * α ^ 2) * ((a ω - G.gstar α β p (G.Z ω)) ^ 2 - (y - G.gstar α β p (G.Z ω)) ^ 2) := by
    unfold gstar
    field_simp
    ring
  nlinarith

omit hG in
lemma gstar_eq (α β p z : ℝ) (hD : 1 + G.κ * α ^ 2 ≠ 0) :
    G.gstar α β p z = (1 / (1 + G.κ * α ^ 2)) * z +
      (-(G.κ * p / 2 + G.κ * α * (β - G.norm)) / (1 + G.κ * α ^ 2)) := by
  unfold gstar
  field_simp
  ring

/-- **Identification of the linear coefficients** where the action reveals `Z`. -/
lemma Std.ident {φ : Kernel ℝ ℝ} {k c : ℝ} (hk : k ≠ 0) {U : Set ℝ}
    (hUpos : 0 < G.P.map (fun ω => k * G.Z ω + c) U)
    (hae : ∀ᵐ x ∂(G.P.map (fun ω => k * G.Z ω + c)), x ∈ U →
      φ x = G.postK (fun x => (x - c) / k) (by fun_prop) x)
    {α β p q : ℝ} (hlin : G.LinOn φ U α β p q) :
    α = G.sens / k ∧ β = G.residMean - G.sens * c / k ∧ p = 0 ∧ q = G.condVar := by
  have hna : ∀ x, G.P.map (fun ω => k * G.Z ω + c) {x} = 0 := fun x => by
    rw [hG.map_aff]
    exact gauss_singleton (hG.aff_var_ne hk) x
  obtain ⟨x₀, x₁, h0U, h1U, hne, h0, h1⟩ := exists_two_of_ae hna hUpos hae
  obtain ⟨-, hm0, hv0⟩ := hlin x₀ h0U
  obtain ⟨-, hm1, hv1⟩ := hlin x₁ h1U
  rw [h0, postK_mean] at hm0
  rw [h1, postK_mean] at hm1
  rw [h0, postK_var] at hv0
  rw [h1, postK_var] at hv1
  have e1 := affine_eq_of_two (p := α) (q := β) (p' := G.sens / k)
    (q' := G.residMean - G.sens * c / k) hne
    (by rw [← hm0]; field_simp; ring) (by rw [← hm1]; field_simp; ring)
  have e2 := affine_eq_of_two (p := p) (q := q) (p' := 0) (q' := G.condVar) hne
    (by rw [← hv0]; ring) (by rw [← hv1]; ring)
  exact ⟨e1.1, e1.2, e2.1, e2.2⟩

/-- **Revealing tail.** If the action is a.s. `E Z + λ (Z - E Z)` with `λ > 0`, then every action is
on path, the belief has mean `(s̃/λ) x + μ - (s̃/λ) E Z` and variance `Var(v | Z)` at every `x`, and
it is Gaussian a.e. -/
lemma Std.tail {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsLinearEq a φ) {l : ℝ} (hl : 0 < l)
    (ha : a =ᵐ[G.P] fun ω => G.meanZ + l * (G.Z ω - G.meanZ)) :
    (G.P.map a).support = univ ∧
      (∀ x, Integrable (fun b : ℝ => b ^ 2) (φ x) ∧
        ∫ b, b ∂(φ x) = G.sens / l * x + (G.norm - G.sens / l * G.meanZ) ∧
        variance id (φ x) = G.condVar) ∧
      ∀ᵐ x ∂(G.P.map a), φ x =
        gaussianReal (G.sens / l * x + (G.norm - G.sens / l * G.meanZ)) G.condVar.toNNReal := by
  have := hG.prob
  set c := (1 - l) * G.meanZ with hc
  have ha' : a =ᵐ[G.P] fun ω => l * G.Z ω + c := ha.mono fun ω hω => by rw [hω, hc]; ring
  have hmap : G.P.map a = G.P.map (fun ω => l * G.Z ω + c) :=
    Measure.map_congr ha'
  have hsupp : (G.P.map a).support = univ := by
    rw [hmap, hG.map_aff]
    exact gauss_support (hG.aff_var_ne hl.ne')
  have hI : G.actionHull a = univ := by
    unfold actionHull
    rw [hsupp, convexHull_univ]
  obtain ⟨α, β, p, q, hlin⟩ := hE.2
  rw [hI] at hlin
  have hae := hG.ae_eq_postK_on hE.1 hl.ne' MeasurableSet.univ
    (ha'.mono fun ω hω => ⟨by simp, fun _ => hω⟩)
  have hpos : 0 < G.P.map (fun ω => l * G.Z ω + c) univ := by simp
  obtain ⟨e1, e2, e3, e4⟩ := hG.ident hl.ne' hpos hae hlin
  have hβ : β = G.norm - G.sens / l * G.meanZ := by
    rw [e2, hG.residMean_eq, hc]
    field_simp
    ring
  refine ⟨hsupp, fun x => ?_, ?_⟩
  · obtain ⟨hi, hm, hv⟩ := hlin x (mem_univ x)
    refine ⟨hi, ?_, ?_⟩
    · rw [hm, e1, hβ]
    · rw [hv, e3, e4]
      ring
  · rw [hmap]
    filter_upwards [hae] with x hx
    rw [hx (mem_univ x), postK_apply]
    congr 1
    rw [hG.residMean_eq, hc]
    field_simp
    ring

end Std

end Game

end CC.LG
