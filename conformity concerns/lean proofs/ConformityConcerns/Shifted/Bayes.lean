import ConformityConcerns.Shifted.Defs
import ConformityConcerns.PeriodGame.RevealingAux

/-!
# Shifted preferences: Bayes' rule and best responses

The consequences of Bayes' rule in `PeriodGame/BayesFacts.lean` and `PeriodGame/DichotomyAux.lean`
use only the measurability, Markov and Bayes fields of an equilibrium; they are restated here for
`IsShPBE` (same proofs). The loss enters through:

* `shConfLoss_eq`: on `I(h)` the shifted conformity loss is `Var + (mean - μ - c)²`;
* `Std.sh_exLoss_eq`: `shExLoss = E (a - Z)² + κ (Var v + c²)` in every perfect Bayesian
  equilibrium;
* `Std.sh_nearest`: almost every type plays the point of `I(h)` nearest to
  `g*(Z) = gstar α (β - c) p Z`.
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A belief with infinite conformity loss about `μ` has infinite conformity loss about `μ + c`. -/
lemma lintegral_shift_top {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {μ : ℝ}
    (h : ∫⁻ b, ENNReal.ofReal ((b - μ) ^ 2) ∂ρ = ∞) (c : ℝ) :
    ∫⁻ b, ENNReal.ofReal ((b - μ - c) ^ 2) ∂ρ = ∞ := by
  have hle : ∀ b : ℝ, ENNReal.ofReal ((b - μ) ^ 2) ≤
      2 * ENNReal.ofReal ((b - μ - c) ^ 2) + ENNReal.ofReal (2 * c ^ 2) := by
    intro b
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (b - μ - 2 * c)])
  have h2 := lintegral_mono (μ := ρ) hle
  rw [h, lintegral_add_right _ measurable_const, lintegral_const_mul _ (by fun_prop),
    lintegral_const, measure_univ, mul_one, top_le_iff] at h2
  by_contra hne
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hne, ENNReal.ofReal_ne_top⟩ h2

/-- Two affine functions of `Z` that agree almost surely have the same coefficients. -/
lemma Game.Std.affine_coeff_eq {G : Game Ω} (hG : G.Std) {k b k' b' : ℝ}
    (h : ∀ᵐ ω ∂G.P, k * G.Z ω + b = k' * G.Z ω + b') : k = k' ∧ b = b' := by
  have := hG.prob
  by_cases hk : k = k'
  · subst hk
    refine ⟨rfl, ?_⟩
    obtain ⟨ω, hω⟩ := h.exists
    linarith
  · exfalso
    have hk' : k - k' ≠ 0 := sub_ne_zero.2 hk
    have hZ : G.Z =ᵐ[G.P] fun _ => (b' - b) / (k - k') := by
      filter_upwards [h] with ω hω
      field_simp
      linear_combination hω
    have h0 : variance G.Z G.P = 0 := by
      rw [variance_congr hZ, variance_eq_integral aemeasurable_const]
      simp
    exact hG.varZ_ne h0

namespace Game

variable {G : Game Ω}

lemma shConfLoss_measurable (c : ℝ) (φ : Kernel ℝ ℝ) : Measurable (G.shConfLoss c φ) :=
  Measurable.lintegral_kernel (by fun_prop)

lemma shConfLoss_eq (c : ℝ) {φ : Kernel ℝ ℝ} [IsMarkovKernel φ] {x : ℝ}
    (hi : Integrable (fun b : ℝ => b ^ 2) (φ x)) :
    G.shConfLoss c φ x =
      ENNReal.ofReal (variance id (φ x) + (∫ b, b ∂(φ x) - G.norm - c) ^ 2) := by
  have h := lintegral_sq_sub hi (G.norm + c)
  simp only [sub_add_eq_sub_sub] at h
  exact h

section Std

variable (hG : G.Std)
include hG

/-- **Ex-ante shifted conformity loss.** For every Bayes-consistent belief,
`E ∫ (b - μ - c)² dφ(a) = Var v + c²`. -/
lemma Std.sh_lintegral_confLoss (c : ℝ) {a : Ω → ℝ} (ha : Measurable a) {φ : Kernel ℝ ℝ}
    [IsMarkovKernel φ] (hb : (G.P.map a) ⊗ₘ φ = G.P.map (fun ω => (a ω, G.v ω))) :
    ∫⁻ ω, G.shConfLoss c φ (a ω) ∂G.P = ENNReal.ofReal (variance G.v G.P + c ^ 2) := by
  have := hG.prob
  rw [← lintegral_map (shConfLoss_measurable c φ) ha]
  have e : ∫⁻ x, G.shConfLoss c φ x ∂(G.P.map a) =
      ∫⁻ p, ENNReal.ofReal ((p.2 - G.norm - c) ^ 2) ∂((G.P.map a) ⊗ₘ φ) := by
    rw [Measure.lintegral_compProd (by fun_prop)]
    rfl
  rw [e, hb, lintegral_map' (by fun_prop) (ha.aemeasurable.prodMk hG.aemv)]
  have e2 : ∫⁻ ω, ENNReal.ofReal ((G.v ω - G.norm - c) ^ 2) ∂G.P =
      ∫⁻ b, ENNReal.ofReal ((b - (G.norm + c)) ^ 2) ∂(G.P.map G.v) := by
    rw [lintegral_map' (by fun_prop) hG.aemv]
    simp only [sub_add_eq_sub_sub]
  have hi : Integrable (fun b : ℝ => b ^ 2) (G.P.map G.v) := by
    rw [integrable_map_measure (by fun_prop) hG.aemv]
    exact hG.memLpv.integrable_sq
  have hmean : ∫ b, b ∂(G.P.map G.v) = G.norm :=
    integral_map hG.aemv aestronglyMeasurable_id
  rw [e2, lintegral_sq_sub hi, variance_id_map hG.aemv, hmean]
  congr 1
  ring

/-- `shExLoss = E (a - Z)² + κ (Var v + c²)` in any perfect Bayesian equilibrium. -/
lemma Std.sh_exLoss_eq (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShPBE c a φ) :
    G.shExLoss c a φ = ∫⁻ ω, ENNReal.ofReal ((a ω - G.Z ω) ^ 2) ∂G.P +
      ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P + c ^ 2) := by
  have := hE.markov
  unfold shExLoss shLoss
  have hm : Measurable fun ω => G.shConfLoss c φ (a ω) :=
    (shConfLoss_measurable c φ).comp hE.meas
  rw [lintegral_add_right' (fun ω => ENNReal.ofReal ((a ω - G.Z ω) ^ 2))
      (g := fun ω => ENNReal.ofReal G.κ * G.shConfLoss c φ (a ω))
      (measurable_const.mul hm).aemeasurable,
    lintegral_const_mul _ hm, hG.sh_lintegral_confLoss c hE.meas hE.bayes]

/-- Adaptation loss of the affine rule `E Z + λ (Z - E Z) + e`. -/
lemma Std.adapt_affine_sh {a : Ω → ℝ} {l e : ℝ}
    (ha : a =ᵐ[G.P] fun ω => G.meanZ + l * (G.Z ω - G.meanZ) + e) :
    ∫⁻ ω, ENNReal.ofReal ((a ω - G.Z ω) ^ 2) ∂G.P =
      ENNReal.ofReal ((1 - l) ^ 2 * variance G.Z G.P + e ^ 2) := by
  have := hG.prob
  have hint1 : Integrable (fun ω => (G.Z ω - G.meanZ) ^ 2) G.P :=
    (hG.memLpZ.sub (memLp_const _)).integrable_sq
  have hint2 : Integrable (fun ω => G.Z ω - G.meanZ) G.P :=
    hG.gZ.integrable.sub (integrable_const _)
  have hX : MemLp (fun ω => (l - 1) * (G.Z ω - G.meanZ) + e) 2 G.P :=
    ((hG.memLpZ.sub (memLp_const _)).const_mul _).add (memLp_const _)
  have e1 : (fun ω => ENNReal.ofReal ((a ω - G.Z ω) ^ 2)) =ᵐ[G.P]
      fun ω => ENNReal.ofReal (((l - 1) * (G.Z ω - G.meanZ) + e) ^ 2) := by
    filter_upwards [ha] with ω hω
    rw [hω]
    congr 1
    ring
  rw [lintegral_congr_ae e1, ← ofReal_integral_eq_lintegral_ofReal hX.integrable_sq
    (ae_of_all _ fun _ => sq_nonneg _)]
  congr 1
  have e2 : (fun ω => ((l - 1) * (G.Z ω - G.meanZ) + e) ^ 2) = fun ω =>
      (l - 1) ^ 2 * (G.Z ω - G.meanZ) ^ 2 + ((2 * e * (l - 1)) * (G.Z ω - G.meanZ) + e ^ 2) := by
    funext ω
    ring
  have hv : variance G.Z G.P = ∫ ω, (G.Z ω - G.meanZ) ^ 2 ∂G.P := variance_eq_integral hG.aemZ
  have h0 : ∫ ω, (G.Z ω - G.meanZ) ∂G.P = 0 := by
    rw [integral_sub hG.gZ.integrable (integrable_const _), integral_const]
    simp [Game.meanZ]
  have hint3 : Integrable (fun ω => (2 * e * (l - 1)) * (G.Z ω - G.meanZ) + e ^ 2) G.P :=
    (hint2.const_mul _).add (integrable_const _)
  have hint4 : Integrable (fun ω => (2 * e * (l - 1)) * (G.Z ω - G.meanZ)) G.P :=
    hint2.const_mul _
  rw [e2, integral_add (hint1.const_mul _) hint3,
    integral_add hint4 (integrable_const _), integral_const_mul,
    integral_const_mul, h0, integral_const, ← hv, probReal_univ, smul_eq_mul]
  ring

/-- **Bayes' rule where the action reveals `Z`** (shifted game). -/
lemma Std.sh_ae_eq_postK_on (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShPBE c a φ)
    {k c₁ : ℝ} (hk : k ≠ 0) {U : Set ℝ} (hU : MeasurableSet U)
    (hae : ∀ᵐ ω ∂G.P, (a ω ∈ U ↔ k * G.Z ω + c₁ ∈ U) ∧ (a ω ∈ U → a ω = k * G.Z ω + c₁)) :
    ∀ᵐ x ∂(G.P.map (fun ω => k * G.Z ω + c₁)), x ∈ U →
      φ x = G.postK (fun x => (x - c₁) / k) (by fun_prop) x := by
  have := hG.prob
  have := hE.markov
  set ψ := G.postK (fun x => (x - c₁) / k) (by fun_prop)
  have hgZ : AEMeasurable (fun ω => k * G.Z ω + c₁) G.P :=
    (measurable_id.const_mul k |>.add_const c₁).comp_aemeasurable hG.aemZ
  have hj := hG.map_comp_v (g := fun z => k * z + c₁) (h := fun x => (x - c₁) / k) (by fun_prop)
    (by fun_prop) (fun z => by field_simp; ring)
  have e1 := hG.map_restrict_eq hE.meas.aemeasurable hgZ hU hae
  have e2 := Game.Std.map_restrict_eq' hE.meas.aemeasurable hgZ hU hae
  have key : ((G.P.map a).restrict U) ⊗ₘ φ = ((G.P.map a).restrict U) ⊗ₘ ψ := by
    rw [compProd_restrict_left' hU, hE.bayes, e1, hj, ← compProd_restrict_left' hU, e2]
  have h := Kernel.ae_eq_of_compProd_eq key
  rw [e2] at h
  exact (ae_restrict_iff' hU).1 h

/-- **Bayes' rule at an atom** (shifted game). -/
lemma Std.sh_atom_eq (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShPBE c a φ) {k c₁ : ℝ}
    (hk : k ≠ 0) {x₀ : ℝ} {T : Set ℝ} (hT : MeasurableSet T)
    (hae : ∀ᵐ ω ∂G.P, a ω = x₀ ↔ k * G.Z ω + c₁ ∈ T) :
    (G.P.map a {x₀}) • φ x₀ =
      ((((G.P.map (fun ω => k * G.Z ω + c₁)).restrict T) ⊗ₘ
        G.postK (fun x => (x - c₁) / k) (by fun_prop))).map Prod.snd := by
  have := hG.prob
  have := hE.markov
  set ψ := G.postK (fun x => (x - c₁) / k) (by fun_prop)
  have hgZ : AEMeasurable (fun ω => k * G.Z ω + c₁) G.P :=
    (measurable_id.const_mul k |>.add_const c₁).comp_aemeasurable hG.aemZ
  have hj := hG.map_comp_v (g := fun z => k * z + c₁) (h := fun x => (x - c₁) / k) (by fun_prop)
    (by fun_prop) (fun z => by field_simp; ring)
  ext B hB
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply measurable_snd hB,
    show (Prod.snd ⁻¹' B : Set (ℝ × ℝ)) = univ ×ˢ B by ext; simp,
    Measure.compProd_apply_prod MeasurableSet.univ hB, Measure.restrict_univ,
    ← Measure.compProd_apply_prod hT hB, ← hj,
    Measure.map_apply_of_aemeasurable (hgZ.prodMk hG.aemv) (hT.prod hB)]
  have hat : G.P.map a {x₀} * φ x₀ B = (G.P.map (fun ω => (a ω, G.v ω))) ({x₀} ×ˢ B) := by
    rw [← hE.bayes, Measure.compProd_apply_prod (measurableSet_singleton x₀) hB,
      lintegral_singleton, mul_comm]
  rw [hat, Measure.map_apply_of_aemeasurable (hE.meas.aemeasurable.prodMk hG.aemv)
    ((measurableSet_singleton x₀).prod hB)]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [hae] with ω hω
  simp only [mem_preimage, mem_prod, mem_singleton_iff]
  rw [hω]

/-- **The endpoint argument** (shifted game). -/
lemma Std.sh_atom_contra (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShPBE c a φ)
    {k c₁ : ℝ} (hk : 0 < k)
    {α β : ℝ} (hmean : ∀ x, G.sens * ((x - c₁) / k) + G.residMean = α * x + β)
    (hs : G.sens ≠ 0) {x₀ : ℝ} (hx₀ : ∫ b, b ∂(φ x₀) = α * x₀ + β) {T : Set ℝ}
    (hT : MeasurableSet T) (hae : ∀ᵐ ω ∂G.P, a ω = x₀ ↔ k * G.Z ω + c₁ ∈ T)
    (hint : ∫ x in T, (x - x₀) ∂(G.P.map (fun ω => k * G.Z ω + c₁)) ≠ 0) : False := by
  have := hG.prob
  have := hE.markov
  set ν' := G.P.map (fun ω => k * G.Z ω + c₁) with hν'
  set ψ := G.postK (fun x => (x - c₁) / k) (by fun_prop) with hψ
  have hat := hG.sh_atom_eq c hE hk.ne' hT hae
  rw [← hν', ← hψ] at hat
  have hgZ : AEMeasurable (fun ω => k * G.Z ω + c₁) G.P :=
    (measurable_id.const_mul k |>.add_const c₁).comp_aemeasurable hG.aemZ
  have hj := hG.map_comp_v (g := fun z => k * z + c₁) (h := fun x => (x - c₁) / k) (by fun_prop)
    (by fun_prop) (fun z => by field_simp; ring)
  rw [← hν', ← hψ] at hj
  have hmass : G.P.map a {x₀} = ν' T := by
    have := congrArg (fun ρ : Measure ℝ => ρ univ) hat
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at this
    rw [this, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ,
      Measure.compProd_apply_univ, Measure.restrict_apply_univ]
  have hint2 : Integrable (fun p : ℝ × ℝ => p.2) ((ν'.restrict T) ⊗ₘ ψ) := by
    rw [compProd_restrict_left' hT, ← hj]
    refine Integrable.restrict ?_
    rw [integrable_map_measure (by fun_prop) (hgZ.prodMk hG.aemv)]
    exact hG.gv.integrable
  have hI := congrArg (fun ρ : Measure ℝ => ∫ b, b ∂ρ) hat
  rw [integral_smul_measure, hx₀, hmass,
    integral_map (f := fun b : ℝ => b) measurable_snd.aemeasurable aestronglyMeasurable_id,
    Measure.integral_compProd hint2] at hI
  have hψmean : ∀ x, ∫ b, b ∂(ψ x) = α * x + β := fun x => by
    rw [hψ, postK_mean, hmean]
  simp only [hψmean] at hI
  have hν'g := hG.map_aff k c₁
  rw [← hν'] at hν'g
  have hInt : Integrable (fun x : ℝ => x - x₀) (ν'.restrict T) := by
    rw [hν'g]
    exact (gauss_integrable_sub _ _ x₀).restrict
  have h3 : ∫ x in T, (α * x + β) ∂ν' =
      α * ∫ x in T, (x - x₀) ∂ν' + ν'.real T * (α * x₀ + β) := by
    have e : (fun x => α * x + β) = fun x => α * (x - x₀) + (α * x₀ + β) := by funext x; ring
    rw [e, integral_add (hInt.const_mul α) (integrable_const _), integral_const_mul,
      setIntegral_const, smul_eq_mul]
  have hα : α = 0 := by
    have h4 : α * ∫ x in T, (x - x₀) ∂ν' = 0 := by
      rw [← hI, Measure.real] at h3
      rw [smul_eq_mul] at h3
      linarith
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · exact absurd h hint
  have h5 := hmean c₁
  have h6 := hmean (c₁ + k)
  rw [sub_self, zero_div, mul_zero, zero_add] at h5
  rw [add_sub_cancel_left, div_self hk.ne', mul_one] at h6
  apply hs
  rw [hα] at h5 h6
  linarith

/-- **Best responses** (shifted game). Almost every type plays the point of `I(h)` nearest to
`g*(Z) = gstar α (β - c) p Z`. -/
lemma Std.sh_nearest (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShPBE c a φ)
    {α β p q : ℝ} (hlin : G.LinOn φ (G.actionHull a) α β p q) :
    ∀ᵐ ω ∂G.P, a ω ∈ G.actionHull a ∧ ∀ y ∈ G.actionHull a,
      (a ω - G.gstar α (β - c) p (G.Z ω)) ^ 2 ≤ (y - G.gstar α (β - c) p (G.Z ω)) ^ 2 := by
  have := hE.markov
  filter_upwards [ae_mem_support (G := G) hE.meas] with ω hω
  have hωI := support_subset_hull (G := G) a hω
  refine ⟨hωI, fun y hy => ?_⟩
  have hnn0 : ∀ x ∈ G.actionHull a, 0 ≤ p * x + q + (α * x + β - G.norm - c) ^ 2 := by
    intro x hx
    obtain ⟨-, -, hv⟩ := hlin x hx
    rw [← hv]
    exact add_nonneg (variance_nonneg _ _) (sq_nonneg _)
  have hloss : ∀ x ∈ G.actionHull a, G.shLoss c φ ω x =
      ENNReal.ofReal ((x - G.Z ω) ^ 2 + G.κ * (p * x + q + (α * x + β - G.norm - c) ^ 2)) := by
    intro x hx
    obtain ⟨hi, hm, hv⟩ := hlin x hx
    unfold shLoss
    rw [shConfLoss_eq c hi, hm, hv, ← ENNReal.ofReal_mul hG.κ_pos.le,
      ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hG.κ_pos.le (hnn0 x hx))]
  have h := hE.optimal ω y
  have hnn : 0 ≤ (y - G.Z ω) ^ 2 + G.κ * (p * y + q + (α * y + β - G.norm - c) ^ 2) :=
    add_nonneg (sq_nonneg _) (mul_nonneg hG.κ_pos.le (hnn0 y hy))
  rw [hloss _ hωI, hloss _ hy, ENNReal.ofReal_le_ofReal_iff hnn] at h
  have hD : 0 < 1 + G.κ * α ^ 2 := by have := hG.κ_pos; positivity
  have key : ((a ω - G.Z ω) ^ 2 + G.κ * (p * a ω + q + (α * a ω + β - G.norm - c) ^ 2)) -
      ((y - G.Z ω) ^ 2 + G.κ * (p * y + q + (α * y + β - G.norm - c) ^ 2)) =
      (1 + G.κ * α ^ 2) * ((a ω - G.gstar α (β - c) p (G.Z ω)) ^ 2 -
        (y - G.gstar α (β - c) p (G.Z ω)) ^ 2) := by
    unfold gstar
    field_simp
    ring
  nlinarith

end Std

end Game

end CC.LG
