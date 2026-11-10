import ConformityConcerns.PeriodGame.GaussianFacts

/-!
# Bayes' rule and best responses in the period game

General consequences of the equilibrium conditions:
* the ex-ante conformity loss equals `κ Var v` for every Bayes-consistent belief, so
  `exLoss = E (a - Z)² + κ Var v`;
* on `I(h)` the conformity loss is `Var + (mean - μ)²`, so under Linearity every type's
  objective on `I(h)` is a strictly convex quadratic and almost every type plays the point of
  `I(h)` nearest to the unconstrained optimum `g*(Z)`;
* Bayes' rule on a set where the action reveals `Z` and at an atom.
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Measure-theoretic helpers -/

lemma compProd_restrict_left' {μ : Measure ℝ} [IsFiniteMeasure μ] {κ : Kernel ℝ ℝ}
    [IsMarkovKernel κ] {U : Set ℝ} (hU : MeasurableSet U) :
    (μ.restrict U) ⊗ₘ κ = (μ ⊗ₘ κ).restrict (U ×ˢ univ) := by
  refine Measure.ext_prod fun {A B} hA hB => ?_
  rw [Measure.compProd_apply_prod hA hB, Measure.restrict_apply (hA.prod hB), prod_inter_prod,
    inter_univ, Measure.compProd_apply_prod (hA.inter hU) hB, Measure.restrict_restrict hA]

lemma affine_eq_of_two {p q p' q' x₀ x₁ : ℝ} (hne : x₀ ≠ x₁) (h0 : p * x₀ + q = p' * x₀ + q')
    (h1 : p * x₁ + q = p' * x₁ + q') : p = p' ∧ q = q' := by
  have hp : (p - p') * (x₀ - x₁) = 0 := by linear_combination h0 - h1
  have hp' : p = p' := by
    rcases mul_eq_zero.1 hp with h | h
    · linarith
    · exact absurd (sub_eq_zero.1 h) hne
  refine ⟨hp', ?_⟩
  subst hp'
  linarith

/-- The conformity loss of a belief with finite second moment. -/
lemma lintegral_sq_sub {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hi : Integrable (fun b : ℝ => b ^ 2) ρ) (μ : ℝ) :
    ∫⁻ b, ENNReal.ofReal ((b - μ) ^ 2) ∂ρ =
      ENNReal.ofReal (variance id ρ + (∫ b, b ∂ρ - μ) ^ 2) := by
  have hm : MemLp (id : ℝ → ℝ) 2 ρ :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 hi
  have hm' : MemLp (fun b : ℝ => b - μ) 2 ρ := hm.sub (memLp_const μ)
  rw [← ofReal_integral_eq_lintegral_ofReal hm'.integrable_sq (ae_of_all _ fun _ => sq_nonneg _)]
  congr 1
  have h1 := variance_eq_sub hm'
  have h4 : Var[fun b : ℝ => b - μ; ρ] = Var[id; ρ] :=
    variance_sub_const (X := id) aestronglyMeasurable_id μ
  rw [h4] at h1
  have h2 : ∫ b, (b - μ) ∂ρ = ∫ b, b ∂ρ - μ := by
    rw [integral_sub (show Integrable (fun b : ℝ => b) ρ from hm.integrable one_le_two)
      (integrable_const _), integral_const]
    simp
  rw [h2] at h1
  have h3 : ρ[(fun b : ℝ => b - μ) ^ 2] = ∫ b, (b - μ) ^ 2 ∂ρ := rfl
  rw [h3] at h1
  linarith

namespace Game

variable {G : Game Ω}

lemma confLoss_measurable (φ : Kernel ℝ ℝ) : Measurable (G.confLoss φ) :=
  Measurable.lintegral_kernel (by fun_prop)

lemma confLoss_eq {φ : Kernel ℝ ℝ} [IsMarkovKernel φ] {x : ℝ}
    (hi : Integrable (fun b : ℝ => b ^ 2) (φ x)) :
    G.confLoss φ x = ENNReal.ofReal (variance id (φ x) + (∫ b, b ∂(φ x) - G.norm) ^ 2) :=
  lintegral_sq_sub hi _

lemma ae_mem_support {a : Ω → ℝ} (ha : Measurable a) :
    ∀ᵐ ω ∂G.P, a ω ∈ (G.P.map a).support :=
  ae_of_ae_map ha.aemeasurable Measure.support_mem_ae

lemma support_subset_hull (a : Ω → ℝ) : (G.P.map a).support ⊆ G.actionHull a :=
  subset_convexHull ℝ _

section Std

variable (hG : G.Std)
include hG

/-- **Ex-ante conformity loss.** For every Bayes-consistent belief, `E ∫ (b - μ)² dφ(a) = Var v`. -/
lemma Std.lintegral_confLoss {a : Ω → ℝ} (ha : Measurable a) {φ : Kernel ℝ ℝ}
    [IsMarkovKernel φ] (hb : (G.P.map a) ⊗ₘ φ = G.P.map (fun ω => (a ω, G.v ω))) :
    ∫⁻ ω, G.confLoss φ (a ω) ∂G.P = ENNReal.ofReal (variance G.v G.P) := by
  have := hG.prob
  rw [← lintegral_map (confLoss_measurable φ) ha]
  have e : ∫⁻ x, G.confLoss φ x ∂(G.P.map a) =
      ∫⁻ p, ENNReal.ofReal ((p.2 - G.norm) ^ 2) ∂((G.P.map a) ⊗ₘ φ) := by
    rw [Measure.lintegral_compProd (by fun_prop)]
    rfl
  rw [e, hb, lintegral_map' (by fun_prop) (ha.aemeasurable.prodMk hG.aemv),
    ofReal_variance hG.memLpv, evariance_eq_lintegral_ofReal]
  rfl

/-- `exLoss = E (a - Z)² + κ Var v` in any perfect Bayesian equilibrium. -/
lemma Std.exLoss_eq {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsPBE a φ) :
    G.exLoss a φ = ∫⁻ ω, ENNReal.ofReal ((a ω - G.Z ω) ^ 2) ∂G.P +
      ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P) := by
  have := hE.markov
  unfold exLoss loss
  have hm : Measurable fun ω => G.confLoss φ (a ω) := (confLoss_measurable φ).comp hE.meas
  rw [lintegral_add_right' (fun ω => ENNReal.ofReal ((a ω - G.Z ω) ^ 2))
      (g := fun ω => ENNReal.ofReal G.κ * G.confLoss φ (a ω)) (measurable_const.mul hm).aemeasurable,
    lintegral_const_mul _ hm, hG.lintegral_confLoss hE.meas hE.bayes]

/-- Adaptation loss of the affine rule `E Z + λ (Z - E Z)`. -/
lemma Std.adapt_affine {a : Ω → ℝ} {l : ℝ}
    (ha : a =ᵐ[G.P] fun ω => G.meanZ + l * (G.Z ω - G.meanZ)) :
    ∫⁻ ω, ENNReal.ofReal ((a ω - G.Z ω) ^ 2) ∂G.P =
      ENNReal.ofReal ((1 - l) ^ 2 * variance G.Z G.P) := by
  have := hG.prob
  have e : ∀ᵐ ω ∂G.P, ENNReal.ofReal ((a ω - G.Z ω) ^ 2) =
      ENNReal.ofReal ((1 - l) ^ 2) * ENNReal.ofReal ((G.Z ω - G.meanZ) ^ 2) := by
    filter_upwards [ha] with ω hω
    rw [hω, ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  rw [lintegral_congr_ae e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.ofReal_mul (sq_nonneg _), ofReal_variance hG.memLpZ, evariance_eq_lintegral_ofReal]
  rfl

/-- Adaptation loss of the constant rule `c`. -/
lemma Std.adapt_const {a : Ω → ℝ} {c : ℝ} (ha : a =ᵐ[G.P] fun _ => c) :
    ∫⁻ ω, ENNReal.ofReal ((a ω - G.Z ω) ^ 2) ∂G.P =
      ENNReal.ofReal ((c - G.meanZ) ^ 2 + variance G.Z G.P) := by
  have := hG.prob
  have hm : MemLp (fun ω => c - G.Z ω) 2 G.P := (memLp_const c).sub hG.memLpZ
  rw [lintegral_congr_ae (ha.mono fun ω hω => by rw [hω]),
    ← ofReal_integral_eq_lintegral_ofReal hm.integrable_sq (ae_of_all _ fun _ => sq_nonneg _)]
  congr 1
  have h1 := variance_eq_sub hm
  rw [variance_const_sub hG.aemZ.aestronglyMeasurable] at h1
  have h2 : ∫ ω, (c - G.Z ω) ∂G.P = c - G.meanZ := by
    rw [integral_sub (integrable_const _) hG.gZ.integrable, integral_const]
    simp [Game.meanZ]
  rw [h2] at h1
  have h3 : G.P[(fun ω => c - G.Z ω) ^ 2] = ∫ ω, (c - G.Z ω) ^ 2 ∂G.P := rfl
  rw [h3] at h1
  linarith

/-- If `f₁ ∈ U ⟺ f₂ ∈ U` and `f₁ = f₂` there (a.s.), the joint laws with `v` agree on `U × ℝ`. -/
lemma Std.map_restrict_eq {f₁ f₂ : Ω → ℝ} (h₁ : AEMeasurable f₁ G.P) (h₂ : AEMeasurable f₂ G.P)
    {U : Set ℝ} (hU : MeasurableSet U)
    (hae : ∀ᵐ ω ∂G.P, (f₁ ω ∈ U ↔ f₂ ω ∈ U) ∧ (f₁ ω ∈ U → f₁ ω = f₂ ω)) :
    (G.P.map (fun ω => (f₁ ω, G.v ω))).restrict (U ×ˢ univ) =
      (G.P.map (fun ω => (f₂ ω, G.v ω))).restrict (U ×ˢ univ) := by
  ext C hC
  rw [Measure.restrict_apply hC, Measure.restrict_apply hC,
    Measure.map_apply_of_aemeasurable (h₁.prodMk hG.aemv) (hC.inter (hU.prod MeasurableSet.univ)),
    Measure.map_apply_of_aemeasurable (h₂.prodMk hG.aemv) (hC.inter (hU.prod MeasurableSet.univ))]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [hae] with ω hω
  simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true]
  constructor
  · rintro ⟨h1, h2⟩
    rw [← hω.2 h2]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have h3 := hω.1.2 h2
    rw [hω.2 h3]
    exact ⟨h1, h2⟩

omit hG in
lemma Std.map_restrict_eq' {f₁ f₂ : Ω → ℝ} (h₁ : AEMeasurable f₁ G.P) (h₂ : AEMeasurable f₂ G.P)
    {U : Set ℝ} (hU : MeasurableSet U)
    (hae : ∀ᵐ ω ∂G.P, (f₁ ω ∈ U ↔ f₂ ω ∈ U) ∧ (f₁ ω ∈ U → f₁ ω = f₂ ω)) :
    (G.P.map f₁).restrict U = (G.P.map f₂).restrict U := by
  ext C hC
  rw [Measure.restrict_apply hC, Measure.restrict_apply hC,
    Measure.map_apply_of_aemeasurable h₁ (hC.inter hU),
    Measure.map_apply_of_aemeasurable h₂ (hC.inter hU)]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [hae] with ω hω
  simp only [mem_preimage, mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rw [← hω.2 h2]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have h3 := hω.1.2 h2
    rw [hω.2 h3]
    exact ⟨h1, h2⟩

/-- **Bayes' rule where the action reveals `Z`.** If, on `U`, the action equals `k Z + c`, then
the belief equals the Gaussian posterior `postK` for a.e. action in `U`. -/
lemma Std.ae_eq_postK_on {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsPBE a φ) {k c : ℝ}
    (hk : k ≠ 0) {U : Set ℝ} (hU : MeasurableSet U)
    (hae : ∀ᵐ ω ∂G.P, (a ω ∈ U ↔ k * G.Z ω + c ∈ U) ∧ (a ω ∈ U → a ω = k * G.Z ω + c)) :
    ∀ᵐ x ∂(G.P.map (fun ω => k * G.Z ω + c)), x ∈ U →
      φ x = G.postK (fun x => (x - c) / k) (by fun_prop) x := by
  have := hG.prob
  have := hE.markov
  set ψ := G.postK (fun x => (x - c) / k) (by fun_prop)
  have hgZ : AEMeasurable (fun ω => k * G.Z ω + c) G.P :=
    (measurable_id.const_mul k |>.add_const c).comp_aemeasurable hG.aemZ
  have hj := hG.map_comp_v (g := fun z => k * z + c) (h := fun x => (x - c) / k) (by fun_prop)
    (by fun_prop) (fun z => by field_simp; ring)
  have e1 := hG.map_restrict_eq hE.meas.aemeasurable hgZ hU hae
  have e2 := Std.map_restrict_eq' hE.meas.aemeasurable hgZ hU hae
  have key : ((G.P.map a).restrict U) ⊗ₘ φ = ((G.P.map a).restrict U) ⊗ₘ ψ := by
    rw [compProd_restrict_left' hU, hE.bayes, e1, hj, ← compProd_restrict_left' hU, e2]
  have h := Kernel.ae_eq_of_compProd_eq key
  rw [e2] at h
  exact (ae_restrict_iff' hU).1 h

/-- **Bayes' rule at an atom.** If `a = x₀` exactly when `k Z + c ∈ T`, then
`P(a = x₀) • φ x₀` is the mixture of the posteriors over `T`. -/
lemma Std.atom_eq {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsPBE a φ) {k c : ℝ} (hk : k ≠ 0)
    {x₀ : ℝ} {T : Set ℝ} (hT : MeasurableSet T)
    (hae : ∀ᵐ ω ∂G.P, a ω = x₀ ↔ k * G.Z ω + c ∈ T) :
    (G.P.map a {x₀}) • φ x₀ =
      ((((G.P.map (fun ω => k * G.Z ω + c)).restrict T) ⊗ₘ
        G.postK (fun x => (x - c) / k) (by fun_prop))).map Prod.snd := by
  have := hG.prob
  have := hE.markov
  set ψ := G.postK (fun x => (x - c) / k) (by fun_prop)
  have hgZ : AEMeasurable (fun ω => k * G.Z ω + c) G.P :=
    (measurable_id.const_mul k |>.add_const c).comp_aemeasurable hG.aemZ
  have hj := hG.map_comp_v (g := fun z => k * z + c) (h := fun x => (x - c) / k) (by fun_prop)
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

end Std

end Game

end CC.LG
