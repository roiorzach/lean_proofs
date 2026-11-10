import ConformityConcerns.PeriodGame.Construct
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The linear dichotomy (strong form of Lemma 3)

`Std.lemma3_ne`: if `s̃ ≠ 0`, every linear equilibrium is pooling or revealing with a slope `λ`
solving `λ² - λ + κ s̃² = 0`, and then the beliefs are Gaussian with variance `Var(v | Z)`.
`Std.lemma3_strong`: the same when `s̃ = 0`, for a signaling equilibrium, provided `Z` is
measurable (Social Optimality compares with the revealing rule `a = Z`, which is a strategy only
when `Z` is measurable).
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Game

variable {G : Game Ω}

/-- The revealing alternative of Lemma 3, with slope `λ`. -/
def RevealingWith (G : Game Ω) (a : Ω → ℝ) (φ : Kernel ℝ ℝ) (l : ℝ) : Prop :=
  0 < l ∧ l ^ 2 - l + G.κ * G.sens ^ 2 = 0 ∧
    a =ᵐ[G.P] (fun ω => G.meanZ + l * (G.Z ω - G.meanZ)) ∧
    (G.P.map a).support = univ ∧
    (∀ x, Integrable (fun b : ℝ => b ^ 2) (φ x) ∧
        ∫ b, b ∂(φ x) = G.sens / l * x + (G.norm - G.sens / l * G.meanZ) ∧
        variance id (φ x) = G.condVar) ∧
    ∀ᵐ x ∂(G.P.map a),
      φ x = gaussianReal (G.sens / l * x + (G.norm - G.sens / l * G.meanZ)) G.condVar.toNNReal

lemma two_support [IsProbabilityMeasure G.P] {a : Ω → ℝ} (ha : Measurable a)
    (hnp : ¬ G.IsPooling a) :
    ∃ x1 x2, x1 ∈ (G.P.map a).support ∧ x2 ∈ (G.P.map a).support ∧ x1 < x2 := by
  have hne : (G.P.map a).support.Nonempty := by
    refine Measure.nonempty_support ?_
    intro h
    have := congrArg (fun μ : Measure ℝ => μ univ) h
    simp at this
  obtain ⟨x1, hx1⟩ := hne
  by_cases hall : ∀ y ∈ (G.P.map a).support, y = x1
  · exact absurd ⟨x1, (ae_mem_support (G := G) ha).mono fun ω hω => hall _ hω⟩ hnp
  · push Not at hall
    obtain ⟨y, hy, hyne⟩ := hall
    rcases lt_or_gt_of_ne hyne with h | h
    · exact ⟨y, x1, hy, hx1, h⟩
    · exact ⟨x1, y, hx1, hy, h⟩

lemma Icc_subset_hull {a : Ω → ℝ} {x y : ℝ} (hx : x ∈ G.actionHull a) (hy : y ∈ G.actionHull a)
    (hxy : x ≤ y) : Icc x y ⊆ G.actionHull a := by
  rw [← segment_eq_Icc hxy]
  exact (convex_convexHull ℝ _).segment_subset hx hy

section Std

variable (hG : G.Std)
include hG

lemma Std.revealingWith_of {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsLinearEq a φ) {l : ℝ}
    (hl : 0 < l) (hroot : l ^ 2 - l + G.κ * G.sens ^ 2 = 0)
    (ha : a =ᵐ[G.P] fun ω => G.meanZ + l * (G.Z ω - G.meanZ)) : G.RevealingWith a φ l :=
  ⟨hl, hroot, ha, hG.tail hE hl ha⟩

/-- **The endpoint argument.** If `a` pools on `x₀` exactly when `k Z + c ∈ T`, Linearity at
`x₀` contradicts Bayes' rule unless `s̃ = 0` (the truncated mean differs from the affine
extrapolation). -/
lemma Std.atom_contra {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsPBE a φ) {k c : ℝ} (hk : 0 < k)
    {α β : ℝ} (hmean : ∀ x, G.sens * ((x - c) / k) + G.residMean = α * x + β)
    (hs : G.sens ≠ 0) {x₀ : ℝ} (hx₀ : ∫ b, b ∂(φ x₀) = α * x₀ + β) {T : Set ℝ}
    (hT : MeasurableSet T) (hae : ∀ᵐ ω ∂G.P, a ω = x₀ ↔ k * G.Z ω + c ∈ T)
    (hint : ∫ x in T, (x - x₀) ∂(G.P.map (fun ω => k * G.Z ω + c)) ≠ 0) : False := by
  have := hG.prob
  have := hE.markov
  set ν' := G.P.map (fun ω => k * G.Z ω + c) with hν'
  set ψ := G.postK (fun x => (x - c) / k) (by fun_prop) with hψ
  have hat := hG.atom_eq hE hk.ne' hT hae
  rw [← hν', ← hψ] at hat
  have hgZ : AEMeasurable (fun ω => k * G.Z ω + c) G.P :=
    (measurable_id.const_mul k |>.add_const c).comp_aemeasurable hG.aemZ
  have hj := hG.map_comp_v (g := fun z => k * z + c) (h := fun x => (x - c) / k) (by fun_prop)
    (by fun_prop) (fun z => by field_simp; ring)
  rw [← hν', ← hψ] at hj
  -- the mass of the atom
  have hmass : G.P.map a {x₀} = ν' T := by
    have := congrArg (fun ρ : Measure ℝ => ρ univ) hat
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at this
    rw [this, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ,
      Measure.compProd_apply_univ, Measure.restrict_apply_univ]
  -- integrability of `b` under the mixture
  have hint2 : Integrable (fun p : ℝ × ℝ => p.2) ((ν'.restrict T) ⊗ₘ ψ) := by
    rw [compProd_restrict_left' hT, ← hj]
    refine Integrable.restrict ?_
    rw [integrable_map_measure (by fun_prop) (hgZ.prodMk hG.aemv)]
    exact hG.gv.integrable
  -- integrate the identity `hat`
  have hI := congrArg (fun ρ : Measure ℝ => ∫ b, b ∂ρ) hat
  rw [integral_smul_measure, hx₀, hmass,
    integral_map (f := fun b : ℝ => b) measurable_snd.aemeasurable aestronglyMeasurable_id,
    Measure.integral_compProd hint2] at hI
  have hψmean : ∀ x, ∫ b, b ∂(ψ x) = α * x + β := fun x => by
    rw [hψ, postK_mean, hmean]
  simp only [hψmean] at hI
  -- `ν'` is Gaussian, so `x - x₀` is integrable
  have hν'g := hG.map_aff k c
  rw [← hν'] at hν'g
  have hInt : Integrable (fun x : ℝ => x - x₀) (ν'.restrict T) := by
    rw [hν'g]
    exact (gauss_integrable_sub _ _ x₀).restrict
  have h3 : ∫ x in T, (α * x + β) ∂ν' = α * ∫ x in T, (x - x₀) ∂ν' + ν'.real T * (α * x₀ + β) := by
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
  -- then `s̃ = α k = 0`
  have h5 := hmean c
  have h6 := hmean (c + k)
  rw [sub_self, zero_div, mul_zero, zero_add] at h5
  rw [add_sub_cancel_left, div_self hk.ne', mul_one] at h6
  apply hs
  rw [hα] at h5 h6
  linarith

/-- **Lemma 3, `s̃ ≠ 0`.** Every linear equilibrium is pooling or revealing. -/
theorem Std.lemma3_ne (hs : G.sens ≠ 0) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsLinearEq a φ) :
    G.IsPooling a ∨ ∃ l, G.RevealingWith a φ l := by
  have := hG.prob
  have := hE.1.markov
  by_cases hpool : G.IsPooling a
  · exact Or.inl hpool
  right
  obtain ⟨α, β, p, q, hlin⟩ := hE.2
  obtain ⟨x1, x2, hx1, hx2, hlt⟩ := two_support hE.1.meas hpool
  have hx1I : x1 ∈ G.actionHull a := support_subset_hull a hx1
  have hx2I : x2 ∈ G.actionHull a := support_subset_hull a hx2
  have hIcc : Icc x1 x2 ⊆ G.actionHull a := Icc_subset_hull hx1I hx2I hlt.le
  set D := 1 + G.κ * α ^ 2 with hDdef
  have hD : 0 < D := by have := hG.κ_pos; positivity
  set k := 1 / D with hkdef
  have hk : 0 < k := by positivity
  set c := -(G.κ * p / 2 + G.κ * α * (β - G.norm)) / D with hcdef
  have hgs : ∀ z, G.gstar α β p z = k * z + c := fun z => gstar_eq α β p z hD.ne'
  have hnear := hG.nearest hE.1 hlin
  have hnear' : ∀ᵐ ω ∂G.P, a ω ∈ G.actionHull a ∧ ∀ y ∈ G.actionHull a,
      (a ω - (k * G.Z ω + c)) ^ 2 ≤ (y - (k * G.Z ω + c)) ^ 2 :=
    hnear.mono fun ω hω => by rw [← hgs]; exact hω
  -- interior: the action reveals `Z` on `(x1, x2)`
  have hint_ae : ∀ᵐ ω ∂G.P, (a ω ∈ Ioo x1 x2 ↔ k * G.Z ω + c ∈ Ioo x1 x2) ∧
      (a ω ∈ Ioo x1 x2 → a ω = k * G.Z ω + c) := by
    filter_upwards [hnear'] with ω hω
    have hiff := np_Ioo hω.2 hx1I hx2I hIcc
    exact ⟨hiff, fun h => np_eq hω.2 (hIcc (Ioo_subset_Icc_self (hiff.1 h)))⟩
  have hpost := hG.ae_eq_postK_on hE.1 hk.ne' measurableSet_Ioo hint_ae
  have hUpos : 0 < G.P.map (fun ω => k * G.Z ω + c) (Ioo x1 x2) := by
    rw [hG.map_aff]
    exact gauss_pos_Ioo (hG.aff_var_ne hk.ne') hlt
  obtain ⟨e1, e2, e3, e4⟩ :=
    hG.ident hk.ne' hUpos hpost (fun x hx => hlin x (hIcc (Ioo_subset_Icc_self hx)))
  have hmeanall : ∀ x, G.sens * ((x - c) / k) + G.residMean = α * x + β := by
    intro x
    rw [e1, e2]
    field_simp
    ring
  have hν'g := hG.map_aff k c
  -- the support is unbounded above
  have hnab : ¬ BddAbove (G.P.map a).support := by
    intro hb
    set hi := sSup (G.P.map a).support
    have hhiS : hi ∈ (G.P.map a).support := Measure.isClosed_support.csSup_mem ⟨x1, hx1⟩ hb
    have hhiI : hi ∈ G.actionHull a := support_subset_hull a hhiS
    have hub : ∀ y ∈ G.actionHull a, y ≤ hi := fun y hy =>
      convexHull_min (fun s hs => le_csSup hb hs) (convex_Iic hi) hy
    have hx1hi : x1 < hi := lt_of_lt_of_le hlt (le_csSup hb hx2)
    have hIcc' : Icc x1 hi ⊆ G.actionHull a := Icc_subset_hull hx1I hhiI hx1hi.le
    have hae : ∀ᵐ ω ∂G.P, a ω = hi ↔ k * G.Z ω + c ∈ Ici hi := by
      filter_upwards [hnear'] with ω hω
      exact np_top hω.2 hx1I hhiI hx1hi hIcc' hub hω.1
    refine hG.atom_contra hE.1 hk hmeanall hs (hlin hi hhiI).2.1 measurableSet_Ici hae ?_
    rw [hν'g]
    exact (gauss_setIntegral_Ici_pos (hG.aff_var_ne hk.ne') hi).ne'
  -- the support is unbounded below
  have hnbb : ¬ BddBelow (G.P.map a).support := by
    intro hb
    set lo := sInf (G.P.map a).support
    have hloS : lo ∈ (G.P.map a).support := Measure.isClosed_support.csInf_mem ⟨x1, hx1⟩ hb
    have hloI : lo ∈ G.actionHull a := support_subset_hull a hloS
    have hlb : ∀ y ∈ G.actionHull a, lo ≤ y := fun y hy =>
      convexHull_min (fun s hs => csInf_le hb hs) (convex_Ici lo) hy
    have hlox2 : lo < x2 := lt_of_le_of_lt (csInf_le hb hx1) hlt
    have hIcc' : Icc lo x2 ⊆ G.actionHull a := Icc_subset_hull hloI hx2I hlox2.le
    have hae : ∀ᵐ ω ∂G.P, a ω = lo ↔ k * G.Z ω + c ∈ Iic lo := by
      filter_upwards [hnear'] with ω hω
      exact np_bot hω.2 hx2I hloI hlox2 hIcc' hlb hω.1
    refine hG.atom_contra hE.1 hk hmeanall hs (hlin lo hloI).2.1 measurableSet_Iic hae ?_
    rw [hν'g]
    exact (gauss_setIntegral_Iic_neg (hG.aff_var_ne hk.ne') lo).ne
  -- hence `I(h) = ℝ` and `a = k Z + c` a.s.
  have hIuniv : ∀ y, y ∈ G.actionHull a := by
    intro y
    obtain ⟨s1, hs1, hs1y⟩ := not_bddBelow_iff.1 hnbb y
    obtain ⟨s2, hs2, hs2y⟩ := not_bddAbove_iff.1 hnab y
    exact Icc_subset_hull (support_subset_hull a hs1) (support_subset_hull a hs2)
      (hs1y.le.trans hs2y.le) ⟨hs1y.le, hs2y.le⟩
  have ha : a =ᵐ[G.P] fun ω => k * G.Z ω + c :=
    hnear'.mono fun ω hω => np_eq hω.2 (hIuniv _)
  -- algebra: `c = (1 - k) E Z` and the root equation
  have hm := hG.residMean_eq
  have hsk : G.sens = α * k := by rw [e1]; field_simp
  have hc1 : c * D = -(G.κ * α * (β - G.norm)) := by
    rw [hcdef, e3]
    field_simp
    ring
  have hβ : β - G.norm = -(α * k) * G.meanZ - α * c := by
    rw [e2, hm, hsk]
    field_simp
    ring
  have hkD : k * D = 1 := by rw [hkdef]; field_simp
  have hc : c = (1 - k) * G.meanZ := by
    rw [hβ] at hc1
    have : c * (D - G.κ * α ^ 2) = G.κ * α ^ 2 * k * G.meanZ := by linear_combination hc1
    rw [hDdef, add_sub_cancel_right, mul_one] at this
    rw [this]
    have : G.κ * α ^ 2 = D - 1 := by rw [hDdef]; ring
    rw [this]
    linear_combination G.meanZ * hkD
  have hroot : k ^ 2 - k + G.κ * G.sens ^ 2 = 0 := by
    rw [hsk]
    have : G.κ * α ^ 2 = D - 1 := by rw [hDdef]; ring
    linear_combination k ^ 2 * this + k * hkD
  refine ⟨k, hG.revealingWith_of hE hk hroot (ha.mono fun ω hω => ?_)⟩
  rw [hω, hc]
  ring

/-- **Lemma 3, `s̃ = 0`.** A signaling equilibrium plays `a = Z` a.s. (requires `Z` measurable). -/
theorem Std.lemma3_zero (hZ : Measurable G.Z) (hs : G.sens = 0) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsSignalingEq a φ) : G.RevealingWith a φ 1 := by
  have := hG.prob
  have hroot : (1 : ℝ) ^ 2 - 1 + G.κ * G.sens ^ 2 = 0 := by rw [hs]; ring
  have hc := hG.rev_isLinearEq hZ one_pos hroot
  have hle := hE.2 _ _ hc
  rw [hG.exLoss_eq hE.1.1, hG.exLoss_affine hc.1 (ae_of_all _ fun _ => rfl)] at hle
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    ENNReal.ofReal_zero, zero_add] at hle
  have hfin : ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h0 : ∫⁻ ω, ENNReal.ofReal ((a ω - G.Z ω) ^ 2) ∂G.P = 0 := by
    have := ENNReal.le_of_add_le_add_right hfin (hle.trans (zero_add _).symm.le)
    exact le_antisymm this zero_le
  rw [lintegral_eq_zero_iff' (by
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hE.1.1.meas.aemeasurable.sub hG.aemZ).pow_const 2)))] at h0
  have ha : a =ᵐ[G.P] fun ω => G.meanZ + 1 * (G.Z ω - G.meanZ) := by
    filter_upwards [h0] with ω hω
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω
    have : (a ω - G.Z ω) ^ 2 = 0 := le_antisymm hω (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  exact hG.revealingWith_of hE.1 one_pos hroot ha

/-- **Lemma 3 (strong form)**, assuming `Z` is measurable. -/
theorem Std.lemma3_strong (hZ : Measurable G.Z) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsLinearEq a φ) (hSO : G.sens = 0 → G.IsSignalingEq a φ) :
    G.IsPooling a ∨ ∃ l, G.RevealingWith a φ l := by
  by_cases hs : G.sens = 0
  · exact Or.inr ⟨1, hG.lemma3_zero hZ hs (hSO hs)⟩
  · exact hG.lemma3_ne hs hE

end Std

end Game

end CC.LG
