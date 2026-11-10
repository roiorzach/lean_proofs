import ConformityConcerns.LearnTheta.MVerAux.CondExp
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The period game at a fixed history: the type distribution and the Bayes formula

At a history where the public belief about `Y_t` is `η`, the type `ṽ_t = v_t + Y_t` has law
`η ∗ G` with `G = vLaw ψ`. This file shows that `η ∗ G` has the continuous, everywhere-positive
density `x ↦ ∫ ψ(x - y) dη(y)`, that `G` is symmetric when `ψ` is even, that `mfun ψ η` is a
version of `E(v² | v + Y)` on the product space `η ⊗ G`, and that it is `η ∗ G`-integrable.
-/

namespace CC.LearnTheta.ExAux

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {ψ : ℝ → ℝ}

/-- The density of `η ∗ G`. -/
noncomputable def convDens (ψ : ℝ → ℝ) (η : Measure ℝ) (x : ℝ) : ℝ := ∫ y, ψ (x - y) ∂η

lemma conv_vLaw_lintegral (hψ : Measurable ψ) (η : Measure ℝ) [IsProbabilityMeasure η]
    [IsProbabilityMeasure (vLaw ψ)] :
    η.conv (vLaw ψ) =
      volume.withDensity (fun x => ∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂η) := by
  ext A hA
  have hAi : Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hA
  have hshift := MVerAux.lintegral_shift hψ η
    (w := fun p : ℝ × ℝ => A.indicator (1 : ℝ → ℝ≥0∞) p.1) (hAi.comp measurable_fst)
  simp only at hshift
  have hmψ : ∀ x, Measurable fun y => ENNReal.ofReal (ψ (x - y)) := fun x =>
    ENNReal.measurable_ofReal.comp (hψ.comp (measurable_const.sub measurable_id))
  rw [← lintegral_indicator_one hA, Measure.lintegral_conv hAi]
  calc ∫⁻ x, ∫⁻ y, A.indicator 1 (x + y) ∂vLaw ψ ∂η
      = ∫⁻ y, ∫⁻ u, ENNReal.ofReal (ψ u) * A.indicator 1 (u + y) ∂volume ∂η := by
        refine lintegral_congr fun y => ?_
        rw [vLaw, lintegral_withDensity_eq_lintegral_mul _
          (show Measurable fun x => ENNReal.ofReal (ψ x) from ENNReal.measurable_ofReal.comp hψ)
          (show Measurable fun u => A.indicator (1 : ℝ → ℝ≥0∞) (y + u) from
            hAi.comp (measurable_const_add y))]
        refine lintegral_congr fun u => ?_
        simp only [Pi.mul_apply]
        rw [add_comm y u]
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ψ (x - y)) * A.indicator 1 x ∂η ∂volume := hshift
    _ = _ := by
        rw [withDensity_apply _ hA, ← lintegral_indicator hA]
        refine lintegral_congr fun x => ?_
        rw [lintegral_mul_const _ (hmψ x)]
        by_cases hx : x ∈ A <;> simp [hx]

lemma integrable_psi_shift (hψ : Measurable ψ) (hψpos : ∀ x, 0 < ψ x) {C : ℝ}
    (hψb : ∀ x, ψ x ≤ C) (η : Measure ℝ) [IsProbabilityMeasure η] (x : ℝ) :
    Integrable (fun y => ψ (x - y)) η :=
  Integrable.of_bound (hψ.comp (measurable_const.sub measurable_id)).aestronglyMeasurable C
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (hψpos _)]; exact hψb _)

lemma conv_vLaw_eq (hψ : Measurable ψ) (hψpos : ∀ x, 0 < ψ x) {C : ℝ} (hψb : ∀ x, ψ x ≤ C)
    (η : Measure ℝ) [IsProbabilityMeasure η] [IsProbabilityMeasure (vLaw ψ)] :
    η.conv (vLaw ψ) = volume.withDensity (fun x => ENNReal.ofReal (convDens ψ η x)) := by
  rw [conv_vLaw_lintegral hψ η]
  congr 1
  funext x
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_psi_shift hψ hψpos hψb η x)
    (Eventually.of_forall fun y => (hψpos _).le)).symm

lemma continuous_convDens (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x) {C : ℝ}
    (hψb : ∀ x, ψ x ≤ C) (η : Measure ℝ) [IsProbabilityMeasure η] :
    Continuous (convDens ψ η) :=
  continuous_of_dominated (bound := fun _ => C)
    (fun x => (hψc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (hψpos _)]; exact hψb _)
    (integrable_const C)
    (Eventually.of_forall fun y => hψc.comp (continuous_id.sub continuous_const))

lemma convDens_pos (hψ : Measurable ψ) (hψpos : ∀ x, 0 < ψ x) {C : ℝ} (hψb : ∀ x, ψ x ≤ C)
    (η : Measure ℝ) [IsProbabilityMeasure η] (x : ℝ) : 0 < convDens ψ η x := by
  unfold convDens
  rw [integral_pos_iff_support_of_nonneg (fun y => (hψpos _).le)
    (integrable_psi_shift hψ hψpos hψb η x)]
  have hs : Function.support (fun y => ψ (x - y)) = Set.univ :=
    Set.eq_univ_of_forall fun y => (hψpos _).ne'
  rw [hs, measure_univ]
  exact one_pos

/-- If `ψ` is even, the law `G` of `v` is symmetric. -/
lemma vLaw_map_neg (hψ : Measurable ψ) (hsymm : ∀ x, ψ (-x) = ψ x) :
    (vLaw ψ).map (fun x => -x) = vLaw ψ := by
  ext A hA
  have hmf : Measurable fun x => ENNReal.ofReal (ψ x) := ENNReal.measurable_ofReal.comp hψ
  rw [Measure.map_apply measurable_neg hA, vLaw, withDensity_apply _ (measurable_neg hA),
    withDensity_apply _ hA, ← lintegral_indicator (measurable_neg hA), ← lintegral_indicator hA,
    ← lintegral_neg_eq_self (μ := volume) (A.indicator fun x => ENNReal.ofReal (ψ x))]
  refine lintegral_congr fun x => ?_
  by_cases hx : -x ∈ A
  · simp [Set.indicator_of_mem, hx, hsymm]
  · simp [hx]

/-- The product space `η ⊗ G`: Fubini and the density of `G`. -/
lemma lintegral_prod_vLaw (hψ : Measurable ψ) (η : Measure ℝ) [IsProbabilityMeasure η]
    [IsProbabilityMeasure (vLaw ψ)] {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(η.prod (vLaw ψ)) =
      ∫⁻ y, ∫⁻ u, ENNReal.ofReal (ψ u) * f (y, u) ∂volume ∂η := by
  rw [lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [vLaw, lintegral_withDensity_eq_lintegral_mul _
    (show Measurable fun x => ENNReal.ofReal (ψ x) from ENNReal.measurable_ofReal.comp hψ)
    (show Measurable fun u => f (y, u) from hf.comp measurable_prodMk_left)]
  rfl

/-- `m(v + Y)` is a version of `E(v² | v + Y)` when `Y ~ η` and `v ~ G` are independent. -/
theorem condExp_prod_eq_mfun (hψ : Measurable ψ) (hψpos : ∀ x, 0 < ψ x) {C : ℝ}
    (hψb : ∀ x, ψ x ≤ C) (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (η : Measure ℝ) [IsProbabilityMeasure η] [IsProbabilityMeasure (vLaw ψ)]
    (hmf : Measurable (mfun ψ η)) :
    (fun p : ℝ × ℝ => mfun ψ η (p.2 + p.1)) =ᵐ[η.prod (vLaw ψ)]
      (η.prod (vLaw ψ))[fun p => p.2 ^ 2 |
        MeasurableSpace.comap (fun p : ℝ × ℝ => p.2 + p.1) inferInstance] := by
  have hZ : Measurable fun p : ℝ × ℝ => p.2 + p.1 := measurable_snd.add measurable_fst
  have key : ∀ S : Set ℝ, MeasurableSet S →
      ∫⁻ p, S.indicator 1 (p.2 + p.1) * ENNReal.ofReal (p.2 ^ 2) ∂(η.prod (vLaw ψ)) =
        ∫⁻ p, S.indicator 1 (p.2 + p.1) * ENNReal.ofReal (mfun ψ η (p.2 + p.1))
          ∂(η.prod (vLaw ψ)) := by
    intro S hS
    have hSi : Measurable fun p : ℝ × ℝ => S.indicator (1 : ℝ → ℝ≥0∞) (p.2 + p.1) :=
      (measurable_one.indicator hS).comp hZ
    rw [lintegral_prod_vLaw hψ η
        (f := fun p => S.indicator 1 (p.2 + p.1) * ENNReal.ofReal (p.2 ^ 2))
        (hSi.mul (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const 2))),
      lintegral_prod_vLaw hψ η
        (f := fun p => S.indicator 1 (p.2 + p.1) * ENNReal.ofReal (mfun ψ η (p.2 + p.1)))
        (hSi.mul (ENNReal.measurable_ofReal.comp (hmf.comp hZ)))]
    exact MVerAux.inner_eq hψ hψpos hψb hv2 η hmf (measurable_one.indicator hS)
  have hgnn : ∀ p : ℝ × ℝ, 0 ≤ mfun ψ η (p.2 + p.1) := fun p => MVerAux.mfun_nonneg hψpos _ _
  have hgm : Measurable fun p : ℝ × ℝ => mfun ψ η (p.2 + p.1) := hmf.comp hZ
  have hsnd : (η.prod (vLaw ψ)).map Prod.snd = vLaw ψ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hfint : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (η.prod (vLaw ψ)) := by
    rw [← hsnd] at hv2
    exact hv2.comp_measurable measurable_snd
  have hgint : Integrable (fun p : ℝ × ℝ => mfun ψ η (p.2 + p.1)) (η.prod (vLaw ψ)) := by
    refine ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall hgnn)).2 ?_⟩
    have := key Set.univ MeasurableSet.univ
    simp only [Set.indicator_univ, Pi.one_apply, one_mul] at this
    rw [← this]
    exact hfint.lintegral_lt_top
  have hm : MeasurableSpace.comap (fun p : ℝ × ℝ => p.2 + p.1) inferInstance ≤
      (inferInstance : MeasurableSpace (ℝ × ℝ)) := hZ.comap_le
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hfint (fun s _ _ => hgint.integrableOn)
    (fun s hs _ => ?_) ?_
  · obtain ⟨S, hS, rfl⟩ := hs
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hgnn) hgm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun p : ℝ × ℝ => sq_nonneg p.2)
        (measurable_snd.pow_const 2).aestronglyMeasurable]
    congr 1
    rw [← lintegral_indicator (hZ hS), ← lintegral_indicator (hZ hS)]
    have e : ∀ φ : ℝ × ℝ → ℝ≥0∞, ∀ p, ((fun p : ℝ × ℝ => p.2 + p.1) ⁻¹' S).indicator φ p =
        S.indicator 1 (p.2 + p.1) * φ p := by
      intro φ p
      by_cases hp : p.2 + p.1 ∈ S
      · simp [Set.indicator_of_mem, hp]
      · simp [Set.indicator_of_notMem, hp]
    simp_rw [e]
    exact (key S hS).symm
  · exact (hmf.comp (comap_measurable _)).stronglyMeasurable.aestronglyMeasurable

/-- `m` is integrable under the type distribution `η ∗ G`: `∫ m d(η ∗ G) = ∫ v² dG`. -/
lemma integrable_mfun_conv (hψ : Measurable ψ) (hψpos : ∀ x, 0 < ψ x) {C : ℝ}
    (hψb : ∀ x, ψ x ≤ C) (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (η : Measure ℝ) [IsProbabilityMeasure η] [IsProbabilityMeasure (vLaw ψ)]
    (hmf : Measurable (mfun ψ η)) : Integrable (mfun ψ η) (η.conv (vLaw ψ)) := by
  refine ⟨hmf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (MVerAux.mfun_nonneg hψpos η))).2 ?_⟩
  have h := MVerAux.inner_eq hψ hψpos hψb hv2 η hmf (b := fun _ => 1) measurable_const
  simp only [one_mul] at h
  have hG : ∫⁻ u, ENNReal.ofReal (ψ u) * ENNReal.ofReal (u ^ 2) ∂volume =
      ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂(vLaw ψ) := by
    rw [vLaw, lintegral_withDensity_eq_lintegral_mul _
      (show Measurable fun x => ENNReal.ofReal (ψ x) from ENNReal.measurable_ofReal.comp hψ)
      (show Measurable fun u : ℝ => ENNReal.ofReal (u ^ 2) from
        ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2))]
    rfl
  rw [Measure.lintegral_conv (show Measurable fun x => ENNReal.ofReal (mfun ψ η x) from
    ENNReal.measurable_ofReal.comp hmf)]
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (mfun ψ η (x + y)) ∂vLaw ψ ∂η
      = ∫⁻ y, ∫⁻ u, ENNReal.ofReal (ψ u) * ENNReal.ofReal (mfun ψ η (u + y)) ∂volume ∂η := by
        refine lintegral_congr fun y => ?_
        rw [vLaw, lintegral_withDensity_eq_lintegral_mul _
          (show Measurable fun x => ENNReal.ofReal (ψ x) from ENNReal.measurable_ofReal.comp hψ)
          (show Measurable fun u => ENNReal.ofReal (mfun ψ η (y + u)) from
            ENNReal.measurable_ofReal.comp (hmf.comp (measurable_const_add y)))]
        refine lintegral_congr fun u => ?_
        simp only [Pi.mul_apply]
        rw [add_comm y u]
    _ = ∫⁻ y, ∫⁻ u, ENNReal.ofReal (ψ u) * ENNReal.ofReal (u ^ 2) ∂volume ∂η := h.symm
    _ = ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂(vLaw ψ) := by
        rw [hG, lintegral_const, measure_univ, mul_one]
    _ < ∞ := hv2.lintegral_lt_top

end CC.LearnTheta.ExAux
