import ConformityConcerns.LearnTheta.Defs
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Auxiliary lemmas for the Bayes formula `mfun`

Lebesgue-integral identities behind `m(x | h) = E(v² | ṽ = x, h)` when `v` has density `ψ`
and is independent of `(h, Y)`, and `ṽ = v + Y`.
-/

namespace CC.LearnTheta.MVerAux

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {ψ : ℝ → ℝ}

/-- Change of variables `x = u + y` in the inner integral, then Tonelli. -/
lemma lintegral_shift (hψ : Measurable ψ) (μ : Measure ℝ) [SFinite μ] {w : ℝ × ℝ → ℝ≥0∞}
    (hw : Measurable w) :
    ∫⁻ y, ∫⁻ u, ENNReal.ofReal (ψ u) * w (u + y, y) ∂volume ∂μ =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ψ (x - y)) * w (x, y) ∂μ ∂volume := by
  have h1 : ∀ y, ∫⁻ u, ENNReal.ofReal (ψ u) * w (u + y, y) ∂volume =
      ∫⁻ x, ENNReal.ofReal (ψ (x - y)) * w (x, y) ∂volume := by
    intro y
    have := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun x => ENNReal.ofReal (ψ (x - y)) * w (x, y)) y
    simpa only [add_sub_cancel_right] using this
  simp_rw [h1]
  have hm : Measurable (Function.uncurry fun (y x : ℝ) => ENNReal.ofReal (ψ (x - y)) * w (x, y)) :=
    (ENNReal.measurable_ofReal.comp (hψ.comp (measurable_snd.sub measurable_fst))).mul
      (hw.comp (measurable_snd.prodMk measurable_fst))
  exact lintegral_lintegral_swap hm.aemeasurable

/-- The numerator `∫ (x-y)² ψ(x-y) dμ(y)` is finite for almost every `x`. -/
lemma ae_numer_ne_top (hψ : Measurable ψ) (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ∫⁻ y, ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2) ∂μ ≠ ∞ := by
  have hmp : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (ψ (p.1 - p.2)) * ENNReal.ofReal ((p.1 - p.2) ^ 2) :=
    (ENNReal.measurable_ofReal.comp (hψ.comp (measurable_fst.sub measurable_snd))).mul
      (ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).pow_const 2))
  have hmeas : Measurable fun x =>
      ∫⁻ y, ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2) ∂μ :=
    hmp.lintegral_prod_right'
  have hw : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 - p.2) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).pow_const 2)
  have heq := lintegral_shift hψ μ hw
  simp only [add_sub_cancel_right] at heq
  have hG : ∫⁻ u, ENNReal.ofReal (ψ u) * ENNReal.ofReal (u ^ 2) =
      ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂vLaw ψ := by
    rw [vLaw, lintegral_withDensity_eq_lintegral_mul _
      (show Measurable fun x => ENNReal.ofReal (ψ x) from ENNReal.measurable_ofReal.comp hψ)
      (show Measurable fun u : ℝ => ENNReal.ofReal (u ^ 2) from
        ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2))]
    rfl
  have hfin : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2) ∂μ
      ∂volume ≠ ∞ := by
    rw [← heq, hG, lintegral_const, measure_univ, mul_one]
    exact hv2.lintegral_lt_top.ne
  filter_upwards [ae_lt_top hmeas hfin] with x hx using hx.ne

/-- Where the numerator is finite, `m(x) · ∫ψ(x-y)dμ(y) = ∫(x-y)²ψ(x-y)dμ(y)`. -/
lemma ofReal_mfun_mul (hψ : Measurable ψ) (hψpos : ∀ x, 0 < ψ x) {C : ℝ}
    (hψb : ∀ x, ψ x ≤ C) (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ)
    (hN : ∫⁻ y, ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2) ∂μ ≠ ∞) :
    ENNReal.ofReal (mfun ψ μ x) * ∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ =
      ∫⁻ y, ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2) ∂μ := by
  have hmψ : Measurable fun y => ψ (x - y) := hψ.comp (measurable_const.sub measurable_id)
  have hNeq : ∫ y, (x - y) ^ 2 * ψ (x - y) ∂μ =
      (∫⁻ y, ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      refine lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
    · exact Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (hψpos _).le
    · exact (((measurable_const.sub measurable_id).pow_const 2).mul hmψ).aestronglyMeasurable
  have hDeq : ∫ y, ψ (x - y) ∂μ = (∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · exact Eventually.of_forall fun y => (hψpos _).le
    · exact hmψ.aestronglyMeasurable
  have hDl_fin : ∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (?_ : ∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ ≤ ENNReal.ofReal C)
    calc ∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ ≤ ∫⁻ _, ENNReal.ofReal C ∂μ :=
          lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hψb _)
      _ = ENNReal.ofReal C := by simp
  have hDl_pos : ∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ ≠ 0 := by
    intro h0
    rw [lintegral_eq_zero_iff (f := fun y => ENNReal.ofReal (ψ (x - y)))
      (ENNReal.measurable_ofReal.comp hmψ)] at h0
    obtain ⟨y, hy⟩ := h0.exists
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hy
    exact absurd hy (not_le.2 (hψpos _))
  have hD : 0 < (∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ).toReal :=
    ENNReal.toReal_pos hDl_pos hDl_fin
  unfold mfun
  rw [hNeq, hDeq]
  calc ENNReal.ofReal ((∫⁻ y, ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2) ∂μ).toReal
          / (∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ).toReal) * ∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ
        = ENNReal.ofReal ((∫⁻ y, ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2) ∂μ).toReal
          / (∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ).toReal) *
            ENNReal.ofReal (∫⁻ y, ENNReal.ofReal (ψ (x - y)) ∂μ).toReal := by
          rw [ENNReal.ofReal_toReal hDl_fin]
      _ = _ := by
          rw [← ENNReal.ofReal_mul (div_nonneg ENNReal.toReal_nonneg hD.le),
            div_mul_cancel₀ _ hD.ne', ENNReal.ofReal_toReal hN]

/-- For each history, the two triple integrals agree (the core of the Bayes computation). -/
lemma inner_eq (hψ : Measurable ψ) (hψpos : ∀ x, 0 < ψ x) {C : ℝ} (hψb : ∀ x, ψ x ≤ C)
    (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : Measurable (mfun ψ μ)) {b : ℝ → ℝ≥0∞} (hb : Measurable b) :
    ∫⁻ y, ∫⁻ u, ENNReal.ofReal (ψ u) * (b (u + y) * ENNReal.ofReal (u ^ 2)) ∂volume ∂μ =
      ∫⁻ y, ∫⁻ u, ENNReal.ofReal (ψ u) * (b (u + y) * ENNReal.ofReal (mfun ψ μ (u + y)))
        ∂volume ∂μ := by
  have h1 := lintegral_shift hψ μ (w := fun p => b p.1 * ENNReal.ofReal ((p.1 - p.2) ^ 2))
    ((hb.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).pow_const 2)))
  have h2 := lintegral_shift hψ μ (w := fun p => b p.1 * ENNReal.ofReal (mfun ψ μ p.1))
    ((hb.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp (hm.comp measurable_fst)))
  simp only [add_sub_cancel_right] at h1 h2
  rw [h1, h2]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_numer_ne_top hψ hv2 μ] with x hx
  have hmψ : Measurable fun y => ENNReal.ofReal (ψ (x - y)) :=
    ENNReal.measurable_ofReal.comp (hψ.comp (measurable_const.sub measurable_id))
  have e1 : ∀ y, ENNReal.ofReal (ψ (x - y)) * (b x * ENNReal.ofReal ((x - y) ^ 2)) =
      b x * (ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2)) := fun y => by ring
  simp_rw [e1]
  have hm2 : Measurable fun y => ENNReal.ofReal (ψ (x - y)) * ENNReal.ofReal ((x - y) ^ 2) :=
    hmψ.mul (ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_id).pow_const 2))
  rw [lintegral_const_mul _ hm2, lintegral_mul_const _ hmψ, ← ofReal_mfun_mul hψ hψpos hψb μ x hx]
  ring

/-- The joint law of `((H, Y), V)` with `V` independent of `(H, Y)` and of law `vLaw ψ`. -/
lemma lintegral_joint {β Ω' : Type*} [MeasurableSpace β] [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {H : Ω' → β} {Y V : Ω' → ℝ} (hH : Measurable H)
    (hY : Measurable Y) (hV : Measurable V) (hind : IndepFun (fun ω => (H ω, Y ω)) V P)
    (hVlaw : P.map V = vLaw ψ) (hψ : Measurable ψ) {f : (β × ℝ) × ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ ω, f ((H ω, Y ω), V ω) ∂P =
      ∫⁻ h, ∫⁻ y, ∫⁻ u, ENNReal.ofReal (ψ u) * f ((h, y), u) ∂volume
        ∂(condDistrib Y H P h) ∂(P.map H) := by
  have hmap3 := (indepFun_iff_map_prod_eq_prod_map_map (hH.prodMk hY).aemeasurable
    hV.aemeasurable).1 hind
  rw [← compProd_map_condDistrib hH.aemeasurable hY.aemeasurable] at hmap3
  calc ∫⁻ ω, f ((H ω, Y ω), V ω) ∂P
      = ∫⁻ p, f p ∂(P.map (fun ω => ((H ω, Y ω), V ω))) :=
        (lintegral_map hf ((hH.prodMk hY).prodMk hV)).symm
    _ = ∫⁻ q, ∫⁻ u, f (q, u) ∂(P.map V) ∂(P.map H ⊗ₘ condDistrib Y H P) := by
        rw [hmap3, lintegral_prod _ hf.aemeasurable]
    _ = ∫⁻ h, ∫⁻ y, ∫⁻ u, f ((h, y), u) ∂(P.map V) ∂(condDistrib Y H P h) ∂(P.map H) :=
        Measure.lintegral_compProd hf.lintegral_prod_right'
    _ = _ := by
        refine lintegral_congr fun h => lintegral_congr fun y => ?_
        rw [hVlaw, vLaw, lintegral_withDensity_eq_lintegral_mul _
          (show Measurable fun x => ENNReal.ofReal (ψ x) from ENNReal.measurable_ofReal.comp hψ)
          (show Measurable fun u => f ((h, y), u) from hf.comp measurable_prodMk_left)]
        rfl

end CC.LearnTheta.MVerAux
