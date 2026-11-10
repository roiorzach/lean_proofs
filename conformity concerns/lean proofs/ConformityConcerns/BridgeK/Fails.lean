import ConformityConcerns.BridgeK.Info
import ConformityConcerns.BridgeK.Fubini
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# No learning when the public signals stop

If, along almost every weight path, all slots from some `K` on are uninformative and
`(Cs K)_{ii} > 0`, then `E(x_i | all information)` differs from `x_i` almost surely: along such a
path the information is `(w, u_0, …, u_{K-1})`, and `x_i` is the Kalman mean (a function of these
signals) plus an independent `N(0, (Cs K)_{ii})` error.
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

set_option warn.classDefReducibility false

variable (S₁ : M2) (D : Sched) (G Gγ : Measure ℝ) [IsProbabilityMeasure G]
  [IsProbabilityMeasure Gγ]

/-- **No learning.** -/
theorem fails_coreK (hS₁ : S₁.PosSemidef) (hD : SchedOK D) (i : Fin 2)
    (hfin : ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => G.prod Gγ), ∃ K,
      (∀ k, K ≤ k → ld S₁ D w k = (0, 0)) ∧ 0 < Cs S₁ D w K i i) :
    lawK S₁ G Gγ {ω | (lawK S₁ G Gγ)[fun ω => ω.1 i | ⨆ t, infoSigmaK S₁ D t] ω = ω.1 i} = 0 := by
  set L := (lawK S₁ G Gγ)[fun ω => ω.1 i | ⨆ t, infoSigmaK S₁ D t] with hLdef
  have hsm : StronglyMeasurable[⨆ t, infoSigmaK S₁ D t] L := stronglyMeasurable_condExp
  have hsm' := hsm.mono (iSup_infoSigmaK_le S₁ D)
  obtain ⟨g, hg, hLg⟩ := hsm'.exists_eq_measurable_comp
  have hΓ : Measurable (fun ω : Ωk => (wts ω, fun k => uS S₁ D k ω)) :=
    measurable_wts.prodMk (measurable_uSeq S₁ D)
  have hset : {ω | L ω = ω.1 i} = {ω : Ωk | g (wts ω, fun k => uS S₁ D k ω) = ω.1 i} := by
    rw [hLg]; rfl
  have hB : MeasurableSet {ω : Ωk | g (wts ω, fun k => uS S₁ D k ω) = ω.1 i} :=
    measurableSet_eq_fun (hg.measurable.comp hΓ) (Bridge.br_meas_coord measurable_fst i)
  rw [hset, measure_lawK S₁ G Gγ hB]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hfin] with w hw
  obtain ⟨K, hK, hpos⟩ := hw
  have hsig : ∀ p : E2 × (ℕ → E2), sigSeq S₁ D w p.1 p.2 = YS S₁ D w p.1 p.2 K := by
    intro p
    funext k
    simp only [YS, Bridge.trunc]
    split_ifs with h
    · rfl
    · simp only [sigSeq, sigF, hK k (not_lt.1 h), ZG_zero]
  let H : (ℕ → ℝ) → ℝ := fun y => g (w, y) - km S₁ D w y K i
  have hH : Measurable H :=
    (hg.measurable.comp (measurable_const.prodMk measurable_id)).sub
      (Bridge.br_meas_coord (measurable_km_fix S₁ D w K) i)
  have hset2 : (fun p : E2 × (ℕ → E2) => ((p.1, (p.2, w)) : Ωk)) ⁻¹'
      {ω : Ωk | g (wts ω, fun k => uS S₁ D k ω) = ω.1 i} =
      {p | (errS S₁ D w p.1 p.2 K) i = H (YS S₁ D w p.1 p.2 K)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    change g (w, sigSeq S₁ D w p.1 p.2) = p.1 i ↔ _
    rw [hsig p]
    simp only [errS, PiLp.sub_apply, H, ← hsig p]
    rw [← km_YS S₁ D w p.1 p.2 K, ← hsig p]
    constructor <;> intro h <;> linarith
  rw [hset2]
  obtain ⟨K1, K2⟩ := kalman_fiberK S₁ D w hS₁ hD K
  have hev : Measurable (fun u : E2 => u i) := Bridge.br_meas_coord measurable_id i
  refine Bridge.br_prob_eq_zero_of_indep (hev.comp (measurable_errS S₁ D w K))
    (hH.comp (measurable_YS S₁ D w K)) (K1.comp hev hH) ?_
  intro y
  have e : (fun p : E2 × (ℕ → E2) => (errS S₁ D w p.1 p.2 K) i) =
      (fun u : E2 => u i) ∘ (fun p => errS S₁ D w p.1 p.2 K) := rfl
  rw [e, ← Measure.map_map hev (measurable_errS S₁ D w K), K2,
    (measurePreserving_eval_multivariateGaussian (Cs_psd S₁ D hD hS₁ w K)).map_eq]
  have := nullSingletonClass_gaussianReal (μ := (0 : E2) i)
    (v := (Cs S₁ D w K i i).toNNReal) (by simpa using hpos)
  exact measure_singleton y

end CC.BridgeK
