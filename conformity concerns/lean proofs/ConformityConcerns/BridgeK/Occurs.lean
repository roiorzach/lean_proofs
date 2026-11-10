import ConformityConcerns.BridgeK.Info
import ConformityConcerns.BridgeK.Fubini
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Learning when `Σ_t → 0` almost surely

The Kalman mean `m_t` after the slots before `2t + 1` is `infoSigmaK t`-measurable and
`E((x_i - m_{t,i})²) = E(Σ_t)_{ii} → 0`, so `x_i` is (a.e. equal to) a function of all the
information, and Lévy's upward theorem gives `E(x_i | infoSigmaK t) → x_i` almost surely.
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

set_option warn.classDefReducibility false

variable (S₁ : M2) (D : Sched) (G Gγ : Measure ℝ) [IsProbabilityMeasure G]
  [IsProbabilityMeasure Gγ]

/-- `E((x_i - m_{k,i})²) = E((Cs k)_{ii})`. -/
lemma lintegral_err_sqK (hS₁ : S₁.PosSemidef) (hD : SchedOK D) (i : Fin 2) (k : ℕ) :
    ∫⁻ ω, ‖ω.1 i - km S₁ D (wts ω) (fun j => uS S₁ D j ω) k i‖ₑ ^ 2 ∂(lawK S₁ G Gγ) =
      ∫⁻ w, ENNReal.ofReal (Cs S₁ D w k i i) ∂(Measure.infinitePi fun _ : ℕ => G.prod Gγ) := by
  have hk : Measurable (fun ω : Ωk => km S₁ D (wts ω) (fun j => uS S₁ D j ω) k) :=
    (measurable_km S₁ D k).comp (measurable_wts.prodMk (measurable_uSeq S₁ D))
  have hm : Measurable (fun ω : Ωk =>
      ‖ω.1 i - km S₁ D (wts ω) (fun j => uS S₁ D j ω) k i‖ₑ ^ 2) :=
    (((Bridge.br_meas_coord measurable_fst i).sub (Bridge.br_meas_coord hk i)).enorm).pow_const 2
  rw [lintegral_lawK S₁ G Gγ _ hm]
  congr 1
  funext w
  have e : (fun p : E2 × (ℕ → E2) =>
      ‖((p.1, (p.2, w)) : Ωk).1 i - km S₁ D (wts ((p.1, (p.2, w)) : Ωk))
        (fun j => uS S₁ D j ((p.1, (p.2, w)) : Ωk)) k i‖ₑ ^ 2) =
      (fun p => ‖(errS S₁ D w p.1 p.2 k) i‖ₑ ^ 2) := by
    funext p
    simp only [errS, PiLp.sub_apply]
    rfl
  rw [e, ← lintegral_map (f := fun u : E2 => ‖u i‖ₑ ^ 2) (by fun_prop) (measurable_errS S₁ D w k),
    (kalman_fiberK S₁ D w hS₁ hD k).2, Bridge.lintegral_sq_mvG (Cs_psd S₁ D hD hS₁ w k)]

lemma tendsto_lintegral_SigK (i : Fin 2) (hbd : ∀ w t, SigK S₁ D w t i i ≤ S₁ i i)
    (hlim : ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => G.prod Gγ),
      Tendsto (fun t => SigK S₁ D w t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫⁻ w, ENNReal.ofReal (SigK S₁ D w t i i)
      ∂(Measure.infinitePi fun _ : ℕ => G.prod Gγ)) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence
    (μ := Measure.infinitePi fun _ : ℕ => G.prod Gγ)
    (F := fun t w => ENNReal.ofReal (SigK S₁ D w t i i)) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal (S₁ i i))
    (fun t => ENNReal.measurable_ofReal.comp
      (Bridge.br_meas_entry (measurable_SigK S₁ D t) i i))
    (fun t => Eventually.of_forall fun w => ENNReal.ofReal_le_ofReal (hbd w t))
    (by simp)
    (by
      filter_upwards [hlim] with w hw
      have h1 := ((continuous_id.matrix_elem i i).tendsto 0).comp hw
      have h2 := ENNReal.tendsto_ofReal h1
      simpa using h2)
  simpa using h

lemma k_limUnder_sm {α : Type*} {m : MeasurableSpace α} {f : ℕ → α → ℝ}
    (hf : ∀ k, StronglyMeasurable[m] (f k)) :
    StronglyMeasurable[m] (fun x => limUnder atTop (fun k => f k x)) := by
  let _ := m
  exact StronglyMeasurable.limUnder hf

/-- **Learning.** If `Σ_t → 0` for almost every weight path (and `Σ_t` stays below `Σ₁` on the
diagonal), the posterior mean of `x_i` converges to `x_i` almost surely. -/
theorem occurs_coreK (hS₁ : S₁.PosSemidef) (hD : SchedOK D) (i : Fin 2)
    (hbd : ∀ w t, SigK S₁ D w t i i ≤ S₁ i i)
    (hlim : ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => G.prod Gγ),
      Tendsto (fun t => SigK S₁ D w t) atTop (𝓝 0)) :
    ∀ᵐ ω ∂(lawK S₁ G Gγ), Tendsto (fun t => (lawK S₁ G Gγ)[fun ω => ω.1 i | infoSigmaK S₁ D t] ω)
      atTop (𝓝 (ω.1 i)) := by
  set P := lawK S₁ G Gγ with hP
  let mi : ℕ → Ωk → ℝ := fun t ω => km S₁ D (wts ω) (fun j => uS S₁ D j ω) (2 * t + 1) i
  have hmi_info : ∀ t, Measurable[infoSigmaK S₁ D t] (mi t) := fun t =>
    meas_info_of_dep S₁ D t (fun p => km S₁ D p.1 p.2 (2 * t + 1) i)
      (Bridge.br_meas_coord (measurable_km S₁ D (2 * t + 1)) i)
      (fun _ _ _ _ h1 h2 => by
        simp only
        rw [km_congr S₁ D (fun s hs => h1 s (by omega)) h2])
  have hmi : ∀ t, Measurable (mi t) := fun t =>
    (hmi_info t).mono (infoSigmaK_le S₁ D t) le_rfl
  have hx : Measurable (fun ω : Ωk => ω.1 i) := Bridge.br_meas_coord measurable_fst i
  -- convergence in `L²`, hence in measure
  have hTM : TendstoInMeasure P mi atTop (fun ω => ω.1 i) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero ?_
    have e : ∀ t, eLpNorm (mi t - fun ω => ω.1 i) 2 P =
        (∫⁻ w, ENNReal.ofReal (SigK S₁ D w t i i)
          ∂(Measure.infinitePi fun _ : ℕ => G.prod Gγ)) ^ (1 / (2 : ℝ)) := by
      intro t
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        ((hmi t).sub hx).aestronglyMeasurable]
      have h2 := lintegral_err_sqK S₁ D G Gγ hS₁ hD i (2 * t + 1)
      simp only [Cs_odd] at h2
      rw [← h2]
      congr 1
      refine lintegral_congr fun ω => ?_
      simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
      rw [enorm_sub_rev]
      norm_cast
    simp_rw [e]
    have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp
      (tendsto_lintegral_SigK S₁ D G Gγ i hbd hlim)
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  obtain ⟨ns, -, hae⟩ := hTM.exists_seq_tendsto_ae
  -- a version of `x_i` measurable for all the information
  let θh : Ωk → ℝ := fun ω => limUnder atTop (fun k => mi (ns k) ω)
  have hθh_sm : StronglyMeasurable[⨆ t, infoSigmaK S₁ D t] θh :=
    k_limUnder_sm fun k => ((hmi_info (ns k)).mono (le_iSup (infoSigmaK S₁ D) (ns k))
      le_rfl).stronglyMeasurable
  have hθh_ae : θh =ᵐ[P] fun ω => ω.1 i := by
    filter_upwards [hae] with ω h
    exact h.limUnder_eq
  have hint : Integrable θh P := (integrable_coord_lawK S₁ G Gγ i).congr hθh_ae.symm
  have h1 := hint.tendsto_ae_condExp (ℱ := infoFiltK S₁ D) hθh_sm
  have h2 : ∀ t, P[fun ω => ω.1 i | infoSigmaK S₁ D t] =ᵐ[P] P[θh | infoFiltK S₁ D t] :=
    fun t => condExp_congr_ae hθh_ae.symm
  filter_upwards [h1, ae_all_iff.2 h2, hθh_ae] with ω a b c
  rw [← c]
  exact a.congr (fun t => (b t).symm)

end CC.BridgeK
