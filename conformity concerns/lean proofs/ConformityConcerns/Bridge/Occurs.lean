import ConformityConcerns.Bridge.Fubini
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Learning when `Σ_t → 0` almost surely

The Kalman mean `m_t` is `infoSigma t`-measurable and `E((x_i - m_{t,i})²) = E(Σ_t)_{ii} → 0`, so
`x_i` is (a.e. equal to) a function of all the information, and Lévy's upward theorem gives
`E(x_i | infoSigma t) → x_i` almost surely.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

set_option warn.classDefReducibility false

variable (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]

/-- `E((x_i - m_{t,i})²) = E((Σ_t)_{ii})`. -/
lemma lintegral_err_sq (hS₁ : S₁.PosSemidef) (i : Fin 2) (t : ℕ) :
    ∫⁻ ω, ‖ω.1 i - kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t i‖ₑ ^ 2 ∂(lawG S₁ G) =
      ∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t i i) ∂(Measure.infinitePi fun _ : ℕ => G) := by
  have hk : Measurable (fun ω : Ωg => kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t) :=
    (measurable_kmean κ S₁ t).comp (measurable_gam.prodMk (measurable_obsSeq κ S₁))
  have hm : Measurable (fun ω : Ωg =>
      ‖ω.1 i - kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t i‖ₑ ^ 2) :=
    (((br_meas_coord measurable_fst i).sub (br_meas_coord hk i)).enorm).pow_const 2
  rw [lintegral_lawG S₁ G _ hm]
  congr 1
  funext γ
  have e : (fun p : E2 × (ℕ → E2) =>
      ‖((p.1, (p.2, γ)) : Ωg).1 i - kmean κ S₁ (gam ((p.1, (p.2, γ)) : Ωg))
        (fun s => obs κ S₁ s ((p.1, (p.2, γ)) : Ωg)) t i‖ₑ ^ 2) =
      (fun p => ‖(errF κ S₁ γ p.1 p.2 t) i‖ₑ ^ 2) := by
    funext p
    simp only [errF, PiLp.sub_apply]
    rfl
  rw [e, ← lintegral_map (f := fun u : E2 => ‖u i‖ₑ ^ 2) (by fun_prop) (measurable_errF κ S₁ γ t),
    (kalman_fiber κ S₁ γ hS₁ t).2, lintegral_sq_mvG (SigmaC_psd' (fun _ => κ) γ S₁ hS₁ t)]

lemma tendsto_lintegral_Sig (hS₁ : S₁.PosSemidef) (i : Fin 2)
    (hlim : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G),
      Tendsto (fun t => SigP κ S₁ γ t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t i i)
      ∂(Measure.infinitePi fun _ : ℕ => G)) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := Measure.infinitePi fun _ : ℕ => G)
    (F := fun t γ => ENNReal.ofReal (SigP κ S₁ γ t i i)) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal (S₁ i i))
    (fun t => ENNReal.measurable_ofReal.comp (br_meas_entry (measurable_SigP κ S₁ t) i i))
    (fun t => Eventually.of_forall fun γ => by
      refine ENNReal.ofReal_le_ofReal ?_
      fin_cases i
      · exact SigmaC_anti00 (κ := fun _ => κ) (γ := γ) hS₁ (Nat.zero_le t)
      · exact SigmaC_anti11 (κ := fun _ => κ) (γ := γ) hS₁ (Nat.zero_le t))
    (by simp)
    (by
      filter_upwards [hlim] with γ hγ
      have h1 := ((continuous_id.matrix_elem i i).tendsto 0).comp hγ
      have h2 := ENNReal.tendsto_ofReal h1
      simpa using h2)
  simpa using h

lemma br_limUnder_sm {α : Type*} {m : MeasurableSpace α} {f : ℕ → α → ℝ}
    (hf : ∀ k, StronglyMeasurable[m] (f k)) :
    StronglyMeasurable[m] (fun x => limUnder atTop (fun k => f k x)) := by
  let _ := m
  exact StronglyMeasurable.limUnder hf

/-- **Learning.** If `Σ_t → 0` for almost every weight path, the posterior mean of `x_i`
converges to `x_i` almost surely. -/
theorem occurs_core (hS₁ : S₁.PosSemidef) (i : Fin 2)
    (hlim : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G),
      Tendsto (fun t => SigP κ S₁ γ t) atTop (𝓝 0)) :
    ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ t] ω)
      atTop (𝓝 (ω.1 i)) := by
  set P := lawG S₁ G with hP
  let mi : ℕ → Ωg → ℝ := fun t ω => kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t i
  have hmi : ∀ t, Measurable (mi t) := fun t =>
    br_meas_coord ((measurable_kmean κ S₁ t).comp
      (measurable_gam.prodMk (measurable_obsSeq κ S₁))) i
  have hmi_info : ∀ t, Measurable[infoSigma κ S₁ t] (mi t) := fun t =>
    meas_info_of_dep κ S₁ t (fun p => kmean κ S₁ p.1 p.2 t i)
      (br_meas_coord (measurable_kmean κ S₁ t) i)
      (fun _ _ _ _ h1 h2 => by
        simp only
        rw [kmean_congr κ S₁ (fun s hs => h1 s hs.le) h2])
  have hx : Measurable (fun ω : Ωg => ω.1 i) := br_meas_coord measurable_fst i
  -- convergence in `L²`, hence in measure
  have hTM : TendstoInMeasure P mi atTop (fun ω => ω.1 i) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero ?_
    have e : ∀ t, eLpNorm (mi t - fun ω => ω.1 i) 2 P =
        (∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t i i)
          ∂(Measure.infinitePi fun _ : ℕ => G)) ^ (1 / (2 : ℝ)) := by
      intro t
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        ((hmi t).sub hx).aestronglyMeasurable, ← lintegral_err_sq κ S₁ G hS₁ i t]
      congr 1
      refine lintegral_congr fun ω => ?_
      simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
      rw [enorm_sub_rev]
      norm_cast
    simp_rw [e]
    have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp
      (tendsto_lintegral_Sig κ S₁ G hS₁ i hlim)
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  obtain ⟨ns, -, hae⟩ := hTM.exists_seq_tendsto_ae
  -- a version of `x_i` measurable for all the information
  let θh : Ωg → ℝ := fun ω => limUnder atTop (fun k => mi (ns k) ω)
  have hθh_sm : StronglyMeasurable[⨆ t, infoSigma κ S₁ t] θh :=
    br_limUnder_sm fun k => ((hmi_info (ns k)).mono (le_iSup (infoSigma κ S₁) (ns k))
      le_rfl).stronglyMeasurable
  have hθh_ae : θh =ᵐ[P] fun ω => ω.1 i := by
    filter_upwards [hae] with ω h
    exact h.limUnder_eq
  have hint : Integrable θh P := (integrable_coord_lawG S₁ G i).congr hθh_ae.symm
  have h1 := hint.tendsto_ae_condExp (ℱ := infoFilt κ S₁) hθh_sm
  have h2 : ∀ t, P[fun ω => ω.1 i | infoSigma κ S₁ t] =ᵐ[P] P[θh | infoFilt κ S₁ t] :=
    fun t => condExp_congr_ae hθh_ae.symm
  filter_upwards [h1, ae_all_iff.2 h2, hθh_ae] with ω a b c
  rw [← c]
  exact a.congr (fun t => (b t).symm)

end CC.Bridge
