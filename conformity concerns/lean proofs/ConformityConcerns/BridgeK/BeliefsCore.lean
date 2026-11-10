import ConformityConcerns.BridgeK.Info
import ConformityConcerns.BridgeK.Fubini
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Public beliefs are Gaussian (core)

Given the information at date `t` (`infoMap S₁ D t`: weights `w_0, …, w_t`, disclosures
`d_0, …, d_t`, observations `o_0, …, o_{t-1}`), the conditional law of `(θ, μ)` is `N(m_t, Σ_t)`
with `m_t` the Kalman mean before slot `2t + 1`: along each weight path, `x = (x - m_t) + m_t`
where `x - m_t ~ N(0, Σ_t)` is independent of the signals (`kalman_fiberK`).
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

set_option warn.classDefReducibility false

/-- The type of the information vector at date `t`. -/
abbrev InfoT (t : ℕ) := (Fin (t + 1) → ℝ × ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ)

variable (S₁ : M2) (D : Sched) (t : ℕ)

/-- The Kalman mean as a function of the information. -/
noncomputable def mtF (q : InfoT t) : E2 :=
  km S₁ D (recon t q).1 (recon t q).2 (2 * t + 1)

/-- `Σ_t` as a function of the information. -/
noncomputable def SgF (q : InfoT t) : M2 := SigK S₁ D (recon t q).1 t

lemma measurable_mtF : Measurable (mtF S₁ D t) :=
  (measurable_km S₁ D (2 * t + 1)).comp (measurable_recon t)

lemma measurable_SgF : Measurable (SgF S₁ D t) :=
  (measurable_SigK S₁ D t).comp (measurable_fst.comp (measurable_recon t))

/-- The candidate posterior `q ↦ N(m_t(q), Σ_t(q))`. -/
noncomputable def postKK : Kernel (InfoT t) E2 where
  toFun q := multivariateGaussian (mtF S₁ D t q) (SgF S₁ D t q)
  measurable' := measurable_multivariateGaussian.comp
    ((measurable_mtF S₁ D t).prodMk (measurable_SgF S₁ D t))

instance : IsMarkovKernel (postKK S₁ D t) :=
  ⟨fun q => by
    change IsProbabilityMeasure (multivariateGaussian (mtF S₁ D t q) (SgF S₁ D t q))
    infer_instance⟩

lemma postKK_apply (q : InfoT t) :
    postKK S₁ D t q = multivariateGaussian (mtF S₁ D t q) (SgF S₁ D t q) := rfl

/-- The information along the weight path `w`, as a function of the slot signals. -/
def Jinfo (w : ℕ → ℝ × ℝ) (y : ℕ → ℝ) : InfoT t :=
  ((fun i : Fin (t + 1) => w i), (fun i : Fin (t + 1) => y (2 * i)),
    (fun i : Fin t => y (2 * i + 1)))

lemma measurable_Jinfo (w : ℕ → ℝ × ℝ) : Measurable (Jinfo t w) :=
  measurable_const.prodMk
    ((Measurable.of_eval fun (i : Fin (t + 1)) => measurable_pi_apply (2 * (i : ℕ))).prodMk
      (Measurable.of_eval fun (i : Fin t) => measurable_pi_apply (2 * (i : ℕ) + 1)))

lemma infoMap_fiber (w : ℕ → ℝ × ℝ) (p : E2 × (ℕ → E2)) :
    infoMap S₁ D t ((p.1, (p.2, w)) : Ωk) = Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) := by
  simp only [infoMap, Jinfo, YS, Bridge.trunc]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext i
    have hi : 2 * (i : ℕ) < 2 * t + 1 := by have := i.2; omega
    simp only [hi, ite_true]
    rw [← uS_even S₁ D]
    rfl
  · funext i
    have hi : 2 * (i : ℕ) + 1 < 2 * t + 1 := by have := i.2; omega
    simp only [hi, ite_true]
    rw [← uS_odd S₁ D]
    rfl

lemma recon_Jinfo_fst (w : ℕ → ℝ × ℝ) (y : ℕ → ℝ) {s : ℕ} (hs : s ≤ t) :
    (recon t (Jinfo t w y)).1 s = w s := by
  simp only [recon, Jinfo]
  rw [extW_apply_lt _ (Nat.lt_succ_of_le hs)]

lemma recon_Jinfo_snd (w : ℕ → ℝ × ℝ) (y : ℕ → ℝ) {k : ℕ} (hk : k < 2 * t + 1) :
    (recon t (Jinfo t w y)).2 k = y k := by
  simp only [recon, Jinfo, extU]
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [ite_eq_left (two_mul_mod s), two_mul_div, Bridge.extF_apply_lt _ (by omega)]
  · rw [ite_eq_right (by rw [two_mul_add_mod]; omega), two_mul_add_div,
      Bridge.extF_apply_lt _ (by omega)]

lemma mtF_Jinfo (w : ℕ → ℝ × ℝ) (y : ℕ → ℝ) :
    mtF S₁ D t (Jinfo t w y) = km S₁ D w y (2 * t + 1) := by
  unfold mtF
  exact km_congr S₁ D (fun s hs => recon_Jinfo_fst t w y (by omega))
    (fun k hk => recon_Jinfo_snd t w y hk)

lemma SgF_Jinfo (w : ℕ → ℝ × ℝ) (y : ℕ → ℝ) : SgF S₁ D t (Jinfo t w y) = SigK S₁ D w t := by
  unfold SgF
  exact SigK_congr S₁ D (fun s hs => recon_Jinfo_fst t w y hs.le)

lemma SgF_infoMap (ω : Ωk) : SgF S₁ D t (infoMap S₁ D t ω) = SigK S₁ D (wts ω) t := by
  unfold SgF
  exact SigK_congr S₁ D (fun s hs => recon_wts S₁ D t ω hs.le)

lemma mvG_map_addK (m : E2) (S : M2) :
    (multivariateGaussian 0 S).map (fun u => u + m) = multivariateGaussian m S := by
  unfold multivariateGaussian
  rw [Measure.map_map (measurable_add_const m) (by fun_prop)]
  congr 1
  funext x
  simp [add_comm]

/-- The fiberwise identity: along a weight path, the joint law of the information and the state
disintegrates with the kernel `postKK`. -/
lemma fiber_rectK (hS₁ : S₁.PosSemidef) (hD : SchedOK D) (w : ℕ → ℝ × ℝ) {B : Set (InfoT t)}
    {C : Set E2} (hB : MeasurableSet B) (hC : MeasurableSet C) :
    Bridge.Qm S₁ {p : E2 × (ℕ → E2) | Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) ∈ B ∧ p.1 ∈ C} =
      ∫⁻ p, {p : E2 × (ℕ → E2) | Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) ∈ B}.indicator
        (fun p => multivariateGaussian (km S₁ D w (YS S₁ D w p.1 p.2 (2 * t + 1)) (2 * t + 1))
          (SigK S₁ D w t) C) p ∂(Bridge.Qm S₁) := by
  obtain ⟨K1, K2⟩ := kalman_fiberK S₁ D w hS₁ hD (2 * t + 1)
  rw [Cs_odd] at K2
  have hY := measurable_YS S₁ D w (2 * t + 1)
  have he := measurable_errS S₁ D w (2 * t + 1)
  have hk := measurable_km_fix S₁ D w (2 * t + 1)
  set Dset : Set ((ℕ → ℝ) × E2) :=
    {z | Jinfo t w z.1 ∈ B ∧ z.2 + km S₁ D w z.1 (2 * t + 1) ∈ C} with hD'
  have hDm : MeasurableSet Dset :=
    ((measurable_Jinfo t w).comp measurable_fst hB).inter
      ((measurable_snd.add (hk.comp measurable_fst)) hC)
  have hset : {p : E2 × (ℕ → E2) | Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) ∈ B ∧ p.1 ∈ C} =
      (fun p => (YS S₁ D w p.1 p.2 (2 * t + 1), errS S₁ D w p.1 p.2 (2 * t + 1))) ⁻¹' Dset := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hD', errS, km_YS, sub_add_cancel]
  have hlaw : (Bridge.Qm S₁).map
      (fun p => (YS S₁ D w p.1 p.2 (2 * t + 1), errS S₁ D w p.1 p.2 (2 * t + 1))) =
      ((Bridge.Qm S₁).map (fun p => YS S₁ D w p.1 p.2 (2 * t + 1))).prod
        (multivariateGaussian 0 (SigK S₁ D w t)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable he.aemeasurable).1 K1.symm, K2]
  have hF : Measurable (fun y : ℕ → ℝ => multivariateGaussian (km S₁ D w y (2 * t + 1))
      (SigK S₁ D w t) C) :=
    (Measure.measurable_coe hC).comp (measurable_multivariateGaussian.comp
      (hk.prodMk measurable_const))
  rw [hset, ← Measure.map_apply (hY.prodMk he) hDm, hlaw, Measure.prod_apply hDm]
  have hsec : ∀ y : ℕ → ℝ, multivariateGaussian 0 (SigK S₁ D w t) (Prod.mk y ⁻¹' Dset) =
      {y : ℕ → ℝ | Jinfo t w y ∈ B}.indicator
        (fun y => multivariateGaussian (km S₁ D w y (2 * t + 1)) (SigK S₁ D w t) C) y := by
    intro y
    by_cases hy : Jinfo t w y ∈ B
    · have : Prod.mk y ⁻¹' Dset = (fun u : E2 => u + km S₁ D w y (2 * t + 1)) ⁻¹' C := by
        ext u; simp [hD', hy]
      rw [this, Set.indicator_of_mem (by exact hy), ← Measure.map_apply (measurable_add_const _) hC,
        mvG_map_addK]
    · have : Prod.mk y ⁻¹' Dset = ∅ := by
        ext u; simp [hD', hy]
      rw [this, Set.indicator_of_notMem (by exact hy)]
      simp
  simp_rw [hsec]
  have hF' : Measurable ({y : ℕ → ℝ | Jinfo t w y ∈ B}.indicator
      (fun y => multivariateGaussian (km S₁ D w y (2 * t + 1)) (SigK S₁ D w t) C)) :=
    hF.indicator ((measurable_Jinfo t w) hB)
  rw [lintegral_map hF' hY]
  rfl

variable (G Gγ : Measure ℝ) [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ]

/-- The joint law of the information and the state disintegrates with `postKK`. -/
theorem joint_eq_compProdK (hS₁ : S₁.PosSemidef) (hD : SchedOK D) :
    (lawK S₁ G Gγ).map (fun ω => (infoMap S₁ D t ω, ω.1)) =
      ((lawK S₁ G Gγ).map (infoMap S₁ D t)) ⊗ₘ postKK S₁ D t := by
  have hV := measurable_infoMap S₁ D t
  refine Measure.ext_prod fun {B} {C} hB hC => ?_
  rw [Measure.map_apply (hV.prodMk measurable_fst) (hB.prod hC),
    Measure.compProd_apply_prod hB hC, setLIntegral_map hB (Kernel.measurable_coe _ hC) hV]
  have hS1 : MeasurableSet ((fun ω => (infoMap S₁ D t ω, ω.1)) ⁻¹' (B ×ˢ C)) :=
    (hV.prodMk measurable_fst) (hB.prod hC)
  have hf2 : Measurable ((infoMap S₁ D t ⁻¹' B).indicator
      (fun x => postKK S₁ D t (infoMap S₁ D t x) C)) :=
    ((Kernel.measurable_coe _ hC).comp hV).indicator (hV hB)
  rw [← lintegral_indicator_one hS1, ← lintegral_indicator (hV hB),
    lintegral_lawK S₁ G Gγ _ (measurable_one.indicator hS1), lintegral_lawK S₁ G Gγ _ hf2]
  congr 1
  funext w
  have e1 : (fun p : E2 × (ℕ → E2) =>
      ((fun ω => (infoMap S₁ D t ω, ω.1)) ⁻¹' (B ×ˢ C)).indicator (1 : Ωk → ℝ≥0∞)
        ((p.1, (p.2, w)) : Ωk)) =
      {p : E2 × (ℕ → E2) | Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) ∈ B ∧ p.1 ∈ C}.indicator
        (1 : E2 × (ℕ → E2) → ℝ≥0∞) := by
    funext p
    have hiff : ((p.1, (p.2, w)) : Ωk) ∈ (fun ω => (infoMap S₁ D t ω, ω.1)) ⁻¹' (B ×ˢ C) ↔
        p ∈ {p : E2 × (ℕ → E2) | Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) ∈ B ∧ p.1 ∈ C} := by
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq, infoMap_fiber]
    by_cases h : p ∈ {p : E2 × (ℕ → E2) | Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) ∈ B ∧ p.1 ∈ C}
    · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]
  have e2 : (fun p : E2 × (ℕ → E2) => (infoMap S₁ D t ⁻¹' B).indicator
      (fun ω => postKK S₁ D t (infoMap S₁ D t ω) C) ((p.1, (p.2, w)) : Ωk)) =
      {p : E2 × (ℕ → E2) | Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) ∈ B}.indicator
        (fun p => multivariateGaussian (km S₁ D w (YS S₁ D w p.1 p.2 (2 * t + 1)) (2 * t + 1))
          (SigK S₁ D w t) C) := by
    funext p
    have hiff : ((p.1, (p.2, w)) : Ωk) ∈ infoMap S₁ D t ⁻¹' B ↔
        p ∈ {p : E2 × (ℕ → E2) | Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) ∈ B} := by
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, infoMap_fiber]
    by_cases h : p ∈ {p : E2 × (ℕ → E2) | Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1)) ∈ B}
    · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h, infoMap_fiber, postKK_apply,
        mtF_Jinfo, SgF_Jinfo]
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]
  rw [e1, e2, lintegral_indicator_one]
  · exact fiber_rectK S₁ D t hS₁ hD w hB hC
  · have hJ : Measurable (fun p : E2 × (ℕ → E2) => Jinfo t w (YS S₁ D w p.1 p.2 (2 * t + 1))) :=
      (measurable_Jinfo t w).comp (measurable_YS S₁ D w (2 * t + 1))
    exact (hJ hB).inter (measurable_fst hC)

/-- **Public beliefs are Gaussian.** -/
theorem beliefs_coreK (hS₁ : S₁.PosSemidef) (hD : SchedOK D) :
    ∀ᵐ ω ∂(lawK S₁ G Gγ),
      condDistrib (fun ω : Ωk => ω.1) (infoMap S₁ D t) (lawK S₁ G Gγ) (infoMap S₁ D t ω) =
        multivariateGaussian (mtF S₁ D t (infoMap S₁ D t ω)) (SigK S₁ D (wts ω) t) := by
  have hV := measurable_infoMap S₁ D t
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := lawK S₁ G Gγ) hV
    measurable_fst (joint_eq_compProdK S₁ D t G Gγ hS₁ hD)
  filter_upwards [ae_of_ae_map hV.aemeasurable h] with ω hω
  rw [hω, postKK_apply, SgF_infoMap]

end CC.BridgeK
