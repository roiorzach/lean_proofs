import ConformityConcerns.Bridge.Fubini
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Public beliefs are Gaussian (core of Lemma 3's last claim)

Given the information `(γ_0, …, γ_t, obs_0, …, obs_{t-1})`, the conditional law of `(θ, μ)` is
`N(m_t, Σ_t)` with `m_t` the Kalman mean: along each weight path, `x = (x - m_t) + m_t` where
`x - m_t ~ N(0, Σ_t)` is independent of the observations (`kalman_fiber`).
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

set_option warn.classDefReducibility false

variable (κ : ℝ) (S₁ : M2) (t : ℕ)

/-- The information at date `t` (same as `infoVec`). -/
noncomputable def infoV (ω : Ωg) : (Fin (t + 1) → ℝ) × (Fin t → ℝ) :=
  ((fun i : Fin (t + 1) => gam ω i), (fun i : Fin t => obs κ S₁ i ω))

/-- The Kalman mean as a function of the information. -/
noncomputable def mtF (q : (Fin (t + 1) → ℝ) × (Fin t → ℝ)) : E2 :=
  kmean κ S₁ (extF (t + 1) q.1) (extF t q.2) t

/-- `Σ_t` as a function of the information. -/
noncomputable def SgF (q : (Fin (t + 1) → ℝ) × (Fin t → ℝ)) : M2 :=
  SigP κ S₁ (extF (t + 1) q.1) t

lemma measurable_infoV : Measurable (infoV κ S₁ t) :=
  (Measurable.of_eval fun (i : Fin (t + 1)) => measurable_gam_apply i).prodMk
    (Measurable.of_eval fun (i : Fin t) => measurable_obs κ S₁ i)

lemma measurable_mtF : Measurable (mtF κ S₁ t) :=
  (measurable_kmean κ S₁ t).comp (((measurable_extF _).comp measurable_fst).prodMk
    ((measurable_extF _).comp measurable_snd))

lemma measurable_SgF : Measurable (SgF κ S₁ t) :=
  (measurable_SigP κ S₁ t).comp ((measurable_extF _).comp measurable_fst)

/-- The candidate posterior `q ↦ N(m_t(q), Σ_t(q))`. -/
noncomputable def postK : Kernel ((Fin (t + 1) → ℝ) × (Fin t → ℝ)) E2 where
  toFun q := multivariateGaussian (mtF κ S₁ t q) (SgF κ S₁ t q)
  measurable' := measurable_multivariateGaussian.comp
    ((measurable_mtF κ S₁ t).prodMk (measurable_SgF κ S₁ t))

instance : IsMarkovKernel (postK κ S₁ t) :=
  ⟨fun q => by
    change IsProbabilityMeasure (multivariateGaussian (mtF κ S₁ t q) (SgF κ S₁ t q))
    infer_instance⟩

lemma postK_apply (q : (Fin (t + 1) → ℝ) × (Fin t → ℝ)) :
    postK κ S₁ t q = multivariateGaussian (mtF κ S₁ t q) (SgF κ S₁ t q) := rfl

/-- The information along the weight path `γ`, as a function of the observations. -/
def Jinfo (γ : ℕ → ℝ) (y : ℕ → ℝ) : (Fin (t + 1) → ℝ) × (Fin t → ℝ) :=
  ((fun i : Fin (t + 1) => γ i), (fun i : Fin t => y i))

lemma measurable_Jinfo (γ : ℕ → ℝ) : Measurable (Jinfo t γ) :=
  measurable_const.prodMk (Measurable.of_eval fun (i : Fin t) => measurable_pi_apply (i : ℕ))

lemma infoV_fiber (γ : ℕ → ℝ) (p : E2 × (ℕ → E2)) :
    infoV κ S₁ t ((p.1, (p.2, γ)) : Ωg) = Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) := by
  simp only [infoV, Jinfo, Ytr, trunc]
  congr 1
  funext i
  simp only [i.2, ite_true]
  rfl

lemma mtF_Jinfo (γ y : ℕ → ℝ) : mtF κ S₁ t (Jinfo t γ y) = kmean κ S₁ γ y t := by
  unfold mtF Jinfo
  exact kmean_congr κ S₁ (fun s hs => extF_apply_lt _ (Nat.lt_succ_of_lt hs))
    (fun s hs => extF_apply_lt _ hs)

lemma SgF_Jinfo (γ y : ℕ → ℝ) : SgF κ S₁ t (Jinfo t γ y) = SigP κ S₁ γ t := by
  unfold SgF Jinfo
  exact SigP_congr κ S₁ (fun s hs => extF_apply_lt _ (Nat.lt_succ_of_lt hs))

lemma SgF_infoV (ω : Ωg) : SgF κ S₁ t (infoV κ S₁ t ω) = Sig κ S₁ ω t := by
  unfold SgF infoV
  exact SigP_congr κ S₁ (fun s hs => extF_apply_lt _ (Nat.lt_succ_of_lt hs))

lemma mvG_map_add (m : E2) (S : M2) :
    (multivariateGaussian 0 S).map (fun u => u + m) = multivariateGaussian m S := by
  unfold multivariateGaussian
  rw [Measure.map_map (measurable_add_const m) (by fun_prop)]
  congr 1
  funext x
  simp [add_comm]

/-- The fiberwise identity: along a weight path, the joint law of the information and the state
disintegrates with the kernel `postK`. -/
lemma fiber_rect (hS₁ : S₁.PosSemidef) (γ : ℕ → ℝ) {B : Set ((Fin (t + 1) → ℝ) × (Fin t → ℝ))}
    {C : Set E2} (hB : MeasurableSet B) (hC : MeasurableSet C) :
    Qm S₁ {p : E2 × (ℕ → E2) | Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) ∈ B ∧ p.1 ∈ C} =
      ∫⁻ p, {p : E2 × (ℕ → E2) | Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) ∈ B}.indicator
        (fun p => multivariateGaussian (kmean κ S₁ γ (Ytr κ S₁ γ p.1 p.2 t) t)
          (SigP κ S₁ γ t) C) p ∂(Qm S₁) := by
  obtain ⟨K1, K2⟩ := kalman_fiber κ S₁ γ hS₁ t
  have hY := measurable_Ytr κ S₁ γ t
  have he := measurable_errF κ S₁ γ t
  have hk := measurable_kmean_fix κ S₁ γ t
  set D : Set ((ℕ → ℝ) × E2) := {z | Jinfo t γ z.1 ∈ B ∧ z.2 + kmean κ S₁ γ z.1 t ∈ C} with hD
  have hDm : MeasurableSet D :=
    ((measurable_Jinfo t γ).comp measurable_fst hB).inter
      ((measurable_snd.add (hk.comp measurable_fst)) hC)
  have hset : {p : E2 × (ℕ → E2) | Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) ∈ B ∧ p.1 ∈ C} =
      (fun p => (Ytr κ S₁ γ p.1 p.2 t, errF κ S₁ γ p.1 p.2 t)) ⁻¹' D := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hD, errF, kmean_Ytr, sub_add_cancel]
  have hlaw : (Qm S₁).map (fun p => (Ytr κ S₁ γ p.1 p.2 t, errF κ S₁ γ p.1 p.2 t)) =
      ((Qm S₁).map (fun p => Ytr κ S₁ γ p.1 p.2 t)).prod
        (multivariateGaussian 0 (SigP κ S₁ γ t)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable he.aemeasurable).1 K1.symm, K2]
  have hF : Measurable (fun y : ℕ → ℝ => multivariateGaussian (kmean κ S₁ γ y t)
      (SigP κ S₁ γ t) C) :=
    (Measure.measurable_coe hC).comp (measurable_multivariateGaussian.comp
      (hk.prodMk measurable_const))
  rw [hset, ← Measure.map_apply (hY.prodMk he) hDm, hlaw, Measure.prod_apply hDm]
  have hsec : ∀ y : ℕ → ℝ, multivariateGaussian 0 (SigP κ S₁ γ t) (Prod.mk y ⁻¹' D) =
      {y : ℕ → ℝ | Jinfo t γ y ∈ B}.indicator
        (fun y => multivariateGaussian (kmean κ S₁ γ y t) (SigP κ S₁ γ t) C) y := by
    intro y
    by_cases hy : Jinfo t γ y ∈ B
    · have : Prod.mk y ⁻¹' D = (fun u : E2 => u + kmean κ S₁ γ y t) ⁻¹' C := by
        ext u; simp [hD, hy]
      rw [this, Set.indicator_of_mem (by exact hy), ← Measure.map_apply (measurable_add_const _) hC,
        mvG_map_add]
    · have : Prod.mk y ⁻¹' D = ∅ := by
        ext u; simp [hD, hy]
      rw [this, Set.indicator_of_notMem (by exact hy)]
      simp
  simp_rw [hsec]
  have hF' : Measurable ({y : ℕ → ℝ | Jinfo t γ y ∈ B}.indicator
      (fun y => multivariateGaussian (kmean κ S₁ γ y t) (SigP κ S₁ γ t) C)) :=
    hF.indicator ((measurable_Jinfo t γ) hB)
  rw [lintegral_map hF' hY]
  rfl

/-- The joint law of the information and the state disintegrates with `postK`. -/
theorem joint_eq_compProd (hS₁ : S₁.PosSemidef) (G : Measure ℝ) [IsProbabilityMeasure G] :
    (lawG S₁ G).map (fun ω => (infoV κ S₁ t ω, ω.1)) =
      ((lawG S₁ G).map (infoV κ S₁ t)) ⊗ₘ postK κ S₁ t := by
  have hV := measurable_infoV κ S₁ t
  refine Measure.ext_prod fun {B} {C} hB hC => ?_
  rw [Measure.map_apply (hV.prodMk measurable_fst) (hB.prod hC),
    Measure.compProd_apply_prod hB hC, setLIntegral_map hB (Kernel.measurable_coe _ hC) hV]
  have hS1 : MeasurableSet ((fun ω => (infoV κ S₁ t ω, ω.1)) ⁻¹' (B ×ˢ C)) :=
    (hV.prodMk measurable_fst) (hB.prod hC)
  have hf2 : Measurable ((infoV κ S₁ t ⁻¹' B).indicator
      (fun x => postK κ S₁ t (infoV κ S₁ t x) C)) :=
    ((Kernel.measurable_coe _ hC).comp hV).indicator (hV hB)
  rw [← lintegral_indicator_one hS1, ← lintegral_indicator (hV hB),
    lintegral_lawG S₁ G _ (measurable_one.indicator hS1), lintegral_lawG S₁ G _ hf2]
  congr 1
  funext γ
  have hm : Measurable (fun p : E2 × (ℕ → E2) => ((p.1, (p.2, γ)) : Ωg)) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have e1 : (fun p : E2 × (ℕ → E2) =>
      ((fun ω => (infoV κ S₁ t ω, ω.1)) ⁻¹' (B ×ˢ C)).indicator (1 : Ωg → ℝ≥0∞)
        ((p.1, (p.2, γ)) : Ωg)) =
      {p : E2 × (ℕ → E2) | Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) ∈ B ∧ p.1 ∈ C}.indicator
        (1 : E2 × (ℕ → E2) → ℝ≥0∞) := by
    funext p
    have hiff : ((p.1, (p.2, γ)) : Ωg) ∈ (fun ω => (infoV κ S₁ t ω, ω.1)) ⁻¹' (B ×ˢ C) ↔
        p ∈ {p : E2 × (ℕ → E2) | Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) ∈ B ∧ p.1 ∈ C} := by
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq, infoV_fiber]
    by_cases h : p ∈ {p : E2 × (ℕ → E2) | Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) ∈ B ∧ p.1 ∈ C}
    · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]
  have e2 : (fun p : E2 × (ℕ → E2) => (infoV κ S₁ t ⁻¹' B).indicator
      (fun ω => postK κ S₁ t (infoV κ S₁ t ω) C) ((p.1, (p.2, γ)) : Ωg)) =
      {p : E2 × (ℕ → E2) | Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) ∈ B}.indicator
        (fun p => multivariateGaussian (kmean κ S₁ γ (Ytr κ S₁ γ p.1 p.2 t) t)
          (SigP κ S₁ γ t) C) := by
    funext p
    have hiff : ((p.1, (p.2, γ)) : Ωg) ∈ infoV κ S₁ t ⁻¹' B ↔
        p ∈ {p : E2 × (ℕ → E2) | Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) ∈ B} := by
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, infoV_fiber]
    by_cases h : p ∈ {p : E2 × (ℕ → E2) | Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t) ∈ B}
    · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h, infoV_fiber, postK_apply,
        mtF_Jinfo, SgF_Jinfo]
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]
  rw [e1, e2, lintegral_indicator_one]
  · exact fiber_rect κ S₁ t hS₁ γ hB hC
  · have hJ : Measurable (fun p : E2 × (ℕ → E2) => Jinfo t γ (Ytr κ S₁ γ p.1 p.2 t)) :=
      (measurable_Jinfo t γ).comp (measurable_Ytr κ S₁ γ t)
    exact (hJ hB).inter (measurable_fst hC)

/-- **Public beliefs are Gaussian.** -/
theorem beliefs_core (hS₁ : S₁.PosSemidef) (G : Measure ℝ) [IsProbabilityMeasure G] :
    ∀ᵐ ω ∂(lawG S₁ G),
      condDistrib (fun ω : Ωg => ω.1) (infoV κ S₁ t) (lawG S₁ G) (infoV κ S₁ t ω) =
        multivariateGaussian (mtF κ S₁ t (infoV κ S₁ t ω)) (Sig κ S₁ ω t) := by
  have hV := measurable_infoV κ S₁ t
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := lawG S₁ G) hV
    measurable_fst (joint_eq_compProd κ S₁ t hS₁ G)
  filter_upwards [ae_of_ae_map hV.aemeasurable h] with ω hω
  rw [hω, postK_apply, SgF_infoV]

end CC.Bridge
