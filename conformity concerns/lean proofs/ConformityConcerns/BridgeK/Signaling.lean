import ConformityConcerns.BridgeK.Hist
import ConformityConcerns.BridgeK.Beliefs
import ConformityConcerns.LinearPaths.Signaling

/-!
# `eqActK` is the signaling equilibrium at the current public beliefs

In the model of Propositions 3 (1) and A1 (`BridgeK/Defs.lean`), the equilibrium action `eqActK` is
defined by a formula. `eqActK_signaling` shows that this is the signaling equilibrium: at almost
every realised history, with `N(m, Σ_t)` the public posterior given the history,

* the rule `eqForm` is a signaling equilibrium of the period game at that history;
* every signaling equilibrium of that period game plays this rule for almost every private
  information;
* the realised action `eqActK` is this rule at the realised private information.
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory Filter
open CC.LinearPaths (eqFormR eqForm eqForm_signaling signaling_ae_eqForm)

set_option warn.classDefReducibility false

variable (S₁ : M2) (G Gγ : Measure ℝ) (D : Sched)

/-- `eqActK` is the explicit rule at the current public beliefs. -/
lemma eqActK_eq_form (t : ℕ) (ω : Ωk) :
    eqActK S₁ G Gγ D t ω = eqFormR (kap ω t) (postThetaI S₁ G Gγ D t ω) (postMuI S₁ G Gγ D t ω)
      (SigK S₁ D (wts ω) t) (gam ω t) (priv t ω) := by
  unfold eqActK eqFormR obsK
  by_cases h : revK S₁ D t ω
  · have h' : revCrit (kap ω t) (SigK S₁ D (wts ω) t) (gam ω t) := h
    simp only [h, h', ↓reduceIte]
    rfl
  · have h' : ¬ revCrit (kap ω t) (SigK S₁ D (wts ω) t) (gam ω t) := h
    simp only [h, h', ↓reduceIte]

variable [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ]

/-- Almost surely `κ_t > 0`. -/
lemma ae_kap_pos (hpos : G (Set.Iic 0) = 0) (t : ℕ) :
    ∀ᵐ ω ∂(lawK S₁ G Gγ), 0 < kap ω t := by
  have h1 : (lawK S₁ G Gγ).map (fun ω : Ωk => ω.2.2) =
      Measure.infinitePi fun _ : ℕ => G.prod Gγ := by
    have : (fun ω : Ωk => ω.2.2) = Prod.snd ∘ Prod.snd := rfl
    unfold lawK
    rw [this, ← Measure.map_map measurable_snd measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, Measure.map_snd_prod, measure_univ, one_smul]
  have ha : ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => G.prod Gγ), ∀ s, (w s).1 ∈ Set.Ioi (0 : ℝ) := by
    refine ae_forall_mem (G.prod Gγ) (s := Prod.fst ⁻¹' Set.Ioi 0)
      (measurable_fst measurableSet_Ioi) ?_
    have : (Prod.fst ⁻¹' Set.Ioi (0 : ℝ) : Set (ℝ × ℝ))ᶜ = Set.Iic 0 ×ˢ Set.univ := by
      ext p; simp
    rw [this, Measure.prod_prod, hpos, zero_mul]
  rw [← h1] at ha
  filter_upwards [ae_of_ae_map (measurable_snd.comp measurable_snd).aemeasurable ha] with ω hω
  exact hω t

/-- **The equilibrium action is the signaling equilibrium at the current public beliefs.** -/
theorem eqActK_signaling (hS : S₁.PosSemidef) (hD : ∀ t i n, D t = some (i, n) → 0 ≤ n)
    (hpos : G (Set.Iic 0) = 0) (t : ℕ) :
    ∀ᵐ ω ∂(lawK S₁ G Gγ), ∃ m : E2,
      m 0 = postThetaK S₁ G Gγ D t ω ∧ m 1 = postMuK S₁ G Gγ D t ω ∧
      condDistrib (fun ω : Ωk => ω.1) (infoVecK S₁ D t) (lawK S₁ G Gγ) (infoVecK S₁ D t ω) =
        multivariateGaussian m (SigK S₁ D (wts ω) t) ∧
      (∃ φ : Kernel ℝ ℝ, (gameAt m (SigK S₁ D (wts ω) t) (gam ω t) (kap ω t)).IsSignalingEq
        (eqForm (kap ω t) m (SigK S₁ D (wts ω) t) (gam ω t)) φ) ∧
      (∀ (a : E2 → ℝ) (φ : Kernel ℝ ℝ),
        (gameAt m (SigK S₁ D (wts ω) t) (gam ω t) (kap ω t)).IsSignalingEq a φ →
        a =ᵐ[(gameAt m (SigK S₁ D (wts ω) t) (gam ω t) (kap ω t)).P]
          eqForm (kap ω t) m (SigK S₁ D (wts ω) t) (gam ω t)) ∧
      eqActK S₁ G Gγ D t ω =
        eqForm (kap ω t) m (SigK S₁ D (wts ω) t) (gam ω t) (priv t ω) := by
  obtain ⟨mt, hmt, hbel⟩ := beliefsK_gaussian S₁ hS G Gγ D hD t
  have hV : Measurable (infoVecK S₁ D t) := measurable_infoMap S₁ D t
  have hmean : ∀ i : Fin 2, (lawK S₁ G Gγ)[fun ω => ω.1 i | infoSigmaK S₁ D t] =ᵐ[lawK S₁ G Gγ]
      fun ω => mt (infoVecK S₁ D t ω) i := by
    intro i
    have h1 := condExp_ae_eq_integral_condDistrib (μ := lawK S₁ G Gγ) (X := infoVecK S₁ D t)
      (Y := fun ω : Ωk => ω.1) hV measurable_fst.aemeasurable (f := fun y : E2 => y i)
      (Bridge.br_meas_coord measurable_id i).stronglyMeasurable (integrable_coord_lawK S₁ G Gγ i)
    filter_upwards [h1, hbel] with ω a b
    refine a.trans ?_
    rw [b, Bridge.integral_coord_mvG (SigK_psd S₁ D hD hS (wts ω) t) i]
  filter_upwards [hbel, hmean 0, hmean 1, ae_kap_pos S₁ G Gγ hpos t] with ω hb h0 h1 hk
  have hpsd : (SigK S₁ D (wts ω) t).PosSemidef := SigK_psd S₁ D hD hS (wts ω) t
  refine ⟨mt (infoVecK S₁ D t ω), ?_, ?_, hb, eqForm_signaling hpsd hk,
    fun a φ hE => signaling_ae_eqForm hpsd hk hE, ?_⟩
  · rw [postThetaK_eq]; exact h0.symm
  · rw [postMuK_eq]; exact h1.symm
  · rw [eqActK_eq_form]
    have h0' : mt (infoVecK S₁ D t ω) 0 = postThetaI S₁ G Gγ D t ω := h0.symm
    have h1' : mt (infoVecK S₁ D t ω) 1 = postMuI S₁ G Gγ D t ω := h1.symm
    show _ = eqFormR _ (mt (infoVecK S₁ D t ω) 0) (mt (infoVecK S₁ D t ω) 1) _ _ _
    rw [h0', h1']

end CC.BridgeK
