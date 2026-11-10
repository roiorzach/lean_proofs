import ConformityConcerns.BridgeK.Defs
import ConformityConcerns.Bridge.Fubini

/-!
# Conditioning on the weight path

The weights are independent of the state and the noises, so integrals against `lawK` are
iterated integrals: first over `(θ, μ)` and the noises (law `Bridge.Qm S₁`), then over the weight
path.
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option warn.classDefReducibility false

variable (S₁ : M2) (G Gγ : Measure ℝ) [IsProbabilityMeasure G] [IsProbabilityMeasure Gγ]

lemma lintegral_lawK (f : Ωk → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f ω ∂(lawK S₁ G Gγ) =
      ∫⁻ w, ∫⁻ p, f (p.1, (p.2, w)) ∂(Bridge.Qm S₁)
        ∂(Measure.infinitePi fun _ : ℕ => G.prod Gγ) := by
  unfold lawK Bridge.Qm
  rw [← Measure.prodAssoc_prod, lintegral_map hf MeasurableEquiv.prodAssoc.measurable]
  exact lintegral_prod_symm (fun a => f (MeasurableEquiv.prodAssoc a))
    (hf.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable

lemma measure_lawK {B : Set Ωk} (hB : MeasurableSet B) :
    lawK S₁ G Gγ B = ∫⁻ w, Bridge.Qm S₁ ((fun p : E2 × (ℕ → E2) => (p.1, (p.2, w))) ⁻¹' B)
      ∂(Measure.infinitePi fun _ : ℕ => G.prod Gγ) := by
  rw [← lintegral_indicator_one hB, lintegral_lawK S₁ G Gγ _ (measurable_one.indicator hB)]
  congr 1
  funext w
  have hm : Measurable (fun p : E2 × (ℕ → E2) => ((p.1, (p.2, w)) : Ωk)) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  rw [← lintegral_indicator_one (hm hB)]
  rfl

lemma integrable_coord_lawK (i : Fin 2) : Integrable (fun ω : Ωk => ω.1 i) (lawK S₁ G Gγ) :=
  (Bridge.integrable_coord S₁ i).comp_fst _

end CC.BridgeK
