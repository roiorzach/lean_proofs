import ConformityConcerns.BridgeK.Hist
import ConformityConcerns.BridgeK.Occurs
import ConformityConcerns.BridgeK.Fails
import ConformityConcerns.BridgeK.SL
import ConformityConcerns.BridgeK.Cov
import ConformityConcerns.Dynamics.Heterogeneous

/-!
# Proposition A1 (Heterogeneous Conformity Concerns) with the paper's definition of social
learning

`κ_t` i.i.d. with law `G` on `(0, ∞)`, publicly observed, independent of all other primitives
(including `γ_t`, i.i.d. with full support on `[0,1]`); no disclosures. Posterior means are given
the public history `h^t = (κ_0, γ_0, a_0, …, κ_{t-1}, γ_{t-1}, a_{t-1}, κ_t, γ_t)`.

`ε = Pr(κ_t < κck)` is `G (Iio κck)`; `inf Supp(κ_t) > κck` is written
`∃ κ₀ > κck, G (Iio κ₀) = 0` (equivalent for a probability measure on `ℝ`).
-/

namespace CC.BridgeK

open MeasureTheory Set Filter Topology

/-- **Proposition A1 (paper's definition of social learning).** Let `κ_t` be i.i.d. with law
`G` on `(0, ∞)`, publicly observed and independent of all other primitives, with `G({κck}) = 0`,
and suppose `Σ₁ ≻ 0` and `γ_t` is i.i.d. with full support on `[0,1]`. If
`ε = Pr(κ_t < κck) > 0`, social learning about fundamentals and preferences occurs. If
`inf Supp(κ_t) > κck`, social learning about fundamentals and preferences fails. -/
theorem propA1_socialLearning (G Gγ : Measure ℝ) [IsProbabilityMeasure G]
    [IsProbabilityMeasure Gγ] (hpos : G (Iic 0) = 0) (hatom : G {κck} = 0)
    (hGγ : FullSupportUnit Gγ) (S₁ : M2) (hS : S₁.PosDef) :
    (0 < G (Iio κck) →
      SLOccurs (lawK S₁ G Gγ) thetaV (postThetaK S₁ G Gγ noDisc) ∧
        SLOccurs (lawK S₁ G Gγ) muV (postMuK S₁ G Gγ noDisc)) ∧
    ((∃ κ₀, κck < κ₀ ∧ G (Iio κ₀) = 0) →
      SLFails (lawK S₁ G Gγ) thetaV (postThetaK S₁ G Gγ noDisc) ∧
        SLFails (lawK S₁ G Gγ) muV (postMuK S₁ G Gγ noDisc)) := by
  set W := Measure.infinitePi fun _ : ℕ => G.prod Gγ with hW
  have hA1 := CC.propA1 G Gγ hpos hatom hGγ S₁ hS
  dsimp only at hA1
  have hD := schedOK_noDisc
  have hθ : Measurable thetaV := Bridge.br_meas_coord measurable_fst 0
  have hμ : Measurable muV := Bridge.br_meas_coord measurable_fst 1
  have hpθ : postThetaK S₁ G Gγ noDisc =
      fun n => (lawK S₁ G Gγ)[fun ω => ω.1 0 | infoSigmaK S₁ noDisc n] :=
    funext fun n => postThetaK_eq S₁ G Gγ noDisc n
  have hpμ : postMuK S₁ G Gγ noDisc =
      fun n => (lawK S₁ G Gγ)[fun ω => ω.1 1 | infoSigmaK S₁ noDisc n] :=
    funext fun n => postMuK_eq S₁ G Gγ noDisc n
  have hmeas : ∀ (i : Fin 2) n, Measurable
      ((lawK S₁ G Gγ)[fun ω => ω.1 i | infoSigmaK S₁ noDisc n]) := fun i n =>
    stronglyMeasurable_condExp.measurable.mono (infoSigmaK_le S₁ noDisc n) le_rfl
  have hcov : ∀ w : ℕ → ℝ × ℝ, (fun t => SigK S₁ noDisc w t) = SigmaH S₁ w :=
    fun w => funext fun t => SigK_noDisc S₁ w t
  refine ⟨fun hε => ?_, fun h0 => ?_⟩
  · have hε' : 0 < (G (Iio κck)).toReal := ENNReal.toReal_pos hε.ne' (measure_ne_top _ _)
    have hlim : ∀ᵐ w ∂W, Tendsto (fun t => SigK S₁ noDisc w t) atTop (𝓝 0) := by
      filter_upwards [hA1.1 hε'] with w hw
      rw [hcov]; exact hw.1
    have hbd : ∀ (i : Fin 2) (w : ℕ → ℝ × ℝ) t, SigK S₁ noDisc w t i i ≤ S₁ i i := by
      intro i w t
      rw [SigK_noDisc]
      fin_cases i
      · exact SigmaC_anti00 (κ := fun s => (w s).1) (γ := fun s => (w s).2) hS.posSemidef
          (Nat.zero_le t)
      · exact SigmaC_anti11 (κ := fun s => (w s).1) (γ := fun s => (w s).2) hS.posSemidef
          (Nat.zero_le t)
    rw [hpθ, hpμ]
    exact ⟨slOccurs_of_ae hθ (hmeas 0)
        (occurs_coreK S₁ noDisc G Gγ hS.posSemidef hD 0 (hbd 0) hlim),
      slOccurs_of_ae hμ (hmeas 1)
        (occurs_coreK S₁ noDisc G Gγ hS.posSemidef hD 1 (hbd 1) hlim)⟩
  · have hfc := hA1.2 h0
    have hfin : ∀ i : Fin 2, ∀ᵐ w ∂W, ∃ K,
        (∀ k, K ≤ k → ld S₁ noDisc w k = (0, 0)) ∧ 0 < Cs S₁ noDisc w K i i := by
      intro i
      filter_upwards [hfc] with w hw
      obtain ⟨T, Sinf, -, hT⟩ := hw
      refine ⟨2 * T, fun k hk => ?_, ?_⟩
      · obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' k
        · rw [ld_even]; rfl
        · rw [ld_odd]
          unfold ldA
          have hn : ¬ revCrit (w s).1 (SigK S₁ noDisc w s) (w s).2 := by
            rw [SigK_noDisc]; exact (hT s (by omega)).1
          rw [ite_eq_right hn]
      · rw [Cs_even]
        change 0 < SigK S₁ noDisc w T i i
        rw [SigK_noDisc]
        exact SigmaC_diag_pos _ _ S₁ hS.posSemidef T i hS.diag_pos
    have hlev : ∀ i : Fin 2, ∀ᵐ ω ∂(lawK S₁ G Gγ),
        Tendsto (fun n => (lawK S₁ G Gγ)[fun ω => ω.1 i | infoSigmaK S₁ noDisc n] ω) atTop
          (𝓝 ((lawK S₁ G Gγ)[fun ω => ω.1 i | ⨆ n, infoSigmaK S₁ noDisc n] ω)) := fun i =>
      tendsto_ae_condExp (ℱ := infoFiltK S₁ noDisc) _
    rw [hpθ, hpμ]
    exact ⟨slFails_of hθ (hlev 0) (fails_coreK S₁ noDisc G Gγ hS.posSemidef hD 0 (hfin 0)),
      slFails_of hμ (hlev 1) (fails_coreK S₁ noDisc G Gγ hS.posSemidef hD 1 (hfin 1))⟩

end CC.BridgeK
