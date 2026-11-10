import ConformityConcerns.LearnTheta.Model
import ConformityConcerns.LearnTheta.MVerAux.CondExp

/-!
# Proposition A5: the Bayes formula for `m` is the conditional expectation

`m(x | h^t) = E(v_t² | ṽ_t = x, h^t)`. As `v_t` has density `ψ` and is independent of
`(h^t, Y_t)`, Bayes' rule gives the version `mfun ψ η x = ∫(x-y)²ψ(x-y) dη(y) / ∫ψ(x-y) dη(y)`,
with `η` the conditional law of `Y_t` given `h^t`. This file proves that `mfun` evaluated at the
realized history and type is a version of `E(v_t² | h^t, ṽ_t)`.
-/

namespace CC.LearnTheta

open MeasureTheory ProbabilityTheory Filter Topology

variable (Lθ Lε : Measure ℝ) (ψ : ℝ → ℝ) [IsProbabilityMeasure Lθ] [IsProbabilityMeasure Lε]
  [IsProbabilityMeasure (vLaw ψ)]

/-- `m(ṽ_t | h^t) = E(v_t² | h^t, ṽ_t)` almost surely, with `m` the Bayes formula `mfun`. -/
theorem mfun_condExp (hψc : Continuous ψ)
    (hψpos : ∀ x, 0 < ψ x) (hψb : ∃ C, ∀ x, ψ x ≤ C)
    (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ) :
    (law Lθ Lε (vLaw ψ))[fun ω => vV t ω ^ 2 |
        histSigma (law Lθ Lε (vLaw ψ)) c t ⊔
          MeasurableSpace.comap (vtil (law Lθ Lε (vLaw ψ)) c t) inferInstance] =ᵐ[law Lθ Lε (vLaw ψ)]
      fun ω => mfun ψ (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω))
        (vtil (law Lθ Lε (vLaw ψ)) c t ω) := by
  obtain ⟨C, hC⟩ := hψb
  have hind : IndepFun (fun ω => (hist (law Lθ Lε (vLaw ψ)) c t ω,
      Ycond (law Lθ Lε (vLaw ψ)) c t ω)) (vV t) (law Lθ Lε (vLaw ψ)) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (indep_v Lθ Lε (vLaw ψ) t).symm
      (measurable_hist_Ycond_past (law Lθ Lε (vLaw ψ)) c hc t).comap_le
  exact MVerAux.condExp_sq_eq_mfun (law Lθ Lε (vLaw ψ)) (measurable_hist _ c hc t)
    (measurable_Ycond _ c hc t) (measurable_pi_apply _) hind (map_vV Lθ Lε (vLaw ψ) t)
    hψc.measurable hψpos hC hv2

end CC.LearnTheta
