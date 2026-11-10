import ConformityConcerns.LearnTheta.MVerAux.Basic

/-!
# The Bayes formula `mfun` is a version of `E(V² | H, V + Y)`

General form: `V` has density `ψ` and is independent of `(H, Y)`.
-/

namespace CC.LearnTheta.MVerAux

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {ψ : ℝ → ℝ}

/-- The map `(h, x) ↦ m(x | η h)` is measurable. -/
lemma measurable_mfun_kernel {β : Type*} [MeasurableSpace β] (η : Kernel β ℝ)
    [IsSFiniteKernel η] (hψ : Measurable ψ) :
    Measurable fun p : β × ℝ => mfun ψ (η p.1) p.2 := by
  have hN := StronglyMeasurable.integral_kernel_prod_right' (κ := η.comap Prod.fst measurable_fst)
    (f := fun q : (β × ℝ) × ℝ => (q.1.2 - q.2) ^ 2 * ψ (q.1.2 - q.2))
    (((measurable_fst.snd.sub measurable_snd).pow_const 2).mul
      (hψ.comp (measurable_fst.snd.sub measurable_snd))).stronglyMeasurable
  have hD := StronglyMeasurable.integral_kernel_prod_right' (κ := η.comap Prod.fst measurable_fst)
    (f := fun q : (β × ℝ) × ℝ => ψ (q.1.2 - q.2))
    (hψ.comp (measurable_fst.snd.sub measurable_snd)).stronglyMeasurable
  exact hN.measurable.div hD.measurable

lemma mfun_nonneg (hψpos : ∀ x, 0 < ψ x) (μ : Measure ℝ) (x : ℝ) : 0 ≤ mfun ψ μ x :=
  div_nonneg (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (hψpos _).le)
    (integral_nonneg fun _ => (hψpos _).le)

/-- `m(V + Y | condDistrib Y H)` is a version of `E(V² | H, V + Y)`. -/
theorem condExp_sq_eq_mfun {β Ω' : Type*} [MeasurableSpace β] {m0 : MeasurableSpace Ω'}
    (P : Measure Ω') [IsProbabilityMeasure P] {H : Ω' → β} {Y V : Ω' → ℝ} (hH : Measurable H)
    (hY : Measurable Y) (hV : Measurable V) (hind : IndepFun (fun ω => (H ω, Y ω)) V P)
    (hVlaw : P.map V = vLaw ψ) (hψ : Measurable ψ) (hψpos : ∀ x, 0 < ψ x) {C : ℝ}
    (hψb : ∀ x, ψ x ≤ C) (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ)) :
    P[fun ω => V ω ^ 2 | MeasurableSpace.comap H inferInstance ⊔
        MeasurableSpace.comap (fun ω => V ω + Y ω) inferInstance] =ᵐ[P]
      fun ω => mfun ψ (condDistrib Y H P (H ω)) (V ω + Y ω) := by
  have hF := measurable_mfun_kernel (condDistrib Y H P) hψ
  have hZ : Measurable fun ω => (H ω, V ω + Y ω) := hH.prodMk (hV.add hY)
  -- the key identity on sets `{(H, V + Y) ∈ S}`
  have key : ∀ S : Set (β × ℝ), MeasurableSet S →
      ∫⁻ ω, S.indicator 1 (H ω, V ω + Y ω) * ENNReal.ofReal (V ω ^ 2) ∂P =
        ∫⁻ ω, S.indicator 1 (H ω, V ω + Y ω) *
          ENNReal.ofReal (mfun ψ (condDistrib Y H P (H ω)) (V ω + Y ω)) ∂P := by
    intro S hS
    have hSi : Measurable fun q : (β × ℝ) × ℝ => S.indicator (1 : β × ℝ → ℝ≥0∞) (q.1.1, q.2 + q.1.2) :=
      (measurable_one.indicator hS).comp
        (measurable_fst.fst.prodMk (measurable_snd.add measurable_fst.snd))
    have h1 := lintegral_joint P hH hY hV hind hVlaw hψ
      (f := fun q => S.indicator 1 (q.1.1, q.2 + q.1.2) * ENNReal.ofReal (q.2 ^ 2))
      (hSi.mul (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const 2)))
    have h2 := lintegral_joint P hH hY hV hind hVlaw hψ
      (f := fun q => S.indicator 1 (q.1.1, q.2 + q.1.2) *
        ENNReal.ofReal (mfun ψ (condDistrib Y H P q.1.1) (q.2 + q.1.2)))
      (hSi.mul (ENNReal.measurable_ofReal.comp
        (hF.comp (measurable_fst.fst.prodMk (measurable_snd.add measurable_fst.snd)))))
    simp only at h1 h2
    rw [h1, h2]
    refine lintegral_congr fun h => ?_
    exact inner_eq hψ hψpos hψb hv2 (condDistrib Y H P h)
      (hF.comp measurable_prodMk_left)
      ((measurable_one.indicator hS).comp measurable_prodMk_left)
  have hgnn : ∀ ω, 0 ≤ mfun ψ (condDistrib Y H P (H ω)) (V ω + Y ω) :=
    fun ω => mfun_nonneg hψpos _ _
  have hgm : Measurable fun ω => mfun ψ (condDistrib Y H P (H ω)) (V ω + Y ω) := hF.comp hZ
  have hfint : Integrable (fun ω => V ω ^ 2) P := by
    rw [← hVlaw] at hv2
    exact hv2.comp_measurable hV
  have hgint : Integrable (fun ω => mfun ψ (condDistrib Y H P (H ω)) (V ω + Y ω)) P := by
    refine ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall hgnn)).2 ?_⟩
    have := key Set.univ MeasurableSet.univ
    simp only [Set.indicator_univ, Pi.one_apply, one_mul] at this
    rw [← this]
    exact hfint.lintegral_lt_top
  rw [← MeasurableSpace.comap_prodMk]
  have hm : MeasurableSpace.comap (fun ω => (H ω, V ω + Y ω)) inferInstance ≤ m0 :=
    hZ.comap_le
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hfint (fun s _ _ => hgint.integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · obtain ⟨S, hS, rfl⟩ := hs
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hgnn) hgm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg (V ω))
        (hV.pow_const 2).aestronglyMeasurable]
    congr 1
    rw [← lintegral_indicator (hZ hS), ← lintegral_indicator (hZ hS)]
    have e : ∀ φ : Ω' → ℝ≥0∞, ∀ ω, ((fun ω => (H ω, V ω + Y ω)) ⁻¹' S).indicator φ ω =
        S.indicator 1 (H ω, V ω + Y ω) * φ ω := by
      intro φ ω
      by_cases hω : (H ω, V ω + Y ω) ∈ S
      · simp [Set.indicator_of_mem, hω]
      · simp [Set.indicator_of_notMem, hω]
    simp_rw [e]
    exact (key S hS).symm
  · exact (hF.comp (comap_measurable _)).stronglyMeasurable.aestronglyMeasurable

end CC.LearnTheta.MVerAux
