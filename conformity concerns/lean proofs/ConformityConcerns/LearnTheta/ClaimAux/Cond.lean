import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditional expectation and independence lemmas for the Claim of Proposition A5

* `integral_freeze`: if `V` is independent of `𝒦` and `W` is `𝒦`-measurable, then
  `E F(W, V) = E ∫ F(W, x) dP_V(x)` (independence and Fubini).
* `integral_mul_condExp`: `E[φ f] = E[φ E(f | m)]` for bounded `m`-measurable `φ`.
* `condExp_congr_setIntegral`, `condExp_le_on`, `condExp_affine`: bookkeeping.
* `condExp_indicator_sub_le`: `E_m[1_A (θ - g)] ≤ E_m |E_{m'} θ - g|` for `A ∈ m' ⊇ m`.
* `tendsto_condExp_abs_sub`: `E_t |θ_∞ - θ_t| → 0` almost surely (Lévy).
-/

namespace CC.LearnTheta.ClaimAux

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*}

/-- **Freezing lemma.** -/
theorem integral_freeze {β : Type*} [MeasurableSpace β] {𝒦 : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] (h𝒦 : 𝒦 ≤ mΩ) {V : Ω → ℝ} (hV : Measurable V)
    (hind : Indep (MeasurableSpace.comap V inferInstance) 𝒦 P) {W : Ω → β}
    (hW : Measurable[𝒦] W) {F : β × ℝ → ℝ} (hF : Measurable F)
    (hint : Integrable (fun ω => F (W ω, V ω)) P) :
    ∫ ω, F (W ω, V ω) ∂P = ∫ ω, (∫ x, F (W ω, x) ∂(P.map V)) ∂P := by
  have hW' : Measurable W := hW.mono h𝒦 le_rfl
  have hWV : Measurable (fun ω => (W ω, V ω)) := hW'.prodMk hV
  have hind' : IndepFun W V P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind.symm hW.comap_le
  have hmap : P.map (fun ω => (W ω, V ω)) = (P.map W).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hW'.aemeasurable hV.aemeasurable).1 hind'
  have hFi : Integrable F ((P.map W).prod (P.map V)) := by
    rw [← hmap]
    exact (integrable_map_measure hF.aestronglyMeasurable hWV.aemeasurable).2 hint
  calc ∫ ω, F (W ω, V ω) ∂P = ∫ p, F p ∂(P.map (fun ω => (W ω, V ω))) :=
        (integral_map hWV.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ w, ∫ x, F (w, x) ∂(P.map V) ∂(P.map W) := by rw [hmap, integral_prod _ hFi]
    _ = ∫ ω, (∫ x, F (W ω, x) ∂(P.map V)) ∂P :=
        integral_map hW'.aemeasurable
          (hF.stronglyMeasurable.integral_prod_right').aestronglyMeasurable

/-- `E[φ E(f | m)] = E[φ f]` for bounded `m`-measurable `φ`. -/
theorem integral_mul_condExp {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hm : m ≤ mΩ)
    {f φ : Ω → ℝ} (hf : Integrable f P) (hφ : StronglyMeasurable[m] φ) {C : ℝ}
    (hC : ∀ ω, |φ ω| ≤ C) :
    ∫ ω, φ ω * (P[f | m]) ω ∂P = ∫ ω, φ ω * f ω ∂P := by
  have h1 : P[φ * f | m] =ᵐ[P] φ * P[f | m] :=
    condExp_stronglyMeasurable_mul_of_bound hm hφ hf C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  calc ∫ ω, φ ω * (P[f | m]) ω ∂P = ∫ ω, (P[φ * f | m]) ω ∂P :=
        integral_congr_ae (h1.symm.mono fun ω h => h)
    _ = ∫ ω, (φ * f) ω ∂P := integral_condExp hm
    _ = _ := rfl

/-- Two integrable functions with equal integrals over `m`-measurable sets have the same
conditional expectation. -/
theorem condExp_congr_setIntegral {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (h : ∀ s, MeasurableSet[m] s → ∫ ω in s, f ω ∂P = ∫ ω in s, g ω ∂P) :
    P[f | m] =ᵐ[P] P[g | m] :=
  ae_eq_condExp_of_forall_setIntegral_eq hm hg (fun _ _ _ => integrable_condExp.integrableOn)
    (fun s hs _ => by rw [setIntegral_condExp hm hf hs, h s hs])
    stronglyMeasurable_condExp.aestronglyMeasurable

/-- Monotonicity of the conditional expectation on an `m`-measurable set. -/
theorem condExp_le_on {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P) {S : Set Ω}
    (hS : MeasurableSet[m] S) (hle : ∀ ω ∈ S, f ω ≤ g ω) :
    ∀ᵐ ω ∂P, ω ∈ S → (P[f | m]) ω ≤ (P[g | m]) ω := by
  have h1 := condExp_indicator (m := m) hf hS
  have h2 := condExp_indicator (m := m) hg hS
  have h3 : P[S.indicator f | m] ≤ᵐ[P] P[S.indicator g | m] :=
    condExp_mono (hf.indicator (hm _ hS)) (hg.indicator (hm _ hS))
      (Eventually.of_forall fun ω => by
        by_cases hω : ω ∈ S
        · simp only [Set.indicator_of_mem hω]; exact hle ω hω
        · simp only [Set.indicator_of_notMem hω, le_refl])
  filter_upwards [h1, h2, h3] with ω e1 e2 e3 hω
  rw [e1, e2, Set.indicator_of_mem hω, Set.indicator_of_mem hω] at e3
  exact e3

/-- Conditional expectation of `a + b f + c g`. -/
theorem condExp_affine {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P) (a b c : ℝ) :
    P[fun ω => a + b * f ω + c * g ω | m] =ᵐ[P]
      fun ω => a + b * (P[f | m]) ω + c * (P[g | m]) ω := by
  have e : (fun ω => a + b * f ω + c * g ω) = ((fun _ => a) + b • f) + c • g := by
    ext ω; simp [smul_eq_mul]
  rw [e]
  have i1 : Integrable ((fun _ : Ω => a) + b • f) P := (integrable_const a).add (hf.smul b)
  filter_upwards [condExp_add i1 (hg.smul c) m, condExp_add (integrable_const a) (hf.smul b) m,
    condExp_smul (μ := P) b f m, condExp_smul (μ := P) c g m] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, condExp_const hm]
  simp [smul_eq_mul]

/-- Conditional expectation of `a + b f`. -/
theorem condExp_affine1 {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : Integrable f P) (a b : ℝ) :
    P[fun ω => a + b * f ω | m] =ᵐ[P] fun ω => a + b * (P[f | m]) ω := by
  have e : (fun ω => a + b * f ω) = fun ω => a + b * f ω + 0 * f ω := by ext ω; ring
  rw [e]
  filter_upwards [condExp_affine hm hf hf a b 0] with ω h
  rw [h]; ring

/-- `E_m[1_A (θ - g)] ≤ E_m |E_{m'} θ - g|` for `A ∈ m'`, `m ≤ m'`. -/
theorem condExp_indicator_sub_le {m m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] (hmm' : m ≤ m')
    (hm' : m' ≤ mΩ) {θ g : Ω → ℝ} (hθ : Integrable θ P) (hg : Integrable g P) {A : Set Ω}
    (hA : MeasurableSet[m'] A) :
    P[A.indicator (fun ω => θ ω - g ω) | m] ≤ᵐ[P]
      P[fun ω => |(P[θ | m']) ω - g ω| | m] := by
  have hm : m ≤ mΩ := hmm'.trans hm'
  have hA' : MeasurableSet A := hm' _ hA
  have e : P[A.indicator (fun ω => θ ω - g ω) | m] =ᵐ[P]
      P[A.indicator (fun ω => (P[θ | m']) ω - g ω) | m] := by
    refine condExp_congr_setIntegral hm ((hθ.sub hg).indicator hA')
      ((integrable_condExp.sub hg).indicator hA') fun s hs => ?_
    rw [setIntegral_indicator hA', setIntegral_indicator hA',
      integral_sub hθ.integrableOn hg.integrableOn,
      integral_sub integrable_condExp.integrableOn hg.integrableOn,
      setIntegral_condExp hm' hθ ((hmm' _ hs).inter hA)]
  refine e.trans_le (condExp_mono ((integrable_condExp.sub hg).indicator hA')
    (integrable_condExp.sub hg).abs (Eventually.of_forall fun ω => ?_))
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω]; exact le_abs_self _
  · simp only [Set.indicator_of_notMem hω]; exact abs_nonneg _

/-- **Lévy's upward theorem, absolute version**: `E_t |θ_∞ - θ_t| → 0` almost surely. -/
theorem tendsto_condExp_abs_sub {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (ℱ : Filtration ℕ mΩ) (θ : Ω → ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun t => (P[fun ω' => |(P[θ | ⨆ n, ℱ n]) ω' - (P[θ | ℱ t]) ω'| | ℱ t]) ω)
      atTop (𝓝 0) := by
  set θi := P[θ | ⨆ n, ℱ n] with hθi
  have h1 : ∀ r : ℚ, ∀ᵐ ω ∂P, Tendsto (fun t => (P[fun ω' => |θi ω' - r| | ℱ t]) ω) atTop
      (𝓝 (|θi ω - r|)) := by
    intro r
    have hsm : StronglyMeasurable[⨆ n, ℱ n] (fun ω' => |θi ω' - r|) := by
      have := (stronglyMeasurable_condExp (m := ⨆ n, ℱ n) (μ := P) (f := θ)).sub
        (stronglyMeasurable_const (b := (r : ℝ)))
      exact this.norm
    have hint : Integrable (fun ω' => |θi ω' - r|) P :=
      (integrable_condExp.sub (integrable_const _)).abs
    exact hint.tendsto_ae_condExp hsm
  have h2 : ∀ t : ℕ, ∀ r : ℚ, ∀ᵐ ω ∂P,
      (P[fun ω' => |θi ω' - (P[θ | ℱ t]) ω'| | ℱ t]) ω ≤
        (P[fun ω' => |θi ω' - r| | ℱ t]) ω + |(r : ℝ) - (P[θ | ℱ t]) ω| := by
    intro t r
    have i1 : Integrable (fun ω' => |θi ω' - r|) P :=
      (integrable_condExp.sub (integrable_const _)).abs
    have i2 : Integrable (fun ω' => |(r : ℝ) - (P[θ | ℱ t]) ω'|) P :=
      ((integrable_const _).sub integrable_condExp).abs
    have i0 : Integrable (fun ω' => |θi ω' - (P[θ | ℱ t]) ω'|) P :=
      (integrable_condExp.sub integrable_condExp).abs
    have hmono := condExp_mono (m := ℱ t) i0 (i1.add i2)
      (Eventually.of_forall fun ω => abs_sub_le (θi ω) (r : ℝ) ((P[θ | ℱ t]) ω))
    have hadd := condExp_add (m := ℱ t) i1 i2
    have hself : P[fun ω' => |(r : ℝ) - (P[θ | ℱ t]) ω'| | ℱ t] =
        fun ω' => |(r : ℝ) - (P[θ | ℱ t]) ω'| := by
      refine condExp_of_stronglyMeasurable (ℱ.le t) ?_ i2
      exact ((stronglyMeasurable_const (b := (r : ℝ))).sub
        (stronglyMeasurable_condExp (m := ℱ t) (μ := P) (f := θ))).norm
    filter_upwards [hmono, hadd] with ω a b
    have b' : (P[(fun ω' => |θi ω' - r|) + fun ω' => |(r : ℝ) - (P[θ | ℱ t]) ω'| | ℱ t]) ω =
        (P[fun ω' => |θi ω' - r| | ℱ t]) ω + |(r : ℝ) - (P[θ | ℱ t]) ω| := by
      rw [b, Pi.add_apply, hself]
    calc _ ≤ _ := a
      _ = _ := b'
  have h3 : ∀ᵐ ω ∂P, Tendsto (fun t => (P[θ | ℱ t]) ω) atTop (𝓝 (θi ω)) :=
    tendsto_ae_condExp θ
  have h4 : ∀ t, ∀ᵐ ω ∂P, 0 ≤ (P[fun ω' => |θi ω' - (P[θ | ℱ t]) ω'| | ℱ t]) ω := fun t =>
    condExp_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
  filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 (fun t => ae_all_iff.2 (h2 t)), h3,
    ae_all_iff.2 h4] with ω h1ω h2ω h3ω h4ω
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show θi ω - δ / 4 < θi ω + δ / 4 by linarith)
  have habs : |θi ω - r| < δ / 4 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have e1 := (h1ω r).eventually (gt_mem_nhds (show |θi ω - r| < |θi ω - r| + δ / 4 by linarith))
  have e2 := h3ω.eventually (Metric.ball_mem_nhds _ (show 0 < δ / 4 by linarith))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (e1.and e2)
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨k1, k2⟩ := hN t ht
  rw [Real.dist_eq] at k2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (h4ω t)]
  have k3 : |(r : ℝ) - (P[θ | ℱ t]) ω| < δ / 2 := by
    calc |(r : ℝ) - (P[θ | ℱ t]) ω| ≤ |(r : ℝ) - θi ω| + |θi ω - (P[θ | ℱ t]) ω| :=
          abs_sub_le _ _ _
      _ < δ / 4 + δ / 4 := by
          rw [abs_sub_comm (r : ℝ) (θi ω), abs_sub_comm (θi ω) ((P[θ | ℱ t]) ω)]
          exact add_lt_add habs k2
      _ = δ / 2 := by ring
  have := h2ω t r
  linarith

/-- If `E(min(|θ - θ_∞|, 1) | m) = 0` a.e. on `E ∈ m`, then `θ = θ_∞ = E(θ | m)` a.e. on `E`. -/
theorem eq_of_condExp_min_zero {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hm : m ≤ mΩ) {θ : Ω → ℝ} (hθ : Integrable θ P) {E : Set Ω}
    (hE : MeasurableSet[m] E)
    (h : ∀ᵐ ω ∂P, ω ∈ E → (P[fun ω => min |θ ω - (P[θ | m]) ω| 1 | m]) ω = 0) :
    ∀ᵐ ω ∂P, ω ∈ E → θ ω = (P[θ | m]) ω := by
  set g : Ω → ℝ := fun ω => min |θ ω - (P[θ | m]) ω| 1 with hg
  have hgm : AEStronglyMeasurable g P :=
    (continuous_abs.min continuous_const).comp_aestronglyMeasurable
      (hθ.1.sub integrable_condExp.1)
  have hgi : Integrable g P := by
    refine Integrable.of_bound hgm 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) zero_le_one)]
    exact min_le_right _ _
  have h0 : ∫ ω in E, g ω ∂P = 0 := by
    rw [← setIntegral_condExp hm hgi hE]
    exact setIntegral_eq_zero_of_ae_eq_zero h
  have h1 : g =ᵐ[P.restrict E] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun ω => le_min (abs_nonneg _) zero_le_one) hgi.integrableOn).1 h0
  have h2 := (ae_restrict_iff' (hm _ hE)).1 h1
  filter_upwards [h2] with ω hω hωE
  have := hω hωE
  simp only [hg, Pi.zero_apply] at this
  rcases min_cases |θ ω - (P[θ | m]) ω| 1 with ⟨e1, _⟩ | ⟨e1, _⟩
  · rw [e1, abs_eq_zero, sub_eq_zero] at this
    exact this
  · rw [e1] at this
    exact absurd this one_ne_zero

/-- If `θ = E(θ | m)` a.e. on `E ∈ m`, then `E(θ² | m) = E(θ | m)²` a.e. on `E`. -/
theorem condExp_sq_eq_on {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hm : m ≤ mΩ) {θ : Ω → ℝ} (hθ : MemLp θ 2 P) {E : Set Ω}
    (hE : MeasurableSet[m] E) (h : ∀ᵐ ω ∂P, ω ∈ E → θ ω = (P[θ | m]) ω) :
    ∀ᵐ ω ∂P, ω ∈ E → (P[fun ω => θ ω ^ 2 | m]) ω = (P[θ | m]) ω ^ 2 := by
  have hq : Integrable (fun ω => θ ω ^ 2) P := hθ.integrable_sq
  have e1 := condExp_indicator (m := m) hq hE
  have e2 : E.indicator (fun ω => θ ω ^ 2) =ᵐ[P] E.indicator (fun ω => (P[θ | m]) ω ^ 2) := by
    filter_upwards [h] with ω hω
    by_cases hωE : ω ∈ E
    · simp only [Set.indicator_of_mem hωE, hω hωE]
    · simp only [Set.indicator_of_notMem hωE]
  have hint : Integrable (E.indicator (fun ω => (P[θ | m]) ω ^ 2)) P :=
    (hq.indicator (hm _ hE)).congr e2
  have e3 : P[E.indicator (fun ω => (P[θ | m]) ω ^ 2) | m] =
      E.indicator (fun ω => (P[θ | m]) ω ^ 2) :=
    condExp_of_stronglyMeasurable hm ((stronglyMeasurable_condExp.pow 2).indicator hE) hint
  filter_upwards [e1, condExp_congr_ae (m := m) e2] with ω h1 h2 hωE
  rw [h2, e3, Set.indicator_of_mem hωE] at h1
  rw [Set.indicator_of_mem hωE] at h1
  exact h1.symm

end CC.LearnTheta.ClaimAux
