import ConformityConcerns.Dynamics.Defs
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.Rat.Cast.Order

/-!
# I.i.d. sequences: strong law for frequencies, infinitely many visits
-/

namespace CC

open MeasureTheory ProbabilityTheory Filter Topology Set

section
variable {α : Type*} [MeasurableSpace α] (G : Measure α) [IsProbabilityMeasure G]

/-- Strong law of large numbers for the frequency of visits to a measurable set. -/
lemma slln_freq {s : Set α} (hs : MeasurableSet s) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => G),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, s.indicator (fun _ => (1 : ℝ)) (ω i)) / n)
        atTop (𝓝 (G s).toReal) := by
  set P := Measure.infinitePi fun _ : ℕ => G
  set f : α → ℝ := s.indicator (fun _ => 1) with hfdef
  have hf : Measurable f := measurable_const.indicator hs
  set X : ℕ → (ℕ → α) → ℝ := fun i ω => f (ω i) with hX
  have hind : iIndepFun X P :=
    iIndepFun_infinitePi (P := fun _ => G) (X := fun _ => f) (fun _ => hf)
  have hmeas : ∀ i, Measurable (X i) := fun i => hf.comp (measurable_pi_apply i)
  have hmap : ∀ i, P.map (X i) = G.map f := by
    intro i
    have : X i = f ∘ fun ω => ω i := rfl
    rw [this, ← Measure.map_map hf (measurable_pi_apply i), Measure.infinitePi_map_eval]
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    { aemeasurable_fst := (hmeas i).aemeasurable
      aemeasurable_snd := (hmeas 0).aemeasurable
      map_eq := by rw [hmap i, hmap 0] }
  have hbd : ∀ ω, ‖X 0 ω‖ ≤ 1 := by
    intro ω
    simp only [hX, hfdef]
    by_cases hω : ω 0 ∈ s <;> simp [hω]
  have hint : Integrable (X 0) P :=
    (integrable_const (1 : ℝ)).mono' (hmeas 0).aestronglyMeasurable (ae_of_all _ hbd)
  have hE : ∫ ω, X 0 ω ∂P = (G s).toReal := by
    have : ∫ ω, X 0 ω ∂P = ∫ x, f x ∂(P.map fun ω => ω 0) := by
      have hm : Measurable fun ω : ℕ → α => ω 0 := measurable_pi_apply 0
      rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
    rw [this, Measure.infinitePi_map_eval, hfdef, integral_indicator_const _ hs, smul_eq_mul,
      mul_one, measureReal_def]
  have := strong_law_ae_real X hint (fun i j hij => hind.indepFun hij) hident
  filter_upwards [this] with ω hω
  rw [hE] at hω
  exact hω

omit [MeasurableSpace α] in
lemma sum_indicator_eq_card (s : Set α) (ω : ℕ → α) (n : ℕ) [DecidablePred fun i => ω i ∈ s] :
    ∑ i ∈ Finset.range n, s.indicator (fun _ => (1 : ℝ)) (ω i) =
      (((Finset.range n).filter fun i => ω i ∈ s).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ω i ∈ s <;> simp [h]

/-- Strong law for counts, in the `Finset.filter` form. -/
lemma slln_count {s : Set α} (hs : MeasurableSet s) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => G),
      haveI := Classical.decPred fun i => ω i ∈ s
      Tendsto (fun n : ℕ => (((Finset.range n).filter fun i => ω i ∈ s).card : ℝ) / n)
        atTop (𝓝 (G s).toReal) := by
  filter_upwards [slln_freq G hs] with ω hω
  classical
  refine hω.congr fun n => ?_
  rw [sum_indicator_eq_card]

/-- A set of positive probability is visited infinitely often, almost surely. -/
lemma ae_frequently_mem {s : Set α} (hs : MeasurableSet s) (hpos : 0 < G s) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => G), ∃ᶠ n in atTop, ω n ∈ s := by
  filter_upwards [slln_freq G hs] with ω hω
  by_contra h
  rw [not_frequently] at h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have hbound : ∀ n, ∑ i ∈ Finset.range n, s.indicator (fun _ => (1 : ℝ)) (ω i) ≤ N := by
    intro n
    calc ∑ i ∈ Finset.range n, s.indicator (fun _ => (1 : ℝ)) (ω i)
        ≤ ∑ i ∈ Finset.range N, s.indicator (fun _ => (1 : ℝ)) (ω i) := by
          rcases le_total n N with hnN | hnN
          · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hnN)
              fun i _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
          · rw [← Finset.sum_range_add_sum_Ico _ hnN]
            have : ∑ i ∈ Finset.Ico N n, s.indicator (fun _ => (1 : ℝ)) (ω i) = 0 := by
              refine Finset.sum_eq_zero fun i hi => ?_
              rw [Set.indicator_of_notMem (hN i (Finset.mem_Ico.1 hi).1)]
            rw [this, add_zero]
      _ ≤ ∑ i ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Set.indicator_le_self' (fun _ _ => zero_le_one) _
      _ = N := by simp
  have h0 : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hle : (G s).toReal ≤ 0 := by
    refine le_of_tendsto_of_tendsto hω h0 (Eventually.of_forall fun n => ?_)
    exact div_le_div_of_nonneg_right (hbound n) (Nat.cast_nonneg n)
  have : 0 < (G s).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top G s)
  linarith

/-- If `G sᶜ = 0`, then almost surely every coordinate lies in `s`. -/
lemma ae_forall_mem {s : Set α} (hs : MeasurableSet s) (h : G sᶜ = 0) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => G), ∀ n, ω n ∈ s := by
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  have : {ω : ℕ → α | ¬ ω n ∈ s} = (fun ω => ω n) ⁻¹' sᶜ := rfl
  rw [this, ← Measure.map_apply (measurable_pi_apply n) hs.compl, Measure.infinitePi_map_eval, h]

end

/-- Visits to rational intervals give visits to all real intervals. -/
lemma visits_of_rat {P : ℕ → Prop} {x : ℕ → ℝ}
    (h : ∀ p q : ℚ, (0 : ℝ) ≤ p → (p : ℝ) < q → (q : ℝ) ≤ 1 → ∃ᶠ t in atTop, P t ∧ x t ∈ Ioo (p : ℝ) q) :
    ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ᶠ t in atTop, P t ∧ x t ∈ Ioo a b := by
  intro a b ha hab hb
  obtain ⟨p, hap, hpb⟩ := exists_rat_btwn hab
  obtain ⟨q, hpq, hqb⟩ := exists_rat_btwn hpb
  refine (h p q (by linarith) hpq (by linarith)).mono fun t ht => ⟨ht.1, ?_, ?_⟩
  · linarith [ht.2.1]
  · linarith [ht.2.2]

end CC
