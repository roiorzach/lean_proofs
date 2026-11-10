import ConformityConcerns.D1Compact.Defs
import ConformityConcerns.General.CP.Convex
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Basic facts for the period game with a compact type space

Beliefs and their conformity losses, incentive compatibility, deterrence of off-path actions,
lower semicontinuity of the indifference index `I_x` on `[lo, hi]` and existence of its
minimizers, and the key step: if the belief after `x` puts no mass outside the minimizers of
`I_x`, then some minimizer `b` satisfies `-ℓ b ≤ I_x b`.
-/

namespace CC.General.Compact

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace CSetting

variable {S : CSetting}

lemma payoff_def (x v : ℝ) (ψ : Measure ℝ) :
    S.payoff x v ψ = -S.g (x - v) - ∫ b, S.ℓ b ∂ψ := rfl

lemma indiff_def (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) (x v : ℝ) :
    S.indiff a φ x v = S.U a φ v + S.g (x - v) := rfl

lemma U_def (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) (v : ℝ) :
    S.U a φ v = S.payoff (a v) v (φ (a v)) := rfl

lemma ae_mem_of_isBelief {ψ : Measure ℝ} (hψ : S.IsBelief ψ) :
    ∀ᵐ b ∂ψ, b ∈ Icc S.lo S.hi := by
  rw [ae_iff]
  exact hψ.2

lemma ae_mem_of_support_subset {ψ : Measure ℝ} {K : Set ℝ} (h : ψ.support ⊆ K) :
    ∀ᵐ b ∂ψ, b ∈ K := by
  filter_upwards [Measure.support_mem_ae (μ := ψ)] with z hz
  exact h hz

lemma integrable_of_isBelief {ψ : Measure ℝ} (hψ : S.IsBelief ψ) : Integrable S.ℓ ψ := by
  have := hψ.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (S.hℓ.continuous.continuousOn (s := Icc S.lo S.hi))
  exact Integrable.of_bound S.hℓ.continuous.aestronglyMeasurable C
    ((ae_mem_of_isBelief hψ).mono fun b hb => hC b hb)

lemma integral_le_of_ae {ψ : Measure ℝ} (hψ : S.IsBelief ψ) {K : Set ℝ}
    (hK : ∀ᵐ z ∂ψ, z ∈ K) {C : ℝ} (hC : ∀ z ∈ K, S.ℓ z ≤ C) : ∫ z, S.ℓ z ∂ψ ≤ C := by
  have := hψ.1
  calc ∫ z, S.ℓ z ∂ψ ≤ ∫ _z, C ∂ψ :=
        integral_mono_ae (integrable_of_isBelief hψ) (integrable_const C)
          (hK.mono fun z hz => hC z hz)
    _ = C := by simp

lemma le_integral_of_ae {ψ : Measure ℝ} (hψ : S.IsBelief ψ) {K : Set ℝ}
    (hK : ∀ᵐ z ∂ψ, z ∈ K) {C : ℝ} (hC : ∀ z ∈ K, C ≤ S.ℓ z) : C ≤ ∫ z, S.ℓ z ∂ψ := by
  have := hψ.1
  calc C = ∫ _z, C ∂ψ := by simp
    _ ≤ ∫ z, S.ℓ z ∂ψ :=
        integral_mono_ae (integrable_const C) (integrable_of_isBelief hψ)
          (hK.mono fun z hz => hC z hz)

lemma isBelief_dirac {b : ℝ} (hb : b ∈ Icc S.lo S.hi) : S.IsBelief (Measure.dirac b) := by
  refine ⟨inferInstance, ?_⟩
  rw [Measure.dirac_apply]
  have : b ∉ (Icc S.lo S.hi)ᶜ := fun h => h hb
  simp [Set.indicator_of_notMem this]

lemma payoff_dirac (x v b : ℝ) : S.payoff x v (Measure.dirac b) = -S.g (x - v) - S.ℓ b := by
  rw [payoff_def, integral_dirac]

lemma support_dirac_subset (b : ℝ) : (Measure.dirac b).support ⊆ {b} := by
  apply Measure.support_subset_of_isClosed isClosed_singleton
  rw [mem_ae_iff, Measure.dirac_apply]
  simp

/-- Some type in `[lo, hi]` other than `z`. -/
lemma exists_ne_mem (z : ℝ) : ∃ w ∈ Icc S.lo S.hi, w ≠ z := by
  by_cases hz : z = S.lo
  · exact ⟨S.hi, right_mem_Icc.2 S.lo_lt_hi.le, by rw [hz]; exact S.lo_lt_hi.ne'⟩
  · exact ⟨S.lo, left_mem_Icc.2 S.lo_lt_hi.le, fun h => hz h.symm⟩

namespace IsCPBE

variable {a : ℝ → ℝ} {φ : ℝ → Measure ℝ} (h : S.IsCPBE a φ)
include h

/-- No type gains from `x` under the equilibrium belief after `x`: `-∫ ℓ dφ(x) ≤ I_x(v)`. -/
lemma deter {v : ℝ} (hv : v ∈ Icc S.lo S.hi) (x : ℝ) :
    -∫ b, S.ℓ b ∂(φ x) ≤ S.indiff a φ x v := by
  have h1 := h.optimal v hv x
  rw [payoff_def] at h1
  rw [indiff_def, U_def]
  linarith

/-- Incentive compatibility: type `v` can imitate type `w`. -/
lemma ic {v : ℝ} (hv : v ∈ Icc S.lo S.hi) (w : ℝ) :
    S.U a φ w + S.g (a w - w) - S.g (a w - v) ≤ S.U a φ v := by
  have h1 := h.optimal v hv (a w)
  rw [payoff_def, payoff_def] at h1
  rw [U_def, U_def, payoff_def, payoff_def]
  linarith

/-- The indifference index is lower semicontinuous on `[lo, hi]`. -/
lemma indiff_lsc (x : ℝ) : LowerSemicontinuousOn (S.indiff a φ x) (Icc S.lo S.hi) := by
  rw [lowerSemicontinuousOn_iff]
  intro v _
  rw [lowerSemicontinuousWithinAt_iff]
  intro y hy
  have hgc : Continuous S.g := S.hg.smooth.continuous
  let f : ℝ → ℝ := fun w => S.U a φ v + S.g (a v - v) - S.g (a v - w) + S.g (x - w)
  have hfc : Continuous f :=
    (continuous_const.sub (hgc.comp (continuous_const.sub continuous_id))).add
      (hgc.comp (continuous_const.sub continuous_id))
  have hfv : f v = S.indiff a φ x v := by
    simp only [f, indiff_def]; ring
  have h1 : ∀ᶠ w in 𝓝 v, y < f w :=
    hfc.continuousAt.eventually (lt_mem_nhds (by rw [hfv]; exact hy))
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with w hw1 hw2
  have h2 := h.ic hw2 v
  rw [indiff_def]
  simp only [f] at hw1
  linarith

/-- `I_x` attains its minimum on `[lo, hi]`. -/
lemma exists_min (x : ℝ) : ∃ v₀ ∈ Icc S.lo S.hi,
    ∀ v ∈ Icc S.lo S.hi, S.indiff a φ x v₀ ≤ S.indiff a φ x v := by
  obtain ⟨v₀, hv₀, hmin⟩ := (h.indiff_lsc x).exists_isMinOn
    (nonempty_Icc.2 S.lo_lt_hi.le) isCompact_Icc
  exact ⟨v₀, hv₀, fun v hv => isMinOn_iff.1 hmin v hv⟩

lemma isCompact_sublevel (x m : ℝ) :
    IsCompact {z | z ∈ Icc S.lo S.hi ∧ S.indiff a φ x z ≤ m} := by
  obtain ⟨V, hV, hEq⟩ := (lowerSemicontinuousOn_iff_preimage_Iic.1 (h.indiff_lsc x)) m
  have : {z | z ∈ Icc S.lo S.hi ∧ S.indiff a φ x z ≤ m} = Icc S.lo S.hi ∩ V := by
    rw [← hEq]; ext z; exact Iff.rfl
  rw [this]
  exact isCompact_Icc.inter_right hV

/-- Key step: if the belief after `x` puts no mass outside the minimizers of `I_x`, then some
minimizer `b` satisfies `-ℓ b ≤ I_x b`. -/
lemma exists_good_min {x v₀ : ℝ} (hv₀ : v₀ ∈ Icc S.lo S.hi)
    (hmin : ∀ v ∈ Icc S.lo S.hi, S.indiff a φ x v₀ ≤ S.indiff a φ x v)
    (hs : ∀ᵐ z ∂(φ x), z ∈ {z | z ∈ Icc S.lo S.hi ∧ S.indiff a φ x z ≤ S.indiff a φ x v₀}) :
    ∃ b ∈ Icc S.lo S.hi, (∀ v ∈ Icc S.lo S.hi, S.indiff a φ x b ≤ S.indiff a φ x v) ∧
      -S.ℓ b ≤ S.indiff a φ x b := by
  obtain ⟨b, hbK, hbmax⟩ := (h.isCompact_sublevel x (S.indiff a φ x v₀)).exists_isMaxOn
    ⟨v₀, hv₀, le_rfl⟩ S.hℓ.continuous.continuousOn
  have h1 := integral_le_of_ae (h.belief x) hs (fun z hz => isMaxOn_iff.1 hbmax z hz)
  have h2 := h.deter hv₀ x
  have h3 := hmin b hbK.1
  refine ⟨b, hbK.1, fun v hv => hbK.2.trans (hmin v hv), ?_⟩
  linarith

end IsCPBE

end CSetting

end CC.General.Compact
