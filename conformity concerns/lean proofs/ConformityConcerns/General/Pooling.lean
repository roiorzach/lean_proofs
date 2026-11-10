import ConformityConcerns.General.CentralPooling
import ConformityConcerns.General.RevCalc

/-!
# Full pooling when no separating tail exists (Section A4)

By Proposition A3 (i) every equilibrium satisfying `D1^∞` is central pooling with cutoffs
`vlo ≤ μ ≤ vhi`, and on each separating tail the action rule solves
`a'(v) = ℓ'(v)/g'(v - a(v)) > 0`. If `vhi` is finite, then for every `d > vhi` the restriction of
`a` to `[d, ∞)` is a right-tail solution with `a(v) < v`; symmetrically for `vlo`. When the
relevant version of Lemma A3 / Corollary A1 rules out such tails, both cutoffs are infinite and
the equilibrium is fully pooling.
-/

namespace CC.General.Rev

open MeasureTheory Filter Topology Set

/-- The data of a separating upper tail `[d, ∞)` of the rule `a`. -/
def RightTail (S : Setting) (a : ℝ → ℝ) (d : ℝ) : Prop :=
  ContinuousOn a (Ici d) ∧ ContDiffOn ℝ 1 a (Ioi d) ∧ (∀ v, d ≤ v → a v < v) ∧
    ∀ v, d ≤ v → HasDerivAt a (deriv S.ℓ v / deriv S.g (v - a v)) v

/-- The data of a separating lower tail `(-∞, d]` of the rule `a`. -/
def LeftTail (S : Setting) (a : ℝ → ℝ) (d : ℝ) : Prop :=
  ContinuousOn a (Iic d) ∧ ContDiffOn ℝ 1 a (Iio d) ∧ (∀ v, v ≤ d → v < a v) ∧
    ∀ v, v ≤ d → HasDerivAt a (deriv S.ℓ v / deriv S.g (v - a v)) v

/-- If no separating tail can exist, every equilibrium satisfying `D1^∞` is fully pooling. -/
theorem const_of_noTails (S : Setting) {a : ℝ → ℝ} {φ : ℝ → Measure EReal}
    (h : S.IsCPBE a φ) (hD : S.D1Inf a φ)
    (hR : ∀ d : ℝ, S.μ < d → ¬ RightTail S a d)
    (hL : ∀ d : ℝ, d < S.μ → ¬ LeftTail S a d) :
    ∃ c : ℝ, ∀ v, a v = c := by
  obtain ⟨vlo, vhi, c, ⟨hlo, hhi, hpool, -, -, -, -⟩, hC1R, hC1L, hode⟩ := propA3_i S h hD
  have hvhi : vhi = ⊤ := by
    by_contra hne
    have hbot : vhi ≠ ⊥ := fun hb => by
      rw [hb] at hhi
      exact EReal.coe_ne_bot _ (le_bot_iff.1 hhi)
    have hH : vhi = ((vhi.toReal : ℝ) : EReal) := (EReal.coe_toReal hne hbot).symm
    have hμH : S.μ ≤ vhi.toReal := by
      rw [hH] at hhi; exact EReal.coe_le_coe_iff.1 hhi
    have htail : ∀ v : ℝ, vhi.toReal + 1 ≤ v → vhi < (v : EReal) := fun v hv => by
      rw [hH]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    apply hR (vhi.toReal + 1) (by linarith)
    refine ⟨fun v hv => (hode v (Or.inr (htail v hv))).2.continuousAt.continuousWithinAt,
      hC1R.mono (fun v hv => htail v (le_of_lt hv)), fun v hv => ?_,
      fun v hv => (hode v (Or.inr (htail v hv))).2⟩
    have hpos := (hode v (Or.inr (htail v hv))).1
    have hℓpos : 0 < deriv S.ℓ v := ℓ_deriv_pos S.hℓ (by linarith)
    have hgpos : 0 < deriv S.g (v - a v) := by
      rcases div_pos_iff.1 hpos with h' | h'
      · exact h'.2
      · exact absurd h'.1 (not_lt.2 hℓpos.le)
    have := pos_of_deriv_pos S.hg hgpos
    linarith
  have hvlo : vlo = ⊥ := by
    by_contra hne
    have htop : vlo ≠ ⊤ := fun ht => by
      rw [ht] at hlo
      exact EReal.coe_ne_top _ (top_le_iff.1 hlo)
    have hH : vlo = ((vlo.toReal : ℝ) : EReal) := (EReal.coe_toReal htop hne).symm
    have hμH : vlo.toReal ≤ S.μ := by
      rw [hH] at hlo; exact EReal.coe_le_coe_iff.1 hlo
    have htail : ∀ v : ℝ, v ≤ vlo.toReal - 1 → (v : EReal) < vlo := fun v hv => by
      rw [hH]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    apply hL (vlo.toReal - 1) (by linarith)
    refine ⟨fun v hv => (hode v (Or.inl (htail v hv))).2.continuousAt.continuousWithinAt,
      hC1L.mono (fun v hv => htail v (le_of_lt hv)), fun v hv => ?_,
      fun v hv => (hode v (Or.inl (htail v hv))).2⟩
    have hpos := (hode v (Or.inl (htail v hv))).1
    have hℓneg : deriv S.ℓ v < 0 := ℓ_deriv_neg S.hℓ (by linarith)
    have hgneg : deriv S.g (v - a v) < 0 := by
      rcases div_pos_iff.1 hpos with h' | h'
      · exact absurd h'.1 (not_lt.2 hℓneg.le)
      · exact h'.2
    have := neg_of_deriv_neg S.hg hgneg
    linarith
  refine ⟨c, fun v => hpool v ?_ ?_⟩
  · rw [hvlo]; exact EReal.bot_lt_coe v
  · rw [hvhi]; exact EReal.coe_lt_top v

end CC.General.Rev
