import ConformityConcerns.General.CP.Survivor
import Mathlib.Topology.Order.LeftRightLim

/-!
# No jumps on separating tails

On an open set `O` of separating types (`T(a v) = {v}`), the action rule is continuous: at a
jump `α < β` of the monotone rule at `v₀`, continuity of `U` forces `α = v₀ - d`, `β = v₀ + d`
with `a(v₀) ∈ {α, β}`, and an off-path action strictly between `a(v₀)` and `v₀` is a profitable
deviation for `v₀` once `D1^∞` forces the belief `δ_{v₀}`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Setting.IsCPBE

variable {S : Setting} {a : ℝ → ℝ} {φ : ℝ → Measure EReal} (h : S.IsCPBE a φ)
  (hD : S.D1Inf a φ)
include h hD

lemma continuousAt_of_sep {O : Set ℝ} (hO : IsOpen O)
    (hsep : ∀ v ∈ O, a ⁻¹' {a v} = {v}) {v₀ : ℝ} (hv₀ : v₀ ∈ O) : ContinuousAt a v₀ := by
  have hmono := h.monotone
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  set α := Function.leftLim a v₀ with hαdef
  set β := Function.rightLim a v₀ with hβdef
  have hαa : α ≤ a v₀ := hmono.leftLim_le le_rfl
  have haβ : a v₀ ≤ β := hmono.le_rightLim le_rfl
  by_contra hne
  have hαβ : α < β := lt_of_le_of_ne (hαa.trans haβ) hne
  have hGc : Continuous (fun v => -S.U a φ v - S.ℓ v) :=
    (h.U_continuous.neg).sub S.hℓ.continuous
  have hGO : ∀ v ∈ O, S.g (a v - v) = -S.U a φ v - S.ℓ v := by
    intro v hv; rw [h.U_sep (hsep v hv)]; ring
  have hOn : O ∈ 𝓝 v₀ := hO.mem_nhds hv₀
  have hgc := S.hg.smooth.continuous
  have hleft : S.g (α - v₀) = S.g (a v₀ - v₀) := by
    have t1 : Tendsto (fun v => S.g (a v - v)) (𝓝[<] v₀) (𝓝 (S.g (α - v₀))) :=
      (hgc.tendsto _).comp
        ((hmono.tendsto_leftLim v₀).sub (tendsto_id.mono_left nhdsWithin_le_nhds))
    have t2 : Tendsto (fun v => S.g (a v - v)) (𝓝[<] v₀) (𝓝 (-S.U a φ v₀ - S.ℓ v₀)) := by
      refine ((hGc.tendsto v₀).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [nhdsWithin_le_nhds hOn] with v hv
      exact (hGO v hv).symm
    rw [tendsto_nhds_unique t1 t2, ← hGO v₀ hv₀]
  have hright : S.g (β - v₀) = S.g (a v₀ - v₀) := by
    have t1 : Tendsto (fun v => S.g (a v - v)) (𝓝[>] v₀) (𝓝 (S.g (β - v₀))) :=
      (hgc.tendsto _).comp
        ((hmono.tendsto_rightLim v₀).sub (tendsto_id.mono_left nhdsWithin_le_nhds))
    have t2 : Tendsto (fun v => S.g (a v - v)) (𝓝[>] v₀) (𝓝 (-S.U a φ v₀ - S.ℓ v₀)) := by
      refine ((hGc.tendsto v₀).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [nhdsWithin_le_nhds hOn] with v hv
      exact (hGO v hv).symm
    rw [tendsto_nhds_unique t1 t2, ← hGO v₀ hv₀]
  have hαβ' : α - v₀ = -(β - v₀) := by
    rcases S.hg.eq_or_eq_neg (hleft.trans hright.symm) with h1 | h1
    · exfalso; linarith
    · exact h1
  have hd : 0 < β - v₀ := by linarith
  have hU : ∀ w, -S.g (a v₀ - w) - S.ℓ v₀ ≤ S.U a φ w := by
    intro w; have := h.ic w v₀; rw [h.U_sep (hsep v₀ hv₀)] at this; linarith
  have hUh : S.U a φ v₀ = -S.g (a v₀ - v₀) - S.ℓ v₀ := by rw [h.U_sep (hsep v₀ hv₀)]; ring
  have hbelow : ∀ w, w < v₀ → a w ≤ α := fun w hw => hmono.le_leftLim hw
  have habove : ∀ w, v₀ < w → β ≤ a w := fun w hw => hmono.rightLim_le hw
  rcases S.hg.eq_or_eq_neg hright.symm with h1 | h1
  · -- `a v₀ = β = v₀ + d`: downward deviation to `x = v₀ + d / 2`
    have hx : v₀ + (β - v₀) / 2 < a v₀ := by linarith
    refine h.d1_contra_down hD (x := v₀ + (β - v₀) / 2) (y₀ := a v₀) (K := S.ℓ v₀) (hb := v₀)
      hx ?_ hU hUh ?_ ?_
    · rintro ⟨w, hw⟩
      rcases lt_trichotomy w v₀ with hw' | hw' | hw'
      · have := hbelow w hw'; linarith
      · subst hw'; linarith
      · have := habove w hw'; linarith
    · intro r hr; have := hbelow r hr; linarith
    · rw [hUh]
      have := S.hg.lt_of_abs_lt (s := v₀ + (β - v₀) / 2 - v₀) (t := a v₀ - v₀)
        (by rw [abs_of_pos (show (0 : ℝ) < v₀ + (β - v₀) / 2 - v₀ by linarith),
              abs_of_pos (show (0 : ℝ) < a v₀ - v₀ by linarith)]; linarith)
      linarith
  · -- `a v₀ = α = v₀ - d`: upward deviation to `x = v₀ - d / 2`
    have hx : a v₀ < v₀ - (β - v₀) / 2 := by linarith
    refine h.d1_contra_up hD (x := v₀ - (β - v₀) / 2) (y₀ := a v₀) (K := S.ℓ v₀) (hb := v₀)
      hx ?_ hU hUh ?_ ?_
    · rintro ⟨w, hw⟩
      rcases lt_trichotomy w v₀ with hw' | hw' | hw'
      · have := hbelow w hw'; linarith
      · subst hw'; linarith
      · have := habove w hw'; linarith
    · intro r hr; have := habove r hr; linarith
    · rw [hUh]
      have := S.hg.lt_of_abs_lt (s := v₀ - (β - v₀) / 2 - v₀) (t := a v₀ - v₀)
        (by rw [abs_of_neg (show v₀ - (β - v₀) / 2 - v₀ < 0 by linarith),
              abs_of_neg (show a v₀ - v₀ < 0 by linarith)]; linarith)
      linarith

end Setting.IsCPBE

end CC.General
