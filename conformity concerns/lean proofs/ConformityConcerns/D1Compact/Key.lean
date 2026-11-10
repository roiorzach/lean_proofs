import ConformityConcerns.D1Compact.Basic

/-!
# Both refinements reduce to one condition

For an equilibrium `(a, φ)` of the compact game and an off-path action `x`, let `m` be the
minimum of `I_x` on `[lo, hi]`. Both `D1^∞` and ordinary D1 imply the condition `KeyCond`:
some minimizer `b` of `I_x` has `-ℓ b ≤ m`. Conversely, if `KeyCond` holds at every off-path
action, replacing each off-path belief by `δ_b` gives an equilibrium with the same strategy
that satisfies both refinements.
-/

namespace CC.General.Compact

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace CSetting

variable {S : CSetting} {a : ℝ → ℝ} {φ : ℝ → Measure ℝ}

/-- Some minimizer `b` of `I_x` on `[lo, hi]` satisfies `-ℓ b ≤ I_x b`. -/
def KeyCond (S : CSetting) (a : ℝ → ℝ) (φ : ℝ → Measure ℝ) (x : ℝ) : Prop :=
  ∃ b ∈ Icc S.lo S.hi, (∀ v ∈ Icc S.lo S.hi, S.indiff a φ x b ≤ S.indiff a φ x v) ∧
    -S.ℓ b ≤ S.indiff a φ x b

/-- `D1^∞` implies the key condition. -/
lemma keyCond_of_D1Inf (h : S.IsCPBE a φ) (hD : S.D1Inf a φ) {x : ℝ}
    (hx : x ∉ a '' Icc S.lo S.hi) : S.KeyCond a φ x := by
  obtain ⟨v₀, hv₀, hmin⟩ := h.exists_min x
  by_cases h0 : 0 ≤ S.indiff a φ x v₀
  · exact ⟨v₀, hv₀, hmin, by linarith [S.hℓ.nonneg v₀]⟩
  · push Not at h0
    apply h.exists_good_min hv₀ hmin
    apply ae_mem_of_support_subset ((hD x hx).trans _)
    intro z hz
    refine ⟨hz.1, ?_⟩
    have h1 := hz.2 v₀ hv₀
    unfold CSetting.clipped at h1
    rw [min_eq_left h0.le] at h1
    rcases min_le_iff.1 h1 with h2 | h2
    · exact h2
    · linarith

/-- Intermediate value step: a type in `[lo, hi]` with conformity loss exactly `c`. -/
lemma exists_ℓ_eq {b₁ b₂ c : ℝ} (hb₁ : b₁ ∈ Icc S.lo S.hi) (hb₂ : b₂ ∈ Icc S.lo S.hi)
    (h₁ : S.ℓ b₁ ≤ c) (h₂ : c ≤ S.ℓ b₂) : ∃ b ∈ Icc S.lo S.hi, S.ℓ b = c := by
  obtain ⟨b, hb, hbc⟩ := intermediate_value_uIcc
    (S.hℓ.continuous.continuousOn (s := uIcc b₁ b₂)) (mem_uIcc.2 (Or.inl ⟨h₁, h₂⟩))
  exact ⟨b, uIcc_subset_Icc hb₁ hb₂ hb, hbc⟩

/-- Ordinary D1 implies the key condition. -/
lemma keyCond_of_D1 (h : S.IsCPBE a φ) (hD : S.D1 a φ) {x : ℝ}
    (hx : x ∉ a '' Icc S.lo S.hi) : S.KeyCond a φ x := by
  obtain ⟨v₀, hv₀, hmin⟩ := h.exists_min x
  by_contra hK
  have hv₀ℓ : S.indiff a φ x v₀ < -S.ℓ v₀ := by
    by_contra hc
    push Not at hc
    exact hK ⟨v₀, hv₀, hmin, hc⟩
  -- a type with the largest conformity loss
  obtain ⟨b₀, hb₀, hb₀max⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 S.lo_lt_hi.le)
    (S.hℓ.continuous.continuousOn (s := Icc S.lo S.hi))
  have hb₀ℓ : -S.indiff a φ x v₀ ≤ S.ℓ b₀ := by
    have h1 := integral_le_of_ae (h.belief x) (ae_mem_of_isBelief (h.belief x))
      (fun z hz => isMaxOn_iff.1 hb₀max z hz)
    have h2 := h.deter hv₀ x
    linarith
  obtain ⟨b₁, hb₁, hb₁ℓ⟩ := exists_ℓ_eq hv₀ hb₀ (by linarith) hb₀ℓ
  -- `v₀` is not eliminated
  have hsurv : v₀ ∈ S.D1Surv a φ x := by
    refine ⟨hv₀, ?_⟩
    rintro ⟨v', hv', -, hall⟩
    have hw : S.U a φ v₀ ≤ S.payoff x v₀ (Measure.dirac b₁) := by
      rw [payoff_dirac, hb₁ℓ]
      have := indiff_def (S := S) a φ x v₀
      linarith
    have h1 := hall (Measure.dirac b₁) (isBelief_dirac hb₁) hw
    rw [payoff_dirac, hb₁ℓ] at h1
    have h2 := hmin v' hv'
    have h3 := indiff_def (S := S) a φ x v₀
    have h4 := indiff_def (S := S) a φ x v'
    linarith
  apply hK
  apply h.exists_good_min hv₀ hmin
  apply ae_mem_of_support_subset ((hD x hx ⟨v₀, hsurv⟩).trans _)
  intro z hz
  refine ⟨hz.1, ?_⟩
  by_contra hlt
  push Not at hlt
  apply hz.2
  refine ⟨v₀, hv₀, ?_, ?_⟩
  · rintro rfl
    exact lt_irrefl _ hlt
  · intro ψ _ hweak
    rw [payoff_def] at hweak ⊢
    rw [indiff_def, indiff_def] at hlt
    linarith

/-- If the key condition holds at every off-path action, replacing each off-path belief by a
Dirac belief gives an equilibrium with the same strategy satisfying both refinements. -/
lemma exists_refined (h : S.IsCPBE a φ)
    (hK : ∀ x, x ∉ a '' Icc S.lo S.hi → S.KeyCond a φ x) :
    ∃ φ' : ℝ → Measure ℝ, S.IsCPBE a φ' ∧ S.D1 a φ' ∧ S.D1Inf a φ' := by
  classical
  choose! B hBT hBmin hBℓ using hK
  obtain ⟨φ', hon, hoff⟩ : ∃ φ' : ℝ → Measure ℝ, (∀ y ∈ a '' Icc S.lo S.hi, φ' y = φ y) ∧
      (∀ x ∉ a '' Icc S.lo S.hi, φ' x = Measure.dirac (B x)) :=
    ⟨fun x => if x ∈ a '' Icc S.lo S.hi then φ x else Measure.dirac (B x),
      fun y hy => by simp [hy], fun x hx => by simp [hx]⟩
  have hav : ∀ v ∈ Icc S.lo S.hi, φ' (a v) = φ (a v) :=
    fun v hv => hon _ (mem_image_of_mem a hv)
  have hU : ∀ v ∈ Icc S.lo S.hi, S.U a φ' v = S.U a φ v := by
    intro v hv
    rw [U_def, U_def, hav v hv]
  have hI : ∀ x, ∀ v ∈ Icc S.lo S.hi, S.indiff a φ' x v = S.indiff a φ x v := by
    intro x v hv
    rw [indiff_def, indiff_def, hU v hv]
  refine ⟨φ', ⟨h.meas, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ a '' Icc S.lo S.hi
    · rw [hon x hx]; exact h.belief x
    · rw [hoff x hx]; exact isBelief_dirac (hBT x hx)
  · intro v hv x
    rw [hav v hv]
    by_cases hx : x ∈ a '' Icc S.lo S.hi
    · rw [hon x hx]; exact h.optimal v hv x
    · rw [hoff x hx, payoff_dirac]
      have h1 := hBℓ x hx
      have h2 := hBmin x hx v hv
      have h3 := indiff_def (S := S) a φ x v
      have h4 := U_def (S := S) a φ v
      linarith
  · intro v hv
    rw [hav v hv]; exact h.onPath_supp v hv
  · intro v hv hpos
    rw [hav v hv]; exact h.onPath_bayes v hv hpos
  · intro v hv hT
    rw [hav v hv]; exact h.onPath_dirac v hv hT
  · -- ordinary D1
    intro x hx hne
    rw [hoff x hx]
    refine (support_dirac_subset _).trans ?_
    rw [singleton_subset_iff]
    refine ⟨hBT x hx, ?_⟩
    rintro ⟨v', hv', -, hall⟩
    obtain ⟨z, hz⟩ := hne
    by_cases hlow : ∃ b₂ ∈ Icc S.lo S.hi, S.ℓ b₂ ≤ -S.indiff a φ x (B x)
    · obtain ⟨b₂, hb₂, hb₂ℓ⟩ := hlow
      obtain ⟨b₁, hb₁, hb₁ℓ⟩ := exists_ℓ_eq hb₂ (hBT x hx) hb₂ℓ (by linarith [hBℓ x hx])
      have hw : S.U a φ' (B x) ≤ S.payoff x (B x) (Measure.dirac b₁) := by
        rw [payoff_dirac, hb₁ℓ, hU _ (hBT x hx)]
        have := indiff_def (S := S) a φ x (B x)
        linarith
      have h1 := hall (Measure.dirac b₁) (isBelief_dirac hb₁) hw
      rw [payoff_dirac, hb₁ℓ, hU v' hv'] at h1
      have h2 := hBmin x hx v' hv'
      have h3 := indiff_def (S := S) a φ x (B x)
      have h4 := indiff_def (S := S) a φ x v'
      linarith
    · push Not at hlow
      apply hz.2
      obtain ⟨bm, hbm, hbmmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 S.lo_lt_hi.le)
        (S.hℓ.continuous.continuousOn (s := Icc S.lo S.hi))
      obtain ⟨w, hw, hwz⟩ := S.exists_ne_mem z
      refine ⟨w, hw, hwz, fun ψ hψ hweak => ?_⟩
      exfalso
      have h1 := le_integral_of_ae hψ (ae_mem_of_isBelief hψ)
        (fun y hy => isMinOn_iff.1 hbmmin y hy)
      have h2 := hlow bm hbm
      have h3 := hBmin x hx z hz.1
      rw [hU z hz.1, payoff_def] at hweak
      have h4 := indiff_def (S := S) a φ x z
      linarith
  · -- `D1^∞`
    intro x hx
    rw [hoff x hx]
    refine (support_dirac_subset _).trans ?_
    rw [singleton_subset_iff]
    refine ⟨hBT x hx, fun z' hz' => ?_⟩
    unfold CSetting.clipped
    rw [hI x _ (hBT x hx), hI x z' hz']
    exact min_le_min_right 0 (hBmin x hx z' hz')

end CSetting

end CC.General.Compact
