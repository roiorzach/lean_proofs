import ConformityConcerns.General.CP.Survivor
import Mathlib.Topology.Order.IntermediateValue

/-!
# Ordinary D1 on the real line gives `D1^∞` strategies

Main text, Section "Extensions Beyond the Linear-Gaussian Model", paragraph "Refinements and
central pooling": "every equilibrium satisfying D1 has the same strategy as an equilibrium
satisfying the adapted refinement".

The setting is `CC.General.Setting` (types on `ℝ` with an everywhere-positive continuous
density). An *ordinary* perfect Bayesian equilibrium uses beliefs that are probability measures
on `ℝ` (no boundary labels `±∞`). The conformity loss `∫ ℓ dβ` of a belief `β` lies in `[0, ∞]`
and may be infinite, so payoffs are compared through losses in `ℝ≥0∞` (the payoff is `-loss`).

* `Setting.IsOrdPBE`: every type optimizes; at every on-path action, beliefs put probability one
  on the pooling set, follow Bayes' rule when it has positive probability, equal `δ_v` when it
  is `{v}`; on-path conformity losses are finite.
* `Setting.OrdD1Elim`, `Setting.OrdD1Surv`, `Setting.OrdD1`: ordinary D1 (Cho and Kreps 1987).
  Type `v` is eliminated after `x` if some other type `v'` strictly gains from `x` under every
  belief under which `v` weakly gains from `x`. After an off-path action, beliefs put no mass
  outside the types that are not eliminated, unless every type is eliminated.
* `ordD1_strategy_D1Inf`: the strategy of every ordinary PBE satisfying D1 is the strategy of a
  compactified PBE satisfying `D1^∞`.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Setting

variable (S : Setting)

/-- Conformity loss `∫ ℓ dβ ∈ [0, ∞]` of a belief `β` on `ℝ`. -/
noncomputable def ordBeliefLoss (β : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ b, ENNReal.ofReal (S.ℓ b) ∂β

/-- Total loss `g(x - v) + ∫ ℓ dβ` of type `v` choosing `x` when the belief after `x` is `β`
(the payoff is `-loss`). -/
noncomputable def ordLoss (x v : ℝ) (β : Measure ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (S.g (x - v)) + S.ordBeliefLoss β

/-- A pure (ordinary) perfect Bayesian equilibrium `(a, ψ)` with beliefs on `ℝ`: (i) every type
minimizes its loss; (ii) at every on-path action `x`, beliefs put probability one on
`{v : a v = x}`, are given by Bayes' rule when this set has positive `F`-probability, and equal
`δ_v` when it is `{v}`; and on-path conformity losses are finite. -/
structure IsOrdPBE (a : ℝ → ℝ) (ψ : ℝ → Measure ℝ) : Prop where
  meas : Measurable a
  prob : ∀ x, IsProbabilityMeasure (ψ x)
  optimal : ∀ v x, S.ordLoss (a v) v (ψ (a v)) ≤ S.ordLoss x v (ψ x)
  onPath_supp : ∀ v, ψ (a v) (a ⁻¹' {a v}) = 1
  onPath_bayes : ∀ v, 0 < S.F (a ⁻¹' {a v}) → ψ (a v) = S.F[|a ⁻¹' {a v}]
  onPath_dirac : ∀ v, a ⁻¹' {a v} = {v} → ψ (a v) = Measure.dirac v
  finite : ∀ v, S.ordBeliefLoss (ψ (a v)) < ∞

/-- Ordinary D1 elimination: type `v` is eliminated after `x` if some other type `v'` gains
strictly from `x` under every belief under which `v` gains weakly from `x`. -/
def OrdD1Elim (a : ℝ → ℝ) (ψ : ℝ → Measure ℝ) (x v : ℝ) : Prop :=
  ∃ v' : ℝ, v' ≠ v ∧ ∀ β : Measure ℝ, IsProbabilityMeasure β →
    S.ordLoss x v β ≤ S.ordLoss (a v) v (ψ (a v)) →
      S.ordLoss x v' β < S.ordLoss (a v') v' (ψ (a v'))

/-- The types that ordinary D1 does not eliminate after `x`. -/
def OrdD1Surv (a : ℝ → ℝ) (ψ : ℝ → Measure ℝ) (x : ℝ) : Set ℝ :=
  {v | ¬ S.OrdD1Elim a ψ x v}

/-- Ordinary D1: after every off-path action `x`, if some type is not eliminated, the belief
puts no mass outside the types that are not eliminated. -/
def OrdD1 (a : ℝ → ℝ) (ψ : ℝ → Measure ℝ) : Prop :=
  ∀ x, x ∉ range a → (S.OrdD1Surv a ψ x).Nonempty → (ψ x).support ⊆ S.OrdD1Surv a ψ x

end Setting

/-- The beliefs of an ordinary equilibrium, as compactified beliefs. -/
noncomputable def ordEmbed (ψ : ℝ → Measure ℝ) (y : ℝ) : Measure EReal :=
  (ψ y).map (fun r : ℝ => (r : EReal))

namespace Setting

variable {S : Setting} {a : ℝ → ℝ} {ψ : ℝ → Measure ℝ} {φ : ℝ → Measure EReal}

lemma confLoss_ordEmbed (y : ℝ) : S.confLoss (ordEmbed ψ) y = S.ordBeliefLoss (ψ y) := by
  unfold Setting.confLoss ordEmbed Setting.ordBeliefLoss
  rw [EReal.measurableEmbedding_coe.lintegral_map]
  simp only [ℓbar_coe]

lemma ordBeliefLoss_dirac (b : ℝ) :
    S.ordBeliefLoss (Measure.dirac b) = ENNReal.ofReal (S.ℓ b) := by
  unfold Setting.ordBeliefLoss
  rw [lintegral_dirac]

lemma ordLoss_of_ne_top {β : Measure ℝ} (hβ : S.ordBeliefLoss β ≠ ∞) (x v : ℝ) :
    S.ordLoss x v β = ENNReal.ofReal (S.g (x - v) + (S.ordBeliefLoss β).toReal) := by
  unfold Setting.ordLoss
  rw [ENNReal.ofReal_add (S.hg.nonneg _) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hβ]

/-- Coercivity of the conformity loss: it exceeds every level somewhere. -/
lemma exists_ℓ_ge (S : Setting) (c : ℝ) : ∃ b, c ≤ S.ℓ b := by
  have h1 : 0 < S.ℓ (S.μ + 1) := by
    have := sc_min_lt S.hℓ.strictConvex S.hℓ.isMin (b := S.μ + 1) (by linarith)
    rwa [S.hℓ.zero] at this
  set t := max 1 (c / S.ℓ (S.μ + 1)) with ht
  refine ⟨S.μ + t, ?_⟩
  have ht1 : 1 ≤ t := le_max_left _ _
  have htpos : 0 < t := by linarith
  have hc := S.hℓ.strictConvex.convexOn.2 (mem_univ (S.μ + t)) (mem_univ S.μ)
    (le_of_lt (inv_pos.2 htpos)) (sub_nonneg.2 (inv_le_one_of_one_le₀ ht1)) (by ring)
  have e : t⁻¹ • (S.μ + t) + (1 - t⁻¹) • S.μ = S.μ + 1 := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [e, S.hℓ.zero] at hc
  simp only [smul_eq_mul, mul_zero, add_zero] at hc
  have h2 : t * S.ℓ (S.μ + 1) ≤ S.ℓ (S.μ + t) := by
    calc t * S.ℓ (S.μ + 1) ≤ t * (t⁻¹ * S.ℓ (S.μ + t)) := mul_le_mul_of_nonneg_left hc htpos.le
      _ = S.ℓ (S.μ + t) := by field_simp
  have h3 : c ≤ t * S.ℓ (S.μ + 1) := by
    have : c / S.ℓ (S.μ + 1) ≤ t := le_max_right _ _
    rwa [div_le_iff₀ h1] at this
  linarith

/-- In a compactified equilibrium, the on-path loss is `-U(v)`. -/
lemma IsCPBE.loss_onPath (h : S.IsCPBE a φ) (v : ℝ) :
    S.loss φ (a v) v = ENNReal.ofReal (-S.U a φ v) := by
  unfold Setting.loss Setting.U
  rw [neg_neg, ENNReal.ofReal_add (S.hg.nonneg _) ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (h.finite v).ne]

namespace IsOrdPBE

variable (h : S.IsOrdPBE a ψ)
include h

/-- The embedded beliefs form a compactified equilibrium with the same losses. -/
lemma isCPBE : S.IsCPBE a (ordEmbed ψ) where
  meas := h.meas
  prob x := by
    have := h.prob x
    unfold ordEmbed
    infer_instance
  optimal v x := by
    unfold Setting.loss
    rw [confLoss_ordEmbed, confLoss_ordEmbed]
    exact h.optimal v x
  onPath_supp v := by
    unfold ordEmbed
    rw [EReal.measurableEmbedding_coe.map_apply, preimage_image_eq _ EReal.coe_injective]
    exact h.onPath_supp v
  onPath_bayes v hpos := by
    unfold ordEmbed
    rw [h.onPath_bayes v hpos]
  onPath_dirac v hv := by
    unfold ordEmbed
    rw [h.onPath_dirac v hv, Measure.map_dirac' measurable_coe_real_ereal]
  finite v := by
    rw [confLoss_ordEmbed]
    exact h.finite v

lemma ordLoss_onPath (v : ℝ) :
    S.ordLoss (a v) v (ψ (a v)) = ENNReal.ofReal (-S.U a (ordEmbed ψ) v) := by
  rw [← h.isCPBE.loss_onPath v]
  unfold Setting.loss Setting.ordLoss
  rw [confLoss_ordEmbed]

omit h in
lemma neg_U_nonneg (v : ℝ) : 0 ≤ -S.U a (ordEmbed ψ) v := by
  have h1 := U_le (S := S) (a := a) (φ := ordEmbed ψ) v
  have h2 := S.hg.nonneg (a v - v)
  linarith

/-- Weak gain from `x` under a belief with finite conformity loss. -/
lemma weak_iff {β : Measure ℝ} (hβ : S.ordBeliefLoss β ≠ ∞) (x v : ℝ) :
    S.ordLoss x v β ≤ S.ordLoss (a v) v (ψ (a v)) ↔
      S.indiff a (ordEmbed ψ) x v ≤ -(S.ordBeliefLoss β).toReal := by
  rw [ordLoss_of_ne_top hβ, h.ordLoss_onPath, ENNReal.ofReal_le_ofReal_iff (neg_U_nonneg (S := S) (a := a) (ψ := ψ) v)]
  unfold Setting.indiff
  constructor <;> intro h' <;> linarith

/-- Strict gain from `x` under a belief with finite conformity loss. -/
lemma strict_iff {β : Measure ℝ} (hβ : S.ordBeliefLoss β ≠ ∞) (x v : ℝ) :
    S.ordLoss x v β < S.ordLoss (a v) v (ψ (a v)) ↔
      S.indiff a (ordEmbed ψ) x v < -(S.ordBeliefLoss β).toReal := by
  rw [ordLoss_of_ne_top hβ, h.ordLoss_onPath,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (add_nonneg (S.hg.nonneg _) ENNReal.toReal_nonneg)]
  unfold Setting.indiff
  constructor <;> intro h' <;> linarith

/-- A belief under which some type weakly gains has finite conformity loss. -/
lemma ne_top_of_weak {β : Measure ℝ} {x v : ℝ}
    (hw : S.ordLoss x v β ≤ S.ordLoss (a v) v (ψ (a v))) : S.ordBeliefLoss β ≠ ∞ := by
  intro htop
  rw [h.ordLoss_onPath] at hw
  unfold Setting.ordLoss at hw
  rw [htop, add_top] at hw
  exact ENNReal.ofReal_ne_top (top_le_iff.1 hw)

/-- No type gains from `x` under the equilibrium belief after `x`. -/
lemma deter (x v : ℝ) (hfin : S.ordBeliefLoss (ψ x) ≠ ∞) :
    -(S.ordBeliefLoss (ψ x)).toReal ≤ S.indiff a (ordEmbed ψ) x v := by
  have h1 := h.optimal v x
  rw [h.ordLoss_onPath, ordLoss_of_ne_top hfin,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (S.hg.nonneg _) ENNReal.toReal_nonneg)] at h1
  unfold Setting.indiff
  linarith

end IsOrdPBE

/-- If neither `±∞` survives, some finite type has a strictly lower index than both. -/
lemma exists_finite_below {x : ℝ} (htop : (⊤ : EReal) ∉ S.survivors a φ x)
    (hbot : (⊥ : EReal) ∉ S.survivors a φ x) :
    ∃ r : ℝ, S.extIndex a φ x (r : EReal) < S.extIndex a φ x ⊤ ∧
      S.extIndex a φ x (r : EReal) < S.extIndex a φ x ⊥ := by
  simp only [mem_survivors, not_forall, not_le] at htop hbot
  obtain ⟨z₁, hz₁⟩ := htop
  obtain ⟨z₂, hz₂⟩ := hbot
  induction z₁ using EReal.rec with
  | bot =>
    induction z₂ using EReal.rec with
    | bot => exact absurd hz₂ (lt_irrefl _)
    | top => exact absurd (hz₁.trans hz₂) (lt_irrefl _)
    | coe r₂ => exact ⟨r₂, hz₂.trans hz₁, hz₂⟩
  | top => exact absurd hz₁ (lt_irrefl _)
  | coe r₁ =>
    induction z₂ using EReal.rec with
    | bot => exact absurd hz₂ (lt_irrefl _)
    | top => exact ⟨r₁, hz₁, hz₁.trans hz₂⟩
    | coe r₂ =>
      rcases le_total (S.extIndex a φ x r₁) (S.extIndex a φ x r₂) with h | h
      · exact ⟨r₁, hz₁, h.trans_lt hz₂⟩
      · exact ⟨r₂, h.trans_lt hz₁, hz₂⟩

/-- If neither `±∞` survives, `I_x` attains a negative minimum on `ℝ`, and its minimizers lie
in a bounded interval. -/
lemma IsCPBE.exists_finite_min (h : S.IsCPBE a φ) {x : ℝ}
    (htop : (⊤ : EReal) ∉ S.survivors a φ x) (hbot : (⊥ : EReal) ∉ S.survivors a φ x) :
    ∃ v₀ A B : ℝ, S.indiff a φ x v₀ < 0 ∧ (∀ v, S.indiff a φ x v₀ ≤ S.indiff a φ x v) ∧
      ∀ v, S.indiff a φ x v ≤ S.indiff a φ x v₀ → v ∈ Icc A B := by
  obtain ⟨r, hr1, hr2⟩ := exists_finite_below htop hbot
  rw [extIndex_coe, extIndex_top] at hr1
  rw [extIndex_coe, extIndex_bot] at hr2
  have hcl : ∀ v, S.clipped a φ x v = min (S.indiff a φ x v) 0 := fun v => rfl
  have hJle : ∀ v, S.clipped a φ x v ≤ 0 := fun v => by rw [hcl]; exact min_le_right _ _
  have hJc : Continuous (S.clipped a φ x) := by
    have : S.clipped a φ x = fun v => min (S.indiff a φ x v) 0 := funext hcl
    rw [this]
    exact (h.indiff_continuous x).min continuous_const
  have hL : liminf (fun v : ℝ => ((S.clipped a φ x v : ℝ) : EReal)) atTop ≤ 0 :=
    liminf_le_of_frequently_le'
      (Frequently.of_forall fun v => EReal.coe_nonpos.2 (hJle v))
  have hr0 : S.clipped a φ x r < 0 := EReal.coe_neg'.1 (hr1.trans_le hL)
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf hr1)
  obtain ⟨K₂, hK₂⟩ := eventually_atBot.1 (eventually_lt_of_lt_liminf hr2)
  have hrAB : r ∈ Icc (min K₂ r) (max K₁ r) := ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨v₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨r, hrAB⟩ hJc.continuousOn
  have hv₀r := isMinOn_iff.1 hmin r hrAB
  have hout : ∀ v, v ∉ Icc (min K₂ r) (max K₁ r) → S.clipped a φ x r < S.clipped a φ x v := by
    intro v hv
    rw [mem_Icc, not_and_or, not_le, not_le] at hv
    rcases hv with hv | hv
    · exact EReal.coe_lt_coe_iff.1 (hK₂ v (hv.le.trans (min_le_left _ _)))
    · exact EReal.coe_lt_coe_iff.1 (hK₁ v ((le_max_left _ _).trans hv.le))
  have hJmin : ∀ v, S.clipped a φ x v₀ ≤ S.clipped a φ x v := by
    intro v
    by_cases hv : v ∈ Icc (min K₂ r) (max K₁ r)
    · exact isMinOn_iff.1 hmin v hv
    · exact hv₀r.trans (hout v hv).le
  have hJ0 : S.clipped a φ x v₀ < 0 := lt_of_le_of_lt hv₀r hr0
  have hI0 : S.indiff a φ x v₀ = S.clipped a φ x v₀ := by
    rw [hcl] at hJ0 ⊢
    rcases min_lt_iff.1 hJ0 with h' | h'
    · exact (min_eq_left h'.le).symm
    · exact absurd h' (lt_irrefl _)
  refine ⟨v₀, min K₂ r, max K₁ r, by rw [hI0]; exact hJ0, fun v => ?_, fun v hv => ?_⟩
  · rw [hI0]
    exact (hJmin v).trans (by rw [hcl]; exact min_le_left _ _)
  · by_contra hv'
    have h1 := hout v hv'
    have h2 : S.clipped a φ x v ≤ S.indiff a φ x v := by rw [hcl]; exact min_le_left _ _
    linarith

/-- The off-path belief: after every off-path action there is a compactified belief supported in
`S^∞(x)` that deters every type. -/
lemma IsOrdPBE.exists_offPath (h : S.IsOrdPBE a ψ) (hD : S.OrdD1 a ψ) {x : ℝ}
    (hx : x ∉ range a) :
    ∃ ν : Measure EReal, IsProbabilityMeasure ν ∧ ν.support ⊆ S.survivors a (ordEmbed ψ) x ∧
      ∀ v, S.loss (ordEmbed ψ) (a v) v ≤ ENNReal.ofReal (S.g (x - v)) + ∫⁻ z, S.ℓbar z ∂ν := by
  have h0 := h.isCPBE
  by_cases htop : (⊤ : EReal) ∈ S.survivors a (ordEmbed ψ) x
  · refine ⟨Measure.dirac ⊤, inferInstance,
      (support_dirac_subset ⊤).trans (singleton_subset_iff.2 htop), fun v => ?_⟩
    rw [lintegral_dirac, ℓbar_top, add_top]
    exact le_top
  by_cases hbot : (⊥ : EReal) ∈ S.survivors a (ordEmbed ψ) x
  · refine ⟨Measure.dirac ⊥, inferInstance,
      (support_dirac_subset ⊥).trans (singleton_subset_iff.2 hbot), fun v => ?_⟩
    rw [lintegral_dirac, ℓbar_bot, add_top]
    exact le_top
  obtain ⟨v₀, A, B, hneg, hmin, hbdd⟩ := h0.exists_finite_min htop hbot
  -- a type `b₁` with `ℓ b₁ = -I_x(v₀)`
  obtain ⟨b₀, hb₀⟩ := S.exists_ℓ_ge (-S.indiff a (ordEmbed ψ) x v₀)
  obtain ⟨b₁, -, hb₁⟩ := intermediate_value_uIcc
    (S.hℓ.continuous.continuousOn (s := uIcc S.μ b₀))
    (mem_uIcc.2 (Or.inl ⟨by rw [S.hℓ.zero]; linarith, hb₀⟩))
  have hβ₁ : S.ordBeliefLoss (Measure.dirac b₁) ≠ ∞ := by
    rw [ordBeliefLoss_dirac]; exact ENNReal.ofReal_ne_top
  have hβ₁r : (S.ordBeliefLoss (Measure.dirac b₁)).toReal = -S.indiff a (ordEmbed ψ) x v₀ := by
    rw [ordBeliefLoss_dirac, ENNReal.toReal_ofReal (S.hℓ.nonneg _), hb₁]
  -- `v₀` is not eliminated by ordinary D1
  have hsurv : v₀ ∈ S.OrdD1Surv a ψ x := by
    rintro ⟨v', -, hall⟩
    have hw := (h.weak_iff hβ₁ x v₀).2 (by rw [hβ₁r, neg_neg])
    have hs := (h.strict_iff hβ₁ x v').1 (hall _ inferInstance hw)
    rw [hβ₁r, neg_neg] at hs
    exact absurd (hmin v') (not_le.2 hs)
  -- the belief after `x` puts no mass outside the minimizers of `I_x`
  have hM : ∀ᵐ z ∂(ψ x), S.indiff a (ordEmbed ψ) x z ≤ S.indiff a (ordEmbed ψ) x v₀ := by
    have hs := hD x hx ⟨v₀, hsurv⟩
    filter_upwards [Measure.support_mem_ae (μ := ψ x)] with z hz
    have hz' := hs hz
    by_contra hlt
    push Not at hlt
    apply hz'
    refine ⟨v₀, ?_, fun β _ hw => ?_⟩
    · rintro rfl
      exact lt_irrefl _ hlt
    · have hfin := h.ne_top_of_weak hw
      have h1 := (h.weak_iff hfin x z).1 hw
      exact (h.strict_iff hfin x v₀).2 (by linarith)
  -- the minimizers form a compact set; take one with the largest conformity loss
  have hMc : IsCompact {z | S.indiff a (ordEmbed ψ) x z ≤ S.indiff a (ordEmbed ψ) x v₀} :=
    (isCompact_Icc (a := A) (b := B)).of_isClosed_subset
      (isClosed_le (h0.indiff_continuous x) continuous_const) (fun z hz => hbdd z hz)
  obtain ⟨b, hbM, hbmax⟩ := hMc.exists_isMaxOn
    ⟨v₀, show S.indiff a (ordEmbed ψ) x v₀ ≤ S.indiff a (ordEmbed ψ) x v₀ from le_rfl⟩ S.hℓ.continuous.continuousOn
  have hle : S.ordBeliefLoss (ψ x) ≤ ENNReal.ofReal (S.ℓ b) := by
    have := h.prob x
    unfold Setting.ordBeliefLoss
    calc ∫⁻ z, ENNReal.ofReal (S.ℓ z) ∂(ψ x) ≤ ∫⁻ _z, ENNReal.ofReal (S.ℓ b) ∂(ψ x) :=
          lintegral_mono_ae (hM.mono fun z hz => ENNReal.ofReal_le_ofReal (isMaxOn_iff.1 hbmax z hz))
      _ = ENNReal.ofReal (S.ℓ b) := by simp
  have hfin : S.ordBeliefLoss (ψ x) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hdet := h.deter x v₀ hfin
  have htr : (S.ordBeliefLoss (ψ x)).toReal ≤ S.ℓ b :=
    ENNReal.toReal_le_of_le_ofReal (S.hℓ.nonneg b) hle
  have hbℓ : -S.ℓ b ≤ S.indiff a (ordEmbed ψ) x v₀ := by linarith
  have hbI : S.indiff a (ordEmbed ψ) x b = S.indiff a (ordEmbed ψ) x v₀ :=
    le_antisymm hbM (hmin b)
  refine ⟨Measure.dirac (b : EReal), inferInstance,
    (support_dirac_subset _).trans (singleton_subset_iff.2 ?_), fun v => ?_⟩
  · have hcl : S.clipped a (ordEmbed ψ) x b = S.indiff a (ordEmbed ψ) x v₀ := by
      unfold Setting.clipped
      rw [hbI]
      exact min_eq_left hneg.le
    have hge : ∀ v, S.indiff a (ordEmbed ψ) x v₀ ≤ S.clipped a (ordEmbed ψ) x v :=
      fun v => le_min (hmin v) hneg.le
    intro z
    rw [extIndex_coe, hcl]
    induction z using EReal.rec with
    | bot =>
      rw [extIndex_bot]
      exact le_liminf_of_le (by isBoundedDefault)
        (Eventually.of_forall fun v => EReal.coe_le_coe_iff.2 (hge v))
    | coe r =>
      rw [extIndex_coe]
      exact EReal.coe_le_coe_iff.2 (hge r)
    | top =>
      rw [extIndex_top]
      exact le_liminf_of_le (by isBoundedDefault)
        (Eventually.of_forall fun v => EReal.coe_le_coe_iff.2 (hge v))
  · rw [lintegral_dirac, ℓbar_coe, h0.loss_onPath v,
      ← ENNReal.ofReal_add (S.hg.nonneg _) (S.hℓ.nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := hmin v
    have h2 : S.indiff a (ordEmbed ψ) x v = S.U a (ordEmbed ψ) v + S.g (x - v) := rfl
    linarith

end Setting

/-- **Main text, ordinary D1 versus the adapted refinement.** On the real line, the strategy of
every ordinary perfect Bayesian equilibrium satisfying D1 is the strategy of a compactified
perfect Bayesian equilibrium satisfying `D1^∞`. -/
theorem ordD1_strategy_D1Inf (S : Setting) (a : ℝ → ℝ) :
    (∃ ψ : ℝ → Measure ℝ, S.IsOrdPBE a ψ ∧ S.OrdD1 a ψ) →
      ∃ φ : ℝ → Measure EReal, S.IsCPBE a φ ∧ S.D1Inf a φ := by
  classical
  rintro ⟨ψ, h, hD⟩
  have h0 := h.isCPBE
  choose! N hNprob hNsupp hNdet using fun x (hx : x ∉ range a) => h.exists_offPath hD hx
  obtain ⟨φ, hon, hoff⟩ : ∃ φ : ℝ → Measure EReal, (∀ y ∈ range a, φ y = ordEmbed ψ y) ∧
      (∀ x ∉ range a, φ x = N x) :=
    ⟨fun x => if x ∈ range a then ordEmbed ψ x else N x,
      fun y hy => by simp [hy], fun x hx => by simp [hx]⟩
  have hav : ∀ v, φ (a v) = ordEmbed ψ (a v) := fun v => hon _ (mem_range_self v)
  have hU : S.U a φ = S.U a (ordEmbed ψ) := by
    funext v
    unfold Setting.U Setting.confLoss
    rw [hav v]
  have hsurv : ∀ x, S.survivors a φ x = S.survivors a (ordEmbed ψ) x := by
    intro x
    unfold Setting.survivors Setting.extIndex Setting.clipped Setting.indiff
    rw [hU]
  have hloss : ∀ v, S.loss φ (a v) v = S.loss (ordEmbed ψ) (a v) v := by
    intro v
    unfold Setting.loss Setting.confLoss
    rw [hav v]
  refine ⟨φ, ⟨h0.meas, fun x => ?_, fun v x => ?_, fun v => ?_, fun v hpos => ?_,
    fun v hv => ?_, fun v => ?_⟩, fun x hx => ?_⟩
  · by_cases hx : x ∈ range a
    · rw [hon x hx]; exact h0.prob x
    · rw [hoff x hx]; exact hNprob x hx
  · rw [hloss v]
    by_cases hx : x ∈ range a
    · have : S.loss φ x v = S.loss (ordEmbed ψ) x v := by
        unfold Setting.loss Setting.confLoss
        rw [hon x hx]
      rw [this]
      exact h0.optimal v x
    · unfold Setting.loss Setting.confLoss
      rw [hoff x hx]
      have := hNdet x hx v
      unfold Setting.loss Setting.confLoss at this
      exact this
  · rw [hav v]; exact h0.onPath_supp v
  · rw [hav v]; exact h0.onPath_bayes v hpos
  · rw [hav v]; exact h0.onPath_dirac v hv
  · unfold Setting.confLoss
    rw [hav v]
    exact h0.finite v
  · rw [hoff x hx, hsurv x]
    exact hNsupp x hx

end CC.General
