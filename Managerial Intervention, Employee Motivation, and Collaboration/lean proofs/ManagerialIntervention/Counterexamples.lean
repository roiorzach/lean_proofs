import ManagerialIntervention.Examples

/-!
# Counterexamples

* `MI.prop5_counterexample` — **Proposition 5 is false as stated.**  Two environments `E1`, `E2`
  with identical primitives (quadratic costs, so `h_a` is linear), `α_a(E1) = -3/2 < -1 =
  α_a(E2)`, and a continuous involvement cost `g` with `g → ∞` at `0` and at `∞`, such that
  `μ*(α_a(E1)) ≤ μ*(α_a(E2))` fails in the strong set order.  The mechanism: with `α_a < 0`
  the agent's centralized effort is truncated at zero once the principal's effort is high
  (the `max{0, ·}` in (A Effort: Centralization)), which the proof's cross-partial
  computation ignores.
* `MI.prop4_boundary`, `MI.propB1_boundary` — at `α_p = 1` no threshold satisfying the
  "iff" of Propositions 4/B.1 can lie strictly below `α̃(1) = 1`.
* `MI.prop3b_concave_equal` — with `h` strictly concave and `α_a = α_p = 1`, the agent's
  efforts under centralization and delegation are equal, so in Proposition 3(b) "lower"
  can only mean "weakly lower".
-/

namespace MI

open Set Filter Topology

/-! ### Proposition 5 -/

section Prop3

/-- The common primitives of `E1` and `E2`. -/
noncomputable abbrev π0 : Prim := E1.prim

lemma π0_A : π0.A = 1 / 2 := E1_A
lemma π0_Na : π0.Na = -1 := E1_Na
lemma π0_Np : π0.Np = -1 / 2 := E1_Np
lemma π0_ca : π0.ca = cq2 := rfl
lemma π0_cp : π0.cp = cq1 := rfl
lemma π0_valid : π0.Valid := E1.prim_valid

lemma pMu_fifth : π0.pMu (1 / 5) = 1 / 10 := by
  unfold Prim.pMu
  rw [π0_Np, π0_cp, Cost.quad_br (by norm_num) (by norm_num)]
  norm_num

lemma pMu_one : π0.pMu 1 = 1 / 2 := by
  unfold Prim.pMu
  rw [π0_Np, π0_cp, Cost.quad_br (by norm_num) (by norm_num)]
  norm_num

lemma eMu_fifth_a : π0.eMu (-3 / 2) (1 / 5) = 7 / 40 := by
  unfold Prim.eMu
  rw [pMu_fifth, π0_A, π0_Na, π0_ca, Cost.quad_br (by norm_num) (by norm_num)]
  norm_num

lemma eMu_fifth_b : π0.eMu (-1) (1 / 5) = 1 / 5 := by
  unfold Prim.eMu
  rw [pMu_fifth, π0_A, π0_Na, π0_ca, Cost.quad_br (by norm_num) (by norm_num)]
  norm_num

/-- For `μ ≥ 1` and `α ≤ -1` the agent exerts no effort. -/
lemma eMu_zero {α μ : ℝ} (hα : α ≤ -1) (hμ : 1 ≤ μ) : π0.eMu α μ = 0 := by
  unfold Prim.eMu
  apply Cost.br_eq_zero_of_nonpos
  have hp : 1 / 2 ≤ π0.pMu μ := pMu_one ▸ Prim.pMu_mono π0_valid hμ
  rw [π0_A, π0_Na]
  nlinarith

/-- The involvement cost of the counterexample. -/
noncomputable def gCE (μ : ℝ) : ℝ := π0.FMu (-3 / 2) μ + max 0 (μ⁻¹ - 5) + max 0 (μ - 1)

lemma gCE_continuousOn : ContinuousOn gCE (Ioi 0) := by
  unfold gCE
  refine ((Prim.FMu_continuousOn (-3 / 2)).add ?_).add ?_
  · exact continuousOn_const.sup
      ((continuousOn_inv₀.mono fun x (hx : 0 < x) => hx.ne').sub continuousOn_const)
  · exact (continuous_const.max (continuous_id.sub continuous_const)).continuousOn

lemma gCE_ge_inv {μ : ℝ} (hμ : 0 < μ) : μ⁻¹ + -5 ≤ gCE μ := by
  unfold gCE
  have := Prim.FMu_nonneg π0_valid (-3 / 2) hμ
  have := le_max_right 0 (μ⁻¹ - 5)
  have := le_max_left 0 (μ - 1)
  linarith

lemma gCE_ge_id {μ : ℝ} (hμ : 0 < μ) : μ + -1 ≤ gCE μ := by
  unfold gCE
  have := Prim.FMu_nonneg π0_valid (-3 / 2) hμ
  have := le_max_left 0 (μ⁻¹ - 5)
  have := le_max_right 0 (μ - 1)
  linarith

lemma gCE_tendsto_zero : Tendsto gCE (𝓝[>] 0) atTop :=
  tendsto_atTop_mono' _ (eventually_nhdsWithin_of_forall fun _ hμ => gCE_ge_inv hμ)
    (tendsto_atTop_add_const_right _ (-5) tendsto_inv_nhdsGT_zero)

lemma gCE_tendsto_top : Tendsto gCE atTop atTop :=
  tendsto_atTop_mono' _ ((eventually_gt_atTop 0).mono fun _ hμ => gCE_ge_id hμ)
    (tendsto_atTop_add_const_right _ (-1) tendsto_id)

lemma one_mem_muStar_a : (1 : ℝ) ∈ π0.muStar gCE (-3 / 2) := by
  refine ⟨one_pos, fun μ' _ => ?_⟩
  unfold gCE
  have := le_max_left 0 (μ'⁻¹ - 5)
  have := le_max_left 0 (μ' - 1)
  norm_num
  linarith

/-- At `α_a = -1`, involvement `1/5` strictly beats every `μ ≥ 1`. -/
lemma obj_b_lt {μ : ℝ} (hμ : 1 ≤ μ) :
    π0.FMu (-1) μ - gCE μ < π0.FMu (-1) (1 / 5) - gCE (1 / 5) := by
  have hU := Prim.UMu_pos π0_valid (by norm_num : (0 : ℝ) < 1 / 5)
  have hlhs : π0.FMu (-1) μ - gCE μ = -(max 0 (μ⁻¹ - 5) + max 0 (μ - 1)) := by
    unfold gCE Prim.FMu
    rw [eMu_zero (by norm_num) hμ, eMu_zero (by norm_num) hμ]
    ring
  have hrhs : π0.FMu (-1) (1 / 5) - gCE (1 / 5) = 1 / 40 * π0.UMu (1 / 5) := by
    unfold gCE Prim.FMu
    rw [eMu_fifth_a, eMu_fifth_b]
    norm_num
    ring
  rw [hlhs, hrhs]
  have := le_max_left 0 (μ⁻¹ - 5)
  have := le_max_left 0 (μ - 1)
  nlinarith

/-- **Proposition 5 fails.** -/
theorem prop5_counterexample :
    ∃ (E E' : Env) (g : ℝ → ℝ), E'.prim = E.prim ∧ E.alphaA < E'.alphaA ∧
      E.ca = Cost.quad 2 (by norm_num) ∧ E.cp = Cost.quad 1 (by norm_num) ∧
      ContinuousOn g (Ioi 0) ∧ Tendsto g (𝓝[>] 0) atTop ∧ Tendsto g atTop atTop ∧
      ¬ SSOle (E.muStar g) (E'.muStar g) := by
  refine ⟨E1, E2, gCE, E2_prim, by rw [E1_alphaA, E2_alphaA]; norm_num, rfl, rfl,
    gCE_continuousOn, gCE_tendsto_zero, gCE_tendsto_top, ?_⟩
  rw [E1.muStar_eq, E2.muStar_eq, E2_prim, E1_alphaA, E2_alphaA]
  intro hsso
  obtain ⟨y, hy⟩ := Prim.muStar_nonempty π0_valid (-1) gCE_continuousOn gCE_tendsto_zero
    gCE_tendsto_top
  have hy1 : y < 1 := by
    by_contra h
    push Not at h
    have := hy.2 (1 / 5) (by norm_num)
    have := obj_b_lt h
    linarith
  have h1 := (hsso 1 one_mem_muStar_a y hy).2
  rw [max_eq_left hy1.le] at h1
  have := h1.2 (1 / 5) (by norm_num)
  have := obj_b_lt (le_refl (1 : ℝ))
  linarith

end Prop3

/-! ### Propositions 4 and B.1 at `α_p = 1` -/

section Boundary

/-- `E3` with the quadratic principal cost. -/
noncomputable abbrev E3q : Env := E3 cq1 (by simp [Cost.quad]; norm_num)

lemma E3q_payoffs_equal {ac pc ad pd : ℝ} (hc : E3q.IsEq .cen ac pc) (hd : E3q.IsEq .del ad pd) :
    ad * E3q.Up .del pd = ac * E3q.Up .cen pc := by
  rw [E3q.payoff_cen hc, E3q.payoff_del hd, E3_alphaA, E3_alphaP]
  exact (Prim.PiC_one_eq_PiD_one E3q.prim_valid).symm

lemma E3q_surplus_equal {ac pc ad pd : ℝ} (hc : E3q.IsEq .cen ac pc)
    (hd : E3q.IsEq .del ad pd) :
    E3q.Ua .del pd ad + ad * E3q.Up .del pd = E3q.Ua .cen pc ac + ac * E3q.Up .cen pc := by
  rw [E3q.surplus_cen hc, E3q.surplus_del hd, E3_alphaA, E3_alphaP]
  exact (Prim.WC_one_eq_WD_one E3q.prim_valid).symm

/-- **The strict inequality `α̂ < α̃` of Proposition 4 fails at `α_p = 1`.** In `E3`
(`v_a = v_p`, so `α_a = α_p = 1`) the principal is indifferent; any threshold that
satisfies the "iff" therefore has `α̂(1) ≥ 1 = α̃(1)`. -/
theorem prop4_boundary :
    ∃ E : Env, E.alphaA = 1 ∧ E.alphaP = 1 ∧
      ∀ αhat : ℝ → ℝ, (∀ ac pc ad pd : ℝ, E.IsEq .cen ac pc → E.IsEq .del ad pd →
        (ad * E.Up .del pd < ac * E.Up .cen pc ↔ αhat E.alphaP < E.alphaA)) →
        alphaTilde E.cp E.Np E.alphaP ≤ αhat E.alphaP := by
  refine ⟨E3q, E3_alphaA _ _, E3_alphaP _ _, fun αhat hiff => ?_⟩
  have h := hiff _ _ _ _ (E3q.isEq_eq .cen) (E3q.isEq_eq .del)
  rw [E3q_payoffs_equal (E3q.isEq_eq .cen) (E3q.isEq_eq .del)] at h
  rw [E3_alphaP, alphaTilde_one _ E3q.Np_neg]
  rw [E3_alphaA, E3_alphaP] at h
  by_contra hlt
  push Not at hlt
  exact lt_irrefl _ (h.2 hlt)

/-- **The strict inequality `α̂^c < α̃` of Proposition B.1 fails at `α_p = 1`.** -/
theorem propB1_boundary :
    ∃ E : Env, E.alphaA = 1 ∧ E.alphaP = 1 ∧
      ∀ αhat : ℝ → ℝ, (∀ ac pc ad pd : ℝ, E.IsEq .cen ac pc → E.IsEq .del ad pd →
        (E.Ua .del pd ad + ad * E.Up .del pd < E.Ua .cen pc ac + ac * E.Up .cen pc ↔
          αhat E.alphaP < E.alphaA)) →
        alphaTilde E.cp E.Np E.alphaP ≤ αhat E.alphaP := by
  refine ⟨E3q, E3_alphaA _ _, E3_alphaP _ _, fun αhat hiff => ?_⟩
  have h := hiff _ _ _ _ (E3q.isEq_eq .cen) (E3q.isEq_eq .del)
  rw [E3q_surplus_equal (E3q.isEq_eq .cen) (E3q.isEq_eq .del)] at h
  rw [E3_alphaP, alphaTilde_one _ E3q.Np_neg]
  rw [E3_alphaA, E3_alphaP] at h
  by_contra hlt
  push Not at hlt
  exact lt_irrefl _ (h.2 hlt)

end Boundary

/-! ### Proposition 3(b) at `α_a = α_p = 1` -/

/-- When `α_a = α_p = 1` the agent's efforts coincide in the two regimes. -/
theorem Env.ea_eq_of_alpha_one (E : Env) (ha : E.alphaA = 1) (hp : E.alphaP = 1) :
    E.ea .cen = E.ea .del := by
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have h := (E.prop3_strict (E.isEq_eq .cen) (E.isEq_eq .del)).1 hlt
    rw [hp, ha, alphaTilde_one _ E.Np_neg] at h
    exact lt_irrefl _ h
  · rw [E.prop3 (E.isEq_eq .cen) (E.isEq_eq .del), hp, ha, alphaTilde_one _ E.Np_neg]

/-- `E3` with the cubic principal cost (`h = √·`, strictly concave). -/
noncomputable abbrev E3c : Env := E3 cube (by rw [cube_d_one]; norm_num)

/-- **Proposition 3(b), concave case, at `α_a = α_p = 1`:** all hypotheses hold and the
agent's efforts are equal, so effort is not strictly lower under centralization. -/
theorem prop3b_concave_equal :
    ∃ E : Env, StrictConcaveOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br ∧ E.alphaA = E.alphaP ∧
      0 < E.alphaP ∧ E.ea .cen = E.ea .del :=
  ⟨E3c, cube_strictConcave, by rw [E3_alphaA, E3_alphaP], by rw [E3_alphaP]; norm_num,
    E3c.ea_eq_of_alpha_one (E3_alphaA _ _) (E3_alphaP _ _)⟩

end MI
