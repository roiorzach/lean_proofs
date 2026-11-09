import ManagerialIntervention.Cost
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The model (Section 2) and the alignment parameters (Definition 1)

An idea has values `(v_a, v_p)` drawn from a joint distribution `F` on `ℝ × ℝ` with finite
means.  The agent finds an idea with probability `e_a`; the principal then reveals
`(v_a, v_p)` with probability `e_p`; the owner of the decision right implements.

We keep the paper's assumptions:
* `E(v_a), E(v_p) > 0`;
* `P(v_a < 0) · P(v_p < 0) > 0`;
* costs as in `MI.Cost`, with `c_a(1)` and `c_p(1)` large enough that optimal efforts are
  interior.  We state "large enough" as `c_a'(1) ≥ E(v_a 1_{v_a ≥ 0})` and
  `c_p'(1) ≥ -E(v_p 1_{v_p < 0})`, which bound every marginal benefit in the model.
-/

namespace MI

open MeasureTheory Set

/-- A model environment: the joint distribution of `(v_a, v_p)` and the two effort costs. -/
structure Env where
  /-- the joint distribution `F` of `(v_a, v_p)` -/
  F : Measure (ℝ × ℝ)
  [isProb : IsProbabilityMeasure F]
  int_a : Integrable (fun v : ℝ × ℝ => v.1) F
  int_p : Integrable (fun v : ℝ × ℝ => v.2) F
  /-- `E(v_a) > 0` -/
  Ea_pos : 0 < ∫ v, v.1 ∂F
  /-- `E(v_p) > 0` -/
  Ep_pos : 0 < ∫ v, v.2 ∂F
  /-- `P(v_a < 0) · P(v_p < 0) > 0` -/
  rej : 0 < F {v | v.1 < 0} * F {v | v.2 < 0}
  /-- the agent's cost `c_a` -/
  ca : Cost
  /-- the principal's cost `c_p` -/
  cp : Cost
  /-- `c_a(1)` is large enough: `c_a'(1) ≥ E(v_a 1_{v_a ≥ 0})` -/
  ca_large : ∫ v, {v : ℝ × ℝ | 0 ≤ v.1}.indicator (fun v => v.1) v ∂F ≤ ca.d 1
  /-- `c_p(1)` is large enough: `c_p'(1) ≥ -E(v_p 1_{v_p < 0})` -/
  cp_large : -∫ v, {v : ℝ × ℝ | v.2 < 0}.indicator (fun v => v.2) v ∂F ≤ cp.d 1

attribute [instance] Env.isProb

/-- Who holds the decision right. -/
inductive Regime
  | cen
  | del
  deriving DecidableEq

/-- The decision maker's own value: `v_p` under centralization, `v_a` under delegation. -/
def Regime.dm : Regime → ℝ × ℝ → ℝ
  | .cen, v => v.2
  | .del, v => v.1

/-- An informed decision maker implements iff her own value is `≥ 0` (the paper's
indicator `1_{v ≥ 0}`); this maximises her payoff for every realisation. -/
theorem informed_rule_optimal (r : Regime) (v : ℝ × ℝ) (implement : Prop) [Decidable implement] :
    (if implement then r.dm v else 0) ≤ (if 0 ≤ r.dm v then r.dm v else 0) := by
  split_ifs <;> linarith

namespace Env

variable (E : Env)

/-! ### Moments and alignment -/

/-- `E(v_a)` -/
noncomputable def A : ℝ := ∫ v, v.1 ∂E.F
/-- `E(v_p)` -/
noncomputable def P : ℝ := ∫ v, v.2 ∂E.F
/-- `E(v_a 1_{v_a<0})` -/
noncomputable def Na : ℝ := ∫ v, {v : ℝ × ℝ | v.1 < 0}.indicator (fun v => v.1) v ∂E.F
/-- `E(v_p 1_{v_p<0})` -/
noncomputable def Np : ℝ := ∫ v, {v : ℝ × ℝ | v.2 < 0}.indicator (fun v => v.2) v ∂E.F
/-- `E(v_a 1_{v_p<0})` -/
noncomputable def Xa : ℝ := ∫ v, {v : ℝ × ℝ | v.2 < 0}.indicator (fun v => v.1) v ∂E.F
/-- `E(v_p 1_{v_a<0})` -/
noncomputable def Xp : ℝ := ∫ v, {v : ℝ × ℝ | v.1 < 0}.indicator (fun v => v.2) v ∂E.F

/-- **Definition 1.** `α_a = E(v_a 1_{v_p<0}) / E(v_a 1_{v_a<0})`. -/
noncomputable def alphaA : ℝ := E.Xa / E.Na
/-- **Definition 1.** `α_p = E(v_p 1_{v_a<0}) / E(v_p 1_{v_p<0})`. -/
noncomputable def alphaP : ℝ := E.Xp / E.Np

lemma mA : MeasurableSet {v : ℝ × ℝ | v.1 < 0} := measurableSet_lt measurable_fst measurable_const
lemma mP : MeasurableSet {v : ℝ × ℝ | v.2 < 0} := measurableSet_lt measurable_snd measurable_const

lemma integral_split {f : ℝ × ℝ → ℝ} (hf : Integrable f E.F) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) :
    ∫ v, f v ∂E.F = ∫ v, s.indicator f v ∂E.F + ∫ v, sᶜ.indicator f v ∂E.F := by
  rw [← integral_add (hf.indicator hs) (hf.indicator hs.compl)]
  congr 1
  funext v
  exact (congrFun (Set.indicator_self_add_compl s f) v).symm

lemma rejA : E.F {v | v.1 < 0} ≠ 0 := by
  intro h; have := E.rej; rw [h, zero_mul] at this; exact lt_irrefl _ this

lemma rejP : E.F {v | v.2 < 0} ≠ 0 := by
  intro h; have := E.rej; rw [h, mul_zero] at this; exact lt_irrefl _ this

lemma neg_part_neg {f : ℝ × ℝ → ℝ} (hf : Integrable f E.F) (hm : Measurable f)
    (hpos : E.F {v | f v < 0} ≠ 0) :
    ∫ v, {v | f v < 0}.indicator f v ∂E.F < 0 := by
  have hs : MeasurableSet {v | f v < 0} := measurableSet_lt hm measurable_const
  have hint : Integrable (fun v => -({v | f v < 0}.indicator f v)) E.F := (hf.indicator hs).neg
  have hnn : 0 ≤ᵐ[E.F] fun v => -({v | f v < 0}.indicator f v) := by
    refine Filter.Eventually.of_forall fun v => ?_
    by_cases h : f v < 0
    · simp only [Set.indicator, Set.mem_ofPred_eq, h, ite_true, Pi.zero_apply]; linarith
    · simp [Set.indicator, h]
  have hsupp : Function.support (fun v => -({v | f v < 0}.indicator f v)) = {v | f v < 0} := by
    ext v
    by_cases h : f v < 0
    · simp [Set.indicator, h, Function.mem_support, h.ne]
    · simp [Set.indicator, h, Function.mem_support]
  have := (integral_pos_iff_support_of_nonneg_ae hnn hint).2 (by rw [hsupp]; exact pos_iff_ne_zero.2 hpos)
  rw [integral_neg] at this
  linarith

/-- `E(v_a 1_{v_a<0}) < 0`. -/
lemma Na_neg : E.Na < 0 := E.neg_part_neg E.int_a measurable_fst E.rejA
/-- `E(v_p 1_{v_p<0}) < 0`. -/
lemma Np_neg : E.Np < 0 := E.neg_part_neg E.int_p measurable_snd E.rejP

lemma A_pos : 0 < E.A := E.Ea_pos
lemma P_pos : 0 < E.P := E.Ep_pos

lemma Na_le_Xa : E.Na ≤ E.Xa := by
  apply integral_mono (E.int_a.indicator mA) (E.int_a.indicator mP)
  intro v
  by_cases h1 : v.1 < 0 <;> by_cases h2 : v.2 < 0 <;> simp [Set.indicator, h1, h2] <;> linarith

lemma Np_le_Xp : E.Np ≤ E.Xp := by
  apply integral_mono (E.int_p.indicator mP) (E.int_p.indicator mA)
  intro v
  by_cases h1 : v.1 < 0 <;> by_cases h2 : v.2 < 0 <;> simp [Set.indicator, h1, h2] <;> linarith

/-- `α_a ≤ 1` (information is worth more to the agent when he decides). -/
theorem alphaA_le_one : E.alphaA ≤ 1 := (div_le_one_of_neg E.Na_neg).2 E.Na_le_Xa

/-- `α_p ≤ 1`. -/
theorem alphaP_le_one : E.alphaP ≤ 1 := (div_le_one_of_neg E.Np_neg).2 E.Np_le_Xp

/-- `α_a < 0` iff `E(v_a 1_{v_p<0}) > 0`. -/
theorem alphaA_neg_iff : E.alphaA < 0 ↔ 0 < E.Xa := by
  unfold alphaA
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : 0 ≤ E.Xa / E.Na := div_nonneg_of_nonpos h' E.Na_neg.le
    linarith
  · intro h; exact div_neg_of_pos_of_neg h E.Na_neg

lemma Xa_eq : E.Xa = E.alphaA * E.Na := by
  unfold alphaA; field_simp [E.Na_neg.ne]

lemma Xp_eq : E.Xp = E.alphaP * E.Np := by
  unfold alphaP; field_simp [E.Np_neg.ne]

lemma compl_A : {v : ℝ × ℝ | v.1 < 0}ᶜ = {v | 0 ≤ v.1} := by ext v; simp [not_lt]
lemma compl_P : {v : ℝ × ℝ | v.2 < 0}ᶜ = {v | 0 ≤ v.2} := by ext v; simp [not_lt]

/-- `E(v_a 1_{v_a ≥ 0}) = E(v_a) - E(v_a 1_{v_a<0})`. -/
lemma posA_eq : ∫ v, {v : ℝ × ℝ | 0 ≤ v.1}.indicator (fun v => v.1) v ∂E.F = E.A - E.Na := by
  have := E.integral_split E.int_a mA
  rw [compl_A] at this
  unfold A Na; linarith

lemma Xa_le : E.Xa ≤ E.A - E.Na := by
  rw [← E.posA_eq]
  apply integral_mono (E.int_a.indicator mP) (E.int_a.indicator (compl_A ▸ mA.compl))
  intro v
  by_cases h1 : 0 ≤ v.1 <;> by_cases h2 : v.2 < 0 <;>
    simp only [Set.indicator, Set.mem_ofPred_eq, h1, h2, ite_true, ite_false] <;> linarith

/-- The agent's marginal-cost bound in the form used below. -/
lemma ca_bound : E.A - E.Na ≤ E.ca.d 1 := E.posA_eq ▸ E.ca_large

lemma cp_bound : -E.Np ≤ E.cp.d 1 := E.cp_large

/-! ### Decisions and payoffs -/

/-- `E(f · 1{the informed decision maker implements})`. -/
noncomputable def EI (r : Regime) (f : ℝ × ℝ → ℝ) : ℝ :=
  ∫ v, {v : ℝ × ℝ | 0 ≤ r.dm v}.indicator f v ∂E.F

/-- An uninformed decision maker implements, since her expected value is positive. -/
theorem uninformed_implements (r : Regime) : 0 < ∫ v, r.dm v ∂E.F := by
  cases r
  · exact E.Ep_pos
  · exact E.Ea_pos

lemma EI_cen_p : E.EI .cen (fun v => v.2) = E.P - E.Np := by
  have := E.integral_split E.int_p mP
  rw [compl_P] at this
  unfold EI P Np; simp only [Regime.dm]; linarith

lemma EI_del_p : E.EI .del (fun v => v.2) = E.P - E.Xp := by
  have := E.integral_split E.int_p mA
  rw [compl_A] at this
  unfold EI P Xp; simp only [Regime.dm]; linarith

lemma EI_cen_a : E.EI .cen (fun v => v.1) = E.A - E.Xa := by
  have := E.integral_split E.int_a mP
  rw [compl_P] at this
  unfold EI A Xa; simp only [Regime.dm]; linarith

lemma EI_del_a : E.EI .del (fun v => v.1) = E.A - E.Na := by
  have := E.integral_split E.int_a mA
  rw [compl_A] at this
  unfold EI A Na; simp only [Regime.dm]; linarith

/-- The principal's interim payoff given an idea, equations (2)–(3):
`(1 - e) E(v_p) + e E(v_p 1_{v_dm ≥ 0}) - c_p(e)`. -/
noncomputable def Up (r : Regime) (e : ℝ) : ℝ :=
  (1 - e) * E.P + e * E.EI r (fun v => v.2) - E.cp.c e

/-- The agent's interim value of an idea given principal effort `e_p`:
`(1 - e_p) E(v_a) + e_p E(v_a 1_{v_dm ≥ 0})`. -/
noncomputable def Va (r : Regime) (ep : ℝ) : ℝ :=
  (1 - ep) * E.A + ep * E.EI r (fun v => v.1)

/-- The agent's payoff from effort `e_a`, equations (4)–(5). -/
noncomputable def Ua (r : Regime) (ep ea : ℝ) : ℝ := ea * E.Va r ep - E.ca.c ea

/-- Subgame-perfect effort choices: `e_p` is a best response for the principal given an
idea, and `e_a` is a best response for the agent who forecasts `e_p`. -/
def IsEq (r : Regime) (ea ep : ℝ) : Prop := IsBR (E.Up r) ep ∧ IsBR (E.Ua r ep) ea

/-- The principal's marginal benefit of effort. -/
noncomputable def mp : Regime → ℝ
  | .cen => -E.Np
  | .del => -E.Xp

lemma Up_eq (r : Regime) (e : ℝ) : E.Up r e = E.P + 1 * (e * E.mp r - E.cp.c e) := by
  cases r
  · simp only [Up, EI_cen_p, mp]; ring
  · simp only [Up, EI_del_p, mp]; ring

lemma Va_cen (ep : ℝ) : E.Va .cen ep = E.A - ep * E.Xa := by
  simp only [Va, EI_cen_a]; ring

lemma Va_del (ep : ℝ) : E.Va .del ep = E.A - ep * E.Na := by
  simp only [Va, EI_del_a]; ring

lemma isBR_Up_iff (r : Regime) {e : ℝ} : IsBR (E.Up r) e ↔ e = E.cp.br (E.mp r) := by
  have : E.Up r = fun e => E.P + 1 * (e * E.mp r - E.cp.c e) := funext (E.Up_eq r)
  rw [this]
  exact E.cp.isBR_affine_iff one_pos

lemma isBR_Ua_iff (r : Regime) {ep ea : ℝ} : IsBR (E.Ua r ep) ea ↔ ea = E.ca.br (E.Va r ep) :=
  E.ca.isBR_iff

/-- Equilibrium principal effort. -/
noncomputable def ep (r : Regime) : ℝ := E.cp.br (E.mp r)
/-- Equilibrium agent effort. -/
noncomputable def ea (r : Regime) : ℝ := E.ca.br (E.Va r (E.ep r))

/-- The equilibrium exists and is unique. -/
theorem isEq_iff (r : Regime) {a p : ℝ} : E.IsEq r a p ↔ p = E.ep r ∧ a = E.ea r := by
  unfold IsEq
  rw [E.isBR_Up_iff, E.isBR_Ua_iff]
  constructor
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

theorem isEq_eq (r : Regime) : E.IsEq r (E.ea r) (E.ep r) := (E.isEq_iff r).2 ⟨rfl, rfl⟩

/-! ### The first-order conditions displayed in Section 3.1 -/

lemma mp_del_eq : E.cp.br (E.mp .del) = E.cp.br (-(max E.alphaP 0) * E.Np) := by
  simp only [mp]
  rw [E.Xp_eq]
  rcases le_or_gt 0 E.alphaP with h | h
  · rw [max_eq_left h]; ring_nf
  · rw [max_eq_right h.le, E.cp.br_eq_zero_of_nonpos, E.cp.br_eq_zero_of_nonpos]
    · simp
    · nlinarith [E.Np_neg]

/-- (P Effort: Centralization) `c_p'(e_p^c) = -E(v_p 1_{v_p<0})`. -/
theorem foc_principal_cen : E.cp.d (E.ep .cen) = -E.Np := by
  show E.cp.d (E.cp.br (-E.Np)) = -E.Np
  exact E.cp.d_br ⟨by linarith [E.Np_neg], E.cp_bound⟩

lemma max_alphaP_mem : max E.alphaP 0 ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_right _ _, max_le E.alphaP_le_one zero_le_one⟩

/-- (P Effort: Delegation) `c_p'(e_p^d) = -max{0, α_p} E(v_p 1_{v_p<0})`. -/
theorem foc_principal_del : E.cp.d (E.ep .del) = -(max E.alphaP 0) * E.Np := by
  unfold ep
  rw [E.mp_del_eq]
  apply E.cp.d_br
  have h := E.max_alphaP_mem
  have hN := E.Np_neg
  refine ⟨by nlinarith [h.1], ?_⟩
  have := E.cp_bound
  nlinarith [h.2]

lemma ep_mem (r : Regime) : E.ep r ∈ Icc (0 : ℝ) 1 := E.cp.br_mem _

/-- (A Effort: Delegation) `c_a'(e_a^d) = E(v_a) - e_p^d E(v_a 1_{v_a<0})`. -/
theorem foc_agent_del : E.ca.d (E.ea .del) = E.A - E.ep .del * E.Na := by
  unfold ea
  rw [E.Va_del]
  apply E.ca.d_br
  have h := E.ep_mem .del
  have hN := E.Na_neg
  have hA := E.A_pos
  refine ⟨by nlinarith [h.1], ?_⟩
  have := E.ca_bound
  nlinarith [h.2]

/-- (A Effort: Centralization)
`c_a'(e_a^c) = max{0, E(v_a) - α_a e_p^c E(v_a 1_{v_a<0})}`. -/
theorem foc_agent_cen :
    E.ca.d (E.ea .cen) = max 0 (E.A - E.alphaA * E.ep .cen * E.Na) := by
  unfold ea
  rw [E.Va_cen, E.Xa_eq]
  have h := E.ep_mem .cen
  rcases le_or_gt (E.A - E.alphaA * E.ep .cen * E.Na) 0 with hm | hm
  · rw [max_eq_left hm, E.ca.br_eq_zero_of_nonpos (by linarith), E.ca.d_zero]
  · rw [max_eq_right hm.le]
    have : E.A - E.ep .cen * (E.alphaA * E.Na) = E.A - E.alphaA * E.ep .cen * E.Na := by ring
    rw [this]
    apply E.ca.d_br
    refine ⟨hm.le, ?_⟩
    have h1 := E.ca_bound
    have h2 := E.Xa_le
    have h3 := E.Na_le_Xa
    rw [E.Xa_eq] at h2 h3
    have hN := E.Na_neg
    have hA := E.A_pos
    -- `A - α e N ≤ A - N`: split on the sign of `α N`
    rcases le_or_gt 0 (E.alphaA * E.Na) with h4 | h4
    · nlinarith [h.1, h.2]
    · nlinarith [h.1, h.2]

end Env

end MI
