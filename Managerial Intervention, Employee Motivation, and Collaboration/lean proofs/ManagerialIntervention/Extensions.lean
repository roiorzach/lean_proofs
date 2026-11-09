import ManagerialIntervention.NonVacuity

/-!
# Appendix B.1: negative-valued projects

Now `E(v_a), E(v_p) < 0`, so an uninformed decision maker rejects.  We add the analogue of
`P(v_a<0)·P(v_p<0) > 0`, namely `P(v_a>0)·P(v_p>0) > 0`, which makes the denominators of
`α_a^n, α_p^n` positive (the paper leaves this implicit).

* `MI.EnvN.lemma1` — Lemma 1 continues to hold.
* `MI.EnvN.lemma2_del`, `MI.EnvN.lemma2_cen` — the analogue of Lemma 2.  Under centralization
  the agent's effort is weakly increasing in the principal's effort for *every* value of
  `α_a^n`, so the "only if" half of Lemma 2(b) has no analogue here.
* `MI.EnvN.effort_iff`, `MI.EnvN.effort_iff_h` — the display before (B.8) and the left side of (B.8): effort is
  higher under centralization iff `max{0, α_a^n} ≥ e_p^{d,n}/e_p^{c,n} = α̃^n`.
* `MI.EnvN.effort_iff_corrected` — the correct form of the equivalence in (B.8):
  iff `α_p^n ≤ 0` or `α_a^n ≥ α̃^n`.
* `MI.EnvN.simplification_fails` — the equivalence in (B.8) (dropping the `max`) is false
  when `α_p^n ≤ 0` and `α_a^n < 0`.
-/

namespace MI

open MeasureTheory Set

/-- The environment of Appendix B.1. -/
structure EnvN where
  F : Measure (ℝ × ℝ)
  [isProb : IsProbabilityMeasure F]
  int_a : Integrable (fun v : ℝ × ℝ => v.1) F
  int_p : Integrable (fun v : ℝ × ℝ => v.2) F
  /-- `E(v_a) < 0` -/
  Ea_neg : ∫ v, v.1 ∂F < 0
  /-- `E(v_p) < 0` -/
  Ep_neg : ∫ v, v.2 ∂F < 0
  /-- `P(v_a > 0) · P(v_p > 0) > 0` -/
  acc : 0 < F {v | 0 < v.1} * F {v | 0 < v.2}
  ca : Cost
  cp : Cost
  ca_large : ∫ v, {v : ℝ × ℝ | 0 ≤ v.1}.indicator (fun v => v.1) v ∂F ≤ ca.d 1
  cp_large : ∫ v, {v : ℝ × ℝ | 0 ≤ v.2}.indicator (fun v => v.2) v ∂F ≤ cp.d 1

attribute [instance] EnvN.isProb

namespace EnvN

variable (E : EnvN)

/-- `E(f · 1{the informed decision maker implements})`. -/
noncomputable def EI (r : Regime) (f : ℝ × ℝ → ℝ) : ℝ :=
  ∫ v, {v : ℝ × ℝ | 0 ≤ r.dm v}.indicator f v ∂E.F

/-- An uninformed decision maker rejects. -/
theorem uninformed_rejects (r : Regime) : ∫ v, r.dm v ∂E.F < 0 := by
  cases r
  · exact E.Ep_neg
  · exact E.Ea_neg

/-- `E(v_a 1_{v_a ≥ 0})` -/
noncomputable def Pa : ℝ := E.EI .del (fun v => v.1)
/-- `E(v_p 1_{v_p ≥ 0})` -/
noncomputable def Pp : ℝ := E.EI .cen (fun v => v.2)
/-- `E(v_a 1_{v_p ≥ 0})` -/
noncomputable def Ya : ℝ := E.EI .cen (fun v => v.1)
/-- `E(v_p 1_{v_a ≥ 0})` -/
noncomputable def Yp : ℝ := E.EI .del (fun v => v.2)

/-- `α_a^n = E(v_a 1_{v_p≥0}) / E(v_a 1_{v_a≥0})` -/
noncomputable def alphaA : ℝ := E.Ya / E.Pa
/-- `α_p^n = E(v_p 1_{v_a≥0}) / E(v_p 1_{v_p≥0})` -/
noncomputable def alphaP : ℝ := E.Yp / E.Pp

lemma pos_part_pos {f : ℝ × ℝ → ℝ} (hf : Integrable f E.F) (hm : Measurable f)
    (hpos : E.F {v | 0 < f v} ≠ 0) : 0 < ∫ v, {v | 0 ≤ f v}.indicator f v ∂E.F := by
  have hnn : 0 ≤ᵐ[E.F] fun v => {v | 0 ≤ f v}.indicator f v := by
    refine Filter.Eventually.of_forall fun v => ?_
    by_cases h : 0 ≤ f v
    · simp only [Set.indicator, Set.mem_ofPred_eq, h, ite_true, Pi.zero_apply]
    · simp [Set.indicator, h]
  have hsupp : Function.support (fun v => {v | 0 ≤ f v}.indicator f v) = {v | 0 < f v} := by
    ext v
    by_cases h : 0 < f v
    · simp [Set.indicator, h.le, Function.mem_support, h.ne', h]
    · by_cases h' : 0 ≤ f v
      · have : f v = 0 := le_antisymm (not_lt.1 h) h'
        simp [Set.indicator, Function.mem_support, this]
      · simp [Set.indicator, Function.mem_support, h, h']
  have hint : Integrable (fun v => {v | 0 ≤ f v}.indicator f v) E.F :=
    hf.indicator (measurableSet_le measurable_const hm)
  exact (integral_pos_iff_support_of_nonneg_ae hnn hint).2
    (by rw [hsupp]; exact pos_iff_ne_zero.2 hpos)

lemma accA : E.F {v | 0 < v.1} ≠ 0 := by
  intro h; have := E.acc; rw [h, zero_mul] at this; exact lt_irrefl _ this

lemma accP : E.F {v | 0 < v.2} ≠ 0 := by
  intro h; have := E.acc; rw [h, mul_zero] at this; exact lt_irrefl _ this

lemma Pa_pos : 0 < E.Pa := E.pos_part_pos E.int_a measurable_fst E.accA
lemma Pp_pos : 0 < E.Pp := E.pos_part_pos E.int_p measurable_snd E.accP

lemma mA' : MeasurableSet {v : ℝ × ℝ | 0 ≤ v.1} :=
  measurableSet_le measurable_const measurable_fst
lemma mP' : MeasurableSet {v : ℝ × ℝ | 0 ≤ v.2} :=
  measurableSet_le measurable_const measurable_snd

lemma Ya_le_Pa : E.Ya ≤ E.Pa := by
  apply integral_mono (E.int_a.indicator mP') (E.int_a.indicator mA')
  intro v
  by_cases h1 : 0 ≤ v.1 <;> by_cases h2 : 0 ≤ v.2 <;>
    simp only [Set.indicator, Set.mem_ofPred_eq, h1, h2, ite_true, ite_false] <;> linarith

lemma Yp_le_Pp : E.Yp ≤ E.Pp := by
  apply integral_mono (E.int_p.indicator mA') (E.int_p.indicator mP')
  intro v
  by_cases h1 : 0 ≤ v.1 <;> by_cases h2 : 0 ≤ v.2 <;>
    simp only [Set.indicator, Set.mem_ofPred_eq, h1, h2, ite_true, ite_false] <;> linarith

lemma alphaP_le_one : E.alphaP ≤ 1 := (div_le_one E.Pp_pos).2 E.Yp_le_Pp

lemma Ya_eq : E.Ya = E.alphaA * E.Pa := by unfold alphaA; field_simp [E.Pa_pos.ne']
lemma Yp_eq : E.Yp = E.alphaP * E.Pp := by unfold alphaP; field_simp [E.Pp_pos.ne']

lemma Pa_le : E.Pa ≤ E.ca.d 1 := E.ca_large
lemma Pp_le : E.Pp ≤ E.cp.d 1 := E.cp_large

/-! ### Payoffs and equilibrium -/

/-- The principal's interim payoff: with no information the idea is rejected (payoff `0`). -/
noncomputable def Up (r : Regime) (e : ℝ) : ℝ := e * E.EI r (fun v => v.2) - E.cp.c e

/-- The agent's interim value of an idea. -/
noncomputable def Va (r : Regime) (ep : ℝ) : ℝ := ep * E.EI r (fun v => v.1)

/-- The agent's payoff from effort. -/
noncomputable def Ua (r : Regime) (ep ea : ℝ) : ℝ := ea * E.Va r ep - E.ca.c ea

/-- Subgame-perfect effort choices. -/
def IsEq (r : Regime) (ea ep : ℝ) : Prop := IsBR (E.Up r) ep ∧ IsBR (E.Ua r ep) ea

lemma isBR_Up_iff (r : Regime) {e : ℝ} : IsBR (E.Up r) e ↔ e = E.cp.br (E.EI r (fun v => v.2)) :=
  E.cp.isBR_iff

lemma isBR_Ua_iff (r : Regime) {ep ea : ℝ} : IsBR (E.Ua r ep) ea ↔ ea = E.ca.br (E.Va r ep) :=
  E.ca.isBR_iff

/-- Equilibrium principal effort. -/
noncomputable def ep (r : Regime) : ℝ := E.cp.br (E.EI r (fun v => v.2))
/-- Equilibrium agent effort. -/
noncomputable def ea (r : Regime) : ℝ := E.ca.br (E.Va r (E.ep r))

theorem isEq_iff (r : Regime) {a p : ℝ} : E.IsEq r a p ↔ p = E.ep r ∧ a = E.ea r := by
  unfold IsEq
  rw [E.isBR_Up_iff, E.isBR_Ua_iff]
  constructor
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

theorem isEq_eq (r : Regime) : E.IsEq r (E.ea r) (E.ep r) := (E.isEq_iff r).2 ⟨rfl, rfl⟩

/-- **Lemma 1 (negative projects).** -/
theorem lemma1 {pc pd : ℝ} (hc : IsBR (E.Up .cen) pc) (hd : IsBR (E.Up .del) pd) : pd ≤ pc := by
  rw [E.isBR_Up_iff] at hc hd
  subst hc hd
  exact E.cp.br_mono E.Yp_le_Pp

/-- **Lemma 2(a) (negative projects).** -/
theorem lemma2_del {p p' a a' : ℝ} (hpp : p ≤ p') (ha : IsBR (E.Ua .del p) a)
    (ha' : IsBR (E.Ua .del p') a') : a ≤ a' := by
  rw [E.isBR_Ua_iff] at ha ha'
  subst ha ha'
  exact E.ca.br_mono (mul_le_mul_of_nonneg_right hpp E.Pa_pos.le)

/-- **Lemma 2(b) (negative projects).** Under centralization the agent's effort is weakly
increasing in the principal's effort, whatever the sign of `α_a^n`. -/
theorem lemma2_cen {p p' a a' : ℝ} (hp : 0 ≤ p) (hpp : p ≤ p') (ha : IsBR (E.Ua .cen p) a)
    (ha' : IsBR (E.Ua .cen p') a') : a ≤ a' := by
  rw [E.isBR_Ua_iff] at ha ha'
  subst ha ha'
  unfold Va
  rcases le_or_gt 0 (E.EI .cen fun v => v.1) with h | h
  · exact E.ca.br_mono (mul_le_mul_of_nonneg_right hpp h)
  · rw [E.ca.br_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hp h.le),
      E.ca.br_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (hp.trans hpp) h.le)]

/-! ### The comparison of agent efforts -/

/-- `α̃^n = h(max{0, α_p^n} E(v_p 1_{v_p≥0})) / h(E(v_p 1_{v_p≥0}))`. -/
noncomputable def alphaTildeN : ℝ := E.cp.br (max E.alphaP 0 * E.Pp) / E.cp.br E.Pp

lemma ep_cen_pos : 0 < E.ep .cen := E.cp.br_pos E.Pp_pos

lemma ep_del_eq : E.ep .del = E.cp.br (max E.alphaP 0 * E.Pp) := by
  show E.cp.br E.Yp = _
  rw [E.Yp_eq]
  rcases le_or_gt 0 E.alphaP with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h.le, zero_mul, E.cp.br_eq_zero_of_nonpos le_rfl,
      E.cp.br_eq_zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg h.le E.Pp_pos.le)]

lemma alphaTildeN_eq : E.alphaTildeN = E.ep .del / E.ep .cen := by
  rw [E.ep_del_eq]; rfl

lemma ea_cen_eq : E.ea .cen = E.ca.br (E.ep .cen * (max 0 E.alphaA * E.Pa)) := by
  show E.ca.br (E.ep .cen * E.Ya) = _
  rw [E.Ya_eq]
  have hp : 0 ≤ E.ep .cen := E.ep_cen_pos.le
  rcases le_or_gt 0 E.alphaA with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h.le, zero_mul, mul_zero, E.ca.br_eq_zero_of_nonpos le_rfl,
      E.ca.br_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hp
        (mul_nonpos_of_nonpos_of_nonneg h.le E.Pa_pos.le))]

lemma ea_del_eq : E.ea .del = E.ca.br (E.ep .del * E.Pa) := rfl

/-- **Appendix B.1, display before (B.8).** The agent's effort is higher under centralization iff
`max{0, α_a^n} ≥ e_p^{d,n} / e_p^{c,n}`. -/
theorem effort_iff {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) :
    ad ≤ ac ↔ pd / pc ≤ max 0 E.alphaA := by
  rw [E.isEq_iff] at hc hd
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨rfl, rfl⟩ := hd
  rw [E.ea_cen_eq, E.ea_del_eq]
  have hPa := E.Pa_pos
  have hM := E.Pa_le
  have hpd : E.ep .del ∈ Icc (0 : ℝ) 1 := E.cp.br_mem _
  have hpc : E.ep .cen ∈ Icc (0 : ℝ) 1 := E.cp.br_mem _
  have hmax : max 0 E.alphaA * E.Pa ≤ E.Pa := by
    rw [max_mul_of_nonneg _ _ hPa.le, zero_mul, ← E.Ya_eq]
    exact max_le hPa.le E.Ya_le_Pa
  have hmax0 : 0 ≤ max 0 E.alphaA * E.Pa := mul_nonneg (le_max_left _ _) hPa.le
  have hx : E.ep .del * E.Pa ∈ Icc 0 (E.ca.d 1) :=
    ⟨mul_nonneg hpd.1 hPa.le, by nlinarith [hpd.2]⟩
  have hy : E.ep .cen * (max 0 E.alphaA * E.Pa) ∈ Icc 0 (E.ca.d 1) :=
    ⟨mul_nonneg hpc.1 hmax0, by nlinarith [hpc.2]⟩
  rw [E.ca.br_strictMonoOn.le_iff_le hx hy, div_le_iff₀ E.ep_cen_pos]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Appendix B.1, left side of (B.8).** Higher under centralization iff
`max{0, α_a^n} ≥ α̃^n`. -/
theorem effort_iff_h {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) :
    ad ≤ ac ↔ E.alphaTildeN ≤ max 0 E.alphaA := by
  rw [E.effort_iff hc hd, E.alphaTildeN_eq]
  rw [E.isEq_iff] at hc hd
  rw [hc.1, hd.1]

/-- **Appendix B.1, corrected equivalence in (B.8).** Higher under centralization iff
`α_p^n ≤ 0` or `α_a^n ≥ α̃^n`. -/
theorem effort_iff_corrected {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc)
    (hd : E.IsEq .del ad pd) : ad ≤ ac ↔ (E.alphaP ≤ 0 ∨ E.alphaTildeN ≤ E.alphaA) := by
  rw [E.effort_iff_h hc hd]
  rcases le_or_gt E.alphaP 0 with hp | hp
  · have : E.alphaTildeN = 0 := by
      unfold alphaTildeN
      rw [max_eq_right hp, zero_mul, E.cp.br_eq_zero_of_nonpos le_rfl, zero_div]
    rw [this]
    exact ⟨fun _ => Or.inl hp, fun _ => le_max_left _ _⟩
  · have hpos : 0 < E.alphaTildeN := by
      unfold alphaTildeN
      rw [max_eq_left hp.le]
      exact div_pos (E.cp.br_pos (mul_pos hp E.Pp_pos)) (E.cp.br_pos E.Pp_pos)
    constructor
    · intro h
      right
      rcases le_or_gt E.alphaA 0 with ha | ha
      · rw [max_eq_left ha] at h; linarith
      · rwa [max_eq_right ha.le] at h
    · rintro (h | h)
      · linarith
      · exact h.trans (le_max_right _ _)

/-! ### A counterexample to the equivalence in (B.8) -/

/-- An environment for Appendix B.1 from a finite discrete distribution. -/
noncomputable def mkN {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ × ℝ) (ca cp : Cost)
    (hr : ∀ i, 0 ≤ r i) (h1 : ∑ i, r i = 1)
    (hA : ∑ i, r i * (x i).1 < 0) (hP : ∑ i, r i * (x i).2 < 0)
    (hra : 0 < ∑ i, r i * {v : ℝ × ℝ | 0 < v.1}.indicator 1 (x i))
    (hrp : 0 < ∑ i, r i * {v : ℝ × ℝ | 0 < v.2}.indicator 1 (x i))
    (hca : ∑ i, r i * {v : ℝ × ℝ | 0 ≤ v.1}.indicator (fun v => v.1) (x i) ≤ ca.d 1)
    (hcp : ∑ i, r i * {v : ℝ × ℝ | 0 ≤ v.2}.indicator (fun v => v.2) (x i) ≤ cp.d 1) : EnvN where
  F := discMeasure r x
  isProb := ⟨by
    have h := disc_real r x hr MeasurableSet.univ
    simp only [Set.indicator_univ, Pi.one_apply, mul_one, h1] at h
    exact (ENNReal.toReal_eq_one_iff _).1 h⟩
  int_a := disc_integrable r x _
  int_p := disc_integrable r x _
  Ea_neg := by rw [disc_integral r x hr]; exact hA
  Ep_neg := by rw [disc_integral r x hr]; exact hP
  acc := CanonicallyOrderedAdd.mul_pos.2
    ⟨pos_iff_ne_zero.2 (disc_ne_zero r x hr (measurableSet_lt measurable_const measurable_fst) hra),
      pos_iff_ne_zero.2
        (disc_ne_zero r x hr (measurableSet_lt measurable_const measurable_snd) hrp)⟩
  ca := ca
  cp := cp
  ca_large := by rw [disc_integral r x hr]; exact hca
  cp_large := by rw [disc_integral r x hr]; exact hcp

/-- `(v_a, v_p) = (1, -2)` or `(-2, 1)` with probability `1/2` each. -/
noncomputable def EN : EnvN :=
  mkN ![1/2, 1/2] ![(1, -2), (-2, 1)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator, Cost.quad]; norm_num)

lemma EN_integral (f : ℝ × ℝ → ℝ) : ∫ v, f v ∂EN.F = 1 / 2 * f (1, -2) + 1 / 2 * f (-2, 1) := by
  show ∫ v, f v ∂(discMeasure ![1/2, 1/2] ![(1, -2), (-2, 1)]) = _
  rw [disc_integral _ _ (by intro i; fin_cases i <;> norm_num), Fin.sum_univ_two]
  simp

lemma EN_Pa : EN.Pa = 1 / 2 := by
  simp [Pa, EI, EN_integral, Set.indicator, Regime.dm]
lemma EN_Pp : EN.Pp = 1 / 2 := by
  simp [Pp, EI, EN_integral, Set.indicator, Regime.dm]
lemma EN_Ya : EN.Ya = -1 := by
  simp [Ya, EI, EN_integral, Set.indicator, Regime.dm]
lemma EN_Yp : EN.Yp = -1 := by
  simp [Yp, EI, EN_integral, Set.indicator, Regime.dm]
lemma EN_alphaA : EN.alphaA = -2 := by rw [alphaA, EN_Ya, EN_Pa]; norm_num
lemma EN_alphaP : EN.alphaP = -2 := by rw [alphaP, EN_Yp, EN_Pp]; norm_num

/-- **The equivalence in (B.8) fails.** In `EN` the agent's effort is (weakly)
higher under centralization, yet `α_a^n < α̃^n`. -/
theorem simplification_fails :
    ∃ E : EnvN, E.ea .del ≤ E.ea .cen ∧ E.alphaA < E.alphaTildeN := by
  refine ⟨EN, ?_, ?_⟩
  · rw [EN.effort_iff_corrected (EN.isEq_eq .cen) (EN.isEq_eq .del), EN_alphaP]
    left; norm_num
  · have : EN.alphaTildeN = 0 := by
      unfold alphaTildeN
      rw [EN_alphaP, max_eq_right (by norm_num), zero_mul,
        EN.cp.br_eq_zero_of_nonpos le_rfl, zero_div]
    rw [this, EN_alphaA]; norm_num

/-- **Analogue of Proposition 3(c), weak form.** If `α_a^n < 0`, the agent's effort is weakly
lower under centralization (it is zero there). -/
theorem prop3c_analogue (hα : E.alphaA < 0) {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc)
    (hd : E.IsEq .del ad pd) : ac ≤ ad := by
  rw [E.isEq_iff] at hc hd
  obtain ⟨-, rfl⟩ := hc
  obtain ⟨-, rfl⟩ := hd
  rw [E.ea_cen_eq, max_eq_left hα.le, zero_mul, mul_zero, E.ca.br_eq_zero_of_nonpos le_rfl]
  exact E.ca.br_nonneg _

/-- **The analogue of Proposition 3(c) holds only weakly.** In `EN`, `α_a^n < 0` and yet the
agent's effort is the same in both regimes (not strictly lower under centralization). -/
theorem prop3c_analogue_weak : ∃ E : EnvN, E.alphaA < 0 ∧ E.ea .cen = E.ea .del := by
  refine ⟨EN, by rw [EN_alphaA]; norm_num, ?_⟩
  apply le_antisymm
  · rw [EN.ea_cen_eq, EN_alphaA, max_eq_left (by norm_num), zero_mul, mul_zero,
      EN.ca.br_eq_zero_of_nonpos le_rfl]
    exact EN.ca.br_nonneg _
  · rw [EN.effort_iff_corrected (EN.isEq_eq .cen) (EN.isEq_eq .del), EN_alphaP]
    left; norm_num

end EnvN

end MI
