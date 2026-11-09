import ManagerialIntervention.Model

/-!
# Section 3.1: formal delegation and agent motivation

* `MI.Env.lemma1`  — Lemma 1 (principal effort higher under centralization);
* `MI.Env.lemma2a`, `MI.Env.lemma2b` — Lemma 2;
* `MI.Env.prop3`   — Proposition 3 (the threshold `α̃`), with parts
  `prop3a`, `prop3b_convex`, `prop3b_concave` (and strict versions), `prop3c_neg`, `prop3c_pos`.

All statements are about the equilibrium objects of `MI.Env.IsEq`, i.e. best responses to
the payoff functions of the model, not about the first-order conditions.
-/

namespace MI

open Set

/-- `α̃(x) = h(-max{x,0} E(v_p 1_{v_p<0})) / h(-E(v_p 1_{v_p<0}))` with `h = (c_p')⁻¹`.
It depends only on `c_p` and `N_p = E(v_p 1_{v_p<0})`. -/
noncomputable def alphaTilde (cp : Cost) (Np x : ℝ) : ℝ := cp.br (-(max x 0) * Np) / cp.br (-Np)

namespace Cost

variable (κ : Cost)

lemma br_le_br_iff {m m' : ℝ} (hm : 0 < m) (hm1 : m ≤ κ.d 1) (hm'1 : m' ≤ κ.d 1) :
    κ.br m ≤ κ.br m' ↔ m ≤ m' := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    rcases le_or_gt m' 0 with h0 | h0
    · rw [κ.br_eq_zero_of_nonpos h0] at h; have := κ.br_pos hm; linarith
    · have := κ.br_strictMonoOn ⟨h0.le, hm'1⟩ ⟨hm.le, hm1⟩ h'; linarith
  · intro h; exact κ.br_mono h

lemma br_lt_br_iff {m m' : ℝ} (hm : 0 < m) (hm1 : m ≤ κ.d 1) (hm'1 : m' ≤ κ.d 1) :
    κ.br m < κ.br m' ↔ m < m' := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have := κ.br_mono h'; linarith
  · intro h; exact κ.br_strictMonoOn ⟨hm.le, hm1⟩ ⟨by linarith, hm'1⟩ h

end Cost

lemma alphaTilde_nonneg (cp : Cost) {Np : ℝ} (hNp : Np < 0) (x : ℝ) : 0 ≤ alphaTilde cp Np x :=
  div_nonneg (cp.br_nonneg _) (cp.br_pos (by linarith)).le

lemma alphaTilde_le_one (cp : Cost) {Np : ℝ} (hNp : Np < 0) {x : ℝ} (hx : x ≤ 1) :
    alphaTilde cp Np x ≤ 1 := by
  unfold alphaTilde
  rw [div_le_one (cp.br_pos (by linarith))]
  apply cp.br_mono
  have : max x 0 ≤ 1 := max_le hx zero_le_one
  nlinarith

lemma alphaTilde_one (cp : Cost) {Np : ℝ} (hNp : Np < 0) : alphaTilde cp Np 1 = 1 := by
  unfold alphaTilde
  rw [max_eq_left zero_le_one, neg_one_mul, div_self (cp.br_pos (by linarith)).ne']

namespace Env

variable (E : Env)

lemma ep_del_eq : E.ep .del = E.cp.br (-(max E.alphaP 0) * E.Np) := E.mp_del_eq

lemma ep_cen_pos : 0 < E.ep .cen := E.cp.br_pos (by simp only [mp]; linarith [E.Np_neg])

lemma alphaTilde_eq : alphaTilde E.cp E.Np E.alphaP = E.ep .del / E.ep .cen := by
  rw [E.ep_del_eq]; rfl

lemma ea_cen_eq : E.ea .cen = E.ca.br (E.A - E.ep .cen * E.Xa) := by unfold ea; rw [E.Va_cen]

lemma ea_del_eq : E.ea .del = E.ca.br (E.A - E.ep .del * E.Na) := by unfold ea; rw [E.Va_del]

lemma md_pos {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) : 0 < E.A - p * E.Na := by
  nlinarith [E.Na_neg, E.A_pos, hp.1]

lemma md_le {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) : E.A - p * E.Na ≤ E.ca.d 1 := by
  nlinarith [E.ca_bound, E.Na_neg, hp.2]

lemma mc_le {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) : E.A - p * E.Xa ≤ E.ca.d 1 := by
  have h1 := E.ca_bound
  have h2 := E.Xa_le
  have h3 := E.Na_le_Xa
  have hN := E.Na_neg
  rcases le_or_gt 0 E.Xa with h4 | h4
  · nlinarith [hp.1, hp.2]
  · nlinarith [hp.1, hp.2]

/-! ### Lemma 1 -/

/-- **Lemma 1.** The principal's effort is weakly higher under centralization than under
delegation. -/
theorem lemma1 {pc pd : ℝ} (hc : IsBR (E.Up .cen) pc) (hd : IsBR (E.Up .del) pd) : pd ≤ pc := by
  rw [E.isBR_Up_iff] at hc hd
  subst hc hd
  exact E.cp.br_mono (by simp only [mp]; linarith [E.Np_le_Xp])

/-! ### Lemma 2 -/

/-- **Lemma 2(a).** Under delegation the agent's best response is weakly increasing in the
principal's effort. -/
theorem lemma2a {p p' a a' : ℝ} (hpp : p ≤ p') (ha : IsBR (E.Ua .del p) a)
    (ha' : IsBR (E.Ua .del p') a') : a ≤ a' := by
  rw [E.isBR_Ua_iff] at ha ha'
  subst ha ha'
  rw [E.Va_del, E.Va_del]
  exact E.ca.br_mono (by nlinarith [E.Na_neg])

/-- **Lemma 2(b).** Under centralization the agent's best response is weakly increasing in the
principal's effort (on `[0,1]`) if and only if `α_a ≥ 0`. -/
theorem lemma2b :
    (∀ p p' a a' : ℝ, p ∈ Icc (0 : ℝ) 1 → p' ∈ Icc (0 : ℝ) 1 → p ≤ p' →
        IsBR (E.Ua .cen p) a → IsBR (E.Ua .cen p') a' → a ≤ a') ↔ 0 ≤ E.alphaA := by
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    have hX : 0 < E.Xa := E.alphaA_neg_iff.1 hneg
    have hA := E.A_pos
    set ε := min 1 (E.A / (2 * E.Xa)) with hε
    have hε0 : 0 < ε := lt_min one_pos (div_pos hA (by linarith))
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεX : ε * E.Xa ≤ E.A / 2 := by
      have : ε ≤ E.A / (2 * E.Xa) := min_le_right _ _
      calc ε * E.Xa ≤ E.A / (2 * E.Xa) * E.Xa := mul_le_mul_of_nonneg_right this hX.le
        _ = E.A / 2 := by field_simp
    have key := h 0 ε (E.ca.br (E.Va .cen 0)) (E.ca.br (E.Va .cen ε)) ⟨le_rfl, zero_le_one⟩
      ⟨hε0.le, hε1⟩ hε0.le ((E.isBR_Ua_iff _).2 rfl) ((E.isBR_Ua_iff _).2 rfl)
    rw [E.Va_cen, E.Va_cen] at key
    have hlt : E.ca.br (E.A - ε * E.Xa) < E.ca.br (E.A - 0 * E.Xa) := by
      rw [E.ca.br_lt_br_iff (by linarith) (E.mc_le ⟨hε0.le, hε1⟩)
        (E.mc_le ⟨le_rfl, zero_le_one⟩)]
      nlinarith
    linarith
  · intro h p p' a a' _ _ hpp ha ha'
    rw [E.isBR_Ua_iff] at ha ha'
    subst ha ha'
    rw [E.Va_cen, E.Va_cen, E.Xa_eq]
    apply E.ca.br_mono
    have : E.alphaA * E.Na ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h E.Na_neg.le
    nlinarith

/-! ### Proposition 3 -/

lemma key_le {pc pd : ℝ} (hpc : 0 < pc) :
    E.A - pd * E.Na ≤ E.A - pc * E.Xa ↔ pd / pc ≤ E.alphaA := by
  rw [E.Xa_eq, div_le_iff₀ hpc]
  have hN := E.Na_neg
  constructor
  · intro h
    have : pc * E.alphaA * E.Na ≤ pd * E.Na := by linarith
    exact by
      have := (mul_le_mul_right_of_neg hN).1 this
      linarith
  · intro h
    have : pc * E.alphaA * E.Na ≤ pd * E.Na := (mul_le_mul_right_of_neg hN).2 (by linarith)
    linarith

lemma key_lt {pc pd : ℝ} (hpc : 0 < pc) :
    E.A - pd * E.Na < E.A - pc * E.Xa ↔ pd / pc < E.alphaA := by
  rw [E.Xa_eq, div_lt_iff₀ hpc]
  have hN := E.Na_neg
  constructor
  · intro h
    have : pc * E.alphaA * E.Na < pd * E.Na := by linarith
    have := (mul_lt_mul_right_of_neg hN).1 this
    linarith
  · intro h
    have : pc * E.alphaA * E.Na < pd * E.Na := (mul_lt_mul_right_of_neg hN).2 (by linarith)
    linarith

/-- The equilibrium version: weak comparison. -/
lemma ea_le_iff : E.ea .del ≤ E.ea .cen ↔ alphaTilde E.cp E.Np E.alphaP ≤ E.alphaA := by
  rw [E.ea_cen_eq, E.ea_del_eq, E.alphaTilde_eq,
    E.ca.br_le_br_iff (E.md_pos (E.ep_mem _)) (E.md_le (E.ep_mem _)) (E.mc_le (E.ep_mem _))]
  exact E.key_le E.ep_cen_pos

/-- The equilibrium version: strict comparison. -/
lemma ea_lt_iff : E.ea .del < E.ea .cen ↔ alphaTilde E.cp E.Np E.alphaP < E.alphaA := by
  rw [E.ea_cen_eq, E.ea_del_eq, E.alphaTilde_eq,
    E.ca.br_lt_br_iff (E.md_pos (E.ep_mem _)) (E.md_le (E.ep_mem _)) (E.mc_le (E.ep_mem _))]
  exact E.key_lt E.ep_cen_pos

/-- **Proposition 3.** The agent's equilibrium effort is (weakly) higher under centralization
than under delegation iff `α_a ≥ α̃(α_p)`. -/
theorem prop3 {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) :
    ad ≤ ac ↔ alphaTilde E.cp E.Np E.alphaP ≤ E.alphaA := by
  rw [E.isEq_iff] at hc hd
  obtain ⟨-, rfl⟩ := hc
  obtain ⟨-, rfl⟩ := hd
  exact E.ea_le_iff

/-- **Proposition 3 (strict form).** The agent's effort is strictly higher under
centralization iff `α_a > α̃(α_p)`. -/
theorem prop3_strict {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) :
    ad < ac ↔ alphaTilde E.cp E.Np E.alphaP < E.alphaA := by
  rw [E.isEq_iff] at hc hd
  obtain ⟨-, rfl⟩ := hc
  obtain ⟨-, rfl⟩ := hd
  exact E.ea_lt_iff

lemma negNp_mem : -E.Np ∈ Icc 0 (E.cp.d 1) := ⟨by linarith [E.Np_neg], E.cp_bound⟩

lemma scaled_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : -x * E.Np ∈ Icc 0 (E.cp.d 1) := by
  have hN := E.Np_neg
  have hb := E.cp_bound
  exact ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩

/-- **Proposition 3(a).** If `h` is linear (e.g. `c_p` quadratic) and `α_p > 0`, the agent's
effort is higher under centralization iff `α_a ≥ α_p`.  (The paper also assumes `α_a > 0`;
it is not needed.) -/
theorem prop3a (hlin : ∃ k b : ℝ, ∀ x ∈ Icc 0 (E.cp.d 1), E.cp.br x = k * x + b)
    (hαp : 0 < E.alphaP) {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) :
    ad ≤ ac ↔ E.alphaP ≤ E.alphaA := by
  rw [E.prop3 hc hd]
  suffices h : alphaTilde E.cp E.Np E.alphaP = E.alphaP by rw [h]
  obtain ⟨k, b, hkb⟩ := hlin
  have hb : b = 0 := by
    have := hkb 0 ⟨le_rfl, E.cp.d_one_pos.le⟩
    rw [E.cp.br_eq_zero_of_nonpos le_rfl] at this
    linarith
  have hpos : 0 < E.cp.br (-E.Np) := E.cp.br_pos (by linarith [E.Np_neg])
  unfold alphaTilde
  rw [max_eq_left hαp.le, hkb _ (E.scaled_mem ⟨hαp.le, E.alphaP_le_one⟩),
    hkb _ E.negNp_mem, hb]
  rw [hkb _ E.negNp_mem, hb] at hpos
  have hk : k * -E.Np ≠ 0 := by linarith
  rw [add_zero, add_zero, div_eq_iff hk]
  ring

/-- The convexity inequality `h(αy) < α h(y)` for `0 < α < 1` used in Proposition 3(b). -/
lemma convex_ineq (hcv : StrictConvexOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br) {α : ℝ} (h0 : 0 < α)
    (h1 : α < 1) : E.cp.br (-α * E.Np) < α * E.cp.br (-E.Np) := by
  have hy : -E.Np ∈ Icc 0 (E.cp.d 1) := E.negNp_mem
  have h0m : (0 : ℝ) ∈ Icc 0 (E.cp.d 1) := ⟨le_rfl, E.cp.d_one_pos.le⟩
  have := hcv.2 hy h0m (by linarith [E.Np_neg]) h0 (by linarith : 0 < 1 - α) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, E.cp.br_eq_zero_of_nonpos le_rfl] at this
  have e : α * -E.Np = -α * E.Np := by ring
  rwa [e] at this

lemma concave_ineq (hcc : StrictConcaveOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br) {α : ℝ} (h0 : 0 < α)
    (h1 : α < 1) : α * E.cp.br (-E.Np) < E.cp.br (-α * E.Np) := by
  have hy : -E.Np ∈ Icc 0 (E.cp.d 1) := E.negNp_mem
  have h0m : (0 : ℝ) ∈ Icc 0 (E.cp.d 1) := ⟨le_rfl, E.cp.d_one_pos.le⟩
  have := hcc.2 hy h0m (by linarith [E.Np_neg]) h0 (by linarith : 0 < 1 - α) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, E.cp.br_eq_zero_of_nonpos le_rfl] at this
  have e : α * -E.Np = -α * E.Np := by ring
  rwa [e] at this

lemma alphaTilde_pos_eq (hpos : 0 < E.alphaP) :
    alphaTilde E.cp E.Np E.alphaP = E.cp.br (-E.alphaP * E.Np) / E.cp.br (-E.Np) := by
  unfold alphaTilde; rw [max_eq_left hpos.le]

/-- **Proposition 3(b), convex case, strict.** If `α_a = α_p ∈ (0,1)` and `h` is strictly
convex, the agent's effort is strictly higher under centralization. -/
theorem prop3b_convex_strict (hcv : StrictConvexOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br)
    (heq : E.alphaA = E.alphaP) (hpos : 0 < E.alphaP) (hlt : E.alphaP < 1)
    {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ad < ac := by
  rw [E.prop3_strict hc hd, E.alphaTilde_pos_eq hpos, heq,
    div_lt_iff₀ (E.cp.br_pos (by linarith [E.Np_neg]))]
  exact E.convex_ineq hcv hpos hlt

/-- **Proposition 3(b), convex case.** If `α_a = α_p > 0` and `h` is strictly convex, the
agent's effort is (weakly) higher under centralization. -/
theorem prop3b_convex (hcv : StrictConvexOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br)
    (heq : E.alphaA = E.alphaP) (hpos : 0 < E.alphaP)
    {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ad ≤ ac := by
  rcases E.alphaP_le_one.lt_or_eq with hlt | h1
  · exact (E.prop3b_convex_strict hcv heq hpos hlt hc hd).le
  · rw [E.prop3 hc hd, heq, h1, alphaTilde_one _ E.Np_neg]

/-- **Proposition 3(b), concave case, strict.** If `α_a = α_p ∈ (0,1)` and `h` is strictly
concave, the agent's effort is strictly lower under centralization. -/
theorem prop3b_concave_strict (hcc : StrictConcaveOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br)
    (heq : E.alphaA = E.alphaP) (hpos : 0 < E.alphaP) (hlt : E.alphaP < 1)
    {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ac < ad := by
  by_contra h
  push Not at h
  rw [E.prop3 hc hd, E.alphaTilde_pos_eq hpos, heq,
    div_le_iff₀ (E.cp.br_pos (by linarith [E.Np_neg]))] at h
  have := E.concave_ineq hcc hpos hlt
  linarith

/-- **Proposition 3(b), concave case.** If `α_a = α_p > 0` and `h` is strictly concave, the
agent's effort is weakly lower under centralization.  At `α_a = α_p = 1` the two efforts are
equal, so "lower" holds only weakly there. -/
theorem prop3b_concave (hcc : StrictConcaveOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br)
    (heq : E.alphaA = E.alphaP) (hpos : 0 < E.alphaP)
    {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ac ≤ ad := by
  rcases E.alphaP_le_one.lt_or_eq with hlt | h1
  · exact (E.prop3b_concave_strict hcc heq hpos hlt hc hd).le
  · -- `α_a = α_p = 1`: the comparison is an equality
    have hge : ad ≤ ac := by rw [E.prop3 hc hd, heq, h1, alphaTilde_one _ E.Np_neg]
    have hle : ¬ ad < ac := by
      rw [E.prop3_strict hc hd, heq, h1, alphaTilde_one _ E.Np_neg]; exact lt_irrefl _
    push Not at hle
    exact hle

/-- **Proposition 3(c), first part.** If `α_a < 0`, the agent's effort is strictly lower under
centralization. -/
theorem prop3c_neg (hα : E.alphaA < 0) {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc)
    (hd : E.IsEq .del ad pd) : ac < ad := by
  by_contra h
  push Not at h
  rw [E.prop3 hc hd] at h
  have := alphaTilde_nonneg E.cp E.Np_neg E.alphaP
  linarith

/-- **Proposition 3(c), second part.** If `α_p < 0 ≤ α_a`, the agent's effort is weakly higher
under centralization. -/
theorem prop3c_pos (hp : E.alphaP < 0) (ha : 0 ≤ E.alphaA) {ac pc ad pd : ℝ}
    (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ad ≤ ac := by
  rw [E.prop3 hc hd]
  unfold alphaTilde
  rw [max_eq_right hp.le]
  simp [E.cp.br_eq_zero_of_nonpos le_rfl, ha]

end Env

end MI
