import ManagerialIntervention.Prop5LogConcave

/-!
# Appendix B.1: the analogues of Propositions 3 and 4

With `E(v_a), E(v_p) < 0`, the appendix states that analogues of Proposition 3(a)–(c) hold with
`α_a^n, α_p^n` and that the principal centralizes iff `α_a^n` exceeds an increasing threshold
in `α_p^n` (the analogue of Proposition 4).

* `MI.EnvN.effort_lt_iff` — strict version of the appendix's comparison of agent efforts.
* `MI.EnvN.prop3a_analogue` — Proposition 3(a): with linear `h` and `α_p^n > 0`, effort is
  weakly higher under centralization iff `α_a^n ≥ α_p^n`.
* `MI.EnvN.prop3b_convex_analogue`, `MI.EnvN.prop3b_concave_analogue` — Proposition 3(b) for
  `α_a^n = α_p^n ∈ (0,1)`; `MI.EnvN.ea_eq_of_alpha_one` — at `α_a^n = α_p^n = 1` the efforts
  coincide, as in the main text.
* `MI.EnvN.prop3c_analogue_strict` — Proposition 3(c), strict, when `α_p^n > 0`.
* `MI.prop4_analogue` — Proposition 4: an increasing threshold `α̂` with "centralize iff
  `α̂(α_p^n) < α_a^n`", for all environments sharing `E(v_a 1_{v_a≥0})`, `E(v_p 1_{v_p≥0})`,
  `c_a`, `c_p`.
* Non-vacuity: `MI.EnvN.nonvacuous_prop3a_analogue`, `MI.EnvN.nonvacuous_prop3b_convex_analogue`,
  `MI.EnvN.nonvacuous_prop3b_concave_analogue`, `MI.EnvN.nonvacuous_prop3c_analogue_strict`,
  `MI.nonvacuous_prop4_analogue`.
-/

namespace MI

open Set

namespace EnvN

variable (E : EnvN)

lemma Pp_mem : E.Pp ∈ Icc 0 (E.cp.d 1) := ⟨E.Pp_pos.le, E.Pp_le⟩

lemma ep_cen_eq' : E.ep .cen = E.cp.br E.Pp := rfl

/-- **Strict comparison of agent efforts.** Strictly higher under centralization iff
`α̃^n < max{0, α_a^n}`. -/
theorem effort_lt_iff {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) :
    ad < ac ↔ E.alphaTildeN < max 0 E.alphaA := by
  rw [E.alphaTildeN_eq]
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
  rw [E.ca.br_strictMonoOn.lt_iff_lt hx hy, div_lt_iff₀ E.ep_cen_pos]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma alphaTildeN_pos_eq (hpos : 0 < E.alphaP) :
    E.alphaTildeN = E.cp.br (E.alphaP * E.Pp) / E.cp.br E.Pp := by
  unfold alphaTildeN; rw [max_eq_left hpos.le]

lemma alphaTildeN_pos (hpos : 0 < E.alphaP) : 0 < E.alphaTildeN := by
  rw [E.alphaTildeN_pos_eq hpos]
  exact div_pos (E.cp.br_pos (mul_pos hpos E.Pp_pos)) (E.cp.br_pos E.Pp_pos)

/-- **Analogue of Proposition 3(a).** With linear `h` and `α_p^n > 0`, the agent's effort is
weakly higher under centralization iff `α_a^n ≥ α_p^n`. -/
theorem prop3a_analogue (hlin : ∃ k b : ℝ, ∀ x ∈ Icc 0 (E.cp.d 1), E.cp.br x = k * x + b)
    (hαp : 0 < E.alphaP) {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) :
    ad ≤ ac ↔ E.alphaP ≤ E.alphaA := by
  rw [E.effort_iff_h hc hd]
  have hT : E.alphaTildeN = E.alphaP := by
    obtain ⟨k, b, hkb⟩ := hlin
    have hb : b = 0 := by
      have := hkb 0 ⟨le_rfl, E.cp.d_one_pos.le⟩
      rw [E.cp.br_eq_zero_of_nonpos le_rfl] at this
      linarith
    have hm : E.alphaP * E.Pp ∈ Icc 0 (E.cp.d 1) :=
      ⟨mul_nonneg hαp.le E.Pp_pos.le, by nlinarith [E.alphaP_le_one, E.Pp_pos, E.Pp_le]⟩
    have hpos : 0 < E.cp.br E.Pp := E.cp.br_pos E.Pp_pos
    rw [E.alphaTildeN_pos_eq hαp, hkb _ hm, hkb _ E.Pp_mem, hb]
    rw [hkb _ E.Pp_mem, hb] at hpos
    have hk : k * E.Pp ≠ 0 := (by linarith : 0 < k * E.Pp).ne'
    rw [add_zero, add_zero, div_eq_iff hk]
    ring
  rw [hT]
  constructor
  · intro h
    rcases le_or_gt E.alphaA 0 with ha | ha
    · rw [max_eq_left ha] at h; linarith
    · rwa [max_eq_right ha.le] at h
  · intro h; exact h.trans (le_max_right _ _)

lemma convex_ineqN (hcv : StrictConvexOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br) {α : ℝ} (h0 : 0 < α)
    (h1 : α < 1) : E.cp.br (α * E.Pp) < α * E.cp.br E.Pp := by
  have h0m : (0 : ℝ) ∈ Icc 0 (E.cp.d 1) := ⟨le_rfl, E.cp.d_one_pos.le⟩
  have := hcv.2 E.Pp_mem h0m E.Pp_pos.ne' h0 (by linarith : 0 < 1 - α) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, E.cp.br_eq_zero_of_nonpos le_rfl] at this
  exact this

lemma concave_ineqN (hcc : StrictConcaveOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br) {α : ℝ} (h0 : 0 < α)
    (h1 : α < 1) : α * E.cp.br E.Pp < E.cp.br (α * E.Pp) := by
  have h0m : (0 : ℝ) ∈ Icc 0 (E.cp.d 1) := ⟨le_rfl, E.cp.d_one_pos.le⟩
  have := hcc.2 E.Pp_mem h0m E.Pp_pos.ne' h0 (by linarith : 0 < 1 - α) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, E.cp.br_eq_zero_of_nonpos le_rfl] at this
  exact this

/-- **Analogue of Proposition 3(b), convex case.** If `α_a^n = α_p^n ∈ (0,1)` and `h` is
strictly convex, the agent's effort is strictly higher under centralization. -/
theorem prop3b_convex_analogue (hcv : StrictConvexOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br)
    (heq : E.alphaA = E.alphaP) (hpos : 0 < E.alphaP) (hlt : E.alphaP < 1)
    {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ad < ac := by
  rw [E.effort_lt_iff hc hd, E.alphaTildeN_pos_eq hpos, heq, max_eq_right hpos.le,
    div_lt_iff₀ (E.cp.br_pos E.Pp_pos)]
  exact E.convex_ineqN hcv hpos hlt

/-- **Analogue of Proposition 3(b), concave case.** If `α_a^n = α_p^n ∈ (0,1)` and `h` is
strictly concave, the agent's effort is strictly lower under centralization. -/
theorem prop3b_concave_analogue (hcc : StrictConcaveOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br)
    (heq : E.alphaA = E.alphaP) (hpos : 0 < E.alphaP) (hlt : E.alphaP < 1)
    {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ac < ad := by
  by_contra h
  push Not at h
  rw [E.effort_iff_h hc hd, E.alphaTildeN_pos_eq hpos, heq, max_eq_right hpos.le,
    div_le_iff₀ (E.cp.br_pos E.Pp_pos)] at h
  have := E.concave_ineqN hcc hpos hlt
  linarith

/-- At `α_a^n = α_p^n = 1` the agent's effort is the same in both regimes. -/
theorem ea_eq_of_alpha_one (ha : E.alphaA = 1) (hp : E.alphaP = 1) : E.ea .cen = E.ea .del := by
  rw [E.ea_cen_eq, E.ea_del_eq, E.ep_del_eq, E.ep_cen_eq', ha, hp]
  norm_num

/-- **Analogue of Proposition 3(c), strict.** If `α_a^n < 0 < α_p^n`, the agent's effort is
strictly lower under centralization. -/
theorem prop3c_analogue_strict (hα : E.alphaA < 0) (hp : 0 < E.alphaP)
    {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ac < ad := by
  by_contra h
  push Not at h
  rw [E.effort_iff_h hc hd, max_eq_left hα.le] at h
  have := E.alphaTildeN_pos hp
  linarith

/-! ### Non-vacuity of the Proposition 3 analogues -/

/-- `(v_a, v_p) = (1, 1)` w.p. `1/4`, `(2, -1)` w.p. `1/8`, `(-1, 2)` w.p. `1/8`, `(-1, -1)`
w.p. `1/2`: negative expected values and `α_a^n = α_p^n = 1/4`. -/
noncomputable def EB (cp : Cost) (hcp : 1 / 2 ≤ cp.d 1) : EnvN :=
  mkN ![1/4, 1/8, 1/8, 1/2] ![(1, 1), (2, -1), (-1, 2), (-1, -1)] cq2 cp
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_four])
    (by norm_num [Fin.sum_univ_four])
    (by norm_num [Fin.sum_univ_four])
    (by norm_num [Fin.sum_univ_four, Set.indicator])
    (by norm_num [Fin.sum_univ_four, Set.indicator])
    (by norm_num [Fin.sum_univ_four, Set.indicator, Cost.quad])
    (by norm_num [Fin.sum_univ_four, Set.indicator]; linarith)

lemma EB_integral (cp : Cost) (hcp : 1 / 2 ≤ cp.d 1) (f : ℝ × ℝ → ℝ) :
    ∫ v, f v ∂(EB cp hcp).F =
      1 / 4 * f (1, 1) + 1 / 8 * f (2, -1) + 1 / 8 * f (-1, 2) + 1 / 2 * f (-1, -1) := by
  show ∫ v, f v ∂(discMeasure ![1/4, 1/8, 1/8, 1/2] ![(1, 1), (2, -1), (-1, 2), (-1, -1)]) = _
  rw [disc_integral _ _ (by intro i; fin_cases i <;> norm_num), Fin.sum_univ_four]
  simp

lemma EB_alphaA (cp : Cost) (hcp : 1 / 2 ≤ cp.d 1) : (EB cp hcp).alphaA = 1 / 4 := by
  rw [alphaA]
  norm_num [Ya, Pa, EI, EB_integral, Set.indicator, Regime.dm]

lemma EB_alphaP (cp : Cost) (hcp : 1 / 2 ≤ cp.d 1) : (EB cp hcp).alphaP = 1 / 4 := by
  rw [alphaP]
  norm_num [Yp, Pp, EI, EB_integral, Set.indicator, Regime.dm]

theorem nonvacuous_prop3a_analogue :
    ∃ E : EnvN, (∃ k b : ℝ, ∀ x ∈ Icc 0 (E.cp.d 1), E.cp.br x = k * x + b) ∧
      0 < E.alphaP ∧ E.ea .del ≤ E.ea .cen := by
  let E := EB cq1 (by simp [Cost.quad]; norm_num)
  have hl : ∃ k b : ℝ, ∀ x ∈ Icc 0 (E.cp.d 1), E.cp.br x = k * x + b := quad_linear one_pos
  have hp : 0 < E.alphaP := by rw [EB_alphaP]; norm_num
  refine ⟨E, hl, hp, ?_⟩
  rw [E.prop3a_analogue hl hp (E.isEq_eq .cen) (E.isEq_eq .del), EB_alphaA, EB_alphaP]

theorem nonvacuous_prop3b_convex_analogue :
    ∃ E : EnvN, StrictConvexOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br ∧ E.alphaA = E.alphaP ∧
      0 < E.alphaP ∧ E.alphaP < 1 ∧ E.ea .del < E.ea .cen := by
  let E := EB cvx (by rw [cvx_d_one]; norm_num)
  have h1 : E.alphaA = E.alphaP := by rw [EB_alphaA, EB_alphaP]
  have h2 : 0 < E.alphaP := by rw [EB_alphaP]; norm_num
  have h3 : E.alphaP < 1 := by rw [EB_alphaP]; norm_num
  exact ⟨E, cvx_strictConvex, h1, h2, h3,
    E.prop3b_convex_analogue cvx_strictConvex h1 h2 h3 (E.isEq_eq .cen) (E.isEq_eq .del)⟩

theorem nonvacuous_prop3b_concave_analogue :
    ∃ E : EnvN, StrictConcaveOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br ∧ E.alphaA = E.alphaP ∧
      0 < E.alphaP ∧ E.alphaP < 1 ∧ E.ea .cen < E.ea .del := by
  let E := EB cube (by rw [cube_d_one]; norm_num)
  have h1 : E.alphaA = E.alphaP := by rw [EB_alphaA, EB_alphaP]
  have h2 : 0 < E.alphaP := by rw [EB_alphaP]; norm_num
  have h3 : E.alphaP < 1 := by rw [EB_alphaP]; norm_num
  exact ⟨E, cube_strictConcave, h1, h2, h3,
    E.prop3b_concave_analogue cube_strictConcave h1 h2 h3 (E.isEq_eq .cen) (E.isEq_eq .del)⟩

/-- `(v_a, v_p) = (1, 1)` w.p. `1/4`, `(-3, 1)` w.p. `1/4`, `(-1, -3)` w.p. `1/2`: negative
expected values, `α_a^n = -2` and `α_p^n = 1/2`. -/
noncomputable def EC : EnvN :=
  mkN ![1/4, 1/4, 1/2] ![(1, 1), (-3, 1), (-1, -3)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three, Set.indicator])
    (by norm_num [Fin.sum_univ_three, Set.indicator])
    (by norm_num [Fin.sum_univ_three, Set.indicator, Cost.quad])
    (by norm_num [Fin.sum_univ_three, Set.indicator, Cost.quad])

lemma EC_integral (f : ℝ × ℝ → ℝ) :
    ∫ v, f v ∂EC.F = 1 / 4 * f (1, 1) + 1 / 4 * f (-3, 1) + 1 / 2 * f (-1, -3) := by
  show ∫ v, f v ∂(discMeasure ![1/4, 1/4, 1/2] ![(1, 1), (-3, 1), (-1, -3)]) = _
  rw [disc_integral _ _ (by intro i; fin_cases i <;> norm_num), Fin.sum_univ_three]
  simp

lemma EC_alphaA : EC.alphaA = -2 := by
  rw [alphaA]
  norm_num [Ya, Pa, EI, EC_integral, Set.indicator, Regime.dm]

lemma EC_alphaP : EC.alphaP = 1 / 2 := by
  rw [alphaP]
  norm_num [Yp, Pp, EI, EC_integral, Set.indicator, Regime.dm]

theorem nonvacuous_prop3c_analogue_strict :
    ∃ E : EnvN, E.alphaA < 0 ∧ 0 < E.alphaP ∧ E.ea .cen < E.ea .del := by
  have h1 : EC.alphaA < 0 := by rw [EC_alphaA]; norm_num
  have h2 : 0 < EC.alphaP := by rw [EC_alphaP]; norm_num
  exact ⟨EC, h1, h2, EC.prop3c_analogue_strict h1 h2 (EC.isEq_eq .cen) (EC.isEq_eq .del)⟩

end EnvN

/-! ### Analogue of Proposition 4 -/

/-- The primitives held fixed in Appendix B.1: `E(v_a 1_{v_a≥0})`, `E(v_p 1_{v_p≥0})` and the
two costs. -/
structure PrimN where
  Pa : ℝ
  Pp : ℝ
  ca : Cost
  cp : Cost

namespace PrimN

variable (π : PrimN)

/-- Principal effort under centralization. -/
noncomputable def epC : ℝ := π.cp.br π.Pp
/-- The principal's interim payoff under centralization. -/
noncomputable def UC : ℝ := π.cp.val π.Pp
/-- The principal's ex-ante payoff under centralization, as a function of `α_a^n`. -/
noncomputable def PiC (α : ℝ) : ℝ := π.ca.br (π.epC * (max 0 α * π.Pa)) * π.UC
/-- Principal effort under delegation, as a function of `α_p^n`. -/
noncomputable def epD (x : ℝ) : ℝ := π.cp.br (max x 0 * π.Pp)
/-- The principal's interim payoff under delegation, as a function of `α_p^n`. -/
noncomputable def UD (x : ℝ) : ℝ := π.cp.val (max x 0 * π.Pp)
/-- The principal's ex-ante payoff under delegation, as a function of `α_p^n`. -/
noncomputable def PiD (x : ℝ) : ℝ := π.ca.br (π.epD x * π.Pa) * π.UD x

variable {π}

lemma PiC_mono (hPa : 0 ≤ π.Pa) : Monotone π.PiC := by
  intro α α' h
  unfold PiC
  apply mul_le_mul_of_nonneg_right _ (π.cp.val_nonneg _)
  apply π.ca.br_mono
  apply mul_le_mul_of_nonneg_left _ (π.cp.br_nonneg _)
  exact mul_le_mul_of_nonneg_right (max_le_max le_rfl h) hPa

lemma PiC_continuous : Continuous π.PiC := by
  unfold PiC
  exact (π.ca.br_continuous.comp (continuous_const.mul
    ((continuous_const.max continuous_id).mul continuous_const))).mul continuous_const

lemma PiC_zero : π.PiC 0 = 0 := by
  unfold PiC
  rw [max_self, zero_mul, mul_zero, π.ca.br_eq_zero_of_nonpos le_rfl, zero_mul]

lemma PiD_nonneg (x : ℝ) : 0 ≤ π.PiD x :=
  mul_nonneg (π.ca.br_nonneg _) (π.cp.val_nonneg _)

lemma PiD_mono (hPa : 0 ≤ π.Pa) (hPp : 0 ≤ π.Pp) : Monotone π.PiD := by
  intro x x' h
  unfold PiD
  have hm : max x 0 * π.Pp ≤ max x' 0 * π.Pp :=
    mul_le_mul_of_nonneg_right (max_le_max h le_rfl) hPp
  have he : π.ca.br (π.epD x * π.Pa) ≤ π.ca.br (π.epD x' * π.Pa) :=
    π.ca.br_mono (mul_le_mul_of_nonneg_right (π.cp.br_mono hm) hPa)
  have hU : π.UD x ≤ π.UD x' := π.cp.val_mono hm
  exact mul_le_mul he hU (π.cp.val_nonneg _) (π.ca.br_nonneg _)

end PrimN

namespace EnvN

variable (E : EnvN)

/-- The primitives of an Appendix B.1 environment. -/
noncomputable def primN : PrimN := ⟨E.Pa, E.Pp, E.ca, E.cp⟩

lemma payoff_cenN {ac pc : ℝ} (hc : E.IsEq .cen ac pc) :
    ac * E.Up .cen pc = E.primN.PiC E.alphaA := by
  rw [E.isEq_iff] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rw [E.ea_cen_eq]
  rfl

lemma payoff_delN {ad pd : ℝ} (hd : E.IsEq .del ad pd) :
    ad * E.Up .del pd = E.primN.PiD E.alphaP := by
  rw [E.isEq_iff] at hd
  obtain ⟨rfl, rfl⟩ := hd
  have hU : E.Up .del (E.ep .del) = E.cp.val (max E.alphaP 0 * E.Pp) := by
    unfold Up
    rw [E.ep_del_eq]
    show E.cp.br (max E.alphaP 0 * E.Pp) * E.Yp - _ = _
    rw [E.Yp_eq]
    rcases le_or_gt 0 E.alphaP with h | h
    · rw [max_eq_left h]; rfl
    · rw [max_eq_right h.le, zero_mul, E.cp.val_eq_zero_of_nonpos le_rfl,
        E.cp.br_eq_zero_of_nonpos le_rfl, E.cp.c_zero]
      ring
  rw [hU, E.ea_del_eq, E.ep_del_eq]
  rfl

end EnvN

/-- **Analogue of Proposition 4.** For fixed `E(v_a 1_{v_a≥0})`, `E(v_p 1_{v_p≥0})`, `c_a`,
`c_p`, there is an increasing threshold `α̂` such that, in every environment with these
primitives, the principal strictly prefers centralization iff `α̂(α_p^n) < α_a^n`. -/
theorem prop4_analogue (π : PrimN) (hPa : 0 < π.Pa) (hPp : 0 < π.Pp) :
    ∃ αhat : ℝ → ℝ, Monotone αhat ∧ ∀ E : EnvN, E.primN = π → ∀ ac pc ad pd : ℝ,
      E.IsEq .cen ac pc → E.IsEq .del ad pd →
        (ad * E.Up .del pd < ac * E.Up .cen pc ↔ αhat E.alphaP < E.alphaA) := by
  obtain ⟨t, ht, -, hiff⟩ := threshold_exists (PrimN.PiC_mono hPa.le) PrimN.PiC_continuous
    (PrimN.PiD_mono hPa.le hPp.le) zero_le_one
    (fun x => by rw [PrimN.PiC_zero]; exact PrimN.PiD_nonneg x)
  refine ⟨t, ht, fun E hE ac pc ad pd hc hd => ?_⟩
  rw [E.payoff_cenN hc, E.payoff_delN hd, hE]
  exact hiff _ _ E.alphaA_le_one

/-- The hypotheses of `MI.prop4_analogue` hold for the primitives of `EB cq1`. -/
theorem nonvacuous_prop4_analogue :
    ∃ π : PrimN, 0 < π.Pa ∧ 0 < π.Pp ∧ ∃ E : EnvN, E.primN = π :=
  let E := EnvN.EB cq1 (by simp [Cost.quad]; norm_num)
  ⟨E.primN, E.Pa_pos, E.Pp_pos, E, rfl⟩

/-! ### Strict comparisons, boundaries and ties at zero effort -/

namespace Env

variable (E : Env)

/-- **Proposition 3(c), second part, strict.** If `α_p < 0 < α_a`, the agent's effort is
strictly higher under centralization. -/
theorem prop3c_pos_strict (hp : E.alphaP < 0) (ha : 0 < E.alphaA) {ac pc ad pd : ℝ}
    (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ad < ac := by
  rw [E.prop3_strict hc hd]
  unfold alphaTilde
  rw [max_eq_right hp.le, neg_zero, zero_mul, E.cp.br_eq_zero_of_nonpos le_rfl, zero_div]
  exact ha

/-- At the boundary `α_a = 0` of Proposition 3(c), second part, the two efforts coincide. -/
theorem ea_eq_of_alphaA_zero (hp : E.alphaP ≤ 0) (ha : E.alphaA = 0) :
    E.ea .cen = E.ea .del := by
  simp only [E.ea_cen_eq, E.ea_del_eq, E.ep_del_eq, E.Xa_eq, ha, max_eq_right hp, neg_zero,
    zero_mul, mul_zero, sub_zero, E.cp.br_eq_zero_of_nonpos (le_refl (0 : ℝ))]

theorem nonvacuous_prop3c_pos_strict :
    ∃ E : Env, E.alphaP < 0 ∧ 0 < E.alphaA ∧ E.ea .del < E.ea .cen := by
  have hp : E5.alphaP < 0 := by rw [E5_alphaP]; norm_num
  have ha : 0 < E5.alphaA := by rw [E5_alphaA]; norm_num
  exact ⟨E5, hp, ha, E5.prop3c_pos_strict hp ha (E5.isEq_eq .cen) (E5.isEq_eq .del)⟩

end Env

namespace EnvN

variable (E : EnvN)

lemma alphaTildeN_nonneg : 0 ≤ E.alphaTildeN :=
  div_nonneg (E.cp.br_nonneg _) (E.cp.br_pos E.Pp_pos).le

lemma alphaTildeN_eq_zero (hp : E.alphaP ≤ 0) : E.alphaTildeN = 0 := by
  unfold alphaTildeN
  rw [max_eq_right hp, zero_mul, E.cp.br_eq_zero_of_nonpos le_rfl, zero_div]

/-- **Equivalence in (B.8), strict form.** The agent's effort is strictly higher under
centralization iff `α_a^n > α̃^n`, with no exception. -/
theorem effort_lt_iff_alpha {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc)
    (hd : E.IsEq .del ad pd) : ad < ac ↔ E.alphaTildeN < E.alphaA := by
  rw [E.effort_lt_iff hc hd]
  constructor
  · intro h
    rcases le_or_gt E.alphaA 0 with ha | ha
    · rw [max_eq_left ha] at h; linarith [E.alphaTildeN_nonneg]
    · rwa [max_eq_right ha.le] at h
  · intro h; exact h.trans_le (le_max_right _ _)

/-- When `α_a^n ≤ 0` and `α_p^n ≤ 0`, the agent exerts no effort in either regime. -/
theorem ea_zero_of_nonpos (ha : E.alphaA ≤ 0) (hp : E.alphaP ≤ 0) :
    E.ea .cen = 0 ∧ E.ea .del = 0 := by
  constructor
  · rw [E.ea_cen_eq, max_eq_left ha, zero_mul, mul_zero, E.ca.br_eq_zero_of_nonpos le_rfl]
  · rw [E.ea_del_eq, E.ep_del_eq, max_eq_right hp, zero_mul, E.cp.br_eq_zero_of_nonpos le_rfl,
      zero_mul, E.ca.br_eq_zero_of_nonpos le_rfl]

/-- With `α_a^n ≤ 0`, the agent exerts no effort under centralization whatever the principal's
effort, so his effort is constant (rather than strictly decreasing) in it. -/
theorem ea_cen_zero (ha : E.alphaA ≤ 0) {p a : ℝ} (hp : 0 ≤ p) (h : IsBR (E.Ua .cen p) a) :
    a = 0 := by
  rw [E.isBR_Ua_iff] at h
  rw [h]
  apply E.ca.br_eq_zero_of_nonpos
  unfold Va
  show p * E.Ya ≤ 0
  rw [E.Ya_eq]
  exact mul_nonpos_of_nonneg_of_nonpos hp (mul_nonpos_of_nonpos_of_nonneg ha E.Pa_pos.le)

/-- **Analogue of Proposition 3(c), second part, strict.** If `α_p^n ≤ 0 < α_a^n`, the agent's
effort is strictly higher under centralization. -/
theorem prop3c_pos_analogue_strict (hp : E.alphaP ≤ 0) (ha : 0 < E.alphaA)
    {ac pc ad pd : ℝ} (hc : E.IsEq .cen ac pc) (hd : E.IsEq .del ad pd) : ad < ac := by
  rw [E.effort_lt_iff_alpha hc hd, E.alphaTildeN_eq_zero hp]
  exact ha

/-- At `α_a^n ≤ 0`, if `μ_g` is the unique minimiser of `g`, then `μ* = {μ_g}`. -/
theorem muStar_eq_singleton (hα : E.alphaA ≤ 0) {g : ℝ → ℝ} {μg : ℝ} (hμg : 0 < μg)
    (huniq : ∀ μ, 0 < μ → μ ≠ μg → g μg < g μ) : E.muStar g = {μg} := by
  ext μ
  rw [E.mem_muStar_iff hα g, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hμ, hmin⟩
    by_contra hne
    have h1 := huniq μ hμ hne
    have h2 := hmin μg hμg
    linarith
  · intro h
    rw [h]
    refine ⟨hμg, fun μ' hμ' => ?_⟩
    rcases eq_or_ne μ' μg with h' | h'
    · rw [h']
    · exact (huniq μ' hμ' h').le

/-- `(v_a, v_p) = (1, 1)` w.p. `1/4`, `(1, -3)` w.p. `1/4`, `(-3, -1)` w.p. `1/2`: negative
expected values, `α_a^n = 1/2` and `α_p^n = -2`. -/
noncomputable def ED : EnvN :=
  mkN ![1/4, 1/4, 1/2] ![(1, 1), (1, -3), (-3, -1)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three, Set.indicator])
    (by norm_num [Fin.sum_univ_three, Set.indicator])
    (by norm_num [Fin.sum_univ_three, Set.indicator, Cost.quad])
    (by norm_num [Fin.sum_univ_three, Set.indicator, Cost.quad])

lemma ED_integral (f : ℝ × ℝ → ℝ) :
    ∫ v, f v ∂ED.F = 1 / 4 * f (1, 1) + 1 / 4 * f (1, -3) + 1 / 2 * f (-3, -1) := by
  show ∫ v, f v ∂(discMeasure ![1/4, 1/4, 1/2] ![(1, 1), (1, -3), (-3, -1)]) = _
  rw [disc_integral _ _ (by intro i; fin_cases i <;> norm_num), Fin.sum_univ_three]
  simp

lemma ED_alphaA : ED.alphaA = 1 / 2 := by
  rw [alphaA]
  norm_num [Ya, Pa, EI, ED_integral, Set.indicator, Regime.dm]

lemma ED_alphaP : ED.alphaP = -2 := by
  rw [alphaP]
  norm_num [Yp, Pp, EI, ED_integral, Set.indicator, Regime.dm]

theorem nonvacuous_prop3c_pos_analogue_strict :
    ∃ E : EnvN, E.alphaP ≤ 0 ∧ 0 < E.alphaA ∧ E.ea .del < E.ea .cen := by
  have hp : ED.alphaP ≤ 0 := by rw [ED_alphaP]; norm_num
  have ha : 0 < ED.alphaA := by rw [ED_alphaA]; norm_num
  exact ⟨ED, hp, ha, ED.prop3c_pos_analogue_strict hp ha (ED.isEq_eq .cen) (ED.isEq_eq .del)⟩

theorem nonvacuous_ea_zero_of_nonpos :
    ∃ E : EnvN, E.alphaA ≤ 0 ∧ E.alphaP ≤ 0 ∧ E.ea .cen = 0 ∧ E.ea .del = 0 := by
  have ha : EN.alphaA ≤ 0 := by rw [EN_alphaA]; norm_num
  have hp : EN.alphaP ≤ 0 := by rw [EN_alphaP]; norm_num
  exact ⟨EN, ha, hp, EN.ea_zero_of_nonpos ha hp⟩

lemma g6_unique {μ : ℝ} (hne : μ ≠ 1) : g6 1 < g6 μ := by
  have h : μ - 1 ≠ 0 := sub_ne_zero.2 hne
  have h1 : 0 < (μ - 1) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))
  have h2 : 0 ≤ (μ⁻¹ - 1) ^ 2 := sq_nonneg _
  unfold g6
  norm_num
  linarith

theorem nonvacuous_muStar_eq_singleton :
    ∃ (E : EnvN) (g : ℝ → ℝ) (μg : ℝ), E.alphaA = 0 ∧ 0 < μg ∧
      (∀ μ, 0 < μ → μ ≠ μg → g μg < g μ) ∧ E.muStar g = {μg} :=
  ⟨EZ, g6, 1, EZ_alphaA, one_pos, fun _ _ hne => g6_unique hne,
    EZ.muStar_eq_singleton EZ_alphaA.le one_pos fun _ _ hne => g6_unique hne⟩

end EnvN

end MI
