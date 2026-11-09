import ManagerialIntervention.Counterexamples

/-!
# Non-vacuity

For each result, a concrete environment in which all of its hypotheses hold, together with
the conclusion the result then delivers.

`E4` is the symmetric distribution `(2,-1)` w.p. `1/8`, `(-1,2)` w.p. `1/8`, `(-1,-1)` w.p.
`3/8`, `(2,2)` w.p. `3/8`, with `α_a = α_p = 1/4`.  Combined with a principal cost whose `h`
is linear, strictly convex or strictly concave, it illustrates all of Proposition 3(a)–(b).
-/

namespace MI

open Set Filter Topology

/-! ### A cost with strictly convex `h` -/

/-- `c(e) = e² - e³/3`, with `c'(e) = 2e - e²` and `h(m) = 1 - √(1-m)` strictly convex. -/
noncomputable def cvx : Cost where
  c e := e ^ 2 - e ^ 3 / 3
  d e := 2 * e - e ^ 2
  hasDerivAt x := by
    have := (hasDerivAt_pow 2 x).sub ((hasDerivAt_pow 3 x).div_const 3)
    convert this using 1
    push_cast
    ring
  c_zero := by simp
  d_zero := by simp
  d_strictMonoOn := fun x hx y hy h => by
    show 2 * x - x ^ 2 < 2 * y - y ^ 2
    nlinarith [hx.1, hy.2]

lemma cvx_d_one : cvx.d 1 = 1 := by show 2 * (1 : ℝ) - 1 ^ 2 = 1; norm_num

lemma cvx_br {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) : cvx.br m = 1 - Real.sqrt (1 - m) := by
  have h1 : 0 ≤ 1 - m := by linarith [hm.2]
  have hs : 1 - Real.sqrt (1 - m) ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [Real.sqrt_le_one.mpr (show 1 - m ≤ 1 by linarith [hm.1])],
      by linarith [Real.sqrt_nonneg (1 - m)]⟩
  have := cvx.br_d hs
  have hd : cvx.d (1 - Real.sqrt (1 - m)) = m := by
    show 2 * (1 - Real.sqrt (1 - m)) - (1 - Real.sqrt (1 - m)) ^ 2 = m
    have := Real.sq_sqrt h1
    nlinarith
  rwa [hd] at this

lemma cvx_strictConvex : StrictConvexOn ℝ (Icc 0 (cvx.d 1)) cvx.br := by
  rw [cvx_d_one]
  have hsq := Real.strictConcaveOn_sqrt
  refine ⟨convex_Icc 0 1, fun a ha b hb hab s t hs ht hst => ?_⟩
  rw [cvx_br ha, cvx_br hb, cvx_br ((convex_Icc (0 : ℝ) 1) ha hb hs.le ht.le hst)]
  have ha' : 1 - a ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith [ha.2]
  have hb' : 1 - b ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith [hb.2]
  have hne : 1 - a ≠ 1 - b := fun h => hab (by linarith)
  have key := hsq.2 ha' hb' hne hs ht hst
  simp only [smul_eq_mul] at key ⊢
  have e : s * (1 - a) + t * (1 - b) = 1 - (s * a + t * b) := by
    have : s + t = 1 := hst
    nlinarith
  rw [e] at key
  nlinarith

/-! ### The symmetric environment `E4` -/

/-- `E4` with principal cost `cp`. -/
noncomputable def E4 (cp : Cost) (hcp : (1 : ℝ) / 2 ≤ cp.d 1) : Env :=
  mkEnv ![1/8, 1/8, 3/8, 3/8] ![(2, -1), (-1, 2), (-1, -1), (2, 2)] cq2 cp
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by simp [Fin.sum_univ_four, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_four, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_four, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_four, Set.indicator]; norm_num; linarith)

section E4

variable (cp : Cost) (hcp : (1 : ℝ) / 2 ≤ cp.d 1)

lemma E4_Na : (E4 cp hcp).Na = -1 / 2 := by
  simp [Env.Na, E4, mkEnv_integral, Fin.sum_univ_four, Set.indicator]; norm_num
lemma E4_Np : (E4 cp hcp).Np = -1 / 2 := by
  simp [Env.Np, E4, mkEnv_integral, Fin.sum_univ_four, Set.indicator]; norm_num
lemma E4_Xa : (E4 cp hcp).Xa = -1 / 8 := by
  simp [Env.Xa, E4, mkEnv_integral, Fin.sum_univ_four, Set.indicator]; norm_num
lemma E4_Xp : (E4 cp hcp).Xp = -1 / 8 := by
  simp [Env.Xp, E4, mkEnv_integral, Fin.sum_univ_four, Set.indicator]; norm_num
lemma E4_alphaA : (E4 cp hcp).alphaA = 1 / 4 := by
  rw [Env.alphaA, E4_Xa, E4_Na]; norm_num
lemma E4_alphaP : (E4 cp hcp).alphaP = 1 / 4 := by
  rw [Env.alphaP, E4_Xp, E4_Np]; norm_num

end E4

/-! ### Proposition 3 -/

/-- Proposition 3(a) applies (linear `h`, `α_p > 0`). -/
theorem nonvacuous_prop3a :
    ∃ E : Env, (∃ k b : ℝ, ∀ x ∈ Icc 0 (E.cp.d 1), E.cp.br x = k * x + b) ∧ 0 < E.alphaP ∧
      E.ea .del ≤ E.ea .cen := by
  let E := E4 cq1 (by simp [Cost.quad]; norm_num)
  have hl : ∃ k b : ℝ, ∀ x ∈ Icc 0 (E.cp.d 1), E.cp.br x = k * x + b := quad_linear one_pos
  have hp : 0 < E.alphaP := by rw [E4_alphaP]; norm_num
  refine ⟨E, hl, hp, ?_⟩
  rw [E.prop3a hl hp (E.isEq_eq .cen) (E.isEq_eq .del), E4_alphaA, E4_alphaP]

/-- Proposition 3(b), convex case, applies: effort is strictly higher under centralization. -/
theorem nonvacuous_prop3b_convex :
    ∃ E : Env, StrictConvexOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br ∧ E.alphaA = E.alphaP ∧
      0 < E.alphaP ∧ E.alphaP < 1 ∧ E.ea .del < E.ea .cen := by
  let E := E4 cvx (by rw [cvx_d_one]; norm_num)
  have h1 : E.alphaA = E.alphaP := by rw [E4_alphaA, E4_alphaP]
  have h2 : 0 < E.alphaP := by rw [E4_alphaP]; norm_num
  have h3 : E.alphaP < 1 := by rw [E4_alphaP]; norm_num
  exact ⟨E, cvx_strictConvex, h1, h2, h3,
    E.prop3b_convex_strict cvx_strictConvex h1 h2 h3 (E.isEq_eq .cen) (E.isEq_eq .del)⟩

/-- Proposition 3(b), concave case, applies: effort is strictly lower under centralization. -/
theorem nonvacuous_prop3b_concave :
    ∃ E : Env, StrictConcaveOn ℝ (Icc 0 (E.cp.d 1)) E.cp.br ∧ E.alphaA = E.alphaP ∧
      0 < E.alphaP ∧ E.alphaP < 1 ∧ E.ea .cen < E.ea .del := by
  let E := E4 cube (by rw [cube_d_one]; norm_num)
  have h1 : E.alphaA = E.alphaP := by rw [E4_alphaA, E4_alphaP]
  have h2 : 0 < E.alphaP := by rw [E4_alphaP]; norm_num
  have h3 : E.alphaP < 1 := by rw [E4_alphaP]; norm_num
  exact ⟨E, cube_strictConcave, h1, h2, h3,
    E.prop3b_concave_strict cube_strictConcave h1 h2 h3 (E.isEq_eq .cen) (E.isEq_eq .del)⟩

/-- Proposition 3(c), first part, applies (`α_a < 0`). -/
theorem nonvacuous_prop3c_neg : ∃ E : Env, E.alphaA < 0 ∧ E.ea .cen < E.ea .del := by
  have h : E1.alphaA < 0 := by rw [E1_alphaA]; norm_num
  exact ⟨E1, h, E1.prop3c_neg h (E1.isEq_eq .cen) (E1.isEq_eq .del)⟩

/-- Proposition 3(c), second part, applies (`α_p < 0 ≤ α_a`). -/
theorem nonvacuous_prop3c_pos :
    ∃ E : Env, E.alphaP < 0 ∧ 0 ≤ E.alphaA ∧ E.ea .del ≤ E.ea .cen := by
  have hp : E5.alphaP < 0 := by rw [E5_alphaP]; norm_num
  have ha : 0 ≤ E5.alphaA := by rw [E5_alphaA]; norm_num
  exact ⟨E5, hp, ha, E5.prop3c_pos hp ha (E5.isEq_eq .cen) (E5.isEq_eq .del)⟩

/-! ### Propositions 4 and B.1 -/

/-- Proposition 4 applies to `E1`: the principal centralizes iff `α_a > α̂(α_p)`. -/
theorem nonvacuous_prop4 :
    ∃ (E : Env) (αhat : ℝ → ℝ), Monotone αhat ∧
      (∀ x < 1, αhat x < alphaTilde E.cp E.Np x) ∧
      (E.ea .del * E.Up .del (E.ep .del) < E.ea .cen * E.Up .cen (E.ep .cen) ↔
        αhat E.alphaP < E.alphaA) := by
  obtain ⟨αhat, hm, hlt, -, hiff⟩ := prop4 E1.prim E1.prim_valid
  exact ⟨E1, αhat, hm, hlt, hiff E1 rfl _ _ _ _ (E1.isEq_eq .cen) (E1.isEq_eq .del)⟩

/-- Proposition B.1 applies to `E1`. -/
theorem nonvacuous_propB1 :
    ∃ (E : Env) (αhat : ℝ → ℝ), Monotone αhat ∧
      (∀ x < 1, αhat x < alphaTilde E.cp E.Np x) ∧
      (E.Ua .del (E.ep .del) (E.ea .del) + E.ea .del * E.Up .del (E.ep .del) <
          E.Ua .cen (E.ep .cen) (E.ea .cen) + E.ea .cen * E.Up .cen (E.ep .cen) ↔
        αhat E.alphaP < E.alphaA) := by
  obtain ⟨αhat, hm, hlt, -, hiff⟩ := propB1_contractible E1.prim E1.prim_valid
  exact ⟨E1, αhat, hm, hlt, hiff E1 rfl _ _ _ _ (E1.isEq_eq .cen) (E1.isEq_eq .del)⟩

/-! ### Propositions 5 and 6 -/

/-- The involvement cost `g(μ) = (μ - 1)² + (1/μ - 1)²`, minimised at `μ_g = 1`. -/
noncomputable def g6 (μ : ℝ) : ℝ := (μ - 1) ^ 2 + (μ⁻¹ - 1) ^ 2

lemma g6_min {μ : ℝ} (_ : 0 < μ) : g6 1 ≤ g6 μ := by
  unfold g6; norm_num; positivity

lemma g6_diff : DifferentiableAt ℝ g6 1 := by
  unfold g6
  have : DifferentiableAt ℝ (fun μ : ℝ => μ⁻¹) 1 := differentiableAt_inv (by norm_num)
  fun_prop

lemma g6_cont : ContinuousOn g6 (Ioi 0) := by
  unfold g6
  have : ContinuousOn (fun μ : ℝ => μ⁻¹) (Ioi 0) :=
    continuousOn_inv₀.mono fun x (hx : 0 < x) => hx.ne'
  fun_prop

lemma sq_sub_one_ge (y : ℝ) : y + -2 ≤ (y - 1) ^ 2 := by nlinarith [sq_nonneg (y - 3 / 2)]

lemma g6_tendsto_zero : Tendsto g6 (𝓝[>] 0) atTop :=
  tendsto_atTop_mono' _ (Eventually.of_forall fun μ => by
      unfold g6; have := sq_sub_one_ge μ⁻¹; nlinarith [sq_nonneg (μ - 1)])
    (tendsto_atTop_add_const_right _ (-2) tendsto_inv_nhdsGT_zero)

lemma g6_tendsto_top : Tendsto g6 atTop atTop :=
  tendsto_atTop_mono' _ (Eventually.of_forall fun μ => by
      unfold g6; have := sq_sub_one_ge μ; simp only [id]; nlinarith [sq_nonneg (μ⁻¹ - 1)])
    (tendsto_atTop_add_const_right _ (-2) tendsto_id)

/-- Proposition 6 applies to `E6` (`α_a = 0`) with `g = g6`: `μ*(0)` is non-empty and every
element exceeds `μ_g = 1`. -/
theorem nonvacuous_prop6 :
    ∃ (E : Env) (g : ℝ → ℝ) (μg : ℝ), E.alphaA = 0 ∧ 0 < μg ∧ (∀ μ, 0 < μ → g μg ≤ g μ) ∧
      DifferentiableAt ℝ g μg ∧ (E.muStar g).Nonempty ∧ ∀ μ ∈ E.muStar g, μg < μ :=
  ⟨E6, g6, 1, E6_alphaA, one_pos, fun _ hμ => g6_min hμ, g6_diff,
    E6.muStar_nonempty g6_cont g6_tendsto_zero g6_tendsto_top,
    E6.prop6 E6_alphaA one_pos (fun _ hμ => g6_min hμ) g6_diff⟩

/-- The hypotheses of the corrected Proposition 5 can hold (`E3`, quadratic `c_a`,
`α_a = 1`), and `μ*` is then non-empty. -/
theorem nonvacuous_prop5 :
    ∃ (E : Env) (g : ℝ → ℝ), ConvexOn ℝ (Icc 0 (E.ca.d 1)) E.ca.br ∧
      (∃ k b : ℝ, ∀ x ∈ Icc 0 (E.ca.d 1), E.ca.br x = k * x + b) ∧
      0 ≤ E.alphaA ∧ E.A / E.Na ≤ E.alphaA ∧ (E.muStar g).Nonempty ∧
      SSOle (E.muStar g) (E.muStar g) := by
  refine ⟨E3q, g6, quad_convex (by norm_num), quad_linear (by norm_num),
    by rw [E3_alphaA]; norm_num, ?_, E3q.muStar_nonempty g6_cont g6_tendsto_zero g6_tendsto_top,
    E3q.prop5_convex E3q rfl g6 (quad_convex (by norm_num)) (by rw [E3_alphaA]; norm_num) le_rfl⟩
  rw [E3_alphaA, E3_A, E3_Na]; norm_num

end MI
