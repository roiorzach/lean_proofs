import ManagerialIntervention.Extensions

/-!
# Proposition 5 under the curvature condition `α_a · h_a'' ≥ 0`

The agent's marginal benefit under centralization is
`m = E(v_a) - α_a E(v_a 1_{v_a<0}) e_p^c(μ)`, which lies above `E(v_a)` exactly when `α_a > 0`.
So "`α_a · h_a''(m) ≥ 0` at every attainable `m`" means: `h_a = (c_a')⁻¹` is convex above
`E(v_a)` and concave below it.  Together with `E(v_a 1_{v_p ≥ 0}) ≥ 0` (the agent never stops
working, i.e. no truncation at zero in (A Effort: Centralization)), this gives Proposition 5.

* `MI.Env.prop5_general` — the pairwise statement.  For `α_a ≤ α_a'`:
  - if `α_a ≤ 0 ≤ α_a'`, nothing beyond the model's assumptions is needed;
  - if `0 < α_a`, `h_a` must be convex on `[E(v_a), c_a'(1)]`;
  - if `α_a' < 0`, `h_a` must be concave on `[0, E(v_a)]` and `E(v_a 1_{v_p≥0}) ≥ 0`.
* `MI.Env.prop5_curvature` — the clean form: `h_a` concave below `E(v_a)` and convex above,
  and `E(v_a 1_{v_p≥0}) ≥ 0`.  It contains `MI.Env.prop5_convex` and `MI.Env.prop5_linear`.
* `MI.Env.prop5_straddle` — a non-negatively aligned agent always faces weakly more
  involvement than a negatively aligned one, with no curvature assumption.
* `MI.prop5_counterexample_smooth` — Proposition 5 fails even with the smooth cost
  `g(μ) = (μ-1)² + (1/μ-1)²` of Proposition 6's form: in the two environments of
  `MI.prop5_counterexample`, the less aligned agent (`α_a = -3/2`) gets the status quo
  `μ* = {μ_g}` and exerts no effort, while the more aligned one (`α_a = -1`) gets a hands-off
  manager (`μ* < μ_g`).  Here `E(v_a 1_{v_p≥0}) < 0`, so `MI.Env.prop5_curvature` does not apply.
* `MI.EnvN.mem_muStar_iff`, `MI.EnvN.prop6_analogue_fails` — Appendix B.1 with informal
  delegation: if `α_a^n ≤ 0`, the agent exerts no effort under centralization for any `μ`,
  so `μ*` is the set of minimisers of `g`; at `α_a^n = 0` this contains `μ_g`, so the analogue
  of Proposition 6 fails.
* `MI.nonvacuous_prop5_curvature` — `E7` (`α_a = -2`) and `E8` (`α_a = -1`) share their
  primitives and satisfy the hypotheses of `MI.Env.prop5_curvature`, so the curvature version
  covers negative alignments that `MI.Env.prop5_convex` does not.
-/

namespace MI

open Set Filter Topology

/-- For a concave `f`, increments over intervals of a fixed length decrease to the right. -/
lemma concave_incr {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) {a b L : ℝ} (hab : a ≤ b)
    (hL : 0 ≤ L) (ha : a ∈ s) (hbL : b + L ∈ s) : f (b + L) - f b ≤ f (a + L) - f a := by
  have h := convex_incr (f := -f) hf.neg hab hL ha hbL
  simp only [Pi.neg_apply] at h
  linarith

/-! ### Increasing differences in reduced form -/

namespace Prim

variable {π : Prim}

/-- With `α ≤ 0`, the agent's effort is decreasing in involvement. -/
lemma eMu_anti_mu (hπ : π.Valid) {α : ℝ} (hα : α ≤ 0) {μ μ' : ℝ} (h : μ ≤ μ') :
    π.eMu α μ' ≤ π.eMu α μ := by
  apply π.ca.br_mono
  have := pMu_mono hπ h
  have h2 : 0 ≤ (-α) * (π.pMu μ' - π.pMu μ) * -π.Na :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith [hπ.Na_neg])
  nlinarith

/-- Increasing differences for `α ≤ 0 ≤ α'`, with no curvature assumption. -/
lemma ID_straddle (hπ : π.Valid) {α α' : ℝ} (hα : α ≤ 0) (hα' : 0 ≤ α') {μ μ' : ℝ}
    (hμ : 0 < μ) (hμμ : μ ≤ μ') : π.FMu α' μ - π.FMu α μ ≤ π.FMu α' μ' - π.FMu α μ' := by
  apply ID_of hπ hμ hμμ _ (hα.trans hα')
  have h1 := eMu_mono_mu hπ hα' hμμ
  have h2 := eMu_anti_mu hπ hα hμμ
  linarith

/-- Increasing differences for `0 ≤ α ≤ α'` when `h_a` is convex above `E(v_a)`. -/
lemma ID_convex_above (hπ : π.Valid) (hB : π.Bounded)
    (hcv : ConvexOn ℝ (Icc π.A (π.ca.d 1)) π.ca.br)
    {α α' : ℝ} (h0 : 0 ≤ α) (hαα : α ≤ α') (h1 : α' ≤ 1) {μ μ' : ℝ} (hμ : 0 < μ)
    (hμμ : μ ≤ μ') : π.FMu α' μ - π.FMu α μ ≤ π.FMu α' μ' - π.FMu α μ' := by
  apply ID_of hπ hμ hμμ _ hαα
  have hp := pMu_mono hπ hμμ
  have hp0 := (pMu_mem (π := π) μ).1
  have hp1 := (pMu_mem (π := π) μ').2
  have hN := hπ.Na_neg
  set p := π.pMu μ
  set p' := π.pMu μ'
  set x := π.A - α * p * π.Na
  set x' := π.A - α * p' * π.Na
  set L := -((α' - α) * p * π.Na)
  set L' := -((α' - α) * p' * π.Na)
  have hxx : x ≤ x' := by
    have : 0 ≤ α * (p' - p) * -π.Na := mul_nonneg (mul_nonneg h0 (by linarith)) (by linarith)
    simp only [x, x']; nlinarith
  have hL : 0 ≤ L := by
    simp only [L]
    have : 0 ≤ (α' - α) * p * -π.Na := mul_nonneg (mul_nonneg (by linarith) hp0) (by linarith)
    linarith
  have hLL : L ≤ L' := by
    simp only [L, L']
    have : 0 ≤ (α' - α) * (p' - p) * -π.Na :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have hxA : π.A ≤ x := by
    have : 0 ≤ α * p * -π.Na := mul_nonneg (mul_nonneg h0 hp0) (by linarith)
    simp only [x]; linarith
  have hxL' : x' + L' ≤ π.ca.d 1 := by
    have : x' + L' = π.A - α' * p' * π.Na := by simp only [x', L']; ring
    rw [this]
    have hαp : α' * p' ≤ 1 := by nlinarith
    unfold Bounded at hB
    nlinarith
  have e1 : π.eMu α' μ = π.ca.br (x + L) := by
    unfold eMu; congr 1; simp only [x, L, p]; ring
  have e2 : π.eMu α' μ' = π.ca.br (x' + L') := by
    unfold eMu; congr 1; simp only [x', L', p']; ring
  have e3 : π.eMu α μ = π.ca.br x := rfl
  have e4 : π.eMu α μ' = π.ca.br x' := rfl
  rw [e1, e2, e3, e4]
  have i1 := convex_incr hcv hxx hL ⟨hxA, by linarith⟩ ⟨by linarith, by linarith⟩
  have i2 := π.ca.br_mono (show x' + L ≤ x' + L' by linarith)
  linarith

/-- Increasing differences for `α ≤ α' ≤ 0` when `h_a` is concave below `E(v_a)` and the agent
never stops working (`α ≥ E(v_a)/E(v_a 1_{v_a<0})`). -/
lemma ID_concave (hπ : π.Valid) (hcc : ConcaveOn ℝ (Icc 0 π.A) π.ca.br)
    {α α' : ℝ} (h0 : π.A / π.Na ≤ α) (hαα : α ≤ α') (h1 : α' ≤ 0) {μ μ' : ℝ} (hμ : 0 < μ)
    (hμμ : μ ≤ μ') : π.FMu α' μ - π.FMu α μ ≤ π.FMu α' μ' - π.FMu α μ' := by
  apply ID_of hπ hμ hμμ _ hαα
  have hp := pMu_mono hπ hμμ
  have hp0 := (pMu_mem (π := π) μ).1
  have hp1 := (pMu_mem (π := π) μ).2
  have hp1' := (pMu_mem (π := π) μ').2
  have hN := hπ.Na_neg
  have hαN : α * π.Na ≤ π.A := by
    have := (div_le_iff_of_neg hN).1 h0
    linarith
  set p := π.pMu μ
  set p' := π.pMu μ'
  set a := π.A - α * p * π.Na
  set c := π.A - α * p' * π.Na
  set L := -((α' - α) * p * π.Na)
  set L' := -((α' - α) * p' * π.Na)
  have hca : c ≤ a := by
    have : 0 ≤ (-α) * (p' - p) * -π.Na :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    simp only [a, c]; nlinarith
  have hL : 0 ≤ L := by
    simp only [L]
    have : 0 ≤ (α' - α) * p * -π.Na := mul_nonneg (mul_nonneg (by linarith) hp0) (by linarith)
    linarith
  have hLL : L ≤ L' := by
    simp only [L, L']
    have : 0 ≤ (α' - α) * (p' - p) * -π.Na :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have hc0 : 0 ≤ c := by
    have : 0 ≤ (-α) * (1 - p') * -π.Na :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    simp only [c]; nlinarith
  have hcA : c ≤ π.A := by
    have : 0 ≤ (-α) * p' * -π.Na :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    simp only [c]; nlinarith
  have hb : a + L = π.A - α' * p * π.Na := by simp only [a, L]; ring
  have hb0 : 0 ≤ a + L := by
    rw [hb]
    have h2 : 0 ≤ (-α') * (1 - p) * -π.Na :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have h3 : 0 ≤ (α' - α) * -π.Na := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hbA : a + L ≤ π.A := by
    rw [hb]
    have : 0 ≤ (-α') * p * -π.Na := mul_nonneg (mul_nonneg (by linarith) hp0) (by linarith)
    nlinarith
  have e1 : π.eMu α' μ = π.ca.br (a + L) := by
    unfold eMu; congr 1; simp only [a, L, p]; ring
  have e2 : π.eMu α' μ' = π.ca.br (c + L') := by
    unfold eMu; congr 1; simp only [c, L', p']; ring
  have e3 : π.eMu α μ = π.ca.br a := rfl
  have e4 : π.eMu α μ' = π.ca.br c := rfl
  rw [e1, e2, e3, e4]
  have i1 := concave_incr hcc hca hL ⟨hc0, hcA⟩ ⟨hb0, hbA⟩
  have i2 := π.ca.br_mono (show c + L ≤ c + L' by linarith)
  linarith

/-- Increasing differences for any `α ≤ α' ≤ 1` under the curvature condition
`α · h_a'' ≥ 0`, split by the signs of `α` and `α'`. -/
lemma ID_general (hπ : π.Valid) (hB : π.Bounded) {α α' : ℝ} (hαα : α ≤ α') (h1 : α' ≤ 1)
    (hcv : 0 < α → ConvexOn ℝ (Icc π.A (π.ca.d 1)) π.ca.br)
    (hcc : α' < 0 → ConcaveOn ℝ (Icc 0 π.A) π.ca.br ∧ π.A / π.Na ≤ α)
    {μ μ' : ℝ} (hμ : 0 < μ) (hμμ : μ ≤ μ') :
    π.FMu α' μ - π.FMu α μ ≤ π.FMu α' μ' - π.FMu α μ' := by
  rcases le_or_gt α 0 with hα | hα
  · rcases le_or_gt 0 α' with hα' | hα'
    · exact ID_straddle hπ hα hα' hμ hμμ
    · obtain ⟨hc, h0⟩ := hcc hα'
      exact ID_concave hπ hc h0 hαα hα'.le hμ hμμ
  · exact ID_convex_above hπ hB (hcv hα) hα.le hαα h1 hμ hμμ

/-- Proposition 5 in reduced form under the curvature condition. -/
theorem muStar_sso_general (hπ : π.Valid) (hB : π.Bounded) (g : ℝ → ℝ) {α α' : ℝ}
    (hαα : α ≤ α') (h1 : α' ≤ 1)
    (hcv : 0 < α → ConvexOn ℝ (Icc π.A (π.ca.d 1)) π.ca.br)
    (hcc : α' < 0 → ConcaveOn ℝ (Icc 0 π.A) π.ca.br ∧ π.A / π.Na ≤ α) :
    SSOle (π.muStar g α) (π.muStar g α') :=
  sso_of_ID g fun _ _ hμ hμμ => ID_general hπ hB hαα h1 hcv hcc hμ hμμ

end Prim

/-! ### Proposition 5 in an environment -/

namespace Env

variable (E : Env)

/-- `α_a ≥ E(v_a)/E(v_a 1_{v_a<0})` says exactly that `E(v_a 1_{v_p≥0}) ≥ 0`: the agent gains,
on average, from the ideas an informed principal approves, so he never stops working. -/
lemma noquit_iff : E.A / E.Na ≤ E.alphaA ↔ 0 ≤ E.EI .cen (fun v => v.1) := by
  rw [E.EI_cen_a, E.Xa_eq, div_le_iff_of_neg E.Na_neg]
  constructor <;> intro h <;> linarith

/-- The agent's equilibrium effort under informal delegation, in reduced form. -/
lemma eaMu_eq (μ : ℝ) : E.eaMu μ = E.prim.eMu E.alphaA μ := by
  unfold eaMu epMu Prim.eMu Prim.pMu
  rw [E.Va_cen, E.Xa_eq]
  simp only [prim]
  congr 1
  ring

/-- **Proposition 5, pairwise form.** Fix the primitives `(E(v_a), E(v_p), E(v_a 1_{v_a<0}),
E(v_p 1_{v_p<0}), c_a, c_p)` and `g`, and let `α_a ≤ α_a'`.  Then `μ*(α_a) ≤ μ*(α_a')` in the
strong set order provided
* `h_a` is convex on `[E(v_a), c_a'(1)]` if `α_a > 0`, and
* `h_a` is concave on `[0, E(v_a)]` and `E(v_a 1_{v_p≥0}) ≥ 0` (for the less aligned
  environment) if `α_a' < 0`.
Nothing more is needed when `α_a ≤ 0 ≤ α_a'`. -/
theorem prop5_general (E' : Env) (hprim : E'.prim = E.prim) (g : ℝ → ℝ)
    (hle : E.alphaA ≤ E'.alphaA)
    (hcv : 0 < E.alphaA → ConvexOn ℝ (Icc E.A (E.ca.d 1)) E.ca.br)
    (hcc : E'.alphaA < 0 →
      ConcaveOn ℝ (Icc 0 E.A) E.ca.br ∧ 0 ≤ E.EI .cen (fun v => v.1)) :
    SSOle (E.muStar g) (E'.muStar g) := by
  rw [E.muStar_eq, E'.muStar_eq, hprim]
  refine Prim.muStar_sso_general E.prim_valid E.prim_bounded g hle E'.alphaA_le_one hcv
    fun h => ?_
  obtain ⟨hc, hq⟩ := hcc h
  exact ⟨hc, E.noquit_iff.2 hq⟩

/-- **Proposition 5 under `α_a h_a'' ≥ 0`.** If `h_a = (c_a')⁻¹` is concave on `[0, E(v_a)]` and
convex on `[E(v_a), c_a'(1)]`, then, holding the primitives and `g` fixed, `μ*(α_a)` is weakly
increasing in the strong set order over all alignments with `E(v_a 1_{v_p≥0}) ≥ 0`
(equivalently `α_a ≥ E(v_a)/E(v_a 1_{v_a<0})`). -/
theorem prop5_curvature (E' : Env) (hprim : E'.prim = E.prim) (g : ℝ → ℝ)
    (hcc : ConcaveOn ℝ (Icc 0 E.A) E.ca.br) (hcv : ConvexOn ℝ (Icc E.A (E.ca.d 1)) E.ca.br)
    (hq : 0 ≤ E.EI .cen (fun v => v.1)) (hle : E.alphaA ≤ E'.alphaA) :
    SSOle (E.muStar g) (E'.muStar g) :=
  E.prop5_general E' hprim g hle (fun _ => hcv) (fun _ => ⟨hcc, hq⟩)

/-- **Proposition 5 across the sign of alignment.** With no curvature assumption, if
`α_a ≤ 0 ≤ α_a'` then `μ*(α_a) ≤ μ*(α_a')` in the strong set order. -/
theorem prop5_straddle (E' : Env) (hprim : E'.prim = E.prim) (g : ℝ → ℝ)
    (h0 : E.alphaA ≤ 0) (h0' : 0 ≤ E'.alphaA) : SSOle (E.muStar g) (E'.muStar g) :=
  E.prop5_general E' hprim g (h0.trans h0') (fun h => absurd h (not_lt.2 h0))
    (fun h => absurd h (not_lt.2 h0'))

end Env

/-! ### Proposition 5 fails with a smooth `g` of Proposition 6's form -/

section Smooth

lemma π0_P : π0.P = 1 := E1_P

lemma pMu_half : π0.pMu (1 / 2) = 1 / 4 := by
  unfold Prim.pMu
  rw [π0_Np, π0_cp, Cost.quad_br (by norm_num) (by norm_num)]
  norm_num

lemma pMu_twothirds : π0.pMu (2 / 3) = 1 / 3 := by
  unfold Prim.pMu
  rw [π0_Np, π0_cp, Cost.quad_br (by norm_num) (by norm_num)]
  norm_num

lemma pMu_ninetenths : π0.pMu (9 / 10) = 9 / 20 := by
  unfold Prim.pMu
  rw [π0_Np, π0_cp, Cost.quad_br (by norm_num) (by norm_num)]
  norm_num

/-- At `α_a = -3/2` the agent stops working once `μ ≥ 2/3`. -/
lemma eMu32_zero {μ : ℝ} (hμ : 2 / 3 ≤ μ) : π0.eMu (-3 / 2) μ = 0 := by
  unfold Prim.eMu
  apply Cost.br_eq_zero_of_nonpos
  have hp : 1 / 3 ≤ π0.pMu μ := pMu_twothirds ▸ Prim.pMu_mono π0_valid hμ
  rw [π0_A, π0_Na]
  nlinarith

lemma eMu32_le {μ : ℝ} (hμ : 1 / 2 ≤ μ) : π0.eMu (-3 / 2) μ ≤ 1 / 16 := by
  unfold Prim.eMu
  have hp : 1 / 4 ≤ π0.pMu μ := pMu_half ▸ Prim.pMu_mono π0_valid hμ
  have h : π0.A - -3 / 2 * π0.pMu μ * π0.Na ≤ 1 / 8 := by rw [π0_A, π0_Na]; linarith
  calc _ ≤ π0.ca.br (1 / 8) := π0.ca.br_mono h
    _ = 1 / 16 := by rw [π0_ca, Cost.quad_br (by norm_num) (by norm_num)]; norm_num

lemma eMu_le_quarter {α : ℝ} (hα : α ≤ 0) (μ : ℝ) : π0.eMu α μ ≤ 1 / 4 := by
  unfold Prim.eMu
  have hp := (Prim.pMu_mem (π := π0) μ).1
  have h : π0.A - α * π0.pMu μ * π0.Na ≤ 1 / 2 := by
    rw [π0_A, π0_Na]; nlinarith [mul_nonpos_of_nonpos_of_nonneg hα hp]
  calc _ ≤ π0.ca.br (1 / 2) := π0.ca.br_mono h
    _ = 1 / 4 := by rw [π0_ca, Cost.quad_br (by norm_num) (by norm_num)]; norm_num

lemma eMu_b_nine : π0.eMu (-1) (9 / 10) = 1 / 40 := by
  unfold Prim.eMu
  rw [pMu_ninetenths, π0_A, π0_Na, π0_ca, Cost.quad_br (by norm_num) (by norm_num)]
  norm_num

lemma FMu_le_of {α μ b : ℝ} (hμ : 0 < μ) (he : π0.eMu α μ ≤ b) : π0.FMu α μ ≤ b * (3 / 2) := by
  unfold Prim.FMu
  have hU := Prim.UMu_le π0_valid hμ
  rw [π0_P, π0_Np] at hU
  have hU0 := Prim.UMu_pos π0_valid hμ
  have he0 := Prim.eMu_nonneg (π := π0) α μ
  have hU' : π0.UMu μ ≤ 3 / 2 := by linarith
  calc π0.eMu α μ * π0.UMu μ ≤ b * π0.UMu μ := mul_le_mul_of_nonneg_right he hU0.le
    _ ≤ b * (3 / 2) := mul_le_mul_of_nonneg_left hU' (he0.trans he)

lemma g6_nonneg (μ : ℝ) : 0 ≤ g6 μ := by unfold g6; positivity

/-- At `α_a = -3/2`, every `μ ≠ 1` does strictly worse than the status quo `μ = 1`. -/
lemma obj_a {μ : ℝ} (hμ : 0 < μ) (hne : μ ≠ 1) : π0.FMu (-3 / 2) μ - g6 μ < 0 := by
  have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ.ne'
  have hi0 : 0 < μ⁻¹ := inv_pos.2 hμ
  rcases le_or_gt (2 / 3) μ with h23 | h23
  · have hF : π0.FMu (-3 / 2) μ = 0 := by unfold Prim.FMu; rw [eMu32_zero h23, zero_mul]
    have hsq : 0 < (μ - 1) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
    have := sq_nonneg (μ⁻¹ - 1)
    rw [hF]; unfold g6; linarith
  · rcases le_or_gt μ (1 / 2) with h12 | h12
    · have hF := FMu_le_of hμ (eMu_le_quarter (by norm_num : (-3 / 2 : ℝ) ≤ 0) μ)
      have h2 : 2 ≤ μ⁻¹ := by nlinarith
      have h3 : 1 ≤ (μ⁻¹ - 1) ^ 2 := by nlinarith
      have := sq_nonneg (μ - 1)
      unfold g6; linarith
    · have hF := FMu_le_of hμ (eMu32_le h12.le)
      have h2 : 3 / 2 ≤ μ⁻¹ := by nlinarith
      have h3 : 1 / 4 ≤ (μ⁻¹ - 1) ^ 2 := by nlinarith
      have h4 : 1 / 9 ≤ (μ - 1) ^ 2 := by nlinarith
      unfold g6; linarith

lemma obj_a_one : π0.FMu (-3 / 2) 1 - g6 1 = 0 := by
  unfold Prim.FMu g6; rw [eMu32_zero (by norm_num)]; norm_num

/-- `μ*(-3/2) = {1}`: the least aligned agent gets the status quo. -/
lemma muStar_a_smooth : π0.muStar g6 (-3 / 2) = {1} := by
  ext μ
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hμ, hmax⟩
    by_contra hne
    have h1 : π0.FMu (-3 / 2) 1 - g6 1 ≤ π0.FMu (-3 / 2) μ - g6 μ := hmax 1 one_pos
    have h2 := obj_a hμ hne
    linarith [obj_a_one]
  · rintro rfl
    refine ⟨one_pos, fun μ' hμ' => ?_⟩
    show π0.FMu (-3 / 2) μ' - g6 μ' ≤ π0.FMu (-3 / 2) 1 - g6 1
    rcases eq_or_ne μ' 1 with h | h
    · rw [h]
    · have := obj_a hμ' h
      linarith [obj_a_one]

lemma obj_b_pos : 0 < π0.FMu (-1) (9 / 10) - g6 (9 / 10) := by
  have hU := Prim.UMu_ge_P (π := π0) (by norm_num : (0 : ℝ) < 9 / 10)
  rw [π0_P] at hU
  have hF : 1 / 40 ≤ π0.FMu (-1) (9 / 10) := by
    unfold Prim.FMu; rw [eMu_b_nine]; linarith
  have hg : g6 (9 / 10) = 1 / 100 + 1 / 81 := by unfold g6; norm_num
  rw [hg]; linarith

lemma obj_b_le {μ : ℝ} (hμ : 1 ≤ μ) : π0.FMu (-1) μ - g6 μ ≤ 0 := by
  have hF : π0.FMu (-1) μ = 0 := by unfold Prim.FMu; rw [eMu_zero (by norm_num) hμ, zero_mul]
  rw [hF]
  have := g6_nonneg μ
  linarith

/-- At `α_a = -1`, every optimal involvement is below the status quo `μ_g = 1`. -/
lemma muStar_b_lt {μ : ℝ} (hμ : μ ∈ π0.muStar g6 (-1)) : μ < 1 := by
  obtain ⟨_, hmax⟩ := hμ
  by_contra h
  have h' : 1 ≤ μ := not_lt.1 h
  have h1 : π0.FMu (-1) (9 / 10) - g6 (9 / 10) ≤ π0.FMu (-1) μ - g6 μ :=
    hmax (9 / 10) (by norm_num)
  have := obj_b_le h'
  have := obj_b_pos
  linarith

/-- **Proposition 5 fails with a smooth `g` of Proposition 6's form.** `E1` (`α_a = -3/2`) and
`E2` (`α_a = -1`) share their primitives (quadratic costs).  With
`g(μ) = (μ-1)² + (1/μ-1)²` (minimised and differentiable at `μ_g = 1`), the less aligned
agent's manager keeps the status quo, `μ*(-3/2) = {1}`, and the agent exerts no effort; the
more aligned agent's manager is hands-off, `μ*(-1) ⊆ (0, 1)`.  Hence
`μ*(-3/2) ≤ μ*(-1)` fails in the strong set order. -/
theorem prop5_counterexample_smooth :
    ∃ (E E' : Env) (g : ℝ → ℝ) (μg : ℝ), E'.prim = E.prim ∧ E.alphaA < E'.alphaA ∧
      E.ca = Cost.quad 2 (by norm_num) ∧ E.cp = Cost.quad 1 (by norm_num) ∧
      0 < μg ∧ (∀ μ, 0 < μ → g μg ≤ g μ) ∧ DifferentiableAt ℝ g μg ∧
      ContinuousOn g (Ioi 0) ∧ Tendsto g (𝓝[>] 0) atTop ∧ Tendsto g atTop atTop ∧
      E.muStar g = {μg} ∧ E.eaMu μg = 0 ∧
      (E'.muStar g).Nonempty ∧ (∀ μ ∈ E'.muStar g, μ < μg) ∧
      ¬ SSOle (E.muStar g) (E'.muStar g) := by
  have hE : E1.muStar g6 = {1} := by rw [E1.muStar_eq, E1_alphaA]; exact muStar_a_smooth
  have hE' : ∀ μ ∈ E2.muStar g6, μ < 1 := by
    intro μ hμ
    rw [E2.muStar_eq, E2_prim, E2_alphaA] at hμ
    exact muStar_b_lt hμ
  have hne : (E2.muStar g6).Nonempty :=
    E2.muStar_nonempty g6_cont g6_tendsto_zero g6_tendsto_top
  refine ⟨E1, E2, g6, 1, E2_prim, by rw [E1_alphaA, E2_alphaA]; norm_num, rfl, rfl, one_pos,
    fun _ hμ => g6_min hμ, g6_diff, g6_cont, g6_tendsto_zero, g6_tendsto_top, hE, ?_, hne,
    hE', ?_⟩
  · rw [E1.eaMu_eq, E1_alphaA]; exact eMu32_zero (by norm_num)
  · intro hsso
    obtain ⟨y, hy⟩ := hne
    have h1 := (hsso 1 (by rw [hE]; exact Set.mem_singleton 1) y hy).2
    rw [max_eq_left (hE' y hy).le] at h1
    exact lt_irrefl _ (hE' 1 h1)

end Smooth

/-! ### Appendix B.1 with informal delegation -/

namespace EnvN

variable (E : EnvN)

/-- The principal's interim payoff under centralization with involvement `μ`; an uninformed
principal rejects, so she gets `0` without information. -/
noncomputable def UpMu (μ e : ℝ) : ℝ := e * E.EI .cen (fun v => v.2) - E.cp.c e / μ

/-- Subgame-perfect efforts after the choice of `μ`. -/
def IsEqMu (μ ea ep : ℝ) : Prop := IsBR (E.UpMu μ) ep ∧ IsBR (E.Ua .cen ep) ea

/-- Equilibrium principal effort given `μ`. -/
noncomputable def epMu (μ : ℝ) : ℝ := E.cp.br (μ * E.Pp)
/-- Equilibrium agent effort given `μ`. -/
noncomputable def eaMu (μ : ℝ) : ℝ := E.ca.br (E.Va .cen (E.epMu μ))

/-- The principal's ex-ante objective at the equilibrium efforts. -/
noncomputable def objMu (g : ℝ → ℝ) (μ : ℝ) : ℝ := E.eaMu μ * E.UpMu μ (E.epMu μ) - g μ

/-- `μ*(α_a^n)`, the profit-maximising involvement levels. -/
def muStar (g : ℝ → ℝ) : Set ℝ := argmaxPos (E.objMu g)

lemma isBR_UpMu_iff {μ e : ℝ} (hμ : 0 < μ) : IsBR (E.UpMu μ) e ↔ e = E.epMu μ := by
  have h : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ.ne'
  have hfun : E.UpMu μ = fun e => 0 + μ⁻¹ * (e * (μ * E.Pp) - E.cp.c e) := by
    funext e
    unfold UpMu Pp
    rw [div_eq_mul_inv]
    linear_combination (-(e * E.EI .cen (fun v => v.2))) * h
  rw [hfun]
  exact E.cp.isBR_affine_iff (inv_pos.2 hμ)

theorem isEqMu_iff {μ a p : ℝ} (hμ : 0 < μ) :
    E.IsEqMu μ a p ↔ p = E.epMu μ ∧ a = E.eaMu μ := by
  unfold IsEqMu
  rw [E.isBR_UpMu_iff hμ, E.isBR_Ua_iff]
  constructor
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- With `α_a^n ≤ 0`, the agent exerts no effort under centralization at any involvement:
an idea is implemented only if the principal investigates and approves it, and the ideas she
approves are bad for him on average. -/
theorem eaMu_eq_zero (hα : E.alphaA ≤ 0) (μ : ℝ) : E.eaMu μ = 0 := by
  unfold eaMu Va
  apply E.ca.br_eq_zero_of_nonpos
  have hp : 0 ≤ E.epMu μ := E.cp.br_nonneg _
  have hY : E.EI .cen (fun v => v.1) ≤ 0 := by
    show E.Ya ≤ 0
    rw [E.Ya_eq]
    exact mul_nonpos_of_nonpos_of_nonneg hα E.Pa_pos.le
  exact mul_nonpos_of_nonneg_of_nonpos hp hY

/-- With `α_a^n ≤ 0`, `μ*` is the set of minimisers of `g`: the principal neither
micromanages nor delegates informally for the agent's sake. -/
theorem mem_muStar_iff (hα : E.alphaA ≤ 0) (g : ℝ → ℝ) {μ : ℝ} :
    μ ∈ E.muStar g ↔ 0 < μ ∧ ∀ μ', 0 < μ' → g μ ≤ g μ' := by
  have hobj : ∀ μ, E.objMu g μ = -g μ := fun μ => by
    unfold objMu; rw [E.eaMu_eq_zero hα, zero_mul, zero_sub]
  constructor
  · rintro ⟨hμ, h⟩
    refine ⟨hμ, fun μ' hμ' => ?_⟩
    have := h μ' hμ'
    rw [hobj, hobj] at this
    linarith
  · rintro ⟨hμ, h⟩
    refine ⟨hμ, fun μ' hμ' => ?_⟩
    rw [hobj, hobj]
    linarith [h μ' hμ']

/-- `(v_a, v_p) = (2, 1)` w.p. `1/4`, `(-2, 1)` w.p. `1/4`, `(-1, -3)` w.p. `1/2`:
negative expected values and `α_a^n = 0`. -/
noncomputable def EZ : EnvN :=
  mkN ![1/4, 1/4, 1/2] ![(2, 1), (-2, 1), (-1, -3)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three])
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)

lemma EZ_integral (f : ℝ × ℝ → ℝ) :
    ∫ v, f v ∂EZ.F = 1 / 4 * f (2, 1) + 1 / 4 * f (-2, 1) + 1 / 2 * f (-1, -3) := by
  show ∫ v, f v ∂(discMeasure ![1/4, 1/4, 1/2] ![(2, 1), (-2, 1), (-1, -3)]) = _
  rw [disc_integral _ _ (by intro i; fin_cases i <;> norm_num), Fin.sum_univ_three]
  simp

lemma EZ_Ya : EZ.Ya = 0 := by
  simp [Ya, EI, EZ_integral, Set.indicator, Regime.dm]

lemma EZ_alphaA : EZ.alphaA = 0 := by rw [alphaA, EZ_Ya, zero_div]

/-- **The analogue of Proposition 6 fails in Appendix B.1.** In `EZ` (`α_a^n = 0`), with a `g`
that is minimised and differentiable at `μ_g = 1`, the agent exerts no effort at any `μ` and
the status quo `μ_g` is optimal, so not every element of `μ*(0)` exceeds `μ_g`. -/
theorem prop6_analogue_fails :
    ∃ (E : EnvN) (g : ℝ → ℝ) (μg : ℝ), E.alphaA = 0 ∧ 0 < μg ∧ (∀ μ, 0 < μ → g μg ≤ g μ) ∧
      DifferentiableAt ℝ g μg ∧ (∀ μ, E.eaMu μ = 0) ∧ μg ∈ E.muStar g :=
  ⟨EZ, g6, 1, EZ_alphaA, one_pos, fun _ hμ => g6_min hμ, g6_diff,
    EZ.eaMu_eq_zero EZ_alphaA.le,
    (EZ.mem_muStar_iff EZ_alphaA.le g6).2 ⟨one_pos, fun _ hμ => g6_min hμ⟩⟩

end EnvN

/-! ### Non-vacuity: the curvature version reaches negative alignment -/

section NonVacuity

lemma quad_concave {k : ℝ} (hk : 0 < k) :
    ConcaveOn ℝ (Icc 0 ((Cost.quad k hk).d 1)) (Cost.quad k hk).br := by
  obtain ⟨a, b, hab⟩ := quad_linear hk
  refine ⟨convex_Icc _ _, fun u hu w hw s t hs ht hst => ?_⟩
  rw [hab u hu, hab w hw, hab _ ((convex_Icc _ _) hu hw hs ht hst)]
  simp only [smul_eq_mul]
  have : b = s * b + t * b := by rw [← add_mul, hst, one_mul]
  nlinarith [this]

/-- `E7`: `(2,-1)` w.p. `1/4`, `(-1,2)` w.p. `1/4`, `(2,2)` w.p. `1/2`; `α_a = -2`. -/
noncomputable def E7 : Env :=
  mkEnv ![1/4, 1/4, 1/2] ![(2, -1), (-1, 2), (2, 2)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)

/-- `E8`: `(1,-1)` w.p. `1/4`, `(-1,2)` w.p. `1/4`, `(5/2,2)` w.p. `1/2`; same primitives as
`E7`, `α_a = -1`. -/
noncomputable def E8 : Env :=
  mkEnv ![1/4, 1/4, 1/2] ![(1, -1), (-1, 2), (5/2, 2)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three])
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)

lemma E7_A : E7.A = 5 / 4 := by
  simp only [Env.A, E7, mkEnv_integral, Fin.sum_univ_three]; norm_num
lemma E7_P : E7.P = 5 / 4 := by
  simp only [Env.P, E7, mkEnv_integral, Fin.sum_univ_three]; norm_num
lemma E7_Na : E7.Na = -1 / 4 := by
  simp [Env.Na, E7, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E7_Np : E7.Np = -1 / 4 := by
  simp [Env.Np, E7, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E7_Xa : E7.Xa = 1 / 2 := by
  simp [Env.Xa, E7, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E7_alphaA : E7.alphaA = -2 := by rw [Env.alphaA, E7_Xa, E7_Na]; norm_num

lemma E8_A : E8.A = 5 / 4 := by
  simp only [Env.A, E8, mkEnv_integral, Fin.sum_univ_three]; norm_num
lemma E8_P : E8.P = 5 / 4 := by
  simp only [Env.P, E8, mkEnv_integral, Fin.sum_univ_three]; norm_num
lemma E8_Na : E8.Na = -1 / 4 := by
  simp [Env.Na, E8, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E8_Np : E8.Np = -1 / 4 := by
  simp [Env.Np, E8, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E8_Xa : E8.Xa = 1 / 4 := by
  simp [Env.Xa, E8, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E8_alphaA : E8.alphaA = -1 := by rw [Env.alphaA, E8_Xa, E8_Na]; norm_num

lemma E8_prim : E8.prim = E7.prim := by
  simp only [Env.prim, E8_A, E8_P, E8_Na, E8_Np, E7_A, E7_P, E7_Na, E7_Np]
  rfl

/-- The hypotheses of `MI.Env.prop5_curvature` hold for two environments with the same
primitives and negative alignments `α_a = -2 < α_a' = -1` (quadratic `c_a`, so `h_a` is both
concave and convex, and `E(v_a 1_{v_p≥0}) = 3/4 ≥ 0`); `μ*` is non-empty for `g = g6`. -/
theorem nonvacuous_prop5_curvature :
    ∃ (E E' : Env) (g : ℝ → ℝ), E'.prim = E.prim ∧ E.alphaA < E'.alphaA ∧ E'.alphaA < 0 ∧
      ConcaveOn ℝ (Icc 0 E.A) E.ca.br ∧ ConvexOn ℝ (Icc E.A (E.ca.d 1)) E.ca.br ∧
      0 ≤ E.EI .cen (fun v => v.1) ∧ (E.muStar g).Nonempty ∧ (E'.muStar g).Nonempty ∧
      SSOle (E.muStar g) (E'.muStar g) := by
  have hcc : ConcaveOn ℝ (Icc 0 E7.A) E7.ca.br :=
    (quad_concave (by norm_num : (0 : ℝ) < 2)).subset
      (Icc_subset_Icc le_rfl (by rw [E7_A, Cost.quad_d_one]; norm_num)) (convex_Icc _ _)
  have hcv : ConvexOn ℝ (Icc E7.A (E7.ca.d 1)) E7.ca.br :=
    (quad_convex (by norm_num : (0 : ℝ) < 2)).subset
      (Icc_subset_Icc (by rw [E7_A]; norm_num) le_rfl) (convex_Icc _ _)
  have hq : 0 ≤ E7.EI .cen (fun v => v.1) := by rw [E7.EI_cen_a, E7_A, E7_Xa]; norm_num
  have hle : E7.alphaA ≤ E8.alphaA := by rw [E7_alphaA, E8_alphaA]; norm_num
  exact ⟨E7, E8, g6, E8_prim, by rw [E7_alphaA, E8_alphaA]; norm_num,
    by rw [E8_alphaA]; norm_num, hcc, hcv, hq,
    E7.muStar_nonempty g6_cont g6_tendsto_zero g6_tendsto_top,
    E8.muStar_nonempty g6_cont g6_tendsto_zero g6_tendsto_top,
    E7.prop5_curvature E8 E8_prim g6 hcc hcv hq hle⟩

end NonVacuity

end MI
