import ManagerialIntervention.Prop5General

/-!
# Proposition 5 under a convex, log-concave marginal cost

The agent's marginal benefit under centralization is
`m = E(v_a) - α_a E(v_a 1_{v_a<0}) e_p^c(μ)`, and his effort is `h_a(m)` with
`h_a = (c_a')⁻¹`.  This file proves Proposition 5 when

* the agent's marginal cost `c_a'` is **convex** on `[0,1]` (so `h_a` is concave), which handles
  negative alignment;
* `c_a'` is **log-concave** on `(0,1]` (so `s ↦ h_a(exp s)` is convex: the effort gained from a
  1% rise in the stakes does not shrink as the stakes grow), which handles positive alignment;
* the less aligned agent exerts **positive effort in equilibrium**, i.e. at every element of
  `μ*(α_a)`.  This replaces the condition `E(v_a 1_{v_p≥0}) ≥ 0` of `MI.Env.prop5_curvature`,
  which asks the agent to work at *every* involvement level.

Main results:

* `MI.Env.prop5_logconcave` — **Proposition 5** under the three conditions above.
* `MI.Env.prop5_logconcave_general` — the pairwise form: log-concavity is needed only when
  `α_a > 0`; convexity and positive equilibrium effort only when `α_a' < 0`; nothing when
  `α_a ≤ 0 ≤ α_a'`.
* `MI.Env.works_of_works_at_min` — if `g` is minimised at `μ_g` and the agent works at `μ_g`,
  then the agent works at every element of `μ*`; `MI.Env.prop5_logconcave_statusQuo` is the
  resulting version of Proposition 5 with a condition on primitives only.
* `MI.Cost.pow` — the cost `c(e) = k eⁿ` (`n ≥ 2`); `MI.Cost.pow_d_convex`,
  `MI.Cost.pow_d_logconcave` (and `MI.Cost.quad_d_convex`, `MI.Cost.quad_d_logconcave`) show it
  satisfies both cost conditions.
* `MI.EnvN.prop5_analogue` — the analogue of Proposition 5 in Appendix B.1 (negative-valued
  projects): with `E(v_a 1_{v_a≥0})`, `E(v_p 1_{v_p≥0})`, the costs and `g` fixed, `μ*(α_a^n)` is
  weakly increasing when `c_a'` is log-concave; no other condition is needed.
* `MI.EnvN.prop6_analogue` — the analogue of Proposition 6 in Appendix B.1 for every
  `α_a^n > 0`; `MI.EnvN.muStar_nonempty` — existence of an optimal `μ` there.
* `MI.EnvN.nonvacuous_prop5_analogue`, `MI.EnvN.nonvacuous_prop6_analogue` — the environments
  `EZ` (`α_a^n = 0`) and `EP` (`α_a^n = 1/2`) satisfy the hypotheses, with non-empty `μ*`.
* `MI.nonvacuous_prop5_logconcave` — the environments `E1` (`α_a = -3/2`) and `E2`
  (`α_a = -1`) with `g(μ) = g6(2μ)` satisfy all hypotheses, although `E(v_a 1_{v_p≥0}) < 0`
  in `E1`, so `MI.Env.prop5_curvature` and `MI.Env.prop5_linear` do not apply.
-/

namespace MI

open Set Filter Topology

/-! ### The cost conditions -/

namespace Cost

variable (κ : Cost)

/-- If `c'` is convex on `[0,1]`, its inverse `h = (c')⁻¹` is concave on `[0, c'(1)]`. -/
lemma br_concaveOn (hcv : ConvexOn ℝ (Icc 0 1) κ.d) : ConcaveOn ℝ (Icc 0 (κ.d 1)) κ.br := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hex := κ.br_mem x
  have hey := κ.br_mem y
  have h1 := hcv.2 hex hey ha hb hab
  rw [κ.d_br hx, κ.d_br hy] at h1
  have hmem : a • κ.br x + b • κ.br y ∈ Icc (0 : ℝ) 1 := (convex_Icc (0 : ℝ) 1) hex hey ha hb hab
  have h2 := κ.br_mono h1
  rwa [κ.br_d hmem] at h2

/-- If `c'` is log-concave on `(0,1]`, then `s ↦ h(exp s)` is convex on `(-∞, log c'(1)]`. -/
lemma br_exp_convexOn (hlc : ConcaveOn ℝ (Ioc 0 1) (fun e => Real.log (κ.d e))) :
    ConvexOn ℝ (Iic (Real.log (κ.d 1))) (fun s => κ.br (Real.exp s)) := by
  refine ⟨convex_Iic _, fun s hs t ht a b ha hb hab => ?_⟩
  have hd1 := κ.d_one_pos
  have hmem : ∀ u ∈ Iic (Real.log (κ.d 1)), Real.exp u ∈ Icc 0 (κ.d 1) := fun u hu =>
    ⟨(Real.exp_pos u).le, by
      have := Real.exp_le_exp.2 (mem_Iic.1 hu)
      rwa [Real.exp_log hd1] at this⟩
  have he : ∀ u, κ.br (Real.exp u) ∈ Ioc (0 : ℝ) 1 := fun u =>
    ⟨κ.br_pos (Real.exp_pos u), κ.br_le_one _⟩
  have hlog : ∀ u ∈ Iic (Real.log (κ.d 1)), Real.log (κ.d (κ.br (Real.exp u))) = u := by
    intro u hu
    rw [κ.d_br (hmem u hu), Real.log_exp]
  have hc := hlc.2 (he s) (he t) ha hb hab
  simp only [smul_eq_mul, hlog s hs, hlog t ht] at hc
  have hm := (convex_Ioc (0 : ℝ) 1) (he s) (he t) ha hb hab
  simp only [smul_eq_mul] at hm
  have hpos : 0 < κ.d (a * κ.br (Real.exp s) + b * κ.br (Real.exp t)) := by
    have := κ.d_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨hm.1.le, hm.2⟩ hm.1
    rwa [κ.d_zero] at this
  have hexp : Real.exp (a * s + b * t) ≤ κ.d (a * κ.br (Real.exp s) + b * κ.br (Real.exp t)) := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hc
  have h2 := κ.br_mono hexp
  rw [κ.br_d ⟨hm.1.le, hm.2⟩] at h2
  simpa only [smul_eq_mul] using h2

/-- Multiplicative increasing differences: if `s ↦ h(exp s)` is convex, then for `k ≥ 1` the
gain `h(k m) - h(m)` is increasing in `m > 0`. -/
lemma mul_incr (hH : ConvexOn ℝ (Iic (Real.log (κ.d 1))) (fun s => κ.br (Real.exp s)))
    {m m' k : ℝ} (hm : 0 < m) (hmm : m ≤ m') (hk : 1 ≤ k) (hkm : k * m' ≤ κ.d 1) :
    κ.br (k * m) - κ.br m ≤ κ.br (k * m') - κ.br m' := by
  have hm' : 0 < m' := hm.trans_le hmm
  have hk0 : 0 < k := by linarith
  have ha : Real.log m ∈ Iic (Real.log (κ.d 1)) :=
    Real.log_le_log hm (by nlinarith)
  have hb : Real.log m' + Real.log k ∈ Iic (Real.log (κ.d 1)) := by
    rw [← Real.log_mul hm'.ne' hk0.ne']
    exact Real.log_le_log (mul_pos hm' hk0) (by linarith [mul_comm m' k])
  have h := convex_incr hH (Real.log_le_log hm hmm) (Real.log_nonneg hk) ha hb
  simp only [Real.exp_add, Real.exp_log hm, Real.exp_log hm', Real.exp_log hk0] at h
  rw [mul_comm k m, mul_comm k m']
  exact h

/-- `e ↦ K e^j` is convex on `[0,1]` for `K ≥ 0`. -/
lemma convex_monomial {K : ℝ} (hK : 0 ≤ K) (j : ℕ) :
    ConvexOn ℝ (Icc 0 1) (fun e : ℝ => K * e ^ j) :=
  ((convexOn_pow j).subset Icc_subset_Ici_self (convex_Icc 0 1)).smul hK

/-- `e ↦ K e^j` is log-concave on `(0,1]` for `K > 0`. -/
lemma logconcave_monomial {K : ℝ} (hK : 0 < K) (j : ℕ) :
    ConcaveOn ℝ (Ioc 0 1) (fun e : ℝ => Real.log (K * e ^ j)) := by
  refine ⟨convex_Ioc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy := ((convex_Ioc (0 : ℝ) 1) hx hy ha hb hab).1
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 (show x ∈ Ioi 0 from hx.1)
    (show y ∈ Ioi 0 from hy.1) ha hb hab
  simp only [smul_eq_mul] at hlog hxy ⊢
  rw [Real.log_mul hK.ne' (pow_ne_zero _ hx.1.ne'), Real.log_mul hK.ne' (pow_ne_zero _ hy.1.ne'),
    Real.log_mul hK.ne' (pow_ne_zero _ hxy.ne')]
  simp only [Real.log_pow]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain rfl : b = 1 - a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog hj]

/-- The power cost `c(e) = k eⁿ` with `n ≥ 2`, so `c'(e) = k n e^{n-1}`. -/
noncomputable def pow (k : ℝ) (hk : 0 < k) (n : ℕ) (hn : 2 ≤ n) : Cost where
  c e := k * e ^ n
  d e := k * n * e ^ (n - 1)
  hasDerivAt x := by
    have := (hasDerivAt_pow n x).const_mul k
    convert this using 1
    ring
  c_zero := by simp [zero_pow (by omega : n ≠ 0)]
  d_zero := by simp [zero_pow (by omega : n - 1 ≠ 0)]
  d_strictMonoOn := fun x hx y _ h => by
    show k * n * x ^ (n - 1) < k * n * y ^ (n - 1)
    have hkn : 0 < k * n := mul_pos hk (Nat.cast_pos.2 (by omega))
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ h hx.1 (by omega)) hkn

lemma pow_d_convex {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 2 ≤ n) :
    ConvexOn ℝ (Icc 0 1) (pow k hk n hn).d :=
  convex_monomial (K := k * n) (mul_nonneg hk.le (Nat.cast_nonneg n)) (n - 1)

lemma pow_d_logconcave {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 2 ≤ n) :
    ConcaveOn ℝ (Ioc 0 1) (fun e => Real.log ((pow k hk n hn).d e)) :=
  logconcave_monomial (K := k * n) (mul_pos hk (Nat.cast_pos.2 (by omega))) (n - 1)

lemma quad_d_convex {k : ℝ} (hk : 0 < k) : ConvexOn ℝ (Icc 0 1) (quad k hk).d := by
  have h := convex_monomial hk.le 1
  simp only [pow_one] at h
  exact h

lemma quad_d_logconcave {k : ℝ} (hk : 0 < k) :
    ConcaveOn ℝ (Ioc 0 1) (fun e => Real.log ((quad k hk).d e)) := by
  have h := logconcave_monomial hk 1
  simp only [pow_one] at h
  exact h

end Cost

/-- Monotone comparative statics needs increasing differences only between a maximiser `μ` for
`α'` and a larger maximiser `μ'` for `α`. -/
theorem sso_of_ID_at {F : ℝ → ℝ → ℝ} (g : ℝ → ℝ) {α α' : ℝ}
    (hID : ∀ μ μ', μ ∈ argmaxPos (fun μ => F α' μ - g μ) →
      μ' ∈ argmaxPos (fun μ => F α μ - g μ) → μ ≤ μ' →
      F α' μ - F α μ ≤ F α' μ' - F α μ') :
    SSOle (argmaxPos fun μ => F α μ - g μ) (argmaxPos fun μ => F α' μ - g μ) := by
  intro x hx y hy
  rcases le_or_gt x y with hxy | hxy
  · rw [min_eq_left hxy, max_eq_right hxy]; exact ⟨hx, hy⟩
  · rw [min_eq_right hxy.le, max_eq_left hxy.le]
    have hID' := hID y x hy hx hxy.le
    refine ⟨⟨hy.1, fun μ' hμ' => ?_⟩, ⟨hx.1, fun μ' hμ' => ?_⟩⟩
    · have h1 := hx.2 μ' hμ'
      have h2 := hy.2 x hx.1
      simp only at h1 h2 ⊢
      linarith
    · have h1 := hy.2 μ' hμ'
      have h2 := hx.2 y hy.1
      simp only at h1 h2 ⊢
      linarith

/-! ### Increasing differences in reduced form -/

namespace Prim

variable {π : Prim}

/-- Increasing differences for `0 < α ≤ α'` when `s ↦ h_a(exp s)` is convex. -/
lemma ID_logconcave (hπ : π.Valid) (hB : π.Bounded)
    (hH : ConvexOn ℝ (Iic (Real.log (π.ca.d 1))) (fun s => π.ca.br (Real.exp s)))
    {α α' : ℝ} (h0 : 0 < α) (hαα : α ≤ α') (h1 : α' ≤ 1) {μ μ' : ℝ} (hμ : 0 < μ)
    (hμμ : μ ≤ μ') : π.FMu α' μ - π.FMu α μ ≤ π.FMu α' μ' - π.FMu α μ' := by
  apply ID_of hπ hμ hμμ _ hαα
  have hp := pMu_mono hπ hμμ
  have hp0 := (pMu_mem (π := π) μ).1
  have hp1 := (pMu_mem (π := π) μ').2
  have hN := hπ.Na_neg
  have hA := hπ.A_pos
  set p := π.pMu μ
  set p' := π.pMu μ'
  set x := π.A - α * p * π.Na
  set x' := π.A - α * p' * π.Na
  set y := π.A - α' * p * π.Na
  set y' := π.A - α' * p' * π.Na
  have hx : 0 < x := by
    have : 0 ≤ α * p * -π.Na := mul_nonneg (mul_nonneg h0.le hp0) (by linarith)
    simp only [x]; linarith
  have hxx : x ≤ x' := by
    have : 0 ≤ α * (p' - p) * -π.Na :=
      mul_nonneg (mul_nonneg h0.le (by linarith)) (by linarith)
    simp only [x, x']; nlinarith
  have hxy : x ≤ y := by
    have : 0 ≤ (α' - α) * p * -π.Na := mul_nonneg (mul_nonneg (by linarith) hp0) (by linarith)
    simp only [x, y]; nlinarith
  have hcross : y * x' ≤ y' * x := by
    have : 0 ≤ π.A * -π.Na * ((α' - α) * (p' - p)) :=
      mul_nonneg (mul_nonneg hA.le (by linarith)) (mul_nonneg (by linarith) (by linarith))
    simp only [x, x', y, y']; nlinarith
  have hy' : y' ≤ π.ca.d 1 := by
    have hαp : α' * p' ≤ 1 := by nlinarith
    have : 0 ≤ (1 - α' * p') * -π.Na := mul_nonneg (by linarith) (by linarith)
    unfold Bounded at hB
    simp only [y']; nlinarith
  have hk : 1 ≤ y / x := (one_le_div hx).2 hxy
  have hkx : y / x * x = y := by field_simp
  have hkx' : y / x * x' ≤ y' := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx]; linarith
  have hmul := Cost.mul_incr π.ca hH hx hxx hk (hkx'.trans hy')
  rw [hkx] at hmul
  have hmono := π.ca.br_mono hkx'
  show π.ca.br y - π.ca.br x ≤ π.ca.br y' - π.ca.br x'
  linarith

/-- Increasing differences for `α ≤ α' ≤ 0` when `h_a` is concave below `E(v_a)` and the less
aligned agent's marginal benefit is non-negative at the larger involvement level `μ'`. -/
lemma ID_concave_at (hπ : π.Valid) (hcc : ConcaveOn ℝ (Icc 0 π.A) π.ca.br)
    {α α' : ℝ} (hαα : α ≤ α') (h1 : α' ≤ 0) {μ μ' : ℝ} (hμ : 0 < μ) (hμμ : μ ≤ μ')
    (hm0 : 0 ≤ π.A - α * π.pMu μ' * π.Na) :
    π.FMu α' μ - π.FMu α μ ≤ π.FMu α' μ' - π.FMu α μ' := by
  apply ID_of hπ hμ hμμ _ hαα
  have hp := pMu_mono hπ hμμ
  have hp0 := (pMu_mem (π := π) μ).1
  have hp1' := (pMu_mem (π := π) μ').2
  have hN := hπ.Na_neg
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
  have hc0 : 0 ≤ c := hm0
  have hcA : c ≤ π.A := by
    have : 0 ≤ (-α) * p' * -π.Na :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    simp only [c]; nlinarith
  have hb : a + L = π.A - α' * p * π.Na := by simp only [a, L]; ring
  have hb0 : 0 ≤ a + L := by
    rw [hb]
    have h2 : 0 ≤ (α' - α) * p * -π.Na :=
      mul_nonneg (mul_nonneg (by linarith) hp0) (by linarith)
    have h3 : 0 ≤ (-α) * (p' - p) * -π.Na :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have : c = π.A - α * p' * π.Na := rfl
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

/-- Proposition 5 in reduced form: log-concavity for positive alignment; concavity of `h_a` and
a non-negative marginal benefit at the less aligned agent's optima for negative alignment. -/
theorem muStar_sso_logconcave (hπ : π.Valid) (hB : π.Bounded) (g : ℝ → ℝ) {α α' : ℝ}
    (hαα : α ≤ α') (h1 : α' ≤ 1)
    (hlc : 0 < α → ConvexOn ℝ (Iic (Real.log (π.ca.d 1))) (fun s => π.ca.br (Real.exp s)))
    (hcc : α' < 0 → ConcaveOn ℝ (Icc 0 π.A) π.ca.br)
    (hwork : α' < 0 → ∀ μ ∈ π.muStar g α, 0 ≤ π.A - α * π.pMu μ * π.Na) :
    SSOle (π.muStar g α) (π.muStar g α') := by
  refine sso_of_ID_at g fun μ μ' hμ hμ' hle => ?_
  rcases le_or_gt α 0 with hα | hα
  · rcases le_or_gt 0 α' with hα' | hα'
    · exact ID_straddle hπ hα hα' hμ.1 hle
    · exact ID_concave_at hπ (hcc hα') hαα hα'.le hμ.1 hle (hwork hα' μ' hμ')
  · exact ID_logconcave hπ hB (hlc hα) hα hαα h1 hμ.1 hle

/-- If the agent exerts positive effort at a minimiser `μ_g` of `g`, he exerts positive effort at
every profit-maximising involvement level. -/
lemma works_of_works_at_min (hπ : π.Valid) {g : ℝ → ℝ} {α μg : ℝ} (hμg : 0 < μg)
    (hmin : ∀ μ, 0 < μ → g μg ≤ g μ) (hw : 0 < π.eMu α μg) :
    ∀ μ ∈ π.muStar g α, 0 < π.eMu α μ := by
  intro μ hμ
  have h0 : 0 ≤ π.eMu α μ := π.ca.br_nonneg _
  rcases h0.eq_or_lt with h0 | h0
  · exfalso
    have h1 := hμ.2 μg hμg
    simp only at h1
    have hF : π.FMu α μ = 0 := by unfold FMu; rw [← h0]; ring
    have hF' : 0 < π.FMu α μg := mul_pos hw (UMu_pos hπ hμg)
    have := hmin μ hμ.1
    linarith
  · exact h0

end Prim

/-! ### Proposition 5 in an environment -/

namespace Env

variable (E : Env)

lemma A_le_d_one : E.A ≤ E.ca.d 1 := by linarith [E.ca_bound, E.Na_neg]

/-- Positive equilibrium effort, in reduced form. -/
lemma work_reduced {g : ℝ → ℝ} (hwork : ∀ μ ∈ E.muStar g, 0 < E.eaMu μ) :
    ∀ μ ∈ E.prim.muStar g E.alphaA,
      0 ≤ E.prim.A - E.alphaA * E.prim.pMu μ * E.prim.Na := by
  intro μ hμ
  rw [← E.muStar_eq] at hμ
  have h := hwork μ hμ
  rw [E.eaMu_eq] at h
  by_contra hneg
  exact h.ne' (E.prim.ca.br_eq_zero_of_nonpos (not_le.1 hneg).le)

/-- **Proposition 5, pairwise form.** Fix the primitives and `g`, and let `α_a ≤ α_a'`.  Then
`μ*(α_a) ≤ μ*(α_a')` in the strong set order provided
* `c_a'` is log-concave on `(0,1]` if `α_a > 0`, and
* `c_a'` is convex on `[0,1]` and the less aligned agent exerts positive effort at every element
  of `μ*(α_a)` if `α_a' < 0`.
Nothing more is needed when `α_a ≤ 0 ≤ α_a'`. -/
theorem prop5_logconcave_general (E' : Env) (hprim : E'.prim = E.prim) (g : ℝ → ℝ)
    (hle : E.alphaA ≤ E'.alphaA)
    (hlc : 0 < E.alphaA → ConcaveOn ℝ (Ioc 0 1) (fun e => Real.log (E.ca.d e)))
    (hcv : E'.alphaA < 0 → ConvexOn ℝ (Icc 0 1) E.ca.d ∧ ∀ μ ∈ E.muStar g, 0 < E.eaMu μ) :
    SSOle (E.muStar g) (E'.muStar g) := by
  rw [E.muStar_eq, E'.muStar_eq, hprim]
  refine Prim.muStar_sso_logconcave E.prim_valid E.prim_bounded g hle E'.alphaA_le_one
    (fun h => E.prim.ca.br_exp_convexOn (hlc h)) (fun h => ?_) (fun h => E.work_reduced (hcv h).2)
  exact (E.prim.ca.br_concaveOn (hcv h).1).subset (Icc_subset_Icc le_rfl E.A_le_d_one)
    (convex_Icc _ _)

/-- **Proposition 5 (corrected).** Fix the primitives `(E(v_a), E(v_p), E(v_a 1_{v_a<0}),
E(v_p 1_{v_p<0}), c_a, c_p)` and `g`.  If the agent's marginal cost `c_a'` is convex and
log-concave, and the less aligned agent exerts positive effort in equilibrium, then
`μ*(α_a) ≤ μ*(α_a')` in the strong set order whenever `α_a ≤ α_a'`. -/
theorem prop5_logconcave (E' : Env) (hprim : E'.prim = E.prim) (g : ℝ → ℝ)
    (hcv : ConvexOn ℝ (Icc 0 1) E.ca.d)
    (hlc : ConcaveOn ℝ (Ioc 0 1) (fun e => Real.log (E.ca.d e)))
    (hwork : ∀ μ ∈ E.muStar g, 0 < E.eaMu μ) (hle : E.alphaA ≤ E'.alphaA) :
    SSOle (E.muStar g) (E'.muStar g) :=
  E.prop5_logconcave_general E' hprim g hle (fun _ => hlc) (fun _ => ⟨hcv, hwork⟩)

/-- If `g` is minimised at `μ_g` and the agent works at `μ_g`, the agent works in equilibrium. -/
theorem works_of_works_at_min {g : ℝ → ℝ} {μg : ℝ} (hμg : 0 < μg)
    (hmin : ∀ μ, 0 < μ → g μg ≤ g μ) (hw : 0 < E.eaMu μg) :
    ∀ μ ∈ E.muStar g, 0 < E.eaMu μ := by
  intro μ hμ
  rw [E.muStar_eq] at hμ
  rw [E.eaMu_eq] at hw ⊢
  exact Prim.works_of_works_at_min E.prim_valid hμg hmin hw μ hμ

/-- **Proposition 5 with a condition on primitives.** As `MI.Env.prop5_logconcave`, with
"positive effort in equilibrium" replaced by "positive effort at the status quo `μ_g`". -/
theorem prop5_logconcave_statusQuo (E' : Env) (hprim : E'.prim = E.prim) {g : ℝ → ℝ}
    {μg : ℝ} (hμg : 0 < μg) (hmin : ∀ μ, 0 < μ → g μg ≤ g μ)
    (hcv : ConvexOn ℝ (Icc 0 1) E.ca.d)
    (hlc : ConcaveOn ℝ (Ioc 0 1) (fun e => Real.log (E.ca.d e)))
    (hw : 0 < E.eaMu μg) (hle : E.alphaA ≤ E'.alphaA) :
    SSOle (E.muStar g) (E'.muStar g) :=
  E.prop5_logconcave E' hprim g hcv hlc (E.works_of_works_at_min hμg hmin hw) hle

end Env

/-! ### Appendix B.1: the analogue of Proposition 5 -/

namespace EnvN

variable (E : EnvN)

/-- The principal's objective without `g`, as a function of the alignment `α` with the
primitives of `E` held fixed: agent effort `h_a(e_p α E(v_a 1_{v_a≥0}))` times the principal's
interim payoff. -/
noncomputable def FN (α μ : ℝ) : ℝ := E.ca.br (E.epMu μ * (α * E.Pa)) * E.UpMu μ (E.epMu μ)

lemma objMu_eq_FN (g : ℝ → ℝ) (μ : ℝ) : E.objMu g μ = E.FN E.alphaA μ - g μ := by
  unfold objMu FN eaMu Va
  rw [show E.EI .cen (fun v => v.1) = E.alphaA * E.Pa from E.Ya_eq]

lemma muStar_eq_FN (g : ℝ → ℝ) : E.muStar g = argmaxPos fun μ => E.FN E.alphaA μ - g μ := by
  unfold muStar
  congr 1
  funext μ
  exact E.objMu_eq_FN g μ

lemma alphaA_le_one : E.alphaA ≤ 1 := (div_le_one E.Pa_pos).2 E.Ya_le_Pa

lemma epMu_pos {μ : ℝ} (hμ : 0 < μ) : 0 < E.epMu μ := E.cp.br_pos (mul_pos hμ E.Pp_pos)

lemma epMu_mono {μ μ' : ℝ} (h : μ ≤ μ') : E.epMu μ ≤ E.epMu μ' :=
  E.cp.br_mono (mul_le_mul_of_nonneg_right h E.Pp_pos.le)

lemma UpMu_opt_nonneg {μ : ℝ} (hμ : 0 < μ) : 0 ≤ E.UpMu μ (E.epMu μ) := by
  have h := ((E.isBR_UpMu_iff hμ).2 rfl).2 0 ⟨le_rfl, zero_le_one⟩
  have h0 : E.UpMu μ 0 = 0 := by unfold UpMu; rw [E.cp.c_zero]; ring
  linarith

lemma UpMu_opt_mono {μ μ' : ℝ} (hμ : 0 < μ) (h : μ ≤ μ') :
    E.UpMu μ (E.epMu μ) ≤ E.UpMu μ' (E.epMu μ') := by
  have hμ' : 0 < μ' := hμ.trans_le h
  have h1 := ((E.isBR_UpMu_iff hμ').2 rfl).2 (E.epMu μ) (E.cp.br_mem _)
  have hc : 0 ≤ E.cp.c (E.epMu μ) := E.cp.c_nonneg (E.cp.br_mem _)
  have h2 : E.cp.c (E.epMu μ) / μ' ≤ E.cp.c (E.epMu μ) / μ :=
    div_le_div_of_nonneg_left hc hμ h
  have h3 : E.UpMu μ (E.epMu μ) ≤ E.UpMu μ' (E.epMu μ) := by unfold UpMu; linarith
  linarith

/-- Increasing differences of the B.1 objective; log-concavity is used only when `α > 0`. -/
lemma ID_FN {α α' : ℝ} (hαα : α ≤ α') (h1 : α' ≤ 1)
    (hlc : 0 < α → ConvexOn ℝ (Iic (Real.log (E.ca.d 1))) (fun s => E.ca.br (Real.exp s)))
    {μ μ' : ℝ} (hμ : 0 < μ) (hμμ : μ ≤ μ') :
    E.FN α' μ - E.FN α μ ≤ E.FN α' μ' - E.FN α μ' := by
  unfold FN
  have hp := E.epMu_pos hμ
  have hpp := E.epMu_mono hμμ
  have hp1 : E.epMu μ' ≤ 1 := E.cp.br_le_one _
  have hPa := E.Pa_pos
  have hU := E.UpMu_opt_mono hμ hμμ
  have hU0 := E.UpMu_opt_nonneg hμ
  set p := E.epMu μ
  set p' := E.epMu μ'
  set U := E.UpMu μ p
  set U' := E.UpMu μ' p'
  have hp' : 0 < p' := hp.trans_le hpp
  have hD : E.ca.br (p * (α' * E.Pa)) - E.ca.br (p * (α * E.Pa)) ≤
      E.ca.br (p' * (α' * E.Pa)) - E.ca.br (p' * (α * E.Pa)) := by
    have z : ∀ q a : ℝ, 0 ≤ q → a ≤ 0 → E.ca.br (q * (a * E.Pa)) = 0 := fun q a hq ha =>
      E.ca.br_eq_zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hq (mul_nonpos_of_nonpos_of_nonneg ha hPa.le))
    rcases le_or_gt α' 0 with hα' | hα'
    · rw [z p α' hp.le hα', z p α hp.le (hαα.trans hα'), z p' α' hp'.le hα',
        z p' α hp'.le (hαα.trans hα')]
    · rcases le_or_gt α 0 with hα | hα
      · rw [z p α hp.le hα, z p' α hp'.le hα]
        have := E.ca.br_mono
          (mul_le_mul_of_nonneg_right hpp (mul_pos hα' hPa).le : p * (α' * E.Pa) ≤ p' * (α' * E.Pa))
        linarith
      · have hm : 0 < p * (α * E.Pa) := mul_pos hp (mul_pos hα hPa)
        have hmm : p * (α * E.Pa) ≤ p' * (α * E.Pa) :=
          mul_le_mul_of_nonneg_right hpp (mul_pos hα hPa).le
        have hk : 1 ≤ α' / α := (one_le_div hα).2 hαα
        have hkm : α' / α * (p' * (α * E.Pa)) = p' * (α' * E.Pa) := by field_simp
        have hkm0 : α' / α * (p * (α * E.Pa)) = p * (α' * E.Pa) := by field_simp
        have hbound : p' * (α' * E.Pa) ≤ E.ca.d 1 := by
          have h3 : p' * α' ≤ 1 := by nlinarith
          have h4 := mul_le_mul_of_nonneg_right h3 hPa.le
          have h5 := E.Pa_le
          nlinarith
        have h := Cost.mul_incr E.ca (hlc hα) hm hmm hk (by rw [hkm]; exact hbound)
        rw [hkm, hkm0] at h
        exact h
  have hD0 : 0 ≤ E.ca.br (p * (α' * E.Pa)) - E.ca.br (p * (α * E.Pa)) :=
    sub_nonneg.2 (E.ca.br_mono
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαα hPa.le) hp.le))
  have := mul_le_mul hD hU hU0 (hD0.trans hD)
  nlinarith [this]

/-- **The analogue of Proposition 5 in Appendix B.1.** Hold fixed `E(v_a 1_{v_a≥0})`,
`E(v_p 1_{v_p≥0})`, `c_a`, `c_p` and `g`.  If `c_a'` is log-concave (needed only when
`α_a^n > 0`), then `μ*(α_a^n)` is weakly increasing in the strong set order.  No convexity or
positive-effort condition is needed: for `α_a^n ≤ 0` the agent never works. -/
theorem prop5_analogue (E' : EnvN) (hPa : E'.Pa = E.Pa) (hPp : E'.Pp = E.Pp)
    (hca : E'.ca = E.ca) (hcp : E'.cp = E.cp) (g : ℝ → ℝ) (hle : E.alphaA ≤ E'.alphaA)
    (hlc : 0 < E.alphaA → ConcaveOn ℝ (Ioc 0 1) (fun e => Real.log (E.ca.d e))) :
    SSOle (E.muStar g) (E'.muStar g) := by
  have hF : ∀ μ, E'.FN E'.alphaA μ = E.FN E'.alphaA μ := by
    intro μ
    have hep : E'.epMu μ = E.epMu μ := by unfold epMu; rw [hcp, hPp]
    have hU : ∀ e, E'.UpMu μ e = E.UpMu μ e := by
      intro e
      show e * E'.Pp - E'.cp.c e / μ = e * E.Pp - E.cp.c e / μ
      rw [hPp, hcp]
    unfold FN
    rw [hep, hU, hca, hPa]
  rw [E.muStar_eq_FN, E'.muStar_eq_FN]
  simp only [hF]
  exact sso_of_ID g fun μ μ' hμ hμμ =>
    E.ID_FN hle E'.alphaA_le_one (fun h => E.ca.br_exp_convexOn (hlc h)) hμ hμμ

/-! ### Appendix B.1: the analogue of Proposition 6 -/

lemma UpMu_opt_diff {μ μ' : ℝ} (hμ' : 0 < μ') :
    E.cp.c (E.epMu μ) * (1 / μ - 1 / μ') ≤ E.UpMu μ' (E.epMu μ') - E.UpMu μ (E.epMu μ) := by
  have h1 := ((E.isBR_UpMu_iff hμ').2 rfl).2 (E.epMu μ) (E.cp.br_mem _)
  have h2 : E.UpMu μ' (E.epMu μ) - E.UpMu μ (E.epMu μ) =
      E.cp.c (E.epMu μ) * (1 / μ - 1 / μ') := by
    unfold UpMu; ring
  linarith

lemma eaMu_eq_br (μ : ℝ) : E.eaMu μ = E.ca.br (E.epMu μ * (E.alphaA * E.Pa)) := by
  unfold eaMu Va
  rw [show E.EI .cen (fun v => v.1) = E.alphaA * E.Pa from E.Ya_eq]

lemma eaMu_pos (hα : 0 < E.alphaA) {μ : ℝ} (hμ : 0 < μ) : 0 < E.eaMu μ := by
  rw [E.eaMu_eq_br]
  exact E.ca.br_pos (mul_pos (E.epMu_pos hμ) (mul_pos hα E.Pa_pos))

lemma eaMu_mono (hα : 0 ≤ E.alphaA) {μ μ' : ℝ} (h : μ ≤ μ') : E.eaMu μ ≤ E.eaMu μ' := by
  rw [E.eaMu_eq_br, E.eaMu_eq_br]
  exact E.ca.br_mono (mul_le_mul_of_nonneg_right (E.epMu_mono h) (mul_nonneg hα E.Pa_pos.le))

/-- **The analogue of Proposition 6 in Appendix B.1.** If `α_a^n > 0` and `g` is differentiable
with a minimum at `μ_g > 0`, every element of `μ*(α_a^n)` is strictly greater than `μ_g`. -/
theorem prop6_analogue (hα : 0 < E.alphaA) {g : ℝ → ℝ} {μg : ℝ} (hμg : 0 < μg)
    (hmin : ∀ μ, 0 < μ → g μg ≤ g μ) (hdiff : DifferentiableAt ℝ g μg) :
    ∀ μ ∈ E.muStar g, μg < μ := by
  intro μ hμ
  obtain ⟨hμ0, hmax⟩ := hμ
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · -- `μ < μ_g` is strictly worse than `μ_g`
    have h1 := hmax μg hμg
    have hUd := E.UpMu_opt_diff (μ := μ) hμg
    have hc : 0 < E.cp.c (E.epMu μ) := E.cp.c_pos ⟨E.epMu_pos hμ0, E.cp.br_le_one _⟩
    have hrec : 0 < 1 / μ - 1 / μg := sub_pos.2 (one_div_lt_one_div_of_lt hμ0 hlt)
    have hU : E.UpMu μ (E.epMu μ) < E.UpMu μg (E.epMu μg) := by nlinarith [mul_pos hc hrec]
    have he := E.eaMu_mono hα.le hlt.le
    have he0 := E.eaMu_pos hα hμg
    have hU0 := E.UpMu_opt_nonneg hμ0
    have := hmin μ hμ0
    unfold objMu at h1
    have : E.eaMu μ * E.UpMu μ (E.epMu μ) < E.eaMu μg * E.UpMu μg (E.epMu μg) :=
      calc E.eaMu μ * E.UpMu μ (E.epMu μ) ≤ E.eaMu μg * E.UpMu μ (E.epMu μ) :=
            mul_le_mul_of_nonneg_right he hU0
        _ < E.eaMu μg * E.UpMu μg (E.epMu μg) := mul_lt_mul_of_pos_left hU he0
    linarith
  · -- `μ = μ_g`: a slightly larger `μ` does strictly better, since `g'(μ_g) = 0`
    subst heq
    have hloc : IsLocalMin g μ :=
      IsMinOn.isLocalMin (isMinOn_iff.2 fun x hx => hmin x hx) (Ioi_mem_nhds hμ0)
    have hderiv : HasDerivAt g 0 μ := by
      have := hloc.hasDerivAt_eq_zero hdiff.hasDerivAt
      rw [← this]; exact hdiff.hasDerivAt
    have he0 : 0 < E.eaMu μ := E.eaMu_pos hα hμ0
    have hc : 0 < E.cp.c (E.epMu μ) := E.cp.c_pos ⟨E.epMu_pos hμ0, E.cp.br_le_one _⟩
    obtain ⟨k, hk⟩ : ∃ k : ℝ, k = E.eaMu μ * E.cp.c (E.epMu μ) / (2 * μ ^ 2) := ⟨_, rfl⟩
    have hkpos : 0 < k := by rw [hk]; positivity
    have hlo := (hasDerivAt_iff_isLittleO.1 hderiv).def (show 0 < k / 2 by positivity)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hlo
    set d := min (δ / 2) μ with hd
    have hd0 : 0 < d := lt_min (by linarith) hμ0
    have hdδ : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdμ : d ≤ μ := min_le_right _ _
    set μ'' := μ + d
    have hμ''0 : 0 < μ'' := by positivity
    have hgb := hball (show dist μ'' μ < δ by
      rw [Real.dist_eq]; simp only [μ'', add_sub_cancel_left, abs_of_pos hd0]; exact hdδ)
    simp only [smul_zero, sub_zero, Real.norm_eq_abs, μ'', add_sub_cancel_left,
      abs_of_pos hd0] at hgb
    have hgup : g (μ + d) - g μ ≤ k / 2 * d := (abs_le.1 hgb).2
    have hUd := E.UpMu_opt_diff (μ := μ) hμ''0
    have hrec : d / (2 * μ ^ 2) ≤ 1 / μ - 1 / μ'' := by
      have : 1 / μ - 1 / μ'' = d / (μ * (μ + d)) := by
        simp only [μ'']; field_simp; ring
      rw [this]
      apply div_le_div_of_nonneg_left hd0.le (by positivity)
      nlinarith
    have hFgain : k * d ≤
        E.eaMu μ'' * E.UpMu μ'' (E.epMu μ'') - E.eaMu μ * E.UpMu μ (E.epMu μ) := by
      have he'' := E.eaMu_mono hα.le (show μ ≤ μ'' by linarith)
      have hU'' := E.UpMu_opt_nonneg hμ''0
      have h1 : E.eaMu μ * E.UpMu μ'' (E.epMu μ'') ≤ E.eaMu μ'' * E.UpMu μ'' (E.epMu μ'') :=
        mul_le_mul_of_nonneg_right he'' hU''
      have h2 : E.eaMu μ * (E.cp.c (E.epMu μ) * (d / (2 * μ ^ 2))) ≤
          E.eaMu μ * (E.UpMu μ'' (E.epMu μ'') - E.UpMu μ (E.epMu μ)) := by
        apply mul_le_mul_of_nonneg_left _ he0.le
        exact le_trans (mul_le_mul_of_nonneg_left hrec hc.le) hUd
      have h3 : k * d = E.eaMu μ * (E.cp.c (E.epMu μ) * (d / (2 * μ ^ 2))) := by
        rw [hk]; field_simp
      nlinarith
    have := hmax μ'' hμ''0
    unfold objMu at this
    nlinarith

/-! ### Appendix B.1: existence and non-vacuity -/

lemma epMu_continuous : Continuous E.epMu :=
  E.cp.br_continuous.comp (continuous_id.mul continuous_const)

/-- `μ*` is non-empty when `g` is continuous on `(0, ∞)` and tends to `∞` at `0` and at `∞`. -/
theorem muStar_nonempty {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    (h0 : Tendsto g (𝓝[>] 0) atTop) (hinf : Tendsto g atTop atTop) :
    (E.muStar g).Nonempty := by
  have hF : ContinuousOn (fun μ => E.eaMu μ * E.UpMu μ (E.epMu μ)) (Ioi 0) := by
    apply ContinuousOn.mul
    · rw [show E.eaMu = fun μ => E.ca.br (E.epMu μ * (E.alphaA * E.Pa)) from
        funext E.eaMu_eq_br]
      exact (E.ca.br_continuous.comp (E.epMu_continuous.mul continuous_const)).continuousOn
    · unfold UpMu
      apply ContinuousOn.sub
      · exact (E.epMu_continuous.mul continuous_const).continuousOn
      · exact ((E.cp.continuous_c.comp E.epMu_continuous).continuousOn).div continuousOn_id
          (fun μ (hμ : 0 < μ) => hμ.ne')
  have hb : ∀ μ, 0 < μ → 0 ≤ E.eaMu μ * E.UpMu μ (E.epMu μ) ∧
      E.eaMu μ * E.UpMu μ (E.epMu μ) ≤ E.Pp := by
    intro μ hμ
    have he0 : 0 ≤ E.eaMu μ := E.ca.br_nonneg _
    have he1 : E.eaMu μ ≤ 1 := E.ca.br_le_one _
    have hU0 := E.UpMu_opt_nonneg hμ
    have hU1 : E.UpMu μ (E.epMu μ) ≤ E.Pp := by
      have hp1 : E.epMu μ ≤ 1 := E.cp.br_le_one _
      have hc : 0 ≤ E.cp.c (E.epMu μ) := E.cp.c_nonneg (E.cp.br_mem _)
      have : 0 ≤ E.cp.c (E.epMu μ) / μ := div_nonneg hc hμ.le
      show E.epMu μ * E.Pp - E.cp.c (E.epMu μ) / μ ≤ E.Pp
      nlinarith [E.Pp_pos]
    exact ⟨mul_nonneg he0 hU0, by nlinarith⟩
  exact Prim.argmaxPos_nonempty hF hb hg h0 hinf

/-- `(v_a, v_p) = (2, 1)` w.p. `1/4`, `(-1, 1)` w.p. `1/4`, `(-1, -3)` w.p. `1/2`:
negative expected values and `α_a^n = 1/2`.  It shares `E(v_a 1_{v_a≥0}) = 1/2`,
`E(v_p 1_{v_p≥0}) = 1/2` and the costs with `EZ` (`α_a^n = 0`). -/
noncomputable def EP : EnvN :=
  mkN ![1/4, 1/4, 1/2] ![(2, 1), (-1, 1), (-1, -3)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three, Set.indicator])
    (by norm_num [Fin.sum_univ_three, Set.indicator])
    (by norm_num [Fin.sum_univ_three, Set.indicator, Cost.quad])
    (by norm_num [Fin.sum_univ_three, Set.indicator, Cost.quad])

lemma EP_integral (f : ℝ × ℝ → ℝ) :
    ∫ v, f v ∂EP.F = 1 / 4 * f (2, 1) + 1 / 4 * f (-1, 1) + 1 / 2 * f (-1, -3) := by
  show ∫ v, f v ∂(discMeasure ![1/4, 1/4, 1/2] ![(2, 1), (-1, 1), (-1, -3)]) = _
  rw [disc_integral _ _ (by intro i; fin_cases i <;> norm_num), Fin.sum_univ_three]
  simp

lemma EP_Ya : EP.Ya = 1 / 4 := by norm_num [Ya, EI, EP_integral, Set.indicator, Regime.dm]
lemma EP_Pa : EP.Pa = 1 / 2 := by norm_num [Pa, EI, EP_integral, Set.indicator, Regime.dm]
lemma EP_Pp : EP.Pp = 1 / 2 := by norm_num [Pp, EI, EP_integral, Set.indicator, Regime.dm]
lemma EP_alphaA : EP.alphaA = 1 / 2 := by rw [alphaA, EP_Ya, EP_Pa]; norm_num
lemma EZ_Pa : EZ.Pa = 1 / 2 := by norm_num [Pa, EI, EZ_integral, Set.indicator, Regime.dm]
lemma EZ_Pp : EZ.Pp = 1 / 2 := by norm_num [Pp, EI, EZ_integral, Set.indicator, Regime.dm]

/-- The hypotheses of `MI.EnvN.prop6_analogue` hold in `EP` with `g = g6`, and `μ*` is
non-empty. -/
theorem nonvacuous_prop6_analogue :
    ∃ (E : EnvN) (g : ℝ → ℝ) (μg : ℝ), 0 < E.alphaA ∧ 0 < μg ∧
      (∀ μ, 0 < μ → g μg ≤ g μ) ∧ DifferentiableAt ℝ g μg ∧ (E.muStar g).Nonempty ∧
      ∀ μ ∈ E.muStar g, μg < μ := by
  have hα : 0 < EP.alphaA := by rw [EP_alphaA]; norm_num
  exact ⟨EP, g6, 1, hα, one_pos, fun _ hμ => g6_min hμ, g6_diff,
    EP.muStar_nonempty g6_cont g6_tendsto_zero g6_tendsto_top,
    EP.prop6_analogue hα one_pos (fun _ hμ => g6_min hμ) g6_diff⟩

/-- The hypotheses of `MI.EnvN.prop5_analogue` hold for `EZ` (`α_a^n = 0`) and `EP`
(`α_a^n = 1/2`) with `g = g6`, and both `μ*` are non-empty. -/
theorem nonvacuous_prop5_analogue :
    ∃ (E E' : EnvN) (g : ℝ → ℝ), E'.Pa = E.Pa ∧ E'.Pp = E.Pp ∧ E'.ca = E.ca ∧ E'.cp = E.cp ∧
      E.alphaA < E'.alphaA ∧ (E.muStar g).Nonempty ∧ (E'.muStar g).Nonempty ∧
      SSOle (E.muStar g) (E'.muStar g) := by
  have hle : EZ.alphaA ≤ EP.alphaA := by rw [EZ_alphaA, EP_alphaA]; norm_num
  have hPa : EP.Pa = EZ.Pa := by rw [EP_Pa, EZ_Pa]
  have hPp : EP.Pp = EZ.Pp := by rw [EP_Pp, EZ_Pp]
  exact ⟨EZ, EP, g6, hPa, hPp, rfl, rfl, by rw [EZ_alphaA, EP_alphaA]; norm_num,
    EZ.muStar_nonempty g6_cont g6_tendsto_zero g6_tendsto_top,
    EP.muStar_nonempty g6_cont g6_tendsto_zero g6_tendsto_top,
    EZ.prop5_analogue EP hPa hPp rfl rfl g6 hle
      (fun h => absurd h (by rw [EZ_alphaA]; exact lt_irrefl 0))⟩

end EnvN

/-! ### Non-vacuity -/

/-- The status-quo cost `g6(2μ)`, minimised at `μ_g = 1/2`. -/
noncomputable def gHalf (μ : ℝ) : ℝ := g6 (2 * μ)

lemma gHalf_min {μ : ℝ} (hμ : 0 < μ) : gHalf (1 / 2) ≤ gHalf μ := by
  unfold gHalf
  rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num]
  exact g6_min (by linarith)

lemma gHalf_cont : ContinuousOn gHalf (Ioi 0) :=
  g6_cont.comp (continuous_const.mul continuous_id).continuousOn
    fun μ (hμ : 0 < μ) => show 0 < 2 * μ by linarith

lemma gHalf_tendsto_zero : Tendsto gHalf (𝓝[>] 0) atTop := by
  have h : Tendsto (fun μ : ℝ => 2 * μ) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous (fun μ : ℝ => 2 * μ) := continuous_const.mul continuous_id
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · exact eventually_nhdsWithin_of_forall fun μ (hμ : 0 < μ) =>
        show 0 < 2 * μ by linarith
  exact g6_tendsto_zero.comp h

lemma gHalf_tendsto_top : Tendsto gHalf atTop atTop :=
  g6_tendsto_top.comp (tendsto_id.const_mul_atTop two_pos)

lemma E1_works_half : 0 < E1.eaMu (1 / 2) := by
  rw [E1.eaMu_eq, E1_alphaA]
  have hp : π0.pMu (1 / 2) = 1 / 4 := by
    unfold Prim.pMu
    rw [π0_Np, π0_cp, Cost.quad_br (by norm_num) (by norm_num)]
    norm_num
  show 0 < π0.eMu (-3 / 2) (1 / 2)
  unfold Prim.eMu
  rw [hp, π0_A, π0_Na]
  apply Cost.br_pos
  norm_num

/-- The hypotheses of `MI.Env.prop5_logconcave` hold in `E1` (`α_a = -3/2`) and `E2`
(`α_a = -1`) with `g = gHalf`, both `μ*` are non-empty, and `E(v_a 1_{v_p≥0}) < 0` in `E1`, so
neither `MI.Env.prop5_curvature` nor `MI.Env.prop5_linear` applies. -/
theorem nonvacuous_prop5_logconcave :
    ∃ (E E' : Env) (g : ℝ → ℝ), E'.prim = E.prim ∧ E.alphaA < E'.alphaA ∧ E'.alphaA < 0 ∧
      ConvexOn ℝ (Icc 0 1) E.ca.d ∧ ConcaveOn ℝ (Ioc 0 1) (fun e => Real.log (E.ca.d e)) ∧
      (∀ μ ∈ E.muStar g, 0 < E.eaMu μ) ∧ E.EI .cen (fun v => v.1) < 0 ∧
      (E.muStar g).Nonempty ∧ (E'.muStar g).Nonempty ∧ SSOle (E.muStar g) (E'.muStar g) := by
  have hcv : ConvexOn ℝ (Icc 0 1) E1.ca.d := Cost.quad_d_convex (k := 2) (by norm_num)
  have hlc : ConcaveOn ℝ (Ioc 0 1) (fun e => Real.log (E1.ca.d e)) :=
    Cost.quad_d_logconcave (k := 2) (by norm_num)
  have hwork := E1.works_of_works_at_min (g := gHalf) (by norm_num) (fun μ hμ => gHalf_min hμ)
    E1_works_half
  have hlt : E1.alphaA ≤ E2.alphaA := by rw [E1_alphaA, E2_alphaA]; norm_num
  refine ⟨E1, E2, gHalf, E2_prim, by rw [E1_alphaA, E2_alphaA]; norm_num,
    by rw [E2_alphaA]; norm_num, hcv, hlc, hwork, ?_,
    E1.muStar_nonempty gHalf_cont gHalf_tendsto_zero gHalf_tendsto_top,
    E2.muStar_nonempty gHalf_cont gHalf_tendsto_zero gHalf_tendsto_top,
    E1.prop5_logconcave E2 E2_prim gHalf hcv hlc hwork hlt⟩
  rw [E1.EI_cen_a, E1_A, E1_Xa]
  norm_num

end MI
