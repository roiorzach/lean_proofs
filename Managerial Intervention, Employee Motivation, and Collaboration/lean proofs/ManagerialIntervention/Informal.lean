import ManagerialIntervention.Threshold

/-!
# Section 3.2: informal delegation (Propositions 5 and 6)

The principal keeps the decision right and chooses a managerial involvement level `μ > 0`
at cost `g(μ)`; her effort cost becomes `c_p(e)/μ`.  Her objective (equation (7)) is
`e_a^c(μ, α_a) · Ũ_p^c(μ) - g(μ)` evaluated at the equilibrium efforts, and `μ*(α_a)` is its
set of maximisers over `μ > 0`.

* `MI.Env.muStar_nonempty` — `μ*` is non-empty when `g` is continuous on `(0, ∞)` and tends
  to `∞` at `0` and at `∞` (the paper's "well-defined" claim, which also needs continuity).
* `MI.Env.prop6` — **Proposition 6**, and `MI.Env.prop6_nonneg`, which extends it to every
  `α_a ≥ 0`.
* `MI.Env.prop5_convex`, `MI.Env.prop5_linear` — **Proposition 5** under extra hypotheses.
  Without them Proposition 5 is false; see `MI.prop5_counterexample`.
-/

namespace MI

open Set Filter Topology

/-- The maximisers of `f` over `μ > 0`. -/
def argmaxPos (f : ℝ → ℝ) : Set ℝ := {μ | 0 < μ ∧ ∀ μ', 0 < μ' → f μ' ≤ f μ}

/-- `S ≤ T` in the strong set order. -/
def SSOle (S T : Set ℝ) : Prop := ∀ x ∈ S, ∀ y ∈ T, min x y ∈ S ∧ max x y ∈ T

/-- Increasing differences give monotone maximisers in the strong set order. -/
theorem sso_of_ID {F : ℝ → ℝ → ℝ} (g : ℝ → ℝ) {α α' : ℝ}
    (hID : ∀ μ μ', 0 < μ → μ ≤ μ' → F α' μ - F α μ ≤ F α' μ' - F α μ') :
    SSOle (argmaxPos fun μ => F α μ - g μ) (argmaxPos fun μ => F α' μ - g μ) := by
  intro x hx y hy
  rcases le_or_gt x y with hxy | hxy
  · rw [min_eq_left hxy, max_eq_right hxy]; exact ⟨hx, hy⟩
  · rw [min_eq_right hxy.le, max_eq_left hxy.le]
    have hID' := hID y x hy.1 hxy.le
    refine ⟨⟨hy.1, fun μ' hμ' => ?_⟩, ⟨hx.1, fun μ' hμ' => ?_⟩⟩
    · have h1 := hx.2 μ' hμ'
      have h2 := hy.2 x hx.1
      simp only at h1 h2 ⊢
      linarith
    · have h1 := hy.2 μ' hμ'
      have h2 := hx.2 y hy.1
      simp only at h1 h2 ⊢
      linarith

/-- For a convex `f`, increments over intervals of a fixed length increase to the right. -/
lemma convex_incr {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {a b L : ℝ} (hab : a ≤ b)
    (hL : 0 ≤ L) (ha : a ∈ s) (hbL : b + L ∈ s) : f (a + L) - f a ≤ f (b + L) - f b := by
  set S := b + L - a with hS
  rcases (show 0 ≤ S by linarith).eq_or_lt with h0 | hpos
  · have hL0 : L = 0 := by linarith
    have hab' : a = b := by linarith
    subst hL0 hab'; simp
  · set t := L / S with ht
    have ht0 : 0 ≤ t := div_nonneg hL hpos.le
    have ht1 : t ≤ 1 := (div_le_one hpos).2 (by linarith)
    have htS : t * S = L := by rw [ht]; field_simp
    have e1 : (1 - t) • a + t • (b + L) = a + L := by
      simp only [smul_eq_mul]; nlinarith [htS]
    have e2 : t • a + (1 - t) • (b + L) = b := by
      simp only [smul_eq_mul]; nlinarith [htS]
    have i1 := hf.2 ha hbL (by linarith : 0 ≤ 1 - t) ht0 (by ring)
    have i2 := hf.2 ha hbL ht0 (by linarith : 0 ≤ 1 - t) (by ring)
    rw [e1] at i1
    rw [e2] at i2
    simp only [smul_eq_mul] at i1 i2
    linarith

/-! ### Reduced form with fixed primitives -/

namespace Prim

variable (π : Prim)

/-- `c_a(1)` large enough for the primitives `π`. -/
def Bounded : Prop := π.A - π.Na ≤ π.ca.d 1

/-- principal effort with involvement `μ` -/
noncomputable def pMu (μ : ℝ) : ℝ := π.cp.br (μ * -π.Np)
/-- the principal's interim payoff `Ũ_p^c(μ)` -/
noncomputable def UMu (μ : ℝ) : ℝ := π.P + π.cp.val (μ * -π.Np) / μ
/-- the agent's effort `e_a^c(μ, α)` -/
noncomputable def eMu (α μ : ℝ) : ℝ := π.ca.br (π.A - α * π.pMu μ * π.Na)
/-- `e_a^c(μ, α) · Ũ_p^c(μ)` -/
noncomputable def FMu (α μ : ℝ) : ℝ := π.eMu α μ * π.UMu μ
/-- `μ*(α)` for primitives `π` and involvement cost `g` -/
def muStar (g : ℝ → ℝ) (α : ℝ) : Set ℝ := argmaxPos fun μ => π.FMu α μ - g μ

variable {π}

lemma pMu_mono (hπ : π.Valid) {μ μ' : ℝ} (h : μ ≤ μ') : π.pMu μ ≤ π.pMu μ' :=
  π.cp.br_mono (by nlinarith [hπ.Np_neg])

lemma pMu_mem (μ : ℝ) : π.pMu μ ∈ Icc (0 : ℝ) 1 := π.cp.br_mem _

lemma pMu_pos (hπ : π.Valid) {μ : ℝ} (hμ : 0 < μ) : 0 < π.pMu μ :=
  π.cp.br_pos (mul_pos hμ (by linarith [hπ.Np_neg]))

/-- `Ũ_p^c(μ) = P + max_e (e (-N_p) - c_p(e)/μ)`, evaluated at the maximiser. -/
lemma UMu_eq {μ : ℝ} (hμ : 0 < μ) :
    π.UMu μ = π.P + (π.pMu μ * -π.Np - π.cp.c (π.pMu μ) / μ) := by
  unfold UMu pMu Cost.val; field_simp

/-- Any effort gives a lower bound for `Ũ_p^c(μ)`. -/
lemma UMu_ge {μ e : ℝ} (hμ : 0 < μ) (he : e ∈ Icc (0 : ℝ) 1) :
    π.P + (e * -π.Np - π.cp.c e / μ) ≤ π.UMu μ := by
  unfold UMu
  have := π.cp.le_val (m := μ * -π.Np) he
  have h2 : e * -π.Np - π.cp.c e / μ = (e * (μ * -π.Np) - π.cp.c e) / μ := by field_simp
  rw [h2]
  have := div_le_div_of_nonneg_right this hμ.le
  linarith

lemma UMu_ge_P {μ : ℝ} (hμ : 0 < μ) : π.P ≤ π.UMu μ := by
  unfold UMu; have := π.cp.val_nonneg (μ * -π.Np); have := div_nonneg this hμ.le; linarith

lemma UMu_pos (hπ : π.Valid) {μ : ℝ} (hμ : 0 < μ) : 0 < π.UMu μ :=
  lt_of_lt_of_le hπ.P_pos (UMu_ge_P hμ)

lemma UMu_le (hπ : π.Valid) {μ : ℝ} (hμ : 0 < μ) : π.UMu μ ≤ π.P + -π.Np := by
  rw [UMu_eq hμ]
  have h1 := π.cp.c_nonneg (pMu_mem (π := π) μ)
  have h2 := (pMu_mem (π := π) μ).2
  have h3 : 0 ≤ π.cp.c (π.pMu μ) / μ := div_nonneg h1 hμ.le
  nlinarith [hπ.Np_neg]

/-- The envelope bound: `Ũ_p^c(μ') - Ũ_p^c(μ) ≥ c_p(e_p(μ)) (1/μ - 1/μ')`. -/
lemma UMu_diff {μ μ' : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ') :
    π.cp.c (π.pMu μ) * (1 / μ - 1 / μ') ≤ π.UMu μ' - π.UMu μ := by
  have h1 := UMu_ge (π := π) hμ' (pMu_mem (π := π) μ)
  rw [UMu_eq hμ]
  have : π.cp.c (π.pMu μ) * (1 / μ - 1 / μ') =
      π.cp.c (π.pMu μ) / μ - π.cp.c (π.pMu μ) / μ' := by ring
  linarith

/-- `Ũ_p^c` is increasing in `μ` (the envelope theorem in the paper). -/
lemma UMu_mono {μ μ' : ℝ} (hμ : 0 < μ) (h : μ ≤ μ') : π.UMu μ ≤ π.UMu μ' := by
  have := UMu_diff (π := π) hμ (lt_of_lt_of_le hμ h)
  have h2 : 0 ≤ π.cp.c (π.pMu μ) * (1 / μ - 1 / μ') :=
    mul_nonneg (π.cp.c_nonneg (pMu_mem μ))
      (sub_nonneg.2 (one_div_le_one_div_of_le hμ h))
  linarith

/-- `Ũ_p^c` is strictly increasing in `μ`. -/
lemma UMu_strict (hπ : π.Valid) {μ μ' : ℝ} (hμ : 0 < μ) (h : μ < μ') : π.UMu μ < π.UMu μ' := by
  have := UMu_diff (π := π) hμ (lt_trans hμ h)
  have hc : 0 < π.cp.c (π.pMu μ) := π.cp.c_pos ⟨pMu_pos hπ hμ, (pMu_mem μ).2⟩
  have h2 : 0 < π.cp.c (π.pMu μ) * (1 / μ - 1 / μ') :=
    mul_pos hc (sub_pos.2 (one_div_lt_one_div_of_lt hμ h))
  linarith

lemma eMu_nonneg (α μ : ℝ) : 0 ≤ π.eMu α μ := π.ca.br_nonneg _

lemma eMu_le_one (α μ : ℝ) : π.eMu α μ ≤ 1 := π.ca.br_le_one _

lemma eMu_pos (hπ : π.Valid) {α : ℝ} (hα : 0 ≤ α) (μ : ℝ) : 0 < π.eMu α μ := by
  apply π.ca.br_pos
  have := (pMu_mem (π := π) μ).1
  nlinarith [hπ.A_pos, hπ.Na_neg, mul_nonneg hα this]

lemma eMu_mono_mu (hπ : π.Valid) {α : ℝ} (hα : 0 ≤ α) {μ μ' : ℝ} (h : μ ≤ μ') :
    π.eMu α μ ≤ π.eMu α μ' := by
  apply π.ca.br_mono
  have := pMu_mono hπ h
  have h2 : 0 ≤ α * (π.pMu μ' - π.pMu μ) * -π.Na :=
    mul_nonneg (mul_nonneg hα (by linarith)) (by linarith [hπ.Na_neg])
  nlinarith

lemma eMu_mono_alpha (hπ : π.Valid) (μ : ℝ) {α α' : ℝ} (h : α ≤ α') :
    π.eMu α μ ≤ π.eMu α' μ := by
  apply π.ca.br_mono
  have := (pMu_mem (π := π) μ).1
  have h2 : 0 ≤ (α' - α) * π.pMu μ * -π.Na :=
    mul_nonneg (mul_nonneg (by linarith) this) (by linarith [hπ.Na_neg])
  nlinarith

lemma FMu_nonneg (hπ : π.Valid) (α : ℝ) {μ : ℝ} (hμ : 0 < μ) : 0 ≤ π.FMu α μ :=
  mul_nonneg (eMu_nonneg α μ) (UMu_pos hπ hμ).le

lemma FMu_le (hπ : π.Valid) (α : ℝ) {μ : ℝ} (hμ : 0 < μ) : π.FMu α μ ≤ π.P + -π.Np := by
  unfold FMu
  have h1 := eMu_le_one (π := π) α μ
  have h2 := eMu_nonneg (π := π) α μ
  have h3 := UMu_pos hπ hμ
  have h4 := UMu_le hπ hμ
  nlinarith

lemma UMu_continuousOn : ContinuousOn π.UMu (Ioi 0) := by
  unfold UMu
  apply continuousOn_const.add
  apply ContinuousOn.div _ continuousOn_id (fun x hx => ne_of_gt hx)
  exact (π.cp.val_continuous.comp (continuous_id.mul continuous_const)).continuousOn

lemma pMu_continuous : Continuous π.pMu :=
  π.cp.br_continuous.comp (continuous_id.mul continuous_const)

lemma FMu_continuousOn (α : ℝ) : ContinuousOn (π.FMu α) (Ioi 0) := by
  unfold FMu eMu
  apply ContinuousOn.mul _ UMu_continuousOn
  exact (π.ca.br_continuous.comp
    (continuous_const.sub ((continuous_const.mul pMu_continuous).mul continuous_const))).continuousOn

/-! #### Existence of a maximiser -/

/-- A maximiser over `(0, ∞)` exists when `F` is continuous and bounded and `g` is continuous
and tends to `∞` at both ends. -/
theorem argmaxPos_nonempty {F g : ℝ → ℝ} {B : ℝ} (hF : ContinuousOn F (Ioi 0))
    (hFb : ∀ μ, 0 < μ → 0 ≤ F μ ∧ F μ ≤ B) (hg : ContinuousOn g (Ioi 0))
    (h0 : Tendsto g (𝓝[>] 0) atTop) (hinf : Tendsto g atTop atTop) :
    (argmaxPos fun μ => F μ - g μ).Nonempty := by
  set T := B + |g 1| + 1 with hT
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h0.eventually (eventually_ge_atTop T))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hinf.eventually (eventually_ge_atTop T))
  have hu0 : 0 < u := hu
  set a := min (u / 2) (1 / 2) with ha
  set b := max N 2 with hb
  have ha0 : 0 < a := lt_min (by linarith) (by norm_num)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hb1 : 1 ≤ b := (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_right _ _)
  have hab : a ≤ b := ha1.trans hb1
  have hsubI : Icc a b ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le ha0 hx.1
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab)
    ((hF.sub hg).mono hsubI)
  rw [isMaxOn_iff] at hmax
  have h1 : (1 : ℝ) ∈ Icc a b := ⟨ha1, hb1⟩
  have hm1 : F 1 - g 1 ≤ F m - g m := hmax 1 h1
  refine ⟨m, hsubI hm, fun μ' hμ' => ?_⟩
  by_cases hin : μ' ∈ Icc a b
  · exact hmax μ' hin
  · have hgT : T ≤ g μ' := by
      rcases not_and_or.1 hin with hlt | hgt
      · push Not at hlt
        exact hsub ⟨hμ', lt_of_lt_of_le hlt ((min_le_left _ _).trans (by linarith))⟩
      · push Not at hgt
        exact hN μ' ((le_max_left _ _).trans hgt.le)
    have hb1' := (hFb μ' hμ').2
    have hF1 := (hFb 1 one_pos).1
    have := le_abs_self (g 1)
    have := neg_abs_le (g 1)
    simp only at this ⊢
    linarith

theorem muStar_nonempty (hπ : π.Valid) (α : ℝ) {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    (h0 : Tendsto g (𝓝[>] 0) atTop) (hinf : Tendsto g atTop atTop) :
    (π.muStar g α).Nonempty :=
  argmaxPos_nonempty (FMu_continuousOn α) (fun _ hμ => ⟨FMu_nonneg hπ α hμ, FMu_le hπ α hμ⟩)
    hg h0 hinf

/-! #### Increasing differences -/

lemma ID_of {α α' μ μ' : ℝ} (hπ : π.Valid) (hμ : 0 < μ) (hμμ : μ ≤ μ')
    (hD : π.eMu α' μ - π.eMu α μ ≤ π.eMu α' μ' - π.eMu α μ') (hαα : α ≤ α') :
    π.FMu α' μ - π.FMu α μ ≤ π.FMu α' μ' - π.FMu α μ' := by
  unfold FMu
  have hU := UMu_mono (π := π) hμ hμμ
  have hU0 := UMu_pos hπ hμ
  have hD0 : 0 ≤ π.eMu α' μ - π.eMu α μ := sub_nonneg.2 (eMu_mono_alpha hπ μ hαα)
  have : (π.eMu α' μ - π.eMu α μ) * π.UMu μ ≤ (π.eMu α' μ' - π.eMu α μ') * π.UMu μ' :=
    mul_le_mul hD hU hU0.le (le_trans hD0 hD)
  linarith

/-- Increasing differences when `h_a` is convex and alignment is non-negative. -/
lemma ID_convex (hπ : π.Valid) (hB : π.Bounded) (hcv : ConvexOn ℝ (Icc 0 (π.ca.d 1)) π.ca.br)
    {α α' : ℝ} (h0 : 0 ≤ α) (hαα : α ≤ α') (h1 : α' ≤ 1) {μ μ' : ℝ} (hμ : 0 < μ)
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
  have hx0 : 0 ≤ x := by
    simp only [x]; nlinarith [mul_nonneg h0 hp0]
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
  have i1 := convex_incr hcv hxx hL ⟨hx0, by linarith⟩ ⟨by linarith, by linarith⟩
  have i2 := π.ca.br_mono (show x' + L ≤ x' + L' by linarith)
  linarith

/-- Increasing differences when `h_a` is affine (e.g. `c_a` quadratic) and the agent's
centralized effort is never truncated at zero (`α ≥ E(v_a)/E(v_a 1_{v_a<0})`). -/
lemma ID_linear (hπ : π.Valid) (hB : π.Bounded)
    (hlin : ∃ k b : ℝ, ∀ x ∈ Icc 0 (π.ca.d 1), π.ca.br x = k * x + b)
    {α α' : ℝ} (h0 : π.A / π.Na ≤ α) (hαα : α ≤ α') (h1 : α' ≤ 1) {μ μ' : ℝ} (hμ : 0 < μ)
    (hμμ : μ ≤ μ') : π.FMu α' μ - π.FMu α μ ≤ π.FMu α' μ' - π.FMu α μ' := by
  apply ID_of hπ hμ hμμ _ hαα
  obtain ⟨k, b, hkb⟩ := hlin
  have hN := hπ.Na_neg
  have hA := hπ.A_pos
  unfold Bounded at hB
  have hd1 : 0 < π.ca.d 1 := π.ca.d_one_pos
  have hk : 0 ≤ k := by
    have e0 := hkb 0 ⟨le_rfl, hd1.le⟩
    have e1 := hkb (π.ca.d 1) ⟨hd1.le, le_rfl⟩
    have := π.ca.br_mono hd1.le
    rw [e0, e1] at this
    nlinarith
  -- `α N_a ≤ A`
  have hαN : α * π.Na ≤ π.A := by
    have := (div_le_iff_of_neg hN).1 h0
    linarith
  have mem : ∀ β p : ℝ, π.A / π.Na ≤ β → β ≤ 1 → p ∈ Icc (0 : ℝ) 1 →
      π.A - β * p * π.Na ∈ Icc 0 (π.ca.d 1) := by
    intro β p hβ0 hβ1 hp
    have hβN : β * π.Na ≤ π.A := by
      have := (div_le_iff_of_neg hN).1 hβ0
      linarith
    constructor
    · rcases le_or_gt 0 (β * π.Na) with hs | hs
      · nlinarith [hp.1, hp.2]
      · nlinarith [hp.1, hp.2]
    · have hβp : β * p ≤ 1 := by
        rcases le_or_gt 0 β with hb0 | hb0
        · nlinarith [hp.1, hp.2]
        · nlinarith [hp.1, hp.2]
      nlinarith
  have hα'0 : π.A / π.Na ≤ α' := h0.trans hαα
  have hα1 : α ≤ 1 := hαα.trans h1
  unfold eMu
  rw [hkb _ (mem α' _ hα'0 h1 (pMu_mem μ)), hkb _ (mem α _ h0 hα1 (pMu_mem μ)),
    hkb _ (mem α' _ hα'0 h1 (pMu_mem μ')), hkb _ (mem α _ h0 hα1 (pMu_mem μ'))]
  have hp := pMu_mono hπ hμμ
  have : 0 ≤ k * ((α' - α) * (π.pMu μ' - π.pMu μ) * -π.Na) :=
    mul_nonneg hk (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  nlinarith

/-! #### Proposition 6 in reduced form -/

/-- With `α ≥ 0`, every maximiser exceeds the minimiser `μ_g` of a cost `g` that is
differentiable at `μ_g`. -/
theorem muStar_gt (hπ : π.Valid) {α : ℝ} (hα : 0 ≤ α) {g : ℝ → ℝ} {μg : ℝ} (hμg : 0 < μg)
    (hmin : ∀ μ, 0 < μ → g μg ≤ g μ) (hdiff : DifferentiableAt ℝ g μg) :
    ∀ μ ∈ π.muStar g α, μg < μ := by
  intro μ hμ
  obtain ⟨hμ0, hmax⟩ := hμ
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · -- `μ < μ_g` is strictly worse than `μ_g`
    have h1 := hmax μg hμg
    have hU := UMu_strict hπ hμ0 hlt
    have he := eMu_mono_mu hπ hα hlt.le
    have he0 := eMu_pos hπ hα μg
    have hU0 := UMu_pos hπ hμ0
    have := hmin μ hμ0
    unfold FMu at h1
    have : π.eMu α μ * π.UMu μ < π.eMu α μg * π.UMu μg :=
      calc π.eMu α μ * π.UMu μ ≤ π.eMu α μg * π.UMu μ := mul_le_mul_of_nonneg_right he hU0.le
        _ < π.eMu α μg * π.UMu μg := mul_lt_mul_of_pos_left hU he0
    linarith
  · -- `μ = μ_g`: a slightly larger `μ` does strictly better, since `g'(μ_g) = 0`
    subst heq
    have hloc : IsLocalMin g μ :=
      IsMinOn.isLocalMin (isMinOn_iff.2 fun x hx => hmin x hx) (Ioi_mem_nhds hμ0)
    have hderiv : HasDerivAt g 0 μ := by
      have := hloc.hasDerivAt_eq_zero hdiff.hasDerivAt
      rw [← this]; exact hdiff.hasDerivAt
    set e0 := π.eMu α μ with he0def
    have he0 : 0 < e0 := eMu_pos hπ hα μ
    have hc : 0 < π.cp.c (π.pMu μ) := π.cp.c_pos ⟨pMu_pos hπ hμ0, (pMu_mem μ).2⟩
    set k := e0 * π.cp.c (π.pMu μ) / (2 * μ ^ 2) with hk
    have hkpos : 0 < k := by positivity
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
    -- the gain in `F`
    have hUd := UMu_diff (π := π) hμ0 hμ''0
    have hrec : d / (2 * μ ^ 2) ≤ 1 / μ - 1 / μ'' := by
      have : 1 / μ - 1 / μ'' = d / (μ * (μ + d)) := by
        simp only [μ'']; field_simp; ring
      rw [this]
      apply div_le_div_of_nonneg_left hd0.le (by positivity)
      nlinarith
    have hFgain : k * d ≤ π.FMu α μ'' - π.FMu α μ := by
      unfold FMu
      have he'' := eMu_mono_mu hπ hα (show μ ≤ μ'' by linarith)
      have hU'' := UMu_pos hπ hμ''0
      have h1 : e0 * π.UMu μ'' ≤ π.eMu α μ'' * π.UMu μ'' := mul_le_mul_of_nonneg_right he'' hU''.le
      have h2 : e0 * (π.cp.c (π.pMu μ) * (d / (2 * μ ^ 2))) ≤ e0 * (π.UMu μ'' - π.UMu μ) := by
        apply mul_le_mul_of_nonneg_left _ he0.le
        exact le_trans (mul_le_mul_of_nonneg_left hrec hc.le) hUd
      have h3 : k * d = e0 * (π.cp.c (π.pMu μ) * (d / (2 * μ ^ 2))) := by
        rw [hk]; field_simp
      rw [← he0def] at *
      nlinarith
    have := hmax μ'' hμ''0
    simp only at this
    nlinarith

/-- Proposition 5 under convexity of `h_a`. -/
theorem muStar_sso_convex (hπ : π.Valid) (hB : π.Bounded)
    (hcv : ConvexOn ℝ (Icc 0 (π.ca.d 1)) π.ca.br) (g : ℝ → ℝ) {α α' : ℝ} (h0 : 0 ≤ α)
    (hαα : α ≤ α') (h1 : α' ≤ 1) : SSOle (π.muStar g α) (π.muStar g α') :=
  sso_of_ID g fun _ _ hμ hμμ => ID_convex hπ hB hcv h0 hαα h1 hμ hμμ

/-- Proposition 5 when `h_a` is affine. -/
theorem muStar_sso_linear (hπ : π.Valid) (hB : π.Bounded)
    (hlin : ∃ k b : ℝ, ∀ x ∈ Icc 0 (π.ca.d 1), π.ca.br x = k * x + b) (g : ℝ → ℝ) {α α' : ℝ}
    (h0 : π.A / π.Na ≤ α) (hαα : α ≤ α') (h1 : α' ≤ 1) :
    SSOle (π.muStar g α) (π.muStar g α') :=
  sso_of_ID g fun _ _ hμ hμμ => ID_linear hπ hB hlin h0 hαα h1 hμ hμμ

end Prim

/-! ### The informal-delegation game in an environment -/

namespace Env

variable (E : Env)

/-- The principal's interim payoff under centralization with involvement `μ`. -/
noncomputable def UpMu (μ e : ℝ) : ℝ :=
  (1 - e) * E.P + e * E.EI .cen (fun v => v.2) - E.cp.c e / μ

/-- Subgame-perfect efforts after the choice of `μ`. -/
def IsEqMu (μ ea ep : ℝ) : Prop := IsBR (E.UpMu μ) ep ∧ IsBR (E.Ua .cen ep) ea

lemma UpMu_eq {μ : ℝ} (hμ : 0 < μ) (e : ℝ) :
    E.UpMu μ e = E.P + μ⁻¹ * (e * (μ * -E.Np) - E.cp.c e) := by
  unfold UpMu; rw [E.EI_cen_p]; field_simp; ring

lemma isBR_UpMu_iff {μ e : ℝ} (hμ : 0 < μ) : IsBR (E.UpMu μ) e ↔ e = E.cp.br (μ * -E.Np) := by
  have : E.UpMu μ = fun e => E.P + μ⁻¹ * (e * (μ * -E.Np) - E.cp.c e) :=
    funext fun e => E.UpMu_eq hμ e
  rw [this]
  exact E.cp.isBR_affine_iff (inv_pos.2 hμ)

/-- Equilibrium principal effort given `μ`. -/
noncomputable def epMu (μ : ℝ) : ℝ := E.cp.br (μ * -E.Np)
/-- Equilibrium agent effort given `μ`. -/
noncomputable def eaMu (μ : ℝ) : ℝ := E.ca.br (E.Va .cen (E.epMu μ))

theorem isEqMu_iff {μ a p : ℝ} (hμ : 0 < μ) : E.IsEqMu μ a p ↔ p = E.epMu μ ∧ a = E.eaMu μ := by
  unfold IsEqMu
  rw [E.isBR_UpMu_iff hμ, E.isBR_Ua_iff]
  constructor
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- The principal's ex-ante objective (7) at the equilibrium efforts. -/
noncomputable def objMu (g : ℝ → ℝ) (μ : ℝ) : ℝ := E.eaMu μ * E.UpMu μ (E.epMu μ) - g μ

/-- `μ*(α_a)`, the profit-maximising involvement levels. -/
def muStar (g : ℝ → ℝ) : Set ℝ := argmaxPos (E.objMu g)

lemma prim_bounded : E.prim.Bounded := E.ca_bound

lemma objMu_eq (g : ℝ → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    E.objMu g μ = E.prim.FMu E.alphaA μ - g μ := by
  unfold objMu Prim.FMu Prim.eMu Prim.UMu Prim.pMu eaMu epMu
  rw [E.UpMu_eq hμ, E.Va_cen, E.Xa_eq]
  simp only [prim, Cost.val]
  congr 1
  congr 1
  · congr 1; ring
  · field_simp

lemma muStar_eq (g : ℝ → ℝ) : E.muStar g = E.prim.muStar g E.alphaA := by
  ext μ
  simp only [muStar, Prim.muStar, argmaxPos, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hμ, h⟩
    refine ⟨hμ, fun μ' hμ' => ?_⟩
    have := h μ' hμ'
    rwa [E.objMu_eq g hμ', E.objMu_eq g hμ] at this
  · rintro ⟨hμ, h⟩
    refine ⟨hμ, fun μ' hμ' => ?_⟩
    rw [E.objMu_eq g hμ', E.objMu_eq g hμ]
    exact h μ' hμ'

/-- `μ*` is non-empty when `g` is continuous on `(0,∞)` with `g → ∞` at `0` and at `∞`. -/
theorem muStar_nonempty {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    (h0 : Tendsto g (𝓝[>] 0) atTop) (hinf : Tendsto g atTop atTop) : (E.muStar g).Nonempty := by
  rw [E.muStar_eq]
  exact Prim.muStar_nonempty E.prim_valid _ hg h0 hinf

/-- **Proposition 6.** If `g` is differentiable with a minimum at `μ_g > 0`, every element of
`μ*(0)` is strictly greater than `μ_g`.  (Only differentiability at `μ_g` is used.) -/
theorem prop6 (hα : E.alphaA = 0) {g : ℝ → ℝ} {μg : ℝ} (hμg : 0 < μg)
    (hmin : ∀ μ, 0 < μ → g μg ≤ g μ) (hdiff : DifferentiableAt ℝ g μg) :
    ∀ μ ∈ E.muStar g, μg < μ := by
  rw [E.muStar_eq]
  exact Prim.muStar_gt E.prim_valid hα.ge hμg hmin hdiff

/-- **Proposition 6, extended.** The same holds for every `α_a ≥ 0`: whenever the agent's
alignment with the principal's decision rule is non-negative, the principal never reduces
her involvement below the status quo (no "absentee managers"). -/
theorem prop6_nonneg (hα : 0 ≤ E.alphaA) {g : ℝ → ℝ} {μg : ℝ} (hμg : 0 < μg)
    (hmin : ∀ μ, 0 < μ → g μg ≤ g μ) (hdiff : DifferentiableAt ℝ g μg) :
    ∀ μ ∈ E.muStar g, μg < μ := by
  rw [E.muStar_eq]
  exact Prim.muStar_gt E.prim_valid hα hμg hmin hdiff

/-- The principal informally delegates (`μ ≤ μ_g`) only when `α_a < 0`, and then doing so
weakly raises the agent's effort relative to the status quo `μ_g`. -/
theorem informal_delegation_motivates {g : ℝ → ℝ} {μg : ℝ} (hμg : 0 < μg)
    (hmin : ∀ μ, 0 < μ → g μg ≤ g μ) (hdiff : DifferentiableAt ℝ g μg) {μ : ℝ}
    (hμ : μ ∈ E.muStar g) (hle : μ ≤ μg) : E.alphaA < 0 ∧ E.eaMu μg ≤ E.eaMu μ := by
  have hneg : E.alphaA < 0 := by
    by_contra h
    push Not at h
    have := E.prop6_nonneg h hμg hmin hdiff μ hμ
    linarith
  refine ⟨hneg, ?_⟩
  unfold eaMu
  apply E.ca.br_mono
  rw [E.Va_cen, E.Va_cen]
  have hX : 0 < E.Xa := E.alphaA_neg_iff.1 hneg
  have : E.epMu μ ≤ E.epMu μg := E.cp.br_mono (by nlinarith [E.Np_neg])
  nlinarith

/-- **Proposition 5 (corrected), convex case.** Fix the primitives and `g`.  If `h_a = (c_a')⁻¹`
is convex and `0 ≤ α_a ≤ α_a'`, then `μ*(α_a) ≤ μ*(α_a')` in the strong set order. -/
theorem prop5_convex (E' : Env) (hprim : E'.prim = E.prim) (g : ℝ → ℝ)
    (hcv : ConvexOn ℝ (Icc 0 (E.ca.d 1)) E.ca.br) (h0 : 0 ≤ E.alphaA)
    (hle : E.alphaA ≤ E'.alphaA) : SSOle (E.muStar g) (E'.muStar g) := by
  rw [E.muStar_eq, E'.muStar_eq, hprim]
  exact Prim.muStar_sso_convex E.prim_valid E.prim_bounded hcv g h0 hle E'.alphaA_le_one

/-- **Proposition 5 (corrected), affine case.** Fix the primitives and `g`.  If `h_a` is affine
(e.g. `c_a` quadratic) and `E(v_a)/E(v_a 1_{v_a<0}) ≤ α_a ≤ α_a'`, then
`μ*(α_a) ≤ μ*(α_a')` in the strong set order. -/
theorem prop5_linear (E' : Env) (hprim : E'.prim = E.prim) (g : ℝ → ℝ)
    (hlin : ∃ k b : ℝ, ∀ x ∈ Icc 0 (E.ca.d 1), E.ca.br x = k * x + b)
    (h0 : E.A / E.Na ≤ E.alphaA) (hle : E.alphaA ≤ E'.alphaA) :
    SSOle (E.muStar g) (E'.muStar g) := by
  rw [E.muStar_eq, E'.muStar_eq, hprim]
  exact Prim.muStar_sso_linear E.prim_valid E.prim_bounded hlin g h0 hle E'.alphaA_le_one

end Env

end MI
