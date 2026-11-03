import NoisyVD.Gaussian

/-!
# Lemma `lemma_threshold_cutoff`

The objects `V(t)`, `𝒰(t)`, `τ` and `\bar F_0`.  Everything here depends only on `π = pr`, `H`,
`ℓ = |L|` and `S = σ² = F(0)(1-F(0))`.  As in the paper, the set `S = τ(D)` is shown to be upward closed
by the Intermediate Value Theorem along a ray, and `inf_D τ > 0` follows from an explicit lower bound.
-/

open Set Filter Topology Real

namespace NoisyVD

/-- `W(u₁, u₀) = π H Φ(-u₁) - (1-π) ℓ Φ(-u₀)`. -/
noncomputable def Wval (pr H l : ℝ) (u₁ u₀ : ℝ) : ℝ := pr * H * Phi (-u₁) - (1 - pr) * l * Phi (-u₀)

/-- The feasible set `𝒰(t)` of equation `eq_feasible_u`. -/
def feasible (H l S t : ℝ) : Set (ℝ × ℝ) :=
  {u | u.1 + t * H / S * phi u.1 = u.2 - t * l / S * phi u.2}

/-- `V(t)` of equation `eq_threshold_value`. -/
noncomputable def Vval (pr H l S t : ℝ) : ℝ :=
  sSup ((fun u : ℝ × ℝ => Wval pr H l u.1 u.2) '' feasible H l S t)

/-- `τ(u₁, u₀)`. -/
noncomputable def tau (H l S u₁ u₀ : ℝ) : ℝ := S * (u₀ - u₁) / (H * phi u₁ + l * phi u₀)

/-- The region `D` on which the decision-maker gains over the status quo. -/
def domainD (pr H l : ℝ) : Set (ℝ × ℝ) := {u | 0 < Wval pr H l u.1 u.2}

/-- The cutoff `\bar F_0`, a function of `π, H, |L|` and `σ²` only. -/
noncomputable def Fbar (pr H l S : ℝ) : ℝ :=
  sInf ((fun u : ℝ × ℝ => tau H l S u.1 u.2) '' domainD pr H l)

/-- The maintained parameter restrictions of the Volunteer's Dilemma. -/
structure Par (pr H l S : ℝ) : Prop where
  pr0 : 0 < pr
  pr1 : pr < 1
  H0 : 0 < H
  l0 : 0 < l
  S0 : 0 < S
  prior : pr * H < (1 - pr) * l

/-! ### Gaussian auxiliaries -/

lemma phi_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : phi y ≤ phi x := by
  unfold phi
  have h := sqrt_two_pi_pos
  have : exp (-y ^ 2 / 2) ≤ exp (-x ^ 2 / 2) := by
    apply Real.exp_le_exp.2
    nlinarith
  exact mul_le_mul_of_nonneg_left this (by positivity)

lemma Phi_mvt {a b : ℝ} (hab : a < b) : ∃ ξ ∈ Ioo a b, Phi b - Phi a = phi ξ * (b - a) := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope Phi phi hab continuous_Phi.continuousOn
    (fun x _ => hasDerivAt_Phi x)
  refine ⟨ξ, hξ, ?_⟩
  have hd : b - a ≠ 0 := by linarith [sub_pos.2 hab]
  rw [h]
  field_simp

lemma qdiff {u₁ u₀ : ℝ} : Phi (-u₁) - Phi (-u₀) = Phi u₀ - Phi u₁ := by
  rw [Phi_neg, Phi_neg]; ring

lemma Phi_neg_anti {x y : ℝ} (h : x ≤ y) : Phi (-y) ≤ Phi (-x) := Phi_mono (by linarith)

/-- The Mills-ratio bound: `φ(u)²/q(u) ≤ φ(0) e^{3/2}` for `u ≥ 1`. -/
lemma phi_sq_le {u : ℝ} (hu : 1 ≤ u) : phi u ^ 2 ≤ phi 0 * exp (3 / 2) * Phi (-u) := by
  have hu0 : 0 < u := by linarith
  have hb : u < u + u⁻¹ := by
    have : 0 < u⁻¹ := by positivity
    linarith
  obtain ⟨ξ, hξ, hmvt⟩ := Phi_mvt hb
  have hξ2 : phi (u + u⁻¹) ≤ phi ξ := phi_anti (by linarith [hξ.1]) hξ.2.le
  have hq : u⁻¹ * phi (u + u⁻¹) ≤ Phi (-u) := by
    rw [Phi_neg]
    have h1 := Phi_le_one (u + u⁻¹)
    have h2 : (u + u⁻¹ - u) = u⁻¹ := by ring
    rw [h2] at hmvt
    have h3 : u⁻¹ * phi (u + u⁻¹) ≤ u⁻¹ * phi ξ :=
      mul_le_mul_of_nonneg_left hξ2 (by positivity)
    linarith [mul_comm (phi ξ) u⁻¹]
  have hexp : phi (u + u⁻¹) = phi u * exp (-(1 + 1 / (2 * u ^ 2))) := by
    unfold phi
    rw [mul_assoc, ← exp_add]
    congr 2
    field_simp
    ring
  have hexp2 : exp (1 + 1 / (2 * u ^ 2)) ≤ exp (3 / 2) := by
    apply Real.exp_le_exp.2
    have : 1 / (2 * u ^ 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hφ := phi_pos u
  have hE : 0 < exp (1 + 1 / (2 * u ^ 2)) := exp_pos _
  have hinv : exp (-(1 + 1 / (2 * u ^ 2))) * exp (1 + 1 / (2 * u ^ 2)) = 1 := by
    rw [← exp_add]; simp
  have h1 : phi u ≤ u * exp (1 + 1 / (2 * u ^ 2)) * Phi (-u) := by
    have h2 : u⁻¹ * (phi u * exp (-(1 + 1 / (2 * u ^ 2)))) ≤ Phi (-u) := by
      rw [← hexp]; exact hq
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ u * exp (1 + 1 / (2 * u ^ 2)) by positivity)
    have hu1 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0.ne'
    have h4 : u * exp (1 + 1 / (2 * u ^ 2)) * (u⁻¹ * (phi u * exp (-(1 + 1 / (2 * u ^ 2))))) = phi u := by
      calc _ = (u * u⁻¹) * phi u * (exp (-(1 + 1 / (2 * u ^ 2))) * exp (1 + 1 / (2 * u ^ 2))) := by ring
        _ = phi u := by rw [hu1, hinv]; ring
    rw [h4] at h3
    exact h3
  have hq0 : 0 < Phi (-u) := Phi_pos _
  have huφ := u_mul_phi_le hu0.le
  have hφ0 := phi_pos 0
  calc phi u ^ 2 = phi u * phi u := by ring
    _ ≤ phi u * (u * exp (1 + 1 / (2 * u ^ 2)) * Phi (-u)) := mul_le_mul_of_nonneg_left h1 hφ.le
    _ = (u * phi u) * exp (1 + 1 / (2 * u ^ 2)) * Phi (-u) := by ring
    _ ≤ phi 0 * exp (3 / 2) * Phi (-u) := by gcongr

variable {pr H l S : ℝ}

lemma P_pos (hp : Par pr H l S) (u₁ u₀ : ℝ) : 0 < H * phi u₁ + l * phi u₀ :=
  add_pos (mul_pos hp.H0 (phi_pos _)) (mul_pos hp.l0 (phi_pos _))

lemma Wval_le (hp : Par pr H l S) (u₁ u₀ : ℝ) : Wval pr H l u₁ u₀ ≤ pr * H := by
  unfold Wval
  have h1 := Phi_le_one (-u₁)
  have h2 := Phi_pos (-u₀)
  have h3 : 0 < pr * H := mul_pos hp.pr0 hp.H0
  have h4 : 0 < (1 - pr) * l := mul_pos (by linarith [hp.pr1]) hp.l0
  nlinarith [mul_pos h4 h2]

lemma continuous_Wval (pr H l : ℝ) : Continuous fun u : ℝ × ℝ => Wval pr H l u.1 u.2 := by
  unfold Wval
  have h1 : Continuous fun u : ℝ × ℝ => Phi (-u.1) := continuous_Phi.comp continuous_fst.neg
  have h2 : Continuous fun u : ℝ × ℝ => Phi (-u.2) := continuous_Phi.comp continuous_snd.neg
  exact (continuous_const.mul h1).sub (continuous_const.mul h2)

lemma isOpen_domainD (pr H l : ℝ) : IsOpen (domainD pr H l) :=
  isOpen_lt continuous_const (continuous_Wval pr H l)

lemma bddAbove_W (hp : Par pr H l S) (t : ℝ) :
    BddAbove ((fun u : ℝ × ℝ => Wval pr H l u.1 u.2) '' feasible H l S t) :=
  ⟨pr * H, by rintro y ⟨u, _, rfl⟩; exact Wval_le hp _ _⟩

/-- On `D` we have `u₀ > u₁`. -/
lemma lt_of_mem_D (hp : Par pr H l S) {u : ℝ × ℝ} (hu : u ∈ domainD pr H l) : u.1 < u.2 := by
  by_contra hcon
  push Not at hcon
  have h1 : Phi (-u.1) ≤ Phi (-u.2) := Phi_neg_anti hcon
  have h2 := Phi_pos (-u.1)
  have h3 : 0 < (1 - pr) * l := mul_pos (by linarith [hp.pr1]) hp.l0
  have hu' : 0 < pr * H * Phi (-u.1) - (1 - pr) * l * Phi (-u.2) := hu
  have h4 := hp.prior
  nlinarith

/-- `τ` characterises feasibility. -/
lemma mem_feasible_iff (hp : Par pr H l S) (t : ℝ) (u₁ u₀ : ℝ) :
    (u₁, u₀) ∈ feasible H l S t ↔ t = tau H l S u₁ u₀ := by
  have hS := hp.S0
  have hP := P_pos hp u₁ u₀
  show u₁ + t * H / S * phi u₁ = u₀ - t * l / S * phi u₀ ↔ _
  unfold tau
  rw [eq_div_iff hP.ne']
  constructor
  · intro h
    field_simp at h
    nlinarith
  · intro h
    field_simp
    nlinarith

/-- `V(t) > 0` iff `t ∈ τ(D)`. -/
lemma Vval_pos_iff (hp : Par pr H l S) (t : ℝ) :
    0 < Vval pr H l S t ↔ t ∈ (fun u : ℝ × ℝ => tau H l S u.1 u.2) '' domainD pr H l := by
  constructor
  · intro h
    have hne : ((fun u : ℝ × ℝ => Wval pr H l u.1 u.2) '' feasible H l S t).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      unfold Vval at h
      rw [hne, Real.sSup_empty] at h
      exact lt_irrefl _ h
    obtain ⟨y, ⟨u, hu, rfl⟩, hy⟩ := exists_lt_of_lt_csSup hne h
    refine ⟨u, hy, ?_⟩
    obtain ⟨u₁, u₀⟩ := u
    exact ((mem_feasible_iff hp t u₁ u₀).1 hu).symm
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨u₁, u₀⟩ := u
    have hmem : (u₁, u₀) ∈ feasible H l S (tau H l S u₁ u₀) := (mem_feasible_iff hp _ u₁ u₀).2 rfl
    have := le_csSup (bddAbove_W hp _) (mem_image_of_mem (fun u : ℝ × ℝ => Wval pr H l u.1 u.2) hmem)
    exact lt_of_lt_of_le hu this

/-- The image of `D` under `τ` is upward closed: IVT along the ray `u₀ ↦ τ(u₁, u₀)`. -/
lemma upward_closed (hp : Par pr H l S) {t t' : ℝ}
    (ht : t ∈ (fun u : ℝ × ℝ => tau H l S u.1 u.2) '' domainD pr H l) (htt' : t < t') :
    t' ∈ (fun u : ℝ × ℝ => tau H l S u.1 u.2) '' domainD pr H l := by
  obtain ⟨⟨u₁, u₀⟩, hD, rfl⟩ := ht
  have hlt := lt_of_mem_D hp hD
  have hS := hp.S0
  have hl := hp.l0
  have hH := hp.H0
  have hc : Continuous fun x => tau H l S u₁ x := by
    unfold tau
    refine ((continuous_const.mul (continuous_id.sub continuous_const))).div
      (continuous_const.add (continuous_const.mul continuous_phi)) fun x => (P_pos hp u₁ x).ne'
  -- a large point
  set C : ℝ := (H + l) * phi 0 with hC
  have hC0 : 0 < C := mul_pos (by linarith) (phi_pos 0)
  set x : ℝ := max u₀ (u₁ + t' * C / S + 1) with hx
  have hx1 : u₀ ≤ x := le_max_left _ _
  have hx2 : u₁ + t' * C / S + 1 ≤ x := le_max_right _ _
  have hlarge : t' ≤ tau H l S u₁ x := by
    unfold tau
    have hP := P_pos hp u₁ x
    have hPle : H * phi u₁ + l * phi x ≤ C := by
      rw [hC, add_mul]
      have h1 := phi_le u₁
      have h2 := phi_le x
      gcongr
    rw [le_div_iff₀ hP]
    have htp : t' * C / S + 1 ≤ x - u₁ := by linarith
    have ht'pos : 0 < t' ∨ t' ≤ 0 := lt_or_ge 0 t'
    rcases ht'pos with h | h
    · have h1 : t' * C / S ≤ x - u₁ := by linarith
      have h2 : t' * C ≤ S * (x - u₁) := by
        rw [div_le_iff₀ hS] at h1
        linarith
      have h3 : t' * (H * phi u₁ + l * phi x) ≤ t' * C := mul_le_mul_of_nonneg_left hPle h.le
      linarith
    · -- `t' ≤ 0` is impossible since `τ > 0` on `D` and `t < t'`
      have hτ : 0 < tau H l S u₁ u₀ := by
        unfold tau
        exact div_pos (mul_pos hS (by simpa using hlt)) (P_pos hp _ _)
      have : tau H l S u₁ u₀ < 0 := lt_of_lt_of_le htt' h
      linarith
  obtain ⟨y, hy, hyeq⟩ := intermediate_value_Icc hx1 hc.continuousOn
    (show t' ∈ Icc (tau H l S u₁ u₀) (tau H l S u₁ x) from ⟨htt'.le, hlarge⟩)
  refine ⟨(u₁, y), ?_, hyeq⟩
  -- `Φ(-y)` decreases in `y`
  have hD' : 0 < pr * H * Phi (-u₁) - (1 - pr) * l * Phi (-u₀) := hD
  show 0 < pr * H * Phi (-u₁) - (1 - pr) * l * Phi (-y)
  have h1 : Phi (-y) ≤ Phi (-u₀) := Phi_neg_anti hy.1
  have h2 : 0 < (1 - pr) * l := mul_pos (by linarith [hp.pr1]) hl
  nlinarith

/-- The explicit lower bound for `τ` on `D`. -/
noncomputable def tauLower (pr H l S : ℝ) : ℝ :=
  let ρ := pr * H / ((1 - pr) * l)
  min (S * (1 - ρ) * Phi (-1) / ((H + l) * phi 0 ^ 2))
    (S * (1 - ρ) / ((H + l) * (phi 0 * exp (3 / 2))))

lemma tauLower_pos (hp : Par pr H l S) : 0 < tauLower pr H l S := by
  have h2 : 0 < (1 - pr) * l := mul_pos (by linarith [hp.pr1]) hp.l0
  have hρ : pr * H / ((1 - pr) * l) < 1 := by
    rw [div_lt_one h2]; exact hp.prior
  have hS := hp.S0
  have hHl : 0 < H + l := add_pos hp.H0 hp.l0
  have hφ := phi_pos 0
  have hE := exp_pos (3 / 2 : ℝ)
  have hq := Phi_pos (-1)
  have h1ρ : 0 < 1 - pr * H / ((1 - pr) * l) := by linarith
  unfold tauLower
  exact lt_min (by positivity) (by positivity)

/-- `inf_D τ > 0`, explicitly. -/
lemma tauLower_le (hp : Par pr H l S) {u : ℝ × ℝ} (hu : u ∈ domainD pr H l) :
    tauLower pr H l S ≤ tau H l S u.1 u.2 := by
  obtain ⟨u₁, u₀⟩ := u
  have hlt : u₁ < u₀ := lt_of_mem_D hp hu
  have hu' : 0 < pr * H * Phi (-u₁) - (1 - pr) * l * Phi (-u₀) := hu
  have hS := hp.S0
  have hHl : 0 < H + l := add_pos hp.H0 hp.l0
  have hh2 : 0 < (1 - pr) * l := mul_pos (by linarith [hp.pr1]) hp.l0
  set ρ := pr * H / ((1 - pr) * l) with hρ
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hh2]; exact hp.prior
  have hd : 0 < u₀ - u₁ := by linarith
  have hP := P_pos hp u₁ u₀
  have hq1 := Phi_pos (-u₁)
  -- `q(u₀) < ρ q(u₁)`, so `q(u₁) - q(u₀) > (1-ρ) q(u₁)`
  have hq : (1 - ρ) * Phi (-u₁) < Phi (-u₁) - Phi (-u₀) := by
    have h3 : Phi (-u₀) < ρ * Phi (-u₁) := by
      rw [hρ, div_mul_eq_mul_div, lt_div_iff₀ hh2]
      linarith
    linarith
  rw [qdiff] at hq
  obtain ⟨ξ, hξ, hmvt⟩ := Phi_mvt hlt
  rw [hmvt] at hq
  have hφ0 := phi_pos 0
  by_cases hc : u₁ < 1
  · -- the bounded regime
    refine (min_le_left _ _).trans ?_
    have hq1' : Phi (-1) ≤ Phi (-u₁) := Phi_neg_anti hc.le
    have h1 : phi ξ ≤ phi 0 := phi_le ξ
    have h2 : (1 - ρ) * Phi (-1) ≤ phi 0 * (u₀ - u₁) := by
      have h3 : (1 - ρ) * Phi (-1) ≤ (1 - ρ) * Phi (-u₁) :=
        mul_le_mul_of_nonneg_left hq1' (by linarith)
      have h4 : phi ξ * (u₀ - u₁) ≤ phi 0 * (u₀ - u₁) := mul_le_mul_of_nonneg_right h1 hd.le
      linarith
    have hPle : H * phi u₁ + l * phi u₀ ≤ (H + l) * phi 0 := by
      have h5 := phi_le u₁
      have h6 := phi_le u₀
      have := mul_le_mul_of_nonneg_left h5 hp.H0.le
      have := mul_le_mul_of_nonneg_left h6 hp.l0.le
      linarith
    unfold tau
    rw [div_le_div_iff₀ (by positivity) hP]
    have h7 : S * ((1 - ρ) * Phi (-1)) * (H * phi u₁ + l * phi u₀)
        ≤ S * (phi 0 * (u₀ - u₁)) * ((H + l) * phi 0) := by
      gcongr
    nlinarith
  · -- the tail regime
    push Not at hc
    refine (min_le_right _ _).trans ?_
    have hu1 : 0 ≤ u₁ := by linarith
    have h1 : phi ξ ≤ phi u₁ := phi_anti hu1 hξ.1.le
    have h2 : (1 - ρ) * Phi (-u₁) ≤ phi u₁ * (u₀ - u₁) := by
      have h4 : phi ξ * (u₀ - u₁) ≤ phi u₁ * (u₀ - u₁) := mul_le_mul_of_nonneg_right h1 hd.le
      linarith
    have hφu := phi_pos u₁
    have hPle : H * phi u₁ + l * phi u₀ ≤ (H + l) * phi u₁ := by
      have h6 : phi u₀ ≤ phi u₁ := phi_anti hu1 hlt.le
      have := mul_le_mul_of_nonneg_left h6 hp.l0.le
      linarith
    have hms := phi_sq_le hc
    set K₀ := phi 0 * exp (3 / 2) with hK₀
    have hK₀pos : 0 < K₀ := by rw [hK₀]; positivity
    have h1ρ : 0 ≤ 1 - ρ := by linarith
    unfold tau
    rw [div_le_div_iff₀ (by positivity) hP]
    -- `(1-ρ) φ² ≤ (1-ρ) K₀ q ≤ K₀ φ d`, hence `(1-ρ) φ ≤ K₀ d`
    have h3 : (1 - ρ) * phi u₁ ≤ K₀ * (u₀ - u₁) := by
      have h4 : (1 - ρ) * phi u₁ ^ 2 ≤ K₀ * ((1 - ρ) * Phi (-u₁)) := by
        have := mul_le_mul_of_nonneg_left hms h1ρ
        nlinarith
      have h5 : K₀ * ((1 - ρ) * Phi (-u₁)) ≤ K₀ * (phi u₁ * (u₀ - u₁)) :=
        mul_le_mul_of_nonneg_left h2 hK₀pos.le
      have h6 : phi u₁ * ((1 - ρ) * phi u₁) ≤ phi u₁ * (K₀ * (u₀ - u₁)) := by nlinarith
      exact le_of_mul_le_mul_left h6 hφu
    have h7 : S * (1 - ρ) * (H * phi u₁ + l * phi u₀) ≤ S * (1 - ρ) * ((H + l) * phi u₁) :=
      mul_le_mul_of_nonneg_left hPle (mul_nonneg hS.le h1ρ)
    have h8 : S * (1 - ρ) * ((H + l) * phi u₁) ≤ S * (u₀ - u₁) * ((H + l) * K₀) := by
      have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hS.le hHl.le)
      nlinarith
    linarith

lemma domainD_nonempty (hp : Par pr H l S) : (domainD pr H l).Nonempty := by
  have h : Tendsto (fun x : ℝ => Phi (-x)) atTop (𝓝 0) := tendsto_Phi_atBot.comp tendsto_neg_atTop_atBot
  have hpos : 0 < pr * H * Phi (-0) := mul_pos (mul_pos hp.pr0 hp.H0) (Phi_pos _)
  have h2 : 0 < (1 - pr) * l := mul_pos (by linarith [hp.pr1]) hp.l0
  have hev := (tendsto_order.1 h).2 (pr * H * Phi (-0) / ((1 - pr) * l)) (div_pos hpos h2)
  obtain ⟨x, hx⟩ := hev.exists
  refine ⟨(0, x), ?_⟩
  show 0 < pr * H * Phi (-0) - (1 - pr) * l * Phi (-x)
  rw [lt_div_iff₀ h2] at hx
  linarith

/-- The infimum of `τ` over `D` is not attained: first-order conditions in each coordinate give
`u₁ > 0` and `u₀ < 0`, contradicting `u₀ > u₁`. -/
lemma not_attained (hp : Par pr H l S) {u : ℝ × ℝ} (hu : u ∈ domainD pr H l)
    (hmin : ∀ v ∈ domainD pr H l, tau H l S u.1 u.2 ≤ tau H l S v.1 v.2) : False := by
  obtain ⟨u₁, u₀⟩ := u
  have hlt : u₁ < u₀ := lt_of_mem_D hp hu
  have hS := hp.S0
  have hd : 0 < u₀ - u₁ := by linarith
  have hP := P_pos hp u₁ u₀
  have hopen := isOpen_domainD pr H l
  have hHp := hp.H0
  have hlp := hp.l0
  -- slice in `u₁`
  have h1 : IsLocalMin (fun x => tau H l S x u₀) u₁ := by
    have hc : ContinuousAt (fun x : ℝ => (x, u₀)) u₁ := by fun_prop
    have hev := hc.eventually (hopen.mem_nhds hu)
    filter_upwards [hev] with x hx
    exact hmin (x, u₀) hx
  have hd1 : HasDerivAt (fun x => tau H l S x u₀)
      ((S * (-1) * (H * phi u₁ + l * phi u₀) - S * (u₀ - u₁) * (H * (-u₁ * phi u₁)))
        / (H * phi u₁ + l * phi u₀) ^ 2) u₁ := by
    unfold tau
    have hn : HasDerivAt (fun x => S * (u₀ - x)) (S * (-1)) u₁ :=
      ((hasDerivAt_id u₁).const_sub u₀).const_mul S
    have hm : HasDerivAt (fun x => H * phi x + l * phi u₀) (H * (-u₁ * phi u₁)) u₁ :=
      ((hasDerivAt_phi u₁).const_mul H).add_const _
    exact hn.div hm hP.ne'
  have hz1 := h1.hasDerivAt_eq_zero hd1
  rw [div_eq_zero_iff] at hz1
  have hz1' : S * (-1) * (H * phi u₁ + l * phi u₀) - S * (u₀ - u₁) * (H * (-u₁ * phi u₁)) = 0 := by
    rcases hz1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 hP.ne')
  have hu1pos : 0 < u₁ := by
    have h3 : (u₀ - u₁) * (H * (u₁ * phi u₁)) = H * phi u₁ + l * phi u₀ := by
      have h4 : S * ((u₀ - u₁) * (H * (u₁ * phi u₁)) - (H * phi u₁ + l * phi u₀)) = 0 := by
        linear_combination hz1'
      have := (mul_eq_zero.1 h4).resolve_left hS.ne'
      linarith
    by_contra hcon
    push Not at hcon
    have h5 : (u₀ - u₁) * (H * (u₁ * phi u₁)) ≤ 0 := by
      have h6 : u₁ * phi u₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon (phi_pos _).le
      have h7 : H * (u₁ * phi u₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hHp.le h6
      exact mul_nonpos_of_nonneg_of_nonpos hd.le h7
    linarith
  -- slice in `u₀`
  have h2 : IsLocalMin (fun x => tau H l S u₁ x) u₀ := by
    have hc : ContinuousAt (fun x : ℝ => (u₁, x)) u₀ := by fun_prop
    have hev := hc.eventually (hopen.mem_nhds hu)
    filter_upwards [hev] with x hx
    exact hmin (u₁, x) hx
  have hd2 : HasDerivAt (fun x => tau H l S u₁ x)
      ((S * 1 * (H * phi u₁ + l * phi u₀) - S * (u₀ - u₁) * (l * (-u₀ * phi u₀)))
        / (H * phi u₁ + l * phi u₀) ^ 2) u₀ := by
    unfold tau
    have hn : HasDerivAt (fun x => S * (x - u₁)) (S * 1) u₀ :=
      ((hasDerivAt_id u₀).sub_const u₁).const_mul S
    have hm : HasDerivAt (fun x => H * phi u₁ + l * phi x) (l * (-u₀ * phi u₀)) u₀ :=
      ((hasDerivAt_phi u₀).const_mul l).const_add _
    exact hn.div hm hP.ne'
  have hz2 := h2.hasDerivAt_eq_zero hd2
  rw [div_eq_zero_iff] at hz2
  have hz2' : S * 1 * (H * phi u₁ + l * phi u₀) - S * (u₀ - u₁) * (l * (-u₀ * phi u₀)) = 0 := by
    rcases hz2 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 hP.ne')
  have hu0pos : 0 < u₀ := by linarith
  have h8 : 0 < S * (H * phi u₁ + l * phi u₀) := mul_pos hS hP
  have h9 : 0 ≤ S * (u₀ - u₁) * (l * (u₀ * phi u₀)) := by
    have := phi_pos u₀
    positivity
  nlinarith

/-- **Lemma `lemma_threshold_cutoff`.** -/
theorem lemma_threshold_cutoff (hp : Par pr H l S) :
    0 < Fbar pr H l S ∧ ∀ t : ℝ, 0 < t → (0 < Vval pr H l S t ↔ Fbar pr H l S < t) := by
  have hne : ((fun u : ℝ × ℝ => tau H l S u.1 u.2) '' domainD pr H l).Nonempty :=
    (domainD_nonempty hp).image _
  have hbdd : BddBelow ((fun u : ℝ × ℝ => tau H l S u.1 u.2) '' domainD pr H l) :=
    ⟨tauLower pr H l S, by rintro y ⟨u, hu, rfl⟩; exact tauLower_le hp hu⟩
  have hpos : 0 < Fbar pr H l S := by
    refine lt_of_lt_of_le (tauLower_pos hp) ?_
    refine le_csInf hne ?_
    rintro y ⟨u, hu, rfl⟩
    exact tauLower_le hp hu
  refine ⟨hpos, fun t _ => ?_⟩
  rw [Vval_pos_iff hp]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine lt_of_le_of_ne (csInf_le hbdd ⟨u, hu, rfl⟩) fun heq => ?_
    refine not_attained hp hu fun v hv => ?_
    have h1 : Fbar pr H l S ≤ tau H l S v.1 v.2 := csInf_le hbdd ⟨v, hv, rfl⟩
    simp only at heq
    rw [← heq]
    exact h1
  · intro ht
    obtain ⟨y, hy, hyt⟩ := exists_lt_of_csInf_lt hne ht
    exact upward_closed hp hy hyt

/-- The function `f_ω(u) = u + κ φ(u)` is onto, with a uniform bound on the solution. -/
lemma exists_solution (κ c : ℝ) : ∃ u, u + κ * phi u = c ∧ |u - c| ≤ |κ| * phi 0 := by
  have hb : ∀ x, |κ * phi x| ≤ |κ| * phi 0 := fun x => by
    rw [abs_mul, abs_of_pos (phi_pos x)]
    exact mul_le_mul_of_nonneg_left (phi_le x) (abs_nonneg κ)
  set K := |κ| * phi 0 with hK
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _) (phi_pos 0).le
  have hc : Continuous fun u => u + κ * phi u := continuous_id.add (continuous_const.mul continuous_phi)
  have h1 : c - K + κ * phi (c - K) ≤ c := by
    have := abs_le.1 (hb (c - K)); linarith [this.2]
  have h2 : c ≤ c + K + κ * phi (c + K) := by
    have := abs_le.1 (hb (c + K)); linarith [this.1]
  obtain ⟨u, hu, hue⟩ := intermediate_value_Icc (show c - K ≤ c + K by linarith) hc.continuousOn
    (show c ∈ Icc _ _ from ⟨h1, h2⟩)
  refine ⟨u, hue, ?_⟩
  rw [abs_le]
  constructor <;> linarith [hu.1, hu.2]

/-- Feasible pairs exist for every level `c`. -/
lemma exists_feasible_level (H l S t c : ℝ) :
    ∃ u : ℝ × ℝ, u ∈ feasible H l S t ∧ u.1 + t * H / S * phi u.1 = c ∧
      |u.1 - c| ≤ |t * H / S| * phi 0 ∧ |u.2 - c| ≤ |t * l / S| * phi 0 := by
  obtain ⟨u₁, h1, h1'⟩ := exists_solution (t * H / S) c
  obtain ⟨u₀, h0, h0'⟩ := exists_solution (-(t * l / S)) c
  refine ⟨(u₁, u₀), ?_, h1, h1', ?_⟩
  · show u₁ + t * H / S * phi u₁ = u₀ - t * l / S * phi u₀
    linarith
  · simpa using h0'

/-- The first assertion of Lemma `lemma_threshold_value`: `V(t) ≥ 0`. -/
theorem Vval_nonneg (hp : Par pr H l S) (t : ℝ) : 0 ≤ Vval pr H l S t := by
  by_contra hcon
  push Not at hcon
  -- choose `c` so large that the loss term is small
  have h2 : 0 < (1 - pr) * l := mul_pos (by linarith [hp.pr1]) hp.l0
  have hlim : Tendsto (fun x : ℝ => (1 - pr) * l * Phi (-x)) atTop (𝓝 0) := by
    have h := (tendsto_Phi_atBot.comp tendsto_neg_atTop_atBot).const_mul ((1 - pr) * l)
    simpa using h
  have hev := (tendsto_order.1 hlim).2 (-Vval pr H l S t) (by linarith)
  obtain ⟨x, hx⟩ := hev.exists
  set K := |t * l / S| * phi 0 with hK
  obtain ⟨u, hu, _, _, hu0⟩ := exists_feasible_level H l S t (x + K)
  have hle := le_csSup (bddAbove_W hp t) (mem_image_of_mem (fun u : ℝ × ℝ => Wval pr H l u.1 u.2) hu)
  have hx' : (1 - pr) * l * Phi (-x) < -Vval pr H l S t := hx
  have hge : x ≤ u.2 := by
    have := abs_le.1 hu0
    linarith [this.1]
  have hq : Phi (-u.2) ≤ Phi (-x) := Phi_neg_anti hge
  have hW : -((1 - pr) * l * Phi (-x)) ≤ Wval pr H l u.1 u.2 := by
    unfold Wval
    have h3 : 0 ≤ pr * H * Phi (-u.1) := mul_nonneg (mul_pos hp.pr0 hp.H0).le (Phi_pos _).le
    nlinarith
  have hle' : Wval pr H l u.1 u.2 ≤ Vval pr H l S t := hle
  linarith

end NoisyVD
