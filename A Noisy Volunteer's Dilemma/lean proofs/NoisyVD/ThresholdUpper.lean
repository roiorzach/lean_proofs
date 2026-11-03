import NoisyVD.VD

/-!
# Lemma `lemma_threshold_value`: the upper bound `limsup Π^T(n) ≤ Π^SQ + V(t)`

As in the paper: along a sequence of thresholds and equilibria, set `c_n = (T_n - ns)/(σ√n)` and
`y_{ω,n} = √n (p_{n,ω} - s)/σ`, which is bounded, and pass to a subsequence along which `c_n` converges in
the extended real line and both `y_{ω,n}` converge.

* If `c_n → ±∞`, Chebyshev's inequality makes the investigation probability converge in both states to
  zero or one, so the limiting gain over `Π^SQ` is `0` or `πH - (1-π)|L| < 0`.
* If `c_n → c ∈ ℝ`, Lemma `lemma_local_binomial` and `F(x) = s + tx + o(x)` give `y_ω = κ_ω φ(u_ω)` with
  `u_ω = c - y_ω`, so `(u₁, u₀) ∈ 𝒰(t)` and the limiting gain is `W(u₁, u₀) ≤ V(t)`.

The rule "investigate iff fewer than `T_n` reports" is handled at the same time, through the sign `g`: the
gross benefit is `g G_ω ρ_{ω,n}`, and the pair in `𝒰(t)` is `(g u₁, g u₀)`.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

/-- `f(u) = u + κ φ(u)`. -/
noncomputable def fOf (κ u : ℝ) : ℝ := u + κ * phi u

lemma continuous_fOf (κ : ℝ) : Continuous (fOf κ) :=
  continuous_id.add (continuous_const.mul continuous_phi)

lemma phi_mul_sign {g : ℝ} (hg : g * g = 1) (z : ℝ) : phi (g * z) = phi z := by
  have : g = 1 ∨ g = -1 := by
    have h : (g - 1) * (g + 1) = 0 := by linarith [hg]
    rcases mul_eq_zero.1 h with h | h
    · left; linarith
    · right; linarith
  rcases this with rfl | rfl
  · simp
  · simp [phi_neg]

namespace VD

variable {E : Env Bool Bool}

/-- The investigation probability under the rule of direction `up`, when the tail converges to `b`. -/
lemma tendsto_Idir (up : Bool) {x : ℕ → ℝ} {b : ℝ} (h : Tendsto x atTop (𝓝 b)) :
    Tendsto (fun j => Idir up (x j)) atTop (𝓝 (Idir up b)) := by
  cases up
  · simpa [Idir] using h.const_sub 1
  · simpa [Idir] using h

/-- **The limiting gain when `c_n → ±∞`**: if the tails converge to the same `b ∈ {0, 1}` in both states
the gain cannot stay above `ε`. -/
lemma not_gain_of_tendsto (hV : Assumptions E) (up : Bool) {x₁ x₀ : ℕ → ℝ} {b : ℝ}
    (hb : b = 0 ∨ b = 1) (h₁ : Tendsto x₁ atTop (𝓝 b)) (h₀ : Tendsto x₀ atTop (𝓝 b)) {ε : ℝ}
    (hε : 0 < ε) : ∃ j, pr E * H E * Idir up (x₁ j) + (1 - pr E) * L E * Idir up (x₀ j) < ε := by
  have hlim := ((tendsto_Idir up h₁).const_mul (pr E * H E)).add
    ((tendsto_Idir up h₀).const_mul ((1 - pr E) * L E))
  have hval : pr E * H E * Idir up b + (1 - pr E) * L E * Idir up b ≤ 0 := by
    have hI : Idir up b = 0 ∨ Idir up b = 1 := by
      cases up <;> rcases hb with rfl | rfl <;> simp [Idir]
    have hp := prior_ineq hV
    rcases hI with h | h <;> rw [h] <;> linarith
  exact ((tendsto_order.1 hlim).2 ε (lt_of_le_of_lt hval hε)).exists

/-- The upper bound for one direction of the threshold rule. -/
theorem upper_dir (hV : Assumptions E) (hN : E.Noise) {t : ℝ} (hS : Smooth E t) (up : Bool) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N, ∀ (T : ℕ) (s : Strat Bool), E.IsEq n (dirRule up T) s →
      E.payoff n (dirRule up T) s
        ≤ E.PiSQ + Vval (pr E) (H E) (-L E) (E.F 0 * (1 - E.F 0)) t + ε := by
  by_contra hcon
  push Not at hcon
  choose n hnge T s he hbad using hcon
  have hs0 := F_zero_pos hN
  have hs1 := F_zero_lt_one hN
  set s0 := E.F 0 with hs0def
  set S := s0 * (1 - s0) with hSdef
  have hSpos : 0 < S := mul_pos hs0 (by linarith)
  set σ := √S with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hSpos
  have hσσ : σ * σ = S := Real.mul_self_sqrt hSpos.le
  obtain ⟨hl0, hLem1⟩ := Env.lemma_noise E hN
  have hl1 := Env.epsStar_le_half E
  set l := E.epsStar with hldef
  set M := Env.pivConst E.B l with hM
  set g := sgn up with hg
  have hgg : g * g = 1 := sgn_sq up
  have hgabs : |g| = 1 := by
    rw [hg]; cases up <;> simp [sgn]
  have hnt : Tendsto n atTop atTop := tendsto_atTop_mono hnge tendsto_id
  have hn2 : ∀ᶠ j in atTop, 2 ≤ n j := hnt.eventually_ge_atTop 2
  have hN1 : ∀ᶠ j in atTop, 1 ≤ n j := hnt.eventually_ge_atTop 1
  have hNt : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hnt
  have hsqrtN : Tendsto (fun j => √(n j : ℝ)) atTop atTop := Real.tendsto_sqrt_atTop.comp hNt
  let p : Bool → ℕ → ℝ := fun ω j => E.rp (s j) ω
  have hpI : ∀ ω j, p ω j ∈ Icc l (1 - l) := fun ω j => hLem1 _ _ _ (he j) ω
  have hp01 : ∀ ω j, 0 ≤ p ω j ∧ p ω j ≤ 1 := fun ω j =>
    ⟨Env.rp_nonneg E _ ω, Env.rp_le_one E _ ω⟩
  let x : Bool → ℕ → ℝ := fun ω j => E.gross (n j) (dirRule up (T j)) (p ω j) ω
  have hxeq : ∀ ω j, x ω j = g * G E ω * rho (n j - 1) (p ω j) (T j) := fun ω j => gross_dir up _ _ _ ω
  have hxbd : ∀ ω, ∀ᶠ j in atTop, |x ω j| ≤ M / √(n j : ℝ) := fun ω => by
    filter_upwards [hn2] with j hj
    exact Env.abs_gross_le_pivot E hN hj _ (hpI ω j) ω
  have hMsq : Tendsto (fun j => M / √(n j : ℝ)) atTop (𝓝 0) := Tendsto.const_div_atTop hsqrtN M
  have hxt : ∀ ω, Tendsto (x ω) atTop (𝓝 0) := fun ω =>
    squeeze_zero_norm' ((hxbd ω).mono fun j hj => by rwa [Real.norm_eq_abs]) hMsq
  obtain ⟨ε₀, hε₀, hcont⟩ := hS.cont
  have hsmall : ∀ ω, ∀ᶠ j in atTop, |x ω j| < ε₀ := fun ω => by
    have := (hxt ω).abs
    rw [abs_zero] at this
    exact (tendsto_order.1 this).2 ε₀ hε₀
  -- equation `eq_threshold_fixed_point`: `p_{n,ω} = F(g G_ω ρ_{ω,n})`
  have hfix : ∀ ω, ∀ᶠ j in atTop, p ω j = E.F (x ω j) := fun ω => by
    filter_upwards [hsmall ω] with j hj
    exact rp_eq_F (he j) (hcont _ hj)
  -- the variables `y_{ω,n}` are bounded
  set K : ℝ := (|t| + 1) * M / σ with hK
  have hlip : ∀ᶠ y in 𝓝 (0 : ℝ), |E.F y - s0| ≤ (|t| + 1) * |y| := by
    have hlo := hasDerivAt_iff_isLittleO_nhds_zero.1 hS.hasDeriv
    have h1 := (Asymptotics.isLittleO_iff.1 hlo) (one_pos : (0 : ℝ) < 1)
    filter_upwards [h1] with y hy
    simp only [zero_add, smul_eq_mul, Real.norm_eq_abs, one_mul] at hy
    have h2 : E.F y - s0 = (E.F y - s0 - y * t) + y * t := by ring
    rw [h2]
    calc |E.F y - s0 - y * t + y * t| ≤ |E.F y - s0 - y * t| + |y * t| := abs_add_le _ _
      _ ≤ |y| + |y| * |t| := by rw [abs_mul]; linarith
      _ = (|t| + 1) * |y| := by ring
  let y : Bool → ℕ → ℝ := fun ω j => √(n j : ℝ) * (p ω j - s0) / σ
  have hybd : ∀ ω, ∀ᶠ j in atTop, |y ω j| ≤ K := fun ω => by
    filter_upwards [(hxt ω).eventually hlip, hfix ω, hxbd ω, hN1] with j h1 h2 h3 h4
    have hNr : (0 : ℝ) < n j := by exact_mod_cast h4
    have hs : 0 < √(n j : ℝ) := Real.sqrt_pos.2 hNr
    simp only [y]
    rw [abs_div, abs_of_pos hσ, abs_mul, abs_of_pos hs, hK]
    apply div_le_div_of_nonneg_right _ hσ.le
    rw [h2]
    have h5 : |x ω j| * √(n j : ℝ) ≤ M := by
      rw [le_div_iff₀ hs] at h3
      exact h3
    calc √(n j : ℝ) * |E.F (x ω j) - s0| ≤ √(n j : ℝ) * ((|t| + 1) * |x ω j|) :=
          mul_le_mul_of_nonneg_left h1 hs.le
      _ = (|t| + 1) * (|x ω j| * √(n j : ℝ)) := by ring
      _ ≤ (|t| + 1) * M := mul_le_mul_of_nonneg_left h5 (by positivity)
  let c : ℕ → ℝ := fun j => ((T j : ℝ) - n j * s0) / (σ * √(n j : ℝ))
  set V := Vval (pr E) (H E) (-L E) S t with hVdef
  have hpar : Par (pr E) (H E) (-L E) S := par hV hSpos
  have hV0 : 0 ≤ V := Vval_nonneg hpar t
  -- the payoff of the sequence stays above `Π^SQ + V(t) + ε`
  have hgain : ∀ j, V + ε < pr E * H E * Idir up (btail (n j) (p true j) (T j))
      + (1 - pr E) * L E * Idir up (btail (n j) (p false j) (T j)) := fun j => by
    have h1 := hbad j
    rw [payoff_dir hV up] at h1
    have h2 : E.PiSQ + V + ε < E.PiSQ + pr E * H E * Idir up (btail (n j) (p true j) (T j))
        + (1 - pr E) * L E * Idir up (btail (n j) (p false j) (T j)) := h1
    linarith
  -- pass to a subsequence along which `c_n` converges in `EReal` and both `y_{ω,n}` converge
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((hybd true).and (hybd false))
  let z : ℕ → EReal × ℝ × ℝ := fun j => ((c (j + N₀) : ℝ), y true (j + N₀), y false (j + N₀))
  have hzK : ∀ j, z j ∈ (univ : Set EReal) ×ˢ (Icc (-K) K ×ˢ Icc (-K) K) := fun j =>
    ⟨mem_univ _, abs_le.1 (hN₀ (j + N₀) (by omega)).1, abs_le.1 (hN₀ (j + N₀) (by omega)).2⟩
  obtain ⟨⟨cbar, y₁, y₀⟩, -, φ, hφ, hzlim⟩ :=
    (isCompact_univ.prod (isCompact_Icc.prod isCompact_Icc)).tendsto_subseq hzK
  let ψ : ℕ → ℕ := fun j => φ j + N₀
  have hψ : Tendsto ψ atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right _ _) hφ.tendsto_atTop
  have hzparts := (Prod.tendsto_iff _ _).1 hzlim
  have hcbar : Tendsto (fun j => ((c (ψ j) : ℝ) : EReal)) atTop (𝓝 cbar) := hzparts.1
  have hyparts := (Prod.tendsto_iff _ _).1 hzparts.2
  have hy₁ : Tendsto (fun j => y true (ψ j)) atTop (𝓝 y₁) := hyparts.1
  have hy₀ : Tendsto (fun j => y false (ψ j)) atTop (𝓝 y₀) := hyparts.2
  have hnψ : Tendsto (fun j => n (ψ j)) atTop atTop := hnt.comp hψ
  have hN1ψ : ∀ᶠ j in atTop, 1 ≤ n (ψ j) := hnψ.eventually_ge_atTop 1
  have hybdψ : ∀ ω, ∀ᶠ j in atTop, |y ω (ψ j)| ≤ K := fun ω => hψ.eventually (hybd ω)
  -- the identity `T - np = σ√n (c - y)`
  have hgap : ∀ ω j, 1 ≤ n j → (T j : ℝ) - n j * p ω j = σ * √(n j : ℝ) * (c j - y ω j) := by
    intro ω j hj
    have hNr : (0 : ℝ) < n j := by exact_mod_cast hj
    have hsn : 0 < √(n j : ℝ) := Real.sqrt_pos.2 hNr
    have hsq : √(n j : ℝ) * √(n j : ℝ) = n j := Real.mul_self_sqrt hNr.le
    simp only [c, y]
    field_simp
    rw [show √(n j : ℝ) ^ 2 = √(n j : ℝ) * √(n j : ℝ) by ring, hsq]
    ring
  -- `n/(4 (σ√n r)²) = 1/(4 σ² r²)`
  have hratio : ∀ j (r : ℝ), 1 ≤ n j → 0 < r →
      (n j : ℝ) / (4 * (σ * √(n j : ℝ) * r) ^ 2) = 1 / (4 * S * r ^ 2) := by
    intro j r hj hr
    have hNr : (0 : ℝ) < n j := by exact_mod_cast hj
    have hsq : √(n j : ℝ) ^ 2 = n j := Real.sq_sqrt hNr.le
    have hs2 : σ ^ 2 = S := by rw [sq]; exact hσσ
    rw [mul_pow, mul_pow, hsq, hs2]
    field_simp
  induction cbar using EReal.rec with
  | bot =>
    -- `c_n → -∞`: the tails converge to one
    have hc : Tendsto (fun j => c (ψ j)) atTop atBot := EReal.tendsto_coe_nhds_bot_iff.1 hcbar
    have htail : ∀ ω, Tendsto (fun j => btail (n (ψ j)) (p ω (ψ j)) (T (ψ j))) atTop (𝓝 1) := by
      intro ω
      have hr : Tendsto (fun j => -c (ψ j) - K) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_neg_atBot_atTop.comp hc)
      have hbd : Tendsto (fun j => 1 / (4 * S * (-c (ψ j) - K) ^ 2)) atTop (𝓝 0) := by
        refine Tendsto.const_div_atTop ?_ 1
        refine Tendsto.const_mul_atTop (by positivity) ?_
        exact (tendsto_pow_atTop (by norm_num)).comp hr
      have h1 : Tendsto (fun j => 1 - btail (n (ψ j)) (p ω (ψ j)) (T (ψ j))) atTop (𝓝 0) := by
        refine squeeze_zero' ?_ ?_ hbd
        · refine Eventually.of_forall fun j => ?_
          have h2 : btail (n (ψ j)) (p ω (ψ j)) (T (ψ j)) ≤ 1 := by
            rw [btail_eq]
            linarith [bcdf_nonneg (m := n (ψ j)) (hp01 ω (ψ j)).1 (hp01 ω (ψ j)).2 ((T (ψ j) : ℝ) - 1)]
          linarith
        · filter_upwards [hr.eventually_gt_atTop 0, hybdψ ω, hN1ψ] with j hrj hyj hnj
          have hNr : (0 : ℝ) < n (ψ j) := by exact_mod_cast hnj
          have hsn : 0 < √(n (ψ j) : ℝ) := Real.sqrt_pos.2 hNr
          have h3 := one_sub_btail_le (n := n (ψ j)) (T := T (ψ j)) (hp01 ω (ψ j)).1 (hp01 ω (ψ j)).2
            (a := σ * √(n (ψ j) : ℝ) * (-c (ψ j) - K)) (by positivity) (by
              have h4 := hgap ω (ψ j) hnj
              have h5 := (abs_le.1 hyj).1
              have h6 : σ * √(n (ψ j) : ℝ) * (-c (ψ j) - K) ≤ σ * √(n (ψ j) : ℝ) * (-c (ψ j) + y ω (ψ j)) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              have h7 : σ * √(n (ψ j) : ℝ) * (-c (ψ j) + y ω (ψ j))
                  = -(σ * √(n (ψ j) : ℝ) * (c (ψ j) - y ω (ψ j))) := by ring
              linarith)
          rwa [hratio _ _ hnj hrj] at h3
      have := h1.const_sub 1
      simpa using this
    obtain ⟨j, hj⟩ := not_gain_of_tendsto hV up (b := 1) (Or.inr rfl) (htail true) (htail false)
      (show 0 < V + ε by linarith)
    exact absurd (hgain (ψ j)) (not_lt.2 hj.le)
  | top =>
    -- `c_n → +∞`: the tails converge to zero
    have hc : Tendsto (fun j => c (ψ j)) atTop atTop := EReal.tendsto_coe_nhds_top_iff.1 hcbar
    have htail : ∀ ω, Tendsto (fun j => btail (n (ψ j)) (p ω (ψ j)) (T (ψ j))) atTop (𝓝 0) := by
      intro ω
      have hr : Tendsto (fun j => c (ψ j) - K) atTop atTop :=
        tendsto_atTop_add_const_right _ _ hc
      have hbd : Tendsto (fun j => 1 / (4 * S * (c (ψ j) - K) ^ 2)) atTop (𝓝 0) := by
        refine Tendsto.const_div_atTop ?_ 1
        refine Tendsto.const_mul_atTop (by positivity) ?_
        exact (tendsto_pow_atTop (by norm_num)).comp hr
      refine squeeze_zero' ?_ ?_ hbd
      · refine Eventually.of_forall fun j => ?_
        rw [btail_eq]
        linarith [bcdf_le_one (m := n (ψ j)) (hp01 ω (ψ j)).1 (hp01 ω (ψ j)).2 ((T (ψ j) : ℝ) - 1)]
      · filter_upwards [hr.eventually_gt_atTop 0, hybdψ ω, hN1ψ] with j hrj hyj hnj
        have hNr : (0 : ℝ) < n (ψ j) := by exact_mod_cast hnj
        have hsn : 0 < √(n (ψ j) : ℝ) := Real.sqrt_pos.2 hNr
        have h3 := btail_le_of_gap (n := n (ψ j)) (T := T (ψ j)) (hp01 ω (ψ j)).1 (hp01 ω (ψ j)).2
          (a := σ * √(n (ψ j) : ℝ) * (c (ψ j) - K)) (by positivity) (by
            have h4 := hgap ω (ψ j) hnj
            have h5 := (abs_le.1 hyj).2
            have h6 : σ * √(n (ψ j) : ℝ) * (c (ψ j) - K) ≤ σ * √(n (ψ j) : ℝ) * (c (ψ j) - y ω (ψ j)) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            linarith)
        rwa [hratio _ _ hnj hrj] at h3
    obtain ⟨j, hj⟩ := not_gain_of_tendsto hV up (b := 0) (Or.inl rfl) (htail true) (htail false)
      (show 0 < V + ε by linarith)
    exact absurd (hgain (ψ j)) (not_lt.2 hj.le)
  | coe c₀ =>
    -- `c_n → c ∈ ℝ`
    have hc : Tendsto (fun j => c (ψ j)) atTop (𝓝 c₀) := EReal.tendsto_coe.1 hcbar
    set K' : ℝ := max K (|c₀| + 1) with hK'
    have hcb : ∀ᶠ j in atTop, |c (ψ j)| ≤ K' := by
      filter_upwards [(tendsto_order.1 hc.abs).2 (|c₀| + 1) (by linarith)] with j hj
      exact hj.le.trans (le_max_right _ _)
    have hyb' : ∀ ω, ∀ᶠ j in atTop, |y ω (ψ j)| ≤ K' := fun ω =>
      (hybdψ ω).mono fun j hj => hj.trans (le_max_left _ _)
    -- Lemma `lemma_local_binomial` along the subsequence
    have hlim : ∀ ω (yω : ℝ), Tendsto (fun j => y ω (ψ j)) atTop (𝓝 yω) →
        Tendsto (fun j => √(n (ψ j) : ℝ) * rho (n (ψ j) - 1) (p ω (ψ j)) (T (ψ j))) atTop
            (𝓝 (phi (c₀ - yω) / σ)) ∧
          Tendsto (fun j => btail (n (ψ j)) (p ω (ψ j)) (T (ψ j))) atTop (𝓝 (Phi (-(c₀ - yω)))) := by
      intro ω yω hyω
      have hu : Tendsto (fun j => uStat s0 (n (ψ j)) (T (ψ j)) (p ω (ψ j))) atTop (𝓝 (c₀ - yω)) := by
        refine (hc.sub hyω).congr' ?_
        filter_upwards [hN1ψ] with j hj
        exact (uStat_eq hs0 hs1 hj _ _).symm
      have hunif : ∀ δ > 0, ∀ᶠ j in atTop,
          |√(n (ψ j) : ℝ) * rho (n (ψ j) - 1) (p ω (ψ j)) (T (ψ j))
              - phi (uStat s0 (n (ψ j)) (T (ψ j)) (p ω (ψ j))) / σ| < δ ∧
            |btail (n (ψ j)) (p ω (ψ j)) (T (ψ j)) - Phi (-uStat s0 (n (ψ j)) (T (ψ j)) (p ω (ψ j)))| < δ := by
        intro δ hδ
        obtain ⟨N, hN⟩ := pivot_tail_uniform hs0 hs1 K' hδ
        filter_upwards [hnψ.eventually_ge_atTop N, hyb' ω, hcb] with j h1 h2 h3
        exact hN _ h1 _ _ h2 h3
      constructor
      · have h1 : Tendsto (fun j => phi (uStat s0 (n (ψ j)) (T (ψ j)) (p ω (ψ j))) / σ) atTop
            (𝓝 (phi (c₀ - yω) / σ)) := (continuous_phi.continuousAt.tendsto.comp hu).div_const σ
        rw [Metric.tendsto_nhds]
        intro δ hδ
        filter_upwards [hunif (δ / 2) (by linarith), Metric.tendsto_nhds.1 h1 (δ / 2) (by linarith)] with j h2 h3
        rw [Real.dist_eq] at h3 ⊢
        have := abs_sub_le (√(n (ψ j) : ℝ) * rho (n (ψ j) - 1) (p ω (ψ j)) (T (ψ j)))
          (phi (uStat s0 (n (ψ j)) (T (ψ j)) (p ω (ψ j))) / σ) (phi (c₀ - yω) / σ)
        linarith [h2.1]
      · have h1 : Tendsto (fun j => Phi (-uStat s0 (n (ψ j)) (T (ψ j)) (p ω (ψ j)))) atTop
            (𝓝 (Phi (-(c₀ - yω)))) := continuous_Phi.continuousAt.tendsto.comp hu.neg
        rw [Metric.tendsto_nhds]
        intro δ hδ
        filter_upwards [hunif (δ / 2) (by linarith), Metric.tendsto_nhds.1 h1 (δ / 2) (by linarith)] with j h2 h3
        rw [Real.dist_eq] at h3 ⊢
        have := abs_sub_le (btail (n (ψ j)) (p ω (ψ j)) (T (ψ j)))
          (Phi (-uStat s0 (n (ψ j)) (T (ψ j)) (p ω (ψ j)))) (Phi (-(c₀ - yω)))
        linarith [h2.2]
    -- the fixed-point equation yields `y_ω = g κ_ω φ(u_ω)`
    have hfp : ∀ ω (yω : ℝ), Tendsto (fun j => y ω (ψ j)) atTop (𝓝 yω) →
        yω = g * (t * G E ω / S) * phi (c₀ - yω) := by
      intro ω yω hyω
      have hρ := (hlim ω yω hyω).1
      have hx : Tendsto (fun j => √(n (ψ j) : ℝ) * x ω (ψ j)) atTop
          (𝓝 (g * G E ω * (phi (c₀ - yω) / σ))) := by
        refine (hρ.const_mul (g * G E ω)).congr fun j => ?_
        rw [hxeq]
        ring
      have hF := tendsto_sqrt_mul_F_sub hS.hasDeriv rfl hnψ hx
      have hdiv := hF.div_const σ
      have hyeq : Tendsto (fun j => y ω (ψ j)) atTop
          (𝓝 (t * (g * G E ω * (phi (c₀ - yω) / σ)) / σ)) := by
        refine hdiv.congr' ?_
        filter_upwards [hψ.eventually (hfix ω)] with j hj
        simp only [y]
        rw [hj]
      have huniq := tendsto_nhds_unique hyω hyeq
      have hne := hσ.ne'
      have e : S = σ * σ := hσσ.symm
      calc yω = t * (g * G E ω * (phi (c₀ - yω) / σ)) / σ := huniq
        _ = g * (t * G E ω / S) * phi (c₀ - yω) := by
            rw [e]
            field_simp
    -- the pair in `𝒰(t)`
    set u₁ := c₀ - y₁ with hu₁
    set u₀ := c₀ - y₀ with hu₀
    have hf₁ := hfp true y₁ hy₁
    have hf₀ := hfp false y₀ hy₀
    have hfeas : (g * u₁, g * u₀) ∈ feasible (H E) (-L E) S t := by
      show g * u₁ + t * H E / S * phi (g * u₁) = g * u₀ - t * (-L E) / S * phi (g * u₀)
      rw [phi_mul_sign hgg, phi_mul_sign hgg]
      have e₁ : t * H E / S * phi u₁ = g * y₁ := by
        have h2 : g * y₁ = g * (g * (t * G E true / S) * phi u₁) := by rw [← hf₁]
        rw [h2]
        have h3 : G E true = H E := rfl
        rw [h3]
        linear_combination (-(t * H E / S * phi u₁)) * hgg
      have e₀ : t * (-L E) / S * phi u₀ = -(g * y₀) := by
        have h2 : g * y₀ = g * (g * (t * G E false / S) * phi u₀) := by rw [← hf₀]
        rw [h2]
        have h3 : G E false = L E := rfl
        rw [h3]
        linear_combination (t * L E / S * phi u₀) * hgg
      rw [e₁, e₀, hu₁, hu₀]
      ring
    have hW : Wval (pr E) (H E) (-L E) (g * u₁) (g * u₀) ≤ V :=
      le_csSup (bddAbove_W hpar t) (mem_image_of_mem (fun u : ℝ × ℝ => Wval (pr E) (H E) (-L E) u.1 u.2) hfeas)
    -- the investigation probabilities converge to `Φ(-g u_ω)`
    have hI : ∀ ω (yω : ℝ), Tendsto (fun j => y ω (ψ j)) atTop (𝓝 yω) →
        Tendsto (fun j => Idir up (btail (n (ψ j)) (p ω (ψ j)) (T (ψ j)))) atTop
          (𝓝 (Phi (-(g * (c₀ - yω))))) := by
      intro ω yω hyω
      have h1 := tendsto_Idir up (hlim ω yω hyω).2
      have e : Idir up (Phi (-(c₀ - yω))) = Phi (-(g * (c₀ - yω))) := by
        rw [hg]
        cases up
        · simp only [Idir, sgn, Bool.false_eq_true, ite_false]
          rw [Phi_neg, show -(-1 * (c₀ - yω)) = c₀ - yω by ring]
          ring
        · simp [Idir, sgn]
      rwa [e] at h1
    have hlimgain := ((hI true y₁ hy₁).const_mul (pr E * H E)).add
      ((hI false y₀ hy₀).const_mul ((1 - pr E) * L E))
    have hval : pr E * H E * Phi (-(g * (c₀ - y₁))) + (1 - pr E) * L E * Phi (-(g * (c₀ - y₀)))
        = Wval (pr E) (H E) (-L E) (g * u₁) (g * u₀) := by
      unfold Wval
      rw [hu₁, hu₀]
      ring
    rw [hval] at hlimgain
    obtain ⟨j, hj⟩ := ((tendsto_order.1 hlimgain).2 (V + ε) (by linarith)).exists
    exact absurd (hgain (ψ j)) (not_lt.2 hj.le)

/-- The upper bound in Lemma `lemma_threshold_value`, equation `eq_threshold_upper_bound`. -/
theorem threshold_upper (hV : Assumptions E) (hN : E.Noise) {t : ℝ} (hS : Smooth E t) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n in atTop,
      E.PiT n ≤ E.PiSQ + Vval (pr E) (H E) (-L E) (E.F 0 * (1 - E.F 0)) t + ε := by
  obtain ⟨N₁, hN₁⟩ := upper_dir hV hN hS true hε
  obtain ⟨N₀, hN₀⟩ := upper_dir hV hN hS false hε
  filter_upwards [eventually_ge_atTop (max N₁ N₀)] with n hn
  have hS0 : 0 < E.F 0 * (1 - E.F 0) := mul_pos (F_zero_pos hN) (by linarith [F_zero_lt_one hN])
  have hV0 := Vval_nonneg (par hV hS0) t
  refine csSup_le ⟨_, E.PiSQ_mem_payoffsT n⟩ ?_
  rintro y ⟨T, a₁, a₀, s, _, he, rfl⟩
  cases a₁ <;> cases a₀
  · -- constant `false`
    have hk := Env.thresholdRule_self T false
    rw [Env.payoff_const E hk, ← PiSQ_eq hV]
    linarith
  · exact hN₀ n (le_trans (le_max_right _ _) hn) T s he
  · exact hN₁ n (le_trans (le_max_left _ _) hn) T s he
  · -- constant `true`
    have hk := Env.thresholdRule_self T true
    rw [Env.payoff_const E hk]
    have := E.integral_u_le_PiSQ true
    linarith

end VD

end NoisyVD
