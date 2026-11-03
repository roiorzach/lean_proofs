import NoisyVD.ThresholdUpper

/-!
# Lemma `lemma_threshold_value`: the lower bound and the limit

For a regular feasible pair the fixed point of each state is found by the Intermediate Value Theorem
around `u_ω`, as in the paper.  Regular pairs are dense among feasible pairs.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

/-- `f'(u) = 1 - κ u φ(u)`. -/
noncomputable def fDeriv (κ u : ℝ) : ℝ := 1 + κ * (-u * phi u)

lemma hasDerivAt_fOf (κ u : ℝ) : HasDerivAt (fOf κ) (fDeriv κ u) u :=
  (hasDerivAt_id u).add ((hasDerivAt_phi u).const_mul κ)

lemma continuous_fDeriv (κ : ℝ) : Continuous (fDeriv κ) := by
  unfold fDeriv
  have : Continuous fun u : ℝ => -u * phi u := continuous_neg.mul continuous_phi
  exact continuous_const.add (continuous_const.mul this)

lemma hasDerivAt_fDeriv (κ u : ℝ) : HasDerivAt (fDeriv κ) (κ * (phi u * (u ^ 2 - 1))) u := by
  have h1 : HasDerivAt (fun y : ℝ => -y) (-1) u := (hasDerivAt_id' u).neg
  have h2 : HasDerivAt (fun y => -y * phi y) (-1 * phi u + (-u) * (-u * phi u)) u :=
    h1.fun_mul (hasDerivAt_phi u)
  have h3 : HasDerivAt (fDeriv κ) (κ * (-1 * phi u + -u * (-u * phi u))) u :=
    (h2.const_mul κ).const_add 1
  convert h3 using 1
  ring

/-- A nonzero derivative forces a sign change arbitrarily close to the point. -/
lemma sign_change {f : ℝ → ℝ} {f' u η : ℝ} (hf : HasDerivAt f f' u) (hf' : f' ≠ 0) (hη : 0 < η) :
    ∃ a b, |a - u| < η ∧ |b - u| < η ∧ f a < f u ∧ f u < f b := by
  have aux : ∀ {g : ℝ → ℝ} {g' : ℝ}, HasDerivAt g g' u → 0 < g' →
      ∃ a b, |a - u| < η ∧ |b - u| < η ∧ g a < g u ∧ g u < g b := by
    intro g g' hg hg'
    have hs := hasDerivAt_iff_tendsto_slope.1 hg
    have hpos : ∀ᶠ x in 𝓝[≠] u, 0 < slope g u x := (tendsto_order.1 hs).1 0 hg'
    have hR : ∀ᶠ x in 𝓝[>] u, 0 < slope g u x :=
      hpos.filter_mono (nhdsWithin_mono _ fun x hx => (ne_of_gt (mem_Ioi.1 hx)))
    have hL : ∀ᶠ x in 𝓝[<] u, 0 < slope g u x :=
      hpos.filter_mono (nhdsWithin_mono _ fun x hx => (ne_of_lt (mem_Iio.1 hx)))
    have hR2 : ∀ᶠ x in 𝓝[>] u, x ∈ Ioo u (u + η) := Ioo_mem_nhdsGT (by linarith)
    have hL2 : ∀ᶠ x in 𝓝[<] u, x ∈ Ioo (u - η) u := Ioo_mem_nhdsLT (by linarith)
    obtain ⟨b, hb1, hb2⟩ := (hR.and hR2).exists
    obtain ⟨a, ha1, ha2⟩ := (hL.and hL2).exists
    refine ⟨a, b, ?_, ?_, ?_, ?_⟩
    · rw [abs_lt]; constructor <;> linarith [ha2.1, ha2.2]
    · rw [abs_lt]; constructor <;> linarith [hb2.1, hb2.2]
    · rw [slope_def_field, lt_div_iff_of_neg (by linarith [ha2.2])] at ha1
      linarith
    · rw [slope_def_field, lt_div_iff₀ (by linarith [hb2.1])] at hb1
      linarith
  rcases lt_or_gt_of_ne hf' with h | h
  · obtain ⟨a, b, h1, h2, h3, h4⟩ := aux hf.neg (by linarith)
    exact ⟨b, a, h2, h1, by simpa using h4, by simpa using h3⟩
  · exact aux hf h

/-- Perturbation lemma behind the density of regular pairs. -/
lemma perturb {κa κb x₀ y₀ η : ℝ} (hκa : κa ≠ 0) (heq : fOf κa x₀ = fOf κb y₀)
    (hb : fDeriv κb y₀ ≠ 0) (hη : 0 < η) :
    ∃ x y, |x - x₀| < η ∧ |y - y₀| < η ∧ fOf κa x = fOf κb y ∧ fDeriv κa x ≠ 0 ∧ fDeriv κb y ≠ 0 := by
  -- nonvanishing of `f_b'` near `y₀`
  have h1 : ∀ᶠ y in 𝓝 y₀, fDeriv κb y ≠ 0 := (continuous_fDeriv κb).continuousAt.eventually_ne hb
  obtain ⟨η₁', hη₁', hball⟩ := Metric.eventually_nhds_iff.1 h1
  set η₁ := min η η₁' with hη₁
  have hη₁pos : 0 < η₁ := lt_min hη hη₁'
  obtain ⟨a, b, ha, hb2, hfa, hfb⟩ := sign_change (hasDerivAt_fOf κb y₀) hb hη₁pos
  -- `f_a` stays between `f_b(a)` and `f_b(b)` near `x₀`
  have h2 : ∀ᶠ x in 𝓝 x₀, fOf κb a < fOf κa x ∧ fOf κa x < fOf κb b := by
    have hc := (continuous_fOf κa).continuousAt (x := x₀)
    have h3 := hc.eventually (lt_mem_nhds (show fOf κb a < fOf κa x₀ by rw [heq]; exact hfa))
    have h4 := hc.eventually (gt_mem_nhds (show fOf κa x₀ < fOf κb b by rw [heq]; exact hfb))
    exact h3.and h4
  obtain ⟨η₂', hη₂', hball2⟩ := Metric.eventually_nhds_iff.1 h2
  set η₂ := min η η₂' with hη₂
  have hη₂pos : 0 < η₂ := lt_min hη hη₂'
  -- some `x` near `x₀` has `f_a'(x) ≠ 0`
  have hex : ∃ x, |x - x₀| < η₂ ∧ fDeriv κa x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    -- three points; one has `x² ≠ 1`
    have hpt : ∃ x₁, |x₁ - x₀| < η₂ ∧ x₁ ^ 2 ≠ 1 := by
      by_contra hc2
      push Not at hc2
      have e1 := hc2 x₀ (by simpa using hη₂pos)
      have e2 := hc2 (x₀ + η₂ / 2) (by
        rw [add_sub_cancel_left, abs_of_pos (by linarith)]; linarith)
      have e3 := hc2 (x₀ + η₂ / 3) (by
        rw [add_sub_cancel_left, abs_of_pos (by linarith)]; linarith)
      have h4 : (η₂ / 2) * (2 * x₀ + η₂ / 2) = 0 := by nlinarith
      have h5 : (η₂ / 3) * (2 * x₀ + η₂ / 3) = 0 := by nlinarith
      have h6 := (mul_eq_zero.1 h4).resolve_left (by linarith : η₂ / 2 ≠ 0)
      have h7 := (mul_eq_zero.1 h5).resolve_left (by linarith : η₂ / 3 ≠ 0)
      linarith
    obtain ⟨x₁, hx₁, hx₁2⟩ := hpt
    have hzero : fDeriv κa =ᶠ[𝓝 x₁] fun _ => 0 := by
      have hopen : Metric.ball x₀ η₂ ∈ 𝓝 x₁ :=
        Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, Real.dist_eq] using hx₁)
      filter_upwards [hopen] with x hx
      exact hcon x (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
    have hd1 := hasDerivAt_fDeriv κa x₁
    have hd2 : HasDerivAt (fDeriv κa) 0 x₁ := (hasDerivAt_const x₁ (0 : ℝ)).congr_of_eventuallyEq hzero
    have huniq := hd1.unique hd2
    have hφ := phi_pos x₁
    have : x₁ ^ 2 - 1 = 0 := by
      have h8 := (mul_eq_zero.1 huniq).resolve_left hκa
      exact (mul_eq_zero.1 h8).resolve_left hφ.ne'
    exact hx₁2 (by linarith)
  obtain ⟨x, hx, hx2⟩ := hex
  have hx3 := hball2 (show dist x x₀ < η₂' by
    rw [Real.dist_eq]; exact lt_of_lt_of_le hx (min_le_right _ _))
  -- solve for `y`
  obtain ⟨y, hy, hye⟩ := intermediate_value_uIcc (continuous_fOf κb).continuousOn
    (mem_uIcc.2 (Or.inl ⟨hx3.1.le, hx3.2.le⟩))
  have hy1 : |y - y₀| < η₁ := by
    rw [mem_uIcc] at hy
    have ha' := abs_lt.1 ha
    have hb' := abs_lt.1 hb2
    rw [abs_lt]
    rcases hy with hy | hy <;> constructor <;> linarith [hy.1, hy.2, ha'.1, ha'.2, hb'.1, hb'.2]
  refine ⟨x, y, lt_of_lt_of_le hx (min_le_left _ _), lt_of_lt_of_le hy1 (min_le_left _ _), hye.symm, hx2, ?_⟩
  exact hball (show dist y y₀ < η₁' by
    rw [Real.dist_eq]; exact lt_of_lt_of_le hy1 (min_le_right _ _))

/-- Regular feasible pairs are dense among feasible pairs. -/
lemma regular_dense {κ₁ κ₀ u₁ u₀ η : ℝ} (hκ₁ : 0 < κ₁) (hκ₀ : κ₀ < 0)
    (heq : fOf κ₁ u₁ = fOf κ₀ u₀) (hη : 0 < η) :
    ∃ v₁ v₀, |v₁ - u₁| < η ∧ |v₀ - u₀| < η ∧ fOf κ₁ v₁ = fOf κ₀ v₀ ∧ fDeriv κ₁ v₁ ≠ 0 ∧
      fDeriv κ₀ v₀ ≠ 0 := by
  by_cases h0 : fDeriv κ₀ u₀ ≠ 0
  · exact perturb hκ₁.ne' heq h0 hη
  · push Not at h0
    have h1 : fDeriv κ₁ u₁ ≠ 0 := by
      intro h1
      unfold fDeriv at h0 h1
      have hφ1 := phi_pos u₁
      have hφ0 := phi_pos u₀
      -- `u₁ > 0`, `u₀ < 0`
      have hu1 : 0 < u₁ := by
        by_contra hc
        push Not at hc
        have : 0 ≤ κ₁ * (-u₁ * phi u₁) := by
          have : 0 ≤ -u₁ * phi u₁ := mul_nonneg (by linarith) hφ1.le
          positivity
        linarith
      have hu0 : u₀ < 0 := by
        by_contra hc
        push Not at hc
        have : 0 ≤ κ₀ * (-u₀ * phi u₀) := by
          have h3 : -u₀ * phi u₀ ≤ 0 := by
            have := mul_nonneg hc hφ0.le
            linarith
          exact mul_nonneg_of_nonpos_of_nonpos hκ₀.le h3
        linarith
      unfold fOf at heq
      have h4 : 0 < κ₁ * phi u₁ := mul_pos hκ₁ hφ1
      have h5 : κ₀ * phi u₀ < 0 := mul_neg_of_neg_of_pos hκ₀ hφ0
      linarith
    obtain ⟨x, y, h2, h3, h4, h5, h6⟩ := perturb hκ₀.ne heq.symm h1 hη
    exact ⟨y, x, h3, h2, h4.symm, h6, h5⟩

namespace VD

variable {E : Env Bool Bool}

/-- The candidate reporting probability `r_n(x) = s + σ(c_n - x)/√n`. -/
noncomputable def rn (s0 σ cn : ℝ) (n : ℕ) (x : ℝ) : ℝ := s0 + σ * (cn - x) / √(n : ℝ)

/-- At `p = r_n(x)` the variable `y` equals `c_n - x`. -/
lemma y_rn {s0 σ cn x : ℝ} {n : ℕ} (hn : 1 ≤ n) (hσ : 0 < σ) :
    √(n : ℝ) * (rn s0 σ cn n x - s0) / σ = cn - x := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
  unfold rn
  field_simp
  ring

/-- At `p = r_n(x)`, `u = c_n - y = x`. -/
lemma uStat_rn {s0 x : ℝ} (hs0 : 0 < s0) (hs1 : s0 < 1) {n T : ℕ} (hn : 1 ≤ n) :
    uStat s0 n T (rn s0 √(s0 * (1 - s0)) (((T : ℝ) - n * s0) / (√(s0 * (1 - s0)) * √(n : ℝ))) n x) = x := by
  have hσ : 0 < √(s0 * (1 - s0)) := Real.sqrt_pos.2 (mul_pos hs0 (by linarith))
  rw [uStat_eq hs0 hs1 hn, y_rn hn hσ]
  ring

/-- The map whose root is a fixed point of the reporting equation. -/
noncomputable def Psi (E : Env Bool Bool) (G s0 σ cn : ℝ) (T n : ℕ) (x : ℝ) : ℝ :=
  x + √(n : ℝ) * (E.F (G * rho (n - 1) (rn s0 σ cn n x) T) - s0) / σ

/-- Pointwise convergence of `Ψ_n` to `f`, from Lemma `lemma_local_binomial` and differentiability of `F`. -/
lemma Psi_tendsto (hN : E.Noise) {t : ℝ} (hS : Smooth E t) {G c : ℝ} {T : ℕ → ℕ}
    (hc : Tendsto (fun n : ℕ => ((T n : ℝ) - n * E.F 0) / (√(E.F 0 * (1 - E.F 0)) * √(n : ℝ))) atTop (𝓝 c))
    (x : ℝ) :
    Tendsto (fun n : ℕ => Psi E G (E.F 0) (√(E.F 0 * (1 - E.F 0)))
        (((T n : ℝ) - n * E.F 0) / (√(E.F 0 * (1 - E.F 0)) * √(n : ℝ))) (T n) n x) atTop
      (𝓝 (fOf (t * G / (E.F 0 * (1 - E.F 0))) x)) := by
  have hs0 := F_zero_pos hN
  have hs1 := F_zero_lt_one hN
  set s0 := E.F 0 with hs0def
  set S := s0 * (1 - s0) with hSdef
  have hSpos : 0 < S := mul_pos hs0 (by linarith)
  set σ := √S with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hSpos
  have hσσ : σ * σ = S := Real.mul_self_sqrt hSpos.le
  set cn : ℕ → ℝ := fun n : ℕ => ((T n : ℝ) - n * s0) / (σ * √(n : ℝ)) with hcn
  -- `c_n` and `y_n = c_n - x` are bounded
  set K : ℝ := |c| + 1 + |x| with hK
  have hcb : ∀ᶠ n : ℕ in atTop, |cn n| ≤ |c| + 1 := by
    filter_upwards [(tendsto_order.1 hc.abs).2 (|c| + 1) (by linarith)] with n hn using hn.le
  have hρ : Tendsto (fun n : ℕ => √(n : ℝ) * rho (n - 1) (rn s0 σ (cn n) n x) (T n)) atTop
      (𝓝 (phi x / σ)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨N, hN'⟩ := pivot_tail_uniform hs0 hs1 K hδ
    filter_upwards [hcb, eventually_ge_atTop N, eventually_ge_atTop 1] with n h1 h2 h3
    have hy : √(n : ℝ) * (rn s0 σ (cn n) n x - s0) / σ = cn n - x := y_rn h3 hσ
    have hyb : |√(n : ℝ) * (rn s0 σ (cn n) n x - s0) / σ| ≤ K := by
      rw [hy, hK]
      have := abs_sub (cn n) x
      linarith
    have hcK : |cn n| ≤ K := by
      rw [hK]
      linarith [abs_nonneg x]
    have h4 := (hN' n h2 (T n) _ hyb hcK).1
    rw [uStat_rn hs0 hs1 h3] at h4
    rwa [Real.dist_eq]
  have hx : Tendsto (fun n : ℕ => √(n : ℝ) * (G * rho (n - 1) (rn s0 σ (cn n) n x) (T n))) atTop
      (𝓝 (G * (phi x / σ))) := by
    refine (hρ.const_mul G).congr fun n => ?_
    ring
  have hF := tendsto_sqrt_mul_F_sub hS.hasDeriv rfl tendsto_id hx
  have hsum := (hF.div_const σ).const_add x
  have e : x + t * (G * (phi x / σ)) / σ = fOf (t * G / S) x := by
    unfold fOf
    rw [← hσσ]
    have := hσ.ne'
    field_simp
  rw [e] at hsum
  exact hsum.congr fun n => rfl

/-- **The fixed point of one state** near a regular solution. -/
lemma exists_fixed_point (hN : E.Noise) {t : ℝ} (hS : Smooth E t) {G c u : ℝ}
    (hu : fOf (t * G / (E.F 0 * (1 - E.F 0))) u = c)
    (hu' : fDeriv (t * G / (E.F 0 * (1 - E.F 0))) u ≠ 0) {T : ℕ → ℕ}
    (hc : Tendsto (fun n : ℕ => ((T n : ℝ) - n * E.F 0) / (√(E.F 0 * (1 - E.F 0)) * √(n : ℝ))) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ p, 0 < p ∧ p < 1 ∧ E.F (G * rho (n - 1) p (T n)) = p ∧
      |btail n p (T n) - Phi (-u)| < ε := by
  have hs0 := F_zero_pos hN
  have hs1 := F_zero_lt_one hN
  set s0 := E.F 0 with hs0def
  set S := s0 * (1 - s0) with hSdef
  have hSpos : 0 < S := mul_pos hs0 (by linarith)
  set σ := √S with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hSpos
  set κ := t * G / S with hκ
  set l : ℝ := min s0 (1 - s0) / 2 with hl
  have hl0 : 0 < l := by
    rw [hl]
    have := lt_min hs0 (show 0 < 1 - s0 by linarith)
    linarith
  have hl1 : l ≤ s0 / 2 := by
    rw [hl]; apply div_le_div_of_nonneg_right (min_le_left _ _); norm_num
  have hl2 : l ≤ (1 - s0) / 2 := by
    rw [hl]; apply div_le_div_of_nonneg_right (min_le_right _ _); norm_num
  have hlhalf : l ≤ 1 / 2 := by linarith
  have hφ0 := phi_pos 0
  set η : ℝ := ε / (4 * (phi 0 + 1)) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηε : phi 0 * η < ε / 2 := by
    rw [hη]
    have h1 : phi 0 * (ε / (4 * (phi 0 + 1))) = ε / 4 * (phi 0 / (phi 0 + 1)) := by
      field_simp
    rw [h1]
    have h2 : phi 0 / (phi 0 + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  obtain ⟨a, b, ha, hb, hfa, hfb⟩ := sign_change (hasDerivAt_fOf κ u) hu' hηpos
  rw [hu] at hfa hfb
  set cn : ℕ → ℝ := fun n : ℕ => ((T n : ℝ) - n * s0) / (σ * √(n : ℝ)) with hcn
  have hsn : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hPa := Psi_tendsto hN hS (G := G) hc a
  have hPb := Psi_tendsto hN hS (G := G) hc b
  have hev1 : ∀ᶠ n : ℕ in atTop, Psi E G s0 σ (cn n) (T n) n a < cn n := by
    have h1 := hPa.sub hc
    have h2 := (tendsto_order.1 h1).2 0 (by linarith)
    filter_upwards [h2] with n hn
    linarith
  have hev2 : ∀ᶠ n : ℕ in atTop, cn n < Psi E G s0 σ (cn n) (T n) n b := by
    have h1 := hPb.sub hc
    have h2 := (tendsto_order.1 h1).1 0 (by linarith)
    filter_upwards [h2] with n hn
    linarith
  -- uniform bound for `r_n` on the segment
  set A : ℝ := |c| + 1 + |a| + |b| with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hev3 : ∀ᶠ n : ℕ in atTop, |cn n| ≤ |c| + 1 := by
    have := (tendsto_order.1 hc.abs).2 (|c| + 1) (by linarith)
    exact this.mono fun n hn => hn.le
  have hsmall : Tendsto (fun n : ℕ => σ * A / √(n : ℝ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop hsn _
  have hev4 : ∀ᶠ n : ℕ in atTop, σ * A / √(n : ℝ) < l :=
    (tendsto_order.1 hsmall).2 _ hl0
  -- the pivotal probability is small
  obtain ⟨ε₀, hε₀, hcont⟩ := hS.cont
  have hmass := massConst_pos hl0 hlhalf
  have hev5 : ∀ᶠ n : ℕ in atTop, |G| * (massConst l / √((n - 1 : ℕ) : ℝ)) < ε₀ := by
    have h1 : Tendsto (fun n : ℕ => √((n - 1 : ℕ) : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
    have h2 := (Tendsto.const_div_atTop h1 (massConst l)).const_mul |G|
    rw [mul_zero] at h2
    exact (tendsto_order.1 h2).2 ε₀ hε₀
  obtain ⟨N₀, hN₀⟩ := pivot_tail_uniform hs0 hs1 (|c| + 1 + (|a| + |b|)) (show 0 < ε / 2 by linarith)
  filter_upwards [hev1, hev2, hev3, hev4, hev5, eventually_ge_atTop 2, eventually_ge_atTop N₀]
    with n h1 h2 h3 h4 h5 hn2 hnN
  have hnr : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hsnpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
  have hm1 : 1 ≤ n - 1 := by omega
  -- on the segment `r_n` stays in `[l, 1-l]`
  have habsx : ∀ x ∈ uIcc a b, |x| ≤ |a| + |b| := by
    intro x hx
    rw [mem_uIcc] at hx
    rw [abs_le]
    have h6 := abs_nonneg a
    have h7 := abs_nonneg b
    have h8 := le_abs_self a
    have h9 := le_abs_self b
    have h10 := neg_abs_le a
    have h11 := neg_abs_le b
    rcases hx with hx | hx <;> constructor <;> linarith [hx.1, hx.2]
  have hseg : ∀ x ∈ uIcc a b, |rn s0 σ (cn n) n x - s0| ≤ σ * A / √(n : ℝ) := by
    intro x hx
    have hxb := habsx x hx
    unfold rn
    rw [add_sub_cancel_left, abs_div, abs_mul, abs_of_pos hσ, abs_of_pos hsnpos]
    apply div_le_div_of_nonneg_right _ hsnpos.le
    apply mul_le_mul_of_nonneg_left _ hσ.le
    calc |cn n - x| ≤ |cn n| + |x| := abs_sub _ _
      _ ≤ A := by rw [hA]; linarith
  have hsegl : ∀ x ∈ uIcc a b, rn s0 σ (cn n) n x ∈ Icc l (1 - l) := by
    intro x hx
    have h6 := abs_le.1 (hseg x hx)
    constructor <;> linarith [h6.1, h6.2]
  have hρsmall : ∀ q ∈ Icc l (1 - l), |G * rho (n - 1) q (T n)| < ε₀ := by
    intro q hq
    have h6 := rho_le_mass (T := T n) hm1 hl0 hlhalf hq
    have h7 : 0 ≤ rho (n - 1) q (T n) := rho_nonneg (by linarith [hq.1]) (by linarith [hq.2])
    rw [abs_mul, abs_of_nonneg h7]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h6 (abs_nonneg G)) h5
  -- continuity of `Ψ_n` on the segment
  have hcontΨ : ContinuousOn (Psi E G s0 σ (cn n) (T n) n) (uIcc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    unfold Psi
    refine continuousAt_id.add (ContinuousAt.div_const (ContinuousAt.mul continuousAt_const
      (ContinuousAt.sub ?_ continuousAt_const)) _)
    have hinner : Continuous fun y => G * rho (n - 1) (rn s0 σ (cn n) n y) (T n) := by
      refine continuous_const.mul ((continuous_rho _ _).comp ?_)
      unfold rn
      exact continuous_const.add
        ((continuous_const.mul (continuous_const.sub continuous_id)).div_const _)
    exact ContinuousAt.comp (f := fun y => G * rho (n - 1) (rn s0 σ (cn n) n y) (T n))
      (hcont _ (hρsmall _ (hsegl x hx))) hinner.continuousAt
  -- IVT
  obtain ⟨x, hx, hxe⟩ := intermediate_value_uIcc hcontΨ (mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩))
  set p := rn s0 σ (cn n) n x with hp
  have hpI := hsegl x hx
  have hp0 : 0 < p := by linarith [hpI.1]
  have hp1 : p < 1 := by linarith [hpI.2]
  refine ⟨p, hp0, hp1, ?_, ?_⟩
  · -- `Ψ_n(x) = c_n` is the fixed point equation
    unfold Psi at hxe
    rw [← hp] at hxe
    have h6 : √(n : ℝ) * (E.F (G * rho (n - 1) p (T n)) - s0) / σ = cn n - x := by linarith
    have h7 : E.F (G * rho (n - 1) p (T n)) - s0 = σ * (cn n - x) / √(n : ℝ) := by
      rw [div_eq_iff hσ.ne'] at h6
      rw [eq_div_iff hsnpos.ne']
      linarith
    have h8 : E.F (G * rho (n - 1) p (T n)) = s0 + σ * (cn n - x) / √(n : ℝ) := by linarith
    rw [h8]
    exact hp.symm
  · -- the tail
    have hn1 : 1 ≤ n := by omega
    have hy : √(n : ℝ) * (p - s0) / σ = cn n - x := y_rn hn1 hσ
    have hxb := habsx x hx
    have hyb : |√(n : ℝ) * (p - s0) / σ| ≤ |c| + 1 + (|a| + |b|) := by
      rw [hy]
      have := abs_sub (cn n) x
      linarith
    have hcK : |cn n| ≤ |c| + 1 + (|a| + |b|) := by linarith [abs_nonneg a, abs_nonneg b]
    have h6 := (hN₀ n hnN (T n) p hyb hcK).2
    rw [hp, uStat_rn hs0 hs1 hn1, ← hp] at h6
    have hxu : |x - u| < η := by
      rw [mem_uIcc] at hx
      have ha' := abs_lt.1 ha
      have hb' := abs_lt.1 hb
      rw [abs_lt]
      rcases hx with hx | hx <;> constructor <;> linarith [hx.1, hx.2, ha'.1, ha'.2, hb'.1, hb'.2]
    have hΦ : |Phi (-x) - Phi (-u)| < ε / 2 := by
      refine lt_of_le_of_lt (abs_Phi_sub_le _ _) ?_
      have e3 : -x - -u = -(x - u) := by ring
      rw [e3, abs_neg]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxu.le hφ0.le) hηε
    calc |btail n p (T n) - Phi (-u)| ≤ |btail n p (T n) - Phi (-x)| + |Phi (-x) - Phi (-u)| :=
          abs_sub_le _ _ _
      _ < ε := by linarith

/-- The lower bound for a regular feasible pair. -/
theorem threshold_lower_regular (hV : Assumptions E) (hN : E.Noise) {t : ℝ} (hS : Smooth E t)
    {u₁ u₀ : ℝ}
    (hfeas : fOf (t * H E / (E.F 0 * (1 - E.F 0))) u₁ = fOf (t * L E / (E.F 0 * (1 - E.F 0))) u₀)
    (hr₁ : fDeriv (t * H E / (E.F 0 * (1 - E.F 0))) u₁ ≠ 0)
    (hr₀ : fDeriv (t * L E / (E.F 0 * (1 - E.F 0))) u₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, E.PiSQ + Wval (pr E) (H E) (-L E) u₁ u₀ - ε ≤ E.PiT n := by
  have hs0 := F_zero_pos hN
  have hs1 := F_zero_lt_one hN
  set s0 := E.F 0 with hs0def
  set S := s0 * (1 - s0) with hSdef
  have hSpos : 0 < S := mul_pos hs0 (by linarith)
  set σ := √S with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hSpos
  set c := fOf (t * H E / S) u₁ with hc
  let T : ℕ → ℕ := fun n => ⌈(n : ℝ) * s0 + c * σ * √(n : ℝ)⌉₊
  have hsn : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  -- `n s0 + c σ √n ≥ 0` eventually
  have hge0 : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℝ) * s0 + c * σ * √(n : ℝ) := by
    have h1 := hsn.eventually_ge_atTop (|c * σ| / s0)
    filter_upwards [h1, eventually_ge_atTop 1] with n hn hn1
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
    have hsq := Real.mul_self_sqrt hnr.le
    rw [div_le_iff₀ hs0] at hn
    have h2 : -(|c * σ| * √(n : ℝ)) ≤ c * σ * √(n : ℝ) := by
      have := neg_abs_le (c * σ)
      nlinarith
    nlinarith
  have hTle : ∀ᶠ n : ℕ in atTop, T n ≤ n + 1 := by
    have h1 := hsn.eventually_ge_atTop (|c * σ| / (1 - s0))
    filter_upwards [h1, hge0, eventually_ge_atTop 1] with n hn h0 hn1
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
    have hsq := Real.mul_self_sqrt hnr.le
    rw [div_le_iff₀ (by linarith)] at hn
    have h2 : c * σ * √(n : ℝ) ≤ |c * σ| * √(n : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hs.le
    have h3 : (T n : ℝ) < (n : ℝ) * s0 + c * σ * √(n : ℝ) + 1 := Nat.ceil_lt_add_one h0
    have h4 : (T n : ℝ) < (n : ℝ) + 1 := by nlinarith
    have : T n < n + 1 := by exact_mod_cast h4
    omega
  -- `c_n → c`
  have hct : Tendsto (fun n : ℕ => ((T n : ℝ) - n * s0) / (σ * √(n : ℝ))) atTop (𝓝 c) := by
    have h1 : Tendsto (fun n : ℕ => 1 / (σ * √(n : ℝ))) atTop (𝓝 0) :=
      Tendsto.const_div_atTop (hsn.const_mul_atTop hσ) 1
    have h2 : Tendsto (fun n : ℕ => ((T n : ℝ) - n * s0) / (σ * √(n : ℝ)) - c) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h1
      filter_upwards [hge0, eventually_ge_atTop 1] with n h0 hn1
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
      have h3 : (T n : ℝ) < (n : ℝ) * s0 + c * σ * √(n : ℝ) + 1 := Nat.ceil_lt_add_one h0
      have h4 : (n : ℝ) * s0 + c * σ * √(n : ℝ) ≤ T n := Nat.le_ceil _
      have e : ((T n : ℝ) - n * s0) / (σ * √(n : ℝ)) - c
          = ((T n : ℝ) - ((n : ℝ) * s0 + c * σ * √(n : ℝ))) / (σ * √(n : ℝ)) := by
        field_simp
        ring
      rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < σ * √(n : ℝ))]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [abs_le]
      constructor <;> linarith
    have := h2.add_const c
    simpa using this
  -- the weights
  have hH := hV.H_pos
  have hL := hV.L_neg
  have hpr0 := hV.pr_pos
  have hpr1 := pr_lt_one hV
  set W₁ : ℝ := pr E * H E with hW₁
  set W₀ : ℝ := (1 - pr E) * (-L E) with hW₀
  have hW₁pos : 0 < W₁ := mul_pos hpr0 hH
  have hW₀pos : 0 < W₀ := mul_pos (by linarith) (by linarith)
  set ε' : ℝ := ε / (W₁ + W₀) with hε'
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  have hfp1 := exists_fixed_point hN hS (G := H E) (c := c) (u := u₁) rfl hr₁ hct hε'pos
  have hfp0 := exists_fixed_point hN hS (G := L E) (c := c) (u := u₀) hfeas.symm hr₀ hct hε'pos
  filter_upwards [hfp1, hfp0, hTle] with n h1 h0 hTn
  obtain ⟨p₁, hp₁0, hp₁1, hp₁F, hp₁t⟩ := h1
  obtain ⟨p₀, hp₀0, hp₀1, hp₀F, hp₀t⟩ := h0
  -- build the equilibrium
  let q : Bool → ℝ := fun ω => if ω then p₁ else p₀
  let cc : Bool → ℝ := fun ω => G E ω * rho (n - 1) (q ω) (T n)
  have hband : ∀ ω, E.Fm (cc ω) ≤ q ω ∧ q ω ≤ E.F (cc ω) := by
    intro ω
    have hq : E.F (cc ω) = q ω := by
      cases ω
      · exact hp₀F
      · exact hp₁F
    rw [hq]
    refine ⟨?_, le_rfl⟩
    rw [← hq]
    exact Env.Fm_le_F E _
  obtain ⟨s, hrp, hs1', hs2'⟩ := E.exists_cutoff_strategy (Measurable.of_discrete)
    (Measurable.of_discrete) hband
  have heq : E.IsEq n (dirRule true (T n)) s := by
    intro ω x
    rw [gross_dir, hrp ω]
    have e : sgn true * G E ω * rho (n - 1) (q ω) (T n) = cc ω := by
      simp [sgn, cc]
    rw [e]
    exact ⟨hs1' ω x, hs2' ω x⟩
  have hmem : E.payoff n (dirRule true (T n)) s ∈ E.payoffsT n :=
    ⟨T n, true, false, s, hTn, heq, rfl⟩
  have hle := le_csSup (Env.bddAbove_payoffsT E n) hmem
  have hpay := payoff_dir hV true n (T n) s
  rw [hrp true, hrp false] at hpay
  simp only [q, Idir, ite_true, Bool.false_eq_true, ite_false] at hpay
  have hW : Wval (pr E) (H E) (-L E) u₁ u₀ = W₁ * Phi (-u₁) - W₀ * Phi (-u₀) := rfl
  have h3 := abs_lt.1 hp₁t
  have h4 := abs_lt.1 hp₀t
  have h5 : W₁ * (Phi (-u₁) - ε') ≤ W₁ * btail n p₁ (T n) :=
    mul_le_mul_of_nonneg_left (by linarith [h3.1]) hW₁pos.le
  have h6 : W₀ * btail n p₀ (T n) ≤ W₀ * (Phi (-u₀) + ε') :=
    mul_le_mul_of_nonneg_left (by linarith [h4.2]) hW₀pos.le
  have h7 : (W₁ + W₀) * ε' = ε := by
    rw [hε']; field_simp
  have h8 : E.payoff n (dirRule true (T n)) s
      = E.PiSQ + W₁ * btail n p₁ (T n) - W₀ * btail n p₀ (T n) := by
    rw [hpay, hW₀]; ring
  have h9 : E.payoff n (dirRule true (T n)) s ≤ E.PiT n := hle
  rw [hW]
  nlinarith

/-- **Lemma `lemma_threshold_value`.** -/
theorem lemma_threshold_value (hV : Assumptions E) (hN : E.Noise) {t : ℝ} (ht : 0 < t)
    (hS : Smooth E t) :
    0 ≤ Vval (pr E) (H E) (-L E) (E.F 0 * (1 - E.F 0)) t ∧
      Tendsto E.PiT atTop (𝓝 (E.PiSQ + Vval (pr E) (H E) (-L E) (E.F 0 * (1 - E.F 0)) t)) := by
  have hs0 := F_zero_pos hN
  have hs1 := F_zero_lt_one hN
  set S := E.F 0 * (1 - E.F 0) with hSdef
  have hSpos : 0 < S := mul_pos hs0 (by linarith)
  have hpar : Par (pr E) (H E) (-L E) S := par hV hSpos
  have hV0 := Vval_nonneg hpar t
  refine ⟨hV0, ?_⟩
  set V := Vval (pr E) (H E) (-L E) S t with hVdef
  rw [tendsto_order]
  constructor
  · intro y hy
    set ε := (E.PiSQ + V - y) / 3 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    -- a nearly optimal feasible pair
    have hne : ((fun u : ℝ × ℝ => Wval (pr E) (H E) (-L E) u.1 u.2) '' feasible (H E) (-L E) S t).Nonempty := by
      obtain ⟨u, hu, _⟩ := exists_feasible_level (H E) (-L E) S t 0
      exact ⟨_, mem_image_of_mem _ hu⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, huW⟩ := exists_lt_of_lt_csSup hne (show V - ε < V by linarith)
    -- perturb to a regular pair
    obtain ⟨η, hη, hWc⟩ := Metric.continuousAt_iff.1
      ((continuous_Wval (pr E) (H E) (-L E)).continuousAt (x := u)) ε hεpos
    have hκ₁ : 0 < t * H E / S := div_pos (mul_pos ht hV.H_pos) hSpos
    have hκ₀ : t * L E / S < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht hV.L_neg) hSpos
    have hfeas : fOf (t * H E / S) u.1 = fOf (t * L E / S) u.2 := by
      unfold fOf
      have h1 : u.1 + t * H E / S * phi u.1 = u.2 - t * (-L E) / S * phi u.2 := hu
      rw [h1]
      ring
    obtain ⟨v₁, v₀, hv₁, hv₀, hveq, hr₁, hr₀⟩ := regular_dense hκ₁ hκ₀ hfeas hη
    have hdist : dist (v₁, v₀) u < η := by
      rw [Prod.dist_eq]
      exact max_lt (by rwa [Real.dist_eq]) (by rwa [Real.dist_eq])
    have hWv := hWc hdist
    rw [Real.dist_eq] at hWv
    have hWv' := abs_lt.1 hWv
    filter_upwards [threshold_lower_regular hV hN hS hveq hr₁ hr₀ hεpos] with n hn
    simp only at hWv' huW
    linarith [hWv'.1]
  · intro y hy
    set ε := (y - (E.PiSQ + V)) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    filter_upwards [threshold_upper hV hN hS hεpos] with n hn
    linarith

end VD

end NoisyVD
