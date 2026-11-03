import NoisyVD.Existence

/-!
# Proposition `prop_general_failures`, Statements 1--3

As in the paper, the three statements share one argument.  Reporting probabilities lie in
`[p_n^-, p_n^+]`, with `p_n^- = max{F((-h_n)⁻), ε_*}` and `p_n^+ = min{F(h_n), 1-ε_*}`, so that
`Π^SQ ≤ Π(n) ≤ β_n Π^SQ + (1-β_n) Π^FB` for `β_n = 1 - TV(Bin(n,p_n^-), Bin(n,p_n^+))`, and each statement
follows from the behaviour of `β_n`.

`BandFamily` records this argument apart from the model, because the proofs of Propositions
`prop_state_dependent` and `prop_noisy_signals` in the Online Appendix reuse it: "the proof of Statements
1--3 uses only that the reporting probabilities lie in `[p_n^-, p_n^+]`".
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-! ### The argument behind Statements 1--3 -/

/-- Payoff sets `V n` bounded by `β_n Π^SQ + (1-β_n) Π^FB`, for `β_n = 1 - TV(Bin(n,pm n), Bin(n,pp n))`,
with `pm n ≤ pp n` in `[l, 1-l]`, and containing `Π^SQ`. -/
structure BandFamily (E : Env A Ω) (V : ℕ → Set ℝ) (l : ℝ) (pm pp : ℕ → ℝ) : Prop where
  l_pos : 0 < l
  sq_mem : ∀ n, E.PiSQ ∈ V n
  le_fb : ∀ n, ∀ y ∈ V n, y ≤ E.PiFB
  mem : ∀ᶠ n in atTop, pm n ∈ Icc l (1 - l) ∧ pp n ∈ Icc l (1 - l) ∧ pm n ≤ pp n
  bound : ∀ᶠ n in atTop, ∀ y ∈ V n,
    y ≤ (1 - tv n (pm n) (pp n)) * E.PiSQ + tv n (pm n) (pp n) * E.PiFB

namespace BandFamily

variable {E : Env A Ω} {V : ℕ → Set ℝ} {l : ℝ} {pm pp : ℕ → ℝ}

lemma bddAbove (h : BandFamily E V l pm pp) (n : ℕ) : BddAbove (V n) := ⟨E.PiFB, h.le_fb n⟩

lemma PiSQ_le (h : BandFamily E V l pm pp) (n : ℕ) : E.PiSQ ≤ sSup (V n) :=
  le_csSup (h.bddAbove n) (h.sq_mem n)

lemma sSup_le_PiFB (h : BandFamily E V l pm pp) (n : ℕ) : sSup (V n) ≤ E.PiFB :=
  csSup_le ⟨_, h.sq_mem n⟩ (h.le_fb n)

/-- Statement 1: if eventually `pp n ≤ pm n`, then `β_n = 1` and `sup V n = Π^SQ`. -/
theorem eq_of_le (h : BandFamily E V l pm pp) (h0 : ∀ᶠ n in atTop, pp n ≤ pm n) :
    ∃ nStar : ℕ, ∀ n > nStar, sSup (V n) = E.PiSQ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.bound.and (h.mem.and h0))
  refine ⟨N, fun n hn => le_antisymm ?_ (h.PiSQ_le n)⟩
  obtain ⟨hb, ⟨_, _, hab⟩, hg⟩ := hN n hn.le
  refine csSup_le ⟨_, h.sq_mem n⟩ fun y hy => ?_
  have hy' := hb y hy
  have this : pm n = pp n := le_antisymm hab hg
  have htv : tv n (pm n) (pp n) = 0 := by
    unfold tv
    rw [this]
    simp
  rw [htv] at hy'
  simpa using hy'

/-- Statement 2: if `√n (pp n - pm n) → 0` then `β_n → 1` and `sup V n → Π^SQ`. -/
theorem tendsto (h : BandFamily E V l pm pp) {g : ℕ → ℝ} (hgap : ∀ᶠ n in atTop, pp n - pm n ≤ g n)
    (hg : Tendsto (fun n : ℕ => √(n : ℝ) * g n) atTop (𝓝 0)) :
    Tendsto (fun n => sSup (V n)) atTop (𝓝 E.PiSQ) := by
  let θ : ℕ → ℝ := fun n => √((√(n : ℝ) * g n) ^ 2 / (2 * l))
  have hθ : Tendsto θ atTop (𝓝 0) := by
    have := ((hg.pow 2).div_const (2 * l)).sqrt
    simpa [θ] using this
  have hSF := E.PiSQ_le_PiFB
  have hlim : Tendsto (fun n => E.PiSQ + θ n * (E.PiFB - E.PiSQ)) atTop (𝓝 E.PiSQ) := by
    have := (hθ.mul_const (E.PiFB - E.PiSQ)).const_add E.PiSQ
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall h.PiSQ_le) ?_
  filter_upwards [h.bound, h.mem, hgap] with n hn hm hgn
  refine csSup_le ⟨_, h.sq_mem n⟩ fun y hy => ?_
  obtain ⟨ha, hb, hab⟩ := hm
  have hy' := hn y hy
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htv : tv n (pm n) (pp n) ≤ θ n := by
    refine (tv_le_of_close h.l_pos ha hb).trans (Real.sqrt_le_sqrt ?_)
    apply div_le_div_of_nonneg_right _ (by have := h.l_pos; positivity)
    rw [mul_pow, Real.sq_sqrt hnr]
    apply mul_le_mul_of_nonneg_left _ hnr
    have : (pm n - pp n) ^ 2 = (pp n - pm n) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by linarith) hgn 2
  have : tv n (pm n) (pp n) * (E.PiFB - E.PiSQ) ≤ θ n * (E.PiFB - E.PiSQ) :=
    mul_le_mul_of_nonneg_right htv (by linarith)
  nlinarith

/-- Statement 3, the quantitative form: if `√n (pp n - pm n)` is bounded then `β_n` is bounded away from
zero. -/
theorem eventually_le_mix (h : BandFamily E V l pm pp) {g : ℕ → ℝ}
    (hgap : ∀ᶠ n in atTop, pp n - pm n ≤ g n) {C : ℝ}
    (hg : ∀ᶠ n : ℕ in atTop, √(n : ℝ) * g n ≤ C) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ᶠ n in atTop, sSup (V n) ≤ β * E.PiSQ + (1 - β) * E.PiFB := by
  have hl := h.l_pos
  set τ : ℝ := √(1 - exp (-(C ^ 2) / l)) with hτ
  have hτ1 : τ < 1 := sqrt_one_sub_exp_lt_one
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg _
  have hSF := E.PiSQ_le_PiFB
  refine ⟨min (1 - τ) (1 / 2), lt_min (by linarith) (by norm_num), by
    have := min_le_right (1 - τ) (1 / 2 : ℝ); linarith, ?_⟩
  set β := min (1 - τ) (1 / 2 : ℝ) with hβ
  have hβ1 : β ≤ 1 - τ := min_le_left _ _
  have hmC : ∀ᶠ n : ℕ in atTop, C ^ 2 / (2 * l) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [h.bound, h.mem, hgap, hg, hmC, eventually_ge_atTop 1] with n hn hm hgapn hgn hmn hn1
  refine csSup_le ⟨_, h.sq_mem n⟩ fun y hy => ?_
  obtain ⟨ha, hb, hab⟩ := hm
  have hy' := hn y hy
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hg0 : 0 ≤ g n := by linarith
  have htv : tv n (pm n) (pp n) ≤ τ := by
    refine tv_le_of_bounded hl ha hb hn1 ?_ hmn
    have h1 : (pm n - pp n) ^ 2 ≤ g n ^ 2 := by
      have : (pm n - pp n) ^ 2 = (pp n - pm n) ^ 2 := by ring
      rw [this]
      exact pow_le_pow_left₀ (by linarith) hgapn 2
    have h2 : (√(n : ℝ) * g n) ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hg0) hgn 2
    rw [mul_pow, Real.sq_sqrt hnr] at h2
    exact (mul_le_mul_of_nonneg_left h1 hnr).trans h2
  have h3 : tv n (pm n) (pp n) * (E.PiFB - E.PiSQ) ≤ (1 - β) * (E.PiFB - E.PiSQ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

/-- Statement 3. -/
theorem limsup_lt (h : BandFamily E V l pm pp) (hFB : E.PiSQ < E.PiFB) {g : ℕ → ℝ}
    (hgap : ∀ᶠ n in atTop, pp n - pm n ≤ g n) {C : ℝ}
    (hg : ∀ᶠ n : ℕ in atTop, √(n : ℝ) * g n ≤ C) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧ limsup (fun n => sSup (V n)) atTop ≤ β * E.PiSQ + (1 - β) * E.PiFB ∧
      β * E.PiSQ + (1 - β) * E.PiFB < E.PiFB := by
  obtain ⟨β, hβ0, hβ1, hβ⟩ := h.eventually_le_mix hgap hg
  refine ⟨β, hβ0, hβ1, ?_, by nlinarith⟩
  refine limsup_le_of_le ?_ hβ
  exact (isBoundedUnder_of (f := atTop) (u := fun n => sSup (V n)) (r := (· ≥ ·))
    ⟨E.PiSQ, h.PiSQ_le⟩).isCoboundedUnder_flip

end BandFamily

namespace Env

/-- `h_n = M/√n`. -/
noncomputable def hn (E : Env A Ω) (n : ℕ) : ℝ := pivConst E.B E.epsStar / √(n : ℝ)

lemma hn_pos (E : Env A Ω) (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) {n : ℕ} (hn : 1 ≤ n) : 0 < E.hn n := by
  have h0 := (lemma_noise E hE).1
  have hM := pivConst_pos (E.B_pos_of_lt hFB) h0 (epsStar_le_half E)
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos hM (Real.sqrt_pos.2 this)

/-- `p_n^- = max{F((-h_n)⁻), ε_*}`. -/
noncomputable def pMinus (E : Env A Ω) (n : ℕ) : ℝ := max (E.Fm (-(E.hn n))) E.epsStar

/-- `p_n^+ = min{F(h_n), 1-ε_*}`. -/
noncomputable def pPlus (E : Env A Ω) (n : ℕ) : ℝ := min (E.F (E.hn n)) (1 - E.epsStar)

/-- Equation `eq_general_reporting_band` and Lemma `lemma_noise`:
`p_{n,ω} ∈ [p_n^-, p_n^+] ⊆ [ε_*, 1-ε_*]`. -/
lemma rp_mem_band (E : Env A Ω) (hE : E.Noise) {n : ℕ} (hn : 2 ≤ n) {d : Rule A} {s : Strat Ω}
    (he : E.IsEq n d s) (ω : Ω) : E.rp s ω ∈ Icc (E.pMinus n) (E.pPlus n) := by
  have h1 := (lemma_noise E hE).2 n d s he ω
  have h2 := reporting_band E hE hn he ω
  exact ⟨max_le h2.1 h1.1, le_min h2.2 h1.2⟩

/-- The band is nonempty, since an equilibrium exists. -/
lemma pMinus_le_pPlus (E : Env A Ω) (hE : E.Noise) {n : ℕ} (hn : 2 ≤ n) : E.pMinus n ≤ E.pPlus n := by
  have := E.nonempty_state
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  obtain ⟨a⟩ := ‹Nonempty A›
  obtain ⟨s, he⟩ := E.exists_equilibrium n (constRule a)
  have h := E.rp_mem_band hE hn he ω₀
  exact h.1.trans h.2

/-- The argument behind Statements 1--3 applies to the main model. -/
theorem bandFamily (E : Env A Ω) (hE : E.Noise) : BandFamily E E.payoffs E.epsStar E.pMinus E.pPlus where
  l_pos := (lemma_noise E hE).1
  sq_mem := E.PiSQ_mem_payoffs
  le_fb := by
    rintro n y ⟨d, s, _, rfl⟩
    exact payoff_le_PiFB E n d s
  mem := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hab := E.pMinus_le_pPlus hE hn
    have h1 : E.epsStar ≤ E.pMinus n := le_max_right _ _
    have h2 : E.pPlus n ≤ 1 - E.epsStar := min_le_right _ _
    exact ⟨⟨h1, hab.trans h2⟩, ⟨h1.trans hab, h2⟩, hab⟩
  bound := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    rintro y ⟨d, s, he, rfl⟩
    have h0 := (lemma_noise E hE).1
    have h1 : E.epsStar ≤ E.pMinus n := le_max_right _ _
    have h2 : E.pPlus n ≤ 1 - E.epsStar := min_le_right _ _
    exact payoff_le_tv E n d s (lt_of_lt_of_le h0 h1) (lt_of_le_of_lt h2 (by linarith))
      (E.rp_mem_band hE hn he)

/-- `h_n → 0`. -/
lemma tendsto_hn (E : Env A Ω) : Tendsto E.hn atTop (𝓝 0) :=
  Tendsto.const_div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) _

/-- If `F(δ) = F(-δ)` then, once `h_n < δ`, both endpoints equal the same constant. -/
lemma pPlus_le_pMinus (E : Env A Ω) {δ : ℝ} (hδ : 0 < δ) (hF : E.F δ - E.F (-δ) = 0) :
    ∀ᶠ n in atTop, E.pPlus n ≤ E.pMinus n := by
  filter_upwards [(tendsto_order.1 E.tendsto_hn).2 δ hδ] with n hn
  have h1 : E.F (E.hn n) ≤ E.F δ := E.F_mono hn.le
  have h2 : E.F (-δ) ≤ E.Fm (-(E.hn n)) := E.F_le_Fm (by linarith)
  have h3 : E.pPlus n ≤ E.F (E.hn n) := min_le_left _ _
  have h4 : E.Fm (-(E.hn n)) ≤ E.pMinus n := le_max_left _ _
  linarith

/-- **Proposition `prop_general_failures`, Statement 1.** -/
theorem prop_general_1 (E : Env A Ω) (hE : E.Noise) {δ : ℝ} (hδ : 0 < δ)
    (hF : E.F δ - E.F (-δ) = 0) : ∃ nStar : ℕ, ∀ n > nStar, E.Pi n = E.PiSQ :=
  (E.bandFamily hE).eq_of_le (E.pPlus_le_pMinus hδ hF)

/-- The difference quotient limit behind equation `eq_derivative`. -/
lemma tendsto_sqrt_mul_gap {F : ℝ → ℝ} {t M : ℝ} (hF : HasDerivAt F t 0) (hM : 0 < M) :
    Tendsto (fun n : ℕ => √(n : ℝ) * (F (M / √(n : ℝ)) - F (-2 * (M / √(n : ℝ))))) atTop
      (𝓝 (3 * M * t)) := by
  have hslope := hF.tendsto_slope_zero
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => M / √(n : ℝ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop hsq M
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < M / √(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos hM (Real.sqrt_pos.2 this)
  have h1 : Tendsto (fun n : ℕ => M / √(n : ℝ)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hh, hpos.mono fun n hn => hn.ne'⟩
  have h2 : Tendsto (fun n : ℕ => -2 * (M / √(n : ℝ))) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hpos.mono fun n hn => ?_⟩
    · have := hh.const_mul (-2)
      simpa using this
    · have : -2 * (M / √(n : ℝ)) < 0 := by linarith
      exact this.ne
  have l1 := hslope.comp h1
  have l2 := hslope.comp h2
  have hsum := (l1.const_mul M).add (l2.const_mul (2 * M))
  have e : M * t + 2 * M * t = 3 * M * t := by ring
  rw [e] at hsum
  refine hsum.congr' ?_
  filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
  simp only [Function.comp, smul_eq_mul, zero_add]
  field_simp
  ring

/-- The gap estimate `p_n^+ - p_n^- ≤ F(h_n) - F(-2h_n)`, from `F((-h_n)⁻) ≥ F(-2h_n)`. -/
lemma pPlus_sub_pMinus_le (E : Env A Ω) (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) {n : ℕ} (hn : 1 ≤ n) :
    E.pPlus n - E.pMinus n ≤ E.F (E.hn n) - E.F (-2 * E.hn n) := by
  have h0 := E.hn_pos hE hFB hn
  have h1 : E.F (-2 * E.hn n) ≤ E.Fm (-(E.hn n)) := E.F_le_Fm (by linarith)
  have h3 : E.pPlus n ≤ E.F (E.hn n) := min_le_left _ _
  have h4 : E.Fm (-(E.hn n)) ≤ E.pMinus n := le_max_left _ _
  linarith

/-- `√n (F(h_n) - F(-2h_n)) → 3 M F'(0)`, the limit in the proof of Statements 2 and 3. -/
lemma tendsto_gap (E : Env A Ω) (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) {t : ℝ} (hF : HasDerivAt E.F t 0) :
    Tendsto (fun n : ℕ => √(n : ℝ) * (E.F (E.hn n) - E.F (-2 * E.hn n))) atTop
      (𝓝 (3 * pivConst E.B E.epsStar * t)) :=
  tendsto_sqrt_mul_gap hF
    (pivConst_pos (E.B_pos_of_lt hFB) (lemma_noise E hE).1 (epsStar_le_half E))

/-- **Proposition `prop_general_failures`, Statement 2.** -/
theorem prop_general_2 (E : Env A Ω) (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) (hF : HasDerivAt E.F 0 0) :
    Tendsto E.Pi atTop (𝓝 E.PiSQ) := by
  refine (E.bandFamily hE).tendsto (g := fun n => E.F (E.hn n) - E.F (-2 * E.hn n)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact E.pPlus_sub_pMinus_le hE hFB hn
  · have := E.tendsto_gap hE hFB hF
    simpa using this

/-- **Proposition `prop_general_failures`, Statement 3**, in the quantitative form proved in the
paper: for any differentiable `F` the limit superior is at most `β Π^SQ + (1-β) Π^FB`, `β > 0`. -/
theorem prop_general_3_quant (E : Env A Ω) (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) {t : ℝ}
    (hF : HasDerivAt E.F t 0) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ᶠ n in atTop, E.Pi n ≤ β * E.PiSQ + (1 - β) * E.PiFB := by
  refine (E.bandFamily hE).eventually_le_mix (g := fun n => E.F (E.hn n) - E.F (-2 * E.hn n))
    (C := 3 * pivConst E.B E.epsStar * t + 1) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact E.pPlus_sub_pMinus_le hE hFB hn
  · exact (tendsto_order.1 (E.tendsto_gap hE hFB hF)).2 _ (by linarith) |>.mono fun n hn => hn.le

lemma isBounded_Pi (E : Env A Ω) : IsBoundedUnder (· ≤ ·) atTop E.Pi :=
  isBoundedUnder_of ⟨E.PiFB, E.Pi_le_PiFB⟩

lemma isCobounded_Pi (E : Env A Ω) : IsCoboundedUnder (· ≤ ·) atTop E.Pi :=
  (isBoundedUnder_of (f := atTop) (u := E.Pi) (r := (· ≥ ·)) ⟨E.PiSQ, E.PiSQ_le_Pi⟩).isCoboundedUnder_le

/-- **Proposition `prop_general_failures`, Statement 3.** -/
theorem prop_general_3 (E : Env A Ω) (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) {t : ℝ}
    (hF : HasDerivAt E.F t 0) : limsup E.Pi atTop < E.PiFB := by
  obtain ⟨β, hβ0, _, hβ⟩ := prop_general_3_quant E hE hFB hF
  have h1 : limsup E.Pi atTop ≤ β * E.PiSQ + (1 - β) * E.PiFB := by
    refine limsup_le_of_le ?_ hβ
    exact (isBoundedUnder_of (f := atTop) (u := E.Pi) (r := (· ≥ ·))
      ⟨E.PiSQ, E.PiSQ_le_Pi⟩).isCoboundedUnder_flip
  nlinarith

end Env

end NoisyVD
