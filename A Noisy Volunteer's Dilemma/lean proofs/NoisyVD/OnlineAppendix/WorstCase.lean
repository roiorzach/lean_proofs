import NoisyVD.OnlineAppendix.Common
import NoisyVD.Volunteer
import NoisyVD.ThresholdUpper

/-!
# Worst-case equilibrium selection (Proposition `prop_worst_equilibrium`)

`Π̲_n = sup_d inf_{e ∈ E(d)} payoff` and its restriction `Π̲^T_n` to threshold rules.  The upper bounds
follow from the sandwich `Π^SQ ≤ Π̲^T_n ≤ Π̲_n ≤ Π(n) ≤ Π^FB`.  The new arguments are the lower bounds:

* the fixed points `z = (t x/σ²) φ(z)` are the values of the inverse `zz` of the increasing bijection
  `z ↦ z/φ(z)` of `ℝ`, which makes `J(t)` continuous and strictly increasing;
* under the threshold `⌈ns⌉`, Lemma `lemma_local_binomial` gives `u_{n,ω} + κ_ω φ(u_{n,ω}) → 0` for
  `u_{n,ω} = (T_n - n p_{n,ω})/(σ√n)`, so `(u_{n,1}, u_{n,0}) → (-z_H, z_ℓ)` and the payoff converges to
  `Π^SQ + J(t)`.  Uniformity over equilibria is proved by contradiction along a sequence of equilibria;
* with an atom at zero, Chebyshev applies uniformly over equilibria.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

namespace OA

/-! ### The function `z ↦ z/φ(z)` and its inverse -/

/-- `z ↦ z/φ(z)`. -/
noncomputable def gz (z : ℝ) : ℝ := z / phi z

lemma gz_eq (z : ℝ) : gz z = √(2 * π) * (z * exp (z ^ 2 / 2)) := by
  unfold gz phi
  have h : exp (-z ^ 2 / 2) = (exp (z ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [h]
  have h1 : √(2 * π) ≠ 0 := sqrt_two_pi_pos.ne'
  have h2 : exp (z ^ 2 / 2) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

lemma hasDerivAt_mul_exp (z : ℝ) :
    HasDerivAt (fun z : ℝ => z * exp (z ^ 2 / 2)) ((1 + z ^ 2) * exp (z ^ 2 / 2)) z := by
  have h1 : HasDerivAt (fun z : ℝ => z ^ 2 / 2) z z := by
    have := (hasDerivAt_pow 2 z).div_const 2
    simpa using this
  have h2 := (hasDerivAt_id' z).mul (h1.exp)
  convert h2 using 1
  ring

lemma gz_strictMono : StrictMono gz := by
  have h : StrictMono fun z : ℝ => z * exp (z ^ 2 / 2) := by
    refine strictMono_of_deriv_pos fun z => ?_
    rw [(hasDerivAt_mul_exp z).deriv]
    have := Real.exp_pos (z ^ 2 / 2)
    positivity
  intro a b hab
  rw [gz_eq, gz_eq]
  exact mul_lt_mul_of_pos_left (h hab) sqrt_two_pi_pos

lemma continuous_gz : Continuous gz := by
  have h : Continuous fun z : ℝ => √(2 * π) * (z * exp (z ^ 2 / 2)) := by fun_prop
  exact h.congr fun z => (gz_eq z).symm

lemma gz_neg (z : ℝ) : gz (-z) = -gz z := by
  unfold gz
  rw [phi_neg]
  ring

lemma gz_zero : gz 0 = 0 := by simp [gz]

lemma le_gz {z : ℝ} (hz : 0 ≤ z) : √(2 * π) * z ≤ gz z := by
  rw [gz_eq]
  apply mul_le_mul_of_nonneg_left _ sqrt_two_pi_pos.le
  have : 1 ≤ exp (z ^ 2 / 2) := Real.one_le_exp (by positivity)
  nlinarith

lemma tendsto_gz_atTop : Tendsto gz atTop atTop := by
  have h : Tendsto (fun z : ℝ => √(2 * π) * z) atTop atTop :=
    tendsto_id.const_mul_atTop sqrt_two_pi_pos
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [eventually_ge_atTop 0] with z hz using le_gz hz

lemma tendsto_gz_atBot : Tendsto gz atBot atBot := by
  have h : Tendsto (fun z : ℝ => -gz (-z)) atBot atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_gz_atTop.comp tendsto_neg_atBot_atTop)
  refine h.congr fun z => ?_
  rw [gz_neg]
  ring

lemma gz_surjective : Function.Surjective gz :=
  continuous_gz.surjective tendsto_gz_atTop tendsto_gz_atBot

/-- `z ↦ z/φ(z)` as an order isomorphism of `ℝ`. -/
noncomputable def gzIso : ℝ ≃o ℝ := gz_strictMono.orderIsoOfSurjective gz gz_surjective

/-- `zz κ` is the unique solution of `z = κ φ(z)`. -/
noncomputable def zz (κ : ℝ) : ℝ := gzIso.symm κ

lemma gz_zz (κ : ℝ) : gz (zz κ) = κ := gzIso.apply_symm_apply κ

lemma zz_gz (z : ℝ) : zz (gz z) = z := gzIso.symm_apply_apply z

lemma zz_spec (κ : ℝ) : zz κ = κ * phi (zz κ) := by
  have h := gz_zz κ
  unfold gz at h
  exact (div_eq_iff (phi_pos (zz κ)).ne').1 h

/-- Uniqueness of the solution of `z = κ φ(z)`. -/
lemma eq_zz {κ z : ℝ} (h : z = κ * phi z) : z = zz κ := by
  have : gz z = κ := by
    unfold gz
    have hφ := phi_pos z
    rw [div_eq_iff hφ.ne']
    exact h
  rw [← this, zz_gz]

lemma continuous_zz : Continuous zz := gzIso.symm.continuous

lemma zz_strictMono : StrictMono zz := gzIso.symm.strictMono

lemma zz_zero : zz 0 = 0 := by
  have := zz_gz 0
  rwa [gz_zero] at this

lemma zz_neg (κ : ℝ) : zz (-κ) = -zz κ := by
  have : -κ = gz (-zz κ) := by rw [gz_neg, gz_zz]
  rw [this, zz_gz]

lemma tendsto_zz_atTop : Tendsto zz atTop atTop := gzIso.symm.tendsto_atTop

/-- A bounded approximate zero of `f(u) = u + κ φ(u)` is close to `-zz κ`. -/
lemma tendsto_of_fOf {κ R : ℝ} {z : ℕ → ℝ} (hz : ∀ᶠ j in atTop, |z j| ≤ R)
    (h : Tendsto (fun j => fOf κ (z j)) atTop (𝓝 0)) : Tendsto z atTop (𝓝 (-zz κ)) := by
  have hR : 0 < phi R := phi_pos R
  have h1 : Tendsto (fun j => gz (-z j)) atTop (𝓝 κ) := by
    have herr : Tendsto (fun j => fOf κ (z j) / phi (z j)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun j => |fOf κ (z j)| / phi R) ?_ ?_
      · filter_upwards [hz] with j hj
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (phi_pos _)]
        apply div_le_div_of_nonneg_left (abs_nonneg _) hR
        have := phi_anti (abs_nonneg (z j)) hj
        rw [show phi |z j| = phi (z j) by
          rcases abs_cases (z j) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
          exact phi_neg _] at this
        have hRabs : phi R = phi R := rfl
        exact this
      · have := h.abs.div_const (phi R)
        simpa using this
    have := herr.const_sub κ
    rw [sub_zero] at this
    refine this.congr fun j => ?_
    unfold fOf gz
    rw [phi_neg]
    have hφ := phi_pos (z j)
    field_simp
    ring
  have h2 := continuous_zz.continuousAt.tendsto.comp h1
  have h3 := h2.neg
  refine h3.congr fun j => ?_
  simp only [Function.comp, zz_gz, neg_neg]

/-! ### The function `J` and the constant `\underline F_0` -/

/-- `J(t) = π H Φ(z_H(t)) - (1-π) ℓ Φ(-z_ℓ(t))`, with `z_x(t) = zz (t x/S)`, `S = σ²`. -/
noncomputable def Jfun (pr H l S t : ℝ) : ℝ :=
  pr * H * Phi (zz (t * H / S)) - (1 - pr) * l * Phi (-zz (t * l / S))

/-- `\underline F_0`: the zero of `J`. It depends on the primitives only through `π, H, ℓ, F(0)`. -/
noncomputable def Fworst (pr H l S : ℝ) : ℝ := sInf {t : ℝ | 0 ≤ Jfun pr H l S t}

section Cutoff

variable {pr H l S : ℝ}

lemma continuous_Jfun (pr H l S : ℝ) : Continuous (Jfun pr H l S) := by
  unfold Jfun
  have h1 : Continuous fun t : ℝ => Phi (zz (t * H / S)) :=
    continuous_Phi.comp (continuous_zz.comp (by fun_prop))
  have h2 : Continuous fun t : ℝ => Phi (-zz (t * l / S)) :=
    continuous_Phi.comp ((continuous_zz.comp (by fun_prop)).neg)
  exact (continuous_const.mul h1).sub (continuous_const.mul h2)

lemma Jfun_strictMono (hp : Par pr H l S) : StrictMono (Jfun pr H l S) := by
  intro a b hab
  unfold Jfun
  have hH := hp.H0
  have hl := hp.l0
  have hS := hp.S0
  have h1 : Phi (zz (a * H / S)) < Phi (zz (b * H / S)) :=
    Phi_strictMono (zz_strictMono (by gcongr))
  have h2 : Phi (-zz (b * l / S)) < Phi (-zz (a * l / S)) :=
    Phi_strictMono (neg_lt_neg (zz_strictMono (by gcongr)))
  have hb1 : 0 < pr * H := mul_pos hp.pr0 hH
  have hb0 : 0 < (1 - pr) * l := mul_pos (by linarith [hp.pr1]) hl
  nlinarith

/-- `lim_{t↓0} J(t) = ½ [π H - (1-π) ℓ] < 0`. -/
lemma Jfun_zero (_hp : Par pr H l S) : Jfun pr H l S 0 = (pr * H - (1 - pr) * l) / 2 := by
  unfold Jfun
  simp only [zero_mul, zero_div, zz_zero, neg_zero, Phi_zero]
  ring

lemma Jfun_zero_neg (hp : Par pr H l S) : Jfun pr H l S 0 < 0 := by
  rw [Jfun_zero hp]
  have := hp.prior
  linarith

/-- `lim_{t→∞} J(t) = π H > 0`. -/
lemma tendsto_Jfun_atTop (hp : Par pr H l S) : Tendsto (Jfun pr H l S) atTop (𝓝 (pr * H)) := by
  have h1 : Tendsto (fun t : ℝ => zz (t * H / S)) atTop atTop := by
    refine tendsto_zz_atTop.comp ?_
    exact tendsto_id.atTop_mul_const (div_pos hp.H0 hp.S0) |>.congr fun t => by simp [id]; ring
  have h2 : Tendsto (fun t : ℝ => zz (t * l / S)) atTop atTop := by
    refine tendsto_zz_atTop.comp ?_
    exact tendsto_id.atTop_mul_const (div_pos hp.l0 hp.S0) |>.congr fun t => by simp [id]; ring
  have h3 : Tendsto (fun t : ℝ => Phi (zz (t * H / S))) atTop (𝓝 1) := tendsto_Phi_atTop.comp h1
  have h4 : Tendsto (fun t : ℝ => Phi (-zz (t * l / S))) atTop (𝓝 0) :=
    tendsto_Phi_atBot.comp (tendsto_neg_atTop_atBot.comp h2)
  have := (h3.const_mul (pr * H)).sub (h4.const_mul ((1 - pr) * l))
  simp only [mul_one, mul_zero, sub_zero] at this
  exact this

/-- There is a unique `\underline F_0 ∈ (0, ∞)` with `J(\underline F_0) = 0`. -/
theorem Fworst_spec (hp : Par pr H l S) :
    0 < Fworst pr H l S ∧ Jfun pr H l S (Fworst pr H l S) = 0 ∧
      ∀ t, 0 < Jfun pr H l S t ↔ Fworst pr H l S < t := by
  have hb1 : 0 < pr * H := mul_pos hp.pr0 hp.H0
  have hcont := continuous_Jfun pr H l S
  have hmono := Jfun_strictMono hp
  obtain ⟨t₁, ht₁⟩ := ((tendsto_order.1 (tendsto_Jfun_atTop hp)).1 0 hb1).exists
  have h0 := Jfun_zero_neg hp
  have ht₁pos : 0 < t₁ := by
    by_contra hcon
    exact absurd (hmono.monotone (not_lt.1 hcon)) (not_le.2 (h0.trans ht₁))
  obtain ⟨tz, htz, hJz⟩ : ∃ tz ∈ Ioo (0 : ℝ) t₁, Jfun pr H l S tz = 0 := by
    have := intermediate_value_Ioo ht₁pos.le hcont.continuousOn
    exact this ⟨h0, ht₁⟩
  have hset : {t : ℝ | 0 ≤ Jfun pr H l S t} = Ici tz := by
    ext t
    simp only [mem_ofPred_eq, mem_Ici]
    rw [← hJz]
    exact hmono.le_iff_le
  have hF : Fworst pr H l S = tz := by
    unfold Fworst
    rw [hset, csInf_Ici]
  rw [hF]
  refine ⟨htz.1, hJz, fun t => ?_⟩
  rw [← hJz]
  exact hmono.lt_iff_lt

end Cutoff

end OA

namespace Env

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

variable (E : Env A Ω)

/-- The payoffs of the equilibria under the rule `d`. -/
def eqPayoffs (n : ℕ) (d : Rule A) : Set ℝ := {y | ∃ s : Strat Ω, E.IsEq n d s ∧ y = E.payoff n d s}

/-- `inf_{e ∈ E(d)} E_{e,d}[u^p(a,ω)]`. -/
noncomputable def worstPayoff (n : ℕ) (d : Rule A) : ℝ := sInf (E.eqPayoffs n d)

/-- `Π̲_n`. -/
noncomputable def PiW (n : ℕ) : ℝ := sSup (range (E.worstPayoff n))

/-- `Π̲^T_n`. -/
noncomputable def PiWT (n : ℕ) : ℝ :=
  sSup {y | ∃ (T : ℕ) (a₁ a₀ : A), T ≤ n + 1 ∧ y = E.worstPayoff n (thresholdRule T a₁ a₀)}

lemma eqPayoffs_nonempty (n : ℕ) (d : Rule A) : (E.eqPayoffs n d).Nonempty := by
  obtain ⟨s, hs⟩ := E.exists_equilibrium n d
  exact ⟨_, s, hs, rfl⟩

lemma abs_payoff_le (n : ℕ) (d : Rule A) (s : Strat Ω) :
    |E.payoff n d s| ≤ max |E.uMax| |E.uMin| := by
  have h := norm_integral_le_of_norm_le_const (μ := (E.prior : Measure Ω))
    (f := fun ω => bexp n (E.rp s ω) (fun k => E.v d k ω)) (C := max |E.uMax| |E.uMin|)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact E.abs_bexp_le n d (rp_nonneg E s ω) (rp_le_one E s ω) ω)
  simpa [payoff] using h

lemma bddBelow_eqPayoffs (n : ℕ) (d : Rule A) : BddBelow (E.eqPayoffs n d) :=
  ⟨-max |E.uMax| |E.uMin|, by
    rintro y ⟨s, _, rfl⟩
    exact (abs_le.1 (E.abs_payoff_le n d s)).1⟩

lemma worstPayoff_le (n : ℕ) {d : Rule A} {s : Strat Ω} (he : E.IsEq n d s) :
    E.worstPayoff n d ≤ E.payoff n d s :=
  csInf_le (E.bddBelow_eqPayoffs n d) ⟨s, he, rfl⟩

lemma le_worstPayoff (n : ℕ) (d : Rule A) {c : ℝ} (h : ∀ s : Strat Ω, E.IsEq n d s → c ≤ E.payoff n d s) :
    c ≤ E.worstPayoff n d :=
  le_csInf (E.eqPayoffs_nonempty n d) (by rintro y ⟨s, he, rfl⟩; exact h s he)

lemma worstPayoff_le_Pi (n : ℕ) (d : Rule A) : E.worstPayoff n d ≤ E.Pi n := by
  obtain ⟨s, hs⟩ := E.exists_equilibrium n d
  exact (E.worstPayoff_le n hs).trans (le_csSup (E.bddAbove_payoffs n) ⟨d, s, hs, rfl⟩)

lemma bddAbove_range_worst (n : ℕ) : BddAbove (range (E.worstPayoff n)) :=
  ⟨E.Pi n, by rintro y ⟨d, rfl⟩; exact E.worstPayoff_le_Pi n d⟩

lemma bddAbove_worstT (n : ℕ) :
    BddAbove {y | ∃ (T : ℕ) (a₁ a₀ : A), T ≤ n + 1 ∧ y = E.worstPayoff n (thresholdRule T a₁ a₀)} :=
  ⟨E.Pi n, by rintro y ⟨T, a₁, a₀, _, rfl⟩; exact E.worstPayoff_le_Pi n _⟩

lemma worst_mem_T (n T : ℕ) (a₁ a₀ : A) (hT : T ≤ n + 1) :
    E.worstPayoff n (thresholdRule T a₁ a₀) ≤ E.PiWT n :=
  le_csSup (E.bddAbove_worstT n) ⟨T, a₁, a₀, hT, rfl⟩

/-- A constant threshold rule that selects a status quo action guarantees `Π^SQ` in every equilibrium. -/
lemma worst_const_eq (n : ℕ) : ∃ a : A, E.worstPayoff n (thresholdRule 0 a a) = E.PiSQ := by
  obtain ⟨a, ha⟩ := E.exists_statusQuo
  refine ⟨a, le_antisymm ?_ ?_⟩
  · obtain ⟨s, hs⟩ := E.exists_equilibrium n (thresholdRule 0 a a)
    refine (E.worstPayoff_le n hs).trans (le_of_eq ?_)
    rw [E.payoff_const (thresholdRule_self 0 a), ha]
  · refine E.le_worstPayoff n _ fun s _ => ?_
    rw [E.payoff_const (thresholdRule_self 0 a), ha]

lemma PiSQ_le_PiWT (n : ℕ) : E.PiSQ ≤ E.PiWT n := by
  obtain ⟨a, ha⟩ := E.worst_const_eq n
  rw [← ha]
  exact E.worst_mem_T n 0 a a (Nat.zero_le _)

lemma PiWT_le_PiW (n : ℕ) : E.PiWT n ≤ E.PiW n := by
  obtain ⟨a, _⟩ := E.worst_const_eq n
  refine csSup_le ⟨_, 0, a, a, Nat.zero_le _, rfl⟩ ?_
  rintro y ⟨T, a₁, a₀, _, rfl⟩
  exact le_csSup (E.bddAbove_range_worst n) ⟨_, rfl⟩

lemma PiW_le_Pi (n : ℕ) : E.PiW n ≤ E.Pi n := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact csSup_le ⟨_, constRule a, rfl⟩ (by rintro y ⟨d, rfl⟩; exact E.worstPayoff_le_Pi n d)

/-- **Equation `eq_worst_equilibrium_sandwich`.** -/
theorem sandwich (n : ℕ) :
    E.PiSQ ≤ E.PiWT n ∧ E.PiWT n ≤ E.PiW n ∧ E.PiW n ≤ E.Pi n ∧ E.Pi n ≤ E.PiFB :=
  ⟨E.PiSQ_le_PiWT n, E.PiWT_le_PiW n, E.PiW_le_Pi n, E.Pi_le_PiFB n⟩

/-! ### The upper bounds of Proposition `prop_worst_equilibrium`

The paper states the proposition for the Volunteer's Dilemma and does not note this, but Statements 1 and 2
and the first claim in Statement 3 hold in the general model. They follow from the sandwich above and
Statements 1-3 of Proposition `prop_general_failures`. `prop_worst_equilibrium` below specializes them. -/

/-- Statement 1, for the general model. -/
theorem worst_statement1 (hE : E.Noise) {δ : ℝ} (hδ : 0 < δ) (hF : E.F δ - E.F (-δ) = 0) :
    ∃ nStar : ℕ, ∀ n > nStar, E.PiW n = E.PiSQ := by
  obtain ⟨N, hN⟩ := E.prop_general_1 hE hδ hF
  refine ⟨N, fun n hn => le_antisymm ?_ ?_⟩
  · rw [← hN n hn]
    exact E.PiW_le_Pi n
  · exact (E.PiSQ_le_PiWT n).trans (E.PiWT_le_PiW n)

/-- Statement 2, for the general model. -/
theorem worst_statement2 (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) (hF : HasDerivAt E.F 0 0) :
    Tendsto E.PiW atTop (𝓝 E.PiSQ) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (E.prop_general_2 hE hFB hF)
    (fun n => (E.PiSQ_le_PiWT n).trans (E.PiWT_le_PiW n)) E.PiW_le_Pi

/-- Statement 3, first claim, for the general model. -/
theorem worst_statement3 (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) {t : ℝ} (hF : HasDerivAt E.F t 0) :
    limsup E.PiW atTop < E.PiFB := by
  obtain ⟨β, hβ0, _, hβ⟩ := E.prop_general_3_quant hE hFB hF
  have h1 : limsup E.PiW atTop ≤ β * E.PiSQ + (1 - β) * E.PiFB := by
    refine limsup_le_of_le ?_ (hβ.mono fun n hn => (E.PiW_le_Pi n).trans hn)
    exact (isBoundedUnder_of (f := atTop) (u := E.PiW) (r := (· ≥ ·))
      ⟨E.PiSQ, fun n => (E.PiSQ_le_PiWT n).trans (E.PiWT_le_PiW n)⟩).isCoboundedUnder_flip
  nlinarith

end Env

namespace OA

variable {E : Env Bool Bool}

/-! ### Statement 3: the lower bound -/

/-- **Equation `eq_vd_fixed_point`.** For all large `n`, in every equilibrium under every threshold rule,
`p_{n,1} = F(H ρ_{n,1})` and `p_{n,0} = F(L ρ_{n,0})`. -/
theorem eq_vd_fixed_point (hN : E.Noise) {t : ℝ} (hS : VD.Smooth E t) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (T : ℕ) (s : Strat Bool), E.IsEq n (VD.dirRule true T) s →
      E.rp s true = E.F (VD.H E * rho (n - 1) (E.rp s true) T) ∧
        E.rp s false = E.F (VD.L E * rho (n - 1) (E.rp s false) T) := by
  obtain ⟨hl0, hLem1⟩ := Env.lemma_noise E hN
  obtain ⟨ε₀, hε₀, hcont⟩ := hS.cont
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => Env.pivConst E.B E.epsStar / √(n : ℝ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop hsq _
  obtain ⟨N, hN'⟩ := eventually_atTop.1
    ((tendsto_order.1 hlim).2 ε₀ hε₀ |>.and (eventually_ge_atTop 2))
  refine ⟨N, fun n hn T s he => ?_⟩
  obtain ⟨hsmall, hn2⟩ := hN' n hn
  have key : ∀ ω, E.rp s ω = E.F (E.gross n (VD.dirRule true T) (E.rp s ω) ω) := fun ω => by
    have h1 := Env.abs_gross_le_pivot E hN hn2 (VD.dirRule true T) (hLem1 n _ s he ω) ω
    exact VD.rp_eq_F he (hcont _ (lt_of_le_of_lt h1 hsmall))
  have hg : ∀ ω p, E.gross n (VD.dirRule true T) p ω = VD.G E ω * rho (n - 1) p T := fun ω p => by
    rw [VD.gross_dir]
    simp [VD.sgn]
  constructor
  · have := key true
    rwa [hg] at this
  · have := key false
    rwa [hg] at this

/-- Under the threshold `⌈ns⌉`, the payoff of every equilibrium is within `ε` of `Π^SQ + J(t)`, for
all large `n`. -/
theorem payoff_ceil_close (hV : VD.Assumptions E) (hN : E.Noise) {t : ℝ} (hS : VD.Smooth E t) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s : Strat Bool, E.IsEq n (VD.dirRule true ⌈(n : ℝ) * E.F 0⌉₊) s →
      |E.payoff n (VD.dirRule true ⌈(n : ℝ) * E.F 0⌉₊) s
        - (E.PiSQ + Jfun (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) t)| < ε := by
  by_contra hcon
  push Not at hcon
  choose n hnge s he hbad using hcon
  have hs0 := VD.F_zero_pos hN
  have hs1 := VD.F_zero_lt_one hN
  set s0 := E.F 0 with hs0def
  set S := s0 * (1 - s0) with hSdef
  have hSpos : 0 < S := mul_pos hs0 (by linarith)
  set σ := √S with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hSpos
  obtain ⟨hl0, hLem1⟩ := Env.lemma_noise E hN
  have hl1 := Env.epsStar_le_half E
  set l := E.epsStar with hldef
  set M := Env.pivConst E.B l with hM
  let T : ℕ → ℕ := fun j => ⌈(n j : ℝ) * s0⌉₊
  have hnt : Tendsto n atTop atTop := tendsto_atTop_mono hnge tendsto_id
  have hn2 : ∀ᶠ j in atTop, 2 ≤ n j := hnt.eventually_ge_atTop 2
  have hN1 : ∀ᶠ j in atTop, 1 ≤ n j := hnt.eventually_ge_atTop 1
  have hNt : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hnt
  have hsqrtN : Tendsto (fun j => √(n j : ℝ)) atTop atTop := Real.tendsto_sqrt_atTop.comp hNt
  let p : Bool → ℕ → ℝ := fun ω j => E.rp (s j) ω
  have hpI : ∀ ω j, p ω j ∈ Icc l (1 - l) := fun ω j => hLem1 _ _ _ (he j) ω
  let x : Bool → ℕ → ℝ := fun ω j => E.gross (n j) (VD.dirRule true (T j)) (p ω j) ω
  have hxeq : ∀ ω j, x ω j = VD.sgn true * VD.G E ω * rho (n j - 1) (p ω j) (T j) :=
    fun ω j => VD.gross_dir true _ _ _ ω
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
  have hfix : ∀ ω, ∀ᶠ j in atTop, p ω j = E.F (x ω j) := fun ω => by
    filter_upwards [hsmall ω] with j hj
    exact VD.rp_eq_F (he j) (hcont _ hj)
  -- `y` is bounded
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
  -- `c_j = (T_j - n_j s)/(σ √n_j) → 0`
  let c : ℕ → ℝ := fun j => ((T j : ℝ) - n j * s0) / (σ * √(n j : ℝ))
  have hct : Tendsto c atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => (1 / σ) / √(n j : ℝ)) atTop (𝓝 0) :=
      Tendsto.const_div_atTop hsqrtN (1 / σ)
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [hN1] with j hj
    have hNr : (0 : ℝ) < n j := by exact_mod_cast hj
    have hs : 0 < √(n j : ℝ) := Real.sqrt_pos.2 hNr
    have hnτ : 0 ≤ (n j : ℝ) * s0 := by positivity
    have hc1 : (T j : ℝ) < (n j : ℝ) * s0 + 1 := Nat.ceil_lt_add_one hnτ
    have hc0 : (n j : ℝ) * s0 ≤ (T j : ℝ) := Nat.le_ceil _
    simp only [c]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (T j : ℝ) - n j * s0 by linarith),
      abs_of_pos (mul_pos hσ hs), div_le_div_iff₀ (mul_pos hσ hs) hs]
    have hs2 : (1 / σ) * (σ * √(n j : ℝ)) = √(n j : ℝ) := by
      field_simp
    rw [hs2]
    nlinarith
  -- the variables `u_{n,ω}` are bounded
  have hσσ : σ * σ = S := Real.mul_self_sqrt hSpos.le
  let u : Bool → ℕ → ℝ := fun ω j => uStat s0 (n j) (T j) (p ω j)
  have hc1 : ∀ᶠ j in atTop, |c j| ≤ 1 := by
    have := hct.abs
    rw [abs_zero] at this
    exact (tendsto_order.1 this).2 1 one_pos |>.mono fun j hj => hj.le
  have huc : ∀ ω, ∀ᶠ j in atTop, u ω j = c j - y ω j := fun ω => by
    filter_upwards [hN1] with j hj
    exact uStat_eq hs0 hs1 hj _ _
  have hz : ∀ ω, ∀ᶠ j in atTop, |u ω j| ≤ K + 1 := fun ω => by
    filter_upwards [huc ω, hc1, hybd ω] with j h1 h2 h3
    rw [h1]
    have := abs_sub (c j) (y ω j)
    linarith
  set K₂ : ℝ := |K| + 1 with hK₂
  have hyK₂ : ∀ ω, ∀ᶠ j in atTop, |y ω j| ≤ K₂ := fun ω =>
    (hybd ω).mono fun j hj => by
      rw [hK₂]
      linarith [le_abs_self K]
  have hcK₂ : ∀ᶠ j in atTop, |c j| ≤ K₂ := hc1.mono fun j hj => by
    rw [hK₂]
    linarith [abs_nonneg K]
  -- Lemma `lemma_local_binomial`
  have hunif : ∀ ω, ∀ δ > 0, ∀ᶠ j in atTop,
      |√(n j : ℝ) * rho (n j - 1) (p ω j) (T j) - phi (u ω j) / σ| < δ ∧
        |btail (n j) (p ω j) (T j) - Phi (-u ω j)| < δ := fun ω δ hδ => by
    obtain ⟨N, hN'⟩ := pivot_tail_uniform hs0 hs1 K₂ hδ
    filter_upwards [hnt.eventually_ge_atTop N, hyK₂ ω, hcK₂] with j h1 h2 h3
    exact hN' _ h1 _ _ h2 h3
  have he1 : ∀ ω, Tendsto (fun j => √(n j : ℝ) * rho (n j - 1) (p ω j) (T j) - phi (u ω j) / σ) atTop
      (𝓝 0) := fun ω => by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    filter_upwards [hunif ω δ hδ] with j hj
    rw [Real.dist_eq, sub_zero]
    exact hj.1
  -- the fixed-point asymptotics `u_{n,ω} + κ_ω φ(u_{n,ω}) → 0`
  have hzlim : ∀ ω, Tendsto (u ω) atTop (𝓝 (-zz (t * VD.G E ω / S))) := fun ω => by
    have hxb : ∀ᶠ j in atTop, |√(n j : ℝ) * x ω j| ≤ M := by
      filter_upwards [hxbd ω, hN1] with j h1 h2
      have hNr : (0 : ℝ) < n j := by exact_mod_cast h2
      have hs : 0 < √(n j : ℝ) := Real.sqrt_pos.2 hNr
      rw [abs_mul, abs_of_pos hs]
      rw [le_div_iff₀ hs] at h1
      linarith
    have herr := tendsto_sqrt_mul_F_err hS.hasDeriv rfl hnt hxb
    have hsum : Tendsto (fun j => c j - (√(n j : ℝ) * (E.F (x ω j) - s0 - t * x ω j)) / σ
        - t * VD.G E ω / σ * (√(n j : ℝ) * rho (n j - 1) (p ω j) (T j) - phi (u ω j) / σ)) atTop (𝓝 0) := by
      have := (hct.sub (herr.div_const σ)).sub ((he1 ω).const_mul (t * VD.G E ω / σ))
      simpa using this
    have h2 : Tendsto (fun j => fOf (t * VD.G E ω / S) (u ω j)) atTop (𝓝 0) := by
      refine hsum.congr' ?_
      filter_upwards [huc ω, hfix ω] with j h3 h4
      have hxe : x ω j = VD.G E ω * rho (n j - 1) (p ω j) (T j) := by
        have h5 := hxeq ω j
        have hsg : VD.sgn true = 1 := rfl
        rw [hsg, one_mul] at h5
        exact h5
      have hyj : y ω j = √(n j : ℝ) * (E.F (x ω j) - s0) / σ := by
        simp only [y]
        rw [← h4]
      unfold fOf
      rw [← hσσ]
      have hne := hσ.ne'
      have huj : u ω j = c j - √(n j : ℝ) * (E.F (x ω j) - s0) / σ := by rw [h3, hyj]
      rw [huj, hxe]
      field_simp
      ring
    exact tendsto_of_fOf (hz ω) h2
  -- the tails
  have hI : ∀ ω, Tendsto (fun j => btail (n j) (p ω j) (T j) - Phi (-(u ω j))) atTop (𝓝 0) := by
    intro ω
    rw [Metric.tendsto_nhds]
    intro δ hδ
    filter_upwards [hunif ω δ hδ] with j hj
    rw [Real.dist_eq, sub_zero]
    exact hj.2
  have hPhi : ∀ ω, Tendsto (fun j => btail (n j) (p ω j) (T j)) atTop
      (𝓝 (Phi (zz (t * VD.G E ω / S)))) := fun ω => by
    have h1 : Tendsto (fun j => Phi (-(u ω j))) atTop (𝓝 (Phi (zz (t * VD.G E ω / S)))) := by
      have h2 := continuous_Phi.continuousAt.tendsto.comp (hzlim ω).neg
      simpa only [neg_neg, Function.comp_def] using h2
    have h3 := (hI ω).add h1
    rw [zero_add] at h3
    refine h3.congr fun j => ?_
    ring
  -- the limit of the payoffs
  have hpayoff : ∀ j, E.payoff (n j) (VD.dirRule true (T j)) (s j)
      = E.PiSQ + VD.pr E * VD.H E * btail (n j) (p true j) (T j)
        + (1 - VD.pr E) * VD.L E * btail (n j) (p false j) (T j) := fun j => by
    rw [VD.payoff_dir hV]
    simp only [VD.Idir, ite_true]
    rfl
  have hlim : Tendsto (fun j => E.payoff (n j) (VD.dirRule true (T j)) (s j)) atTop
      (𝓝 (E.PiSQ + Jfun (VD.pr E) (VD.H E) (-VD.L E) S t)) := by
    have h1 := ((hPhi true).const_mul (VD.pr E * VD.H E)).add
      ((hPhi false).const_mul ((1 - VD.pr E) * VD.L E))
    have h2 := h1.const_add E.PiSQ
    have e : E.PiSQ + (VD.pr E * VD.H E * Phi (zz (t * VD.G E true / S))
        + (1 - VD.pr E) * VD.L E * Phi (zz (t * VD.G E false / S)))
        = E.PiSQ + Jfun (VD.pr E) (VD.H E) (-VD.L E) S t := by
      have h3 : VD.G E true = VD.H E := rfl
      have h4 : VD.G E false = VD.L E := rfl
      rw [h3, h4]
      unfold Jfun
      have h5 : t * VD.L E / S = -(t * (-VD.L E) / S) := by ring
      rw [h5, zz_neg]
      ring
    rw [e] at h2
    refine h2.congr fun j => ?_
    rw [hpayoff j]
    ring
  have hclose := (tendsto_order.1 (hlim.sub_const (E.PiSQ + Jfun (VD.pr E) (VD.H E) (-VD.L E) S t)))
  simp only [sub_self] at hclose
  obtain ⟨j, hj1, hj2⟩ := ((hclose.1 (-ε) (by linarith)).and (hclose.2 ε hε)).exists
  exact absurd (abs_lt.2 ⟨hj1, hj2⟩) (not_lt.2 (hbad j))

lemma ceil_le_succ {n : ℕ} {τ : ℝ} (_hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : ⌈(n : ℝ) * τ⌉₊ ≤ n + 1 := by
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : ⌈(n : ℝ) * τ⌉₊ ≤ n := Nat.ceil_le.2 (by nlinarith)
  omega

/-- `lim_n inf_{e ∈ E(d_n)} payoff = Π^SQ + J(t)`, for `d_n` the threshold rule at `⌈ns⌉`. -/
theorem tendsto_worst_ceil (hV : VD.Assumptions E) (hN : E.Noise) {t : ℝ} (hS : VD.Smooth E t) :
    Tendsto (fun n : ℕ => E.worstPayoff n (VD.dirRule true ⌈(n : ℝ) * E.F 0⌉₊)) atTop
      (𝓝 (E.PiSQ + Jfun (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) t)) := by
  set J := Jfun (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) t with hJ
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN'⟩ := payoff_ceil_close hV hN hS (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : E.PiSQ + J - ε / 2 ≤ E.worstPayoff n (VD.dirRule true ⌈(n : ℝ) * E.F 0⌉₊) := by
      refine E.le_worstPayoff n _ fun s he => ?_
      have := abs_lt.1 (hN' n hn s he)
      linarith [this.1]
    linarith
  · obtain ⟨s, he⟩ := E.exists_equilibrium n (VD.dirRule true ⌈(n : ℝ) * E.F 0⌉₊)
    have h1 := E.worstPayoff_le n he
    have := abs_lt.1 (hN' n hn s he)
    linarith [this.2]

/-- `liminf Π̲^T_n ≥ Π^SQ + max{0, J(t)}`. -/
theorem le_liminf_PiWT (hV : VD.Assumptions E) (hN : E.Noise) {t : ℝ} (hS : VD.Smooth E t) :
    E.PiSQ + max 0 (Jfun (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) t)
      ≤ liminf E.PiWT atTop := by
  have hs0 := VD.F_zero_pos hN
  have hs1 := VD.F_zero_lt_one hN
  have hco : IsCoboundedUnder (· ≥ ·) atTop E.PiWT :=
    (isBoundedUnder_of (f := atTop) (u := E.PiWT) (r := (· ≤ ·))
      ⟨E.PiFB, fun n => ((E.PiWT_le_PiW n).trans (E.PiW_le_Pi n)).trans (E.Pi_le_PiFB n)⟩).isCoboundedUnder_ge
  have hbd : IsBoundedUnder (· ≥ ·) atTop E.PiWT :=
    isBoundedUnder_of (f := atTop) (u := E.PiWT) (r := (· ≥ ·)) ⟨E.PiSQ, E.PiSQ_le_PiWT⟩
  have hq0 : E.PiSQ ≤ liminf E.PiWT atTop :=
    le_liminf_of_le hco (Eventually.of_forall E.PiSQ_le_PiWT)
  have hq1 : E.PiSQ + Jfun (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) t
      ≤ liminf E.PiWT atTop := by
    have hlim := tendsto_worst_ceil hV hN hS
    have hle : (fun n : ℕ => E.worstPayoff n (VD.dirRule true ⌈(n : ℝ) * E.F 0⌉₊)) ≤ E.PiWT := fun n =>
      E.worst_mem_T n _ true false (ceil_le_succ hs0.le hs1.le)
    calc _ = liminf (fun n : ℕ => E.worstPayoff n (VD.dirRule true ⌈(n : ℝ) * E.F 0⌉₊)) atTop :=
          hlim.liminf_eq.symm
      _ ≤ liminf E.PiWT atTop :=
          liminf_le_liminf (Eventually.of_forall hle) hlim.isBoundedUnder_ge hco
  rcases le_total 0 (Jfun (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) t) with h | h
  · rwa [max_eq_right h]
  · rw [max_eq_left h, add_zero]
    exact hq0

/-! ### Statement 4 -/

/-- **Statement 4.** -/
theorem worst_statement4 (hV : VD.Assumptions E) (hN : E.Noise) {α : ℝ} (hα : 0 < α)
    (h : Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α)) :
    Tendsto E.PiWT atTop (𝓝 E.PiFB) := by
  have hat := E.atom_pos hα h
  set hi := E.F 0 with hhi
  set lo := E.Fm 0 with hlo
  set τ := (hi + lo) / 2 with hτ
  set η := (hi - lo) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hlo0 : 0 ≤ lo := E.Fm_nonneg 0
  have hhi1 : hi ≤ 1 := E.F_le_one 0
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  have hτ1 : τ ≤ 1 := by rw [hτ]; linarith
  obtain ⟨hl0, hLem1⟩ := Env.lemma_noise E hN
  have hl1 := Env.epsStar_le_half E
  refine tendsto_of_rate (fun n => ((E.PiWT_le_PiW n).trans (E.PiW_le_Pi n)).trans (E.Pi_le_PiFB n))
    (C := (VD.pr E * VD.H E - (1 - VD.pr E) * VD.L E) * (1 / η ^ 2)) ?_
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 / η ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hlarge, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨hT1, hTn⟩ := ceil_mem (n := n) hτ0 hτ1 hn1
  set T := ⌈(n : ℝ) * τ⌉₊ with hT
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have e : (VD.pr E * VD.H E - (1 - VD.pr E) * VD.L E) * (1 / η ^ 2) * (1 / (n : ℝ))
      = (VD.pr E * VD.H E - (1 - VD.pr E) * VD.L E) * (1 / ((n : ℝ) * η ^ 2)) := by
    field_simp
  rw [e]
  have hmain : E.PiFB - (VD.pr E * VD.H E - (1 - VD.pr E) * VD.L E) * (1 / ((n : ℝ) * η ^ 2))
      ≤ E.worstPayoff n (VD.dirRule true T) := by
    refine E.le_worstPayoff n _ fun s he => ?_
    have hmem : ∀ ω, 0 < E.rp s ω ∧ E.rp s ω < 1 := fun ω => by
      have h1 := hLem1 n _ s he ω
      exact ⟨lt_of_lt_of_le hl0 h1.1, lt_of_le_of_lt h1.2 (by linarith)⟩
    have hs : ∀ ω, E.rp s ω ∈ Icc (0 : ℝ) 1 := fun ω => ⟨(hmem ω).1.le, (hmem ω).2.le⟩
    have hup' : τ + η ≤ E.rp s true := by
      have h1 := (gross_sign hV true (hmem true).1 (hmem true).2 hT1 hTn).1
      have h2 := (Env.band E he true).1
      have h3 : E.F 0 ≤ E.Fm (E.gross n (VD.dirRule true T) (E.rp s true) true) := E.F_le_Fm h1
      have e : τ + η = hi := by rw [hτ, hη]; ring
      rw [e]
      exact h3.trans h2
    have hdown : E.rp s false ≤ τ - η := by
      have h1 := (gross_sign hV true (hmem false).1 (hmem false).2 hT1 hTn).2
      have h2 := (Env.band E he false).2
      have h3 : E.F (E.gross n (VD.dirRule true T) (E.rp s false) false) ≤ E.Fm 0 := E.F_le_Fm h1
      have e : τ - η = lo := by rw [hτ, hη]; ring
      rw [e]
      exact h2.trans h3
    exact sep_payoff hV true hη0 hτ0.le hn (q := E.rp s) hs hup' hdown
  exact hmain.trans (E.worst_mem_T n T true false (by omega))

/-- **Proposition `prop_worst_equilibrium`.**  The constant `\underline F_0` is
`Fworst π H ℓ (F(0)(1 - F(0)))`, which depends only on `π, H, L, F(0)`. -/
theorem prop_worst_equilibrium (hV : VD.Assumptions E) (hN : E.Noise) :
    -- Statement 1
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, E.PiW n = E.PiSQ) ∧
    -- Statement 2
    (HasDerivAt E.F 0 0 → Tendsto E.PiW atTop (𝓝 E.PiSQ)) ∧
    -- Statement 3, first claim
    (∀ t > 0, HasDerivAt E.F t 0 → limsup E.PiW atTop < E.PiFB) ∧
    -- Statement 3, second claim
    (0 < Fworst (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) ∧
      ∀ (U : Set ℝ) (t : ℝ), IsOpen U → (0 : ℝ) ∈ U → ContDiffOn ℝ 1 E.F U → deriv E.F 0 = t → 0 < t →
        Fworst (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) < t →
        E.PiSQ < liminf E.PiWT atTop) ∧
    -- Statement 4
    (∀ α > 0, Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α) → Tendsto E.PiWT atTop (𝓝 E.PiFB)) := by
  have hs0 := VD.F_zero_pos hN
  have hs1 := VD.F_zero_lt_one hN
  have hSpos : 0 < E.F 0 * (1 - E.F 0) := mul_pos hs0 (by linarith)
  have hpar := VD.par hV hSpos
  obtain ⟨hF0, _, hiff⟩ := Fworst_spec hpar
  refine ⟨fun δ hδ h => E.worst_statement1 hN hδ h, fun h => E.worst_statement2 hN (VD.PiSQ_lt_PiFB hV) h,
    fun t _ h => E.worst_statement3 hN (VD.PiSQ_lt_PiFB hV) h, ⟨hF0, ?_⟩,
    fun α hα h => worst_statement4 hV hN hα h⟩
  intro U t hU h0 hF hder _ hlt
  have hJ := (hiff t).2 hlt
  have hle := le_liminf_PiWT hV hN (VD.Smooth.of_contDiffOn hU h0 hF hder)
  rw [max_eq_right hJ.le] at hle
  linarith

end OA

end NoisyVD
