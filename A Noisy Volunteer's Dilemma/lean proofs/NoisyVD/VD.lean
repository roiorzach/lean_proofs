import NoisyVD.ThresholdAsymp
import NoisyVD.Existence

/-!
# The Volunteer's Dilemma as a special case of the model (Section 4 of the paper)

Here `Ω = A = Bool`, with `true` standing for `1`.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

namespace VD

variable (E : Env Bool Bool)

/-- `H = u^p(1,1) - u^p(0,1)`. -/
noncomputable def H : ℝ := E.u true true - E.u false true

/-- `L = u^p(1,0) - u^p(0,0)`. -/
noncomputable def L : ℝ := E.u true false - E.u false false

/-- `π = Pr(ω = 1)`. -/
noncomputable def pr : ℝ := (E.prior : Measure Bool).real {true}

/-- The gain from investigating in state `ω`. -/
noncomputable def G (ω : Bool) : ℝ := E.u true ω - E.u false ω

/-- The maintained assumptions of Section 4: `H > 0`, `L < 0`, `π > 0` and `E_ω u^p(1,ω) < E_ω u^p(0,ω)`.
(`π > 0` is the non-triviality assumption `Π^FB > Π^SQ`, see `PiFB_sub_PiSQ`.) -/
structure Assumptions : Prop where
  H_pos : 0 < H E
  L_neg : L E < 0
  pr_pos : 0 < pr E
  prior : ∫ ω, E.u true ω ∂(E.prior : Measure Bool) < ∫ ω, E.u false ω ∂(E.prior : Measure Bool)

lemma real_false : (E.prior : Measure Bool).real {false} = 1 - pr E := by
  have h : ({true} : Set Bool) ∪ {false} = univ := by
    ext b; cases b <;> simp
  have hd : Disjoint ({true} : Set Bool) {false} := by simp
  have := measureReal_union (μ := (E.prior : Measure Bool)) hd (measurableSet_singleton false)
  rw [h] at this
  simp only [probReal_univ] at this
  unfold pr
  linarith

/-- Integration against the prior. -/
lemma integral_bool (f : Bool → ℝ) :
    ∫ ω, f ω ∂(E.prior : Measure Bool) = pr E * f true + (1 - pr E) * f false := by
  rw [integral_fintype (f := f) Integrable.of_finite, Fintype.sum_bool, real_false]
  simp only [smul_eq_mul, pr]

lemma pr_nonneg : 0 ≤ pr E := measureReal_nonneg

lemma pr_le_one : pr E ≤ 1 := measureReal_le_one

variable {E}

lemma prior_ineq (h : Assumptions E) : pr E * H E + (1 - pr E) * L E < 0 := by
  have := h.prior
  rw [integral_bool, integral_bool] at this
  unfold H L
  linarith

lemma pr_lt_one (h : Assumptions E) : pr E < 1 := by
  by_contra hcon
  have h1 : pr E = 1 := le_antisymm (pr_le_one E) (not_lt.1 hcon)
  have h2 := prior_ineq h
  rw [h1] at h2
  have := h.H_pos
  linarith

/-- The Volunteer's Dilemma parameters satisfy the restrictions of `Par`. -/
lemma par (h : Assumptions E) {S : ℝ} (hS : 0 < S) : Par (pr E) (H E) (-L E) S where
  pr0 := h.pr_pos
  pr1 := pr_lt_one h
  H0 := h.H_pos
  l0 := by linarith [h.L_neg]
  S0 := hS
  prior := by
    have := prior_ineq h
    linarith

lemma PiSQ_eq (h : Assumptions E) : E.PiSQ = ∫ ω, E.u false ω ∂(E.prior : Measure Bool) := by
  obtain ⟨a, ha⟩ := E.exists_statusQuo
  cases a with
  | false => exact ha.symm
  | true =>
    have h1 := E.integral_u_le_PiSQ false
    have h2 := h.prior
    rw [← ha] at h1
    linarith

lemma PiSQ_eq' (h : Assumptions E) :
    E.PiSQ = pr E * E.u false true + (1 - pr E) * E.u false false := by
  rw [PiSQ_eq h, integral_bool]

lemma PiFB_eq (h : Assumptions E) :
    E.PiFB = pr E * E.u true true + (1 - pr E) * E.u false false := by
  have hm1 : E.maxU true = E.u true true := by
    obtain ⟨a, ha⟩ := E.exists_maxU true
    rw [← ha]
    cases a with
    | true => rfl
    | false =>
      have h1 := E.u_le_maxU true true
      have h2 := h.H_pos
      unfold H at h2
      rw [← ha] at h1
      linarith
  have hm0 : E.maxU false = E.u false false := by
    obtain ⟨a, ha⟩ := E.exists_maxU false
    rw [← ha]
    cases a with
    | false => rfl
    | true =>
      have h1 := E.u_le_maxU false false
      have h2 := h.L_neg
      unfold L at h2
      rw [← ha] at h1
      linarith
  unfold Env.PiFB
  rw [integral_bool, hm1, hm0]

/-- `Π^FB - Π^SQ = π H`, so the maintained non-triviality assumption amounts to `π > 0`. -/
lemma PiFB_sub_PiSQ (h : Assumptions E) : E.PiFB - E.PiSQ = pr E * H E := by
  rw [PiFB_eq h, PiSQ_eq' h]
  unfold H
  ring

lemma PiSQ_lt_PiFB (h : Assumptions E) : E.PiSQ < E.PiFB := by
  have := PiFB_sub_PiSQ h
  have h1 := mul_pos h.pr_pos h.H_pos
  linarith

/-! ### Threshold rules -/

lemma v_threshold (T : ℕ) (a₁ a₀ : Bool) (k : ℕ) (ω : Bool) :
    E.v (thresholdRule T a₁ a₀) k ω = E.u (if T ≤ k then a₁ else a₀) ω := by
  refine E.v_dirac ?_ ω
  unfold thresholdRule
  split_ifs <;> rfl

/-- The gross benefit under a threshold rule is the pivot probability times the payoff gain. -/
lemma gross_threshold (n T : ℕ) (a₁ a₀ : Bool) (p : ℝ) (ω : Bool) :
    E.gross n (thresholdRule T a₁ a₀) p ω = rho (n - 1) p T * (E.u a₁ ω - E.u a₀ ω) := by
  unfold Env.gross marginal
  have hv : ∀ k, E.v (thresholdRule T a₁ a₀) (k + 1) ω - E.v (thresholdRule T a₁ a₀) k ω
      = if k + 1 = T then E.u a₁ ω - E.u a₀ ω else 0 := by
    intro k
    rw [v_threshold, v_threshold]
    by_cases h1 : T ≤ k
    · have h2 : T ≤ k + 1 := by omega
      have h3 : k + 1 ≠ T := by omega
      simp [h1, h2, h3]
    · by_cases h2 : T ≤ k + 1
      · have h3 : k + 1 = T := by omega
        simp [h1, h3]
      · have h3 : k + 1 ≠ T := by omega
        simp [h1, h2, h3]
  simp_rw [hv]
  unfold rho
  by_cases hT : T = 0
  · subst hT
    simp
  · rw [ite_eq_right hT]
    obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
    simp only [Nat.add_right_cancel_iff, Nat.add_sub_cancel, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.range (n - 1 + 1)) t]
    by_cases ht : t ∈ Finset.range (n - 1 + 1)
    · rw [ite_eq_left ht]
    · rw [ite_eq_right ht]
      have : n - 1 < t := by
        rw [Finset.mem_range] at ht
        omega
      rw [bpmf_eq_zero_of_gt this]
      simp

/-- The smoothed payoff under a threshold rule. -/
lemma bexp_threshold (n T : ℕ) (a₁ a₀ : Bool) (p : ℝ) (ω : Bool) :
    bexp n p (fun k => E.v (thresholdRule T a₁ a₀) k ω)
      = E.u a₀ ω + btail n p T * (E.u a₁ ω - E.u a₀ ω) := by
  unfold bexp btail
  have key : ∀ k ∈ Finset.range (n + 1), bpmf n p k * E.v (thresholdRule T a₁ a₀) k ω
      = bpmf n p k * E.u a₀ ω + (if T ≤ k then bpmf n p k else 0) * (E.u a₁ ω - E.u a₀ ω) := by
    intro k _
    rw [v_threshold]
    by_cases h : T ≤ k
    · simp only [h, ite_true]; ring
    · simp only [h, ite_false]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, bpmf_sum, one_mul,
    ← Finset.sum_mul]

/-- `Idir up x` is the investigation probability when `x = Pr(count ≥ T)`. -/
def Idir (up : Bool) (x : ℝ) : ℝ := if up then x else 1 - x

/-- The sign of the rule. -/
def sgn (up : Bool) : ℝ := if up then 1 else -1

lemma sgn_sq (up : Bool) : sgn up * sgn up = 1 := by cases up <;> simp [sgn]

/-- The rule "investigate iff at least `T` reports" (`up = true`) or "iff fewer than `T`". -/
noncomputable def dirRule (up : Bool) (T : ℕ) : Rule Bool :=
  if up then thresholdRule T true false else thresholdRule T false true

lemma gross_dir (up : Bool) (n T : ℕ) (p : ℝ) (ω : Bool) :
    E.gross n (dirRule up T) p ω = sgn up * G E ω * rho (n - 1) p T := by
  cases up <;> simp [dirRule, sgn, gross_threshold, G] <;> ring

/-- `payoff = Π^SQ + π H Pr(a=1|ω=1) + (1-π) L Pr(a=1|ω=0)`. -/
lemma payoff_dir (h : Assumptions E) (up : Bool) (n T : ℕ) (s : Strat Bool) :
    E.payoff n (dirRule up T) s = E.PiSQ + pr E * H E * Idir up (btail n (E.rp s true) T)
      + (1 - pr E) * L E * Idir up (btail n (E.rp s false) T) := by
  unfold Env.payoff
  rw [integral_bool, PiSQ_eq' h]
  cases up
  · simp only [dirRule, Idir, Bool.false_eq_true, ite_false, bexp_threshold, H, L]
    ring
  · simp only [dirRule, Idir, ite_true, bexp_threshold, H, L]
    ring

/-- `|Idir up (tail) - Φ(-w)|` with `w = sgn up · z`. -/
lemma abs_Idir_sub (up : Bool) (x z : ℝ) :
    |Idir up x - Phi (-(sgn up * z))| = |x - (1 - Phi z)| := by
  cases up
  · simp only [Idir, sgn, Bool.false_eq_true, ite_false]
    rw [show -(-1 * z) = z by ring, abs_sub_comm x]
    congr 1
    ring
  · simp only [Idir, sgn, ite_true]
    rw [show -(1 * z) = -z by ring, Phi_neg]

/-! ### Regularity of `F` near zero -/

/-- The regularity of `F` used in Lemma `lemma_threshold_value`.  It is implied by continuous
differentiability on an open neighbourhood of zero (`Smooth.of_contDiffOn`). -/
structure Smooth (E : Env Bool Bool) (t : ℝ) : Prop where
  hasDeriv : HasDerivAt E.F t 0
  cont : ∃ ε₀ > 0, ∀ x, |x| < ε₀ → ContinuousAt E.F x

lemma Smooth.of_contDiffOn {U : Set ℝ} (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U)
    (hF : ContDiffOn ℝ 1 E.F U) {t : ℝ} (ht : deriv E.F 0 = t) : Smooth E t := by
  refine ⟨?_, ?_⟩
  · have hd : DifferentiableAt ℝ E.F 0 :=
      (hF.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds h0)
    rw [← ht]
    exact hd.hasDerivAt
  · obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
    refine ⟨ε₀, hε₀, fun x hx => ?_⟩
    have hxU : x ∈ U := hball (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
    exact (hF.continuousOn.continuousAt (hU.mem_nhds hxU))

/-- A point of continuity of `F` carries no atom. -/
lemma Fm_eq_F_of_continuousAt {c : ℝ} (h : ContinuousAt E.F c) : E.Fm c = E.F c := by
  refine le_antisymm (Env.Fm_le_F E c) ?_
  by_contra hcon
  push Not at hcon
  have hev : ∀ᶠ x in 𝓝 c, E.Fm c < E.F x := h.eventually (lt_mem_nhds hcon)
  have hlt : ∀ᶠ x in 𝓝[<] c, x < c := eventually_mem_nhdsWithin
  obtain ⟨x, hx1, hx2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and hlt).exists
  have := Env.F_le_Fm E hx2
  linarith

/-- Near zero an equilibrium reporting probability equals `F` at the gross benefit. -/
lemma rp_eq_F {n : ℕ} {d : Rule Bool} {s : Strat Bool} (he : E.IsEq n d s) {ω : Bool}
    (hc : ContinuousAt E.F (E.gross n d (E.rp s ω) ω)) :
    E.rp s ω = E.F (E.gross n d (E.rp s ω) ω) := by
  obtain ⟨h1, h2⟩ := Env.band E he ω
  rw [Fm_eq_F_of_continuousAt hc] at h1
  exact le_antisymm h2 h1

lemma F_zero_mem (_hN : E.Noise) : E.epsStar ≤ E.F 0 ∧ E.F 0 ≤ 1 - E.epsStar := by
  have hB := E.B_nonneg
  have h1 : E.epsStar ≤ (E.cost : Measure ℝ).real (Iio (-E.B)) := min_le_left _ _
  have h2 : E.epsStar ≤ (E.cost : Measure ℝ).real (Ioi E.B) := min_le_right _ _
  constructor
  · refine h1.trans ?_
    exact measureReal_mono (fun x hx => le_of_lt (lt_of_lt_of_le (mem_Iio.1 hx) (by linarith)))
  · have h3 := Env.F_add_Ioi E 0
    have h4 : (E.cost : Measure ℝ).real (Ioi E.B) ≤ (E.cost : Measure ℝ).real (Ioi 0) :=
      measureReal_mono (fun x hx => lt_of_le_of_lt hB (mem_Ioi.1 hx))
    linarith

lemma F_zero_pos (hN : E.Noise) : 0 < E.F 0 :=
  lt_of_lt_of_le (Env.lemma_noise E hN).1 (F_zero_mem hN).1

lemma F_zero_lt_one (hN : E.Noise) : E.F 0 < 1 := by
  have := (F_zero_mem hN).2
  have h2 := (Env.lemma_noise E hN).1
  linarith

end VD

end NoisyVD
