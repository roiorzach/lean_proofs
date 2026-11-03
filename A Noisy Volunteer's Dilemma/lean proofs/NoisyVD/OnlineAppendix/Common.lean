import NoisyVD.GeneralUpper
import NoisyVD.VD

/-!
# Tools shared by the extensions in the Online Appendix

* `constStrat`: every state-contingent reporting probability is induced by some strategy.  This lets
  the payoff bounds of the main-text library apply to models whose equilibrium behaviour is not that
  of the main model.
* `band_of_br`: a best-responding cutoff rule has reporting probability between `F(c⁻)` and `F(c)`.
* `sep_payoff`: separated reporting probabilities plus Chebyshev give nearly the first-best payoff.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

namespace OA

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-! ### Reporting probabilities as strategies -/

/-- The strategy under which every type reports with probability `q ω` in state `ω`. -/
noncomputable def constStrat {Ω : Type*} [MeasurableSpace Ω] (q : Ω → ℝ) (hq : Measurable q)
    (h01 : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) : Strat Ω where
  σ := fun ω _ => q ω
  meas := hq.comp measurable_fst
  mem := fun ω _ => h01 ω

lemma rp_constStrat (E : Env A Ω) {q : Ω → ℝ} (hq : Measurable q)
    (h01 : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) (ω : Ω) : E.rp (constStrat q hq h01) ω = q ω := by
  simp [Env.rp, constStrat]

/-- The decision-maker's payoff when the report count in state `ω` is `Bin(n, q ω)`. -/
noncomputable def payoffOf (E : Env A Ω) (n : ℕ) (d : Rule A) (q : Ω → ℝ) : ℝ :=
  ∫ ω, bexp n (q ω) (fun k => E.v d k ω) ∂(E.prior : Measure Ω)

lemma payoff_eq_payoffOf (E : Env A Ω) (n : ℕ) (d : Rule A) (s : Strat Ω) :
    E.payoff n d s = payoffOf E n d (E.rp s) := rfl

lemma payoffOf_eq_payoff (E : Env A Ω) (n : ℕ) (d : Rule A) {q : Ω → ℝ} (hq : Measurable q)
    (h01 : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) : payoffOf E n d q = E.payoff n d (constStrat q hq h01) := by
  rw [payoff_eq_payoffOf]
  congr 1
  funext ω
  exact (rp_constStrat E hq h01 ω).symm

lemma payoffOf_le_PiFB (E : Env A Ω) (n : ℕ) (d : Rule A) {q : Ω → ℝ} (hq : Measurable q)
    (h01 : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) : payoffOf E n d q ≤ E.PiFB := by
  rw [payoffOf_eq_payoff E n d hq h01]
  exact Env.payoff_le_PiFB E n d _

/-- The master bound of the library for arbitrary reporting probabilities. -/
theorem payoffOf_le_tv (E : Env A Ω) (n : ℕ) (d : Rule A) {q : Ω → ℝ} (hq : Measurable q) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hab : ∀ ω, q ω ∈ Icc a b) :
    payoffOf E n d q ≤ (1 - tv n a b) * E.PiSQ + tv n a b * E.PiFB := by
  have h01 : ∀ ω, q ω ∈ Icc (0 : ℝ) 1 := fun ω =>
    ⟨ha.le.trans (hab ω).1, ((hab ω).2).trans hb.le⟩
  rw [payoffOf_eq_payoff E n d hq h01]
  refine Env.payoff_le_tv E n d _ ha hb fun ω => ?_
  rw [rp_constStrat E hq h01]
  exact hab ω

/-- The master bound when the band holds only for almost every state. -/
theorem payoffOf_le_tv_ae (E : Env A Ω) (n : ℕ) (d : Rule A) {q : Ω → ℝ} (hq : Measurable q)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hae : ∀ᵐ ω ∂(E.prior : Measure Ω), q ω ∈ Icc a b) :
    payoffOf E n d q ≤ (1 - tv n a b) * E.PiSQ + tv n a b * E.PiFB := by
  let q' : Ω → ℝ := fun ω => max a (min b (q ω))
  have hq' : Measurable q' := measurable_const.max (measurable_const.min hq)
  have hmem : ∀ ω, q' ω ∈ Icc a b := fun ω =>
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have heq : payoffOf E n d q = payoffOf E n d q' := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    have : q' ω = q ω := by
      simp only [q']
      rw [min_eq_right hω.2, max_eq_right hω.1]
    show bexp n (q ω) _ = bexp n (q' ω) _
    rw [this]
  rw [heq]
  exact payoffOf_le_tv E n d hq' ha hb hmem

/-! ### Reporting probabilities of cutoff rules -/

/-- A rule that is `1` below the cutoff `c` and `0` above it, for almost every type, has mean between
`F(c⁻)` and `F(c)`. -/
lemma band_of_br {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ} (hf : Measurable f)
    (h01 : ∀ x, f x ∈ Icc (0 : ℝ) 1) {c : ℝ}
    (h : ∀ᵐ x ∂μ, (x < c → f x = 1) ∧ (c < x → f x = 0)) :
    μ.real (Iio c) ≤ ∫ x, f x ∂μ ∧ ∫ x, f x ∂μ ≤ μ.real (Iic c) := by
  have hint : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(h01 x).1, (h01 x).2])
  constructor
  · have h1 : μ.real (Iio c) = ∫ x, (Iio c).indicator (fun _ => (1 : ℝ)) x ∂μ := by
      rw [integral_indicator_const _ measurableSet_Iio]
      simp
    rw [h1]
    refine integral_mono_ae ((integrable_const (1 : ℝ)).indicator measurableSet_Iio) hint ?_
    filter_upwards [h] with x hx
    by_cases hxc : x < c
    · simp only [indicator_of_mem (mem_Iio.2 hxc)]
      rw [hx.1 hxc]
    · rw [indicator_of_notMem (by simpa using hxc)]
      exact (h01 x).1
  · have h1 : μ.real (Iic c) = ∫ x, (Iic c).indicator (fun _ => (1 : ℝ)) x ∂μ := by
      rw [integral_indicator_const _ measurableSet_Iic]
      simp
    rw [h1]
    refine integral_mono_ae hint ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) ?_
    filter_upwards [h] with x hx
    by_cases hxc : x ≤ c
    · simp only [indicator_of_mem (mem_Iic.2 hxc)]
      exact (h01 x).2
    · rw [indicator_of_notMem (by simpa using hxc)]
      exact (hx.2 (not_le.1 hxc)).le

/-! ### Chebyshev for threshold rules -/

/-- Chebyshev around the threshold `⌈nτ⌉`, with the rate `1/(nη²)`. -/
lemma tails_of_sep {n : ℕ} {τ η hi lo : ℝ} (hη : 0 < η) (hτ : 0 ≤ τ) (hn : 2 / η ≤ n)
    (hhi0 : 0 ≤ hi) (hhi1 : hi ≤ 1) (hlo0 : 0 ≤ lo) (hlo1 : lo ≤ 1)
    (hhi : τ + η ≤ hi) (hlo : lo ≤ τ - η) :
    1 - btail n hi ⌈(n : ℝ) * τ⌉₊ ≤ 1 / (n * η ^ 2) ∧ btail n lo ⌈(n : ℝ) * τ⌉₊ ≤ 1 / (n * η ^ 2) := by
  have hn2 : 2 ≤ (n : ℝ) * η := by rwa [div_le_iff₀ hη] at hn
  have hnpos : (0 : ℝ) < n := by
    by_contra hcon
    have : (n : ℝ) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg n)
    rw [this] at hn2
    linarith
  have hnτ : 0 ≤ (n : ℝ) * τ := by positivity
  have hc1 : (⌈(n : ℝ) * τ⌉₊ : ℝ) < (n : ℝ) * τ + 1 := Nat.ceil_lt_add_one hnτ
  have hc0 : (n : ℝ) * τ ≤ (⌈(n : ℝ) * τ⌉₊ : ℝ) := Nat.le_ceil _
  set a := (n : ℝ) * η / 2 with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hrate : (n : ℝ) / (4 * a ^ 2) = 1 / (n * η ^ 2) := by
    rw [ha]
    field_simp
    ring
  constructor
  · rw [← hrate]
    refine one_sub_btail_le hhi0 hhi1 ha0 ?_
    have : (n : ℝ) * (τ + η) ≤ n * hi := mul_le_mul_of_nonneg_left hhi hnpos.le
    have e : (n : ℝ) * η = 2 * a := by rw [ha]; ring
    nlinarith
  · rw [← hrate]
    refine btail_le_of_gap hlo0 hlo1 ha0 ?_
    have : (n : ℝ) * lo ≤ n * (τ - η) := mul_le_mul_of_nonneg_left hlo hnpos.le
    have e : (n : ℝ) * η = 2 * a := by rw [ha]; ring
    nlinarith

/-! ### Separated reporting probabilities in the binary Volunteer's Dilemma -/

variable {E : Env Bool Bool}

lemma measurable_bool (q : Bool → ℝ) : Measurable q := measurable_from_top

/-- `payoff_dir` for arbitrary reporting probabilities. -/
lemma payoffOf_dir (hV : VD.Assumptions E) (up : Bool) (n T : ℕ) {q : Bool → ℝ}
    (hq : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) :
    payoffOf E n (VD.dirRule up T) q = E.PiSQ + VD.pr E * VD.H E * VD.Idir up (btail n (q true) T)
      + (1 - VD.pr E) * VD.L E * VD.Idir up (btail n (q false) T) := by
  rw [payoffOf_eq_payoff E n _ (measurable_bool q) hq, VD.payoff_dir hV]
  simp only [rp_constStrat E (measurable_bool q) hq]

/-- If reporting is high in state `up` and low in the other state, then the rule `dirRule up ⌈nτ⌉`
yields nearly the first-best payoff. -/
theorem sep_payoff (hV : VD.Assumptions E) (up : Bool) {n : ℕ} {τ η : ℝ} (hη : 0 < η) (hτ : 0 ≤ τ)
    (hn : 2 / η ≤ n) {q : Bool → ℝ} (hq : ∀ ω, q ω ∈ Icc (0 : ℝ) 1) (hhi : τ + η ≤ q up)
    (hlo : q (!up) ≤ τ - η) :
    E.PiFB - (VD.pr E * VD.H E - (1 - VD.pr E) * VD.L E) * (1 / (n * η ^ 2))
      ≤ payoffOf E n (VD.dirRule up ⌈(n : ℝ) * τ⌉₊) q := by
  obtain ⟨h1, h2⟩ := tails_of_sep hη hτ hn (hq up).1 (hq up).2 (hq (!up)).1 (hq (!up)).2 hhi hlo
  rw [payoffOf_dir hV up n _ hq]
  have hFS := VD.PiFB_sub_PiSQ hV
  have hb1 : 0 < VD.pr E * VD.H E := mul_pos hV.pr_pos hV.H_pos
  have hb0 : 0 < (1 - VD.pr E) * (-VD.L E) :=
    mul_pos (by linarith [VD.pr_lt_one hV]) (by linarith [hV.L_neg])
  set e := 1 / ((n : ℝ) * η ^ 2) with he
  cases up with
  | true =>
    simp only [VD.Idir, ite_true, Bool.not_true] at *
    nlinarith
  | false =>
    simp only [VD.Idir, Bool.false_eq_true, ite_false, Bool.not_false] at *
    nlinarith

/-- The pivotal probability is positive for interior reporting probabilities. -/
lemma rho_pos {n T : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hT1 : 1 ≤ T) (hTn : T ≤ n) :
    0 < rho (n - 1) p T := by
  unfold rho
  rw [ite_eq_right (by omega)]
  unfold bpmf
  have hk : T - 1 ≤ n - 1 := by omega
  have : 0 < ((n - 1).choose (T - 1) : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have h1 : 0 < 1 - p := by linarith
  positivity

/-- Under a threshold rule, reporting is strictly attractive in state `up` and strictly unattractive
in the other state. -/
lemma gross_sign (hV : VD.Assumptions E) (up : Bool) {n T : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hT1 : 1 ≤ T) (hTn : T ≤ n) :
    0 < E.gross n (VD.dirRule up T) p up ∧ E.gross n (VD.dirRule up T) p (!up) < 0 := by
  have hρ := rho_pos hp0 hp1 hT1 hTn
  have hH := hV.H_pos
  have hL := hV.L_neg
  rw [VD.gross_dir, VD.gross_dir]
  cases up with
  | true =>
    have h1 : VD.G E true = VD.H E := rfl
    have h0 : VD.G E false = VD.L E := rfl
    simp only [VD.sgn, ite_true, Bool.not_true, h1, h0, one_mul]
    exact ⟨mul_pos hH hρ, mul_neg_of_neg_of_pos hL hρ⟩
  | false =>
    have h1 : VD.G E true = VD.H E := rfl
    have h0 : VD.G E false = VD.L E := rfl
    simp only [VD.sgn, Bool.false_eq_true, ite_false, Bool.not_false, h1, h0]
    constructor
    · nlinarith
    · nlinarith

/-- The threshold `⌈nτ⌉` is in `{1, …, n}`. -/
lemma ceil_mem {n : ℕ} {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hn : 1 ≤ n) :
    1 ≤ ⌈(n : ℝ) * τ⌉₊ ∧ ⌈(n : ℝ) * τ⌉₊ ≤ n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact Nat.one_le_ceil_iff.2 (mul_pos hnr hτ0)
  · apply Nat.ceil_le.2
    nlinarith

/-- The squeeze for a limit equal to the first-best payoff. -/
lemma tendsto_of_rate {f : ℕ → ℝ} {FB C : ℝ} (hle : ∀ n, f n ≤ FB)
    (hlow : ∀ᶠ n : ℕ in atTop, FB - C * (1 / (n : ℝ)) ≤ f n) : Tendsto f atTop (𝓝 FB) := by
  have h1 : Tendsto (fun n : ℕ => FB - C * (1 / (n : ℝ))) atTop (𝓝 FB) := by
    have h2 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have := (h2.const_mul C).const_sub FB
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds hlow
    (Eventually.of_forall hle)

end OA

end NoisyVD
