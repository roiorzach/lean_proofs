import NoisyVD.Overlap
import NoisyVD.LocalBinomial

/-!
# The model (Section 3 of the paper)

* `Env A Ω`: primitives `u^p`, the prior on `Ω` and the distribution of `ν_i`.
* `Rule A`: symmetric decision rules `d : {0,…,n} → Δ(A)` (only values at `k ≤ n` matter).
* `Strat Ω`: a symmetric strategy, the probability that type `ν_i = x` reports in state `ω`.
* `Env.IsEq`: symmetric Bayesian Nash equilibrium.
* `Env.Pi`, `Env.PiT`, `Env.PiSQ`, `Env.PiFB`: the payoff objects `Π(n)`, `Π^T(n)`, `Π^SQ`, `Π^FB`.

Individuals observe `ω`, so given the rule and the opponents' reporting probability `p` a type `x`'s
gain from reporting is `gross - x`, where `gross` is the expected change in `u^p`.  The file
`NoisyVD/Game.lean` proves this reduction from the underlying profile-level expected utilities.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

/-- The primitives of the model. -/
structure Env (A Ω : Type*) [TopologicalSpace A] [TopologicalSpace Ω] [MeasurableSpace Ω] where
  /-- The common payoff `u^p(a, ω)`. -/
  u : A → Ω → ℝ
  u_cont : Continuous (Function.uncurry u)
  /-- The common prior on `Ω`. -/
  prior : ProbabilityMeasure Ω
  /-- The distribution of the reporting cost `ν_i`. -/
  cost : ProbabilityMeasure ℝ

/-- A symmetric decision rule. -/
abbrev Rule (A : Type*) [MeasurableSpace A] := ℕ → ProbabilityMeasure A

/-- A symmetric (behavioural) reporting strategy, measurable in `(ω, x)`. -/
structure Strat (Ω : Type*) [MeasurableSpace Ω] where
  σ : Ω → ℝ → ℝ
  meas : Measurable (Function.uncurry σ)
  mem : ∀ ω x, σ ω x ∈ Icc (0 : ℝ) 1

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

namespace Env

/-- `F(x) = Pr(ν_i ≤ x)`. -/
noncomputable def F (E : Env A Ω) (x : ℝ) : ℝ := (E.cost : Measure ℝ).real (Iic x)

/-- `F(x⁻) = Pr(ν_i < x)`. -/
noncomputable def Fm (E : Env A Ω) (x : ℝ) : ℝ := (E.cost : Measure ℝ).real (Iio x)

/-- `max_{a,ω} u^p(a,ω)`. -/
noncomputable def uMax (E : Env A Ω) : ℝ := sSup (range (Function.uncurry E.u))

/-- `min_{a,ω} u^p(a,ω)`. -/
noncomputable def uMin (E : Env A Ω) : ℝ := sInf (range (Function.uncurry E.u))

/-- The range `B` of `u^p`. -/
noncomputable def B (E : Env A Ω) : ℝ := E.uMax - E.uMin

/-- **Assumption 1** (`assumption_noise`). -/
def Noise (E : Env A Ω) : Prop :=
  0 < (E.cost : Measure ℝ).real (Iio (-E.B)) ∧ 0 < (E.cost : Measure ℝ).real (Ioi E.B)

/-- `ε_* = min {Pr(ν_i < -B), Pr(ν_i > B)}`. -/
noncomputable def epsStar (E : Env A Ω) : ℝ :=
  min ((E.cost : Measure ℝ).real (Iio (-E.B))) ((E.cost : Measure ℝ).real (Ioi E.B))

/-- `v_k(ω) = ∫ u^p(a, ω) d(k)(da)`. -/
noncomputable def v (E : Env A Ω) (d : Rule A) (k : ℕ) (ω : Ω) : ℝ :=
  ∫ a, E.u a ω ∂(d k : Measure A)

/-- The gross expected benefit `Δ` of reporting when the `n-1` others report with probability `p`. -/
noncomputable def gross (E : Env A Ω) (n : ℕ) (d : Rule A) (p : ℝ) (ω : Ω) : ℝ :=
  marginal (n - 1) p fun k => E.v d k ω

/-- The state-contingent reporting probability induced by a strategy. -/
noncomputable def rp (E : Env A Ω) (s : Strat Ω) (ω : Ω) : ℝ :=
  ∫ x, s.σ ω x ∂(E.cost : Measure ℝ)

/-- Symmetric Bayesian Nash equilibrium: every type in every state best responds. -/
def IsEq (E : Env A Ω) (n : ℕ) (d : Rule A) (s : Strat Ω) : Prop :=
  ∀ ω x, (x < E.gross n d (E.rp s ω) ω → s.σ ω x = 1) ∧ (E.gross n d (E.rp s ω) ω < x → s.σ ω x = 0)

/-- The decision-maker's expected payoff. -/
noncomputable def payoff (E : Env A Ω) (n : ℕ) (d : Rule A) (s : Strat Ω) : ℝ :=
  ∫ ω, bexp n (E.rp s ω) (fun k => E.v d k ω) ∂(E.prior : Measure Ω)

/-- `max_a u^p(a, ω)`. -/
noncomputable def maxU (E : Env A Ω) (ω : Ω) : ℝ := sSup (range fun a => E.u a ω)

/-- The first-best payoff `Π^FB = E_ω max_a u^p(a,ω)`. -/
noncomputable def PiFB (E : Env A Ω) : ℝ := ∫ ω, E.maxU ω ∂(E.prior : Measure Ω)

/-- The status quo payoff `Π^SQ = max_a E_ω u^p(a,ω)`. -/
noncomputable def PiSQ (E : Env A Ω) : ℝ :=
  sSup (range fun a => ∫ ω, E.u a ω ∂(E.prior : Measure Ω))

/-- The set of attainable payoffs over symmetric rules and symmetric equilibria. -/
def payoffs (E : Env A Ω) (n : ℕ) : Set ℝ :=
  {y | ∃ (d : Rule A) (s : Strat Ω), E.IsEq n d s ∧ y = E.payoff n d s}

/-- `Π(n)`. -/
noncomputable def Pi (E : Env A Ω) (n : ℕ) : ℝ := sSup (E.payoffs n)

end Env

/-- The Dirac rule at an action. -/
noncomputable def diracPM (a : A) : ProbabilityMeasure A :=
  ⟨Measure.dirac a, Measure.dirac.isProbabilityMeasure⟩

/-- `d_T`: choose `a₁` if at least `T` reports are made and `a₀` otherwise. -/
noncomputable def thresholdRule (T : ℕ) (a₁ a₀ : A) : Rule A :=
  fun k => if T ≤ k then diracPM a₁ else diracPM a₀

namespace Env

/-- Payoffs attainable with threshold rules, `T ∈ {0,…,n+1}`. -/
def payoffsT (E : Env A Ω) (n : ℕ) : Set ℝ :=
  {y | ∃ (T : ℕ) (a₁ a₀ : A) (s : Strat Ω), T ≤ n + 1 ∧ E.IsEq n (thresholdRule T a₁ a₀) s ∧
    y = E.payoff n (thresholdRule T a₁ a₀) s}

/-- `Π^T(n)`. -/
noncomputable def PiT (E : Env A Ω) (n : ℕ) : ℝ := sSup (E.payoffsT n)

variable (E : Env A Ω)

/-! ### Elementary properties of the primitives -/

lemma isCompact_range_u : IsCompact (range (Function.uncurry E.u)) :=
  isCompact_range E.u_cont

lemma u_le_uMax (a : A) (ω : Ω) : E.u a ω ≤ E.uMax :=
  le_csSup E.isCompact_range_u.bddAbove ⟨(a, ω), rfl⟩

lemma uMin_le_u (a : A) (ω : Ω) : E.uMin ≤ E.u a ω :=
  csInf_le E.isCompact_range_u.bddBelow ⟨(a, ω), rfl⟩

lemma nonempty_state (E : Env A Ω) : Nonempty Ω :=
  nonempty_of_isProbabilityMeasure (E.prior : Measure Ω)

lemma B_nonneg : 0 ≤ E.B := by
  have := E.nonempty_state
  obtain ⟨a⟩ := ‹Nonempty A›
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := E.u_le_uMax a ω
  have := E.uMin_le_u a ω
  unfold B
  linarith

lemma continuous_u_left (ω : Ω) : Continuous fun a => E.u a ω :=
  E.u_cont.comp (continuous_id.prodMk continuous_const)

lemma continuous_u_right (a : A) : Continuous fun ω => E.u a ω :=
  E.u_cont.comp (continuous_const.prodMk continuous_id)

/-- Bounded measurable functions are integrable against any probability measure. -/
lemma integrable_of_bdd {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (h : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact h x)

lemma abs_u_le (a : A) (ω : Ω) : |E.u a ω| ≤ max |E.uMax| |E.uMin| := by
  rw [abs_le]
  have h1 := E.u_le_uMax a ω
  have h2 := E.uMin_le_u a ω
  constructor
  · have := le_max_right |E.uMax| |E.uMin|
    have := neg_abs_le E.uMin
    linarith
  · have := le_max_left |E.uMax| |E.uMin|
    have := le_abs_self E.uMax
    linarith

lemma integrable_u_left (m : ProbabilityMeasure A) (ω : Ω) :
    Integrable (fun a => E.u a ω) (m : Measure A) :=
  integrable_of_bdd _ (E.continuous_u_left ω).measurable fun a => E.abs_u_le a ω

lemma integrable_u_right (a : A) :
    Integrable (fun ω => E.u a ω) (E.prior : Measure Ω) :=
  integrable_of_bdd _ (E.continuous_u_right a).measurable fun ω => E.abs_u_le a ω

/-! ### The functions `v_k` -/

lemma v_le_of (d : Rule A) (k : ℕ) (ω : Ω) {c : ℝ} (h : ∀ a, E.u a ω ≤ c) : E.v d k ω ≤ c := by
  calc E.v d k ω = ∫ a, E.u a ω ∂(d k : Measure A) := rfl
    _ ≤ ∫ _, c ∂(d k : Measure A) :=
        integral_mono (E.integrable_u_left (d k) ω) (integrable_const c) h
    _ = c := by simp

lemma le_v_of (d : Rule A) (k : ℕ) (ω : Ω) {c : ℝ} (h : ∀ a, c ≤ E.u a ω) : c ≤ E.v d k ω := by
  calc c = ∫ _, c ∂(d k : Measure A) := by simp
    _ ≤ ∫ a, E.u a ω ∂(d k : Measure A) :=
        integral_mono (integrable_const c) (E.integrable_u_left (d k) ω) h

lemma v_le_uMax (d : Rule A) (k : ℕ) (ω : Ω) : E.v d k ω ≤ E.uMax :=
  E.v_le_of d k ω fun a => E.u_le_uMax a ω

lemma uMin_le_v (d : Rule A) (k : ℕ) (ω : Ω) : E.uMin ≤ E.v d k ω :=
  E.le_v_of d k ω fun a => E.uMin_le_u a ω

lemma v_mem (d : Rule A) (ω : Ω) (k : ℕ) :
    E.uMin ≤ E.v d k ω ∧ E.v d k ω ≤ E.uMin + E.B := by
  refine ⟨E.uMin_le_v d k ω, ?_⟩
  have := E.v_le_uMax d k ω
  unfold B
  linarith

lemma continuous_v (d : Rule A) (k : ℕ) : Continuous (E.v d k) := by
  have h : Continuous (Function.uncurry fun (ω : Ω) (a : A) => E.u a ω) :=
    E.u_cont.comp continuous_swap
  have := continuous_parametric_integral_of_continuous (μ := (d k : Measure A)) h
    (isCompact_univ (X := A))
  show Continuous fun ω => ∫ a, E.u a ω ∂(d k : Measure A)
  simpa using this

lemma continuous_gross (n : ℕ) (d : Rule A) :
    Continuous fun z : Ω × ℝ => E.gross n d z.2 z.1 := by
  unfold gross marginal
  refine continuous_finsetSum _ fun k _ => ?_
  have h1 : Continuous fun z : Ω × ℝ => bpmf (n - 1) z.2 k :=
    (continuous_bpmf _ _).comp continuous_snd
  have h2 := (E.continuous_v d (k + 1)).comp (continuous_fst (X := Ω) (Y := ℝ))
  have h3 := (E.continuous_v d k).comp (continuous_fst (X := Ω) (Y := ℝ))
  exact h1.mul (h2.sub h3)

/-- `|Δ| ≤ B`: the bound used in Lemma `lemma_noise`. -/
lemma abs_gross_le (n : ℕ) (d : Rule A) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (ω : Ω) :
    |E.gross n d p ω| ≤ E.B :=
  abs_marginal_le_range h0 h1 (E.v_mem d ω)

/-! ### Reporting probabilities -/

variable {E}

lemma Strat.measurable_slice (s : Strat Ω) (ω : Ω) : Measurable (s.σ ω) :=
  s.meas.comp (measurable_const.prodMk measurable_id)

lemma integrable_sigma (E : Env A Ω) (s : Strat Ω) (ω : Ω) :
    Integrable (s.σ ω) (E.cost : Measure ℝ) :=
  integrable_of_bdd _ (Strat.measurable_slice s ω) (C := 1) fun x => by
    rw [abs_le]; constructor <;> linarith [(s.mem ω x).1, (s.mem ω x).2]

lemma rp_nonneg (E : Env A Ω) (s : Strat Ω) (ω : Ω) : 0 ≤ E.rp s ω :=
  integral_nonneg fun x => (s.mem ω x).1

lemma rp_le_one (E : Env A Ω) (s : Strat Ω) (ω : Ω) : E.rp s ω ≤ 1 := by
  have h := integral_mono (μ := (E.cost : Measure ℝ)) (integrable_sigma E s ω)
    (integrable_const (1 : ℝ)) (fun x => (s.mem ω x).2)
  simpa [rp] using h

lemma measurable_rp (E : Env A Ω) (s : Strat Ω) : Measurable (E.rp s) := by
  have h : StronglyMeasurable (Function.uncurry s.σ) := s.meas.stronglyMeasurable
  have := h.integral_prod_right (ν := (E.cost : Measure ℝ))
  exact this.measurable

/-! ### The band for reporting probabilities -/

lemma F_mono (E : Env A Ω) : Monotone E.F := fun _ _ h =>
  measureReal_mono (Iic_subset_Iic.2 h)

lemma Fm_mono (E : Env A Ω) : Monotone E.Fm := fun _ _ h =>
  measureReal_mono (Iio_subset_Iio h)

lemma Fm_le_F (E : Env A Ω) (x : ℝ) : E.Fm x ≤ E.F x :=
  measureReal_mono Iio_subset_Iic_self

lemma F_le_Fm (E : Env A Ω) {x y : ℝ} (h : x < y) : E.F x ≤ E.Fm y :=
  measureReal_mono (Iic_subset_Iio.2 h)

lemma F_le_one (E : Env A Ω) (x : ℝ) : E.F x ≤ 1 := measureReal_le_one

lemma F_nonneg (E : Env A Ω) (x : ℝ) : 0 ≤ E.F x := measureReal_nonneg

lemma Fm_nonneg (E : Env A Ω) (x : ℝ) : 0 ≤ E.Fm x := measureReal_nonneg

/-- In any equilibrium `F(Δ⁻) ≤ p_ω ≤ F(Δ)`. -/
lemma band (E : Env A Ω) {n : ℕ} {d : Rule A} {s : Strat Ω} (he : E.IsEq n d s) (ω : Ω) :
    E.Fm (E.gross n d (E.rp s ω) ω) ≤ E.rp s ω ∧ E.rp s ω ≤ E.F (E.gross n d (E.rp s ω) ω) := by
  set c := E.gross n d (E.rp s ω) ω with hc
  constructor
  · have h1 : E.Fm c = ∫ x, (Iio c).indicator (fun _ => (1 : ℝ)) x ∂(E.cost : Measure ℝ) := by
      rw [integral_indicator_const _ measurableSet_Iio]
      simp [Fm]
    rw [h1]
    refine integral_mono ?_ (integrable_sigma E s ω) fun x => ?_
    · exact (integrable_const (1 : ℝ)).indicator measurableSet_Iio
    · by_cases hx : x < c
      · rw [indicator_of_mem (mem_Iio.2 hx), ((he ω x).1 hx)]
      · rw [indicator_of_notMem (by simpa using hx)]
        exact (s.mem ω x).1
  · have h1 : E.F c = ∫ x, (Iic c).indicator (fun _ => (1 : ℝ)) x ∂(E.cost : Measure ℝ) := by
      rw [integral_indicator_const _ measurableSet_Iic]
      simp [F]
    rw [h1]
    refine integral_mono (integrable_sigma E s ω) ?_ fun x => ?_
    · exact (integrable_const (1 : ℝ)).indicator measurableSet_Iic
    · by_cases hx : x ≤ c
      · rw [indicator_of_mem (mem_Iic.2 hx)]
        exact (s.mem ω x).2
      · rw [indicator_of_notMem (by simpa using hx), ((he ω x).2 (not_le.1 hx))]

lemma epsStar_le_half (E : Env A Ω) : E.epsStar ≤ 1 / 2 := by
  have hB := E.B_nonneg
  have hdisj : Disjoint (Iio (-E.B)) (Ioi E.B) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : x < -E.B := hx
    have h2 : E.B < x := hx'
    linarith
  have h := measureReal_union (μ := (E.cost : Measure ℝ)) hdisj measurableSet_Ioi
  have h2 : (E.cost : Measure ℝ).real (Iio (-E.B) ∪ Ioi E.B) ≤ 1 := measureReal_le_one
  unfold epsStar
  have h3 := min_le_left ((E.cost : Measure ℝ).real (Iio (-E.B))) ((E.cost : Measure ℝ).real (Ioi E.B))
  have h4 := min_le_right ((E.cost : Measure ℝ).real (Iio (-E.B))) ((E.cost : Measure ℝ).real (Ioi E.B))
  linarith

lemma F_add_Ioi (E : Env A Ω) (x : ℝ) : E.F x + (E.cost : Measure ℝ).real (Ioi x) = 1 := by
  have hdisj : Disjoint (Iic x) (Ioi x) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact absurd (mem_Ioi.1 hy') (not_lt.2 (mem_Iic.1 hy))
  have h := measureReal_union (μ := (E.cost : Measure ℝ)) hdisj measurableSet_Ioi
  rw [Iic_union_Ioi] at h
  simp only [probReal_univ] at h
  unfold F
  linarith

/-- **Lemma 1** (`lemma_noise`). -/
theorem lemma_noise (E : Env A Ω) (hE : E.Noise) :
    0 < E.epsStar ∧ ∀ (n : ℕ) (d : Rule A) (s : Strat Ω), E.IsEq n d s → ∀ ω,
      E.rp s ω ∈ Icc E.epsStar (1 - E.epsStar) := by
  refine ⟨lt_min hE.1 hE.2, fun n d s he ω => ?_⟩
  obtain ⟨h1, h2⟩ := band E he ω
  have hΔ := E.abs_gross_le n d (rp_nonneg E s ω) (rp_le_one E s ω) ω
  have hΔ' := abs_le.1 hΔ
  constructor
  · refine le_trans (min_le_left _ _) (le_trans ?_ h1)
    exact E.Fm_mono hΔ'.1
  · have h3 : E.F (E.gross n d (E.rp s ω) ω) ≤ E.F E.B := E.F_mono hΔ'.2
    have h4 := E.F_add_Ioi E.B
    have h5 : E.epsStar ≤ (E.cost : Measure ℝ).real (Ioi E.B) := min_le_right _ _
    linarith

/-! ### Lemma 2 -/

/-- The constant `M = √2 B C` in Lemma `lemma_pivotal`, which depends only on `B` and `ε_*`. -/
noncomputable def pivConst (B ε : ℝ) : ℝ := √2 * B * massConst ε

lemma pivConst_pos {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) : 0 < pivConst B ε := by
  unfold pivConst
  have := massConst_pos hε hε'
  positivity

/-- The bound `|Δ| ≤ M/√n` in the proof of Lemma `lemma_pivotal`, for any lower bound `l` on the
probabilities of reporting and of not reporting. -/
theorem abs_gross_le_of_mem (E : Env A Ω) {n : ℕ} (hn : 2 ≤ n) (d : Rule A) {l p : ℝ}
    (hl : 0 < l) (hl' : l ≤ 1 / 2) (hp : p ∈ Icc l (1 - l)) (ω : Ω) :
    |E.gross n d p ω| ≤ pivConst E.B l / √(n : ℝ) := by
  have hB := E.B_nonneg
  have hp0 : 0 < p := lt_of_lt_of_le hl hp.1
  have hp1 : p < 1 := lt_of_le_of_lt hp.2 (by linarith)
  have hm : 1 ≤ n - 1 := by omega
  have h1 := abs_marginal_le_mode (m := n - 1) hp0 hp1 (E.v_mem d ω)
  have h2 := bpmf_le_massConst hm hl hl' hp (bmode (n - 1) p)
  have hC := massConst_pos hl hl'
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hmr : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by rw [hcast]; linarith
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsm : 0 < √((n - 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hmr
  -- `√n ≤ √2 √(n-1)`
  have hroot : √(n : ℝ) ≤ √2 * √((n - 1 : ℕ) : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    rw [hcast]
    linarith
  have h3 : massConst l / √((n - 1 : ℕ) : ℝ) ≤ √2 * massConst l / √(n : ℝ) := by
    rw [div_le_div_iff₀ hsm hsn]
    nlinarith
  calc |E.gross n d p ω| ≤ E.B * bpmf (n - 1) p (bmode (n - 1) p) := h1
    _ ≤ E.B * (massConst l / √((n - 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h2 hB
    _ ≤ E.B * (√2 * massConst l / √(n : ℝ)) := mul_le_mul_of_nonneg_left h3 hB
    _ = pivConst E.B l / √(n : ℝ) := by unfold pivConst; ring

/-- The bound `|Δ| ≤ M/√n`, with the `ε_*` of Lemma `lemma_noise`. -/
theorem abs_gross_le_pivot (E : Env A Ω) (hE : E.Noise) {n : ℕ} (hn : 2 ≤ n) (d : Rule A)
    {p : ℝ} (hp : p ∈ Icc E.epsStar (1 - E.epsStar)) (ω : Ω) :
    |E.gross n d p ω| ≤ pivConst E.B E.epsStar / √(n : ℝ) :=
  abs_gross_le_of_mem E hn d (lemma_noise E hE).1 (epsStar_le_half E) hp ω

/-- **Lemma 2** (`lemma_pivotal`). -/
theorem lemma_pivotal (E : Env A Ω) (hE : E.Noise) {n : ℕ} (hn : 2 ≤ n) {d : Rule A} {s : Strat Ω}
    (he : E.IsEq n d s) (ω : Ω) (x : ℝ) :
    (pivConst E.B E.epsStar / √(n : ℝ) < x → s.σ ω x = 0) ∧
    (x < -(pivConst E.B E.epsStar / √(n : ℝ)) → s.σ ω x = 1) := by
  have h := abs_gross_le_pivot E hE hn d ((lemma_noise E hE).2 n d s he ω) ω
  have h' := abs_le.1 h
  constructor
  · intro hx
    exact (he ω x).2 (lt_of_le_of_lt h'.2 hx)
  · intro hx
    exact (he ω x).1 (lt_of_lt_of_le hx h'.1)

/-- The equation `eq_general_reporting_band` of the paper. -/
theorem reporting_band (E : Env A Ω) (hE : E.Noise) {n : ℕ} (hn : 2 ≤ n) {d : Rule A} {s : Strat Ω}
    (he : E.IsEq n d s) (ω : Ω) :
    E.Fm (-(pivConst E.B E.epsStar / √(n : ℝ))) ≤ E.rp s ω ∧
      E.rp s ω ≤ E.F (pivConst E.B E.epsStar / √(n : ℝ)) := by
  have h := abs_gross_le_pivot E hE hn d ((lemma_noise E hE).2 n d s he ω) ω
  have h' := abs_le.1 h
  obtain ⟨h1, h2⟩ := band E he ω
  exact ⟨(E.Fm_mono h'.1).trans h1, h2.trans (E.F_mono h'.2)⟩

/-! ### Payoff comparisons -/

lemma continuous_integral_u (E : Env A Ω) :
    Continuous fun a => ∫ ω, E.u a ω ∂(E.prior : Measure Ω) := by
  have := continuous_parametric_integral_of_continuous (μ := (E.prior : Measure Ω)) E.u_cont
    (isCompact_univ (X := Ω))
  simpa using this

lemma integral_u_le_PiSQ (E : Env A Ω) (a : A) :
    ∫ ω, E.u a ω ∂(E.prior : Measure Ω) ≤ E.PiSQ :=
  le_csSup (isCompact_range E.continuous_integral_u).bddAbove ⟨a, rfl⟩

/-- A status quo action exists. -/
lemma exists_statusQuo (E : Env A Ω) : ∃ a, ∫ ω, E.u a ω ∂(E.prior : Measure Ω) = E.PiSQ := by
  obtain ⟨a, ha⟩ := (isCompact_range E.continuous_integral_u).exists_isGreatest (range_nonempty _)
    |>.imp fun _ h => h
  obtain ⟨a', rfl⟩ := ha.1
  exact ⟨a', (ha.csSup_eq).symm⟩

/-- Fubini: any fixed action distribution yields at most `Π^SQ`. -/
lemma integral_v_le_PiSQ (E : Env A Ω) (d : Rule A) (k : ℕ) :
    ∫ ω, E.v d k ω ∂(E.prior : Measure Ω) ≤ E.PiSQ := by
  have hswap : ∫ ω, E.v d k ω ∂(E.prior : Measure Ω)
      = ∫ a, (∫ ω, E.u a ω ∂(E.prior : Measure Ω)) ∂(d k : Measure A) := by
    unfold v
    refine integral_integral_swap (f := fun ω a => E.u a ω) ?_
    have hc : Continuous (Function.uncurry fun (ω : Ω) (a : A) => E.u a ω) :=
      E.u_cont.comp continuous_swap
    exact integrable_of_bdd _ hc.measurable (C := max |E.uMax| |E.uMin|) fun z => E.abs_u_le z.2 z.1
  rw [hswap]
  have hbd : ∀ a, |∫ ω, E.u a ω ∂(E.prior : Measure Ω)| ≤ max |E.uMax| |E.uMin| := by
    intro a
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |E.u a ω| ∂(E.prior : Measure Ω)
        ≤ ∫ _, max |E.uMax| |E.uMin| ∂(E.prior : Measure Ω) :=
          integral_mono (E.integrable_u_right a).abs (integrable_const _) (fun ω => E.abs_u_le a ω)
      _ = _ := by simp
  calc ∫ a, (∫ ω, E.u a ω ∂(E.prior : Measure Ω)) ∂(d k : Measure A)
      ≤ ∫ _, E.PiSQ ∂(d k : Measure A) :=
        integral_mono (integrable_of_bdd _ E.continuous_integral_u.measurable hbd)
          (integrable_const E.PiSQ) (fun a => E.integral_u_le_PiSQ a)
    _ = E.PiSQ := by simp

lemma continuous_maxU (E : Env A Ω) : Continuous E.maxU := by
  have h : Continuous (Function.uncurry fun (ω : Ω) (a : A) => E.u a ω) :=
    E.u_cont.comp continuous_swap
  have := IsCompact.continuous_sSup (f := fun (ω : Ω) (a : A) => E.u a ω)
    (isCompact_univ (X := A)) h
  show Continuous fun ω => sSup (range fun a => E.u a ω)
  simpa [image_univ] using this

lemma u_le_maxU (E : Env A Ω) (a : A) (ω : Ω) : E.u a ω ≤ E.maxU ω :=
  le_csSup (isCompact_range (E.continuous_u_left ω)).bddAbove ⟨a, rfl⟩

lemma exists_maxU (E : Env A Ω) (ω : Ω) : ∃ a, E.u a ω = E.maxU ω := by
  obtain ⟨y, hy⟩ := (isCompact_range (E.continuous_u_left ω)).exists_isGreatest (range_nonempty _)
    |>.imp fun _ h => h
  obtain ⟨a, rfl⟩ := hy.1
  exact ⟨a, hy.csSup_eq.symm⟩

lemma abs_maxU_le (E : Env A Ω) (ω : Ω) : |E.maxU ω| ≤ max |E.uMax| |E.uMin| := by
  obtain ⟨a, ha⟩ := E.exists_maxU ω
  rw [← ha]; exact E.abs_u_le a ω

lemma integrable_maxU (E : Env A Ω) : Integrable E.maxU (E.prior : Measure Ω) :=
  integrable_of_bdd _ E.continuous_maxU.measurable (E.abs_maxU_le)

lemma v_le_maxU (E : Env A Ω) (d : Rule A) (k : ℕ) (ω : Ω) : E.v d k ω ≤ E.maxU ω :=
  E.v_le_of d k ω fun a => E.u_le_maxU a ω

lemma PiSQ_le_PiFB (E : Env A Ω) : E.PiSQ ≤ E.PiFB := by
  obtain ⟨a, ha⟩ := E.exists_statusQuo
  rw [← ha]
  exact integral_mono (E.integrable_u_right a) E.integrable_maxU (fun ω => E.u_le_maxU a ω)

/-- The maintained assumption `Π^FB > Π^SQ` gives `B > 0`, hence `M > 0` in Lemma `lemma_pivotal`. -/
lemma B_pos_of_lt (E : Env A Ω) (hFB : E.PiSQ < E.PiFB) : 0 < E.B := by
  have h1 : E.PiFB ≤ E.uMax := by
    calc E.PiFB ≤ ∫ _, E.uMax ∂(E.prior : Measure Ω) :=
          integral_mono E.integrable_maxU (integrable_const _) fun ω => by
            obtain ⟨a, ha⟩ := E.exists_maxU ω
            rw [← ha]
            exact E.u_le_uMax a ω
      _ = E.uMax := by simp
  have h2 : E.uMin ≤ E.PiSQ := by
    obtain ⟨a, ha⟩ := E.exists_statusQuo
    rw [← ha]
    calc E.uMin = ∫ _, E.uMin ∂(E.prior : Measure Ω) := by simp
      _ ≤ _ := integral_mono (integrable_const _) (E.integrable_u_right a) fun ω => E.uMin_le_u a ω
  unfold B
  linarith

lemma abs_v_le (E : Env A Ω) (d : Rule A) (k : ℕ) (ω : Ω) : |E.v d k ω| ≤ max |E.uMax| |E.uMin| := by
  rw [abs_le]
  have h1 := E.v_le_uMax d k ω
  have h2 := E.uMin_le_v d k ω
  constructor
  · have := le_max_right |E.uMax| |E.uMin|
    have := neg_abs_le E.uMin
    linarith
  · have := le_max_left |E.uMax| |E.uMin|
    have := le_abs_self E.uMax
    linarith

lemma integrable_v (E : Env A Ω) (d : Rule A) (k : ℕ) :
    Integrable (E.v d k) (E.prior : Measure Ω) :=
  integrable_of_bdd _ (E.continuous_v d k).measurable (E.abs_v_le d k)

lemma measurable_bexp_rp (E : Env A Ω) (n : ℕ) (d : Rule A) {q : Ω → ℝ} (hq : Measurable q) :
    Measurable fun ω => bexp n (q ω) (fun k => E.v d k ω) := by
  unfold bexp
  refine Finset.measurable_sum _ fun k _ => ?_
  exact ((continuous_bpmf n k).measurable.comp hq).mul (E.continuous_v d k).measurable

lemma abs_bexp_le (E : Env A Ω) (n : ℕ) (d : Rule A) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (ω : Ω) :
    |bexp n p (fun k => E.v d k ω)| ≤ max |E.uMax| |E.uMin| := by
  unfold bexp
  calc |∑ k ∈ Finset.range (n + 1), bpmf n p k * E.v d k ω|
      ≤ ∑ k ∈ Finset.range (n + 1), |bpmf n p k * E.v d k ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), bpmf n p k * max |E.uMax| |E.uMin| := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (bpmf_nonneg h0 h1)]
        exact mul_le_mul_of_nonneg_left (E.abs_v_le d k ω) (bpmf_nonneg h0 h1)
    _ = _ := by rw [← Finset.sum_mul, bpmf_sum, one_mul]

lemma integrable_bexp (E : Env A Ω) (n : ℕ) (d : Rule A) (s : Strat Ω) :
    Integrable (fun ω => bexp n (E.rp s ω) (fun k => E.v d k ω)) (E.prior : Measure Ω) :=
  integrable_of_bdd _ (E.measurable_bexp_rp n d (measurable_rp E s))
    (fun ω => E.abs_bexp_le n d (rp_nonneg E s ω) (rp_le_one E s ω) ω)

/-- Any report count distribution yields at most the first-best payoff. -/
lemma payoff_le_PiFB (E : Env A Ω) (n : ℕ) (d : Rule A) (s : Strat Ω) : E.payoff n d s ≤ E.PiFB := by
  refine integral_mono (E.integrable_bexp n d s) E.integrable_maxU fun ω => ?_
  have h0 := rp_nonneg E s ω
  have h1 := rp_le_one E s ω
  show bexp n (E.rp s ω) (fun k => E.v d k ω) ≤ E.maxU ω
  unfold bexp
  calc ∑ k ∈ Finset.range (n + 1), bpmf n (E.rp s ω) k * E.v d k ω
      ≤ ∑ k ∈ Finset.range (n + 1), bpmf n (E.rp s ω) k * E.maxU ω :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (E.v_le_maxU d k ω) (bpmf_nonneg h0 h1)
    _ = E.maxU ω := by rw [← Finset.sum_mul, bpmf_sum, one_mul]

/-- **Master bound.**  If the report count distribution dominates, in every state, a state-independent
sub-probability `w` of mass `β`, then the payoff is at most `β Π^SQ + (1-β) Π^FB`.  This is the
decomposition `P_{n,ω} = β R_n + (1-β) Q_{n,ω}` in the proof of Proposition `prop_general_failures`. -/
theorem payoff_le_mix (E : Env A Ω) (n : ℕ) (d : Rule A) (s : Strat Ω) {w : ℕ → ℝ}
    (hw0 : ∀ k, 0 ≤ w k) (hw : ∀ ω, ∀ k, w k ≤ bpmf n (E.rp s ω) k) :
    E.payoff n d s ≤ (∑ k ∈ Finset.range (n + 1), w k) * E.PiSQ
      + (1 - ∑ k ∈ Finset.range (n + 1), w k) * E.PiFB := by
  set β := ∑ k ∈ Finset.range (n + 1), w k with hβ
  have hpt : ∀ ω, bexp n (E.rp s ω) (fun k => E.v d k ω)
      ≤ ∑ k ∈ Finset.range (n + 1), w k * E.v d k ω + (1 - β) * E.maxU ω := by
    intro ω
    unfold bexp
    have h1 : ∑ k ∈ Finset.range (n + 1), (bpmf n (E.rp s ω) k - w k) = 1 - β := by
      rw [Finset.sum_sub_distrib, bpmf_sum]
    rw [← h1, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have h2 := mul_le_mul_of_nonneg_left (E.v_le_maxU d k ω)
      (show 0 ≤ bpmf n (E.rp s ω) k - w k by linarith [hw ω k])
    nlinarith
  have hint : Integrable (fun ω => ∑ k ∈ Finset.range (n + 1), w k * E.v d k ω)
      (E.prior : Measure Ω) :=
    integrable_finsetSum _ fun k _ => (E.integrable_v d k).const_mul _
  have hint2 : Integrable (fun ω => (1 - β) * E.maxU ω) (E.prior : Measure Ω) :=
    E.integrable_maxU.const_mul _
  calc E.payoff n d s
      ≤ ∫ ω, (∑ k ∈ Finset.range (n + 1), w k * E.v d k ω + (1 - β) * E.maxU ω)
          ∂(E.prior : Measure Ω) :=
        integral_mono (E.integrable_bexp n d s) (hint.add hint2) hpt
    _ = ∑ k ∈ Finset.range (n + 1), w k * ∫ ω, E.v d k ω ∂(E.prior : Measure Ω)
          + (1 - β) * E.PiFB := by
        rw [integral_add hint hint2, integral_finsetSum _ fun k _ => (E.integrable_v d k).const_mul _,
          integral_const_mul]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul]
    _ ≤ ∑ k ∈ Finset.range (n + 1), w k * E.PiSQ + (1 - β) * E.PiFB := by
        have : ∑ k ∈ Finset.range (n + 1), w k * ∫ ω, E.v d k ω ∂(E.prior : Measure Ω)
            ≤ ∑ k ∈ Finset.range (n + 1), w k * E.PiSQ :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (E.integral_v_le_PiSQ d k) (hw0 k)
        linarith
    _ = _ := by rw [← Finset.sum_mul]

/-- The master bound with the `min` weights: if every reporting probability lies in `[a, b]`, the
payoff is at most `(1-TV) Π^SQ + TV Π^FB`. -/
theorem payoff_le_tv (E : Env A Ω) (n : ℕ) (d : Rule A) (s : Strat Ω) {a b : ℝ} (ha : 0 < a)
    (hb : b < 1) (hab : ∀ ω, E.rp s ω ∈ Icc a b) :
    E.payoff n d s ≤ (1 - tv n a b) * E.PiSQ + tv n a b * E.PiFB := by
  have := E.nonempty_state
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hab' : a ≤ b := (hab ω₀).1.trans (hab ω₀).2
  have ha1 : a ≤ 1 := by linarith
  have hb0 : 0 ≤ b := by linarith
  have h := payoff_le_mix E n d s (w := fun k => min (bpmf n a k) (bpmf n b k))
    (fun k => le_min (bpmf_nonneg ha.le ha1) (bpmf_nonneg hb0 hb.le))
    (fun ω k => bpmf_ge_min ha hb (hab ω).1 (hab ω).2)
  rw [sum_min_eq] at h
  simpa using h

/-! ### Constant rules -/

/-- The constant rule. -/
noncomputable def constRule (a : A) : Rule A := fun _ => diracPM a

lemma v_dirac (E : Env A Ω) {d : Rule A} {k : ℕ} {a : A} (h : d k = diracPM a) (ω : Ω) :
    E.v d k ω = E.u a ω := by
  unfold v
  rw [h]
  show ∫ x, E.u x ω ∂(Measure.dirac a) = E.u a ω
  exact integral_dirac _ _

/-- The strategy under which exactly the types with `x < 0` report. -/
noncomputable def negStrat : Strat Ω where
  σ := fun _ x => if x < 0 then 1 else 0
  meas := by
    have h : Measurable fun z : Ω × ℝ => if z.2 < 0 then (1 : ℝ) else 0 :=
      Measurable.ite (measurableSet_lt measurable_snd measurable_const) measurable_const
        measurable_const
    exact h
  mem := fun _ x => by
    by_cases hx : x < 0 <;> simp [hx]

/-- If the marginal benefit vanishes, `negStrat` is an equilibrium. -/
lemma isEq_negStrat (E : Env A Ω) {n : ℕ} {d : Rule A}
    (h : ∀ p ω, E.gross n d p ω = 0) : E.IsEq n d (negStrat (Ω := Ω)) := by
  intro ω x
  rw [h]
  constructor
  · intro hx
    simp [negStrat, hx]
  · intro hx
    simp [negStrat, not_lt.2 hx.le]

lemma gross_const (E : Env A Ω) {n : ℕ} {d : Rule A} {a : A} (h : ∀ k, d k = diracPM a)
    (p : ℝ) (ω : Ω) : E.gross n d p ω = 0 := by
  unfold gross marginal
  refine Finset.sum_eq_zero fun k _ => ?_
  show bpmf (n - 1) p k * (E.v d (k + 1) ω - E.v d k ω) = 0
  rw [E.v_dirac (h k) ω, E.v_dirac (h (k + 1)) ω]
  ring

lemma payoff_const (E : Env A Ω) {n : ℕ} {d : Rule A} {a : A} (h : ∀ k, d k = diracPM a)
    (s : Strat Ω) : E.payoff n d s = ∫ ω, E.u a ω ∂(E.prior : Measure Ω) := by
  unfold payoff
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show bexp n (E.rp s ω) (fun k => E.v d k ω) = E.u a ω
  unfold bexp
  have : ∀ k ∈ Finset.range (n + 1), bpmf n (E.rp s ω) k * E.v d k ω
      = bpmf n (E.rp s ω) k * E.u a ω := fun k _ => by rw [E.v_dirac (h k) ω]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, bpmf_sum, one_mul]

/-- `Π^SQ` is attained by a constant rule. -/
lemma PiSQ_mem_payoffs (E : Env A Ω) (n : ℕ) : E.PiSQ ∈ E.payoffs n := by
  obtain ⟨a, ha⟩ := E.exists_statusQuo
  have hk : ∀ k, constRule a k = diracPM a := fun _ => rfl
  exact ⟨constRule a, negStrat, isEq_negStrat E (gross_const E hk), by
    rw [payoff_const E hk, ha]⟩

lemma thresholdRule_self (T : ℕ) (a : A) (k : ℕ) : thresholdRule T a a k = diracPM a := by
  unfold thresholdRule
  split_ifs <;> rfl

/-- `Π^SQ` is attained by a constant threshold rule. -/
lemma PiSQ_mem_payoffsT (E : Env A Ω) (n : ℕ) : E.PiSQ ∈ E.payoffsT n := by
  obtain ⟨a, ha⟩ := E.exists_statusQuo
  have hk := thresholdRule_self 0 a
  exact ⟨0, a, a, negStrat, Nat.zero_le _, isEq_negStrat E (gross_const E hk), by
    rw [payoff_const E hk, ha]⟩

lemma bddAbove_payoffs (E : Env A Ω) (n : ℕ) : BddAbove (E.payoffs n) :=
  ⟨E.PiFB, by rintro y ⟨d, s, _, rfl⟩; exact payoff_le_PiFB E n d s⟩

lemma bddAbove_payoffsT (E : Env A Ω) (n : ℕ) : BddAbove (E.payoffsT n) :=
  ⟨E.PiFB, by rintro y ⟨T, a₁, a₀, s, _, _, rfl⟩; exact payoff_le_PiFB E n _ s⟩

lemma PiSQ_le_Pi (E : Env A Ω) (n : ℕ) : E.PiSQ ≤ E.Pi n :=
  le_csSup (bddAbove_payoffs E n) (PiSQ_mem_payoffs E n)

lemma Pi_le_PiFB (E : Env A Ω) (n : ℕ) : E.Pi n ≤ E.PiFB :=
  csSup_le ⟨_, PiSQ_mem_payoffs E n⟩ (by rintro y ⟨d, s, _, rfl⟩; exact payoff_le_PiFB E n d s)

lemma PiSQ_le_PiT (E : Env A Ω) (n : ℕ) : E.PiSQ ≤ E.PiT n :=
  le_csSup (bddAbove_payoffsT E n) (PiSQ_mem_payoffsT E n)

lemma PiT_le_PiFB (E : Env A Ω) (n : ℕ) : E.PiT n ≤ E.PiFB :=
  csSup_le ⟨_, PiSQ_mem_payoffsT E n⟩
    (by rintro y ⟨T, a₁, a₀, s, _, _, rfl⟩; exact payoff_le_PiFB E n _ s)

/-- `Π^T(n) ≤ Π(n)`. -/
lemma PiT_le_Pi (E : Env A Ω) (n : ℕ) : E.PiT n ≤ E.Pi n :=
  csSup_le ⟨_, PiSQ_mem_payoffsT E n⟩ (by
    rintro y ⟨T, a₁, a₀, s, _, he, rfl⟩
    exact le_csSup (bddAbove_payoffs E n) ⟨_, s, he, rfl⟩)

end Env

end NoisyVD
