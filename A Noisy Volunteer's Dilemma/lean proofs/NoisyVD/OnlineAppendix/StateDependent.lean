import NoisyVD.OnlineAppendix.Common
import NoisyVD.Existence

/-!
# State-dependent reporting costs (Proposition `prop_state_dependent`)

The binary Volunteer's Dilemma of Section 4, with the reporting cost drawn from `F_ω` in state `ω`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

namespace OA

/-- The primitives of the Volunteer's Dilemma with state-dependent reporting costs. -/
structure SDEnv where
  /-- The common payoff `u^p(a, ω)`. -/
  u : Bool → Bool → ℝ
  /-- The common prior. -/
  prior : ProbabilityMeasure Bool
  /-- The distribution `F_ω` of the reporting cost in state `ω`. -/
  cost : Bool → ProbabilityMeasure ℝ

namespace SDEnv

variable (E : SDEnv)

/-- The main model with cost distribution `F_ω`. -/
noncomputable def env (ω : Bool) : Env Bool Bool where
  u := E.u
  u_cont := continuous_of_discreteTopology
  prior := E.prior
  cost := E.cost ω

/-- The objects that do not depend on the cost distribution (`u`, `prior`, `B`, `Π^SQ`, `Π^FB`, the
gross benefit) are read from this environment. -/
noncomputable abbrev base : Env Bool Bool := E.env true

/-- `F_ω(x)`. -/
noncomputable def F (ω : Bool) (x : ℝ) : ℝ := (E.env ω).F x

/-- `F_ω(x⁻)`. -/
noncomputable def Fm (ω : Bool) (x : ℝ) : ℝ := (E.env ω).Fm x

/-- The state-contingent reporting probability. -/
noncomputable def rp (s : Strat Bool) (ω : Bool) : ℝ := (E.env ω).rp s ω

/-- Symmetric Bayesian Nash equilibrium: every type in every state best responds. -/
def IsEq (n : ℕ) (d : Rule Bool) (s : Strat Bool) : Prop :=
  ∀ ω x, (x < E.base.gross n d (E.rp s ω) ω → s.σ ω x = 1) ∧
    (E.base.gross n d (E.rp s ω) ω < x → s.σ ω x = 0)

/-- The decision-maker's expected payoff. -/
noncomputable def payoff (n : ℕ) (d : Rule Bool) (s : Strat Bool) : ℝ :=
  payoffOf E.base n d (E.rp s)

/-- The attainable payoffs over symmetric rules and symmetric equilibria. -/
def payoffs (n : ℕ) : Set ℝ := {y | ∃ (d : Rule Bool) (s : Strat Bool), E.IsEq n d s ∧ y = E.payoff n d s}

/-- `Π(n)`. -/
noncomputable def Pi (n : ℕ) : ℝ := sSup (E.payoffs n)

/-- The analogue of Assumption 1 for each `F_ω`. -/
def Noise : Prop := ∀ ω, (E.env ω).Noise

/-- `ε_* = min_ω ε_*(F_ω)`. -/
noncomputable def eps : ℝ := min (E.env true).epsStar (E.env false).epsStar

/-- The constant `M` of Lemma 2 at `ε_*`, where `ε_*` works for both `F_1` and `F_0`. -/
noncomputable def M : ℝ := Env.pivConst E.base.B E.eps

variable {E}

lemma env_gross (ω : Bool) (n : ℕ) (d : Rule Bool) (p : ℝ) (ω' : Bool) :
    (E.env ω).gross n d p ω' = E.base.gross n d p ω' := rfl

lemma env_B (ω : Bool) : (E.env ω).B = E.base.B := rfl

lemma rp_mem (s : Strat Bool) (ω : Bool) : E.rp s ω ∈ Icc (0 : ℝ) 1 :=
  ⟨Env.rp_nonneg _ s ω, Env.rp_le_one _ s ω⟩

/-- In any equilibrium `F_ω(Δ⁻) ≤ p_ω ≤ F_ω(Δ)`. -/
lemma band {n : ℕ} {d : Rule Bool} {s : Strat Bool} (he : E.IsEq n d s) (ω : Bool) :
    E.Fm ω (E.base.gross n d (E.rp s ω) ω) ≤ E.rp s ω ∧
      E.rp s ω ≤ E.F ω (E.base.gross n d (E.rp s ω) ω) :=
  band_of_br (μ := ((E.cost ω : ProbabilityMeasure ℝ) : Measure ℝ))
    (Env.Strat.measurable_slice s ω) (fun x => s.mem ω x)
    (Eventually.of_forall fun x => he ω x)

lemma eps_pos (hN : E.Noise) : 0 < E.eps :=
  lt_min (Env.lemma_noise _ (hN true)).1 (Env.lemma_noise _ (hN false)).1

/-- The analogue of Lemma `lemma_noise`. -/
theorem lemma_noise {n : ℕ} {d : Rule Bool} {s : Strat Bool} (he : E.IsEq n d s) (ω : Bool) :
    E.rp s ω ∈ Icc (E.env ω).epsStar (1 - (E.env ω).epsStar) := by
  obtain ⟨h1, h2⟩ := band he ω
  have hΔ := abs_le.1 ((E.env ω).abs_gross_le n d (rp_mem (E := E) s ω).1 (rp_mem (E := E) s ω).2 ω)
  have hg : E.base.gross n d (E.rp s ω) ω = (E.env ω).gross n d (E.rp s ω) ω := rfl
  rw [hg] at h1 h2
  constructor
  · refine le_trans (min_le_left _ _) (le_trans ?_ h1)
    exact (E.env ω).Fm_mono hΔ.1
  · have h3 : (E.env ω).F ((E.env ω).gross n d (E.rp s ω) ω) ≤ (E.env ω).F (E.env ω).B :=
      (E.env ω).F_mono hΔ.2
    have h4 := (E.env ω).F_add_Ioi (E.env ω).B
    have h5 : (E.env ω).epsStar ≤ ((E.env ω).cost : Measure ℝ).real (Ioi (E.env ω).B) := min_le_right _ _
    have h6 : E.F ω ((E.env ω).gross n d (E.rp s ω) ω) ≤ (E.env ω).F (E.env ω).B := h3
    linarith

lemma rp_mem_eps {n : ℕ} {d : Rule Bool} {s : Strat Bool} (he : E.IsEq n d s) (ω : Bool) :
    E.rp s ω ∈ Icc E.eps (1 - E.eps) := by
  obtain ⟨h1, h2⟩ := lemma_noise he ω
  have hle : E.eps ≤ (E.env ω).epsStar := by
    cases ω
    · exact min_le_right _ _
    · exact min_le_left _ _
  exact ⟨hle.trans h1, by linarith⟩

lemma eps_le_half : E.eps ≤ 1 / 2 :=
  (min_le_left _ _).trans (Env.epsStar_le_half _)

lemma M_pos (hN : E.Noise) (hV : VD.Assumptions E.base) : 0 < E.M :=
  Env.pivConst_pos (E.base.B_pos_of_lt (VD.PiSQ_lt_PiFB hV)) (eps_pos hN) eps_le_half

/-- `|Δ_{n,ω}| ≤ M/√n`, the analogue of Lemma `lemma_pivotal`. -/
theorem abs_gross_le (hN : E.Noise) {n : ℕ} (hn : 2 ≤ n) (d : Rule Bool) {s : Strat Bool}
    (he : E.IsEq n d s) (ω : Bool) :
    |E.base.gross n d (E.rp s ω) ω| ≤ E.M / √(n : ℝ) :=
  Env.abs_gross_le_of_mem E.base hn d (eps_pos hN) eps_le_half (rp_mem_eps he ω) ω

/-- **Equation `eq_sd_band`.** -/
theorem eq_sd_band (hN : E.Noise) {n : ℕ} (hn : 2 ≤ n) {d : Rule Bool} {s : Strat Bool}
    (he : E.IsEq n d s) (ω : Bool) :
    E.Fm ω (-(E.M / √(n : ℝ))) ≤ E.rp s ω ∧ E.rp s ω ≤ E.F ω (E.M / √(n : ℝ)) := by
  have h' := abs_le.1 (abs_gross_le hN hn d he ω)
  obtain ⟨h1, h2⟩ := band he ω
  exact ⟨((E.env ω).Fm_mono h'.1).trans h1, h2.trans ((E.env ω).F_mono h'.2)⟩

/-! ### Status quo and first best -/

/-- `Π^SQ` is attained by a constant rule. -/
lemma PiSQ_mem_payoffs (n : ℕ) : E.base.PiSQ ∈ E.payoffs n := by
  obtain ⟨a, ha⟩ := E.base.exists_statusQuo
  have hk : ∀ k, Env.constRule a k = diracPM a := fun _ => rfl
  refine ⟨Env.constRule a, Env.negStrat, ?_, ?_⟩
  · intro ω x
    rw [Env.gross_const E.base hk]
    constructor
    · intro hx
      simp [Env.negStrat, hx]
    · intro hx
      simp [Env.negStrat, not_lt.2 hx.le]
  · show E.base.PiSQ = payoffOf E.base n _ _
    rw [payoffOf_eq_payoff E.base n _ (measurable_bool _) (fun ω => rp_mem _ ω),
      Env.payoff_const E.base hk, ha]

lemma payoff_le_PiFB (n : ℕ) (d : Rule Bool) (s : Strat Bool) : E.payoff n d s ≤ E.base.PiFB :=
  payoffOf_le_PiFB E.base n d (measurable_bool _) (fun ω => rp_mem s ω)

lemma le_PiFB (n : ℕ) : ∀ y ∈ E.payoffs n, y ≤ E.base.PiFB := by
  rintro y ⟨d, s, _, rfl⟩
  exact payoff_le_PiFB n d s

lemma Pi_le_PiFB (n : ℕ) : E.Pi n ≤ E.base.PiFB :=
  csSup_le ⟨_, PiSQ_mem_payoffs n⟩ (le_PiFB n)

/-! ### Existence of equilibrium -/

/-- The fixed-point argument of Lemma `lemma_symmetric_equilibrium_exists` applied state by state. -/
theorem exists_equilibrium (E : SDEnv) (n : ℕ) (d : Rule Bool) : ∃ s : Strat Bool, E.IsEq n d s := by
  choose s hs using fun ω => (E.env ω).exists_equilibrium n d
  let σ : Bool → ℝ → ℝ := fun ω x => (s ω).σ ω x
  refine ⟨⟨σ, ?_, fun ω x => (s ω).mem ω x⟩, ?_⟩
  · exact measurable_from_prod_countable_right fun ω => Env.Strat.measurable_slice (s ω) ω
  · intro ω x
    exact hs ω ω x

/-! ### The upper bounds when `F₁(0) = F₀(0)` -/

/-- `h_n = M/√n`. -/
noncomputable def hn (E : SDEnv) (n : ℕ) : ℝ := E.M / √(n : ℝ)

/-- `p_n^- = max{min_ω F_ω((-h_n)⁻), ε_*}`. -/
noncomputable def pMinus (E : SDEnv) (n : ℕ) : ℝ :=
  max (min (E.Fm true (-(hn E n))) (E.Fm false (-(hn E n)))) E.eps

/-- `p_n^+ = min{max_ω F_ω(h_n), 1-ε_*}`. -/
noncomputable def pPlus (E : SDEnv) (n : ℕ) : ℝ :=
  min (max (E.F true (hn E n)) (E.F false (hn E n))) (1 - E.eps)

/-- By `eq_sd_band` and Lemma `lemma_noise`, `p_{n,ω} ∈ [p_n^-, p_n^+] ⊆ [ε_*, 1-ε_*]`. -/
lemma rp_mem_band (hN : E.Noise) {n : ℕ} (hn2 : 2 ≤ n) {d : Rule Bool} {s : Strat Bool}
    (he : E.IsEq n d s) (ω : Bool) : E.rp s ω ∈ Icc (pMinus E n) (pPlus E n) := by
  obtain ⟨h1, h2⟩ := eq_sd_band hN hn2 he ω
  obtain ⟨h3, h4⟩ := rp_mem_eps he ω
  refine ⟨max_le ?_ h3, le_min ?_ h4⟩
  · cases ω
    · exact (min_le_right _ _).trans h1
    · exact (min_le_left _ _).trans h1
  · cases ω
    · exact h2.trans (le_max_right _ _)
    · exact h2.trans (le_max_left _ _)

/-- The proof of Statements 1--3 of Proposition `prop_general_failures` applies: it uses only that the
reporting probabilities lie in `[p_n^-, p_n^+]`. -/
theorem bandFamily (hN : E.Noise) : BandFamily E.base E.payoffs E.eps (pMinus E) (pPlus E) where
  l_pos := eps_pos hN
  sq_mem := PiSQ_mem_payoffs
  le_fb := le_PiFB
  mem := by
    filter_upwards [eventually_ge_atTop 2] with n hn2
    obtain ⟨s, he⟩ := E.exists_equilibrium n (Env.constRule true)
    have h := rp_mem_band hN hn2 he true
    have hab := h.1.trans h.2
    have h1 : E.eps ≤ pMinus E n := le_max_right _ _
    have h2 : pPlus E n ≤ 1 - E.eps := min_le_right _ _
    exact ⟨⟨h1, hab.trans h2⟩, ⟨h1.trans hab, h2⟩, hab⟩
  bound := by
    filter_upwards [eventually_ge_atTop 2] with n hn2
    rintro y ⟨d, s, he, rfl⟩
    have hε := eps_pos hN
    have h1 : E.eps ≤ pMinus E n := le_max_right _ _
    have h2 : pPlus E n ≤ 1 - E.eps := min_le_right _ _
    exact payoffOf_le_tv E.base n d (measurable_bool _) (lt_of_lt_of_le hε h1)
      (lt_of_le_of_lt h2 (by linarith [eps_le_half (E := E)])) (rp_mem_band hN hn2 he)

/-- The gap: `max_ω F_ω(h_n) - min_ω F_ω(-2h_n)`. -/
noncomputable def gap (E : SDEnv) (n : ℕ) : ℝ :=
  max (E.F true (hn E n)) (E.F false (hn E n))
    - min (E.F true (-2 * hn E n)) (E.F false (-2 * hn E n))

lemma pPlus_sub_pMinus_le (hN : E.Noise) (hV : VD.Assumptions E.base) {n : ℕ} (hn1 : 1 ≤ n) :
    pPlus E n - pMinus E n ≤ gap E n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hh : 0 < hn E n := div_pos (M_pos hN hV) (Real.sqrt_pos.2 hnr)
  have h1 : pPlus E n ≤ max (E.F true (hn E n)) (E.F false (hn E n)) := min_le_left _ _
  have h2 : min (E.Fm true (-(hn E n))) (E.Fm false (-(hn E n))) ≤ pMinus E n := le_max_left _ _
  have h3 : min (E.F true (-2 * hn E n)) (E.F false (-2 * hn E n))
      ≤ min (E.Fm true (-(hn E n))) (E.Fm false (-(hn E n))) :=
    min_le_min ((E.env true).F_le_Fm (by linarith)) ((E.env false).F_le_Fm (by linarith))
  unfold gap
  linarith

/-- `√n (F(κ M/√n) - F(0)) → κ M F'(0)`. -/
lemma tendsto_sqrt_mul_F {F : ℝ → ℝ} {t : ℝ} (hF : HasDerivAt F t 0) (A : ℝ) :
    Tendsto (fun n : ℕ => √(n : ℝ) * (F (A / √(n : ℝ)) - F 0)) atTop (𝓝 (t * A)) := by
  refine tendsto_sqrt_mul_F_sub hF rfl tendsto_id ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
  simp only [id]
  field_simp

/-- `√n (max_ω F_ω(h_n) - min_ω F_ω(-2h_n)) → 3 M max{F₁'(0), F₀'(0)}`, using `F₁(0) = F₀(0)`. -/
lemma gap_tendsto (hN : E.Noise) (hs : E.F true 0 = E.F false 0) {t₁ t₀ : ℝ}
    (h₁ : HasDerivAt (E.F true) t₁ 0) (h₀ : HasDerivAt (E.F false) t₀ 0) :
    Tendsto (fun n : ℕ => √(n : ℝ) * gap E n) atTop (𝓝 (3 * E.M * max t₁ t₀)) := by
  have hM : 0 ≤ E.M := by
    have h1 := massConst_pos (eps_pos hN) (eps_le_half (E := E))
    have h2 := E.base.B_nonneg
    unfold M Env.pivConst
    positivity
  have hlim := ((tendsto_sqrt_mul_F h₁ E.M).max (tendsto_sqrt_mul_F h₀ E.M)).sub
    ((tendsto_sqrt_mul_F h₁ (-2 * E.M)).min (tendsto_sqrt_mul_F h₀ (-2 * E.M)))
  have hval : max (t₁ * E.M) (t₀ * E.M) - min (t₁ * (-2 * E.M)) (t₀ * (-2 * E.M))
      = 3 * E.M * max t₁ t₀ := by
    rcases le_total t₁ t₀ with h | h
    · rw [max_eq_right (mul_le_mul_of_nonneg_right h hM),
        min_eq_right (mul_le_mul_of_nonpos_right h (by linarith)), max_eq_right h]
      ring
    · rw [max_eq_left (mul_le_mul_of_nonneg_right h hM),
        min_eq_left (mul_le_mul_of_nonpos_right h (by linarith)), max_eq_left h]
      ring
  rw [hval] at hlim
  refine hlim.congr fun n => ?_
  have hr : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have e : (-2 * E.M) / √(n : ℝ) = -2 * hn E n := by
    unfold hn
    ring
  rw [e, ← hs, ← mul_max_of_nonneg _ _ hr, ← mul_min_of_nonneg _ _ hr, max_sub_sub_right,
    min_sub_sub_right]
  show _ = √(n : ℝ) * gap E n
  unfold gap hn
  ring

/-- **Statement 1.** -/
theorem statement1 (hN : E.Noise) (hs : E.F true 0 = E.F false 0) {δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ ω, E.F ω δ - E.F ω (-δ) = 0) : ∃ nStar : ℕ, ∀ n > nStar, E.Pi n = E.base.PiSQ := by
  refine (bandFamily hN).eq_of_le ?_
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (hn E) atTop (𝓝 0) := Tendsto.const_div_atTop hsq E.M
  filter_upwards [(tendsto_order.1 hlim).2 δ hδ] with n hn'
  -- each `F_ω` is constant on `[-δ, δ]`, with value `s`
  set v := E.F true 0 with hv
  have hup : ∀ ω, E.F ω (hn E n) ≤ v := fun ω => by
    have h1 : E.F ω (hn E n) ≤ E.F ω δ := (E.env ω).F_mono hn'.le
    have h2 : E.F ω (-δ) ≤ E.F ω 0 := (E.env ω).F_mono (by linarith)
    have h3 := hF ω
    have h4 : E.F ω 0 = v := by
      cases ω
      · exact hs.symm
      · rfl
    linarith
  have hlo : ∀ ω, v ≤ E.Fm ω (-(hn E n)) := fun ω => by
    have h1 : E.F ω (-δ) ≤ E.Fm ω (-(hn E n)) := (E.env ω).F_le_Fm (by linarith)
    have h2 : E.F ω 0 ≤ E.F ω δ := (E.env ω).F_mono hδ.le
    have h3 := hF ω
    have h4 : E.F ω 0 = v := by
      cases ω
      · exact hs.symm
      · rfl
    linarith
  have h1 : pPlus E n ≤ max (E.F true (hn E n)) (E.F false (hn E n)) := min_le_left _ _
  have h2 : min (E.Fm true (-(hn E n))) (E.Fm false (-(hn E n))) ≤ pMinus E n := le_max_left _ _
  have h3 : max (E.F true (hn E n)) (E.F false (hn E n)) ≤ v := max_le (hup _) (hup _)
  have h4 : v ≤ min (E.Fm true (-(hn E n))) (E.Fm false (-(hn E n))) := le_min (hlo _) (hlo _)
  linarith

/-- **Statement 2.** -/
theorem statement2 (hN : E.Noise) (hV : VD.Assumptions E.base) (hs : E.F true 0 = E.F false 0)
    (h₁ : HasDerivAt (E.F true) 0 0) (h₀ : HasDerivAt (E.F false) 0 0) :
    Tendsto E.Pi atTop (𝓝 E.base.PiSQ) := by
  refine (bandFamily hN).tendsto (g := gap E) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact pPlus_sub_pMinus_le hN hV hn
  · have := gap_tendsto hN hs h₁ h₀
    simpa using this

/-- **Statement 3.** -/
theorem statement3 (hV : VD.Assumptions E.base) (hN : E.Noise) (hs : E.F true 0 = E.F false 0)
    {t₁ t₀ : ℝ} (h₁ : HasDerivAt (E.F true) t₁ 0) (h₀ : HasDerivAt (E.F false) t₀ 0) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧ limsup E.Pi atTop ≤ β * E.base.PiSQ + (1 - β) * E.base.PiFB ∧
      β * E.base.PiSQ + (1 - β) * E.base.PiFB < E.base.PiFB := by
  refine (bandFamily hN).limsup_lt (VD.PiSQ_lt_PiFB hV) (g := gap E) (C := 3 * E.M * max t₁ t₀ + 1) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact pPlus_sub_pMinus_le hN hV hn
  · exact (tendsto_order.1 (gap_tendsto hN hs h₁ h₀)).2 _ (by linarith) |>.mono fun n hn => hn.le

/-! ### The final statement -/

/-- **Final statement** of Proposition `prop_state_dependent`. -/
theorem statement_final (hV : VD.Assumptions E.base) (hN : E.Noise)
    (hs : E.F true 0 ≠ E.F false 0) : Tendsto E.Pi atTop (𝓝 E.base.PiFB) := by
  -- `up` is the state with the larger value of `F_ω(0)`
  obtain ⟨up, hup⟩ : ∃ up : Bool, E.F (!up) 0 < E.F up 0 := by
    rcases lt_or_gt_of_ne hs with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  set hi := E.F up 0 with hhi
  set lo := E.F (!up) 0 with hlo
  set τ := (hi + lo) / 2 with hτ
  set η := (hi - lo) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hlo0 : 0 ≤ lo := (E.env (!up)).F_nonneg 0
  have hhi1 : hi ≤ 1 := (E.env up).F_le_one 0
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  have hτ1 : τ ≤ 1 := by rw [hτ]; linarith
  have hC : 0 ≤ (VD.pr E.base * VD.H E.base - (1 - VD.pr E.base) * VD.L E.base) := by
    have h1 := mul_pos hV.pr_pos hV.H_pos
    have h2 := mul_pos (show 0 < 1 - VD.pr E.base by linarith [VD.pr_lt_one hV])
      (show 0 < -VD.L E.base by linarith [hV.L_neg])
    nlinarith
  refine tendsto_of_rate Pi_le_PiFB
    (C := (VD.pr E.base * VD.H E.base - (1 - VD.pr E.base) * VD.L E.base) * (1 / η ^ 2)) ?_
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 / η ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hlarge, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨hT1, hTn⟩ := ceil_mem (n := n) hτ0 hτ1 hn1
  set T := ⌈(n : ℝ) * τ⌉₊ with hT
  obtain ⟨s, he⟩ := E.exists_equilibrium n (VD.dirRule up T)
  -- reporting is high in state `up` and low in the other state
  have hmem : ∀ ω, 0 < E.rp s ω ∧ E.rp s ω < 1 := fun ω => by
    have h1 := rp_mem_eps he ω
    have h2 := eps_pos hN
    exact ⟨lt_of_lt_of_le h2 h1.1, lt_of_le_of_lt h1.2 (by linarith)⟩
  have hup' : τ + η ≤ E.rp s up := by
    have h1 := (gross_sign (E := E.base) hV up (hmem up).1 (hmem up).2 hT1 hTn).1
    have h2 := (band he up).1
    have h3 : E.F up 0 ≤ E.Fm up (E.base.gross n (VD.dirRule up T) (E.rp s up) up) :=
      (E.env up).F_le_Fm h1
    have e : τ + η = hi := by rw [hτ, hη]; ring
    rw [e]
    exact h3.trans h2
  have hdown : E.rp s (!up) ≤ τ - η := by
    have h1 := (gross_sign (E := E.base) hV up (hmem (!up)).1 (hmem (!up)).2 hT1 hTn).2
    have h2 := (band he (!up)).2
    have h3 : E.F (!up) (E.base.gross n (VD.dirRule up T) (E.rp s (!up)) (!up)) ≤ E.F (!up) 0 :=
      (E.env (!up)).F_mono h1.le
    have e : τ - η = lo := by rw [hτ, hη]; ring
    rw [e]
    exact h2.trans h3
  have hpay := sep_payoff (E := E.base) hV up hη0 hτ0.le hn (q := E.rp s) (fun ω => rp_mem s ω) hup' hdown
  have hmemP : E.payoff n (VD.dirRule up T) s ∈ E.payoffs n := ⟨_, s, he, rfl⟩
  have hle : E.payoff n (VD.dirRule up T) s ≤ E.Pi n := le_csSup ⟨_, le_PiFB n⟩ hmemP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have e : (VD.pr E.base * VD.H E.base - (1 - VD.pr E.base) * VD.L E.base) * (1 / η ^ 2) * (1 / (n : ℝ))
      = (VD.pr E.base * VD.H E.base - (1 - VD.pr E.base) * VD.L E.base) * (1 / ((n : ℝ) * η ^ 2)) := by
    field_simp
  rw [e]
  exact hpay.trans hle

/-- **Proposition `prop_state_dependent`.** -/
theorem prop_state_dependent (hV : VD.Assumptions E.base) (hN : E.Noise) :
    (E.F true 0 = E.F false 0 →
      (∀ δ > 0, (∀ ω, E.F ω δ - E.F ω (-δ) = 0) → ∃ nStar : ℕ, ∀ n > nStar, E.Pi n = E.base.PiSQ) ∧
      (HasDerivAt (E.F true) 0 0 → HasDerivAt (E.F false) 0 0 → Tendsto E.Pi atTop (𝓝 E.base.PiSQ)) ∧
      (∀ t₁ t₀ : ℝ, HasDerivAt (E.F true) t₁ 0 → HasDerivAt (E.F false) t₀ 0 →
        ∃ β : ℝ, 0 < β ∧ β < 1 ∧ limsup E.Pi atTop ≤ β * E.base.PiSQ + (1 - β) * E.base.PiFB ∧
          β * E.base.PiSQ + (1 - β) * E.base.PiFB < E.base.PiFB)) ∧
    (E.F true 0 ≠ E.F false 0 → Tendsto E.Pi atTop (𝓝 E.base.PiFB)) :=
  ⟨fun hs => ⟨fun _ hδ hF => statement1 hN hs hδ hF, fun h₁ h₀ => statement2 hN hV hs h₁ h₀,
    fun _ _ h₁ h₀ => statement3 hV hN hs h₁ h₀⟩, fun hs => statement_final hV hN hs⟩

end SDEnv

end OA

end NoisyVD
