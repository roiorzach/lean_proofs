import NoisyVD.GeneralUpper

/-!
# Proposition `prop_general_failures`, Statement 4

If `F` has an atom at zero the decision-maker approaches her first-best payoff.  We follow the
paper's construction: a non-monotone rule built from finitely many "modules" `[c_j - ρ, c_j + ρ]`
inside `(F(0⁻), F(0))`, with zero-cost types mixing so that the gross benefit of reporting vanishes.
In states with `g(ω) > 2e_n`, the reporting probability is the smallest maximizer of `W_{n,ω}` over
`[x_{j*(ω)}^-, x_{j*(ω)}^+]`; both `j*` and this maximizer are measurable in `ω`.
-/

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace NoisyVD

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-- The uniform mixture `d̄` over finitely many actions. -/
noncomputable def mixPM {K : ℕ} (hK : 0 < K) (a : Fin K → A) : ProbabilityMeasure A :=
  ⟨∑ j, ((K : ℝ≥0∞)⁻¹) • Measure.dirac (a j), by
    constructor
    simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hK.ne') (ENNReal.natCast_ne_top K)⟩

/-- The rule of equation `eq_general_module_rule`. -/
noncomputable def moduleRule {K : ℕ} (hK : 0 < K) (a : Fin K → A) (c : Fin K → ℝ) (ρ : ℝ) (n : ℕ) :
    Rule A := fun k =>
  open Classical in
  if h : ∃ j, |(k : ℝ) / n - c j| ≤ ρ then diracPM (a h.choose) else mixPM hK a

/-- Concentration: Chebyshev bound for `bexp`. -/
lemma abs_bexp_sub_le {n : ℕ} (hn : 1 ≤ n) {p r y B : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 < r)
    {f : ℕ → ℝ} (hclose : ∀ k, k ≤ n → |(k : ℝ) / n - p| < r → f k = y)
    (hB : ∀ k, |f k - y| ≤ B) : |bexp n p f - y| ≤ B / (4 * n * r ^ 2) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have heq : bexp n p f - y = ∑ k ∈ Finset.range (n + 1), bpmf n p k * (f k - y) := by
    unfold bexp
    have : y = ∑ k ∈ Finset.range (n + 1), bpmf n p k * y := by
      rw [← Finset.sum_mul, bpmf_sum, one_mul]
    conv_lhs => rw [this]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [heq]
  -- restrict to the far values
  let S := (Finset.range (n + 1)).filter (fun k : ℕ => (n : ℝ) * r ≤ |(k : ℝ) - (n : ℝ) * p|)
  have hcheb := bpmf_chebyshev (m := n) hp0 hp1 (a := (n : ℝ) * r) (by positivity)
  have hS : ∑ k ∈ S, bpmf n p k ≤ 1 / (4 * n * r ^ 2) := by
    refine hcheb.trans ?_
    have hpq : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (n : ℝ) * p * (1 - p) * (4 * n * r ^ 2) = (n : ℝ) * (n * r ^ 2) * (4 * (p * (1 - p))) := by
      ring
    rw [this]
    have hnn : 0 ≤ (n : ℝ) * (n * r ^ 2) := by positivity
    nlinarith
  have hbound : ∀ k ∈ Finset.range (n + 1), |bpmf n p k * (f k - y)|
      ≤ if (n : ℝ) * r ≤ |(k : ℝ) - (n : ℝ) * p| then bpmf n p k * B else 0 := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [abs_mul, abs_of_nonneg (bpmf_nonneg hp0 hp1)]
    by_cases hfar : (n : ℝ) * r ≤ |(k : ℝ) - (n : ℝ) * p|
    · rw [ite_eq_left hfar]
      exact mul_le_mul_of_nonneg_left (hB k) (bpmf_nonneg hp0 hp1)
    · rw [ite_eq_right hfar]
      have hc : |(k : ℝ) / n - p| < r := by
        push Not at hfar
        have e : (k : ℝ) / n - p = ((k : ℝ) - n * p) / n := by field_simp
        rw [e, abs_div, abs_of_pos hnr, div_lt_iff₀ hnr]
        linarith
      rw [hclose k hk' hc]
      simp
  calc |∑ k ∈ Finset.range (n + 1), bpmf n p k * (f k - y)|
      ≤ ∑ k ∈ Finset.range (n + 1), |bpmf n p k * (f k - y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          (if (n : ℝ) * r ≤ |(k : ℝ) - (n : ℝ) * p| then bpmf n p k * B else 0) :=
        Finset.sum_le_sum hbound
    _ = (∑ k ∈ S, bpmf n p k) * B := by
        rw [Finset.sum_mul, Finset.sum_filter]
    _ ≤ (1 / (4 * n * r ^ 2)) * B := mul_le_mul_of_nonneg_right hS h0
    _ = B / (4 * n * r ^ 2) := by ring

namespace Env

/-- Equation `eq_general_finite_action_approximation`: finitely many actions approximate the maximum
uniformly in the state. -/
lemma exists_finite_actions (E : Env A Ω) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (K : ℕ) (_ : 0 < K) (a : Fin K → A), ∀ ω, ∃ j, E.maxU ω - ξ ≤ E.u (a j) ω := by
  let U : C(A × Ω, ℝ) := ⟨Function.uncurry E.u, E.u_cont⟩
  let Uc : C(A, C(Ω, ℝ)) := U.curry
  have hopen : ∀ a₀ : A, {a | dist (Uc a) (Uc a₀) < ξ} ∈ 𝓝 a₀ := fun a₀ =>
    (isOpen_lt (Uc.continuous.dist continuous_const) continuous_const).mem_nhds (by simpa using hξ)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun a₀ => {a | dist (Uc a) (Uc a₀) < ξ})
    (fun a₀ _ => hopen a₀)
  obtain ⟨_, hcover⟩ := ht
  have htne : t.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨a⟩ := ‹Nonempty A›
    have := hcover (mem_univ a)
    simp [hne] at this
  refine ⟨t.card, Finset.card_pos.2 htne, fun j => (t.equivFin.symm j : A), fun ω => ?_⟩
  obtain ⟨a, ha⟩ := E.exists_maxU ω
  have hmem := hcover (mem_univ a)
  simp only [mem_iUnion, exists_prop] at hmem
  obtain ⟨a₀, ha₀, hdist⟩ := hmem
  refine ⟨t.equivFin ⟨a₀, ha₀⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  have hd : dist (Uc a) (Uc a₀) < ξ := hdist
  have h2 := (ContinuousMap.dist_lt_iff hξ).1 hd ω
  have h3 : dist (E.u a ω) (E.u a₀ ω) < ξ := h2
  rw [Real.dist_eq, abs_lt] at h3
  rw [← ha]
  linarith [h3.2]

/-- Module value: `v_k = u(a_j)` when the report share is in module `j`. -/
lemma v_module_close (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) {c : Fin K → ℝ} {ρ : ℝ}
    (hsep : ∀ i j, i ≠ j → 10 * ρ ≤ |c i - c j|) (hρ : 0 < ρ) {n k : ℕ} {j : Fin K}
    (hj : |(k : ℝ) / n - c j| ≤ ρ) (ω : Ω) :
    E.v (moduleRule hK a c ρ n) k ω = E.u (a j) ω := by
  have hex : ∃ j, |(k : ℝ) / n - c j| ≤ ρ := ⟨j, hj⟩
  have hunique : hex.choose = j := by
    by_contra hne
    have h1 := hsep _ _ hne
    have h2 := hex.choose_spec
    have h3 : |c hex.choose - c j| ≤ |(k : ℝ) / n - c hex.choose| + |(k : ℝ) / n - c j| := by
      have := abs_sub_le (c hex.choose) ((k : ℝ) / n) (c j)
      rwa [abs_sub_comm (c hex.choose) ((k : ℝ) / n)] at this
    linarith
  refine E.v_dirac ?_ ω
  unfold moduleRule
  rw [dite_eq_left hex, hunique]

/-- The average payoff `ū`. -/
noncomputable def uBar (E : Env A Ω) {K : ℕ} (a : Fin K → A) (ω : Ω) : ℝ :=
  (1 / (K : ℝ)) * ∑ j, E.u (a j) ω

lemma v_module_far (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) {c : Fin K → ℝ} {ρ : ℝ}
    {n k : ℕ} (hfar : ∀ j, ρ < |(k : ℝ) / n - c j|) (ω : Ω) :
    E.v (moduleRule hK a c ρ n) k ω = E.uBar a ω := by
  have hex : ¬ ∃ j, |(k : ℝ) / n - c j| ≤ ρ := by
    rintro ⟨j, hj⟩
    exact absurd (hfar j) (not_lt.2 hj)
  unfold v moduleRule
  rw [dite_eq_right hex]
  show ∫ x, E.u x ω ∂(∑ j, ((K : ℝ≥0∞)⁻¹) • Measure.dirac (a j)) = _
  rw [integral_finsetSum_measure]
  · unfold uBar
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_measure, integral_dirac]
    simp
  · intro j _
    refine Integrable.smul_measure ?_ (by simpa using hK.ne')
    exact integrable_dirac (by simp)

lemma uBar_mem (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (ω : Ω) :
    E.uMin ≤ E.uBar a ω ∧ E.uBar a ω ≤ E.uMax := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold uBar
  constructor
  · rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hKr]
    calc E.uMin * K = ∑ _j : Fin K, E.uMin := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ => E.uMin_le_u _ _
  · rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hKr]
    calc ∑ j, E.u (a j) ω ≤ ∑ _j : Fin K, E.uMax := Finset.sum_le_sum fun j _ => E.u_le_uMax _ _
      _ = E.uMax * K := by simp [mul_comm]

lemma continuous_uBar (E : Env A Ω) {K : ℕ} (a : Fin K → A) : Continuous (E.uBar a) := by
  unfold uBar
  exact continuous_const.mul (continuous_finsetSum _ fun j _ => E.continuous_u_right _)

/-- `M_K(ω) = max_j u(a_j, ω)`. -/
noncomputable def maxK (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (ω : Ω) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hK⟩, Finset.mem_univ _⟩ fun j => E.u (a j) ω

lemma le_maxK (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (ω : Ω) (j : Fin K) :
    E.u (a j) ω ≤ E.maxK hK a ω :=
  Finset.le_sup' (fun j => E.u (a j) ω) (Finset.mem_univ j)

lemma exists_maxK (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (ω : Ω) :
    ∃ j, E.u (a j) ω = E.maxK hK a ω := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) ⟨⟨0, hK⟩, Finset.mem_univ _⟩
    (fun j => E.u (a j) ω)
  exact ⟨j, hj.symm⟩

lemma continuous_maxK (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) :
    Continuous (E.maxK hK a) := by
  unfold maxK
  exact Continuous.finset_sup'_apply _ fun j _ => E.continuous_u_right _

lemma continuous_bexp_joint (E : Env A Ω) (n : ℕ) (d : Rule A) :
    Continuous fun z : Ω × ℝ => bexp n z.2 (fun k => E.v d k z.1) := by
  unfold bexp
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((continuous_bpmf n k).comp continuous_snd).mul ((E.continuous_v d k).comp continuous_fst)

lemma abs_v_sub_u_le (E : Env A Ω) (d : Rule A) (k : ℕ) (ω : Ω) {y : ℝ} (h1 : E.uMin ≤ y)
    (h2 : y ≤ E.uMax) : |E.v d k ω - y| ≤ E.B := by
  have h3 := E.v_le_uMax d k ω
  have h4 := E.uMin_le_v d k ω
  unfold B
  rw [abs_le]
  constructor <;> linarith

/-- The data of the module construction. -/
structure Modules (K : ℕ) where
  c : Fin K → ℝ
  ρ : ℝ
  ρ_pos : 0 < ρ
  sep : ∀ i j, i ≠ j → 10 * ρ ≤ |c i - c j|

/-- Concentration at a module centre: `|W(c_j) - u(a_j)| ≤ e_n`. -/
lemma W_center (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (D : Modules K) {n : ℕ} (hn : 1 ≤ n)
    (j : Fin K) (h0 : 0 ≤ D.c j) (h1 : D.c j ≤ 1) (ω : Ω) :
    |bexp n (D.c j) (fun k => E.v (moduleRule hK a D.c D.ρ n) k ω) - E.u (a j) ω|
      ≤ E.B / (4 * n * D.ρ ^ 2) := by
  refine abs_bexp_sub_le hn h0 h1 D.ρ_pos (fun k _ hk => ?_) (fun k => ?_)
  · exact E.v_module_close hK a D.sep D.ρ_pos hk.le ω
  · exact E.abs_v_sub_u_le _ k ω (E.uMin_le_u _ _) (E.u_le_uMax _ _)

/-- Concentration at the side points `x_j^± = c_j ± 3ρ`: `|W(x_j^±) - ū| ≤ e_n`. -/
lemma W_side (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (D : Modules K) {n : ℕ} (hn : 1 ≤ n)
    (j : Fin K) {x : ℝ} (hx : |x - D.c j| = 3 * D.ρ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (ω : Ω) :
    |bexp n x (fun k => E.v (moduleRule hK a D.c D.ρ n) k ω) - E.uBar a ω|
      ≤ E.B / (4 * n * D.ρ ^ 2) := by
  have hρ := D.ρ_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := abs_bexp_sub_le (f := fun k => E.v (moduleRule hK a D.c D.ρ n) k ω) (y := E.uBar a ω)
    (B := E.B) (r := 2 * D.ρ) hn h0 h1 (by linarith) (fun k _ hk => ?_) (fun k => ?_)
  · refine hb.trans ?_
    apply div_le_div_of_nonneg_left E.B_nonneg (by positivity)
    have : 0 < (n : ℝ) * D.ρ ^ 2 := by positivity
    nlinarith
  · refine E.v_module_far hK a (fun l => ?_) ω
    by_cases hl : l = j
    · subst hl
      have h3 := abs_sub_abs_le_abs_sub (x - D.c l) (x - (k : ℝ) / n)
      have e : x - D.c l - (x - (k : ℝ) / n) = (k : ℝ) / n - D.c l := by ring
      rw [e, hx, abs_sub_comm x] at h3
      linarith
    · have h3 := D.sep j l (Ne.symm hl)
      have h4 : |D.c j - D.c l| ≤ |D.c j - x| + |x - (k : ℝ) / n| + |(k : ℝ) / n - D.c l| := by
        have s1 := abs_sub_le (D.c j) x (D.c l)
        have s2 := abs_sub_le x ((k : ℝ) / n) (D.c l)
        linarith
      rw [abs_sub_comm (D.c j) x, hx, abs_sub_comm x ((k : ℝ) / n)] at h4
      linarith
  · have := E.uBar_mem hK a ω
    exact E.abs_v_sub_u_le _ k ω this.1 this.2

/-- `j*(ω)`: the smallest index with `u(a_j, ω) = M_K(ω)`. -/
noncomputable def jStar (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (ω : Ω) : Fin K :=
  open Classical in
  (Finset.univ.filter fun j => E.u (a j) ω = E.maxK hK a ω).min' (by
    obtain ⟨j, hj⟩ := E.exists_maxK hK a ω
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩)

lemma u_jStar (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (ω : Ω) :
    E.u (a (E.jStar hK a ω)) ω = E.maxK hK a ω := by
  classical
  have h := Finset.min'_mem (Finset.univ.filter fun j => E.u (a j) ω = E.maxK hK a ω) (by
    obtain ⟨j, hj⟩ := E.exists_maxK hK a ω
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩)
  exact (Finset.mem_filter.1 h).2

lemma jStar_le (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (ω : Ω) {j : Fin K}
    (hj : E.u (a j) ω = E.maxK hK a ω) : E.jStar hK a ω ≤ j := by
  classical
  unfold jStar
  exact Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)

/-- `j*` is measurable, because `{j* = j}` is a finite Boolean combination of closed sets. -/
lemma measurable_jStar (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) :
    Measurable (E.jStar hK a) := by
  have hclosed : ∀ j, MeasurableSet {ω | E.u (a j) ω = E.maxK hK a ω} := fun j =>
    (isClosed_eq (E.continuous_u_right _) (E.continuous_maxK hK a)).measurableSet
  refine measurable_to_countable' fun j => ?_
  have heq : E.jStar hK a ⁻¹' {j} = {ω | E.u (a j) ω = E.maxK hK a ω} ∩
      ⋂ i ∈ {i : Fin K | i < j}, {ω | E.u (a i) ω = E.maxK hK a ω}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_compl_iff]
    constructor
    · rintro rfl
      exact ⟨E.u_jStar hK a ω, fun i hi hu => absurd (E.jStar_le hK a ω hu) (not_le.2 hi)⟩
    · rintro ⟨h1, h2⟩
      refine le_antisymm (E.jStar_le hK a ω h1) ?_
      by_contra hlt
      exact h2 _ (not_le.1 hlt) (E.u_jStar hK a ω)
  rw [heq]
  refine (hclosed j).inter (MeasurableSet.biInter (Set.to_countable _) fun i _ => (hclosed i).compl)

/-- The maximizers of `W_{n,ω}` over `[c_j - 3ρ, c_j + 3ρ]`, as a closed subset of `Ω × ℝ`. -/
def maximizers (W : Ω × ℝ → ℝ) (lo hi : ℝ) : Set (Ω × ℝ) :=
  {z | z.2 ∈ Icc lo hi ∧ ∀ y ∈ Icc lo hi, W (z.1, y) ≤ W z}

lemma isClosed_maximizers {W : Ω × ℝ → ℝ} (hW : Continuous W) (lo hi : ℝ) :
    IsClosed (maximizers W lo hi) := by
  have h1 : IsClosed {z : Ω × ℝ | z.2 ∈ Icc lo hi} := isClosed_Icc.preimage continuous_snd
  have h2 : IsClosed {z : Ω × ℝ | ∀ y ∈ Icc lo hi, W (z.1, y) ≤ W z} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le (hW.comp (continuous_fst.prodMk continuous_const)) hW
  exact h1.inter h2

/-- **The measurable selection.**  Because `j*` takes finitely many values and `W_{n,ω}(p)` is jointly
continuous in `(p, ω)`, the smallest maximizer over `[x_{j*(ω)}^-, x_{j*(ω)}^+]` is measurable in `ω`. -/
lemma exists_measurable_maximizer (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) {W : Ω × ℝ → ℝ}
    (hW : Continuous W) {lo hi : Fin K → ℝ} (hle : ∀ j, lo j ≤ hi j) :
    ∃ q : Ω → ℝ, Measurable q ∧ ∀ ω, q ω ∈ Icc (lo (E.jStar hK a ω)) (hi (E.jStar hK a ω)) ∧
      ∀ y ∈ Icc (lo (E.jStar hK a ω)) (hi (E.jStar hK a ω)), W (ω, y) ≤ W (ω, q ω) := by
  have hGne : ∀ j ω, ∃ y, (ω, y) ∈ maximizers W (lo j) (hi j) := by
    intro j ω
    have hc : ContinuousOn (fun y => W (ω, y)) (Icc (lo j) (hi j)) :=
      (hW.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨y, hy, hymax⟩ := isCompact_Icc.exists_isMaxOn ⟨_, left_mem_Icc.2 (hle j)⟩ hc
    exact ⟨y, hy, fun y' hy' => hymax hy'⟩
  have hsel : ∀ j, (Measurable fun ω => sInf {y | (ω, y) ∈ maximizers W (lo j) (hi j)}) ∧
      ∀ ω, (ω, sInf {y | (ω, y) ∈ maximizers W (lo j) (hi j)}) ∈ maximizers W (lo j) (hi j) := fun j =>
    have h := measurable_sInf_section (isClosed_maximizers hW (lo j) (hi j))
      (a := lo j) (b := hi j) (fun z hz => hz.1) (hGne j)
    ⟨h.1, fun ω => (h.2 ω).1⟩
  let pj : Fin K × Ω → ℝ := fun z => sInf {y | (z.2, y) ∈ maximizers W (lo z.1) (hi z.1)}
  have hjoint : Measurable pj := measurable_from_prod_countable_right fun j => (hsel j).1
  have hm : Measurable fun ω => pj (E.jStar hK a ω, ω) :=
    hjoint.comp ((E.measurable_jStar hK a).prodMk measurable_id)
  exact ⟨_, hm, fun ω => (hsel (E.jStar hK a ω)).2 ω⟩

/-- In states with `g(ω) > 2e_n`, the smoothed payoff attains its maximum over
`[x_{j*}^-, x_{j*}^+]` at an interior point, at which the gross benefit of reporting vanishes. -/
lemma interior_of_maximizer (E : Env A Ω) {K : ℕ} (hK : 0 < K) (a : Fin K → A) (D : Modules K) {n : ℕ}
    (hn : 1 ≤ n) {j : Fin K} {ω : Ω} (hj : E.u (a j) ω = E.maxK hK a ω)
    (hlo : 0 ≤ D.c j - 3 * D.ρ) (hhi : D.c j + 3 * D.ρ ≤ 1)
    (hg : 2 * (E.B / (4 * n * D.ρ ^ 2)) < E.maxK hK a ω - E.uBar a ω) {p : ℝ}
    (hpI : p ∈ Icc (D.c j - 3 * D.ρ) (D.c j + 3 * D.ρ))
    (hpmax : ∀ y ∈ Icc (D.c j - 3 * D.ρ) (D.c j + 3 * D.ρ),
      bexp n y (fun k => E.v (moduleRule hK a D.c D.ρ n) k ω)
        ≤ bexp n p (fun k => E.v (moduleRule hK a D.c D.ρ n) k ω)) :
    E.gross n (moduleRule hK a D.c D.ρ n) p ω = 0 ∧
      E.maxK hK a ω - E.B / (4 * n * D.ρ ^ 2)
        ≤ bexp n p (fun k => E.v (moduleRule hK a D.c D.ρ n) k ω) := by
  set d := moduleRule hK a D.c D.ρ n with hd
  set e := E.B / (4 * n * D.ρ ^ 2) with he
  have hρ := D.ρ_pos
  set x₁ := D.c j - 3 * D.ρ with hx₁
  set x₂ := D.c j + 3 * D.ρ with hx₂
  have hc0 : 0 ≤ D.c j := by linarith
  have hc1 : D.c j ≤ 1 := by linarith
  let W : ℝ → ℝ := fun p => bexp n p (fun k => E.v d k ω)
  have hcenter := abs_le.1 (E.W_center hK a D hn j hc0 hc1 ω)
  have hside₁ := abs_le.1 (E.W_side hK a D hn j (x := x₁)
    (by rw [hx₁]; ring_nf; rw [abs_neg, abs_of_pos (by linarith)]) (by linarith) (by linarith) ω)
  have hside₂ := abs_le.1 (E.W_side hK a D hn j (x := x₂)
    (by rw [hx₂]; ring_nf; rw [abs_of_pos (by linarith)]) (by linarith) (by linarith) ω)
  have hWp : W (D.c j) ≤ W p := hpmax _ ⟨by linarith, by linarith⟩
  have hWc2 : E.maxK hK a ω - e ≤ W (D.c j) := by
    have := hcenter.1
    rw [hj] at this
    show E.maxK hK a ω - e ≤ bexp n (D.c j) (fun k => E.v d k ω)
    linarith
  have hW1 : W x₁ < E.maxK hK a ω - e := by
    have : W x₁ ≤ e + E.uBar a ω := by
      have := hside₁.2
      show bexp n x₁ (fun k => E.v d k ω) ≤ _
      linarith
    linarith
  have hW2 : W x₂ < E.maxK hK a ω - e := by
    have : W x₂ ≤ e + E.uBar a ω := by
      have := hside₂.2
      show bexp n x₂ (fun k => E.v d k ω) ≤ _
      linarith
    linarith
  have hp1 : x₁ < p := by
    refine lt_of_le_of_ne hpI.1 ?_
    rintro rfl
    linarith
  have hp2 : p < x₂ := by
    refine lt_of_le_of_ne hpI.2 ?_
    rintro rfl
    linarith
  refine ⟨?_, by
    show E.maxK hK a ω - e ≤ W p
    linarith⟩
  -- first-order condition: equation `eq_general_derivative_identity`
  have hloc : IsLocalMax W p := by
    filter_upwards [Icc_mem_nhds hp1 hp2] with y hy using hpmax y hy
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hder := hasDerivAt_bexp m (fun k => E.v d k ω) p
  have hzero := hloc.hasDerivAt_eq_zero hder
  have hmpos : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have := (mul_eq_zero.1 hzero).resolve_left hmpos
  show marginal (m + 1 - 1) p (fun k => E.v d k ω) = 0
  simpa using this

/-- The module system inside `(s₋, s₊)`. -/
noncomputable def modulesOf (K : ℕ) (sm α : ℝ) (hα : 0 < α) : Modules K where
  c := fun j => sm + α * ((j : ℝ) + 1) / ((K : ℝ) + 1)
  ρ := α / (10 * ((K : ℝ) + 1))
  ρ_pos := by positivity
  sep := by
    intro i j hij
    have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    have h1 : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      have h2 : (1 : ℤ) ≤ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| := by
        apply Int.one_le_abs
        omega
      have h3 : ((1 : ℤ) : ℝ) ≤ ((|((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h2
      simpa using h3
    have e : sm + α * ((i : ℝ) + 1) / ((K : ℝ) + 1) - (sm + α * ((j : ℝ) + 1) / ((K : ℝ) + 1))
        = (α / ((K : ℝ) + 1)) * ((i : ℝ) - j) := by
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < α / ((K : ℝ) + 1))]
    have h4 : 10 * (α / (10 * ((K : ℝ) + 1))) = α / ((K : ℝ) + 1) := by
      field_simp
    rw [h4]
    have h5 : 0 < α / ((K : ℝ) + 1) := by positivity
    nlinarith

/-- For a fixed action set, an equilibrium of the module rule yields the payoff bound of the paper. -/
theorem exists_eq_module_payoff (E : Env A Ω) {α : ℝ} (hα : 0 < α) (hatom : E.F 0 - E.Fm 0 = α)
    {K : ℕ} (hK : 0 < K) (a : Fin K → A) {n : ℕ} (hn : 1 ≤ n) :
    let D := modulesOf K (E.Fm 0) α hα
    ∃ s : Strat Ω, E.IsEq n (moduleRule hK a D.c D.ρ n) s ∧
      ∀ ω, E.maxK hK a ω - 2 * K * (E.B / (4 * n * D.ρ ^ 2))
        ≤ bexp n (E.rp s ω) (fun k => E.v (moduleRule hK a D.c D.ρ n) k ω) := by
  intro D
  set d := moduleRule hK a D.c D.ρ n with hd
  set e := E.B / (4 * n * D.ρ ^ 2) with he
  have hρ := D.ρ_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have he0 : 0 ≤ e := div_nonneg E.B_nonneg (by positivity)
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set sm := E.Fm 0 with hsm
  have hsm0 : 0 ≤ sm := E.Fm_nonneg 0
  have hsp1 : sm + α ≤ 1 := by
    have := E.F_le_one 0
    linarith
  set lo := sm + D.ρ with hlo
  set hi := sm + α - D.ρ with hhi
  have hcdef : ∀ j : Fin K, D.c j = sm + α * ((j : ℝ) + 1) / ((K : ℝ) + 1) := fun _ => rfl
  have hρdef : D.ρ = α / (10 * ((K : ℝ) + 1)) := rfl
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hscale : α / ((K : ℝ) + 1) = 10 * D.ρ := by
    rw [hρdef]; field_simp
  have hαρ : α = 10 * ((K : ℝ) + 1) * D.ρ := by
    rw [hρdef]; field_simp
  have hcj1 : ∀ j : Fin K, sm + 10 * D.ρ ≤ D.c j := by
    intro j
    rw [hcdef, ← hscale]
    have : α / ((K : ℝ) + 1) ≤ α * ((j : ℝ) + 1) / ((K : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right _ hK1.le
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      nlinarith
    linarith
  have hcj2 : ∀ j : Fin K, D.c j ≤ sm + α - 10 * D.ρ := by
    intro j
    rw [hcdef, ← hscale]
    have hj : ((j : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast j.2
    have : α * ((j : ℝ) + 1) / ((K : ℝ) + 1) + α / ((K : ℝ) + 1) ≤ α := by
      rw [← add_div, div_le_iff₀ hK1]
      nlinarith
    linarith
  have hlojx : ∀ j, lo ≤ D.c j - 3 * D.ρ := fun j => by rw [hlo]; linarith [hcj1 j]
  have hhijx : ∀ j, D.c j + 3 * D.ρ ≤ hi := fun j => by rw [hhi]; linarith [hcj2 j]
  have hlo0 : 0 ≤ lo := by rw [hlo]; linarith
  have hhi1 : hi ≤ 1 := by rw [hhi]; linarith
  have hlohi : lo ≤ hi := by
    obtain ⟨j⟩ : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    linarith [hlojx j, hhijx j]
  let g : Ω → ℝ := fun ω => E.maxK hK a ω - E.uBar a ω
  have hgc : Continuous g := (E.continuous_maxK hK a).sub (E.continuous_uBar a)
  let W : Ω × ℝ → ℝ := fun z => bexp n z.2 (fun k => E.v d k z.1)
  have hWc : Continuous W := E.continuous_bexp_joint n d
  have hΔc := E.continuous_gross n d
  -- `p*_{n,ω}`: the smallest maximizer over `[x_{j*}^-, x_{j*}^+]`, measurable in `ω`
  obtain ⟨q, hqm, hqspec⟩ := E.exists_measurable_maximizer hK a hWc
    (lo := fun j => D.c j - 3 * D.ρ) (hi := fun j => D.c j + 3 * D.ρ) (fun j => by linarith)
  have hqI : ∀ ω, q ω ∈ Icc lo hi := fun ω => by
    have h1 := (hqspec ω).1
    exact ⟨(hlojx _).trans h1.1, h1.2.trans (hhijx _)⟩
  -- a background equilibrium
  obtain ⟨s₀, hs₀⟩ := E.exists_equilibrium n d
  have hmeasG : MeasurableSet {ω | 2 * e < g ω} := measurableSet_lt measurable_const hgc.measurable
  classical
  let q' : Ω → ℝ := fun ω => if 2 * e < g ω then q ω else E.rp s₀ ω
  let c' : Ω → ℝ := fun ω => if 2 * e < g ω then 0 else E.gross n d (E.rp s₀ ω) ω
  have hq'm : Measurable q' := Measurable.ite hmeasG hqm (measurable_rp E s₀)
  have hc'm : Measurable c' := Measurable.ite hmeasG measurable_const
    (hΔc.measurable.comp (measurable_id.prodMk (measurable_rp E s₀)))
  have hband : ∀ ω, E.Fm (c' ω) ≤ q' ω ∧ q' ω ≤ E.F (c' ω) := by
    intro ω
    by_cases hgω : 2 * e < g ω
    · simp only [q', c', ite_eq_left hgω]
      have hqI' := hqI ω
      have hF0 : E.F 0 = sm + α := by linarith
      rw [hF0]
      constructor
      · rw [hlo] at hqI'
        have := hqI'.1
        linarith
      · rw [hhi] at hqI'
        have := hqI'.2
        linarith
    · simp only [q', c', ite_eq_right hgω]
      exact band E hs₀ ω
  obtain ⟨s, hrp, hs1, hs2⟩ := E.exists_cutoff_strategy hq'm hc'm hband
  have hgrossq : ∀ ω, 2 * e < g ω → E.gross n d (q ω) ω = 0 ∧ E.maxK hK a ω - e ≤ W (ω, q ω) := by
    intro ω hgω
    have hx := hqspec ω
    exact E.interior_of_maximizer hK a D hn (E.u_jStar hK a ω)
      ((hlo0.trans (hlojx _))) ((hhijx _).trans hhi1) hgω hx.1 hx.2
  have hgross : ∀ ω, E.gross n d (E.rp s ω) ω = c' ω := by
    intro ω
    rw [hrp ω]
    by_cases hgω : 2 * e < g ω
    · simp only [q', c', ite_eq_left hgω]
      exact (hgrossq ω hgω).1
    · simp only [q', c', ite_eq_right hgω]
  refine ⟨s, fun ω x => ?_, fun ω => ?_⟩
  · rw [hgross ω]
    exact ⟨hs1 ω x, hs2 ω x⟩
  · by_cases hgω : 2 * e < g ω
    · have h1 : E.rp s ω = q ω := by
        rw [hrp ω]; simp only [q', ite_eq_left hgω]
      rw [h1]
      have h2 := (hgrossq ω hgω).2
      have : e ≤ 2 * K * e := by nlinarith
      show _ ≤ W (ω, q ω)
      linarith
    · -- every action distribution is nearly optimal
      have hgle : g ω ≤ 2 * e := not_lt.1 hgω
      have hg0 : 0 ≤ g ω := by
        have hKr' : (0 : ℝ) < K := by linarith
        simp only [g, uBar]
        rw [sub_nonneg, one_div, ← div_eq_inv_mul, div_le_iff₀ hKr']
        calc ∑ j, E.u (a j) ω ≤ ∑ _j : Fin K, E.maxK hK a ω :=
              Finset.sum_le_sum fun j _ => E.le_maxK hK a ω j
          _ = E.maxK hK a ω * K := by simp [mul_comm]
      have huj : ∀ j, E.maxK hK a ω - 2 * K * e ≤ E.u (a j) ω := by
        intro j
        have hsum : ∑ l, (E.maxK hK a ω - E.u (a l) ω) = K * g ω := by
          rw [Finset.sum_sub_distrib]
          simp only [g, uBar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hKr' : (K : ℝ) ≠ 0 := by positivity
          field_simp
        have hsingle : E.maxK hK a ω - E.u (a j) ω ≤ ∑ l, (E.maxK hK a ω - E.u (a l) ω) :=
          Finset.single_le_sum (f := fun l => E.maxK hK a ω - E.u (a l) ω)
            (fun l _ => sub_nonneg.2 (E.le_maxK hK a ω l)) (Finset.mem_univ j)
        have : (K : ℝ) * g ω ≤ K * (2 * e) := mul_le_mul_of_nonneg_left hgle (by linarith)
        linarith
      have hubar : E.maxK hK a ω - 2 * K * e ≤ E.uBar a ω := by
        have : g ω ≤ 2 * K * e := by nlinarith
        simp only [g] at this
        linarith
      have hvk : ∀ k, E.maxK hK a ω - 2 * K * e ≤ E.v d k ω := by
        intro k
        by_cases hex : ∃ j, |(k : ℝ) / n - D.c j| ≤ D.ρ
        · obtain ⟨j, hj⟩ := hex
          rw [E.v_module_close hK a D.sep hρ hj ω]
          exact huj j
        · push Not at hex
          rw [E.v_module_far hK a hex ω]
          exact hubar
      have h0 := rp_nonneg E s ω
      have h1 := rp_le_one E s ω
      unfold bexp
      calc E.maxK hK a ω - 2 * K * e
          = ∑ k ∈ Finset.range (n + 1), bpmf n (E.rp s ω) k * (E.maxK hK a ω - 2 * K * e) := by
            rw [← Finset.sum_mul, bpmf_sum, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hvk k) (bpmf_nonneg h0 h1)

/-- A positive limit of `F(δ) - F(-δ)` forces an atom at zero. -/
lemma atom_pos (E : Env A Ω) {α : ℝ} (hα : 0 < α)
    (h : Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α)) : 0 < E.F 0 - E.Fm 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : E.Fm 0 - α / 4 < E.Fm 0 := by linarith
  obtain ⟨c₀, hc₀, hy⟩ := E.exists_lt_Fm h1
  have husc : ∀ᶠ x in 𝓝 (0 : ℝ), E.F x < E.F 0 + α / 4 :=
    E.upperSemicontinuous_F 0 _ (by linarith)
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), E.F δ < E.F 0 + α / 4 := husc.filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < -c₀ := by
    have : -c₀ > 0 := by linarith
    filter_upwards [Ioo_mem_nhdsGT this] with δ hδ using hδ.2
  have h4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), α / 2 < E.F δ - E.F (-δ) :=
    (tendsto_order.1 h).1 _ (by linarith)
  obtain ⟨δ, hδ2, hδ3, hδ4⟩ := (h2.and (h3.and h4)).exists
  have h5 : E.Fm c₀ ≤ E.F (-δ) := (E.Fm_mono (by linarith)).trans (E.Fm_le_F _)
  linarith

/-- **Proposition `prop_general_failures`, Statement 4.** -/
theorem prop_general_4 (E : Env A Ω) {α : ℝ} (hα : 0 < α)
    (h : Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α)) :
    Tendsto E.Pi atTop (𝓝 E.PiFB) := by
  have hat := E.atom_pos hα h
  set α' := E.F 0 - E.Fm 0 with hα'
  rw [tendsto_order]
  refine ⟨fun y hy => ?_, fun y hy => Eventually.of_forall fun n =>
    lt_of_le_of_lt (E.Pi_le_PiFB n) hy⟩
  -- Fix `ξ` and the actions
  set ξ := (E.PiFB - y) / 3 with hξ
  have hξ0 : 0 < ξ := by rw [hξ]; linarith
  obtain ⟨K, hK, a, ha⟩ := E.exists_finite_actions hξ0
  set D := modulesOf K (E.Fm 0) α' hat with hD
  have hρ := D.ρ_pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  -- `2 K e_n → 0`
  have hlim : Tendsto (fun n : ℕ => 2 * K * (E.B / (4 * n * D.ρ ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 4 * (n : ℝ) * D.ρ ^ 2) atTop atTop := by
      have h2 : Tendsto (fun n : ℕ => (n : ℝ) * (4 * D.ρ ^ 2)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
      refine h2.congr fun n => ?_
      ring
    have h3 := (Tendsto.const_div_atTop h1 E.B).const_mul (2 * (K : ℝ))
    simpa using h3
  have hev := (tendsto_order.1 hlim).2 ξ hξ0
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨s, he, hpt⟩ := E.exists_eq_module_payoff hat rfl hK a hn1
  have hmem : E.payoff n (moduleRule hK a D.c D.ρ n) s ∈ E.payoffs n := ⟨_, s, he, rfl⟩
  have hle := le_csSup (E.bddAbove_payoffs n) hmem
  -- integrate the pointwise bound
  set c0 := 2 * K * (E.B / (4 * n * D.ρ ^ 2)) with hc0
  have hint : ∫ ω, (E.maxU ω - ξ - c0) ∂(E.prior : Measure Ω) = E.PiFB - ξ - c0 := by
    have i1 : Integrable (fun ω => E.maxU ω - ξ) (E.prior : Measure Ω) :=
      E.integrable_maxU.sub (integrable_const ξ)
    rw [integral_sub i1 (integrable_const c0), integral_sub E.integrable_maxU (integrable_const ξ)]
    simp [PiFB]
  have hbd : E.PiFB - ξ - c0 ≤ E.payoff n (moduleRule hK a D.c D.ρ n) s := by
    rw [← hint]
    have i1 : Integrable (fun ω => E.maxU ω - ξ) (E.prior : Measure Ω) :=
      E.integrable_maxU.sub (integrable_const ξ)
    refine integral_mono (i1.sub (integrable_const c0)) (E.integrable_bexp n _ s) fun ω => ?_
    obtain ⟨j, hj⟩ := ha ω
    have h1 := E.le_maxK hK a ω j
    have h2 := hpt ω
    show E.maxU ω - ξ - c0 ≤ bexp n (E.rp s ω) _
    linarith
  have hy3 : y = E.PiFB - 3 * ξ := by rw [hξ]; ring
  have hh : y < E.Pi n := by
    have h6 : c0 < ξ := hn
    have h7 : E.payoff n (moduleRule hK a D.c D.ρ n) s ≤ E.Pi n := hle
    linarith
  exact hh

end Env

end NoisyVD
