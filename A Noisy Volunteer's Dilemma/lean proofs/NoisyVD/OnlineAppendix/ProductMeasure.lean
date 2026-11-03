import NoisyVD.Binomial

/-!
# Finite products of probability measures

The probabilistic core of the general message space extension, independent of the economic model:

* `exists_density`: a measure sandwiched between multiples of `P` has a bounded density;
* `pi_withDensity`: the product of tilted measures is the product measure tilted by the product density;
* `anon_bound_of_density`, `anon_bound`: replacing one of `n` i.i.d. draws by a draw from a dominated law
  moves the mean of a symmetric bounded function by at most `(B/2) √((Λ-1)/n)`;
* `IsTilt.abs_sub_le`, `IsTilt.sq_le`: the second-moment and inverse-moment comparisons of `Pⁿ` and
  `(P⁰)ⁿ` when `P` has density in `[1-c, 1+c]` with respect to `P⁰`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace NoisyVD

namespace OA

section Bounded

variable {Y : Type*} [MeasurableSpace Y]

/-- Bounded and measurable. -/
def BM (f : Y → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ y, |f y| ≤ C

lemma BM.const (c : ℝ) : BM (fun _ : Y => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

lemma BM.mul {f g : Y → ℝ} (hf : BM f) (hg : BM g) : BM (fun y => f y * g y) := by
  obtain ⟨mf, Cf, hCf⟩ := hf
  obtain ⟨mg, Cg, hCg⟩ := hg
  refine ⟨mf.mul mg, Cf * Cg, fun y => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hCf y) (hCg y) (abs_nonneg _) ((abs_nonneg _).trans (hCf y))

lemma BM.add {f g : Y → ℝ} (hf : BM f) (hg : BM g) : BM (fun y => f y + g y) := by
  obtain ⟨mf, Cf, hCf⟩ := hf
  obtain ⟨mg, Cg, hCg⟩ := hg
  exact ⟨mf.add mg, Cf + Cg, fun y => (abs_add_le _ _).trans (add_le_add (hCf y) (hCg y))⟩

lemma BM.sub {f g : Y → ℝ} (hf : BM f) (hg : BM g) : BM (fun y => f y - g y) := by
  obtain ⟨mf, Cf, hCf⟩ := hf
  obtain ⟨mg, Cg, hCg⟩ := hg
  exact ⟨mf.sub mg, Cf + Cg, fun y => (abs_sub _ _).trans (add_le_add (hCf y) (hCg y))⟩

lemma BM.pow {f : Y → ℝ} (hf : BM f) (k : ℕ) : BM (fun y => f y ^ k) := by
  obtain ⟨mf, Cf, hCf⟩ := hf
  refine ⟨mf.pow_const k, Cf ^ k, fun y => ?_⟩
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hCf y) k

lemma BM.integrable {f : Y → ℝ} (hf : BM f) (μ : Measure Y) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨mf, C, hC⟩ := hf
  exact Integrable.of_bound mf.aestronglyMeasurable C (ae_of_all _ fun y => by simpa using hC y)

lemma BM.integral_add {f g : Y → ℝ} (hf : BM f) (hg : BM g) (μ : Measure Y) [IsFiniteMeasure μ] :
    ∫ y, (f y + g y) ∂μ = ∫ y, f y ∂μ + ∫ y, g y ∂μ :=
  MeasureTheory.integral_add (hf.integrable μ) (hg.integrable μ)

lemma BM.integral_sub {f g : Y → ℝ} (hf : BM f) (hg : BM g) (μ : Measure Y) [IsFiniteMeasure μ] :
    ∫ y, (f y - g y) ∂μ = ∫ y, f y ∂μ - ∫ y, g y ∂μ :=
  MeasureTheory.integral_sub (hf.integrable μ) (hg.integrable μ)

lemma BM.sum {ι : Type*} (t : Finset ι) {f : ι → Y → ℝ} (hf : ∀ i ∈ t, BM (f i)) :
    BM fun y => ∑ i ∈ t, f i y := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using BM.const (0 : ℝ)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma BM.of_mem {f : Y → ℝ} (hf : Measurable f) {a b : ℝ} (h : ∀ y, f y ∈ Icc a b) : BM f :=
  ⟨hf, max |a| |b|, fun y => abs_le_max_abs_abs (h y).1 (h y).2⟩

/-- The Cauchy--Schwarz inequality for bounded measurable functions. -/
theorem sq_integral_mul_le {μ : Measure Y} [IsProbabilityMeasure μ] {f g : Y → ℝ} (hf : BM f) (hg : BM g) :
    (∫ y, f y * g y ∂μ) ^ 2 ≤ (∫ y, f y ^ 2 ∂μ) * ∫ y, g y ^ 2 ∂μ := by
  have hff := (hf.pow 2).integrable μ
  have hgg := (hg.pow 2).integrable μ
  have hfg := (hf.mul hg).integrable μ
  have key : ∀ t : ℝ, 0 ≤ (∫ y, f y ^ 2 ∂μ) * (t * t) + (2 * ∫ y, f y * g y ∂μ) * t + ∫ y, g y ^ 2 ∂μ := by
    intro t
    have h0 : 0 ≤ ∫ y, (t * f y + g y) ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
    have e : ∫ y, (t * f y + g y) ^ 2 ∂μ
        = ∫ y, ((t * t) * f y ^ 2 + (2 * t) * (f y * g y) + g y ^ 2) ∂μ :=
      integral_congr_ae (ae_of_all _ fun y => by ring)
    have b1 : BM fun y => (t * t) * f y ^ 2 := (BM.const _).mul (hf.pow 2)
    have b2 : BM fun y => (2 * t) * (f y * g y) := (BM.const _).mul (hf.mul hg)
    rw [e, (b1.add b2).integral_add (hg.pow 2) μ, b1.integral_add b2 μ, integral_const_mul,
      integral_const_mul] at h0
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

end Bounded

variable {X : Type*} [MeasurableSpace X]

/-! ### Densities -/

/-- A measure sandwiched between multiples of `P` has a density between these multiples. -/
theorem exists_density {P Q : Measure X} [IsFiniteMeasure P] [IsFiniteMeasure Q] {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hlo : ∀ S, MeasurableSet S → a * P.real S ≤ Q.real S)
    (hhi : ∀ S, MeasurableSet S → Q.real S ≤ b * P.real S) :
    ∃ r : X → ℝ, Measurable r ∧ (∀ x, r x ∈ Icc a b) ∧
      Q = P.withDensity fun x => ENNReal.ofReal (r x) := by
  have hb : 0 ≤ b := ha.trans hab
  have hloE : ∀ S, MeasurableSet S → ENNReal.ofReal a * P S ≤ Q S := fun S hS => by
    rw [← ofReal_measureReal (μ := P) (s := S), ← ofReal_measureReal (μ := Q) (s := S),
      ← ENNReal.ofReal_mul ha]
    exact ENNReal.ofReal_le_ofReal (hlo S hS)
  have hhiE : ∀ S, MeasurableSet S → Q S ≤ ENNReal.ofReal b * P S := fun S hS => by
    rw [← ofReal_measureReal (μ := P) (s := S), ← ofReal_measureReal (μ := Q) (s := S),
      ← ENNReal.ofReal_mul hb]
    exact ENNReal.ofReal_le_ofReal (hhi S hS)
  have hac : Q ≪ P := Measure.AbsolutelyContinuous.mk fun S hS hP0 => by
    have := hhiE S hS
    rw [hP0, mul_zero] at this
    exact le_zero_iff.1 this
  set g := Q.rnDeriv P with hg
  have hgm : Measurable g := Measure.measurable_rnDeriv Q P
  have hset : ∀ S, MeasurableSet S → ∫⁻ x in S, g x ∂P = Q S := fun S _ =>
    Measure.setLIntegral_rnDeriv hac S
  have hgle : ∀ᵐ x ∂P, g x ≤ ENNReal.ofReal b := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hgm fun S hS _ => ?_
    rw [hset S hS, setLIntegral_const]
    exact hhiE S hS
  have hgge : ∀ᵐ x ∂P, ENNReal.ofReal a ≤ g x := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const fun S hS _ => ?_
    rw [hset S hS, setLIntegral_const]
    exact hloE S hS
  let r : X → ℝ := fun x => max a (min b (g x).toReal)
  have hrm : Measurable r :=
    measurable_const.max (measurable_const.min hgm.ennreal_toReal)
  refine ⟨r, hrm, fun x => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩, ?_⟩
  have hae : (fun x => ENNReal.ofReal (r x)) =ᵐ[P] g := by
    filter_upwards [hgle, hgge] with x h1 h2
    have hfin : g x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
    have h3 : (g x).toReal ≤ b := ENNReal.toReal_le_of_le_ofReal hb h1
    have h4 : a ≤ (g x).toReal := by
      rw [← ENNReal.toReal_ofReal ha]
      exact ENNReal.toReal_mono hfin h2
    have : r x = (g x).toReal := by
      simp only [r]
      rw [min_eq_right h3, max_eq_right h4]
    rw [this, ENNReal.ofReal_toReal hfin]
  rw [withDensity_congr_ae hae, hg, Measure.withDensity_rnDeriv_eq Q P hac]

/-! ### Products of tilted measures -/

lemma setIntegral_density {μ ν : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ} (hf : BM f)
    (h0 : ∀ x, 0 ≤ f x) (hν : ν = μ.withDensity fun x => ENNReal.ofReal (f x)) {S : Set X}
    (hS : MeasurableSet S) : ν S = ENNReal.ofReal (∫ x, S.indicator f x ∂μ) := by
  have hint : Integrable (S.indicator f) μ := (hf.integrable μ).indicator hS
  have hnn : 0 ≤ᵐ[μ] S.indicator f :=
    ae_of_all _ fun x => indicator_nonneg (fun y _ => h0 y) x
  rw [hν, withDensity_apply _ hS, ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← lintegral_indicator hS]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ S <;> simp [hx]

/-- The product of tilted measures is the product measure tilted by the product density. -/
theorem pi_withDensity {n : ℕ} (μ ν : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (f : Fin n → X → ℝ) (hf : ∀ i, BM (f i)) (h0 : ∀ i x, 0 ≤ f i x)
    (hν : ∀ i, ν i = (μ i).withDensity fun x => ENNReal.ofReal (f i x)) :
    Measure.pi ν = (Measure.pi μ).withDensity fun y => ENNReal.ofReal (∏ i, f i (y i)) := by
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.pi univ s) := MeasurableSet.univ_pi hs
  have hprod : ∀ y : Fin n → X,
      (Set.pi univ s).indicator (fun y => ∏ i, f i (y i)) y = ∏ i, (s i).indicator (f i) (y i) := by
    intro y
    by_cases hy : y ∈ Set.pi univ s
    · rw [indicator_of_mem hy]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [indicator_of_mem (hy i (mem_univ i))]
    · rw [indicator_of_notMem hy]
      simp only [Set.mem_pi, mem_univ, forall_const, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  have hBM : BM fun y : Fin n → X => ∏ i, (s i).indicator (f i) (y i) := by
    refine BM.of_mem (a := 0) (b := ∏ i, (max |0| (Classical.choose (hf i).2))) ?_ fun y => ?_
    · refine Finset.measurable_prod _ fun i _ => ?_
      exact ((hf i).1.indicator (hs i)).comp (measurable_pi_apply i)
    · constructor
      · exact Finset.prod_nonneg fun i _ => indicator_nonneg (fun x _ => h0 i x) _
      · refine Finset.prod_le_prod₀ (fun i _ => indicator_nonneg (fun x _ => h0 i x) _) fun i _ => ?_
        by_cases hx : y i ∈ s i
        · rw [indicator_of_mem hx]
          exact (le_abs_self _).trans ((Classical.choose_spec (hf i).2 (y i)).trans (le_max_right _ _))
        · rw [indicator_of_notMem hx]
          exact le_max_of_le_left (abs_nonneg _)
  have hL : ∫⁻ y in Set.pi univ s, ENNReal.ofReal (∏ i, f i (y i)) ∂(Measure.pi μ)
      = ENNReal.ofReal (∫ y, ∏ i, (s i).indicator (f i) (y i) ∂(Measure.pi μ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hBM.integrable _) (ae_of_all _ fun y =>
      Finset.prod_nonneg fun i _ => indicator_nonneg (fun x _ => h0 i x) _),
      ← lintegral_indicator hbox]
    refine lintegral_congr fun y => ?_
    rw [← hprod y]
    by_cases hy : y ∈ Set.pi univ s <;> simp [hy]
  rw [withDensity_apply _ hbox, hL, integral_fintype_prod_eq_prod (𝕜 := ℝ),
    ENNReal.ofReal_prod_of_nonneg fun i _ =>
      integral_nonneg fun x => indicator_nonneg (fun y _ => h0 i y) x]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (setIntegral_density (hf i) (h0 i) (hν i) (hs i)).symm

/-- Integrals against a product of tilted measures. -/
theorem integral_pi_tilt {n : ℕ} (μ ν : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (f : Fin n → X → ℝ) (hf : ∀ i, BM (f i)) (h0 : ∀ i x, 0 ≤ f i x)
    (hν : ∀ i, ν i = (μ i).withDensity fun x => ENNReal.ofReal (f i x)) (V : (Fin n → X) → ℝ) :
    ∫ y, V y ∂(Measure.pi ν) = ∫ y, (∏ i, f i (y i)) * V y ∂(Measure.pi μ) := by
  rw [pi_withDensity μ ν f hf h0 hν]
  have hm : Measurable fun y : Fin n → X => (∏ i, f i (y i)).toNNReal :=
    (Finset.measurable_prod _ fun i _ => (hf i).1.comp (measurable_pi_apply i)).real_toNNReal
  have h := integral_withDensity_eq_integral_smul (μ := Measure.pi μ) hm V
  have e : (fun y : Fin n → X => ENNReal.ofReal (∏ i, f i (y i)))
      = fun y => (((∏ i, f i (y i)).toNNReal : NNReal) : ℝ≥0∞) := rfl
  rw [e, h]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show (∏ i, f i (y i)).toNNReal • V y = _
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Finset.prod_nonneg fun i _ => h0 i _), smul_eq_mul]

lemma integral_density_eq_one {P Q : Measure X} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {r : X → ℝ} (hr : BM r) (h0 : ∀ x, 0 ≤ r x) (hQ : Q = P.withDensity fun x => ENNReal.ofReal (r x)) :
    ∫ x, r x ∂P = 1 := by
  have h := setIntegral_density hr h0 hQ (S := univ) MeasurableSet.univ
  simp only [measure_univ, indicator_univ] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (integral_nonneg h0)] at h2
  simpa using h2.symm

/-- The law of i.i.d. draws is invariant under permutations of the coordinates. -/
theorem map_perm {n : ℕ} (P : Measure X) [IsProbabilityMeasure P] (τ : Equiv.Perm (Fin n)) :
    (Measure.pi fun _ : Fin n => P).map (fun y => y ∘ τ) = Measure.pi fun _ : Fin n => P := by
  have hm : Measurable fun y : Fin n → X => y ∘ τ :=
    measurable_pi_iff.2 fun j => measurable_pi_apply (τ j)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun y : Fin n → X => y ∘ τ) ⁻¹' Set.pi univ s = Set.pi univ fun l => s (τ.symm l) := by
    ext y
    simp only [mem_preimage, Set.mem_pi, mem_univ, forall_const, Function.comp]
    constructor
    · intro h l
      have := h (τ.symm l)
      simpa using this
    · intro h j
      have := h (τ j)
      simpa using this
  rw [hpre, Measure.pi_pi]
  exact Equiv.prod_comp τ.symm fun j => P (s j)

lemma integral_perm {n : ℕ} (P : Measure X) [IsProbabilityMeasure P] (τ : Equiv.Perm (Fin n))
    {g : (Fin n → X) → ℝ} (hg : Measurable g) :
    ∫ y, g (y ∘ τ) ∂(Measure.pi fun _ : Fin n => P) = ∫ y, g y ∂(Measure.pi fun _ : Fin n => P) := by
  have hm : Measurable fun y : Fin n → X => y ∘ τ :=
    measurable_pi_iff.2 fun j => measurable_pi_apply (τ j)
  conv_rhs => rw [← map_perm P τ]
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]

/-! ### Replacing one draw (the anonymous reweighting argument) -/

/-- **Anonymous influence, abstractly.** If `Q` has a density `w ∈ [0, Λ]` with respect to `P`, then
replacing one of `n` i.i.d. draws from `P` by a draw from `Q` moves the mean of a symmetric function with
range `B` by at most `(B/2) √((Λ-1)/n)`.  This is the paper's argument: `U = E[V W]` with
`W = (1/n) Σ_j w(Y_j)`, `E[W] = 1`, `Var(W) ≤ (Λ-1)/n`, `Var(V) ≤ B²/4`, and Cauchy--Schwarz. -/
theorem anon_bound_of_density {n : ℕ} (hn : 0 < n) {P Q : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Λ : ℝ} {w : X → ℝ} (hwm : Measurable w) (hwI : ∀ x, w x ∈ Icc 0 Λ)
    (hQw : Q = P.withDensity fun x => ENNReal.ofReal (w x))
    {V : (Fin n → X) → ℝ} (hV : Measurable V) {a B : ℝ} (hVb : ∀ y, V y ∈ Icc a (a + B))
    (hsym : ∀ (τ : Equiv.Perm (Fin n)) y, V (y ∘ τ) = V y) (i : Fin n) :
    |∫ y, V y ∂(Measure.pi (Function.update (fun _ : Fin n => P) i Q))
        - ∫ y, V y ∂(Measure.pi fun _ : Fin n => P)| ≤ (B / 2) * √((Λ - 1) / n) := by
  have hw0 : ∀ x, 0 ≤ w x := fun x => (hwI x).1
  have hwB : BM w := BM.of_mem hwm hwI
  have hw1 : ∫ x, w x ∂P = 1 := integral_density_eq_one hwB hw0 hQw
  have hΛ1 : 1 ≤ Λ := by
    have := integral_mono (μ := P) (hwB.integrable P) (integrable_const Λ) fun x => (hwI x).2
    simpa [hw1] using this
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set π₀ := Measure.pi fun _ : Fin n => P with hπ₀
  obtain ⟨y₀⟩ : Nonempty (Fin n → X) := by
    have : Nonempty X := nonempty_of_isProbabilityMeasure P
    infer_instance
  have hB : 0 ≤ B := by linarith [(hVb y₀).1, (hVb y₀).2]
  -- the replaced draw
  have hνprob : ∀ j, IsProbabilityMeasure (Function.update (fun _ : Fin n => P) i Q j) := fun j => by
    by_cases h : j = i
    · rw [h, Function.update_self]
      infer_instance
    · rw [Function.update_of_ne h]
      infer_instance
  let f : Fin n → X → ℝ := fun j x => if j = i then w x else 1
  have hfB : ∀ j, BM (f j) := fun j => by
    by_cases h : j = i
    · simpa [f, h] using hwB
    · simpa [f, h] using BM.const (1 : ℝ)
  have hf0 : ∀ j x, 0 ≤ f j x := fun j x => by
    by_cases h : j = i
    · simpa [f, h] using hw0 x
    · simp [f, h]
  have hν : ∀ j, Function.update (fun _ : Fin n => P) i Q j
      = P.withDensity fun x => ENNReal.ofReal (f j x) := fun j => by
    by_cases h : j = i
    · subst h
      simpa [f] using hQw
    · simp [f, h]
  have hU : ∫ y, V y ∂(Measure.pi (Function.update (fun _ : Fin n => P) i Q))
      = ∫ y, w (y i) * V y ∂π₀ := by
    rw [integral_pi_tilt (fun _ => P) _ f hfB hf0 hν V]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [f]
    rw [Finset.prod_ite_eq' Finset.univ i (fun j => w (y j))]
    simp
  set U := ∫ y, w (y i) * V y ∂π₀ with hUdef
  -- symmetry
  have hwpi : ∀ j, BM fun y : Fin n → X => w (y j) := fun j =>
    BM.of_mem (hwm.comp (measurable_pi_apply j)) fun y => hwI (y j)
  have hVB : BM V := BM.of_mem hV hVb
  have hUj : ∀ j, ∫ y, w (y j) * V y ∂π₀ = U := fun j => by
    have h := integral_perm P (Equiv.swap i j) (g := fun y => w (y i) * V y)
      ((hwpi i).1.mul hV)
    rw [hUdef, ← h]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [Function.comp, Equiv.swap_apply_left, hsym]
  -- the average weight
  let W : (Fin n → X) → ℝ := fun y => (∑ j, w (y j)) / n
  have hWB : BM W := by
    have h1 : BM fun y : Fin n → X => ∑ j, w (y j) := by
      refine ⟨Finset.measurable_sum _ fun j _ => (hwpi j).1, ∑ j : Fin n, Λ, fun y => ?_⟩
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_of_nonneg (hw0 _)]
      exact (hwI _).2
    exact ⟨h1.1.div_const _, by
      obtain ⟨C, hC⟩ := h1.2
      exact ⟨C / n, fun y => by
        simp only [W]
        rw [abs_div, abs_of_pos hnr]
        exact div_le_div_of_nonneg_right (hC y) hnr.le⟩⟩
  have hUW : U = ∫ y, W y * V y ∂π₀ := by
    have h1 : ∫ y, W y * V y ∂π₀ = (∑ j, ∫ y, w (y j) * V y ∂π₀) / n := by
      rw [← integral_finsetSum _ fun j _ => ((hwpi j).mul hVB).integrable π₀, ← integral_div]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [W]
      rw [div_mul_eq_mul_div, Finset.sum_mul]
    rw [h1]
    simp only [hUj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- first and second moments of the weights
  have hprod2 : ∀ (j l : Fin n), ∫ y, w (y j) * w (y l) ∂π₀
      = if j = l then ∫ x, w x ^ 2 ∂P else 1 := by
    intro j l
    let h : Fin n → X → ℝ := fun t x => (if t = j then w x else 1) * (if t = l then w x else 1)
    have e : ∀ y : Fin n → X, w (y j) * w (y l) = ∏ t, h t (y t) := fun y => by
      simp only [h]
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j (fun t => w (y t)),
        Finset.prod_ite_eq' Finset.univ l (fun t => w (y t))]
      simp
    have e2 : ∫ y, w (y j) * w (y l) ∂π₀ = ∏ t, ∫ x, h t x ∂P := by
      simp_rw [e]
      exact integral_fintype_prod_eq_prod (𝕜 := ℝ) h
    rw [e2]
    by_cases hjl : j = l
    · subst hjl
      rw [ite_eq_left rfl]
      have : ∀ t, ∫ x, h t x ∂P = if t = j then ∫ x, w x ^ 2 ∂P else 1 := fun t => by
        by_cases ht : t = j
        · simp only [h, ht, ite_true, ← pow_two]
        · simp [h, ht]
      simp_rw [this]
      rw [Finset.prod_ite_eq' Finset.univ j (fun _ => ∫ x, w x ^ 2 ∂P)]
      simp
    · rw [ite_eq_right hjl]
      refine Finset.prod_eq_one fun t _ => ?_
      by_cases ht : t = j
      · have htl : t ≠ l := fun h' => hjl (ht.symm.trans h')
        simp [h, ht, hjl, hw1]
      · by_cases htl : t = l
        · simp [h, htl, Ne.symm hjl, hw1]
        · simp [h, ht, htl]
  have hprod1 : ∀ j, ∫ y, w (y j) ∂π₀ = 1 := fun j => by
    let h : Fin n → X → ℝ := fun t x => if t = j then w x else 1
    have e : ∀ y : Fin n → X, w (y j) = ∏ t, h t (y t) := fun y => by
      simp only [h]
      rw [Finset.prod_ite_eq' Finset.univ j (fun t => w (y t))]
      simp
    have e2 : ∫ y, w (y j) ∂π₀ = ∏ t, ∫ x, h t x ∂P := by
      simp_rw [e]
      exact integral_fintype_prod_eq_prod (𝕜 := ℝ) h
    rw [e2]
    refine Finset.prod_eq_one fun t _ => ?_
    by_cases ht : t = j <;> simp [h, ht, hw1]
  set m := ∫ x, w x ^ 2 ∂P with hm
  have hmle : m ≤ Λ := by
    have h1 : ∫ x, w x ^ 2 ∂P ≤ ∫ x, Λ * w x ∂P :=
      integral_mono ((hwB.pow 2).integrable P) ((hwB.integrable P).const_mul Λ) fun x => by
        simp only
        have := hwI x
        nlinarith [this.1, this.2]
    rw [integral_const_mul, hw1, mul_one] at h1
    exact h1
  have hW1 : ∫ y, W y ∂π₀ = 1 := by
    simp only [W]
    rw [integral_div, integral_finsetSum _ fun j _ => (hwpi j).integrable π₀]
    simp only [hprod1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  have hW2 : ∫ y, W y ^ 2 ∂π₀ = 1 + (m - 1) / n := by
    have e : ∀ y : Fin n → X, W y ^ 2 = (∑ j, ∑ l, w (y j) * w (y l)) / (n : ℝ) ^ 2 := fun y => by
      simp only [W]
      rw [div_pow, pow_two (∑ j, w (y j)), Finset.sum_mul_sum]
    simp_rw [e]
    rw [integral_div, integral_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun l _ => ((hwpi j).mul (hwpi l)).integrable π₀]
    have h1 : ∀ j : Fin n, ∫ y, ∑ l, w (y j) * w (y l) ∂π₀ = (n : ℝ) + (m - 1) := fun j => by
      rw [integral_finsetSum _ fun l _ => ((hwpi j).mul (hwpi l)).integrable π₀]
      simp only [hprod2]
      have : ∀ l : Fin n, (if j = l then m else 1) = 1 + (if j = l then m - 1 else 0) := fun l => by
        split_ifs <;> ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- the covariance
  set c := a + B / 2 with hc
  have hVc : BM fun y => V y - c := hVB.sub (BM.const c)
  have hWm : BM fun y => W y - 1 := hWB.sub (BM.const 1)
  have hcov : U - ∫ y, V y ∂π₀ = ∫ y, (W y - 1) * (V y - c) ∂π₀ := by
    have e : ∀ y, (W y - 1) * (V y - c) = W y * V y - V y - c * (W y - 1) := fun y => by ring
    simp_rw [e]
    have b1 : BM fun y => W y * V y := hWB.mul hVB
    have b2 : BM fun y => c * (W y - 1) := (BM.const c).mul hWm
    rw [(b1.sub hVB).integral_sub b2 π₀, b1.integral_sub hVB π₀, ← hUW, integral_const_mul,
      hWB.integral_sub (BM.const 1) π₀, hW1]
    simp
  have hvarW : ∫ y, (W y - 1) ^ 2 ∂π₀ = (m - 1) / n := by
    have e : ∀ y, (W y - 1) ^ 2 = W y ^ 2 - 2 * W y + 1 := fun y => by ring
    simp_rw [e]
    have b1 : BM fun y => W y ^ 2 := hWB.pow 2
    have b2 : BM fun y => 2 * W y := (BM.const 2).mul hWB
    rw [(b1.sub b2).integral_add (BM.const 1) π₀, b1.integral_sub b2 π₀, hW2, integral_const_mul, hW1]
    simp
    ring
  have hvarV : ∫ y, (V y - c) ^ 2 ∂π₀ ≤ (B / 2) ^ 2 := by
    have h1 : ∫ y, (V y - c) ^ 2 ∂π₀ ≤ ∫ _, (B / 2) ^ 2 ∂π₀ :=
      integral_mono ((hVc.pow 2).integrable π₀) (integrable_const _) fun y => by
        simp only
        have h2 := hVb y
        have h3 : |V y - c| ≤ B / 2 := by
          rw [abs_le]
          constructor <;> linarith [h2.1, h2.2]
        exact sq_le_sq' (abs_le.1 h3).1 (abs_le.1 h3).2
    simpa using h1
  have hCS := sq_integral_mul_le (μ := π₀) hWm hVc
  rw [hvarW] at hCS
  have hm1 : 0 ≤ (m - 1) / n := by
    rw [← hvarW]
    exact integral_nonneg fun y => sq_nonneg _
  have hfinal : (∫ y, (W y - 1) * (V y - c) ∂π₀) ^ 2 ≤ ((B / 2) * √((Λ - 1) / n)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by
      apply div_nonneg (by linarith) hnr.le)]
    have h2 : (m - 1) / n ≤ (Λ - 1) / n := div_le_div_of_nonneg_right (by linarith) hnr.le
    calc _ ≤ (m - 1) / n * ∫ y, (V y - c) ^ 2 ∂π₀ := hCS
      _ ≤ (m - 1) / n * (B / 2) ^ 2 := mul_le_mul_of_nonneg_left hvarV hm1
      _ ≤ (Λ - 1) / n * (B / 2) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = _ := by ring
  rw [hU, hcov]
  have hpos : 0 ≤ (B / 2) * √((Λ - 1) / n) := by positivity
  exact abs_le_of_sq_le_sq hfinal hpos

/-- **Anonymous influence, from domination.** If `Q ≤ Λ P`, the density of `Q` with respect to `P` lies in
`[0, Λ]`, so the conclusion of `anon_bound_of_density` holds. -/
theorem anon_bound {n : ℕ} (hn : 0 < n) {P Q : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Λ : ℝ} (hQ : ∀ S, MeasurableSet S → Q.real S ≤ Λ * P.real S)
    {V : (Fin n → X) → ℝ} (hV : Measurable V) {a B : ℝ} (hVb : ∀ y, V y ∈ Icc a (a + B))
    (hsym : ∀ (τ : Equiv.Perm (Fin n)) y, V (y ∘ τ) = V y) (i : Fin n) :
    |∫ y, V y ∂(Measure.pi (Function.update (fun _ : Fin n => P) i Q))
        - ∫ y, V y ∂(Measure.pi fun _ : Fin n => P)| ≤ (B / 2) * √((Λ - 1) / n) := by
  have hΛ1 : 1 ≤ Λ := by
    have := hQ univ MeasurableSet.univ
    simpa using this
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨w, hwm, hwI, hQw⟩ := exists_density (P := P) (Q := Q) (a := 0) le_rfl hΛ0
    (fun S _ => by simp) hQ
  exact anon_bound_of_density hn hwm hwI hQw hV hVb hsym i

/-! ### Comparing `Pⁿ` and `(P⁰)ⁿ` -/

/-- `P` has density `r ∈ [1-c, 1+c]` with respect to `P⁰`. -/
structure IsTilt (P₀ P : Measure X) (r : X → ℝ) (c : ℝ) : Prop where
  meas : Measurable r
  mem : ∀ x, r x ∈ Icc (1 - c) (1 + c)
  c0 : 0 ≤ c
  c1 : c ≤ 1
  eq : P = P₀.withDensity fun x => ENNReal.ofReal (r x)

namespace IsTilt

variable {P₀ P : Measure X} [IsProbabilityMeasure P₀] [IsProbabilityMeasure P] {r : X → ℝ} {c : ℝ}

lemma r_nonneg (h : IsTilt P₀ P r c) (x : X) : 0 ≤ r x := by
  have := (h.mem x).1
  have := h.c1
  linarith

lemma bm (h : IsTilt P₀ P r c) : BM r := BM.of_mem h.meas h.mem

lemma integral_r (h : IsTilt P₀ P r c) : ∫ x, r x ∂P₀ = 1 :=
  integral_density_eq_one h.bm h.r_nonneg h.eq

lemma integral_sq_sub_le (h : IsTilt P₀ P r c) : ∫ x, (r x - 1) ^ 2 ∂P₀ ≤ c ^ 2 := by
  have hb := (h.bm.sub (BM.const 1)).pow 2
  have h1 : ∫ x, (r x - 1) ^ 2 ∂P₀ ≤ ∫ _, c ^ 2 ∂P₀ :=
    integral_mono (hb.integrable P₀) (integrable_const _) fun x => by
      simp only
      have h2 := h.mem x
      exact sq_le_sq' (by linarith [h2.1]) (by linarith [h2.2])
  simpa using h1

lemma integral_sq_le (h : IsTilt P₀ P r c) : ∫ x, r x ^ 2 ∂P₀ ≤ 1 + c ^ 2 := by
  have hb := h.bm
  have e : ∫ x, r x ^ 2 ∂P₀ = ∫ x, (r x - 1) ^ 2 ∂P₀ + (2 * ∫ x, r x ∂P₀ - 1) := by
    have : ∀ x, r x ^ 2 = (r x - 1) ^ 2 + (2 * r x - 1) := fun x => by ring
    simp_rw [this]
    have b1 : BM fun x => (r x - 1) ^ 2 := (hb.sub (BM.const 1)).pow 2
    have b2 : BM fun x => 2 * r x := (BM.const 2).mul hb
    rw [b1.integral_add (b2.sub (BM.const 1)) P₀, b2.integral_sub (BM.const 1) P₀, integral_const_mul]
    simp
  rw [e, h.integral_r]
  linarith [h.integral_sq_sub_le]

/-- The likelihood ratio `L(y) = ∏ r(y_i)`. -/
noncomputable def L (r : X → ℝ) {n : ℕ} (y : Fin n → X) : ℝ := ∏ i, r (y i)

lemma L_nonneg (h : IsTilt P₀ P r c) {n : ℕ} (y : Fin n → X) : 0 ≤ L r y :=
  Finset.prod_nonneg fun _ _ => h.r_nonneg _

lemma bm_L (h : IsTilt P₀ P r c) (n : ℕ) : BM (L r (n := n)) := by
  refine BM.of_mem (a := 0) (b := (1 + c) ^ n) ?_ fun y => ⟨h.L_nonneg y, ?_⟩
  · exact Finset.measurable_prod _ fun i _ => h.meas.comp (measurable_pi_apply i)
  · unfold L
    calc ∏ i, r (y i) ≤ ∏ _i : Fin n, (1 + c) :=
          Finset.prod_le_prod₀ (fun i _ => h.r_nonneg _) fun i _ => (h.mem _).2
      _ = (1 + c) ^ n := by simp

lemma integral_eq_L (h : IsTilt P₀ P r c) {n : ℕ} (V : (Fin n → X) → ℝ) :
    ∫ y, V y ∂(Measure.pi fun _ : Fin n => P) = ∫ y, L r y * V y ∂(Measure.pi fun _ : Fin n => P₀) :=
  integral_pi_tilt (fun _ => P₀) (fun _ => P) (fun _ => r) (fun _ => h.bm) (fun _ => h.r_nonneg)
    (fun _ => h.eq) V

lemma integral_L (h : IsTilt P₀ P r c) (n : ℕ) :
    ∫ y, L r y ∂(Measure.pi fun _ : Fin n => P₀) = 1 := by
  unfold L
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) fun _ => r]
  simp [h.integral_r]

lemma integral_L_sq_le (h : IsTilt P₀ P r c) (n : ℕ) :
    ∫ y, L r y ^ 2 ∂(Measure.pi fun _ : Fin n => P₀) ≤ exp ((n : ℝ) * c ^ 2) := by
  have e : ∀ y : Fin n → X, L r y ^ 2 = ∏ i, r (y i) ^ 2 := fun y => by
    unfold L
    rw [Finset.prod_pow]
  simp_rw [e]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) fun _ x => r x ^ 2]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : ∫ x, r x ^ 2 ∂P₀ ≤ exp (c ^ 2) := h.integral_sq_le.trans (by
    have := Real.add_one_le_exp (c ^ 2)
    linarith)
  have h0 : 0 ≤ ∫ x, r x ^ 2 ∂P₀ := integral_nonneg fun x => sq_nonneg _
  calc (∫ x, r x ^ 2 ∂P₀) ^ n ≤ exp (c ^ 2) ^ n := pow_le_pow_left₀ h0 h1 n
    _ = exp ((n : ℝ) * c ^ 2) := by rw [← Real.exp_nat_mul]

/-- The second-moment bound: `E⁰[(L-1)²] ≤ e^{n c²} - 1`, hence the comparison of the expectations. -/
theorem abs_sub_le (h : IsTilt P₀ P r c) {n : ℕ} {Z : (Fin n → X) → ℝ} (hZ : Measurable Z) {B : ℝ}
    (hZb : ∀ y, Z y ∈ Icc 0 B) :
    |∫ y, Z y ∂(Measure.pi fun _ : Fin n => P) - ∫ y, Z y ∂(Measure.pi fun _ : Fin n => P₀)|
      ≤ B * √(exp ((n : ℝ) * c ^ 2) - 1) := by
  set π₀ := Measure.pi fun _ : Fin n => P₀ with hπ₀
  have hLB := h.bm_L n
  have hZB : BM Z := BM.of_mem hZ hZb
  have : Nonempty X := nonempty_of_isProbabilityMeasure P₀
  have hB0 : 0 ≤ B := (hZb (Classical.arbitrary _)).1.trans (hZb (Classical.arbitrary _)).2
  have hdiff : ∫ y, Z y ∂(Measure.pi fun _ : Fin n => P) - ∫ y, Z y ∂π₀
      = ∫ y, (L r y - 1) * Z y ∂π₀ := by
    rw [h.integral_eq_L Z, ← (hLB.mul hZB).integral_sub hZB π₀]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  have hvar : ∫ y, (L r y - 1) ^ 2 ∂π₀ ≤ exp ((n : ℝ) * c ^ 2) - 1 := by
    have e : ∀ y : Fin n → X, (L r y - 1) ^ 2 = L r y ^ 2 - 2 * L r y + 1 := fun y => by ring
    simp_rw [e]
    have b1 : BM fun y : Fin n → X => L r y ^ 2 := hLB.pow 2
    have b2 : BM fun y : Fin n → X => 2 * L r y := (BM.const 2).mul hLB
    rw [(b1.sub b2).integral_add (BM.const 1) π₀, b1.integral_sub b2 π₀,
      integral_const_mul, h.integral_L]
    have := h.integral_L_sq_le n
    have hu : π₀.real univ = 1 := probReal_univ
    simp only [integral_const, hu, smul_eq_mul, mul_one]
    linarith
  have hZ2 : ∫ y, Z y ^ 2 ∂π₀ ≤ B ^ 2 := by
    have h1 : ∫ y, Z y ^ 2 ∂π₀ ≤ ∫ _, B ^ 2 ∂π₀ :=
      integral_mono ((hZB.pow 2).integrable π₀) (integrable_const _) fun y =>
        pow_le_pow_left₀ (hZb y).1 (hZb y).2 2
    simpa using h1
  have hCS := sq_integral_mul_le (μ := π₀) (hLB.sub (BM.const 1)) hZB
  have hv0 : 0 ≤ ∫ y, (L r y - 1) ^ 2 ∂π₀ := integral_nonneg fun y => sq_nonneg _
  have hE0 : 0 ≤ exp ((n : ℝ) * c ^ 2) - 1 := hv0.trans hvar
  rw [hdiff]
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, Real.sq_sqrt hE0]
  calc _ ≤ (∫ y, (L r y - 1) ^ 2 ∂π₀) * ∫ y, Z y ^ 2 ∂π₀ := hCS
    _ ≤ (exp ((n : ℝ) * c ^ 2) - 1) * B ^ 2 :=
      mul_le_mul hvar hZ2 (integral_nonneg fun y => sq_nonneg _) hE0
    _ = _ := by ring

lemma r_inv_le (h : IsTilt P₀ P r c) (hc : c ≤ 1 / 2) (x : X) :
    (r x)⁻¹ ≤ 1 - (r x - 1) + 2 * (r x - 1) ^ 2 := by
  have h1 := h.mem x
  have hpos : 0 < r x := by linarith [h1.1]
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  have h2 : 1 / 2 ≤ r x := by linarith [h1.1]
  nlinarith [sq_nonneg (r x - 1), mul_nonneg (sq_nonneg (r x - 1)) (by linarith : 0 ≤ 2 * r x - 1)]

lemma bm_inv (h : IsTilt P₀ P r c) (hc : c ≤ 1 / 2) : BM fun x => (r x)⁻¹ := by
  refine BM.of_mem (a := 0) (b := 2) h.meas.inv fun x => ?_
  have h1 := h.mem x
  have hpos : 1 / 2 ≤ r x := by linarith [h1.1]
  refine ⟨inv_nonneg.2 (by linarith), ?_⟩
  rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
  linarith

lemma integral_inv_le (h : IsTilt P₀ P r c) (hc : c ≤ 1 / 2) :
    ∫ x, (r x)⁻¹ ∂P₀ ≤ 1 + 2 * c ^ 2 := by
  have hb := h.bm
  have hbs := (hb.sub (BM.const 1))
  have h1 : ∫ x, (r x)⁻¹ ∂P₀ ≤ ∫ x, (1 - (r x - 1) + 2 * (r x - 1) ^ 2) ∂P₀ :=
    integral_mono ((h.bm_inv hc).integrable P₀)
      ((((BM.const (1 : ℝ)).sub hbs).add ((BM.const (2 : ℝ)).mul (hbs.pow 2))).integrable P₀)
      fun x => h.r_inv_le hc x
  have h2 : ∫ x, (1 - (r x - 1) + 2 * (r x - 1) ^ 2) ∂P₀
      = 1 - (∫ x, r x ∂P₀ - 1) + 2 * ∫ x, (r x - 1) ^ 2 ∂P₀ := by
    have b1 : BM fun x => (1 : ℝ) - (r x - 1) := (BM.const (1 : ℝ)).sub hbs
    have b2 : BM fun x => 2 * (r x - 1) ^ 2 := (BM.const (2 : ℝ)).mul (hbs.pow 2)
    rw [b1.integral_add b2 P₀, (BM.const (1 : ℝ)).integral_sub hbs P₀,
      hb.integral_sub (BM.const 1) P₀, integral_const_mul]
    simp
  rw [h2, h.integral_r] at h1
  linarith [h.integral_sq_sub_le]

/-- The inverse-moment bound and Cauchy--Schwarz: `(R⁰)² ≤ B e^{2 n c²} R`. -/
theorem sq_le (h : IsTilt P₀ P r c) (hc : c ≤ 1 / 2) {n : ℕ} {Z : (Fin n → X) → ℝ} (hZ : Measurable Z)
    {B : ℝ} (hZb : ∀ y, Z y ∈ Icc 0 B) :
    (∫ y, Z y ∂(Measure.pi fun _ : Fin n => P₀)) ^ 2
      ≤ B * exp (2 * (n : ℝ) * c ^ 2) * ∫ y, Z y ∂(Measure.pi fun _ : Fin n => P) := by
  set π₀ := Measure.pi fun _ : Fin n => P₀ with hπ₀
  have hLB := h.bm_L n
  have hZB : BM Z := BM.of_mem hZ hZb
  have : Nonempty X := nonempty_of_isProbabilityMeasure P₀
  have hB0 : 0 ≤ B := (hZb (Classical.arbitrary _)).1.trans (hZb (Classical.arbitrary _)).2
  have hLpos : ∀ y : Fin n → X, 0 < L r y := fun y =>
    Finset.prod_pos fun i _ => by
      have := (h.mem (y i)).1
      linarith
  have hLinv : BM fun y : Fin n → X => ∏ i, (r (y i))⁻¹ := by
    refine BM.of_mem (a := 0) (b := 2 ^ n) ?_ fun y => ?_
    · exact Finset.measurable_prod _ fun i _ => (h.meas.comp (measurable_pi_apply i)).inv
    · have hb : ∀ i, (r (y i))⁻¹ ∈ Icc (0 : ℝ) 2 := fun i => by
        have h1 := h.mem (y i)
        have hpos : 1 / 2 ≤ r (y i) := by linarith [h1.1]
        refine ⟨inv_nonneg.2 (by linarith), ?_⟩
        rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
        linarith
      refine ⟨Finset.prod_nonneg fun i _ => (hb i).1, ?_⟩
      calc ∏ i, (r (y i))⁻¹ ≤ ∏ _i : Fin n, (2 : ℝ) :=
            Finset.prod_le_prod₀ (fun i _ => (hb i).1) fun i _ => (hb i).2
        _ = 2 ^ n := by simp
  have hinv_eq : ∀ y : Fin n → X, (L r y)⁻¹ = ∏ i, (r (y i))⁻¹ := fun y => by
    unfold L
    rw [Finset.prod_inv_distrib]
  -- `E⁰[1/L] ≤ e^{2 n c²}`
  have hE : ∫ y, ∏ i, (r (y i))⁻¹ ∂π₀ ≤ exp (2 * (n : ℝ) * c ^ 2) := by
    rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) fun _ x => (r x)⁻¹]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h1 : ∫ x, (r x)⁻¹ ∂P₀ ≤ exp (2 * c ^ 2) := (h.integral_inv_le hc).trans (by
      have := Real.add_one_le_exp (2 * c ^ 2)
      linarith)
    have h0 : 0 ≤ ∫ x, (r x)⁻¹ ∂P₀ := integral_nonneg fun x => (h.bm_inv hc |>.1 |> fun _ => by
      have h2 := (h.mem x).1
      exact inv_nonneg.2 (by linarith))
    calc (∫ x, (r x)⁻¹ ∂P₀) ^ n ≤ exp (2 * c ^ 2) ^ n := pow_le_pow_left₀ h0 h1 n
      _ = exp (2 * (n : ℝ) * c ^ 2) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  -- Cauchy--Schwarz with `√(Z L)` and `√(Z/L)`
  let A : (Fin n → X) → ℝ := fun y => √(Z y * L r y)
  let C : (Fin n → X) → ℝ := fun y => √(Z y * ∏ i, (r (y i))⁻¹)
  have hAsq : ∀ y, A y ^ 2 = Z y * L r y := fun y =>
    Real.sq_sqrt (mul_nonneg (hZb y).1 (h.L_nonneg y))
  have hinv0 : ∀ y : Fin n → X, 0 ≤ ∏ i, (r (y i))⁻¹ := fun y => by
    rw [← hinv_eq]
    exact (inv_pos.2 (hLpos y)).le
  have hCsq : ∀ y, C y ^ 2 = Z y * ∏ i, (r (y i))⁻¹ := fun y =>
    Real.sq_sqrt (mul_nonneg (hZb y).1 (hinv0 y))
  have hAC : ∀ y, A y * C y = Z y := fun y => by
    simp only [A, C]
    rw [← Real.sqrt_mul (mul_nonneg (hZb y).1 (h.L_nonneg y)), ← hinv_eq]
    have hne := (hLpos y).ne'
    have : Z y * L r y * (Z y * (L r y)⁻¹) = Z y ^ 2 := by
      field_simp
    rw [this, Real.sqrt_sq (hZb y).1]
  have hAB : BM A := by
    obtain ⟨CC, hCC⟩ := (hZB.mul hLB).2
    refine ⟨(hZB.mul hLB).1.sqrt, √|CC|, fun y => ?_⟩
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans ((hCC y).trans (le_abs_self _)))
  have hCB : BM C := by
    obtain ⟨CC, hCC⟩ := (hZB.mul hLinv).2
    refine ⟨(hZB.mul hLinv).1.sqrt, √|CC|, fun y => ?_⟩
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans ((hCC y).trans (le_abs_self _)))
  have hCS := sq_integral_mul_le (μ := π₀) hAB hCB
  simp_rw [hAC, hAsq, hCsq] at hCS
  have hR : ∫ y, Z y * L r y ∂π₀ = ∫ y, Z y ∂(Measure.pi fun _ : Fin n => P) := by
    rw [h.integral_eq_L Z]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  have hRnn : 0 ≤ ∫ y, Z y ∂(Measure.pi fun _ : Fin n => P) := integral_nonneg fun y => (hZb y).1
  have hsecond : ∫ y, Z y * ∏ i, (r (y i))⁻¹ ∂π₀ ≤ B * exp (2 * (n : ℝ) * c ^ 2) := by
    have h1 : ∫ y, Z y * ∏ i, (r (y i))⁻¹ ∂π₀ ≤ ∫ y, B * ∏ i, (r (y i))⁻¹ ∂π₀ :=
      integral_mono ((hZB.mul hLinv).integrable π₀) ((hLinv.integrable π₀).const_mul B) fun y =>
        mul_le_mul_of_nonneg_right (hZb y).2 (hinv0 y)
    rw [integral_const_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hE hB0)
  rw [hR] at hCS
  calc _ ≤ _ := hCS
    _ ≤ (∫ y, Z y ∂(Measure.pi fun _ : Fin n => P)) * (B * exp (2 * (n : ℝ) * c ^ 2)) :=
      mul_le_mul_of_nonneg_left hsecond hRnn
    _ = _ := by ring

end IsTilt

end OA

end NoisyVD
