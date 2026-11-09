import ManagerialIntervention.Informal
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Concrete environments

Finite discrete distributions of `(v_a, v_p)` with quadratic (or cubic) costs.  They show
that the model's assumptions are satisfiable and that the hypotheses of the results can hold
simultaneously, and they supply the counterexamples in `MI.Counterexamples`.

| env  | support (prob.)                                  | `α_a` | `α_p` |
|------|--------------------------------------------------|-------|-------|
| `E1` | (3,-1) ½, (-2,3) ½                               | -3/2  | -3    |
| `E2` | (2,-1) ½, (-4,3) ¼, (2,3) ¼                      | -1    | -3/2  |
| `E3` | (2,2) ½, (-1,-1) ½    (`v_a = v_p`)              | 1     | 1     |
| `E5` | (-1,3) ¼, (-1,-1) ¼, (2,1) ½                     | 1/2   | -2    |
| `E6` | (1,-1) ¼, (-1,-1) ¼, (1,2) ½                     | 0     | 1/2   |

`E1` and `E2` share all primitives `(E v_a, E v_p, E(v_a 1_{v_a<0}), E(v_p 1_{v_p<0}), c_a, c_p)`.
-/

namespace MI

open MeasureTheory Set Filter Topology

/-- A finite discrete distribution with real weights `r i` on points `x i`. -/
noncomputable def discMeasure {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ × ℝ) : Measure (ℝ × ℝ) :=
  ∑ i, ENNReal.ofReal (r i) • Measure.dirac (x i)

lemma disc_integrable_each {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ × ℝ) (f : ℝ × ℝ → ℝ)
    (i : Fin n) : Integrable f (ENNReal.ofReal (r i) • Measure.dirac (x i)) :=
  (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

lemma disc_integrable {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ × ℝ) (f : ℝ × ℝ → ℝ) :
    Integrable f (discMeasure r x) :=
  integrable_finsetSum_measure.2 fun i _ => disc_integrable_each r x f i

lemma disc_integral {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ × ℝ) (hr : ∀ i, 0 ≤ r i)
    (f : ℝ × ℝ → ℝ) : ∫ v, f v ∂(discMeasure r x) = ∑ i, r i * f (x i) := by
  unfold discMeasure
  rw [integral_finsetSum_measure (fun i _ => disc_integrable_each r x f i)]
  congr 1
  funext i
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hr i), smul_eq_mul]

lemma disc_real {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ × ℝ) (hr : ∀ i, 0 ≤ r i)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    (discMeasure r x).real s = ∑ i, r i * s.indicator 1 (x i) := by
  rw [← integral_indicator_one hs, disc_integral r x hr]

lemma disc_ne_zero {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ × ℝ) (hr : ∀ i, 0 ≤ r i)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hpos : 0 < ∑ i, r i * s.indicator 1 (x i)) :
    discMeasure r x s ≠ 0 := by
  intro h
  have := disc_real r x hr hs
  rw [measureReal_def, h, ENNReal.toReal_zero] at this
  linarith

/-- An environment from a finite discrete distribution; the hypotheses are the paper's
assumptions written out for the discrete distribution. -/
noncomputable def mkEnv {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ × ℝ) (ca cp : Cost)
    (hr : ∀ i, 0 ≤ r i) (h1 : ∑ i, r i = 1)
    (hA : 0 < ∑ i, r i * (x i).1) (hP : 0 < ∑ i, r i * (x i).2)
    (hra : 0 < ∑ i, r i * {v : ℝ × ℝ | v.1 < 0}.indicator 1 (x i))
    (hrp : 0 < ∑ i, r i * {v : ℝ × ℝ | v.2 < 0}.indicator 1 (x i))
    (hca : ∑ i, r i * {v : ℝ × ℝ | 0 ≤ v.1}.indicator (fun v => v.1) (x i) ≤ ca.d 1)
    (hcp : -∑ i, r i * {v : ℝ × ℝ | v.2 < 0}.indicator (fun v => v.2) (x i) ≤ cp.d 1) : Env where
  F := discMeasure r x
  isProb := ⟨by
    have h := disc_real r x hr MeasurableSet.univ
    simp only [Set.indicator_univ, Pi.one_apply, mul_one, h1] at h
    exact (ENNReal.toReal_eq_one_iff _).1 h⟩
  int_a := disc_integrable r x _
  int_p := disc_integrable r x _
  Ea_pos := by rw [disc_integral r x hr]; exact hA
  Ep_pos := by rw [disc_integral r x hr]; exact hP
  rej := CanonicallyOrderedAdd.mul_pos.2
    ⟨pos_iff_ne_zero.2 (disc_ne_zero r x hr Env.mA hra),
      pos_iff_ne_zero.2 (disc_ne_zero r x hr Env.mP hrp)⟩
  ca := ca
  cp := cp
  ca_large := by rw [disc_integral r x hr]; exact hca
  cp_large := by rw [disc_integral r x hr]; exact hcp

section mkEnvLemmas

variable {n : ℕ} {r : Fin n → ℝ} {x : Fin n → ℝ × ℝ} {ca cp : Cost} {hr : ∀ i, 0 ≤ r i}
  {h1 : ∑ i, r i = 1} {hA : 0 < ∑ i, r i * (x i).1} {hP : 0 < ∑ i, r i * (x i).2}
  {hra : 0 < ∑ i, r i * {v : ℝ × ℝ | v.1 < 0}.indicator 1 (x i)}
  {hrp : 0 < ∑ i, r i * {v : ℝ × ℝ | v.2 < 0}.indicator 1 (x i)}
  {hca : ∑ i, r i * {v : ℝ × ℝ | 0 ≤ v.1}.indicator (fun v => v.1) (x i) ≤ ca.d 1}
  {hcp : -∑ i, r i * {v : ℝ × ℝ | v.2 < 0}.indicator (fun v => v.2) (x i) ≤ cp.d 1}

lemma mkEnv_integral (f : ℝ × ℝ → ℝ) :
    ∫ v, f v ∂(mkEnv r x ca cp hr h1 hA hP hra hrp hca hcp).F = ∑ i, r i * f (x i) :=
  disc_integral r x hr f

end mkEnvLemmas

/-! ### Costs -/

/-- `c_a(e) = e²` (so `c_a'(e) = 2e`). -/
noncomputable abbrev cq2 : Cost := Cost.quad 2 (by norm_num)
/-- `c_p(e) = e²/2` (so `c_p'(e) = e`). -/
noncomputable abbrev cq1 : Cost := Cost.quad 1 (by norm_num)

/-- The cubic cost `c(e) = e³/3`, with `c'(e) = e²` and `h = (c')⁻¹ = √·` strictly concave. -/
noncomputable def cube : Cost where
  c e := e ^ 3 / 3
  d e := e ^ 2
  hasDerivAt x := by
    have := (hasDerivAt_pow 3 x).div_const 3
    convert this using 1
    push_cast
    ring
  c_zero := by simp
  d_zero := by simp
  d_strictMonoOn := fun x hx y _ h => by
    show x ^ 2 < y ^ 2
    nlinarith [hx.1]

lemma cube_br {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) : cube.br m = Real.sqrt m := by
  have hs : Real.sqrt m ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hm.2⟩
  have := cube.br_d hs
  have hd : cube.d (Real.sqrt m) = m := by
    show Real.sqrt m ^ 2 = m
    exact Real.sq_sqrt hm.1
  rwa [hd] at this

lemma cube_d_one : cube.d 1 = 1 := by show (1 : ℝ) ^ 2 = 1; norm_num

/-- For the cubic cost, `h` is strictly concave. -/
lemma cube_strictConcave : StrictConcaveOn ℝ (Icc 0 (cube.d 1)) cube.br := by
  rw [cube_d_one]
  have hsq := Real.strictConcaveOn_sqrt.subset Icc_subset_Ici_self (convex_Icc (0 : ℝ) 1)
  refine ⟨convex_Icc 0 1, fun a ha b hb hab s t hs ht hst => ?_⟩
  rw [cube_br ha, cube_br hb, cube_br ((convex_Icc (0 : ℝ) 1) ha hb hs.le ht.le hst)]
  exact hsq.2 ha hb hab hs ht hst

/-- For the quadratic cost `c(e) = k e²/2`, `h(m) = m/k` is linear on `[0, c'(1)]`. -/
lemma quad_linear {k : ℝ} (hk : 0 < k) :
    ∃ a b : ℝ, ∀ m ∈ Icc 0 ((Cost.quad k hk).d 1), (Cost.quad k hk).br m = a * m + b :=
  ⟨1 / k, 0, fun m hm => by
    rw [Cost.quad_d_one] at hm
    rw [Cost.quad_br hk hm]; ring⟩

lemma quad_convex {k : ℝ} (hk : 0 < k) :
    ConvexOn ℝ (Icc 0 ((Cost.quad k hk).d 1)) (Cost.quad k hk).br := by
  obtain ⟨a, b, hab⟩ := quad_linear hk
  refine ⟨convex_Icc _ _, fun u hu w hw s t hs ht hst => ?_⟩
  rw [hab u hu, hab w hw, hab _ ((convex_Icc _ _) hu hw hs ht hst)]
  simp only [smul_eq_mul]
  have : b = s * b + t * b := by rw [← add_mul, hst, one_mul]
  nlinarith [this]

/-! ### The environments -/

/-- `E1`: `(v_a,v_p) = (3,-1)` or `(-2,3)` with probability `1/2` each. -/
noncomputable def E1 : Env :=
  mkEnv ![1/2, 1/2] ![(3, -1), (-2, 3)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (by simp [Fin.sum_univ_two])
    (by simp [Fin.sum_univ_two, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator, Cost.quad]; norm_num)

/-- `E2`: `(2,-1)` w.p. `1/2`, `(-4,3)` w.p. `1/4`, `(2,3)` w.p. `1/4`. -/
noncomputable def E2 : Env :=
  mkEnv ![1/2, 1/4, 1/4] ![(2, -1), (-4, 3), (2, 3)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three])
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)

/-- `E3`: `v_a = v_p`, equal to `2` or `-1` with probability `1/2` each. -/
noncomputable def E3 (cp : Cost) (hcp : (1 : ℝ) / 2 ≤ cp.d 1) : Env :=
  mkEnv ![1/2, 1/2] ![(2, 2), (-1, -1)] cq2 cp
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_two, Set.indicator]; norm_num; linarith)

/-- `E5`: `(-1,3)` w.p. `1/4`, `(-1,-1)` w.p. `1/4`, `(2,1)` w.p. `1/2`. -/
noncomputable def E5 : Env :=
  mkEnv ![1/4, 1/4, 1/2] ![(-1, 3), (-1, -1), (2, 1)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)

/-- `E6`: `(1,-1)` w.p. `1/4`, `(-1,-1)` w.p. `1/4`, `(1,2)` w.p. `1/2`. -/
noncomputable def E6 : Env :=
  mkEnv ![1/4, 1/4, 1/2] ![(1, -1), (-1, -1), (1, 2)] cq2 cq1
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three])
    (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)
    (by simp [Fin.sum_univ_three, Set.indicator, Cost.quad]; norm_num)

/-! ### Moments -/

section Moments

open Env

lemma E1_A : E1.A = 1 / 2 := by
  simp only [Env.A, E1, mkEnv_integral, Fin.sum_univ_two]; norm_num
lemma E1_P : E1.P = 1 := by
  simp only [Env.P, E1, mkEnv_integral, Fin.sum_univ_two]; norm_num
lemma E1_Na : E1.Na = -1 := by
  simp [Env.Na, E1, mkEnv_integral, Fin.sum_univ_two, Set.indicator]; norm_num
lemma E1_Np : E1.Np = -1 / 2 := by
  simp [Env.Np, E1, mkEnv_integral, Fin.sum_univ_two, Set.indicator]; norm_num
lemma E1_Xa : E1.Xa = 3 / 2 := by
  simp [Env.Xa, E1, mkEnv_integral, Fin.sum_univ_two, Set.indicator]; norm_num
lemma E1_Xp : E1.Xp = 3 / 2 := by
  simp [Env.Xp, E1, mkEnv_integral, Fin.sum_univ_two, Set.indicator]; norm_num
lemma E1_alphaA : E1.alphaA = -3 / 2 := by rw [Env.alphaA, E1_Xa, E1_Na]; norm_num
lemma E1_alphaP : E1.alphaP = -3 := by rw [Env.alphaP, E1_Xp, E1_Np]; norm_num

lemma E2_A : E2.A = 1 / 2 := by
  simp only [Env.A, E2, mkEnv_integral, Fin.sum_univ_three]; norm_num
lemma E2_P : E2.P = 1 := by
  simp only [Env.P, E2, mkEnv_integral, Fin.sum_univ_three]; norm_num
lemma E2_Na : E2.Na = -1 := by
  simp [Env.Na, E2, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E2_Np : E2.Np = -1 / 2 := by
  simp [Env.Np, E2, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E2_Xa : E2.Xa = 1 := by
  simp [Env.Xa, E2, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E2_alphaA : E2.alphaA = -1 := by rw [Env.alphaA, E2_Xa, E2_Na]; norm_num

lemma E2_prim : E2.prim = E1.prim := by
  simp only [Env.prim, E2_A, E2_P, E2_Na, E2_Np, E1_A, E1_P, E1_Na, E1_Np]
  rfl

lemma E3_A (cp hcp) : (E3 cp hcp).A = 1 / 2 := by
  simp only [Env.A, E3, mkEnv_integral, Fin.sum_univ_two]; norm_num
lemma E3_Na (cp hcp) : (E3 cp hcp).Na = -1 / 2 := by
  simp [Env.Na, E3, mkEnv_integral, Fin.sum_univ_two, Set.indicator]; norm_num
lemma E3_Np (cp hcp) : (E3 cp hcp).Np = -1 / 2 := by
  simp [Env.Np, E3, mkEnv_integral, Fin.sum_univ_two, Set.indicator]; norm_num
lemma E3_Xa (cp hcp) : (E3 cp hcp).Xa = -1 / 2 := by
  simp [Env.Xa, E3, mkEnv_integral, Fin.sum_univ_two, Set.indicator]; norm_num
lemma E3_Xp (cp hcp) : (E3 cp hcp).Xp = -1 / 2 := by
  simp [Env.Xp, E3, mkEnv_integral, Fin.sum_univ_two, Set.indicator]; norm_num
lemma E3_alphaA (cp hcp) : (E3 cp hcp).alphaA = 1 := by
  rw [Env.alphaA, E3_Xa, E3_Na]; norm_num
lemma E3_alphaP (cp hcp) : (E3 cp hcp).alphaP = 1 := by
  rw [Env.alphaP, E3_Xp, E3_Np]; norm_num

lemma E5_Na : E5.Na = -1 / 2 := by
  simp [Env.Na, E5, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E5_Np : E5.Np = -1 / 4 := by
  simp [Env.Np, E5, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E5_Xa : E5.Xa = -1 / 4 := by
  simp [Env.Xa, E5, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E5_Xp : E5.Xp = 1 / 2 := by
  simp [Env.Xp, E5, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E5_alphaA : E5.alphaA = 1 / 2 := by rw [Env.alphaA, E5_Xa, E5_Na]; norm_num
lemma E5_alphaP : E5.alphaP = -2 := by rw [Env.alphaP, E5_Xp, E5_Np]; norm_num

lemma E6_Na : E6.Na = -1 / 4 := by
  simp [Env.Na, E6, mkEnv_integral, Fin.sum_univ_three, Set.indicator]; norm_num
lemma E6_Xa : E6.Xa = 0 := by
  simp [Env.Xa, E6, mkEnv_integral, Fin.sum_univ_three, Set.indicator]
lemma E6_alphaA : E6.alphaA = 0 := by rw [Env.alphaA, E6_Xa, E6_Na]; norm_num

end Moments

end MI
