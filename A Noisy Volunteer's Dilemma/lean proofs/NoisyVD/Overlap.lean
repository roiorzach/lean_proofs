import NoisyVD.Binomial

/-!
# Total variation and overlap of binomial laws

The paper's Lemma `lemma_binomial_overlap`.
-/

open Finset Real Filter Topology

namespace NoisyVD

/-- Total variation distance between `Bin(m,p)` and `Bin(m,q)`. -/
noncomputable def tv (m : ℕ) (p q : ℝ) : ℝ :=
  (1 / 2) * ∑ k ∈ range (m + 1), |bpmf m p k - bpmf m q k|

/-- The Bhattacharyya affinity. -/
noncomputable def affinity (m : ℕ) (p q : ℝ) : ℝ :=
  ∑ k ∈ range (m + 1), √(bpmf m p k * bpmf m q k)

/-- `b_n` of the paper. -/
noncomputable def bhatt (p q : ℝ) : ℝ := √(p * q) + √((1 - p) * (1 - q))

lemma tv_nonneg (m : ℕ) (p q : ℝ) : 0 ≤ tv m p q := by
  unfold tv
  have : 0 ≤ ∑ k ∈ range (m + 1), |bpmf m p k - bpmf m q k| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

/-- `A_n = b_n^n`. -/
lemma affinity_eq {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    affinity m p q = bhatt p q ^ m := by
  unfold affinity bhatt
  rw [add_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hp' : 0 ≤ 1 - p := by linarith
  have hq' : 0 ≤ 1 - q := by linarith
  have e : bpmf m p k * bpmf m q k
      = ((m.choose k : ℝ) * √(p * q) ^ k * √((1 - p) * (1 - q)) ^ (m - k)) ^ 2 := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2, mul_comm (m - k) 2, pow_mul, pow_mul,
      Real.sq_sqrt (mul_nonneg hp0 hq0), Real.sq_sqrt (mul_nonneg hp' hq')]
    simp only [bpmf]
    rw [mul_pow, mul_pow]
    ring
  rw [e, Real.sqrt_sq (by positivity)]
  ring

/-- `1 - b_n = ½[(√p-√q)² + (√(1-p)-√(1-q))²]`, and the bound `eq_affinity_bound`. -/
lemma one_sub_bhatt_le {l p q : ℝ} (hl : 0 < l) (hp : p ∈ Set.Icc l (1 - l))
    (hq : q ∈ Set.Icc l (1 - l)) : 1 - bhatt p q ≤ (p - q) ^ 2 / (4 * l) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hp' : 0 < 1 - p := by linarith
  have hq' : 0 < 1 - q := by linarith
  have aux : ∀ {x y : ℝ}, l ≤ x → l ≤ y → (√x - √y) ^ 2 ≤ (x - y) ^ 2 / (4 * l) := by
    intro x y hx hy
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < y := by linarith
    have hsx : √l ≤ √x := Real.sqrt_le_sqrt hx
    have hsy : √l ≤ √y := Real.sqrt_le_sqrt hy
    have hsl : 0 < √l := Real.sqrt_pos.2 hl
    have hsum : 2 * √l ≤ √x + √y := by linarith
    have hsq : (2 * √l) ^ 2 ≤ (√x + √y) ^ 2 := pow_le_pow_left₀ (by positivity) hsum 2
    have h4 : 4 * l = (2 * √l) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hl.le]; norm_num
    have hdiff : x - y = (√x - √y) * (√x + √y) := by
      have h1 := Real.mul_self_sqrt hx0.le
      have h2 := Real.mul_self_sqrt hy0.le
      nlinarith
    rw [hdiff, h4, mul_pow, mul_div_assoc]
    have hpos : 0 < (2 * √l) ^ 2 := by positivity
    have : 1 ≤ (√x + √y) ^ 2 / (2 * √l) ^ 2 := by
      rw [one_le_div hpos]; exact hsq
    have h0 := sq_nonneg (√x - √y)
    nlinarith
  have h1 := aux hp1 hq1
  have h2 := aux (x := 1 - p) (y := 1 - q) (by linarith) (by linarith)
  have e1 : √(p * q) = √p * √q := Real.sqrt_mul hp0.le q
  have e2 : √((1 - p) * (1 - q)) = √(1 - p) * √(1 - q) := Real.sqrt_mul hp'.le _
  have s1 := Real.mul_self_sqrt hp0.le
  have s2 := Real.mul_self_sqrt hq0.le
  have s3 := Real.mul_self_sqrt hp'.le
  have s4 := Real.mul_self_sqrt hq'.le
  have hid : 1 - bhatt p q = ((√p - √q) ^ 2 + (√(1 - p) - √(1 - q)) ^ 2) / 2 := by
    unfold bhatt
    rw [e1, e2]
    nlinarith
  rw [hid]
  have e3 : ((1 - p) - (1 - q)) ^ 2 = (p - q) ^ 2 := by ring
  rw [e3] at h2
  have : ((√p - √q) ^ 2 + (√(1 - p) - √(1 - q)) ^ 2) / 2
      ≤ ((p - q) ^ 2 / (4 * l) + (p - q) ^ 2 / (4 * l)) / 2 := by
    gcongr
  linarith

lemma bhatt_nonneg (p q : ℝ) : 0 ≤ bhatt p q := by
  unfold bhatt; positivity

lemma bhatt_le_one {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    bhatt p q ≤ 1 := by
  have h1 : 0 ≤ (√p - √q) ^ 2 + (√(1 - p) - √(1 - q)) ^ 2 := by positivity
  have s1 := Real.mul_self_sqrt hp0
  have s2 := Real.mul_self_sqrt hq0
  have s3 := Real.mul_self_sqrt (show 0 ≤ 1 - p by linarith)
  have s4 := Real.mul_self_sqrt (show 0 ≤ 1 - q by linarith)
  unfold bhatt
  rw [Real.sqrt_mul hp0, Real.sqrt_mul (show 0 ≤ 1 - p by linarith)]
  nlinarith

/-- The Cauchy--Schwarz inequality `eq_tv_affinity`. -/
lemma tv_le_affinity {m : ℕ} {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    tv m p q ≤ √(1 - affinity m p q ^ 2) := by
  set P := bpmf m p with hP
  set Q := bpmf m q with hQ
  have hP0 : ∀ k, 0 ≤ P k := fun k => bpmf_nonneg hp0 hp1
  have hQ0 : ∀ k, 0 ≤ Q k := fun k => bpmf_nonneg hq0 hq1
  set s := range (m + 1) with hs
  have hPs : ∑ k ∈ s, P k = 1 := bpmf_sum m p
  have hQs : ∑ k ∈ s, Q k = 1 := bpmf_sum m q
  have hA : affinity m p q = ∑ k ∈ s, √(P k) * √(Q k) := by
    unfold affinity
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Real.sqrt_mul (hP0 k) _
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => |√(P k) - √(Q k)|)
    (fun k => √(P k) + √(Q k))
  have h1 : ∑ k ∈ s, |√(P k) - √(Q k)| * (√(P k) + √(Q k)) = ∑ k ∈ s, |P k - Q k| := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hnn : 0 ≤ √(P k) + √(Q k) := by positivity
    have e0 : |√(P k) - √(Q k)| * (√(P k) + √(Q k)) = |(√(P k) - √(Q k)) * (√(P k) + √(Q k))| := by
      rw [abs_mul, abs_of_nonneg hnn]
    rw [e0]
    congr 1
    have e1 := Real.mul_self_sqrt (hP0 k)
    have e2 := Real.mul_self_sqrt (hQ0 k)
    nlinarith
  have h2 : ∑ k ∈ s, |√(P k) - √(Q k)| ^ 2 = 2 - 2 * affinity m p q := by
    have : ∀ k ∈ s, |√(P k) - √(Q k)| ^ 2 = P k + Q k - 2 * (√(P k) * √(Q k)) := by
      intro k _
      rw [sq_abs]
      have e1 := Real.mul_self_sqrt (hP0 k)
      have e2 := Real.mul_self_sqrt (hQ0 k)
      nlinarith
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_add_distrib, hPs, hQs, hA,
      Finset.mul_sum]
    ring
  have h3 : ∑ k ∈ s, (√(P k) + √(Q k)) ^ 2 = 2 + 2 * affinity m p q := by
    have : ∀ k ∈ s, (√(P k) + √(Q k)) ^ 2 = P k + Q k + 2 * (√(P k) * √(Q k)) := by
      intro k _
      have e1 := Real.mul_self_sqrt (hP0 k)
      have e2 := Real.mul_self_sqrt (hQ0 k)
      nlinarith
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib, hPs, hQs, hA,
      Finset.mul_sum]
    ring
  rw [h1, h2, h3] at hCS
  apply Real.le_sqrt_of_sq_le
  have ht : tv m p q = (1 / 2) * ∑ k ∈ s, |P k - Q k| := rfl
  rw [ht]
  nlinarith [hCS]

/-- First claim, quantitative: `TV ≤ √(m (p-q)² / (2l))`. -/
theorem tv_le_of_close {m : ℕ} {l p q : ℝ} (hl : 0 < l) (hp : p ∈ Set.Icc l (1 - l))
    (hq : q ∈ Set.Icc l (1 - l)) : tv m p q ≤ √((m : ℝ) * (p - q) ^ 2 / (2 * l)) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hp1 : p ≤ 1 := by linarith [hp.2]
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hq1 : q ≤ 1 := by linarith [hq.2]
  refine (tv_le_affinity hp0 hp1 hq0 hq1).trans (Real.sqrt_le_sqrt ?_)
  rw [affinity_eq hp0 hp1 hq0 hq1]
  have hb0 := bhatt_nonneg p q
  have hb := one_sub_bhatt_le hl hp hq
  have hbern : 1 + (m : ℝ) * (bhatt p q - 1) ≤ bhatt p q ^ m := by
    have h := one_add_mul_le_pow (a := bhatt p q - 1) (by linarith) m
    simpa using h
  set A := bhatt p q ^ m with hA
  have hA0 : 0 ≤ A := by positivity
  have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- `A ≤ 1`
  have hb1 : bhatt p q ≤ 1 := bhatt_le_one hp0 hp1 hq0 hq1
  have hA1 : A ≤ 1 := pow_le_one₀ hb0 hb1
  have hstep : 1 - A ^ 2 ≤ 2 * (1 - A) := by nlinarith
  have hstep2 : 1 - A ≤ (m : ℝ) * (1 - bhatt p q) := by linarith
  have hstep3 : (m : ℝ) * (1 - bhatt p q) ≤ (m : ℝ) * ((p - q) ^ 2 / (4 * l)) :=
    mul_le_mul_of_nonneg_left hb hmr
  have e : (m : ℝ) * (p - q) ^ 2 / (2 * l) = 2 * ((m : ℝ) * ((p - q) ^ 2 / (4 * l))) := by
    field_simp
    ring
  rw [e]
  linarith

/-- Second claim, explicit: `m (p-q)² ≤ C` and `m ≥ C/(2l)` give `TV ≤ √(1 - exp(-C/l))`. -/
theorem tv_le_of_bounded {m : ℕ} {l p q C : ℝ} (hl : 0 < l) (hp : p ∈ Set.Icc l (1 - l))
    (hq : q ∈ Set.Icc l (1 - l)) (hm : 1 ≤ m) (hC : (m : ℝ) * (p - q) ^ 2 ≤ C)
    (hmC : C / (2 * l) ≤ m) : tv m p q ≤ √(1 - exp (-C / l)) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hp1 : p ≤ 1 := by linarith [hp.2]
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hq1 : q ≤ 1 := by linarith [hq.2]
  refine (tv_le_affinity hp0 hp1 hq0 hq1).trans (Real.sqrt_le_sqrt ?_)
  rw [affinity_eq hp0 hp1 hq0 hq1]
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := one_sub_bhatt_le hl hp hq
  have h1b : (m : ℝ) * (1 - bhatt p q) ≤ C / (4 * l) := by
    have : (m : ℝ) * (1 - bhatt p q) ≤ (m : ℝ) * ((p - q) ^ 2 / (4 * l)) :=
      mul_le_mul_of_nonneg_left hb hmr.le
    refine this.trans ?_
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hC (by positivity)
  have hC0 : 0 ≤ C := le_trans (mul_nonneg hmr.le (sq_nonneg _)) hC
  have hhalf : 1 - bhatt p q ≤ 1 / 2 := by
    have h2 : C / (4 * l) ≤ (m : ℝ) / 2 := by
      have : C / (4 * l) = C / (2 * l) / 2 := by field_simp; ring
      rw [this]
      linarith
    have h3 : (m : ℝ) * (1 - bhatt p q) ≤ (m : ℝ) * (1 / 2) := by linarith
    exact le_of_mul_le_mul_left h3 hmr
  have hb2 : 1 / 2 ≤ bhatt p q := by linarith
  have hbpos : 0 < bhatt p q := by linarith
  have hlog : -(2 * (1 - bhatt p q)) ≤ log (bhatt p q) := by
    have h := Real.one_sub_inv_le_log_of_pos hbpos
    have hb1 : bhatt p q ≤ 1 := bhatt_le_one hp0 hp1 hq0 hq1
    have h4 : (bhatt p q)⁻¹ ≤ 1 + 2 * (1 - bhatt p q) := by
      rw [inv_le_iff_one_le_mul₀ hbpos]
      nlinarith
    linarith
  have hAexp : exp (-C / (2 * l)) ≤ bhatt p q ^ m := by
    rw [← Real.exp_log (pow_pos hbpos m), Real.log_pow]
    apply Real.exp_le_exp.2
    have h5 : (m : ℝ) * -(2 * (1 - bhatt p q)) ≤ (m : ℝ) * log (bhatt p q) :=
      mul_le_mul_of_nonneg_left hlog hmr.le
    have h6 : -C / (2 * l) = -2 * (C / (4 * l)) := by field_simp; ring
    rw [h6]
    nlinarith
  have hsq : exp (-C / l) ≤ (bhatt p q ^ m) ^ 2 := by
    have e : exp (-C / l) = exp (-C / (2 * l)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [e]
    exact pow_le_pow_left₀ (exp_pos _).le hAexp 2
  linarith

/-- The uniform bound in Lemma `lemma_binomial_overlap` is strictly below one. -/
lemma sqrt_one_sub_exp_lt_one {C l : ℝ} : √(1 - exp (-C / l)) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  have := exp_pos (-C / l)
  linarith

/-- `Σ_k min(P(k), Q(k)) = 1 - TV(P, Q)`. -/
lemma sum_min_eq (m : ℕ) (p q : ℝ) :
    ∑ k ∈ range (m + 1), min (bpmf m p k) (bpmf m q k) = 1 - tv m p q := by
  have h : ∀ k ∈ range (m + 1), min (bpmf m p k) (bpmf m q k)
      = (bpmf m p k + bpmf m q k - |bpmf m p k - bpmf m q k|) / 2 := by
    intro k _
    rcases le_total (bpmf m p k) (bpmf m q k) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    bpmf_sum, bpmf_sum]
  unfold tv
  ring

/-- **Lemma `lemma_binomial_overlap`.** -/
theorem lemma_binomial_overlap {l : ℝ} (hl : 0 < l) {p q : ℕ → ℝ}
    (hp : ∀ n, p n ∈ Set.Icc l (1 - l)) (hq : ∀ n, q n ∈ Set.Icc l (1 - l)) :
    (Tendsto (fun n : ℕ => (n : ℝ) * (p n - q n) ^ 2) atTop (𝓝 0) →
      Tendsto (fun n => tv n (p n) (q n)) atTop (𝓝 0)) ∧
    (∀ C : ℝ, (∀ n : ℕ, (n : ℝ) * (p n - q n) ^ 2 ≤ C) →
      ∀ᶠ n in atTop, tv n (p n) (q n) ≤ √(1 - exp (-C / l)) ∧ √(1 - exp (-C / l)) < 1) := by
  constructor
  · intro h
    have h1 : Tendsto (fun n : ℕ => √((n : ℝ) * (p n - q n) ^ 2 / (2 * l))) atTop (𝓝 0) := by
      have := (h.div_const (2 * l)).sqrt
      simpa using this
    refine squeeze_zero (fun n => tv_nonneg _ _ _) (fun n => ?_) h1
    exact tv_le_of_close hl (hp n) (hq n)
  · intro C hC
    have hm1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    have hm2 : ∀ᶠ n : ℕ in atTop, C / (2 * l) ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    filter_upwards [hm1, hm2] with n h1 h2
    exact ⟨tv_le_of_bounded hl (hp n) (hq n) h1 (hC n) h2, sqrt_one_sub_exp_lt_one⟩

/-- Quasi-concavity of `p ↦ Pr(Bin(n,p)=k)`: the log-concavity step of Prop. `prop_general_failures`. -/
lemma bpmf_ge_min {n k : ℕ} {a b p : ℝ} (ha : 0 < a) (hb : b < 1) (hap : a ≤ p) (hpb : p ≤ b) :
    min (bpmf n a k) (bpmf n b k) ≤ bpmf n p k := by
  have hab : a ≤ b := hap.trans hpb
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hb0 : 0 < b := by linarith
  have ha1 : a < 1 := by linarith
  by_cases hk : k ≤ n
  swap
  · rw [bpmf_eq_zero_of_gt (not_le.1 hk), bpmf_eq_zero_of_gt (not_le.1 hk),
      bpmf_eq_zero_of_gt (not_le.1 hk)]
    simp
  have hc : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  let g : ℝ → ℝ := fun x => (k : ℝ) * log x + ((n - k : ℕ) : ℝ) * log (1 - x)
  have hbp : ∀ x : ℝ, 0 < x → x < 1 → bpmf n x k = (n.choose k : ℝ) * exp (g x) := by
    intro x hx0 hx1
    simp only [bpmf, g]
    rw [exp_add, ← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity),
      Real.exp_log (pow_pos (by linarith) _)]
    ring
  rw [hbp a ha ha1, hbp b hb0 hb, hbp p hp0 hp1]
  -- concavity of `log`
  rcases hab.eq_or_lt with rfl | hlt
  · have : p = a := le_antisymm hpb hap
    subst this
    simp
  set w : ℝ := (p - a) / (b - a) with hw
  have hd : 0 < b - a := by linarith
  have hw0 : 0 ≤ w := div_nonneg (by linarith) hd.le
  have hw1 : w ≤ 1 := by rw [hw, div_le_one hd]; linarith
  have hpw : p = (1 - w) * a + w * b := by
    rw [hw]; field_simp; ring
  have hlog : ∀ x y : ℝ, 0 < x → 0 < y →
      (1 - w) * log x + w * log y ≤ log ((1 - w) * x + w * y) := by
    intro x y hx hy
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy)
      (show 0 ≤ 1 - w by linarith) hw0 (by ring)
    simpa [smul_eq_mul] using this
  have h1 := hlog a b ha hb0
  have h2 := hlog (1 - a) (1 - b) (by linarith) (by linarith)
  rw [← hpw] at h1
  have e : (1 - w) * (1 - a) + w * (1 - b) = 1 - p := by rw [hpw]; ring
  rw [e] at h2
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn0 : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hg : (1 - w) * g a + w * g b ≤ g p := by
    simp only [g]
    have h3 := mul_le_mul_of_nonneg_left h1 hk0
    have h4 := mul_le_mul_of_nonneg_left h2 hn0
    nlinarith
  have hmin : min (g a) (g b) ≤ g p := by
    refine le_trans ?_ hg
    rcases le_total (g a) (g b) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  rw [← mul_min_of_nonneg _ _ hc.le]
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  rcases le_total (g a) (g b) with h | h
  · rw [min_eq_left (Real.exp_le_exp.2 h)]
    rw [min_eq_left h] at hmin
    exact Real.exp_le_exp.2 hmin
  · rw [min_eq_right (Real.exp_le_exp.2 h)]
    rw [min_eq_right h] at hmin
    exact Real.exp_le_exp.2 hmin

end NoisyVD
