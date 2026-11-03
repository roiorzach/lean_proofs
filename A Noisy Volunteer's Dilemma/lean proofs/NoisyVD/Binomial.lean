import Mathlib

/-!
# Binomial probabilities

Elementary facts about the binomial mass function used throughout the paper: the mode, the
marginal-benefit bound behind Lemma `lemma_pivotal`, Chebyshev's inequality, and the derivative
identity `eq_general_derivative_identity`.

The bound `bpmf_le_four_div_sqrt` is an auxiliary step inside our proof of the Berry--Esseen Theorem
(`NoisyVD/BerryEsseen.lean`).  The rest of the library uses the paper's mass bound `bpmf_le_massConst`,
which is derived from Berry--Esseen as in the paper.
-/

open Finset Real Filter Topology

namespace NoisyVD

/-- `Pr(Bin(m,p) = k)`, defined for an arbitrary real parameter `p`. -/
noncomputable def bpmf (m : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)

lemma bpmf_nonneg {m k : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bpmf m p k := by
  unfold bpmf
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma bpmf_eq_zero_of_gt {m k : ℕ} (h : m < k) (p : ℝ) : bpmf m p k = 0 := by
  simp [bpmf, Nat.choose_eq_zero_of_lt h]

lemma bpmf_sum (m : ℕ) (p : ℝ) : ∑ k ∈ range (m + 1), bpmf m p k = 1 := by
  have h := add_pow p (1 - p) m
  simp only [add_sub_cancel, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [bpmf]; ring

lemma bpmf_le_one {m k : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : bpmf m p k ≤ 1 := by
  by_cases hk : k ≤ m
  · rw [← bpmf_sum m p]
    exact Finset.single_le_sum (f := fun i => bpmf m p i) (fun i _ => bpmf_nonneg h0 h1)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  · rw [bpmf_eq_zero_of_gt (not_le.1 hk)]; exact zero_le_one

lemma continuous_bpmf (m k : ℕ) : Continuous fun p : ℝ => bpmf m p k := by
  unfold bpmf; fun_prop

/-- Ratio recurrence for the binomial probabilities. -/
lemma bpmf_succ_mul (m : ℕ) (p : ℝ) {k : ℕ} (hk : k ≤ m) :
    bpmf m p (k + 1) * ((k + 1 : ℝ) * (1 - p)) = bpmf m p k * (((m : ℝ) - k) * p) := by
  rcases hk.eq_or_lt with rfl | hk
  · rw [bpmf_eq_zero_of_gt (Nat.lt_succ_self k)]; simp
  · have h1 : ((m.choose (k + 1) : ℝ)) * (k + 1) = (m.choose k : ℝ) * ((m : ℝ) - k) := by
      have := Nat.choose_succ_right_eq m k
      have h2 : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by
        rw [Nat.cast_sub hk.le]
      rw [← h2]
      exact_mod_cast this
    have h3 : m - k = (m - (k + 1)) + 1 := by omega
    simp only [bpmf]
    rw [h3, pow_succ (1 - p) (m - (k + 1)), pow_succ p k]
    have : m - (m - (k + 1) + 1) = k := by omega
    calc (m.choose (k + 1) : ℝ) * (p ^ k * p) * (1 - p) ^ (m - (k + 1)) * ((k + 1 : ℝ) * (1 - p))
        = ((m.choose (k + 1) : ℝ) * (k + 1)) * (p ^ k * p * ((1 - p) ^ (m - (k + 1)) * (1 - p))) := by
          ring
      _ = ((m.choose k : ℝ) * ((m : ℝ) - k)) * (p ^ k * p * ((1 - p) ^ (m - (k + 1)) * (1 - p))) := by
          rw [h1]
      _ = _ := by ring

/-- The probabilities increase up to `(m+1)p`. -/
lemma bpmf_le_succ {m i : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hi : (i + 1 : ℝ) ≤ (m + 1) * p) :
    bpmf m p i ≤ bpmf m p (i + 1) := by
  have hq : 0 < 1 - p := by linarith
  by_cases him : i ≤ m
  · have hrec := bpmf_succ_mul m p him
    have hb : 0 ≤ bpmf m p i := bpmf_nonneg hp.le hp1.le
    have hpos : 0 < (i + 1 : ℝ) * (1 - p) := by positivity
    have hle : (i + 1 : ℝ) * (1 - p) ≤ ((m : ℝ) - i) * p := by nlinarith
    have : bpmf m p i * ((i + 1 : ℝ) * (1 - p)) ≤ bpmf m p (i + 1) * ((i + 1 : ℝ) * (1 - p)) := by
      rw [hrec]; exact mul_le_mul_of_nonneg_left hle hb
    exact le_of_mul_le_mul_right this hpos
  · rw [bpmf_eq_zero_of_gt (not_le.1 him), bpmf_eq_zero_of_gt (by omega)]

/-- The probabilities decrease after `(m+1)p`. -/
lemma bpmf_succ_le {m i : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hi : (m + 1) * p ≤ (i + 1 : ℝ)) :
    bpmf m p (i + 1) ≤ bpmf m p i := by
  have hq : 0 < 1 - p := by linarith
  by_cases him : i ≤ m
  · have hrec := bpmf_succ_mul m p him
    have hb : 0 ≤ bpmf m p i := bpmf_nonneg hp.le hp1.le
    have hpos : 0 < (i + 1 : ℝ) * (1 - p) := by positivity
    have hle : ((m : ℝ) - i) * p ≤ (i + 1 : ℝ) * (1 - p) := by nlinarith
    have : bpmf m p (i + 1) * ((i + 1 : ℝ) * (1 - p)) ≤ bpmf m p i * ((i + 1 : ℝ) * (1 - p)) := by
      rw [hrec]; exact mul_le_mul_of_nonneg_left hle hb
    exact le_of_mul_le_mul_right this hpos
  · rw [bpmf_eq_zero_of_gt (not_le.1 him), bpmf_eq_zero_of_gt (by omega)]

/-- A mode of the binomial distribution. -/
noncomputable def bmode (m : ℕ) (p : ℝ) : ℕ := ⌊((m : ℝ) + 1) * p⌋₊

lemma bpmf_mono_to_mode {m : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ bmode m p) : bpmf m p i ≤ bpmf m p j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    refine (ih (by omega)).trans (bpmf_le_succ hp hp1 ?_)
    have h0 : (0 : ℝ) ≤ ((m : ℝ) + 1) * p := by positivity
    have := Nat.floor_le h0
    have h2 : ((j + 1 : ℕ) : ℝ) ≤ (bmode m p : ℝ) := by exact_mod_cast hj
    push_cast at h2
    unfold bmode at h2
    linarith

lemma bpmf_anti_from_mode {m : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {i j : ℕ} (hij : i ≤ j)
    (hi : bmode m p ≤ i) : bpmf m p j ≤ bpmf m p i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    refine (bpmf_succ_le hp hp1 ?_).trans ih
    have h0 : (0 : ℝ) ≤ ((m : ℝ) + 1) * p := by positivity
    have := Nat.lt_floor_add_one (((m : ℝ) + 1) * p)
    have h2 : (bmode m p : ℝ) ≤ (j : ℝ) := by exact_mod_cast hi.trans hij
    unfold bmode at h2
    linarith

/-- `bmode m p` maximises the binomial mass function. -/
lemma bpmf_le_mode {m : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (k : ℕ) :
    bpmf m p k ≤ bpmf m p (bmode m p) := by
  rcases le_total k (bmode m p) with h | h
  · exact bpmf_mono_to_mode hp hp1 h le_rfl
  · exact bpmf_anti_from_mode hp hp1 h le_rfl

/-- One step of the flatness estimate below the mode. -/
lemma bpmf_step_down {m i : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hm : i < m)
    (hi : (i + 1 : ℝ) ≤ (m + 1) * p) :
    bpmf m p (i + 1) * (1 - ((m + 1) * p - (i + 1)) / ((m + 1) * (p * (1 - p)))) ≤ bpmf m p i := by
  have hq : 0 < 1 - p := by linarith
  set θ : ℝ := (m + 1) * p - (i + 1) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  set V : ℝ := (m + 1) * (p * (1 - p)) with hV
  have hVpos : 0 < V := by rw [hV]; positivity
  have hrec := bpmf_succ_mul m p hm.le
  have hb : 0 ≤ bpmf m p (i + 1) := bpmf_nonneg hp.le hp1.le
  have hmi : (0 : ℝ) < (m : ℝ) - i := by
    have : (i : ℝ) < m := by exact_mod_cast hm
    linarith
  have hD : 0 < ((m : ℝ) - i) * p := by positivity
  -- `(m-i)p = (i+1)q + θ` and `(m-i)p ≥ V`
  have h1 : ((m : ℝ) - i) * p = (i + 1 : ℝ) * (1 - p) + θ := by rw [hθ]; ring
  have h2 : V ≤ ((m : ℝ) - i) * p := by
    have : ((m : ℝ) - i) * p = V + θ * p := by rw [hV, hθ]; ring
    rw [this]; have := mul_nonneg hθ0 hp.le; linarith
  have hb' : bpmf m p i = bpmf m p (i + 1) * (((i + 1 : ℝ) * (1 - p)) / (((m : ℝ) - i) * p)) := by
    field_simp
    linarith
  rw [hb']
  refine mul_le_mul_of_nonneg_left ?_ hb
  have h3 : ((i + 1 : ℝ) * (1 - p)) / (((m : ℝ) - i) * p) = 1 - θ / (((m : ℝ) - i) * p) := by
    field_simp
    linarith
  rw [h3]
  have h4 : θ / (((m : ℝ) - i) * p) ≤ θ / V := div_le_div_of_nonneg_left hθ0 hVpos h2
  linarith

/-- Flatness of the binomial mass function below its mode. -/
lemma bpmf_flat {m : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {J : ℕ}
    (hJ : (J : ℝ) * (J + 1) ≤ ((m : ℝ) + 1) * (p * (1 - p))) (hJk : J ≤ bmode m p) :
    ∀ j : ℕ, j ≤ J →
      bpmf m p (bmode m p) * (1 - (j : ℝ) * (j + 1) / (2 * (((m : ℝ) + 1) * (p * (1 - p)))))
        ≤ bpmf m p (bmode m p - j) := by
  have hq : 0 < 1 - p := by linarith
  set V : ℝ := ((m : ℝ) + 1) * (p * (1 - p)) with hV
  have hVpos : 0 < V := by rw [hV]; positivity
  have hmodeb : bmode m p ≤ m := by
    have h1 : (bmode m p : ℝ) ≤ ((m : ℝ) + 1) * p := Nat.floor_le (by positivity)
    have h2 : ((m : ℝ) + 1) * p < (m : ℝ) + 1 := by nlinarith
    have h3 : (bmode m p : ℝ) < (m : ℝ) + 1 := lt_of_le_of_lt h1 h2
    have : bmode m p < m + 1 := by exact_mod_cast h3
    omega
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hj
    have hjJ : j ≤ J := by omega
    have ih' := ih hjJ
    have hb0 : 0 ≤ bpmf m p (bmode m p) := bpmf_nonneg hp.le hp1.le
    -- step: `i + 1 = bmode - j`
    set i := bmode m p - (j + 1) with hi
    have hi1 : i + 1 = bmode m p - j := by omega
    have hilt : i < m := by omega
    have hfloor : ((m : ℝ) + 1) * p < (bmode m p : ℝ) + 1 := Nat.lt_floor_add_one _
    have hfloor2 : (bmode m p : ℝ) ≤ ((m : ℝ) + 1) * p := Nat.floor_le (by positivity)
    have hcast : ((i : ℝ) + 1) + j = bmode m p := by
      have : i + 1 + j = bmode m p := by omega
      exact_mod_cast this
    have hi2 : ((i : ℝ) + 1) ≤ ((m : ℝ) + 1) * p := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hstep := bpmf_step_down hp hp1 hilt hi2
    rw [hi1] at hstep
    have hθ : ((m : ℝ) + 1) * p - ((i : ℝ) + 1) ≤ (j : ℝ) + 1 := by linarith
    have hθ0 : 0 ≤ ((m : ℝ) + 1) * p - ((i : ℝ) + 1) := by linarith
    have hfrac : ((m : ℝ) + 1) * p - ((i : ℝ) + 1) ≤ (j + 1 : ℝ) := hθ
    have hb1 : 0 ≤ bpmf m p (bmode m p - j) := bpmf_nonneg hp.le hp1.le
    have hJ' : ((j : ℝ) + 1) * ((j : ℝ) + 2) ≤ V := by
      have h1 : ((j : ℝ) + 1) ≤ J := by exact_mod_cast hj
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have h3 : (J : ℝ) * (J + 1) ≤ V := hJ
      nlinarith
    have hA1 : (j + 1 : ℝ) / V ≤ 1 := by
      rw [div_le_one hVpos]
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    have hA2 : 0 ≤ 1 - (j : ℝ) * (j + 1) / (2 * V) := by
      have h3 : (j : ℝ) * (j + 1) / (2 * V) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        nlinarith
      linarith
    have hr : 1 - (j + 1 : ℝ) / V
        ≤ 1 - (((m : ℝ) + 1) * p - ((i : ℝ) + 1)) / (((m : ℝ) + 1) * (p * (1 - p))) := by
      have : (((m : ℝ) + 1) * p - ((i : ℝ) + 1)) / V ≤ (j + 1 : ℝ) / V :=
        div_le_div_of_nonneg_right hfrac hVpos.le
      rw [← hV]; linarith
    have hr0 : 0 ≤ 1 - (j + 1 : ℝ) / V := by linarith
    calc bpmf m p (bmode m p) * (1 - ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) / (2 * V))
        ≤ bpmf m p (bmode m p) * ((1 - (j : ℝ) * (j + 1) / (2 * V)) * (1 - (j + 1 : ℝ) / V)) := by
          refine mul_le_mul_of_nonneg_left ?_ hb0
          have key : (1 - (j : ℝ) * (j + 1) / (2 * V)) * (1 - (j + 1 : ℝ) / V)
              = 1 - ((j : ℝ) + 1) * ((j : ℝ) + 2) / (2 * V)
                + ((j : ℝ) * (j + 1) / (2 * V)) * ((j + 1 : ℝ) / V) := by
            field_simp
            ring
          rw [key]
          have hnn : 0 ≤ ((j : ℝ) * (j + 1) / (2 * V)) * ((j + 1 : ℝ) / V) := by positivity
          push_cast
          have e : ((j : ℝ) + 1 + 1) = (j : ℝ) + 2 := by ring
          rw [e]
          linarith
      _ = (bpmf m p (bmode m p) * (1 - (j : ℝ) * (j + 1) / (2 * V))) * (1 - (j + 1 : ℝ) / V) := by
          ring
      _ ≤ bpmf m p (bmode m p - j) * (1 - (j + 1 : ℝ) / V) :=
          mul_le_mul_of_nonneg_right ih' hr0
      _ ≤ bpmf m p (bmode m p - j)
            * (1 - (((m : ℝ) + 1) * p - ((i : ℝ) + 1)) / (((m : ℝ) + 1) * (p * (1 - p)))) :=
          mul_le_mul_of_nonneg_left hr hb1
      _ ≤ bpmf m p i := hstep

/-- An elementary bound on the largest binomial mass, from the ratio recurrence.  It is used only inside
the proof of the Berry--Esseen Theorem. -/
theorem bpmf_le_four_div_sqrt {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (k : ℕ) :
    bpmf m p k ≤ 4 / √((m : ℝ) * (p * (1 - p))) := by
  have hq : 0 < 1 - p := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set W : ℝ := (m : ℝ) * (p * (1 - p)) with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  set V : ℝ := ((m : ℝ) + 1) * (p * (1 - p)) with hV
  have hVpos : 0 < V := by rw [hV]; positivity
  have hWV : W ≤ V := by rw [hW, hV]; nlinarith [mul_pos hp hq]
  have hsqrtW : 0 < √W := Real.sqrt_pos.2 hWpos
  have hsqrtV : 0 < √V := Real.sqrt_pos.2 hVpos
  have hsqrtWV : √W ≤ √V := Real.sqrt_le_sqrt hWV
  refine (bpmf_le_mode hp hp1 k).trans ?_
  by_cases hV4 : V < 4
  · have h1 : √V < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith
    have h2 : (1 : ℝ) ≤ 4 / √W := by
      rw [le_div_iff₀ hsqrtW]; linarith
    exact (bpmf_le_one hp.le hp1.le).trans h2
  · push Not at hV4
    have hs2 : 2 ≤ √V := by
      rw [show (2 : ℝ) = √4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; simp]
      exact Real.sqrt_le_sqrt hV4
    set N : ℕ := ⌊√V⌋₊ with hN
    have hN1 : (N : ℝ) ≤ √V := Nat.floor_le hsqrtV.le
    have hN2 : √V < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hNpos : 1 ≤ N := by
      have : (2 : ℝ) < (N : ℝ) + 1 := lt_of_le_of_lt hs2 hN2
      have : (1 : ℝ) < N := by linarith
      have : 1 < N := by exact_mod_cast this
      omega
    set J : ℕ := N - 1 with hJdef
    have hJN : (J : ℝ) + 1 = N := by
      have : J + 1 = N := by omega
      exact_mod_cast this
    have hsq : √V * √V = V := Real.mul_self_sqrt hVpos.le
    have hNsq : (N : ℝ) * N ≤ V := by nlinarith
    have hJ : (J : ℝ) * (J + 1) ≤ V := by
      rw [hJN]
      have : (J : ℝ) = N - 1 := by linarith
      rw [this]; nlinarith
    -- `J ≤ bmode`
    have hVmp : V ≤ ((m : ℝ) + 1) * p := by
      rw [hV]
      have : p * (1 - p) ≤ p := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hsV : √V ≤ V := by nlinarith
    have hNmode : N ≤ bmode m p := by
      unfold bmode
      exact Nat.floor_mono (hsV.trans hVmp)
    have hJk : J ≤ bmode m p := by omega
    have hflat := bpmf_flat hp hp1 hJ hJk
    set h := bpmf m p (bmode m p) with hh
    have h0 : 0 ≤ h := bpmf_nonneg hp.le hp1.le
    -- each term in the window has mass at least `h/2`
    have hhalf : ∀ j ∈ range (J + 1), h / 2 ≤ bpmf m p (bmode m p - j) := by
      intro j hj
      have hj' : j ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have h1 := hflat j hj'
      have hj2 : (j : ℝ) * (j + 1) ≤ V := by
        have h3 : (j : ℝ) ≤ J := by exact_mod_cast hj'
        have h4 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        nlinarith
      have hfr : (j : ℝ) * (j + 1) / (2 * V) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have : h * (1 / 2) ≤ h * (1 - (j : ℝ) * (j + 1) / (2 * V)) :=
        mul_le_mul_of_nonneg_left (by linarith) h0
      linarith
    have hsum : ∑ j ∈ range (J + 1), bpmf m p (bmode m p - j) ≤ 1 := by
      rw [← bpmf_sum m p]
      have hinj : Set.InjOn (fun j => bmode m p - j) (range (J + 1) : Set ℕ) := by
        intro a ha b hb hab
        have ha' := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_coe.1 ha))
        have hb' := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_coe.1 hb))
        simp only at hab
        omega
      have hmodeb : bmode m p ≤ m := by
        have h1 : (bmode m p : ℝ) ≤ ((m : ℝ) + 1) * p := Nat.floor_le (by positivity)
        have h2 : ((m : ℝ) + 1) * p < (m : ℝ) + 1 := by nlinarith
        have h3 : (bmode m p : ℝ) < (m : ℝ) + 1 := lt_of_le_of_lt h1 h2
        have : bmode m p < m + 1 := by exact_mod_cast h3
        omega
      calc ∑ j ∈ range (J + 1), bpmf m p (bmode m p - j)
          = ∑ i ∈ (range (J + 1)).image (fun j => bmode m p - j), bpmf m p i := by
            rw [Finset.sum_image hinj]
        _ ≤ ∑ i ∈ range (m + 1), bpmf m p i := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => bpmf_nonneg hp.le hp1.le)
            intro i hi
            obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hi
            exact Finset.mem_range.2 (by omega)
    have hcount : ((J : ℝ) + 1) * (h / 2) ≤ 1 := by
      have := Finset.card_nsmul_le_sum (range (J + 1)) (fun j => bpmf m p (bmode m p - j)) (h / 2)
        hhalf
      simp only [card_range, nsmul_eq_mul] at this
      push_cast at this
      linarith
    have hNge : √V / 2 ≤ (N : ℝ) := by linarith
    have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
    rw [hJN] at hcount
    have hh2 : h ≤ 2 / N := by
      rw [le_div_iff₀ hNp]; linarith
    have hh3 : 2 / (N : ℝ) ≤ 4 / √V := by
      rw [div_le_div_iff₀ hNp hsqrtV]; linarith
    have hh4 : 4 / √V ≤ 4 / √W := div_le_div_of_nonneg_left (by norm_num) hsqrtW hsqrtWV
    linarith

/-! ### The expected marginal benefit of a report -/

/-- `Σ_{k≤m} Pr(Bin(m,p)=k) (v(k+1) - v(k))`: the gross expected gain from one extra report when
`m` other individuals report with probability `p`. -/
noncomputable def marginal (m : ℕ) (p : ℝ) (v : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (m + 1), bpmf m p k * (v (k + 1) - v k)

lemma marginal_congr {m : ℕ} {p : ℝ} {v w : ℕ → ℝ} (h : ∀ k, k ≤ m + 1 → v k = w k) :
    marginal m p v = marginal m p w := by
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [h k (by omega), h (k + 1) (by omega)]

/-- A crude bound: the marginal benefit is at most the oscillation of `v`. -/
lemma abs_marginal_le_range {m : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {v : ℕ → ℝ} {l B : ℝ}
    (hv : ∀ k, l ≤ v k ∧ v k ≤ l + B) : |marginal m p v| ≤ B := by
  unfold marginal
  have hB : ∀ k, |v (k + 1) - v k| ≤ B := fun k => by
    rw [abs_le]; constructor <;> linarith [(hv k).1, (hv k).2, (hv (k + 1)).1, (hv (k + 1)).2]
  calc |∑ k ∈ range (m + 1), bpmf m p k * (v (k + 1) - v k)|
      ≤ ∑ k ∈ range (m + 1), |bpmf m p k * (v (k + 1) - v k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (m + 1), bpmf m p k * B := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (bpmf_nonneg h0 h1)]
        exact mul_le_mul_of_nonneg_left (hB k) (bpmf_nonneg h0 h1)
    _ = B := by rw [← Finset.sum_mul, bpmf_sum, one_mul]

lemma bmode_le {m : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : bmode m p ≤ m := by
  have h1 : (bmode m p : ℝ) ≤ ((m : ℝ) + 1) * p := Nat.floor_le (by positivity)
  have h2 : ((m : ℝ) + 1) * p < (m : ℝ) + 1 := by nlinarith
  have h3 : (bmode m p : ℝ) < (m : ℝ) + 1 := lt_of_le_of_lt h1 h2
  have : bmode m p < m + 1 := by exact_mod_cast h3
  omega

/-- A reporting incentive is unchanged when `u^p` is shifted by a constant. -/
lemma marginal_sub_const (m : ℕ) (p c : ℝ) (v : ℕ → ℝ) :
    marginal m p (fun k => v k - c) = marginal m p v := by
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Summation by parts, as in the proof of Lemma `lemma_pivotal`. -/
lemma marginal_eq_parts (m : ℕ) (p : ℝ) (v : ℕ → ℝ) :
    marginal m p v = v (m + 1) * bpmf m p m - v 0 * bpmf m p 0
      + ∑ k ∈ range m, v (k + 1) * (bpmf m p k - bpmf m p (k + 1)) := by
  have key : ∀ N, ∑ k ∈ range (N + 1), bpmf m p k * (v (k + 1) - v k)
      = v (N + 1) * bpmf m p N - v 0 * bpmf m p 0
        + ∑ k ∈ range N, v (k + 1) * (bpmf m p k - bpmf m p (k + 1)) := by
    intro N
    induction N with
    | zero => simp; ring
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ N]
      ring
  exact key m

/-- The telescoping sum in the proof of Lemma `lemma_pivotal`: the variation of the unimodal mass
function is `2 max_k Pr(x = k) - Pr(x = 0) - Pr(x = m)`. -/
lemma sum_abs_bpmf_diff {m : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∑ k ∈ range m, |bpmf m p k - bpmf m p (k + 1)|
      = 2 * bpmf m p (bmode m p) - bpmf m p 0 - bpmf m p m := by
  set kk := bmode m p with hkk
  have hkm : kk ≤ m := bmode_le hp hp1
  have hsplit : ∑ k ∈ range m, |bpmf m p k - bpmf m p (k + 1)|
      = ∑ k ∈ range kk, |bpmf m p k - bpmf m p (k + 1)|
        + ∑ k ∈ Finset.Ico kk m, |bpmf m p k - bpmf m p (k + 1)| := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) hkm]
  have hL : ∀ j, j ≤ kk → ∑ k ∈ range j, |bpmf m p k - bpmf m p (k + 1)|
      = bpmf m p j - bpmf m p 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ, ih (by omega),
        abs_of_nonpos (sub_nonpos.2 (bpmf_mono_to_mode hp hp1 (Nat.le_succ j) hj))]
      ring
  have hR : ∀ j, kk ≤ j → ∑ k ∈ Finset.Ico kk j, |bpmf m p k - bpmf m p (k + 1)|
      = bpmf m p kk - bpmf m p j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => simp
    | succ j hj ih =>
      rw [Finset.sum_Ico_succ_top hj, ih,
        abs_of_nonneg (sub_nonneg.2 (bpmf_anti_from_mode hp hp1 (Nat.le_succ j) hj))]
      ring
  rw [hsplit, hL kk le_rfl, hR m hkm]
  ring

/-- Lemma `lemma_pivotal`, combinatorial core: `|Δ| ≤ B max_k Pr(x = k)`.  As in the paper: center the
payoffs so that they lie in `[-B/2, B/2]`, sum by parts, apply the triangle inequality, and telescope
around the mode. -/
theorem abs_marginal_le_mode {m : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {v : ℕ → ℝ} {l B : ℝ}
    (hv : ∀ k, l ≤ v k ∧ v k ≤ l + B) : |marginal m p v| ≤ B * bpmf m p (bmode m p) := by
  set w : ℕ → ℝ := fun k => v k - (l + B / 2) with hw
  have hwb : ∀ k, |w k| ≤ B / 2 := fun k => by
    simp only [hw]
    rw [abs_le]
    constructor <;> linarith [(hv k).1, (hv k).2]
  have hB2 : 0 ≤ B / 2 := (abs_nonneg _).trans (hwb 0)
  have hb0 : ∀ k, 0 ≤ bpmf m p k := fun k => bpmf_nonneg hp.le hp1.le
  rw [← marginal_sub_const m p (l + B / 2) v, marginal_eq_parts]
  have h1 : |w (m + 1) * bpmf m p m| ≤ B / 2 * bpmf m p m := by
    rw [abs_mul, abs_of_nonneg (hb0 m)]
    exact mul_le_mul_of_nonneg_right (hwb _) (hb0 m)
  have h2 : |w 0 * bpmf m p 0| ≤ B / 2 * bpmf m p 0 := by
    rw [abs_mul, abs_of_nonneg (hb0 0)]
    exact mul_le_mul_of_nonneg_right (hwb _) (hb0 0)
  have h3 : |∑ k ∈ range m, w (k + 1) * (bpmf m p k - bpmf m p (k + 1))|
      ≤ B / 2 * ∑ k ∈ range m, |bpmf m p k - bpmf m p (k + 1)| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hwb _) (abs_nonneg _)
  rw [sum_abs_bpmf_diff hp hp1] at h3
  have h4 := abs_add_le (w (m + 1) * bpmf m p m - w 0 * bpmf m p 0)
    (∑ k ∈ range m, w (k + 1) * (bpmf m p k - bpmf m p (k + 1)))
  have h5 := abs_sub (w (m + 1) * bpmf m p m) (w 0 * bpmf m p 0)
  have h6 : B / 2 * bpmf m p m + B / 2 * bpmf m p 0
      + B / 2 * (2 * bpmf m p (bmode m p) - bpmf m p 0 - bpmf m p m) = B * bpmf m p (bmode m p) := by
    ring
  linarith

/-! ### Moments -/

lemma bpmf_eval_bernstein (m k : ℕ) (p : ℝ) :
    (bernsteinPolynomial ℝ m k).eval p = bpmf m p k := by
  simp [bernsteinPolynomial, bpmf]

/-- The binomial variance. -/
lemma bpmf_variance (m : ℕ) (p : ℝ) :
    ∑ k ∈ range (m + 1), ((m : ℝ) * p - k) ^ 2 * bpmf m p k = (m : ℝ) * p * (1 - p) := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.variance ℝ m)
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, nsmul_eq_mul, bpmf_eval_bernstein] at h
  simpa [mul_assoc] using h

/-- Chebyshev's inequality for the binomial distribution, in the form used in the paper. -/
lemma bpmf_chebyshev {m : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {a : ℝ} (ha : 0 < a) :
    ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => a ≤ |(k : ℝ) - (m : ℝ) * p|), bpmf m p k
      ≤ (m : ℝ) * p * (1 - p) / a ^ 2 := by
  rw [le_div_iff₀ (by positivity), Finset.sum_mul]
  calc ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => a ≤ |(k : ℝ) - (m : ℝ) * p|), bpmf m p k * a ^ 2
      ≤ ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => a ≤ |(k : ℝ) - (m : ℝ) * p|),
          ((m : ℝ) * p - k) ^ 2 * bpmf m p k := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := (Finset.mem_filter.1 hk).2
        have : a ^ 2 ≤ ((m : ℝ) * p - k) ^ 2 := by
          rw [← sq_abs ((m : ℝ) * p - k), abs_sub_comm]
          exact pow_le_pow_left₀ ha.le hk' 2
        nlinarith [bpmf_nonneg (m := m) (k := k) h0 h1]
    _ ≤ ∑ k ∈ range (m + 1), ((m : ℝ) * p - k) ^ 2 * bpmf m p k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => ?_
        exact mul_nonneg (sq_nonneg _) (bpmf_nonneg h0 h1)
    _ = _ := bpmf_variance m p

/-! ### Derivative of the smoothed payoff -/

/-- `Σ_{k≤n} Pr(Bin(n,p)=k) v(k)`: the expectation of `v` under `Bin(n,p)`. -/
noncomputable def bexp (n : ℕ) (p : ℝ) (v : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), bpmf n p k * v k

lemma bexp_congr {n : ℕ} {p : ℝ} {v w : ℕ → ℝ} (h : ∀ k, k ≤ n → v k = w k) :
    bexp n p v = bexp n p w := by
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

lemma continuous_bexp (n : ℕ) (v : ℕ → ℝ) : Continuous fun p => bexp n p v := by
  unfold bexp
  exact continuous_finsetSum _ fun k _ => (continuous_bpmf n k).mul continuous_const

lemma hasDerivAt_bpmf_succ (m k : ℕ) (p : ℝ) :
    HasDerivAt (fun x => bpmf (m + 1) x k)
      (((m + 1 : ℕ) : ℝ) * ((if k = 0 then 0 else bpmf m p (k - 1)) - bpmf m p k)) p := by
  have hP := (bernsteinPolynomial ℝ (m + 1) k).hasDerivAt p
  have heq : (fun x => bpmf (m + 1) x k) = fun x => (bernsteinPolynomial ℝ (m + 1) k).eval x := by
    funext x; rw [bpmf_eval_bernstein]
  rw [heq]
  convert hP using 1
  cases k with
  | zero =>
    rw [bernsteinPolynomial.derivative_zero]
    simp [Polynomial.eval_mul, Polynomial.eval_natCast, bpmf_eval_bernstein]
    ring
  | succ k =>
    rw [bernsteinPolynomial.derivative_succ]
    simp [Polynomial.eval_mul, Polynomial.eval_natCast, bpmf_eval_bernstein, Polynomial.eval_sub]

/-- The derivative identity `d/dp Σ_k b_{n,p}(k) v(k) = n Σ_k b_{n-1,p}(k) (v(k+1) - v(k))`
(equation `eq_general_derivative_identity` of the paper). -/
theorem hasDerivAt_bexp (m : ℕ) (v : ℕ → ℝ) (p : ℝ) :
    HasDerivAt (fun x => bexp (m + 1) x v) (((m + 1 : ℕ) : ℝ) * marginal m p v) p := by
  have h : HasDerivAt (fun x => ∑ k ∈ range (m + 2), bpmf (m + 1) x k * v k)
      (∑ k ∈ range (m + 2), (((m + 1 : ℕ) : ℝ) *
        ((if k = 0 then 0 else bpmf m p (k - 1)) - bpmf m p k)) * v k) p := by
    have := HasDerivAt.fun_sum (u := range (m + 2)) (fun k _ =>
      (hasDerivAt_bpmf_succ m k p).mul_const (v k))
    exact this
  have hfun : (fun x => bexp (m + 1) x v) = fun x => ∑ k ∈ range (m + 2), bpmf (m + 1) x k * v k :=
    rfl
  rw [hfun]
  convert h using 1
  unfold marginal
  -- reindex
  have h1 : ∑ k ∈ range (m + 2), (((m + 1 : ℕ) : ℝ) *
        ((if k = 0 then 0 else bpmf m p (k - 1)) - bpmf m p k)) * v k
      = ((m + 1 : ℕ) : ℝ) * (∑ k ∈ range (m + 2), (if k = 0 then 0 else bpmf m p (k - 1)) * v k
          - ∑ k ∈ range (m + 2), bpmf m p k * v k) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1, Finset.sum_range_succ' (fun k => (if k = 0 then 0 else bpmf m p (k - 1)) * v k),
    Finset.sum_range_succ (fun k => bpmf m p k * v k) (m + 1)]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, ite_true,
    zero_mul, add_zero]
  rw [bpmf_eq_zero_of_gt (Nat.lt_succ_self m), zero_mul, add_zero, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end NoisyVD
