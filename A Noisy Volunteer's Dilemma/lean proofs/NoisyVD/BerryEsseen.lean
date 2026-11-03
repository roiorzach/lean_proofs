import NoisyVD.Binomial
import NoisyVD.Gaussian

/-!
# The Berry--Esseen Theorem for Bernoulli sums

The proof of Lemma `lemma_local_binomial` in the paper cites the Berry--Esseen Theorem for
`X_{m,p} = ξ₁ + ⋯ + ξ_m` with `ξ_j` i.i.d. Bernoulli(`p`).  Mathlib does not contain the theorem, so we
prove the case the paper uses, `berry_esseen_binomial`, with an explicit universal constant `CBE`:

  `sup_z |Pr(X_{m,p} ≤ mp + z σ_{m,p}) - Φ(z)| ≤ C_BE E|ξ₁ - p|³ / ((p(1-p))^{3/2} √m)`.

The proof is Stein's method.  With `f = stein z` the bounded solution of
`f'(w) - w f(w) = 1_{w ≤ z} - Φ(z)`, the difference `Pr(W ≤ z) - Φ(z)` equals `E[f'(W) - W f(W)]` for the
standardised count `W`.  The binomial identity `sum_stein_identity` turns `E[W f(W)]` into an average
of increments of `f`, and the increments are compared with `f'` by `stein_incr`.  The discontinuity of
`f'` at `z` contributes the probability that `Bin(m-1,p)` lands in an interval of length one, which is at
most twice its largest mass; the elementary bound `bpmf_le_four_div_sqrt` controls that mass.

The file ends with the bound `eq_be` of the paper and with the two consequences the paper draws
from it: the mass bound with the paper's constant `C_λ = 1/√(2πλ(1-λ)) + 2B_λ`, and the tail estimate.
-/

open Finset Real Filter Topology

namespace NoisyVD

/-! ### Standardisation -/

/-- The standard deviation of `Bin(m,p)`. -/
noncomputable def sdev (m : ℕ) (p : ℝ) : ℝ := √((m : ℝ) * (p * (1 - p)))

/-- The standardised value of `k` under `Bin(m,p)`. -/
noncomputable def zscore (m : ℕ) (p : ℝ) (k : ℕ) : ℝ := ((k : ℝ) - m * p) / sdev m p

lemma sdev_pos {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < sdev m p := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  exact Real.sqrt_pos.2 (mul_pos hmr (mul_pos hp (by linarith)))

lemma sdev_mul_self {m : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    sdev m p * sdev m p = (m : ℝ) * (p * (1 - p)) :=
  Real.mul_self_sqrt (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hp (by linarith)))

/-- `Pr(Bin(m,p) ≤ y)`. -/
noncomputable def bcdf (m : ℕ) (p y : ℝ) : ℝ :=
  ∑ k ∈ range (m + 1), if (k : ℝ) ≤ y then bpmf m p k else 0

/-- `Pr(Bin(m,p) ≥ T)`. -/
noncomputable def btail (m : ℕ) (p : ℝ) (T : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1), if T ≤ i then bpmf m p i else 0

lemma bcdf_nonneg {m : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (y : ℝ) : 0 ≤ bcdf m p y := by
  refine Finset.sum_nonneg fun k _ => ?_
  split_ifs
  · exact bpmf_nonneg h0 h1
  · exact le_rfl

lemma bcdf_le_one {m : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (y : ℝ) : bcdf m p y ≤ 1 := by
  rw [← bpmf_sum m p]
  refine Finset.sum_le_sum fun k _ => ?_
  split_ifs
  · exact le_rfl
  · exact bpmf_nonneg h0 h1

/-- `Pr(X ≥ T) = 1 - Pr(X ≤ T - 1)`. -/
lemma btail_eq (m : ℕ) (p : ℝ) (T : ℕ) : btail m p T = 1 - bcdf m p ((T : ℝ) - 1) := by
  have h : btail m p T + bcdf m p ((T : ℝ) - 1) = ∑ k ∈ range (m + 1), bpmf m p k := by
    unfold btail bcdf
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : T ≤ i
    · have : ¬ ((i : ℝ) ≤ (T : ℝ) - 1) := by
        have h2 : (T : ℝ) ≤ i := by exact_mod_cast hi
        linarith
      simp [hi, this]
    · have : (i : ℝ) ≤ (T : ℝ) - 1 := by
        have h2 : i + 1 ≤ T := by omega
        have h3 : (i : ℝ) + 1 ≤ T := by exact_mod_cast h2
        linarith
      simp [hi, this]
  rw [bpmf_sum] at h
  linarith

/-- `Pr(X = k) = Pr(X ≤ k) - Pr(X ≤ k - 1)`. -/
lemma bpmf_eq_bcdf_sub (m k : ℕ) (p : ℝ) :
    bpmf m p k = bcdf m p (k : ℝ) - bcdf m p ((k : ℝ) - 1) := by
  unfold bcdf
  rw [← Finset.sum_sub_distrib]
  have key : ∀ i ∈ range (m + 1), ((if (i : ℝ) ≤ (k : ℝ) then bpmf m p i else 0)
      - if (i : ℝ) ≤ (k : ℝ) - 1 then bpmf m p i else 0) = if i = k then bpmf m p i else 0 := by
    intro i _
    by_cases hik : i = k
    · subst hik
      simp
    · rcases lt_or_gt_of_ne hik with h | h
      · have h1 : (i : ℝ) ≤ k := by exact_mod_cast h.le
        have h2 : (i : ℝ) ≤ (k : ℝ) - 1 := by
          have h3 : (i : ℝ) + 1 ≤ k := by exact_mod_cast h
          linarith
        simp [hik, h1, h2]
      · have h1 : ¬ (i : ℝ) ≤ k := by
          have h3 : (k : ℝ) < i := by exact_mod_cast h
          linarith
        have h2 : ¬ (i : ℝ) ≤ (k : ℝ) - 1 := by
          have h3 : (k : ℝ) < i := by exact_mod_cast h
          linarith
        simp [hik, h1, h2]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (range (m + 1)) k]
  by_cases hk : k ∈ range (m + 1)
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, bpmf_eq_zero_of_gt]
    rw [Finset.mem_range] at hk
    omega

/-! ### Mills' ratio -/

/-- `(1 - Φ(w))/φ(w)`, Mills' ratio. -/
noncomputable def millsB (w : ℝ) : ℝ := (1 - Phi w) / phi w

/-- `Φ(w)/φ(w)`, which equals `millsB (-w)`. -/
noncomputable def millsA (w : ℝ) : ℝ := Phi w / phi w

lemma millsA_eq (w : ℝ) : millsA w = millsB (-w) := by
  unfold millsA millsB
  rw [Phi_neg, phi_neg]
  ring

lemma millsB_nonneg (w : ℝ) : 0 ≤ millsB w :=
  div_nonneg (by linarith [Phi_le_one w]) (phi_pos w).le

lemma millsA_nonneg (w : ℝ) : 0 ≤ millsA w := div_nonneg (Phi_nonneg w) (phi_pos w).le

lemma hasDerivAt_millsB (x : ℝ) : HasDerivAt millsB (x * millsB x - 1) x := by
  have h : HasDerivAt millsB (((0 - phi x) * phi x - (1 - Phi x) * (-x * phi x)) / phi x ^ 2) x :=
    ((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_Phi x)).fun_div (hasDerivAt_phi x)
      (phi_pos x).ne'
  refine h.congr_deriv ?_
  have := (phi_pos x).ne'
  unfold millsB
  field_simp
  ring

lemma hasDerivAt_millsA (x : ℝ) : HasDerivAt millsA (x * millsA x + 1) x := by
  have h : HasDerivAt millsA ((phi x * phi x - Phi x * (-x * phi x)) / phi x ^ 2) x :=
    (hasDerivAt_Phi x).fun_div (hasDerivAt_phi x) (phi_pos x).ne'
  refine h.congr_deriv ?_
  have := (phi_pos x).ne'
  unfold millsA
  field_simp
  ring

lemma continuous_millsB : Continuous millsB :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_millsB x).continuousAt

/-- Mills' inequality: `w (1 - Φ(w)) ≤ φ(w)` for `w > 0`. -/
lemma mills {w : ℝ} (hw : 0 < w) : w * (1 - Phi w) ≤ phi w := by
  let k : ℝ → ℝ := fun x => 1 - Phi x - phi x / x
  have hderiv : ∀ x, 0 < x → HasDerivAt k (phi x / x ^ 2) x := by
    intro x hx
    have h1 : HasDerivAt k (0 - phi x - ((-x * phi x) * x - phi x * 1) / x ^ 2) x :=
      ((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_Phi x)).fun_sub
        ((hasDerivAt_phi x).fun_div (hasDerivAt_id' x) hx.ne')
    refine h1.congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn k (Set.Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) (fun x hx => ?_) (fun x hx => ?_)
      (fun x hx => ?_)
    · exact (hderiv x hx).continuousAt.continuousWithinAt
    · rw [interior_Ioi] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi] at hx
      rw [(hderiv x hx).deriv]
      exact div_nonneg (phi_pos x).le (by positivity)
  have hlim : Tendsto k atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 - Phi x) atTop (𝓝 0) := by
      simpa using tendsto_Phi_atTop.const_sub 1
    have h2 : Tendsto (fun x : ℝ => phi x / x) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ (Tendsto.const_div_atTop tendsto_id (phi 0))
      · filter_upwards [eventually_gt_atTop 0] with x hx
        exact div_nonneg (phi_pos x).le hx.le
      · filter_upwards [eventually_gt_atTop 0] with x hx
        exact div_le_div_of_nonneg_right (phi_le x) hx.le
    simpa using h1.sub h2
  have hk : k w ≤ 0 := ge_of_tendsto hlim ((eventually_ge_atTop w).mono fun x hx =>
    hmono hw (lt_of_lt_of_le hw hx) hx)
  have h3 : 1 - Phi w ≤ phi w / w := by
    have : 1 - Phi w - phi w / w ≤ 0 := hk
    linarith
  rwa [le_div_iff₀ hw, mul_comm] at h3

lemma mul_millsB_le {w : ℝ} (hw : 0 ≤ w) : w * millsB w ≤ 1 := by
  rcases hw.eq_or_lt with rfl | hw
  · simp
  · unfold millsB
    rw [← mul_div_assoc, div_le_one (phi_pos w)]
    exact mills hw

/-- `millsB` is largest at zero on the nonnegative half-line. -/
lemma millsB_le {w : ℝ} (hw : 0 ≤ w) : millsB w ≤ millsB 0 := by
  have hanti : AntitoneOn millsB (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) continuous_millsB.continuousOn
      (fun x _ => (hasDerivAt_millsB x).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
    rw [interior_Ici] at hx
    rw [(hasDerivAt_millsB x).deriv]
    linarith [mul_millsB_le (le_of_lt hx)]
  exact hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hw) hw

/-- The bound on the Stein solution: `c = (1 - Φ(0))/φ(0) = √(2π)/2`. -/
noncomputable def steinC : ℝ := millsB 0

lemma steinC_nonneg : 0 ≤ steinC := millsB_nonneg 0

lemma steinC_le : steinC ≤ 3 / 2 := by
  unfold steinC millsB
  rw [Phi_zero, phi_zero]
  have hs : √(2 * π) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  have hp := sqrt_two_pi_pos
  rw [div_inv_eq_mul]
  nlinarith

/-- The key inequality behind the bound on `f'`: `(1 - Φ(v))(1 + v Φ(v)/φ(v)) ≤ 1` for `v ≥ 0`. -/
lemma mills_key {v : ℝ} (hv : 0 ≤ v) : (1 - Phi v) * (1 + v * millsA v) ≤ 1 := by
  have h1 := mul_millsB_le hv
  have h2 : (1 - Phi v) * (1 + v * millsA v) = (1 - Phi v) + Phi v * (v * millsB v) := by
    unfold millsA millsB
    have := (phi_pos v).ne'
    field_simp
  rw [h2]
  have h3 : Phi v * (v * millsB v) ≤ Phi v * 1 := mul_le_mul_of_nonneg_left h1 (Phi_nonneg v)
  linarith

/-! ### The Stein solution -/

/-- The left piece of the Stein solution. -/
noncomputable def steinL (z w : ℝ) : ℝ := (1 - Phi z) * millsA w

/-- The right piece of the Stein solution. -/
noncomputable def steinR (z w : ℝ) : ℝ := Phi z * millsB w

/-- The bounded solution of `f'(w) - w f(w) = 1_{w ≤ z} - Φ(z)`. -/
noncomputable def stein (z w : ℝ) : ℝ := if w ≤ z then steinL z w else steinR z w

/-- The derivative of `stein z`, with its left value at the kink: `w f(w) + 1_{w ≤ z} - Φ(z)`. -/
noncomputable def steinD (z w : ℝ) : ℝ := w * stein z w + (if w ≤ z then 1 else 0) - Phi z

lemma steinL_self (z : ℝ) : steinL z z = steinR z z := by
  unfold steinL steinR millsA millsB
  ring

lemma stein_of_le {z w : ℝ} (h : w ≤ z) : stein z w = steinL z w := ite_eq_left h

lemma stein_of_ge {z w : ℝ} (h : z ≤ w) : stein z w = steinR z w := by
  rcases h.eq_or_lt with rfl | h
  · rw [stein_of_le le_rfl, steinL_self]
  · exact ite_eq_right (not_le.2 h)

lemma hasDerivAt_steinL (z x : ℝ) :
    HasDerivAt (steinL z) (x * steinL z x + (1 - Phi z)) x := by
  have h : HasDerivAt (steinL z) ((1 - Phi z) * (x * millsA x + 1)) x :=
    (hasDerivAt_millsA x).const_mul (1 - Phi z)
  refine h.congr_deriv ?_
  unfold steinL
  ring

lemma hasDerivAt_steinR (z x : ℝ) : HasDerivAt (steinR z) (x * steinR z x - Phi z) x := by
  have h : HasDerivAt (steinR z) (Phi z * (x * millsB x - 1)) x :=
    (hasDerivAt_millsB x).const_mul (Phi z)
  refine h.congr_deriv ?_
  unfold steinR
  ring

/-- `|f| ≤ c`, the left piece. -/
lemma abs_steinL_le {z w : ℝ} (h : w ≤ z) : |steinL z w| ≤ steinC := by
  have h0 : 0 ≤ steinL z w := mul_nonneg (by linarith [Phi_le_one z]) (millsA_nonneg w)
  rw [abs_of_nonneg h0]
  rcases le_total w 0 with hw | hw
  · have h1 : millsA w ≤ steinC := by
      rw [millsA_eq]
      exact millsB_le (by linarith)
    have h2 := Phi_nonneg z
    calc (1 - Phi z) * millsA w ≤ 1 * millsA w :=
          mul_le_mul_of_nonneg_right (by linarith) (millsA_nonneg w)
      _ ≤ steinC := by linarith
  · have h1 : 1 - Phi z ≤ 1 - Phi w := by linarith [Phi_mono h]
    have e : (1 - Phi w) * millsA w = Phi w * millsB w := by
      unfold millsA millsB
      ring
    calc (1 - Phi z) * millsA w ≤ (1 - Phi w) * millsA w :=
          mul_le_mul_of_nonneg_right h1 (millsA_nonneg w)
      _ = Phi w * millsB w := e
      _ ≤ 1 * millsB w := mul_le_mul_of_nonneg_right (Phi_le_one w) (millsB_nonneg w)
      _ ≤ steinC := by rw [one_mul]; exact millsB_le hw

/-- `|f| ≤ c`, the right piece. -/
lemma abs_steinR_le {z w : ℝ} (h : z ≤ w) : |steinR z w| ≤ steinC := by
  have h0 : 0 ≤ steinR z w := mul_nonneg (Phi_nonneg z) (millsB_nonneg w)
  rw [abs_of_nonneg h0]
  rcases le_total 0 w with hw | hw
  · calc Phi z * millsB w ≤ 1 * millsB w :=
          mul_le_mul_of_nonneg_right (Phi_le_one z) (millsB_nonneg w)
      _ ≤ steinC := by rw [one_mul]; exact millsB_le hw
  · have e : Phi w * millsB w = (1 - Phi w) * millsA w := by
      unfold millsA millsB
      ring
    have h1 : millsA w ≤ steinC := by
      rw [millsA_eq]
      exact millsB_le (by linarith)
    calc Phi z * millsB w ≤ Phi w * millsB w :=
          mul_le_mul_of_nonneg_right (Phi_mono h) (millsB_nonneg w)
      _ = (1 - Phi w) * millsA w := e
      _ ≤ 1 * millsA w :=
          mul_le_mul_of_nonneg_right (by linarith [Phi_nonneg w]) (millsA_nonneg w)
      _ ≤ steinC := by linarith

lemma abs_stein_le (z w : ℝ) : |stein z w| ≤ steinC := by
  rcases le_total w z with h | h
  · rw [stein_of_le h]
    exact abs_steinL_le h
  · rw [stein_of_ge h]
    exact abs_steinR_le h

/-- `|f'| ≤ 1`, the left piece. -/
lemma abs_steinL_deriv_le {z w : ℝ} (h : w ≤ z) : |w * steinL z w + (1 - Phi z)| ≤ 1 := by
  have e : w * steinL z w + (1 - Phi z) = (1 - Phi z) * (1 + w * millsA w) := by
    unfold steinL
    ring
  rw [e]
  have hz0 : 0 ≤ 1 - Phi z := by linarith [Phi_le_one z]
  have hz1 : 1 - Phi z ≤ 1 := by linarith [Phi_nonneg z]
  rcases le_total w 0 with hw | hw
  · have h1 : (-w) * millsB (-w) ≤ 1 := mul_millsB_le (by linarith)
    have h2 : w * millsA w = -((-w) * millsB (-w)) := by
      rw [millsA_eq]
      ring
    have h3 : 0 ≤ (-w) * millsB (-w) := mul_nonneg (by linarith) (millsB_nonneg _)
    have h4 : 0 ≤ 1 + w * millsA w := by linarith
    have h5 : 1 + w * millsA w ≤ 1 := by linarith
    rw [abs_of_nonneg (mul_nonneg hz0 h4)]
    calc (1 - Phi z) * (1 + w * millsA w) ≤ 1 * 1 := mul_le_mul hz1 h5 h4 zero_le_one
      _ = 1 := one_mul 1
  · have h4 : 0 ≤ 1 + w * millsA w := by
      have := mul_nonneg hw (millsA_nonneg w)
      linarith
    rw [abs_of_nonneg (mul_nonneg hz0 h4)]
    have h1 : 1 - Phi z ≤ 1 - Phi w := by linarith [Phi_mono h]
    exact (mul_le_mul_of_nonneg_right h1 h4).trans (mills_key hw)

/-- `|f'| ≤ 1`, the right piece. -/
lemma abs_steinR_deriv_le {z w : ℝ} (h : z ≤ w) : |w * steinR z w - Phi z| ≤ 1 := by
  have e : w * steinR z w - Phi z = -(Phi z * (1 - w * millsB w)) := by
    unfold steinR
    ring
  rw [e, abs_neg]
  have hz0 := Phi_nonneg z
  have hz1 := Phi_le_one z
  rcases le_total 0 w with hw | hw
  · have h1 := mul_millsB_le hw
    have h2 : 0 ≤ w * millsB w := mul_nonneg hw (millsB_nonneg w)
    rw [abs_of_nonneg (mul_nonneg hz0 (by linarith))]
    calc Phi z * (1 - w * millsB w) ≤ 1 * 1 :=
          mul_le_mul hz1 (by linarith) (by linarith) zero_le_one
      _ = 1 := one_mul 1
  · set v := -w with hv
    have hv0 : 0 ≤ v := by rw [hv]; linarith
    have e2 : 1 - w * millsB w = 1 + v * millsA v := by
      rw [millsA_eq, hv, neg_neg]
      ring
    rw [e2]
    have h4 : 0 ≤ 1 + v * millsA v := by
      have := mul_nonneg hv0 (millsA_nonneg v)
      linarith
    rw [abs_of_nonneg (mul_nonneg hz0 h4)]
    have h5 : Phi z ≤ 1 - Phi v := by
      have h6 := Phi_mono h
      have h7 : Phi w = 1 - Phi v := by
        rw [← Phi_neg, hv, neg_neg]
      linarith
    exact (mul_le_mul_of_nonneg_right h5 h4).trans (mills_key hv0)

lemma abs_steinD_le (z w : ℝ) : |steinD z w| ≤ 1 := by
  unfold steinD
  rcases le_or_gt w z with h | h
  · rw [stein_of_le h, ite_eq_left h]
    have := abs_steinL_deriv_le h
    rwa [show w * steinL z w + 1 - Phi z = w * steinL z w + (1 - Phi z) by ring]
  · rw [stein_of_ge h.le, ite_eq_right (not_le.2 h)]
    have := abs_steinR_deriv_le h.le
    rwa [show w * steinR z w + 0 - Phi z = w * steinR z w - Phi z by ring]

lemma steinL_lipschitz {z a b : ℝ} (ha : a ≤ z) (hb : b ≤ z) :
    |steinL z a - steinL z b| ≤ |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := steinL z)
    (f' := fun x => x * steinL z x + (1 - Phi z)) (s := Set.Iic z) (C := 1) (x := b) (y := a)
    (fun x _ => (hasDerivAt_steinL z x).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact abs_steinL_deriv_le hx)
    (convex_Iic z) hb ha
  simpa [Real.norm_eq_abs] using h

lemma steinR_lipschitz {z a b : ℝ} (ha : z ≤ a) (hb : z ≤ b) :
    |steinR z a - steinR z b| ≤ |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := steinR z)
    (f' := fun x => x * steinR z x - Phi z) (s := Set.Ici z) (C := 1) (x := b) (y := a)
    (fun x _ => (hasDerivAt_steinR z x).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact abs_steinR_deriv_le hx)
    (convex_Ici z) hb ha
  simpa [Real.norm_eq_abs] using h

/-- `f` is `1`-Lipschitz. -/
lemma stein_lipschitz (z a b : ℝ) : |stein z a - stein z b| ≤ |a - b| := by
  rcases le_total a z with ha | ha <;> rcases le_total b z with hb | hb
  · rw [stein_of_le ha, stein_of_le hb]
    exact steinL_lipschitz ha hb
  · rw [stein_of_le ha, stein_of_ge hb]
    have h1 := steinL_lipschitz ha le_rfl
    have h2 := steinR_lipschitz (z := z) le_rfl hb
    rw [steinL_self] at h1
    rw [abs_of_nonpos (show a - z ≤ 0 by linarith)] at h1
    rw [abs_of_nonpos (show z - b ≤ 0 by linarith)] at h2
    rw [abs_of_nonpos (show a - b ≤ 0 by linarith)]
    have := abs_sub_le (steinL z a) (steinR z z) (steinR z b)
    linarith
  · rw [stein_of_ge ha, stein_of_le hb]
    have h1 := steinR_lipschitz (z := z) ha le_rfl
    have h2 := steinL_lipschitz le_rfl hb
    rw [steinL_self] at h2
    rw [abs_of_nonneg (show 0 ≤ a - z by linarith)] at h1
    rw [abs_of_nonneg (show 0 ≤ z - b by linarith)] at h2
    rw [abs_of_nonneg (show 0 ≤ a - b by linarith)]
    have := abs_sub_le (steinR z a) (steinR z z) (steinL z b)
    linarith
  · rw [stein_of_ge ha, stein_of_ge hb]
    exact steinR_lipschitz ha hb

/-- An increment of a function with `g'(w) = w g(w) + κ`, compared with the derivative at any point. -/
lemma incr_of_ode {g : ℝ → ℝ} {κ a b v c : ℝ} (hab : a < b) (hv : v ∈ Set.Icc a b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt g (x * g x + κ) x) (hc : ∀ x ∈ Set.Icc a b, |g x| ≤ c)
    (hL : ∀ x ∈ Set.Icc a b, |g x - g v| ≤ |x - v|) :
    |g b - g a - (b - a) * (v * g v + κ)| ≤ (b - a) * (b - a) * (c + |v|) := by
  have hcont : ContinuousOn g (Set.Icc a b) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g (fun x => x * g x + κ) hab hcont
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
  have hδ : 0 < b - a := by linarith
  have hΞ : ξ ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hξ
  have e : g b - g a = (b - a) * (ξ * g ξ + κ) := by
    rw [hξe]
    field_simp
  have hdiff : |ξ - v| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hξ.1, hξ.2, hv.1, hv.2]
  have h1 : |(ξ - v) * g ξ| ≤ (b - a) * c := by
    rw [abs_mul]
    exact mul_le_mul hdiff (hc ξ hΞ) (abs_nonneg _) hδ.le
  have h2 : |v * (g ξ - g v)| ≤ |v| * (b - a) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hL ξ hΞ).trans hdiff) (abs_nonneg _)
  have h3 : |ξ * g ξ - v * g v| ≤ (b - a) * (c + |v|) := by
    have e2 : ξ * g ξ - v * g v = (ξ - v) * g ξ + v * (g ξ - g v) := by ring
    rw [e2]
    calc |(ξ - v) * g ξ + v * (g ξ - g v)| ≤ |(ξ - v) * g ξ| + |v * (g ξ - g v)| := abs_add_le _ _
      _ ≤ (b - a) * c + |v| * (b - a) := add_le_add h1 h2
      _ = (b - a) * (c + |v|) := by ring
  have e3 : g b - g a - (b - a) * (v * g v + κ) = (b - a) * (ξ * g ξ - v * g v) := by
    rw [e]
    ring
  rw [e3, abs_mul, abs_of_pos hδ]
  calc (b - a) * |ξ * g ξ - v * g v| ≤ (b - a) * ((b - a) * (c + |v|)) :=
        mul_le_mul_of_nonneg_left h3 hδ.le
    _ = (b - a) * (b - a) * (c + |v|) := by ring

/-- An increment of `f` compared with `f'` at a point of the interval.  The kink at `z` costs `2δ`. -/
lemma stein_incr {z a b v : ℝ} (hab : a < b) (hv : v ∈ Set.Icc a b) :
    |stein z b - stein z a - (b - a) * steinD z v|
      ≤ (b - a) * (b - a) * (steinC + |v|) + (if a ≤ z ∧ z ≤ b then 2 * (b - a) else 0) := by
  have hδ : 0 < b - a := by linarith
  have hnn : 0 ≤ (b - a) * (b - a) * (steinC + |v|) :=
    mul_nonneg (mul_self_nonneg _) (add_nonneg steinC_nonneg (abs_nonneg _))
  by_cases hbad : a ≤ z ∧ z ≤ b
  · rw [ite_eq_left hbad]
    have h1 : |stein z b - stein z a| ≤ b - a := by
      refine (stein_lipschitz z b a).trans (le_of_eq (abs_of_pos hδ))
    have h2 : |(b - a) * steinD z v| ≤ b - a := by
      rw [abs_mul, abs_of_pos hδ]
      calc (b - a) * |steinD z v| ≤ (b - a) * 1 :=
            mul_le_mul_of_nonneg_left (abs_steinD_le z v) hδ.le
        _ = b - a := mul_one _
    have h3 := abs_sub (stein z b - stein z a) ((b - a) * steinD z v)
    linarith
  · rw [ite_eq_right hbad, add_zero]
    rcases not_and_or.1 hbad with h | h
    · -- `z < a`: the right piece on the whole interval
      push Not at h
      have hmem : ∀ x ∈ Set.Icc a b, z ≤ x := fun x hx => h.le.trans hx.1
      have hb := stein_of_ge (hmem b ⟨hab.le, le_rfl⟩)
      have ha := stein_of_ge (hmem a ⟨le_rfl, hab.le⟩)
      have hD : steinD z v = v * steinR z v + -Phi z := by
        unfold steinD
        rw [stein_of_ge (hmem v hv), ite_eq_right (not_le.2 (lt_of_lt_of_le h hv.1))]
        ring
      rw [hb, ha, hD]
      refine incr_of_ode hab hv (fun x _ => ?_) (fun x hx => abs_steinR_le (hmem x hx))
        (fun x hx => steinR_lipschitz (hmem x hx) (hmem v hv))
      have := hasDerivAt_steinR z x
      rwa [show x * steinR z x - Phi z = x * steinR z x + -Phi z by ring] at this
    · -- `b < z`: the left piece on the whole interval
      push Not at h
      have hmem : ∀ x ∈ Set.Icc a b, x ≤ z := fun x hx => hx.2.trans h.le
      have hb := stein_of_le (hmem b ⟨hab.le, le_rfl⟩)
      have ha := stein_of_le (hmem a ⟨le_rfl, hab.le⟩)
      have hD : steinD z v = v * steinL z v + (1 - Phi z) := by
        unfold steinD
        rw [stein_of_le (hmem v hv), ite_eq_left (hmem v hv)]
        ring
      rw [hb, ha, hD]
      exact incr_of_ode hab hv (fun x _ => hasDerivAt_steinL z x)
        (fun x hx => abs_steinL_le (hmem x hx))
        (fun x hx => steinL_lipschitz (hmem x hx) (hmem v hv))

/-! ### Binomial identities -/

/-- Pascal's rule for the binomial probabilities. -/
lemma bpmf_succ_succ (m j : ℕ) (p : ℝ) :
    bpmf (m + 1) p (j + 1) = p * bpmf m p j + (1 - p) * bpmf m p (j + 1) := by
  rcases lt_trichotomy j m with h | rfl | h
  · have e1 : m + 1 - (j + 1) = m - j := by omega
    have e2 : m - j = (m - (j + 1)) + 1 := by omega
    unfold bpmf
    rw [Nat.choose_succ_succ, e1, e2]
    have e3 : m - (j + 1) + 1 - (j + 1 - (j + 1)) = m - (j + 1) + 1 := by omega
    push_cast
    rw [pow_succ p j, pow_succ (1 - p) (m - (j + 1))]
    ring
  · unfold bpmf
    simp [Nat.choose_succ_self, pow_succ]
    ring
  · rw [bpmf_eq_zero_of_gt (by omega), bpmf_eq_zero_of_gt h, bpmf_eq_zero_of_gt (by omega)]
    ring

lemma bpmf_zero_succ (m : ℕ) (p : ℝ) : bpmf (m + 1) p 0 = (1 - p) * bpmf m p 0 := by
  simp [bpmf, pow_succ]
  ring

/-- `Bin(m+1,p)` is `Bin(m,p)` plus an independent Bernoulli(`p`): `E h(X) = E[p h(X'+1) + q h(X')]`. -/
lemma sum_bpmf_split (m : ℕ) (p : ℝ) (h : ℕ → ℝ) :
    ∑ k ∈ range (m + 2), bpmf (m + 1) p k * h k
      = ∑ j ∈ range (m + 1), bpmf m p j * (p * h (j + 1) + (1 - p) * h j) := by
  rw [Finset.sum_range_succ']
  simp_rw [bpmf_succ_succ, bpmf_zero_succ]
  have h1 : ∑ j ∈ range (m + 1), bpmf m p j * ((1 - p) * h j)
      = (1 - p) * bpmf m p 0 * h 0
        + ∑ j ∈ range (m + 1), (1 - p) * bpmf m p (j + 1) * h (j + 1) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ _ m]
    rw [bpmf_eq_zero_of_gt (Nat.lt_succ_self m)]
    simp only [mul_zero, zero_mul, add_zero]
    rw [add_comm]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      ring
  have h2 : ∑ j ∈ range (m + 1), bpmf m p j * (p * h (j + 1) + (1 - p) * h j)
      = ∑ j ∈ range (m + 1), p * bpmf m p j * h (j + 1)
        + ∑ j ∈ range (m + 1), bpmf m p j * ((1 - p) * h j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, h1]
  have h3 : ∑ j ∈ range (m + 1), (p * bpmf m p j + (1 - p) * bpmf m p (j + 1)) * h (j + 1)
      = ∑ j ∈ range (m + 1), p * bpmf m p j * h (j + 1)
        + ∑ j ∈ range (m + 1), (1 - p) * bpmf m p (j + 1) * h (j + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h3]
  ring

/-- `(j+1) Pr(Bin(m+1,p) = j+1) = (m+1) p Pr(Bin(m,p) = j)`. -/
lemma succ_mul_bpmf_succ (m j : ℕ) (p : ℝ) :
    ((j : ℝ) + 1) * bpmf (m + 1) p (j + 1) = ((m : ℝ) + 1) * p * bpmf m p j := by
  by_cases hj : j ≤ m
  · have e1 : m + 1 - (j + 1) = m - j := by omega
    have h := Nat.add_one_mul_choose_eq m j
    have h' : ((m : ℝ) + 1) * (m.choose j : ℝ) = ((m + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
      exact_mod_cast h
    unfold bpmf
    rw [e1, pow_succ p j]
    calc ((j : ℝ) + 1) * (((m + 1).choose (j + 1) : ℝ) * (p ^ j * p) * (1 - p) ^ (m - j))
        = (((m + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1)) * (p ^ j * p * (1 - p) ^ (m - j)) := by ring
      _ = (((m : ℝ) + 1) * (m.choose j : ℝ)) * (p ^ j * p * (1 - p) ^ (m - j)) := by rw [h']
      _ = _ := by ring
  · rw [bpmf_eq_zero_of_gt (by omega), bpmf_eq_zero_of_gt (by omega)]
    ring

/-- The Stein identity: `E[(X - mp) g(X)] = m p q E[g(X'+1) - g(X')]`, for `X ~ Bin(m,p)`,
`X' ~ Bin(m-1,p)`. -/
lemma sum_stein_identity (m : ℕ) (p : ℝ) (g : ℕ → ℝ) :
    ∑ k ∈ range (m + 2), bpmf (m + 1) p k * (((k : ℝ) - ((m : ℝ) + 1) * p) * g k)
      = ((m : ℝ) + 1) * (p * (1 - p)) * ∑ j ∈ range (m + 1), bpmf m p j * (g (j + 1) - g j) := by
  have h1 : ∑ k ∈ range (m + 2), bpmf (m + 1) p k * ((k : ℝ) * g k)
      = ((m : ℝ) + 1) * p * ∑ j ∈ range (m + 1), bpmf m p j * g (j + 1) := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    have := succ_mul_bpmf_succ m j p
    calc bpmf (m + 1) p (j + 1) * (((j : ℝ) + 1) * g (j + 1))
        = (((j : ℝ) + 1) * bpmf (m + 1) p (j + 1)) * g (j + 1) := by ring
      _ = _ := by rw [this]; ring
  have h2 := sum_bpmf_split m p g
  have h3 : ∑ k ∈ range (m + 2), bpmf (m + 1) p k * (((k : ℝ) - ((m : ℝ) + 1) * p) * g k)
      = ∑ k ∈ range (m + 2), bpmf (m + 1) p k * ((k : ℝ) * g k)
        - ((m : ℝ) + 1) * p * ∑ k ∈ range (m + 2), bpmf (m + 1) p k * g k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h3, h1, h2, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- At most two consecutive counts can lie in an interval of length one. -/
lemma sum_bad_le {m : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (y : ℝ) {K : ℝ}
    (hK : ∀ k, bpmf m p k ≤ K) :
    ∑ j ∈ range (m + 1), bpmf m p j * (if (j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1 then 1 else 0) ≤ 2 * K := by
  set j0 : ℕ := ⌈y - 1⌉₊ with hj0
  have hsub : (range (m + 1)).filter (fun j : ℕ => (j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1) ⊆ {j0, j0 + 1} := by
    intro j hj
    obtain ⟨_, hj1, hj2⟩ := Finset.mem_filter.1 hj
    have hlo : j0 ≤ j := Nat.ceil_le.2 (by linarith)
    have hhi : (j : ℝ) ≤ (j0 : ℝ) + 1 := by
      have := Nat.le_ceil (y - 1)
      rw [← hj0] at this
      linarith
    have hhi' : j ≤ j0 + 1 := by exact_mod_cast hhi
    have : j = j0 ∨ j = j0 + 1 := by omega
    simpa using this
  calc ∑ j ∈ range (m + 1), bpmf m p j * (if (j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1 then 1 else 0)
      = ∑ j ∈ (range (m + 1)).filter (fun j : ℕ => (j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1), bpmf m p j := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ j ∈ ({j0, j0 + 1} : Finset ℕ), bpmf m p j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => bpmf_nonneg h0 h1
    _ = bpmf m p j0 + bpmf m p (j0 + 1) := by
        rw [Finset.sum_pair (by omega)]
    _ ≤ 2 * K := by linarith [hK j0, hK (j0 + 1)]

/-- `E|X - mp|/σ ≤ 1`. -/
lemma sum_abs_standardised_le {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∑ k ∈ range (m + 1), bpmf m p k * |((k : ℝ) - m * p) / sdev m p| ≤ 1 := by
  have hσ := sdev_pos hm hp hp1
  have hσ2 := sdev_mul_self (m := m) hp.le hp1.le
  have hv := bpmf_variance m p
  have hb : ∀ k ∈ range (m + 1), bpmf m p k * |((k : ℝ) - m * p) / sdev m p|
      ≤ bpmf m p k * (1 / 2) + (((m : ℝ) * p - k) ^ 2 * bpmf m p k) / (2 * (sdev m p * sdev m p)) := by
    intro k _
    have h0 := bpmf_nonneg (m := m) (k := k) hp.le hp1.le
    set x := ((k : ℝ) - m * p) / sdev m p with hx
    have h1 : |x| ≤ 1 / 2 + x ^ 2 / 2 := by
      have := sq_nonneg (|x| - 1)
      rw [sub_sq, sq_abs] at this
      nlinarith
    have h2 : x ^ 2 = ((m : ℝ) * p - k) ^ 2 / (sdev m p * sdev m p) := by
      rw [hx, div_pow]
      congr 1
      · ring
      · ring
    calc bpmf m p k * |x| ≤ bpmf m p k * (1 / 2 + x ^ 2 / 2) := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := by
          rw [h2]
          field_simp
  refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, bpmf_sum, ← Finset.sum_div, hv, hσ2]
  have hne : (m : ℝ) * (p * (1 - p)) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have := mul_pos hp (show 0 < 1 - p by linarith)
    positivity
  field_simp
  ring

/-! ### The theorem -/

/-- The main estimate, for `m + 1` summands with `m ≥ 1`. -/
lemma stein_bound {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (z : ℝ) :
    |bcdf (m + 1) p (((m + 1 : ℕ) : ℝ) * p + z * sdev (m + 1) p) - Phi z|
      ≤ (steinC + 1) / sdev (m + 1) p + 16 / √((m : ℝ) * (p * (1 - p))) := by
  have hq : 0 < 1 - p := by linarith
  have hpq : 0 < p * (1 - p) := mul_pos hp hq
  set M : ℝ := ((m + 1 : ℕ) : ℝ) with hM
  have hMe : M = (m : ℝ) + 1 := by rw [hM]; push_cast; rfl
  set σ := sdev (m + 1) p with hσdef
  have hσ : 0 < σ := sdev_pos (by omega) hp hp1
  have hσ2 : σ * σ = M * (p * (1 - p)) := sdev_mul_self hp.le hp1.le
  set δ : ℝ := 1 / σ with hδ
  have hδpos : 0 < δ := by positivity
  let x : ℕ → ℝ := fun k => ((k : ℝ) - M * p) / σ
  have hxsucc : ∀ j : ℕ, x (j + 1) - x j = δ := by
    intro j
    simp only [x, hδ]
    push_cast
    field_simp
    ring
  let g : ℕ → ℝ := fun k => stein z (x k)
  let D : ℕ → ℝ := fun k => steinD z (x k)
  let y : ℝ := M * p + z * σ
  have hxy : ∀ k : ℕ, x k ≤ z ↔ (k : ℝ) ≤ y := by
    intro k
    simp only [x, y]
    rw [div_le_iff₀ hσ]
    constructor <;> intro h <;> linarith
  -- rewrite the difference through `D - x g`
  have hdiff : bcdf (m + 1) p y - Phi z
      = ∑ k ∈ range (m + 2), bpmf (m + 1) p k * D k
        - ∑ k ∈ range (m + 2), bpmf (m + 1) p k * (x k * g k) := by
    rw [← Finset.sum_sub_distrib]
    have h1 : Phi z = ∑ k ∈ range (m + 2), bpmf (m + 1) p k * Phi z := by
      rw [← Finset.sum_mul, bpmf_sum, one_mul]
    rw [h1]
    unfold bcdf
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [D, g, steinD]
    by_cases hk : x k ≤ z
    · have := (hxy k).1 hk
      simp only [this, hk, ite_true]
      ring
    · have h2 : ¬ (k : ℝ) ≤ y := fun h => hk ((hxy k).2 h)
      simp only [h2, hk, ite_false]
      ring
  -- the Stein identity
  have hstein : ∑ k ∈ range (m + 2), bpmf (m + 1) p k * (x k * g k)
      = σ * ∑ j ∈ range (m + 1), bpmf m p j * (g (j + 1) - g j) := by
    have h1 := sum_stein_identity m p g
    have h2 : ∑ k ∈ range (m + 2), bpmf (m + 1) p k * (x k * g k)
        = (1 / σ) * ∑ k ∈ range (m + 2), bpmf (m + 1) p k * (((k : ℝ) - ((m : ℝ) + 1) * p) * g k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [x]
      rw [hMe]
      field_simp
    rw [h2, h1, ← hMe, ← hσ2]
    field_simp
  have hsplit := sum_bpmf_split m p D
  -- the combination
  have hcomb : bcdf (m + 1) p y - Phi z = ∑ j ∈ range (m + 1), bpmf m p j *
      (p * (D (j + 1) - σ * (g (j + 1) - g j)) + (1 - p) * (D j - σ * (g (j + 1) - g j))) := by
    rw [hdiff, hstein, hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- the term bound
  let bad : ℕ → ℝ := fun j => if (j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1 then 1 else 0
  have hbadiff : ∀ j : ℕ, (x j ≤ z ∧ z ≤ x (j + 1)) ↔ ((j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1) := by
    intro j
    rw [hxy j]
    simp only [x, y]
    rw [le_div_iff₀ hσ]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  have hterm : ∀ j v, v ∈ Set.Icc (x j) (x (j + 1)) →
      |steinD z v - σ * (g (j + 1) - g j)| ≤ δ * (steinC + |v|) + 2 * bad j := by
    intro j v hv
    have hab : x j < x (j + 1) := by linarith [hxsucc j]
    have h1 := stein_incr (z := z) hab hv
    rw [hxsucc j] at h1
    have e : steinD z v - σ * (g (j + 1) - g j)
        = -(σ * (stein z (x (j + 1)) - stein z (x j) - δ * steinD z v)) := by
      simp only [g, hδ]
      field_simp
      ring
    rw [e, abs_neg, abs_mul, abs_of_pos hσ]
    have hbadsimp : (if x j ≤ z ∧ z ≤ x (j + 1) then 2 * δ else 0) = 2 * δ * bad j := by
      simp only [bad]
      by_cases hb : x j ≤ z ∧ z ≤ x (j + 1)
      · rw [ite_eq_left hb, ite_eq_left ((hbadiff j).1 hb)]
        ring
      · rw [ite_eq_right hb, ite_eq_right (fun h => hb ((hbadiff j).2 h))]
        ring
    rw [hbadsimp] at h1
    calc σ * |stein z (x (j + 1)) - stein z (x j) - δ * steinD z v|
        ≤ σ * (δ * δ * (steinC + |v|) + 2 * δ * bad j) := mul_le_mul_of_nonneg_left h1 hσ.le
      _ = δ * (steinC + |v|) + 2 * bad j := by
          simp only [hδ]
          field_simp
  -- sum the term bound
  have hbp : ∀ j, 0 ≤ bpmf m p j := fun j => bpmf_nonneg hp.le hp1.le
  have hsum : |bcdf (m + 1) p y - Phi z| ≤ ∑ j ∈ range (m + 1), bpmf m p j *
      (p * (δ * (steinC + |x (j + 1)|) + 2 * bad j) + (1 - p) * (δ * (steinC + |x j|) + 2 * bad j)) := by
    rw [hcomb]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hbp j)]
    refine mul_le_mul_of_nonneg_left ?_ (hbp j)
    have hab : x j ≤ x (j + 1) := by linarith [hxsucc j]
    have t1 := hterm j (x (j + 1)) ⟨hab, le_rfl⟩
    have t2 := hterm j (x j) ⟨le_rfl, hab⟩
    calc |p * (D (j + 1) - σ * (g (j + 1) - g j)) + (1 - p) * (D j - σ * (g (j + 1) - g j))|
        ≤ |p * (D (j + 1) - σ * (g (j + 1) - g j))| + |(1 - p) * (D j - σ * (g (j + 1) - g j))| :=
          abs_add_le _ _
      _ = p * |D (j + 1) - σ * (g (j + 1) - g j)| + (1 - p) * |D j - σ * (g (j + 1) - g j)| := by
          rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hq]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left t1 hp.le) (mul_le_mul_of_nonneg_left t2 hq.le)
  -- the two sums
  have hs1 : ∑ j ∈ range (m + 1), bpmf m p j * (p * |x (j + 1)| + (1 - p) * |x j|) ≤ 1 := by
    have h1 := sum_bpmf_split m p (fun k => |x k|)
    rw [← h1]
    have h2 := sum_abs_standardised_le (m := m + 1) (by omega) hp hp1
    exact h2
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set K : ℝ := 4 / √((m : ℝ) * (p * (1 - p))) with hK
  have hs2 : ∑ j ∈ range (m + 1), bpmf m p j * bad j ≤ 2 * K :=
    sum_bad_le hp.le hp1.le y (fun k => bpmf_le_four_div_sqrt hm hp hp1 k)
  have hexpand : ∑ j ∈ range (m + 1), bpmf m p j *
      (p * (δ * (steinC + |x (j + 1)|) + 2 * bad j) + (1 - p) * (δ * (steinC + |x j|) + 2 * bad j))
      = δ * steinC + δ * ∑ j ∈ range (m + 1), bpmf m p j * (p * |x (j + 1)| + (1 - p) * |x j|)
        + 2 * ∑ j ∈ range (m + 1), bpmf m p j * bad j := by
    have h1 : δ * steinC = ∑ j ∈ range (m + 1), bpmf m p j * (δ * steinC) := by
      rw [← Finset.sum_mul, bpmf_sum, one_mul]
    rw [h1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexpand] at hsum
  have hfin : δ * steinC + δ * ∑ j ∈ range (m + 1), bpmf m p j * (p * |x (j + 1)| + (1 - p) * |x j|)
      + 2 * ∑ j ∈ range (m + 1), bpmf m p j * bad j ≤ (steinC + 1) / σ + 16 / √((m : ℝ) * (p * (1 - p))) := by
    have e1 : (steinC + 1) / σ = δ * steinC + δ * 1 := by
      simp only [hδ]
      field_simp
    have e2 : 16 / √((m : ℝ) * (p * (1 - p))) = 2 * (2 * K) := by
      rw [hK]
      ring
    rw [e1, e2]
    have h3 : δ * ∑ j ∈ range (m + 1), bpmf m p j * (p * |x (j + 1)| + (1 - p) * |x j|) ≤ δ * 1 :=
      mul_le_mul_of_nonneg_left hs1 hδpos.le
    linarith
  exact hsum.trans hfin

/-- The third absolute central moment `E|ξ - p|³` of a Bernoulli(`p`) variable. -/
noncomputable def thirdMoment (p : ℝ) : ℝ := p * |1 - p| ^ 3 + (1 - p) * |0 - p| ^ 3

/-- `E|ξ - p|³ = p(1-p)(p² + (1-p)²)`, as in the paper. -/
lemma thirdMoment_eq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    thirdMoment p = p * (1 - p) * (p ^ 2 + (1 - p) ^ 2) := by
  unfold thirdMoment
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 - p), zero_sub, abs_neg, abs_of_nonneg h0]
  ring

/-- The universal constant `C_BE`. -/
noncomputable def CBE : ℝ := 52

/-- The ratio `E|ξ - p|³/(p(1-p))^{3/2}` in the Berry--Esseen bound. -/
noncomputable def beRatio (p : ℝ) : ℝ := thirdMoment p / ((p * (1 - p)) * √(p * (1 - p)))

lemma beRatio_eq {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    beRatio p = (p ^ 2 + (1 - p) ^ 2) / √(p * (1 - p)) := by
  unfold beRatio
  rw [thirdMoment_eq h0.le h1.le]
  have hpq : 0 < p * (1 - p) := mul_pos h0 (by linarith)
  have hs := Real.sqrt_pos.2 hpq
  field_simp

/-- **The Berry--Esseen Theorem for Bernoulli sums**: for `X ~ Bin(m,p)`, `σ² = m p (1-p)`,
`|Pr(X ≤ mp + zσ) - Φ(z)| ≤ C_BE E|ξ-p|³ / ((p(1-p))^{3/2} √m)`. -/
theorem berry_esseen_binomial {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (z : ℝ) :
    |bcdf m p ((m : ℝ) * p + z * sdev m p) - Phi z| ≤ CBE * beRatio p / √(m : ℝ) := by
  have hq : 0 < 1 - p := by linarith
  have hpq : 0 < p * (1 - p) := mul_pos hp hq
  have hspq : 0 < √(p * (1 - p)) := Real.sqrt_pos.2 hpq
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 hmr
  have hσ : 0 < sdev m p := sdev_pos hm hp hp1
  have hσe : sdev m p = √(m : ℝ) * √(p * (1 - p)) := Real.sqrt_mul hmr.le _
  -- `26/σ ≤` the claimed bound, because `p² + q² ≥ 1/2`
  have hratio : 26 / sdev m p ≤ CBE * beRatio p / √(m : ℝ) := by
    rw [beRatio_eq hp hp1, hσe]
    unfold CBE
    have h2 : (1 : ℝ) / 2 ≤ p ^ 2 + (1 - p) ^ 2 := by nlinarith [sq_nonneg (2 * p - 1)]
    have e1 : (52 : ℝ) * ((p ^ 2 + (1 - p) ^ 2) / √(p * (1 - p))) / √(m : ℝ)
        = (52 * (p ^ 2 + (1 - p) ^ 2)) / (√(m : ℝ) * √(p * (1 - p))) := by
      field_simp
    rw [e1]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  refine le_trans ?_ hratio
  by_cases hm1 : m = 1
  · subst hm1
    -- one summand: both terms lie in `[0,1]`
    have h1 := bcdf_le_one (m := 1) hp.le hp1.le (((1 : ℕ) : ℝ) * p + z * sdev 1 p)
    have h2 := bcdf_nonneg (m := 1) hp.le hp1.le (((1 : ℕ) : ℝ) * p + z * sdev 1 p)
    have hle : |bcdf 1 p (((1 : ℕ) : ℝ) * p + z * sdev 1 p) - Phi z| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [Phi_nonneg z, Phi_le_one z]
    refine hle.trans ?_
    rw [le_div_iff₀ hσ]
    have hsd : sdev 1 p ≤ 1 := by
      unfold sdev
      refine Real.sqrt_le_iff.2 ⟨zero_le_one, ?_⟩
      push_cast
      nlinarith
    linarith
  · -- at least two summands
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : 1 ≤ m' := by omega
    refine (stein_bound hm' hp hp1 z).trans ?_
    have hm'r : (0 : ℝ) < m' := by exact_mod_cast hm'
    have hC := steinC_le
    have hC0 := steinC_nonneg
    -- `√(m' pq) ≥ σ/√2`
    have hsqrt : sdev (m' + 1) p ≤ √2 * √((m' : ℝ) * (p * (1 - p))) := by
      unfold sdev
      rw [← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      push_cast
      have h3 : (1 : ℝ) ≤ m' := by exact_mod_cast hm'
      nlinarith
    have hs2 : √2 ≤ 1.42 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hspos : 0 < √((m' : ℝ) * (p * (1 - p))) := Real.sqrt_pos.2 (by positivity)
    have h1 : 16 / √((m' : ℝ) * (p * (1 - p))) ≤ 16 * 1.42 / sdev (m' + 1) p := by
      rw [div_le_div_iff₀ hspos hσ]
      have h4 : sdev (m' + 1) p ≤ 1.42 * √((m' : ℝ) * (p * (1 - p))) :=
        hsqrt.trans (mul_le_mul_of_nonneg_right hs2 hspos.le)
      nlinarith
    have h2 : (steinC + 1) / sdev (m' + 1) p ≤ (5 / 2) / sdev (m' + 1) p :=
      div_le_div_of_nonneg_right (by linarith) hσ.le
    have e : (5 / 2) / sdev (m' + 1) p + 16 * 1.42 / sdev (m' + 1) p ≤ 26 / sdev (m' + 1) p := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) hσ.le
    linarith

/-! ### The paper's consequences -/

/-- `B_λ = C_BE / √(λ(1-λ))`. -/
noncomputable def beConst (l : ℝ) : ℝ := CBE / √(l * (1 - l))

/-- For `p ∈ [l, 1-l]`, `p(1-p) ≥ l(1-l)`. -/
lemma mul_one_sub_ge {l p : ℝ} (hl : p ∈ Set.Icc l (1 - l)) :
    l * (1 - l) ≤ p * (1 - p) := by
  obtain ⟨h1, h2⟩ := hl
  nlinarith

/-- The ratio in the Berry--Esseen bound is at most `1/√(λ(1-λ))`, the paper's displayed bound. -/
lemma beRatio_le {l p : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2) (hp : p ∈ Set.Icc l (1 - l)) :
    beRatio p ≤ 1 / √(l * (1 - l)) := by
  have hp0 : 0 < p := lt_of_lt_of_le hl hp.1
  have hp1 : p < 1 := lt_of_le_of_lt hp.2 (by linarith)
  have hll : 0 < l * (1 - l) := mul_pos hl (by linarith)
  have hsl := Real.sqrt_pos.2 hll
  rw [beRatio_eq hp0 hp1]
  have h1 : p ^ 2 + (1 - p) ^ 2 ≤ 1 := by nlinarith
  have h2 : √(l * (1 - l)) ≤ √(p * (1 - p)) := Real.sqrt_le_sqrt (mul_one_sub_ge hp)
  exact div_le_div₀ zero_le_one h1 hsl h2

/-- Equation `eq_be` of the paper. -/
theorem eq_be {m : ℕ} (hm : 1 ≤ m) {l p : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2)
    (hp : p ∈ Set.Icc l (1 - l)) (z : ℝ) :
    |bcdf m p ((m : ℝ) * p + z * sdev m p) - Phi z| ≤ beConst l / √(m : ℝ) := by
  have hp0 : 0 < p := lt_of_lt_of_le hl hp.1
  have hp1 : p < 1 := lt_of_le_of_lt hp.2 (by linarith)
  refine (berry_esseen_binomial hm hp0 hp1 z).trans ?_
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  unfold beConst
  have h := mul_le_mul_of_nonneg_left (beRatio_le hl hl' hp) (show (0 : ℝ) ≤ CBE by norm_num [CBE])
  simpa [div_eq_mul_inv] using h

lemma beConst_pos {l : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2) : 0 < beConst l := by
  unfold beConst CBE
  have : 0 < l * (1 - l) := mul_pos hl (by linarith)
  positivity

/-- The constant `C_λ = 1/√(2πλ(1-λ)) + 2B_λ` of Lemma `lemma_local_binomial`. -/
noncomputable def massConst (l : ℝ) : ℝ := 1 / √(2 * π * (l * (1 - l))) + 2 * beConst l

lemma massConst_pos {l : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2) : 0 < massConst l := by
  unfold massConst
  have h1 := beConst_pos hl hl'
  have h2 : 0 < l * (1 - l) := mul_pos hl (by linarith)
  have h3 : 0 < √(2 * π * (l * (1 - l))) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- `σ_{m,p} ≥ √(m λ(1-λ))`. -/
lemma sqrt_mul_le_sdev {m : ℕ} {l p : ℝ} (hp : p ∈ Set.Icc l (1 - l)) :
    √(m : ℝ) * √(l * (1 - l)) ≤ sdev m p := by
  unfold sdev
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (mul_one_sub_ge hp) (Nat.cast_nonneg _))

/-- First claim of Lemma `lemma_local_binomial`: `Pr(X_{m,p} = k) ≤ C_λ/√m`.  As in the paper, subtract
`eq_be` at `(k-1-mp)/σ` from `eq_be` at `(k-mp)/σ` and use `Φ' = φ ≤ 1/√(2π)`. -/
theorem bpmf_le_massConst {m : ℕ} (hm : 1 ≤ m) {l p : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2)
    (hp : p ∈ Set.Icc l (1 - l)) (k : ℕ) : bpmf m p k ≤ massConst l / √(m : ℝ) := by
  have hp0 : 0 < p := lt_of_lt_of_le hl hp.1
  have hp1 : p < 1 := lt_of_le_of_lt hp.2 (by linarith)
  have hσ := sdev_pos hm hp0 hp1
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 hmr
  have hll : 0 < l * (1 - l) := mul_pos hl (by linarith)
  have hsl := Real.sqrt_pos.2 hll
  set z₁ : ℝ := ((k : ℝ) - m * p) / sdev m p with hz₁
  set z₀ : ℝ := ((k : ℝ) - 1 - m * p) / sdev m p with hz₀
  have e₁ : (m : ℝ) * p + z₁ * sdev m p = k := by
    rw [hz₁]
    field_simp
    ring
  have e₀ : (m : ℝ) * p + z₀ * sdev m p = (k : ℝ) - 1 := by
    rw [hz₀]
    field_simp
    ring
  have h₁ := abs_le.1 (eq_be hm hl hl' hp z₁)
  have h₀ := abs_le.1 (eq_be hm hl hl' hp z₀)
  rw [e₁] at h₁
  rw [e₀] at h₀
  have hΦ : Phi z₁ - Phi z₀ ≤ phi 0 * (1 / sdev m p) := by
    have h := abs_Phi_sub_le z₁ z₀
    have e : z₁ - z₀ = 1 / sdev m p := by
      rw [hz₁, hz₀]
      field_simp
      ring
    rw [e, abs_of_pos (by positivity : 0 < 1 / sdev m p)] at h
    exact (le_abs_self _).trans h
  have hφ : phi 0 * (1 / sdev m p) ≤ (1 / √(2 * π * (l * (1 - l)))) / √(m : ℝ) := by
    rw [phi_zero]
    have e : √(2 * π * (l * (1 - l))) = √(2 * π) * √(l * (1 - l)) :=
      Real.sqrt_mul (by positivity) _
    rw [e]
    have hτ := sqrt_two_pi_pos
    have hlow := sqrt_mul_le_sdev (m := m) hp
    have h1 : 1 / sdev m p ≤ 1 / (√(m : ℝ) * √(l * (1 - l))) :=
      one_div_le_one_div_of_le (by positivity) hlow
    calc (√(2 * π))⁻¹ * (1 / sdev m p) ≤ (√(2 * π))⁻¹ * (1 / (√(m : ℝ) * √(l * (1 - l)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp
  rw [bpmf_eq_bcdf_sub]
  have e : massConst l / √(m : ℝ)
      = (1 / √(2 * π * (l * (1 - l)))) / √(m : ℝ) + 2 * (beConst l / √(m : ℝ)) := by
    unfold massConst
    ring
  rw [e]
  linarith [h₁.2, h₀.1]

/-- Equation `eq_be` at `z = z_T - 1/σ`, the form the paper uses for the tail:
`|Pr(X ≥ T) - (1 - Φ(z_T))| ≤ B_λ/√m + φ(0)/σ`. -/
lemma abs_btail_sub_le {m : ℕ} (hm : 1 ≤ m) {l p : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2)
    (hp : p ∈ Set.Icc l (1 - l)) (T : ℕ) :
    |btail m p T - (1 - Phi (zscore m p T))| ≤ beConst l / √(m : ℝ) + phi 0 / sdev m p := by
  have hp0 : 0 < p := lt_of_lt_of_le hl hp.1
  have hp1 : p < 1 := lt_of_le_of_lt hp.2 (by linarith)
  have hσ := sdev_pos hm hp0 hp1
  set z : ℝ := zscore m p T with hz
  set z' : ℝ := z - 1 / sdev m p with hz'
  have e : (m : ℝ) * p + z' * sdev m p = (T : ℝ) - 1 := by
    rw [hz', hz]
    unfold zscore
    field_simp
    ring
  have h1 := eq_be hm hl hl' hp z'
  rw [e] at h1
  have h2 := abs_Phi_sub_le z' z
  have e2 : z' - z = -(1 / sdev m p) := by
    rw [hz']
    ring
  rw [e2, abs_neg, abs_of_pos (by positivity : 0 < 1 / sdev m p)] at h2
  rw [btail_eq]
  have e3 : 1 - bcdf m p ((T : ℝ) - 1) - (1 - Phi z)
      = -(bcdf m p ((T : ℝ) - 1) - Phi z') + (Phi z - Phi z') := by
    ring
  rw [e3]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_sub_comm (Phi z)]
  have e4 : phi 0 * (1 / sdev m p) = phi 0 / sdev m p := by ring
  linarith

/-- `sup_T |Pr(Bin(m,p) ≥ T) - (1 - Φ(z_T))| → 0`, uniformly in `p ∈ [l, 1-l]`. -/
theorem uniform_tail {l : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ p ∈ Set.Icc l (1 - l), ∀ T : ℕ,
      |btail m p T - (1 - Phi (zscore m p T))| < ε := by
  have hll : 0 < l * (1 - l) := mul_pos hl (by linarith)
  have hsl := Real.sqrt_pos.2 hll
  have hsq : Tendsto (fun m : ℕ => √(m : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  set A : ℝ := beConst l + phi 0 / √(l * (1 - l)) with hA
  have hlim : Tendsto (fun m : ℕ => A / √(m : ℝ)) atTop (𝓝 0) := Tendsto.const_div_atTop hsq A
  obtain ⟨N, hN⟩ := eventually_atTop.1 (((tendsto_order.1 hlim).2 ε hε).and (eventually_ge_atTop 1))
  refine ⟨N, fun m hm p hp T => ?_⟩
  obtain ⟨hlt, hm1⟩ := hN m hm
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm1
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 hmr
  have h1 := abs_btail_sub_le hm1 hl hl' hp T
  have h2 : phi 0 / sdev m p ≤ phi 0 / (√(m : ℝ) * √(l * (1 - l))) :=
    div_le_div_of_nonneg_left (phi_pos 0).le (by positivity) (sqrt_mul_le_sdev hp)
  have e : A / √(m : ℝ) = beConst l / √(m : ℝ) + phi 0 / (√(m : ℝ) * √(l * (1 - l))) := by
    rw [hA]
    field_simp
  rw [e] at hlt
  linarith

end NoisyVD
