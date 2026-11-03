import NoisyVD.Benchmarks

/-!
# Appendix `app_microfoundations`

* behavioural types and noisy communication imply Lemma `lemma_noise`;
* biased individuals: Proposition `prop_monotone`, Remark `remark_ex_post`,
  Proposition `prop_tie_breaking`.

Throughout, a rule over `{0,1}` is summarised by `x k = E_{a ∼ d(k)} a`, the probability of an
investigation following `k` reports.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

/-! ### Behavioural types -/

/-- **Behavioural types.** If an individual always reports with probability `ε₁`, never reports
with probability `ε₀` and is otherwise rational, reports occur with probability in
`[ε_*, 1 - ε_*]` for `ε_* = min {ε₁, ε₀}`, whatever the rational types do. -/
theorem behavioral_noise {ε₁ ε₀ τ : ℝ} (_h1 : 0 ≤ ε₁) (_h0 : 0 ≤ ε₀) (hsum : ε₁ + ε₀ ≤ 1)
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ε₁ + (1 - ε₁ - ε₀) * τ ∈ Icc (min ε₁ ε₀) (1 - min ε₁ ε₀) := by
  have hr : 0 ≤ 1 - ε₁ - ε₀ := by linarith
  have h2 := mul_nonneg hr hτ.1
  have h3 : (1 - ε₁ - ε₀) * τ ≤ 1 - ε₁ - ε₀ := by nlinarith [hτ.2]
  have h4 := min_le_left ε₁ ε₀
  have h5 := min_le_right ε₁ ε₀
  constructor <;> linarith

/-! ### Noisy communication -/

/-- **Noisy communication.** If `r_i = \tilde r_i` with probability `p ∈ (1/2, 1)` and otherwise the
report is flipped, reports occur with probability in `[1-p, p]` for every intended report mix `τ`. -/
theorem noisyComm_noise {p τ : ℝ} (hp : 1 / 2 < p) (_hp1 : p < 1) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    τ * p + (1 - τ) * (1 - p) ∈ Icc (1 - p) p := by
  have h1 := hτ.1
  have h2 := hτ.2
  constructor <;> nlinarith

/-- The noisy-communication incentive: the gross benefit of raising the *intended* report equals
`(2p - 1)` times the gross benefit of raising the *observed* report. -/
theorem noisyComm_incentive (p U₀ U₁ : ℝ) :
    (p * U₁ + (1 - p) * U₀) - ((1 - p) * U₁ + p * U₀) = (2 * p - 1) * (U₁ - U₀) := by
  ring

/-- Hence the noisy-communication incentive stays within the band of Lemma `lemma_pivotal`. -/
theorem noisyComm_band {p Δ h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hΔ : |Δ| ≤ h) :
    |(2 * p - 1) * Δ| ≤ h := by
  rw [abs_mul, abs_of_pos (by linarith)]
  have h0 := abs_nonneg Δ
  nlinarith

/-- A zero-cost type is indifferent exactly when its gross benefit vanishes, which is unaffected
by the `(2p-1)` scaling. -/
theorem noisyComm_zero_cost {p Δ : ℝ} (hp : 1 / 2 < p) : (2 * p - 1) * Δ = 0 ↔ Δ = 0 := by
  constructor
  · intro h
    exact (mul_eq_zero.1 h).resolve_left (by linarith)
  · rintro rfl
    simp

/-! ### Biased individuals -/

/-- `r = 1` weakly dominates `r = 0` given payoffs `U r k` when `k` others report, `k ≤ m`. -/
def WeaklyDominates1 (m : ℕ) (U : ℕ → ℕ → ℝ) : Prop :=
  (∀ k ≤ m, U 0 k ≤ U 1 k) ∧ ∃ k ≤ m, U 0 k < U 1 k

/-- `r = 0` weakly dominates `r = 1`. -/
def WeaklyDominates0 (m : ℕ) (U : ℕ → ℕ → ℝ) : Prop :=
  (∀ k ≤ m, U 1 k ≤ U 0 k) ∧ ∃ k ≤ m, U 1 k < U 0 k

/-- A reporting probability `σ` puts no weight on a weakly dominated action. -/
def NoDominated (m : ℕ) (U : ℕ → ℕ → ℝ) (σ : ℝ) : Prop :=
  (WeaklyDominates1 m U → σ = 1) ∧ (WeaklyDominates0 m U → σ = 0)

/-- Upward-biased utility from report `r` when `k` others report: `E a`. -/
def Uup (x : ℕ → ℝ) (r k : ℕ) : ℝ := x (k + r)

/-- Downward-biased utility from report `r` when `k` others report: `-E a`. -/
def Udown (x : ℕ → ℝ) (r k : ℕ) : ℝ := -x (k + r)

/-- The overall reporting probability in a state: an individual is upward-biased with probability
`pu` (reporting with probability `σu`), downward-biased with probability `pd` (reporting with
probability `σd`), and otherwise unbiased (reporting with probability `τ`). -/
def biasedRp (pu pd σu σd τ : ℝ) : ℝ := pu * σu + pd * σd + (1 - pu - pd) * τ

/-- A rule is monotone on `{0,…,n}` if `x` is weakly increasing or weakly decreasing there. -/
def MonotoneRule (n : ℕ) (x : ℕ → ℝ) : Prop :=
  (∀ k < n, x k ≤ x (k + 1)) ∨ (∀ k < n, x (k + 1) ≤ x k)

/-- The rule is nonconstant on `{0,…,n}`. -/
def NonconstantRule (n : ℕ) (x : ℕ → ℝ) : Prop := ∃ k < n, x (k + 1) ≠ x k

/-- **Proposition `prop_monotone`.** -/
theorem prop_monotone {n : ℕ} {x : ℕ → ℝ} {pu pd : ℝ} (hpu : 0 < pu) (hpd : 0 < pd)
    (hsum : pu + pd < 1) (hmono : MonotoneRule n x) (hnc : NonconstantRule n x)
    {σu σd τ : ℝ} (hσu : NoDominated (n - 1) (Uup x) σu) (hσd : NoDominated (n - 1) (Udown x) σd)
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    biasedRp pu pd σu σd τ ∈ Icc (min pu pd) (1 - min pu pd) := by
  obtain ⟨k₀, hk₀, hne⟩ := hnc
  have hn : n - 1 + 1 = n := by omega
  have hr : 0 ≤ 1 - pu - pd := by linarith
  have h2 := mul_nonneg hr hτ.1
  have h3 : (1 - pu - pd) * τ ≤ 1 - pu - pd := by nlinarith [hτ.2]
  have h4 := min_le_left pu pd
  have h5 := min_le_right pu pd
  have hk₀' : k₀ ≤ n - 1 := by omega
  rcases hmono with hinc | hdec
  · -- increasing: the upward-biased report and the downward-biased do not
    have hu : σu = 1 := hσu.1 ⟨fun k hk => hinc k (by omega),
      k₀, hk₀', lt_of_le_of_ne (hinc k₀ hk₀) hne.symm⟩
    have hd : σd = 0 := hσd.2 ⟨fun k hk => by
      have := hinc k (by omega)
      show -x (k + 1) ≤ -x (k + 0)
      simpa using this,
      k₀, hk₀', by
        have := lt_of_le_of_ne (hinc k₀ hk₀) hne.symm
        show -x (k₀ + 1) < -x (k₀ + 0)
        simpa using this⟩
    unfold biasedRp
    rw [hu, hd]
    constructor <;> linarith
  · -- decreasing: the roles are reversed
    have hu : σu = 0 := hσu.2 ⟨fun k hk => hdec k (by omega),
      k₀, hk₀', lt_of_le_of_ne (hdec k₀ hk₀) hne⟩
    have hd : σd = 1 := hσd.1 ⟨fun k hk => by
      have := hdec k (by omega)
      show -x (k + 0) ≤ -x (k + 1)
      simpa using this,
      k₀, hk₀', by
        have := lt_of_le_of_ne (hdec k₀ hk₀) hne
        show -x (k₀ + 0) < -x (k₀ + 1)
        simpa using this⟩
    unfold biasedRp
    rw [hu, hd]
    constructor <;> linarith

/-- The expected change in the action from reporting, `Δ_n(ω)` of Prop. `prop_tie_breaking`. -/
noncomputable def actionGain (m : ℕ) (p : ℝ) (x : ℕ → ℝ) : ℝ := marginal m p x

/-- Best responses of biased types under the tie-breaking rule of Prop. `prop_tie_breaking`: the
upward-biased report iff `Δ ≥ 0`, the downward-biased report iff `Δ < 0`. -/
def TieBreak (Δ σu σd : ℝ) : Prop :=
  (0 ≤ Δ → σu = 1) ∧ (Δ < 0 → σu = 0) ∧ (0 ≤ Δ → σd = 0) ∧ (Δ < 0 → σd = 1)

/-- **Proposition `prop_tie_breaking`.** -/
theorem prop_tie_breaking {pu pd : ℝ} (hpu : 0 < pu) (hpd : 0 < pd) (hsum : pu + pd < 1)
    {Δ σu σd τ : ℝ} (hb : TieBreak Δ σu σd) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    biasedRp pu pd σu σd τ ∈ Icc (min pu pd) (1 - min pu pd) := by
  have hr : 0 ≤ 1 - pu - pd := by linarith
  have h2 := mul_nonneg hr hτ.1
  have h3 : (1 - pu - pd) * τ ≤ 1 - pu - pd := by nlinarith [hτ.2]
  have h4 := min_le_left pu pd
  have h5 := min_le_right pu pd
  obtain ⟨h1u, h2u, h1d, h2d⟩ := hb
  unfold biasedRp
  rcases le_or_gt 0 Δ with h | h
  · rw [h1u h, h1d h]
    constructor <;> linarith
  · rw [h2u h, h2d h]
    constructor <;> linarith

/-! ### Remark `remark_ex_post` -/

/-- The posterior-weighted gain from investigating after `k` reports. -/
noncomputable def postGain (pr H L q₁ q₀ : ℝ) (n k : ℕ) : ℝ :=
  pr * H * bpmf n q₁ k + (1 - pr) * L * bpmf n q₀ k

/-- `k` is on path when it has positive probability in some state. -/
def OnPath (q₁ q₀ : ℝ) (n k : ℕ) : Prop := 0 < bpmf n q₁ k ∨ 0 < bpmf n q₀ k

/-- A rule is ex post efficient if, on path, its action is optimal given the posterior. -/
def ExPostEfficient (pr H L q₁ q₀ : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  ∀ k, OnPath q₁ q₀ n k → (0 < postGain pr H L q₁ q₀ n k → x k = 1) ∧
    (postGain pr H L q₁ q₀ n k < 0 → x k = 0)

/-- Monotonicity on path. -/
def MonotoneOnPath (q₁ q₀ : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  (∀ k k', OnPath q₁ q₀ n k → OnPath q₁ q₀ n k' → k ≤ k' → x k ≤ x k') ∨
  (∀ k k', OnPath q₁ q₀ n k → OnPath q₁ q₀ n k' → k ≤ k' → x k' ≤ x k)

lemma bpmf_reflect {n k : ℕ} (hk : k ≤ n) (q : ℝ) : bpmf n q k = bpmf n (1 - q) (n - k) := by
  unfold bpmf
  have h1 : n - (n - k) = k := by omega
  rw [h1, Nat.choose_symm hk]
  simp only [sub_sub_cancel]
  ring

lemma le_of_pos_bpmf {n k : ℕ} {q : ℝ} (h : 0 < bpmf n q k) : k ≤ n := by
  by_contra hcon
  rw [bpmf_eq_zero_of_gt (not_le.1 hcon)] at h
  exact lt_irrefl _ h

/-- Strict monotone likelihood ratio for binomial probabilities in the interior. -/
lemma strict_mlr {n k d : ℕ} {q₁ q₀ : ℝ} (h0 : 0 < q₀) (h01 : q₀ < q₁) (h1 : q₁ < 1)
    (hk : k + d ≤ n) (hd : 0 < d) :
    bpmf n q₁ k * bpmf n q₀ (k + d) < bpmf n q₁ (k + d) * bpmf n q₀ k := by
  have hq₁ : 0 < q₁ := h0.trans h01
  have hq₀1 : q₀ < 1 := h01.trans h1
  have ha : 0 < 1 - q₁ := by linarith
  have hb : 0 < 1 - q₀ := by linarith
  have hC1 : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hC2 : (0 : ℝ) < (n.choose (k + d) : ℝ) := by exact_mod_cast Nat.choose_pos hk
  set m := n - (k + d) with hm
  have hnk : n - k = d + m := by omega
  unfold bpmf
  rw [hnk, ← hm]
  -- common factor
  have hbase : q₀ * (1 - q₁) < q₁ * (1 - q₀) := by nlinarith
  have hpow : (q₀ * (1 - q₁)) ^ d < (q₁ * (1 - q₀)) ^ d :=
    pow_lt_pow_left₀ hbase (by positivity) hd.ne'
  have hfac : 0 < (n.choose k : ℝ) * (n.choose (k + d) : ℝ)
      * (q₁ ^ k * (1 - q₁) ^ m * q₀ ^ k * (1 - q₀) ^ m) := by positivity
  have := mul_lt_mul_of_pos_left hpow hfac
  calc (n.choose k : ℝ) * q₁ ^ k * (1 - q₁) ^ (d + m)
        * ((n.choose (k + d) : ℝ) * q₀ ^ (k + d) * (1 - q₀) ^ m)
      = (n.choose k : ℝ) * (n.choose (k + d) : ℝ)
        * (q₁ ^ k * (1 - q₁) ^ m * q₀ ^ k * (1 - q₀) ^ m) * (q₀ * (1 - q₁)) ^ d := by
        rw [mul_pow, pow_add, pow_add]; ring
    _ < (n.choose k : ℝ) * (n.choose (k + d) : ℝ)
        * (q₁ ^ k * (1 - q₁) ^ m * q₀ ^ k * (1 - q₀) ^ m) * (q₁ * (1 - q₀)) ^ d := this
    _ = _ := by
        rw [mul_pow, pow_add, pow_add]; ring

/-- Single crossing of the posterior gain when `q₁ > q₀`. -/
lemma single_crossing {pr H L q₁ q₀ : ℝ} (hpr0 : 0 < pr) (hpr1 : pr < 1) (hH : 0 < H) (hL : L < 0)
    (h00 : 0 ≤ q₀) (h11 : q₁ ≤ 1) (h01 : q₀ < q₁) {n k k' : ℕ} (hkk' : k < k')
    (hk : OnPath q₁ q₀ n k) (hk' : OnPath q₁ q₀ n k')
    (hg : 0 ≤ postGain pr H L q₁ q₀ n k) : 0 < postGain pr H L q₁ q₀ n k' := by
  have hA : 0 < pr * H := mul_pos hpr0 hH
  have hB : 0 < (1 - pr) * (-L) := mul_pos (by linarith) (by linarith)
  have hq₁0 : 0 ≤ q₁ := h00.trans h01.le
  have hq₀1 : q₀ ≤ 1 := h01.le.trans h11
  have hb1k' : 0 ≤ bpmf n q₁ k' := bpmf_nonneg hq₁0 h11
  have hb0k' : 0 ≤ bpmf n q₀ k' := bpmf_nonneg h00 hq₀1
  have hb1k : 0 ≤ bpmf n q₁ k := bpmf_nonneg hq₁0 h11
  have hb0k : 0 ≤ bpmf n q₀ k := bpmf_nonneg h00 hq₀1
  unfold postGain at hg ⊢
  rcases hb0k'.eq_or_lt with h0 | h0
  · -- `b⁰(k') = 0`, so `b¹(k') > 0` on path
    rw [← h0, mul_zero, add_zero]
    have : 0 < bpmf n q₁ k' := by
      rcases hk' with h | h
      · exact h
      · exact absurd h (by rw [← h0]; exact lt_irrefl _)
    exact mul_pos hA this
  · -- `b⁰(k') > 0`: the interior case
    have hb1 : 0 < bpmf n q₁ k := by
      rcases hb1k.eq_or_lt with h1 | h1
      · exfalso
        rw [← h1, mul_zero, zero_add] at hg
        have h2 : 0 < bpmf n q₀ k := by
          rcases hk with h | h
          · exact absurd h (by rw [← h1]; exact lt_irrefl _)
          · exact h
        have h3 : (1 - pr) * L < 0 := mul_neg_of_pos_of_neg (by linarith) hL
        have := mul_neg_of_neg_of_pos h3 h2
        linarith
      · exact h1
    have hk'n : k' ≤ n := le_of_pos_bpmf h0
    -- positivity of the parameters
    have hq₀pos : 0 < q₀ := by
      rcases h00.eq_or_lt with h | h
      · exfalso
        have hk'pos : k' ≠ 0 := by omega
        unfold bpmf at h0
        rw [← h, zero_pow hk'pos] at h0
        simp at h0
      · exact h
    have hq₁lt : q₁ < 1 := by
      rcases h11.eq_or_lt with h | h
      · exfalso
        have hnk : n - k ≠ 0 := by omega
        unfold bpmf at hb1
        rw [h, sub_self, zero_pow hnk] at hb1
        simp at hb1
      · exact h
    obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
    have hd : 0 < d := by omega
    have hmlr := strict_mlr hq₀pos h01 hq₁lt hk'n hd
    have hb0pos : 0 < bpmf n q₀ k := by
      have hk0 : k ≤ n := by omega
      unfold bpmf
      have hC : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk0
      have : 0 < 1 - q₀ := by linarith
      positivity
    -- divide out
    have h1 : (1 - pr) * (-L) * bpmf n q₀ k ≤ pr * H * bpmf n q₁ k := by nlinarith
    have h2 : (1 - pr) * (-L) * bpmf n q₀ k * bpmf n q₀ (k + d)
        ≤ pr * H * bpmf n q₁ k * bpmf n q₀ (k + d) := mul_le_mul_of_nonneg_right h1 h0.le
    have h3 : pr * H * (bpmf n q₁ k * bpmf n q₀ (k + d))
        < pr * H * (bpmf n q₁ (k + d) * bpmf n q₀ k) := mul_lt_mul_of_pos_left hmlr hA
    have h4 : bpmf n q₀ k * ((1 - pr) * (-L) * bpmf n q₀ (k + d))
        < bpmf n q₀ k * (pr * H * bpmf n q₁ (k + d)) := by nlinarith
    have h5 := lt_of_mul_lt_mul_left h4 hb0pos.le
    nlinarith

/-- **Remark `remark_ex_post`.** Any ex post efficient decision rule is monotone on path. -/
theorem remark_ex_post {pr H L q₁ q₀ : ℝ} (hpr0 : 0 < pr) (hpr1 : pr < 1) (hH : 0 < H) (hL : L < 0)
    (hprior : pr * H + (1 - pr) * L < 0) (h10 : 0 ≤ q₁) (h11 : q₁ ≤ 1) (h00 : 0 ≤ q₀) (h01 : q₀ ≤ 1)
    {n : ℕ} {x : ℕ → ℝ} (hx : ∀ k, x k ∈ Icc (0 : ℝ) 1)
    (hE : ExPostEfficient pr H L q₁ q₀ n x) : MonotoneOnPath q₁ q₀ n x := by
  rcases lt_trichotomy q₀ q₁ with hlt | heq | hgt
  · -- likelihood ratio increasing
    left
    intro k k' hk hk' hle
    rcases hle.eq_or_lt with rfl | hlt'
    · exact le_rfl
    · by_contra hcon
      push Not at hcon
      have hxk : 0 < x k := lt_of_le_of_lt (hx k').1 hcon
      have hg : 0 ≤ postGain pr H L q₁ q₀ n k := by
        by_contra h
        have := (hE k hk).2 (not_le.1 h)
        linarith
      have hg' := single_crossing hpr0 hpr1 hH hL h00 h11 hlt hlt' hk hk' hg
      have := (hE k' hk').1 hg'
      have h1 := (hx k).2
      linarith
  · -- reports are uninformative: the prior action is optimal
    left
    subst heq
    have hzero : ∀ k, OnPath q₀ q₀ n k → x k = 0 := by
      intro k hk
      refine (hE k hk).2 ?_
      have hpos : 0 < bpmf n q₀ k := by
        rcases hk with h | h <;> exact h
      unfold postGain
      have : pr * H * bpmf n q₀ k + (1 - pr) * L * bpmf n q₀ k
          = (pr * H + (1 - pr) * L) * bpmf n q₀ k := by ring
      rw [this]
      exact mul_neg_of_neg_of_pos hprior hpos
    intro k k' hk hk' _
    rw [hzero k hk, hzero k' hk']
  · -- likelihood ratio decreasing: reflect `k ↦ n - k`
    right
    intro k k' hk hk' hle
    rcases hle.eq_or_lt with rfl | hlt'
    · exact le_rfl
    · have hkn : k' ≤ n := by
        rcases hk' with h | h <;> exact le_of_pos_bpmf h
      have hk0n : k ≤ n := by omega
      have hrefl : ∀ j, j ≤ n → OnPath q₁ q₀ n j → OnPath (1 - q₁) (1 - q₀) n (n - j) := by
        intro j hj h
        unfold OnPath at h ⊢
        rwa [bpmf_reflect hj q₁, bpmf_reflect hj q₀] at h
      have hgainrefl : ∀ j, j ≤ n → postGain pr H L q₁ q₀ n j
          = postGain pr H L (1 - q₁) (1 - q₀) n (n - j) := by
        intro j hj
        unfold postGain
        rw [bpmf_reflect hj q₁, bpmf_reflect hj q₀]
      by_contra hcon
      push Not at hcon
      have hxk' : 0 < x k' := lt_of_le_of_lt (hx k).1 hcon
      have hg : 0 ≤ postGain pr H L q₁ q₀ n k' := by
        by_contra h
        have := (hE k' hk').2 (not_le.1 h)
        linarith
      rw [hgainrefl k' hkn] at hg
      have hs := single_crossing hpr0 hpr1 hH hL (q₁ := 1 - q₁) (q₀ := 1 - q₀) (by linarith)
        (by linarith) (by linarith) (n := n) (k := n - k') (k' := n - k) (by omega)
        (hrefl k' hkn hk') (hrefl k hk0n hk) hg
      rw [← hgainrefl k hk0n] at hs
      have := (hE k hk).1 hs
      have h1 := (hx k').2
      linarith

end NoisyVD
