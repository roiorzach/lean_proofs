import NoisyVD.Benchmarks
import NoisyVD.Fidelity
import NoisyVD.LocalBinomial

/-!
# A Noisy Volunteer's Dilemma: all results in the main text and Appendices A--C

Each theorem below is the Lean statement of a labelled result of `current.tex`.  The final block
prints the axioms used by each one: only `propext`, `Classical.choice` and `Quot.sound`, the
standard foundations of Lean's Mathlib.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-- **Proposition 1 (Benchmark: No Noise)**, in the exact density form of Section 2. -/
theorem Proposition1 {E : Env Bool Bool} {a b : ℝ} {f : ℝ → ℝ} (hf : VD.CostDensity E a b f)
    (hH : a < VD.H E) (hL : VD.L E < 0) :
    (∀ n : ℕ, 2 ≤ n → ∃ c ∈ Ioo a b, c = VD.H E * (1 - E.F c) ^ (n - 1) ∧
      (∀ c', c' = VD.H E * (1 - E.F c') ^ (n - 1) → c' = c) ∧
      (∃ s : Strat Bool, E.IsEq n VD.oneReport s) ∧
      ∀ s : Strat Bool, E.IsEq n VD.oneReport s →
        (∀ x > 0, s.σ false x = 0) ∧ E.rp s false = 0 ∧ btail n (E.rp s false) 1 = 0 ∧
        (∀ x < c, s.σ true x = 1) ∧ (∀ x > c, s.σ true x = 0) ∧ E.rp s true = E.F c ∧
        1 - btail n (E.rp s true) 1 = (1 - E.F c) ^ n) ∧
    (∀ c : ℕ → ℝ, (∀ n, 2 ≤ n → c n ∈ Ioo a b ∧ c n = VD.H E * (1 - E.F (c n)) ^ (n - 1)) →
      Tendsto (fun n => (1 - E.F (c n)) ^ n) atTop (𝓝 (a / VD.H E))) ∧
    a / VD.H E < 1 :=
  VD.prop_no_clueless hf.toBenchmark hH hL

/-- **Proposition 1, the limit along equilibria**: there is never an investigation in state `0`, and
along any sequence of symmetric equilibria the probability of no investigation in state `1`
converges to `ν̲/H`. -/
theorem Proposition1_limit {E : Env Bool Bool} {a b : ℝ} {f : ℝ → ℝ} (hf : VD.CostDensity E a b f)
    (hH : a < VD.H E) (hL : VD.L E < 0) {s : ℕ → Strat Bool}
    (hs : ∀ n, 2 ≤ n → E.IsEq n VD.oneReport (s n)) :
    (∀ n, 2 ≤ n → btail n (E.rp (s n) false) 1 = 0) ∧
      Tendsto (fun n => 1 - btail n (E.rp (s n) true) 1) atTop (𝓝 (a / VD.H E)) :=
  VD.prop_no_clueless_limit hf.toBenchmark hH hL hs

/-- The proof of Proposition 1: `ν*(n)` is decreasing in `n` and converges to `ν̲`. -/
theorem Proposition1_cutoff {E : Env Bool Bool} {a b : ℝ} {f : ℝ → ℝ} (hf : VD.CostDensity E a b f)
    (hH : 0 < VD.H E) {c : ℕ → ℝ}
    (hc : ∀ n, 2 ≤ n → c n ∈ Ioo a b ∧ c n = VD.H E * (1 - E.F (c n)) ^ (n - 1)) :
    (∀ n, 2 ≤ n → c (n + 1) ≤ c n) ∧ Tendsto c atTop (𝓝 a) :=
  ⟨fun n hn => hf.toBenchmark.cutoff_succ_le hH hn (hc n hn).2 (hc (n + 1) (by omega)).2,
    hf.toBenchmark.tendsto_cutoff hH hc⟩

/-- **Proposition 2 (Benchmark: With Noise).** -/
theorem Proposition2 {E : Env Bool Bool} {a ε : ℝ} (ha : 0 < a) (hFa : E.Fm a = 0) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ nStar : ℕ, ∀ n ≥ nStar, ∀ (T : ℕ) (s : Strat Bool),
      VD.IsEqMech E ε n (thresholdRule T true false) s →
      (∀ ω, ∀ x ≥ a, s.σ ω x = 0) ∧ (∀ ω, E.rp s ω = 0) ∧
        VD.payoffMech E ε n (thresholdRule T true false) s ≤ E.PiSQ :=
  VD.prop_noise_threshold ha hFa hε0 hε1

/-- Proposition 2 is not vacuous: for all large `n`, an equilibrium exists under every threshold. -/
theorem Proposition2_exists {E : Env Bool Bool} {a ε : ℝ} (ha : 0 < a) (hFa : E.Fm a = 0)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ nStar : ℕ, ∀ n ≥ nStar, ∀ T : ℕ, ∃ s : Strat Bool,
      VD.IsEqMech E ε n (thresholdRule T true false) s :=
  VD.exists_eq_mech ha hFa hε0 hε1

/-- **Lemma 1 (`lemma_noise`).** -/
theorem Lemma1 (E : Env A Ω) (hE : E.Noise) :
    0 < E.epsStar ∧ ∀ (n : ℕ) (d : Rule A) (s : Strat Ω), E.IsEq n d s → ∀ ω,
      E.rp s ω ∈ Icc E.epsStar (1 - E.epsStar) :=
  Env.lemma_noise E hE

/-- **Lemma 2 (`lemma_pivotal`).** The constant `M = Env.pivConst B ε_* = √2 B C_{ε_*}` depends only on `B`,
`ε_*`.  It is positive because the maintained assumption `Π^FB > Π^SQ` gives `B > 0`. -/
theorem Lemma2 (E : Env A Ω) (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) :
    0 < Env.pivConst E.B E.epsStar ∧ ∀ {n : ℕ}, 2 ≤ n → ∀ {d : Rule A} {s : Strat Ω}, E.IsEq n d s →
      ∀ (ω : Ω) (x : ℝ),
        (Env.pivConst E.B E.epsStar / √(n : ℝ) < x → s.σ ω x = 0) ∧
        (x < -(Env.pivConst E.B E.epsStar / √(n : ℝ)) → s.σ ω x = 1) :=
  ⟨Env.pivConst_pos (E.B_pos_of_lt hFB) (Env.lemma_noise E hE).1 (Env.epsStar_le_half E),
    fun hn _ _ he ω x => Env.lemma_pivotal E hE hn he ω x⟩

/-- **Proposition 3 (`prop_volunteers`).** -/
theorem Proposition3 {E : Env Bool Bool} (hV : VD.Assumptions E) (hN : E.Noise) :
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, E.Pi n = E.PiSQ) ∧
    (HasDerivAt E.F 0 0 → Tendsto E.Pi atTop (𝓝 E.PiSQ)) ∧
    (∀ t > 0, HasDerivAt E.F t 0 → limsup E.Pi atTop < E.PiFB) ∧
    (0 < Fbar (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) ∧
      ∀ (U : Set ℝ) (t : ℝ), IsOpen U → (0 : ℝ) ∈ U → ContDiffOn ℝ 1 E.F U → deriv E.F 0 = t → 0 < t →
        (E.PiSQ < liminf E.PiT atTop ↔ Fbar (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) < t)) ∧
    (∀ α > 0, Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α) → Tendsto E.Pi atTop (𝓝 E.PiFB)) :=
  VD.prop_volunteers hV hN

/-- **Proposition 4 (`prop_general_failures`).** -/
theorem Proposition4 (E : Env A Ω) (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) :
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, E.Pi n = E.PiSQ) ∧
    (HasDerivAt E.F 0 0 → Tendsto E.Pi atTop (𝓝 E.PiSQ)) ∧
    (∀ t > 0, HasDerivAt E.F t 0 → limsup E.Pi atTop < E.PiFB) ∧
    (∀ α > 0, Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α) → Tendsto E.Pi atTop (𝓝 E.PiFB)) :=
  ⟨fun _ hδ h => Env.prop_general_1 E hE hδ h, Env.prop_general_2 E hE hFB,
    fun _ _ h => Env.prop_general_3 E hE hFB h, fun _ hα h => Env.prop_general_4 E hα h⟩

/-- **Lemma A (`lemma_threshold_value`).** -/
theorem LemmaThresholdValue {E : Env Bool Bool} (hV : VD.Assumptions E) (hN : E.Noise) {U : Set ℝ}
    (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) (hF : ContDiffOn ℝ 1 E.F U) {t : ℝ} (ht : deriv E.F 0 = t)
    (htpos : 0 < t) :
    0 ≤ Vval (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) t ∧
      Tendsto E.PiT atTop (𝓝 (E.PiSQ + Vval (VD.pr E) (VD.H E) (-VD.L E) (E.F 0 * (1 - E.F 0)) t)) :=
  VD.lemma_threshold_value hV hN htpos (VD.Smooth.of_contDiffOn hU h0 hF ht)

/-- **Lemma A (`lemma_threshold_cutoff`).** -/
theorem LemmaThresholdCutoff {pr H l S : ℝ} (hp : Par pr H l S) :
    0 < Fbar pr H l S ∧ ∀ t : ℝ, 0 < t → (0 < Vval pr H l S t ↔ Fbar pr H l S < t) :=
  lemma_threshold_cutoff hp

/-- **Proposition B1 (`prop_monotone`).** -/
theorem PropositionB1 {n : ℕ} {d : Rule Bool} {pu pd : ℝ} (hpu : 0 < pu) (hpd : 0 < pd)
    (hsum : pu + pd < 1) (hmono : MonotoneRule n (VD.rateX d)) (hnc : NonconstantRule n (VD.rateX d))
    {σu σd τ : ℝ} (hσu : NoDominated (n - 1) (Uup (VD.rateX d)) σu)
    (hσd : NoDominated (n - 1) (Udown (VD.rateX d)) σd) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    biasedRp pu pd σu σd τ ∈ Icc (min pu pd) (1 - min pu pd) :=
  prop_monotone_rule hpu hpd hsum hmono hnc hσu hσd hτ

/-- **Remark 1 (`remark_ex_post`).** -/
theorem Remark1 {pr H L q₁ q₀ : ℝ} (hpr0 : 0 < pr) (hpr1 : pr < 1) (hH : 0 < H) (hL : L < 0)
    (hprior : pr * H + (1 - pr) * L < 0) (h10 : 0 ≤ q₁) (h11 : q₁ ≤ 1) (h00 : 0 ≤ q₀) (h01 : q₀ ≤ 1)
    {n : ℕ} {x : ℕ → ℝ} (hx : ∀ k, x k ∈ Icc (0 : ℝ) 1)
    (hE : ExPostEfficient pr H L q₁ q₀ n x) : MonotoneOnPath q₁ q₀ n x :=
  remark_ex_post hpr0 hpr1 hH hL hprior h10 h11 h00 h01 hx hE

/-- **Proposition B2 (`prop_tie_breaking`)**, stated at the level of the game. -/
theorem PropositionB2 {n : ℕ} {x : ℕ → ℝ} {p pu pd : ℝ} (hpu : 0 < pu) (hpd : 0 < pd)
    (hsum : pu + pd < 1) {σu σd τ : ℝ} (hσu : σu ∈ Icc (0 : ℝ) 1) (hσd : σd ∈ Icc (0 : ℝ) 1)
    (hBRu : ∀ r ∈ Icc (0 : ℝ) 1,
      r * indivU (m := n - 1) p x 0 1 + (1 - r) * indivU (m := n - 1) p x 0 0
        ≤ σu * indivU (m := n - 1) p x 0 1 + (1 - σu) * indivU (m := n - 1) p x 0 0)
    (hBRd : ∀ r ∈ Icc (0 : ℝ) 1,
      r * indivU (m := n - 1) p (fun k => -x k) 0 1 + (1 - r) * indivU (m := n - 1) p (fun k => -x k) 0 0
        ≤ σd * indivU (m := n - 1) p (fun k => -x k) 0 1
          + (1 - σd) * indivU (m := n - 1) p (fun k => -x k) 0 0)
    (htieu : indivU (m := n - 1) p x 0 1 = indivU (m := n - 1) p x 0 0 → σu = 1)
    (htied : indivU (m := n - 1) p x 0 1 = indivU (m := n - 1) p x 0 0 → σd = 0)
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    biasedRp pu pd σu σd τ ∈ Icc (min pu pd) (1 - min pu pd) :=
  prop_tie_breaking_game hpu hpd hsum hσu hσd hBRu hBRd htieu htied hτ

/-- **Lemma C (`lemma_binomial_overlap`).** -/
theorem LemmaBinomialOverlap {l : ℝ} (hl : 0 < l) {p q : ℕ → ℝ}
    (hp : ∀ n, p n ∈ Icc l (1 - l)) (hq : ∀ n, q n ∈ Icc l (1 - l)) :
    (Tendsto (fun n : ℕ => (n : ℝ) * (p n - q n) ^ 2) atTop (𝓝 0) →
      Tendsto (fun n => tv n (p n) (q n)) atTop (𝓝 0)) ∧
    (∀ C : ℝ, (∀ n : ℕ, (n : ℝ) * (p n - q n) ^ 2 ≤ C) →
      ∀ᶠ n in atTop, tv n (p n) (q n) ≤ √(1 - exp (-C / l)) ∧ √(1 - exp (-C / l)) < 1) :=
  lemma_binomial_overlap hl hp hq

/-- **Lemma C (`lemma_symmetric_equilibrium_exists`).** -/
theorem LemmaEquilibriumExists (E : Env A Ω) (n : ℕ) (d : Rule A) : ∃ s : Strat Ω, E.IsEq n d s :=
  Env.exists_equilibrium E n d

/-- **Lemma C (`lemma_local_binomial`).** -/
theorem LemmaLocalBinomial :
    (∀ l : ℝ, 0 < l → l ≤ 1 / 2 → ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ p ∈ Icc l (1 - l), ∀ k : ℕ,
      bpmf m p k ≤ C / √(m : ℝ)) ∧
    (∀ s : ℝ, 0 < s → s < 1 → ∀ K L₀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x t : ℝ, |x| ≤ K → |t| ≤ K →
      ∀ l : ℤ, |(l : ℝ)| ≤ L₀ →
      |√(n : ℝ) * bpmf ((n : ℤ) + l).toNat (s + x / √(n : ℝ)) ⌊(n : ℝ) * s + t * √(n : ℝ)⌋₊
          - 1 / √(s * (1 - s)) * phi ((t - x) / √(s * (1 - s)))| < ε ∧
      |btail ((n : ℤ) + l).toNat (s + x / √(n : ℝ)) ⌊(n : ℝ) * s + t * √(n : ℝ)⌋₊
          - (1 - Phi ((t - x) / √(s * (1 - s))))| < ε) :=
  lemma_local_binomial

/-- The first claim of Lemma C (`lemma_local_binomial`) with the paper's constant
`C_λ = 1/√(2πλ(1-λ)) + 2 B_λ`, `B_λ = C_BE/√(λ(1-λ))`, derived from the Berry--Esseen Theorem as in the paper. -/
theorem LemmaLocalBinomial_massBound {m : ℕ} (hm : 1 ≤ m) {l p : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2)
    (hp : p ∈ Icc l (1 - l)) (k : ℕ) :
    bpmf m p k ≤ (1 / √(2 * π * (l * (1 - l))) + 2 * (CBE / √(l * (1 - l)))) / √(m : ℝ) :=
  bpmf_le_massConst hm hl hl' hp k

/-- **The Berry--Esseen Theorem**, for sums of i.i.d. Bernoulli(`p`) variables, as the paper applies it:
`|Pr(X_{m,p} ≤ mp + zσ_{m,p}) - Φ(z)| ≤ C_BE E|ξ-p|³/((p(1-p))^{3/2} √m)`, with `C_BE = 52`. -/
theorem BerryEsseen {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (z : ℝ) :
    |bcdf m p ((m : ℝ) * p + z * sdev m p) - Phi z|
      ≤ CBE * ((p * |1 - p| ^ 3 + (1 - p) * |0 - p| ^ 3) / ((p * (1 - p)) * √(p * (1 - p)))) / √(m : ℝ) :=
  berry_esseen_binomial hm hp hp1 z

/-- **Equation `eq_be`.** -/
theorem EqBe {m : ℕ} (hm : 1 ≤ m) {l p : ℝ} (hl : 0 < l) (hl' : l ≤ 1 / 2) (hp : p ∈ Icc l (1 - l)) (z : ℝ) :
    |bcdf m p ((m : ℝ) * p + z * sdev m p) - Phi z| ≤ (CBE / √(l * (1 - l))) / √(m : ℝ) :=
  eq_be hm hl hl' hp z

/-- **Benchmark payoff limit** (the remark after Proposition 1 and Section 6). -/
theorem BenchmarkPayoffLimit {E : Env Bool Bool} (hV : VD.Assumptions E) {a b : ℝ} {f : ℝ → ℝ}
    (hf : VD.CostDensity E a b f) (hH : a < VD.H E) {c : ℕ → ℝ}
    (hc : ∀ n, 2 ≤ n → c n ∈ Ioo a b ∧ c n = VD.H E * (1 - E.F (c n)) ^ (n - 1)) {s : ℕ → Strat Bool}
    (hs : ∀ n, 2 ≤ n → E.IsEq n VD.oneReport (s n)) :
    Tendsto (fun n => E.payoff n VD.oneReport (s n)) atTop (𝓝 (E.PiFB - VD.pr E * a)) :=
  VD.benchmark_limit_payoff hV hf.toBenchmark hH hc hs

/-- **Equation `eq_derivative`**: `lim_n n (F(M/√n) - F(-M/√n)) / √n = 2 M F'(0)`. -/
theorem EqDerivative {F : ℝ → ℝ} {t M : ℝ} (hF : HasDerivAt F t 0) (hM : 0 < M) :
    Tendsto (fun n : ℕ => (n : ℝ) * (F (M / √(n : ℝ)) - F (-(M / √(n : ℝ)))) / √(n : ℝ)) atTop
      (𝓝 (2 * M * t)) := by
  have hslope := hF.tendsto_slope_zero
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => M / √(n : ℝ)) atTop (𝓝 0) := Tendsto.const_div_atTop hsq M
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < M / √(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos hM (Real.sqrt_pos.2 this)
  have h1 : Tendsto (fun n : ℕ => M / √(n : ℝ)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hh, hpos.mono fun n hn => hn.ne'⟩
  have h2 : Tendsto (fun n : ℕ => -(M / √(n : ℝ))) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hpos.mono fun n hn => ?_⟩
    · simpa using hh.neg
    · have : -(M / √(n : ℝ)) < 0 := by linarith
      exact this.ne
  have hsum := ((hslope.comp h1).const_mul M).add ((hslope.comp h2).const_mul M)
  have e : M * t + M * t = 2 * M * t := by ring
  rw [e] at hsum
  refine hsum.congr' ?_
  filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnr
  have hsqr : (n : ℝ) / √(n : ℝ) = √(n : ℝ) := Real.div_sqrt
  simp only [Function.comp, smul_eq_mul, zero_add]
  have e2 : (n : ℝ) * (F (M / √(n : ℝ)) - F (-(M / √(n : ℝ)))) / √(n : ℝ)
      = ((n : ℝ) / √(n : ℝ)) * (F (M / √(n : ℝ)) - F (-(M / √(n : ℝ)))) := by ring
  rw [e2, hsqr]
  field_simp
  ring

/-- Proposition 4 in the paper's literal setting: `A` and `Ω` compact subsets of the reals (for
compact `S`, `CompactSpace S` follows from `isCompact_iff_compactSpace`). -/
theorem Proposition4_real_subsets {SA SΩ : Set ℝ} [CompactSpace SA] [CompactSpace SΩ] [Nonempty SA]
    (E : Env SA SΩ) (hE : E.Noise) (hFB : E.PiSQ < E.PiFB) :
    (∀ δ > 0, E.F δ - E.F (-δ) = 0 → ∃ nStar : ℕ, ∀ n > nStar, E.Pi n = E.PiSQ) ∧
    (HasDerivAt E.F 0 0 → Tendsto E.Pi atTop (𝓝 E.PiSQ)) ∧
    (∀ t > 0, HasDerivAt E.F t 0 → limsup E.Pi atTop < E.PiFB) ∧
    (∀ α > 0, Tendsto (fun δ => E.F δ - E.F (-δ)) (𝓝[>] 0) (𝓝 α) → Tendsto E.Pi atTop (𝓝 E.PiFB)) :=
  Proposition4 E hE hFB

end NoisyVD

/-! ### Axiom audit -/

#print axioms NoisyVD.Proposition1
#print axioms NoisyVD.Proposition1_limit
#print axioms NoisyVD.Proposition1_cutoff
#print axioms NoisyVD.Proposition2
#print axioms NoisyVD.Proposition2_exists
#print axioms NoisyVD.Lemma1
#print axioms NoisyVD.Lemma2
#print axioms NoisyVD.Proposition3
#print axioms NoisyVD.Proposition4
#print axioms NoisyVD.LemmaThresholdValue
#print axioms NoisyVD.LemmaThresholdCutoff
#print axioms NoisyVD.PropositionB1
#print axioms NoisyVD.Remark1
#print axioms NoisyVD.PropositionB2
#print axioms NoisyVD.LemmaBinomialOverlap
#print axioms NoisyVD.LemmaEquilibriumExists
#print axioms NoisyVD.LemmaLocalBinomial
#print axioms NoisyVD.LemmaLocalBinomial_massBound
#print axioms NoisyVD.BerryEsseen
#print axioms NoisyVD.EqBe
#print axioms NoisyVD.BenchmarkPayoffLimit
#print axioms NoisyVD.EqDerivative
#print axioms NoisyVD.Proposition4_real_subsets
#print axioms NoisyVD.Env.isEq_iff_bestResponse
#print axioms NoisyVD.Env.payoff_eq_profile
#print axioms NoisyVD.Env.micro_prop
#print axioms NoisyVD.VD.biased_upper
#print axioms NoisyVD.Example.threshold_applies
#print axioms NoisyVD.Env.payoffs_ae_eq
#print axioms NoisyVD.VD.micro_threshold_iff
#print axioms NoisyVD.Phi_eq_cdf
#print axioms NoisyVD.Env.tendsto_F_left
