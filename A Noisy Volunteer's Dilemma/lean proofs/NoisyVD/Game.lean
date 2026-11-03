import NoisyVD.Micro

/-!
# From the strategic-form game to the reduced form

`NoisyVD/Model.lean` defines equilibrium and payoffs through binomial formulas.  This file proves those
formulas from the underlying game: reports are independent across individuals with probability `p`,
so a report profile is a subset `S` of individuals with probability `p^{|S|} (1-p)^{n-|S|}`, and
each type chooses the report that maximises expected utility `u^p(a,ω) - r x`.
-/

open MeasureTheory Set Filter Topology Real Finset

namespace NoisyVD

/-- The probability of the report profile `S` under i.i.d. reporting with probability `p`. -/
noncomputable def profileProb {m : ℕ} (p : ℝ) (S : Finset (Fin m)) : ℝ :=
  ∏ i, if i ∈ S then p else 1 - p

lemma profileProb_eq {m : ℕ} (p : ℝ) (S : Finset (Fin m)) :
    profileProb p S = p ^ S.card * (1 - p) ^ (m - S.card) := by
  unfold profileProb
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have h1 : (Finset.univ.filter fun i => i ∈ S) = S := by
    ext i; simp
  have h2 : (Finset.univ.filter fun i => i ∉ S).card = m - S.card := by
    have := Finset.card_compl S
    rw [Fintype.card_fin] at this
    rw [← this]
    congr 1
    ext i; simp
  rw [h1, h2]

/-- The report count under i.i.d. reports is binomial. -/
theorem sum_profile {m : ℕ} (p : ℝ) (f : ℕ → ℝ) :
    ∑ S : Finset (Fin m), profileProb p S * f S.card = bexp m p f := by
  have h := Finset.sum_powerset_apply_card (fun k => p ^ k * (1 - p) ^ (m - k) * f k)
    (x := (Finset.univ : Finset (Fin m)))
  simp only [Finset.card_univ, Fintype.card_fin, Finset.powerset_univ, nsmul_eq_mul] at h
  unfold bexp
  simp_rw [profileProb_eq]
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold bpmf
  ring

/-- An individual's expected utility from report `r` when `m` others report i.i.d. with probability
`p`, with reporting cost `x`, and gross payoff `v(k)` when `k` reports are made in total. -/
noncomputable def indivU {m : ℕ} (p : ℝ) (v : ℕ → ℝ) (x : ℝ) (r : ℕ) : ℝ :=
  ∑ S : Finset (Fin m), profileProb p S * v (S.card + r) - r * x

/-- The expected gain from reporting is the gross benefit minus the cost. -/
theorem indivU_gain {m : ℕ} (p : ℝ) (v : ℕ → ℝ) (x : ℝ) :
    indivU (m := m) p v x 1 - indivU (m := m) p v x 0 = marginal m p v - x := by
  unfold indivU
  have h1 := sum_profile (m := m) p (fun k => v (k + 1))
  have h0 := sum_profile (m := m) p (fun k => v (k + 0))
  rw [h1, h0]
  unfold bexp marginal
  simp only [add_zero, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, sub_zero]
  have : ∑ k ∈ range (m + 1), bpmf m p k * (v (k + 1) - v k)
      = ∑ k ∈ range (m + 1), bpmf m p k * v (k + 1) - ∑ k ∈ range (m + 1), bpmf m p k * v k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  linarith

/-- A mixture `σ` is a best response iff it reports when the net gain is positive and abstains when
it is negative. -/
theorem bestResponse_iff {U₀ U₁ σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    (∀ τ ∈ Icc (0 : ℝ) 1, τ * U₁ + (1 - τ) * U₀ ≤ σ * U₁ + (1 - σ) * U₀) ↔
      ((U₀ < U₁ → σ = 1) ∧ (U₁ < U₀ → σ = 0)) := by
  constructor
  · intro h
    constructor
    · intro hlt
      have h1 := h 1 ⟨zero_le_one, le_rfl⟩
      have h2 : (1 - σ) * (U₁ - U₀) ≤ 0 := by nlinarith
      have h3 : 1 - σ ≤ 0 := by
        by_contra hc
        push Not at hc
        have := mul_pos hc (sub_pos.2 hlt)
        linarith
      linarith [hσ.2]
    · intro hlt
      have h1 := h 0 ⟨le_rfl, zero_le_one⟩
      have h2 : σ * (U₀ - U₁) ≤ 0 := by nlinarith
      have h3 : σ ≤ 0 := by
        by_contra hc
        push Not at hc
        have := mul_pos hc (sub_pos.2 hlt)
        linarith
      linarith [hσ.1]
  · rintro ⟨h1, h2⟩ τ hτ
    rcases lt_trichotomy U₀ U₁ with h | h | h
    · rw [h1 h]
      nlinarith [hτ.2, sub_pos.2 h]
    · subst h
      nlinarith
    · rw [h2 h]
      nlinarith [hτ.1, sub_pos.2 h]

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

namespace Env

/-- **`IsEq` is symmetric Bayesian Nash equilibrium**: a strategy is in `IsEq` iff in every state,
every type's report probability maximises expected utility, the other `n-1` individuals reporting
i.i.d. with the probability that the strategy induces. -/
theorem isEq_iff_bestResponse (E : Env A Ω) {n : ℕ} (d : Rule A) (s : Strat Ω) :
    E.IsEq n d s ↔ ∀ ω x, ∀ τ ∈ Icc (0 : ℝ) 1,
      τ * indivU (m := n - 1) (E.rp s ω) (fun k => E.v d k ω) x 1
          + (1 - τ) * indivU (m := n - 1) (E.rp s ω) (fun k => E.v d k ω) x 0
        ≤ s.σ ω x * indivU (m := n - 1) (E.rp s ω) (fun k => E.v d k ω) x 1
          + (1 - s.σ ω x) * indivU (m := n - 1) (E.rp s ω) (fun k => E.v d k ω) x 0 := by
  have hgain : ∀ ω x, indivU (m := n - 1) (E.rp s ω) (fun k => E.v d k ω) x 1
      - indivU (m := n - 1) (E.rp s ω) (fun k => E.v d k ω) x 0 = E.gross n d (E.rp s ω) ω - x :=
    fun ω x => indivU_gain _ _ _
  constructor
  · intro he ω x τ hτ
    refine (bestResponse_iff (s.mem ω x)).2 ⟨fun h => ?_, fun h => ?_⟩ τ hτ
    · refine (he ω x).1 ?_
      have := hgain ω x
      linarith
    · refine (he ω x).2 ?_
      have := hgain ω x
      linarith
  · intro h ω x
    have h2 := (bestResponse_iff (s.mem ω x)).1 (h ω x)
    constructor
    · intro hx
      refine h2.1 ?_
      have := hgain ω x
      linarith
    · intro hx
      refine h2.2 ?_
      have := hgain ω x
      linarith

/-- **The decision-maker's payoff** is the expectation of `u^p` over report profiles. -/
theorem payoff_eq_profile (E : Env A Ω) (n : ℕ) (d : Rule A) (s : Strat Ω) :
    E.payoff n d s = ∫ ω, ∑ S : Finset (Fin n), profileProb (E.rp s ω) S * E.v d S.card ω
      ∂(E.prior : Measure Ω) := by
  unfold payoff
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  exact (sum_profile (E.rp s ω) (fun k => E.v d k ω)).symm

end Env

end NoisyVD
