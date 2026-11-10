import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ConformityConcerns.LearnTheta.ClaimAux.Period2
import ConformityConcerns.LearnTheta.ClaimAux.Tower

/-!
# Proposition A5, across histories: the Claim

The proof of Proposition A5 uses the following Claim: almost surely,
if decisions keep revealing whether `ṽ_t` lies above a threshold, the public posterior about `θ`
converges to `δ_θ`. This file states it for an abstract filtration.

* `ℱ t` is the public information before period `t` (the σ-algebra of `h^t`).
* `𝒜 t ⊇ ℱ t` is everything realised before period `t` (`θ` and the past shocks).
* The signal is `s_t = θ + ε_t`, with `ε_t` independent of `𝒜 t` and distributed as `Lε`.
* `Y_t = E(θ | s_t, h^t)` and the one-dimensional type is `ṽ_t = v_t + Y_t`, with `v_t`
  independent of `𝒜 t ⊔ σ(ε_t)`, with an everywhere positive continuous density `ψ`.
* Revelation at a threshold `d` on an `ℱ t`-measurable event `Rev t`: on `Rev t`, the period-`t`
  decision reveals whether `ṽ_t > d`, i.e. `{ṽ_t > d} ∩ Rev t` is (up to a null set) in
  `ℱ (t + 1)`.

Conclusion: almost surely, if `Rev t` happens infinitely often, then `θ(h^t) → θ` and
`Var(θ | h^t) → 0`.

No assumption on the law of `ε_t` is needed beyond independence and a common law.
-/

namespace CC.LearnTheta

open MeasureTheory ProbabilityTheory Filter Topology

set_option warn.classDefReducibility false

/-- The hypotheses of the Claim in the proof of Proposition A5. -/
structure ClaimSetup {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) where
  /-- Public information before period `t`: the σ-algebra of the history `h^t`. -/
  ℱ : Filtration ℕ mΩ
  /-- Everything realised before period `t`. -/
  𝒜 : ℕ → MeasurableSpace Ω
  /-- The fundamental. -/
  θ : Ω → ℝ
  /-- Signal noise: player `t` observes `s_t = θ + ε_t`. -/
  ε : ℕ → Ω → ℝ
  /-- Preference shocks. -/
  v : ℕ → Ω → ℝ
  /-- The common law of the signal noise. -/
  Lε : Measure ℝ
  /-- The density of the preference shocks. -/
  ψ : ℝ → ℝ
  A_le : ∀ t, 𝒜 t ≤ mΩ
  F_le_A : ∀ t, ℱ t ≤ 𝒜 t
  θ_meas : ∀ t, Measurable[𝒜 t] θ
  θ_sq : MemLp θ 2 P
  ε_meas : ∀ t, Measurable (ε t)
  v_meas : ∀ t, Measurable (v t)
  ε_indep : ∀ t, Indep (MeasurableSpace.comap (ε t) inferInstance) (𝒜 t) P
  v_indep : ∀ t, Indep (MeasurableSpace.comap (v t) inferInstance)
    (𝒜 t ⊔ MeasurableSpace.comap (ε t) inferInstance) P
  ε_law : ∀ t, P.map (ε t) = Lε
  v_law : ∀ t, P.map (v t) = volume.withDensity (fun x => ENNReal.ofReal (ψ x))
  ψ_cont : Continuous ψ
  ψ_pos : ∀ x, 0 < ψ x

namespace ClaimSetup

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} (S : ClaimSetup P)

/-- `σ(h^t, s_t)`: the information of player `t` about `θ`. -/
def 𝒢 (t : ℕ) : MeasurableSpace Ω :=
  S.ℱ t ⊔ MeasurableSpace.comap (fun ω => S.θ ω + S.ε t ω) inferInstance

/-- `Y_t = E(θ | s_t, h^t)`. -/
noncomputable def Y (t : ℕ) : Ω → ℝ := P[S.θ | S.𝒢 t]

/-- The one-dimensional type `ṽ_t = v_t + E(θ | s_t, h^t)`. -/
noncomputable def vt (t : ℕ) (ω : Ω) : ℝ := S.v t ω + S.Y t ω

/-- The public posterior mean `θ(h^t) = E(θ | h^t)`. -/
noncomputable def post (t : ℕ) : Ω → ℝ := P[S.θ | S.ℱ t]

/-- The public posterior variance `Var(θ | h^t)`. -/
noncomputable def postVar (t : ℕ) (ω : Ω) : ℝ :=
  (P[fun ω => S.θ ω ^ 2 | S.ℱ t]) ω - S.post t ω ^ 2

/-- One period of the setup, in the form used by the helper lemmas. -/
lemma periodHyp [IsProbabilityMeasure P] (t : ℕ) :
    ClaimAux.PeriodHyp (S.ℱ t) (S.𝒜 t) mΩ P S.θ (S.ε t) (S.v t) where
  m_le_A := S.F_le_A t
  A_le := S.A_le t
  θ_meas := S.θ_meas t
  θ_int := S.θ_sq.integrable one_le_two
  ε_meas := S.ε_meas t
  v_meas := S.v_meas t
  ε_indep := S.ε_indep t
  v_indep := S.v_indep t

/-- `Y_t` is square integrable. -/
lemma Y_memLp [IsProbabilityMeasure P] (t : ℕ) : MemLp (S.Y t) 2 P :=
  S.θ_sq.condExp (m := S.𝒢 t) one_le_two

/-- `E(Y_t | h^t) = θ(h^t)`. -/
lemma condExp_Y [IsProbabilityMeasure P] (t : ℕ) : P[S.Y t | S.ℱ t] =ᵐ[P] S.post t :=
  ClaimAux.condExp_tower_fin (le_sup_left : S.ℱ t ≤ S.𝒢 t) (S.periodHyp t).g_le S.θ

/-- `E(Y_t² | h^t) ≤ E(θ² | h^t)`. -/
lemma condExp_Y_sq_le [IsProbabilityMeasure P] (t : ℕ) :
    P[fun ω => S.Y t ω ^ 2 | S.ℱ t] ≤ᵐ[P] P[fun ω => S.θ ω ^ 2 | S.ℱ t] := by
  exact ClaimAux.condExp_sq_condExp_le (le_sup_left : S.ℱ t ≤ S.𝒢 t) (S.periodHyp t).g_le
    S.θ_sq

/-- `ℱ_∞ = ⨆ t, ℱ t`. -/
def ℱinf : MeasurableSpace Ω := ⨆ n, (S.ℱ n : MeasurableSpace Ω)

/-- **The Claim, upper tail.** If on `Rev t` the period-`t` decision reveals whether `ṽ_t > d`,
then almost surely, when `Rev t` happens infinitely often, `θ(h^t) → θ` and
`Var(θ | h^t) → 0`. -/
theorem claim_upper [IsProbabilityMeasure P] (d : ℝ) (Rev : ℕ → Set Ω)
    (hRev : ∀ t, MeasurableSet[S.ℱ t] (Rev t))
    (hreveal : ∀ t, ∃ A : Set Ω, MeasurableSet[S.ℱ (t + 1)] A ∧
      A =ᵐ[P] ({ω | d < S.vt t ω} ∩ Rev t)) :
    ∀ᵐ ω ∂P, (∃ᶠ t in atTop, ω ∈ Rev t) →
      Tendsto (fun t => S.post t ω) atTop (𝓝 (S.θ ω)) ∧
        Tendsto (fun t => S.postVar t ω) atTop (𝓝 0) := by
  -- Notation.
  have hFinf : S.ℱinf ≤ mΩ := iSup_le fun n => S.ℱ.le n
  have hle : ∀ t, (S.ℱ t : MeasurableSpace Ω) ≤ S.ℱinf := fun t =>
    le_iSup (fun n => (S.ℱ n : MeasurableSpace Ω)) t
  have hθi : Integrable S.θ P := S.θ_sq.integrable one_le_two
  set θi : Ω → ℝ := P[S.θ | S.ℱinf] with hθidef
  set G : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (S.ψ x)) with hGdef
  have hG : ∀ t, P.map (S.v t) = G := S.v_law
  have hGp : IsProbabilityMeasure G := by rw [← hG 0]; infer_instance
  have hLp : IsProbabilityMeasure S.Lε := by rw [← S.ε_law 0]; infer_instance
  -- The constants `c_R`.
  have hcR : ∀ R : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Set.Icc (d - R - 1) (d + R + 1), c ≤ S.ψ x := by
    intro R
    have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    obtain ⟨x0, -, hmin⟩ := (isCompact_Icc (a := d - R - 1) (b := d + R + 1)).exists_isMinOn
      (Set.nonempty_Icc.2 (by linarith)) S.ψ_cont.continuousOn
    exact ⟨S.ψ x0, S.ψ_pos x0, fun x hx => hmin hx⟩
  choose c hc0 hc using hcR
  -- The conditional quantities.
  set J : ℕ → Ω → ℝ := fun t => P[ClaimAux.jfun P (S.ℱ t) S.θ (S.ε t) G d | S.ℱ t] with hJ
  set M : ℕ → Ω → ℝ := fun t => P[ClaimAux.gYfun P (S.ℱ t) S.θ (S.ε t) | S.ℱ t] with hM
  set N : ℕ → Ω → ℝ := fun t => P[ClaimAux.nfun P (S.ℱ t) S.θ S.Lε | S.ℱ t] with hN
  set L : ℕ → Ω → ℝ := fun t => P[ClaimAux.gθfun P (S.ℱ t) S.θ | S.ℱ t] with hL
  set D : ℕ → Ω → ℝ := fun t => P[fun ω => |θi ω - (P[S.θ | S.ℱ t]) ω| | S.ℱ t] with hD
  set W : ℕ → Ω → ℝ := fun t => P[fun ω => min |S.θ ω - θi ω| 1 | S.ℱ t] with hW
  set Winf : Ω → ℝ := P[fun ω => min |S.θ ω - θi ω| 1 | S.ℱinf] with hWinf
  -- Per-period facts.
  have fa : ∀ t, ∀ᵐ ω ∂P, ω ∈ Rev t → J t ω ≤ D t ω := by
    intro t
    obtain ⟨A, hA, hAeq⟩ := hreveal t
    exact (S.periodHyp t).condExp_J_le (hG t) d (hle t) hFinf (hRev t) (hle (t + 1) _ hA) hAeq
  have fb : ∀ t, ∀ R : ℕ, ∀ᵐ ω ∂P, |S.post t ω| ≤ R → c R * M t ω ≤ J t ω := fun t R =>
    (S.periodHyp t).condExp_J_ge (hG t) hGdef d (hc0 R).le (hc R)
  have fc : ∀ t, ∀ n : ℕ, ∀ᵐ ω ∂P,
      N t ω ≤ Real.pi / 2 / ((n : ℝ) + 1) + Real.pi / 2 * ((n : ℝ) + 1) * M t ω := fun t n =>
    (S.periodHyp t).condExp_N_le (S.ε_law t) n
  have fd : ∀ t, ∀ R : ℕ, ∀ᵐ ω ∂P, |S.post t ω| ≤ R →
      ClaimAux.kconst S.Lε R * L t ω ≤ N t ω := fun t R =>
    (S.periodHyp t).condExp_N_ge (S.ε_law t) R
  have hmin_int : Integrable (fun ω => min |S.θ ω - θi ω| 1) P := by
    refine Integrable.of_bound ((continuous_abs.min continuous_const).comp_aestronglyMeasurable
      (hθi.1.sub (integrable_condExp (m := S.ℱinf) (μ := P) (f := S.θ)).1)) 1
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) zero_le_one)]
    exact min_le_right _ _
  have fe : ∀ t, ∀ n : ℕ, ∀ᵐ ω ∂P,
      W t ω ≤ 1 / ((n : ℝ) + 1) + ((n : ℝ) + 1) * L t ω + D t ω := by
    intro t n
    have hDint : Integrable (fun ω => |θi ω - (P[S.θ | S.ℱ t]) ω|) P :=
      (integrable_condExp.sub integrable_condExp).abs
    have hmono := condExp_mono (m := S.ℱ t) hmin_int
      (((integrable_const _).add ((S.periodHyp t).integrable_gθ.const_mul ((n : ℝ) + 1))).add
        (hDint.const_mul 1))
      (Eventually.of_forall fun ω => by
        have := ClaimAux.min_abs_sub_le (S.θ ω) ((P[S.θ | S.ℱ t]) ω) (θi ω) n
        simp only [ClaimAux.gθfun, Pi.add_apply]
        linarith)
    have aff := ClaimAux.condExp_affine (S.ℱ.le t) (S.periodHyp t).integrable_gθ hDint
      (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) 1
    filter_upwards [hmono, aff] with ω h1 h2
    have h1' : W t ω ≤ (P[fun ω => 1 / ((n : ℝ) + 1) + ((n : ℝ) + 1) *
        ClaimAux.gθfun P (S.ℱ t) S.θ ω + 1 * |θi ω - (P[S.θ | S.ℱ t]) ω| | S.ℱ t]) ω := h1
    rw [h2] at h1'
    simpa only [one_mul] using h1'
  have fM0 : ∀ t, ∀ᵐ ω ∂P, 0 ≤ M t ω := fun t =>
    condExp_nonneg (Eventually.of_forall fun ω => ClaimAux.gfun_nonneg _)
  have fL0 : ∀ t, ∀ᵐ ω ∂P, 0 ≤ L t ω := fun t =>
    condExp_nonneg (Eventually.of_forall fun ω => ClaimAux.gfun_nonneg _)
  have fW0 : ∀ t, ∀ᵐ ω ∂P, 0 ≤ W t ω := fun t =>
    condExp_nonneg (Eventually.of_forall fun ω => le_min (abs_nonneg _) zero_le_one)
  have fD0 : ∀ t, ∀ᵐ ω ∂P, 0 ≤ D t ω := fun t =>
    condExp_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
  -- Martingale convergence.
  have l1 : ∀ᵐ ω ∂P, Tendsto (fun t => S.post t ω) atTop (𝓝 (θi ω)) :=
    tendsto_ae_condExp S.θ
  have l2 : ∀ᵐ ω ∂P, Tendsto (fun t => (P[fun ω => S.θ ω ^ 2 | S.ℱ t]) ω) atTop
      (𝓝 ((P[fun ω => S.θ ω ^ 2 | S.ℱinf]) ω)) := tendsto_ae_condExp _
  have l3 : ∀ᵐ ω ∂P, Tendsto (fun t => D t ω) atTop (𝓝 0) :=
    ClaimAux.tendsto_condExp_abs_sub S.ℱ S.θ
  have l4 : ∀ᵐ ω ∂P, Tendsto (fun t => W t ω) atTop (𝓝 (Winf ω)) := tendsto_ae_condExp _
  -- The event `E` that `Rev t` happens infinitely often.
  set E : Set Ω := {ω | ∃ᶠ t in atTop, ω ∈ Rev t} with hEdef
  have hE : MeasurableSet[S.ℱinf] E := by
    have e : E = ⋂ a : ℕ, ⋃ b : ℕ, ⋃ (_ : a ≤ b), Rev b := by
      ext ω
      simp [hEdef, Filter.frequently_atTop]
    rw [e]
    exact MeasurableSet.iInter fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun _ => hle b _ (hRev b)
  -- Key step: `E(min(|θ - θ_∞|, 1) | ℱ_∞) = 0` on `E`.
  have hW0 : ∀ᵐ ω ∂P, ω ∈ E → Winf ω = 0 := by
    filter_upwards [ae_all_iff.2 fa, ae_all_iff.2 (fun t => ae_all_iff.2 (fb t)),
      ae_all_iff.2 (fun t => ae_all_iff.2 (fc t)), ae_all_iff.2 (fun t => ae_all_iff.2 (fd t)),
      ae_all_iff.2 (fun t => ae_all_iff.2 (fe t)), ae_all_iff.2 fM0, ae_all_iff.2 fL0,
      ae_all_iff.2 fW0, ae_all_iff.2 fD0, l1, l3, l4]
      with ω ha hb hc' hd he hM0 hL0 hW0' hD0 hl1 hl3 hl4 hωE
    obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ t, |S.post t ω| ≤ R := by
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
        (Metric.isBounded_range_of_tendsto (fun t => S.post t ω) hl1)
      refine ⟨⌈C⌉₊, fun t => ?_⟩
      have := hC _ (Set.mem_range_self t)
      rw [Real.norm_eq_abs] at this
      exact this.trans (Nat.le_ceil C)
    exact ClaimAux.final_pointwise (Rev := fun t => ω ∈ Rev t) (J := fun t => J t ω)
      (M := fun t => M t ω) (N := fun t => N t ω) (L := fun t => L t ω) (W := fun t => W t ω)
      (D := fun t => D t ω) (K := Real.pi / 2) hωE (hc0 R) (ClaimAux.kconst_pos S.Lε R)
      (fun t ht => ha t ht) (fun t => hb t R (hR t)) hM0 (fun t n => hc' t n)
      (fun t => hd t R (hR t)) hL0 (fun t n => he t n) hW0' hl3 hD0 hl4
  -- Hence `θ = θ_∞` and `E(θ² | ℱ_∞) = θ_∞²` on `E`.
  have hθeq : ∀ᵐ ω ∂P, ω ∈ E → S.θ ω = θi ω :=
    ClaimAux.eq_of_condExp_min_zero hFinf hθi hE hW0
  have hsq : ∀ᵐ ω ∂P, ω ∈ E → (P[fun ω => S.θ ω ^ 2 | S.ℱinf]) ω = θi ω ^ 2 :=
    ClaimAux.condExp_sq_eq_on hFinf S.θ_sq hE hθeq
  filter_upwards [hθeq, hsq, l1, l2] with ω h1 h2 h3 h4 hωE
  refine ⟨?_, ?_⟩
  · rw [h1 hωE]; exact h3
  · have := h4.sub (h3.pow 2)
    rw [h2 hωE, sub_self] at this
    exact this

/-- **The Claim, lower tail.** If on `Rev t` the period-`t` decision reveals whether `ṽ_t < d`,
then almost surely, when `Rev t` happens infinitely often, `θ(h^t) → θ` and
`Var(θ | h^t) → 0`. -/
theorem claim_lower [IsProbabilityMeasure P] (d : ℝ) (Rev : ℕ → Set Ω)
    (hRev : ∀ t, MeasurableSet[S.ℱ t] (Rev t))
    (hreveal : ∀ t, ∃ A : Set Ω, MeasurableSet[S.ℱ (t + 1)] A ∧
      A =ᵐ[P] ({ω | S.vt t ω < d} ∩ Rev t)) :
    ∀ᵐ ω ∂P, (∃ᶠ t in atTop, ω ∈ Rev t) →
      Tendsto (fun t => S.post t ω) atTop (𝓝 (S.θ ω)) ∧
        Tendsto (fun t => S.postVar t ω) atTop (𝓝 0) := by
  refine S.claim_upper d Rev hRev fun t => ?_
  obtain ⟨A, hA, hAeq⟩ := hreveal t
  refine ⟨Rev t \ A, (S.ℱ.mono (Nat.le_succ t) _ (hRev t)).diff hA, ?_⟩
  have hne : ∀ᵐ ω ∂P, S.vt t ω ≠ d := (S.periodHyp t).ae_ne (S.v_law t) d
  filter_upwards [hAeq, hne] with ω h1 h2
  have h1' : ω ∈ A ↔ S.vt t ω < d ∧ ω ∈ Rev t := Iff.of_eq h1
  show (ω ∈ Rev t ∧ ω ∉ A) = (d < S.vt t ω ∧ ω ∈ Rev t)
  apply propext
  constructor
  · rintro ⟨hR, hnA⟩
    refine ⟨?_, hR⟩
    rcases lt_trichotomy (S.vt t ω) d with h | h | h
    · exact absurd (h1'.2 ⟨h, hR⟩) hnA
    · exact absurd h h2
    · exact h
  · rintro ⟨hd, hR⟩
    exact ⟨hR, fun hA' => absurd (h1'.1 hA').1 (not_lt.2 hd.le)⟩

end ClaimSetup

end CC.LearnTheta
