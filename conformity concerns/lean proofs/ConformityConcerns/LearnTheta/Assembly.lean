import ConformityConcerns.LearnTheta.Model
import ConformityConcerns.LearnTheta.PoolTail
import ConformityConcerns.General.KnownMu
import ConformityConcerns.General.CentralPooling
import ConformityConcerns.LearnTheta.AsmAux.Det

/-!
# Proposition A5, the claims across histories

The last sentence of Proposition A5:

* `κ ≤ κck`: at every history at which `m(· | h^t)` is `C²` with `0 < m'' ≤ 2`, the period game
  has a fully revealing equilibrium satisfying `D1^∞` (`propA5_revealing_every_history`), and
  in every profile that is fully revealing at every history, `θ(h^t) → θ` almost surely
  (`propA5_learning`).
* `κ > κck`: in every profile that is an equilibrium satisfying `D1^∞` at every history and has
  bounded adaptation losses `E((a_t - ṽ_t)² | h^t) ≤ B`, the probability (given `h^t`) that
  player `t` chooses the central pool's action converges to one almost surely
  (`propA5_pooling`).

"At every history" is "at almost every realised history". The period game at `h^t` has the
type distribution `typeLaw` (the conditional law of `ṽ_t` given `h^t`) and the conformity loss
`κ (m(· | h^t) - min m(· | h^t))`, with `m = mfun ψ (beliefY …)`.
-/

namespace CC.LearnTheta

open MeasureTheory ProbabilityTheory Filter Topology
open CC.General
open scoped ENNReal

/-- The conditional law of `Y_t` given `h^t` is a Markov kernel. -/
instance asm_beliefY_isMarkovKernel (P : Measure Ω) [IsFiniteMeasure P] (c : Profile) (t : ℕ) :
    IsMarkovKernel (beliefY P c t) := by
  unfold beliefY; infer_instance

variable (Lθ Lε : Measure ℝ) (ψ : ℝ → ℝ) [IsProbabilityMeasure Lθ] [IsProbabilityMeasure Lε]
  [IsProbabilityMeasure (vLaw ψ)]

omit [IsProbabilityMeasure (vLaw ψ)] in
/-- **Proposition A5, `κ ≤ κck`, every history.** If `m(· | h^t)` is `C²` with `0 < m'' ≤ 2` at
the history `h`, the period game at `h` has a fully revealing equilibrium satisfying `D1^∞`. -/
theorem propA5_revealing_every_history (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ κck)
    (P : Measure Ω) [IsFiniteMeasure P] (c : Profile) (t : ℕ) (h : Fin t → ℝ)
    (hm : ContDiff ℝ 2 (mfun ψ (beliefY P c t h)))
    (hm2 : ∀ x, 0 < iteratedDeriv 2 (mfun ψ (beliefY P c t h)) x ∧
      iteratedDeriv 2 (mfun ψ (beliefY P c t h)) x ≤ 2)
    (S : Setting) (hg : S.g = fun z => z ^ 2)
    (hℓ : S.ℓ = fun x => κ * (mfun ψ (beliefY P c t h) x - mfun ψ (beliefY P c t h) S.μ)) :
    ∃ (a : ℝ → ℝ) (φ : ℝ → Measure EReal), S.IsCPBE a φ ∧ S.D1Inf a φ ∧ StrictMono a := by
  have hx : deriv (mfun ψ (beliefY P c t h)) S.μ = 0 := AsmAux.deriv_m_eq_zero hκ0 hℓ
  refine (propA5_period κ hκ0 _ hm hm2 S hx hg hℓ).1 (fun x => ?_)
  have h2 := (hm2 x).2
  calc κ * (iteratedDeriv 2 (mfun ψ (beliefY P c t h)) x / 2) ≤ κ * 1 := by
        gcongr; linarith
    _ ≤ κck := by linarith

/-- **Proposition A5, `κ ≤ κck`, social learning.** In every profile that is fully revealing at
(almost) every history, the public posterior mean `θ(h^t)` converges to `θ` almost surely. -/
theorem propA5_learning (hθ : Integrable (fun x => x ^ 2) Lθ) (hψc : Continuous ψ)
    (hψpos : ∀ x, 0 < ψ x) (P : Measure Ω) (hP : P = law Lθ Lε (vLaw ψ))
    (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (hrev : ∀ t, ∀ᵐ ω ∂P, StrictMono (c t (hist P c t ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun t => (P[thetaV | histSigma P c t]) ω) atTop (𝓝 (thetaV ω)) := by
  subst hP
  have hmono : ∀ t, ∀ᵐ ω ∂(law Lθ Lε (vLaw ψ)),
      Monotone (c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) :=
    fun t => (hrev t).mono fun ω h => h.monotone
  have hcl := (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).claim_upper 0
    (fun t => RevUp (law Lθ Lε (vLaw ψ)) c t 0)
    (fun t => measurableSet_revUp _ c hc t 0) (fun t => reveal_up _ c hc t 0 (hmono t))
  filter_upwards [hcl, ae_all_iff.2 hrev] with ω hω hs
  have hfr : ∃ᶠ t in atTop, ω ∈ RevUp (law Lθ Lε (vLaw ψ)) c t 0 :=
    Filter.Eventually.frequently (Filter.Eventually.of_forall fun t q hq => hs t hq)
  exact (hω hfr).1

section Tail

variable {ψ}

/-- Bounded second moments of the public's beliefs bound the second moments of the types. -/
lemma exists_sq_conv_bound (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (η : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (η t)] (e2 : ℕ → ℝ)
    (hη2 : ∀ t, Integrable (fun y => y ^ 2) (η t) ∧ ∫ y, y ^ 2 ∂η t ≤ e2 t)
    (M : ℝ) (hM : ∀ t, e2 t ≤ M) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t, ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(Measure.conv (η t) (vLaw ψ)) ≤ K := by
  have hG : ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂(vLaw ψ) ≠ ∞ := by
    rw [AsmAux.lintegral_sq_eq _ hv2]; exact ENNReal.ofReal_ne_top
  refine ⟨2 * ENNReal.ofReal M + 2 * ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂(vLaw ψ),
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (by simp) hG⟩, fun t => ?_⟩
  refine (AsmAux.lintegral_sq_conv_le _ _).trans ?_
  rw [AsmAux.lintegral_sq_eq _ (hη2 t).1]
  gcongr
  exact (hη2 t).2.trans (hM t)

/-- If the mass above the central pool is at least `δ` infinitely often and second moments stay
bounded, decisions infinitely often reveal whether the type exceeds a fixed natural number. -/
lemma frequently_reveal_hi (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (η : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (η t)] (e2 : ℕ → ℝ)
    (hη2 : ∀ t, Integrable (fun y => y ^ 2) (η t) ∧ ∫ y, y ^ 2 ∂η t ≤ e2 t)
    (M : ℝ) (hM : ∀ t, e2 t ≤ M)
    (S : ℕ → Setting) (a : ℕ → ℝ → ℝ) (vlo vhi : ℕ → EReal) (c₀ : ℕ → ℝ)
    (hmono : ∀ t, Monotone (a t))
    (hcp : ∀ t, (S t).IsCentralPoolingWith (a t) (vlo t) (vhi t) (c₀ t))
    {δ : ℝ} (hδ : 0 < δ) (hfreq : ∃ᶠ t in atTop, ENNReal.ofReal δ ≤
      Measure.conv (η t) (vLaw ψ) {x | vhi t < (x : EReal)}) :
    ∃ n : ℕ, ∃ᶠ t in atTop, ∀ q : ℚ, (n : ℝ) < (q : ℝ) → a t n < a t q := by
  obtain ⟨K, hKfin, hK⟩ := exists_sq_conv_bound hv2 η e2 hη2 M hM
  obtain ⟨n, hn⟩ := AsmAux.exists_nat_sq_mul_gt hKfin hδ
  refine ⟨n, hfreq.mono fun t ht q hq => ?_⟩
  exact AsmAux.reveal_hi (hmono t) (hcp t)
    (AsmAux.le_of_tail_hi (Nat.cast_nonneg n) (hK t) hn ht) hq

/-- The mirror image of `frequently_reveal_hi`, for the mass below the central pool. -/
lemma frequently_reveal_lo (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (η : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (η t)] (e2 : ℕ → ℝ)
    (hη2 : ∀ t, Integrable (fun y => y ^ 2) (η t) ∧ ∫ y, y ^ 2 ∂η t ≤ e2 t)
    (M : ℝ) (hM : ∀ t, e2 t ≤ M)
    (S : ℕ → Setting) (a : ℕ → ℝ → ℝ) (vlo vhi : ℕ → EReal) (c₀ : ℕ → ℝ)
    (hmono : ∀ t, Monotone (a t))
    (hcp : ∀ t, (S t).IsCentralPoolingWith (a t) (vlo t) (vhi t) (c₀ t))
    {δ : ℝ} (hδ : 0 < δ) (hfreq : ∃ᶠ t in atTop, ENNReal.ofReal δ ≤
      Measure.conv (η t) (vLaw ψ) {x | (x : EReal) < vlo t}) :
    ∃ n : ℕ, ∃ᶠ t in atTop, ∀ q : ℚ, (q : ℝ) < -(n : ℝ) → a t q < a t (-(n : ℝ)) := by
  obtain ⟨K, hKfin, hK⟩ := exists_sq_conv_bound hv2 η e2 hη2 M hM
  obtain ⟨n, hn⟩ := AsmAux.exists_nat_sq_mul_gt hKfin hδ
  refine ⟨n, hfreq.mono fun t ht q hq => ?_⟩
  exact AsmAux.reveal_lo (hmono t) (hcp t)
    (AsmAux.le_of_tail_lo (Nat.cast_nonneg n) (hK t) hn ht) hq

/-- Along a path on which the Claim applies, the upper tail of the central pool vanishes. -/
theorem tail_hi_tendsto (κ : ℝ) (hκ : κck < κ) (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x)
    (hψb : ∃ C, ∀ x, ψ x ≤ C) (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (θ0 : ℝ) (η : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (η t)]
    (post pv e2 : ℕ → ℝ) (hpv : ∀ t, pv t = e2 t - post t ^ 2)
    (hη1 : ∀ t, Integrable id (η t) ∧ ∫ y, y ∂η t = post t)
    (hη2 : ∀ t, Integrable (fun y => y ^ 2) (η t) ∧ ∫ y, y ^ 2 ∂η t ≤ e2 t)
    (M : ℝ) (hM : ∀ t, e2 t ≤ M)
    (S : ℕ → Setting) (a : ℕ → ℝ → ℝ) (vlo vhi : ℕ → EReal) (c₀ : ℕ → ℝ)
    (hSg : ∀ t, (S t).g = fun z => z ^ 2)
    (hSℓ : ∀ t, (S t).ℓ = fun x => κ * (mfun ψ (η t) x - mfun ψ (η t) (S t).μ))
    (hmono : ∀ t, Monotone (a t))
    (hcp : ∀ t, (S t).IsCentralPoolingWith (a t) (vlo t) (vhi t) (c₀ t))
    (hode : ∀ t, (S t).TailODE (a t) (vlo t) (vhi t))
    (B : ℝ) (hB : ∀ t, ∫⁻ x, ENNReal.ofReal ((a t x - x) ^ 2) ∂(Measure.conv (η t) (vLaw ψ)) ≤
      ENNReal.ofReal B)
    (hup : ∀ d : ℕ, (∃ᶠ t in atTop, ∀ q : ℚ, (d : ℝ) < (q : ℝ) → a t d < a t q) →
      Tendsto post atTop (𝓝 θ0) ∧ Tendsto pv atTop (𝓝 0)) :
    Tendsto (fun t => Measure.conv (η t) (vLaw ψ) {x | vhi t < (x : EReal)}) atTop (𝓝 0) := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  apply AsmAux.tendsto_zero_of_not_frequently
  intro δ hδ hfreq
  obtain ⟨n, hrev⟩ := frequently_reveal_hi hv2 η e2 hη2 M hM S a vlo vhi c₀ hmono hcp hδ hfreq
  obtain ⟨hpost, hpv0⟩ := hup n hrev
  have hdev : ∀ t, Integrable (fun y => (y - θ0) ^ 2) (η t) ∧
      ∫ y, (y - θ0) ^ 2 ∂η t ≤ pv t + (post t - θ0) ^ 2 := by
    intro t
    obtain ⟨hi, he⟩ := AsmAux.integral_sq_dev (η t) (hη1 t).1 (hη2 t).1 θ0
    refine ⟨hi, ?_⟩
    rw [he, (hη1 t).2, hpv t]
    nlinarith [(hη2 t).2]
  have hconc : Tendsto (fun t => ∫ y, (y - θ0) ^ 2 ∂η t) atTop (𝓝 0) := by
    have hup' : Tendsto (fun t => pv t + (post t - θ0) ^ 2) atTop (𝓝 0) := by
      have := hpv0.add ((hpost.sub_const θ0).pow 2)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup'
      (fun t => integral_nonneg fun y => sq_nonneg _) (fun t => (hdev t).2)
  exact upper_tail_false κ hκ ψ hψc hψpos hψb θ0 η (fun t => (hdev t).1) hconc a
    (fun t => (S t).μ) vhi
    (fun t => AsmAux.m_strictConvex hκ0 (hSℓ t))
    (fun t => AsmAux.m_differentiable hκ0 (hSℓ t))
    (fun t x => AsmAux.m_min hκ0 (hSℓ t) x)
    (fun t => (hcp t).2.1)
    (fun t x hx => by
      have h := (hode t).2.2 x (Or.inr hx)
      rwa [AsmAux.deriv_ℓ hκ0 (hSℓ t), AsmAux.deriv_g (hSg t)] at h)
    B hB δ hδ hfreq

/-- Along a path on which the Claim applies, the lower tail of the central pool vanishes. -/
theorem tail_lo_tendsto (κ : ℝ) (hκ : κck < κ) (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x)
    (hψb : ∃ C, ∀ x, ψ x ≤ C) (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (θ0 : ℝ) (η : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (η t)]
    (post pv e2 : ℕ → ℝ) (hpv : ∀ t, pv t = e2 t - post t ^ 2)
    (hη1 : ∀ t, Integrable id (η t) ∧ ∫ y, y ∂η t = post t)
    (hη2 : ∀ t, Integrable (fun y => y ^ 2) (η t) ∧ ∫ y, y ^ 2 ∂η t ≤ e2 t)
    (M : ℝ) (hM : ∀ t, e2 t ≤ M)
    (S : ℕ → Setting) (a : ℕ → ℝ → ℝ) (vlo vhi : ℕ → EReal) (c₀ : ℕ → ℝ)
    (hSg : ∀ t, (S t).g = fun z => z ^ 2)
    (hSℓ : ∀ t, (S t).ℓ = fun x => κ * (mfun ψ (η t) x - mfun ψ (η t) (S t).μ))
    (hmono : ∀ t, Monotone (a t))
    (hcp : ∀ t, (S t).IsCentralPoolingWith (a t) (vlo t) (vhi t) (c₀ t))
    (hode : ∀ t, (S t).TailODE (a t) (vlo t) (vhi t))
    (B : ℝ) (hB : ∀ t, ∫⁻ x, ENNReal.ofReal ((a t x - x) ^ 2) ∂(Measure.conv (η t) (vLaw ψ)) ≤
      ENNReal.ofReal B)
    (hlo : ∀ d : ℕ, (∃ᶠ t in atTop, ∀ q : ℚ, (q : ℝ) < -(d : ℝ) → a t q < a t (-(d : ℝ))) →
      Tendsto post atTop (𝓝 θ0) ∧ Tendsto pv atTop (𝓝 0)) :
    Tendsto (fun t => Measure.conv (η t) (vLaw ψ) {x | (x : EReal) < vlo t}) atTop (𝓝 0) := by
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  apply AsmAux.tendsto_zero_of_not_frequently
  intro δ hδ hfreq
  obtain ⟨n, hrev⟩ := frequently_reveal_lo hv2 η e2 hη2 M hM S a vlo vhi c₀ hmono hcp hδ hfreq
  obtain ⟨hpost, hpv0⟩ := hlo n hrev
  have hdev : ∀ t, Integrable (fun y => (y - θ0) ^ 2) (η t) ∧
      ∫ y, (y - θ0) ^ 2 ∂η t ≤ pv t + (post t - θ0) ^ 2 := by
    intro t
    obtain ⟨hi, he⟩ := AsmAux.integral_sq_dev (η t) (hη1 t).1 (hη2 t).1 θ0
    refine ⟨hi, ?_⟩
    rw [he, (hη1 t).2, hpv t]
    nlinarith [(hη2 t).2]
  have hconc : Tendsto (fun t => ∫ y, (y - θ0) ^ 2 ∂η t) atTop (𝓝 0) := by
    have hup' : Tendsto (fun t => pv t + (post t - θ0) ^ 2) atTop (𝓝 0) := by
      have := hpv0.add ((hpost.sub_const θ0).pow 2)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup'
      (fun t => integral_nonneg fun y => sq_nonneg _) (fun t => (hdev t).2)
  exact lower_tail_false κ hκ ψ hψc hψpos hψb θ0 η (fun t => (hdev t).1) hconc a
    (fun t => (S t).μ) vlo
    (fun t => AsmAux.m_strictConvex hκ0 (hSℓ t))
    (fun t => AsmAux.m_differentiable hκ0 (hSℓ t))
    (fun t x => AsmAux.m_min hκ0 (hSℓ t) x)
    (fun t => (hcp t).1)
    (fun t x hx => by
      have h := (hode t).2.2 x (Or.inl hx)
      rwa [AsmAux.deriv_ℓ hκ0 (hSℓ t), AsmAux.deriv_g (hSg t)] at h)
    B hB δ hδ hfreq

end Tail

/-- The Claim at every natural threshold, along a measurable profile with monotone period
strategies. -/
lemma claim_thresholds (hθ : Integrable (fun x => x ^ 2) Lθ) (hψc : Continuous ψ)
    (hψpos : ∀ x, 0 < ψ x) (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (hmono : ∀ t, ∀ᵐ ω ∂(law Lθ Lε (vLaw ψ)),
      Monotone (c t (hist (law Lθ Lε (vLaw ψ)) c t ω))) :
    (∀ d : ℕ, ∀ᵐ ω ∂(law Lθ Lε (vLaw ψ)),
      (∃ᶠ t in atTop, ω ∈ RevUp (law Lθ Lε (vLaw ψ)) c t d) →
        Tendsto (fun t => (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).post t ω) atTop (𝓝 (thetaV ω)) ∧
          Tendsto (fun t => (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).postVar t ω) atTop (𝓝 0)) ∧
    (∀ d : ℕ, ∀ᵐ ω ∂(law Lθ Lε (vLaw ψ)),
      (∃ᶠ t in atTop, ω ∈ RevDown (law Lθ Lε (vLaw ψ)) c t (-(d : ℝ))) →
        Tendsto (fun t => (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).post t ω) atTop (𝓝 (thetaV ω)) ∧
          Tendsto (fun t => (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).postVar t ω) atTop (𝓝 0)) :=
  ⟨fun d => (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).claim_upper d
      (fun t => RevUp (law Lθ Lε (vLaw ψ)) c t d)
      (fun t => measurableSet_revUp _ c hc t d) (fun t => reveal_up _ c hc t d (hmono t)),
    fun d => (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).claim_lower (-(d : ℝ))
      (fun t => RevDown (law Lθ Lε (vLaw ψ)) c t (-(d : ℝ)))
      (fun t => measurableSet_revDown _ c hc t _) (fun t => reveal_down _ c hc t _ (hmono t))⟩

/-- **The Claim in the proof of Proposition A5, as the paper states it.** Take a measurable profile
whose period strategies are monotone at almost every realized history, as they are in every
equilibrium. Almost surely, for any central pools `[vlo t, vhi t]` of the realized period
strategies: if `q_t^+ = Pr_t(ṽ_t > vhi t)` or `q_t^- = Pr_t(ṽ_t < vlo t)` does not converge to
zero, then `θ(h^t) → θ` and `Var(θ | h^t) → 0`. -/
theorem propA5_claim (hθ : Integrable (fun x => x ^ 2) Lθ)
    (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ)) (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x)
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : P = law Lθ Lε (vLaw ψ))
    (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (hmono : ∀ t, ∀ᵐ ω ∂P, Monotone (c t (hist P c t ω))) :
    ∀ᵐ ω ∂P, ∀ (S : ℕ → Setting) (vlo vhi : ℕ → EReal) (c₀ : ℕ → ℝ),
      (∀ t, (S t).IsCentralPoolingWith (c t (hist P c t ω)) (vlo t) (vhi t) (c₀ t)) →
      (¬ Tendsto (fun t => typeLaw P c t (hist P c t ω) {x | vhi t < (x : EReal)}) atTop (𝓝 0) ∨
        ¬ Tendsto (fun t => typeLaw P c t (hist P c t ω) {x | (x : EReal) < vlo t}) atTop (𝓝 0)) →
      Tendsto (fun t => (P[thetaV | histSigma P c t]) ω) atTop (𝓝 (thetaV ω)) ∧
        Tendsto (fun t => (P[fun ω => thetaV ω ^ 2 | histSigma P c t]) ω -
          (P[thetaV | histSigma P c t]) ω ^ 2) atTop (𝓝 0) := by
  subst hP
  set CS := claimSetup Lθ Lε ψ hθ hψc hψpos c hc with hCS
  obtain ⟨hup, hlo⟩ := claim_thresholds Lθ Lε ψ hθ hψc hψpos c hc hmono
  filter_upwards [ae_all_iff.2 hmono, ae_all_iff.2 (typeLaw_eq_conv Lθ Lε ψ c hc),
    ae_all_iff.2 (beliefY_sq Lθ Lε ψ hθ c hc), ae_all_iff.2 (fun t => CS.condExp_Y_sq_le t),
    ae_all_iff.2 hup, ae_all_iff.2 hlo,
    tendsto_ae_condExp (μ := law Lθ Lε (vLaw ψ)) (ℱ := CS.ℱ) (fun ω => thetaV ω ^ 2)]
    with ω hmω hcv h2 hY2 hupω hloω hlevω S vlo vhi c₀ hcp hq
  obtain ⟨M, hM⟩ := hlevω.bddAbove_range
  have hη2 : ∀ t,
      Integrable (fun y => y ^ 2)
        (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) ∧
      ∫ y, y ^ 2 ∂(beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) ≤
        ((law Lθ Lε (vLaw ψ))[fun ω => thetaV ω ^ 2 | CS.ℱ t]) ω :=
    fun t => ⟨(h2 t).1, (h2 t).2.trans_le (hY2 t)⟩
  have hM' : ∀ t, ((law Lθ Lε (vLaw ψ))[fun ω => thetaV ω ^ 2 | CS.ℱ t]) ω ≤ M :=
    fun t => hM ⟨t, rfl⟩
  have hfreq : ∀ u : ℕ → ℝ≥0∞, ¬ Tendsto u atTop (𝓝 0) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ t in atTop, ENNReal.ofReal δ ≤ u t := fun u hu => by
    by_contra h
    exact hu (AsmAux.tendsto_zero_of_not_frequently fun δ hδ hf => h ⟨δ, hδ, hf⟩)
  simp only [hcv] at hq
  rcases hq with hq | hq
  · obtain ⟨δ, hδ, hf⟩ := hfreq _ hq
    obtain ⟨n, hrev⟩ := frequently_reveal_hi hv2 _ _ hη2 M hM' S _ vlo vhi c₀ hmω hcp hδ hf
    exact hupω n hrev
  · obtain ⟨δ, hδ, hf⟩ := hfreq _ hq
    obtain ⟨n, hrev⟩ := frequently_reveal_lo hv2 _ _ hη2 M hM' S _ vlo vhi c₀ hmω hcp hδ hf
    exact hloω n hrev

/-- **Proposition A5, `κ > κck`.** In every profile that is an equilibrium satisfying `D1^∞` at
(almost) every history and has bounded adaptation losses, almost surely the probability given
`h^t` that player `t` chooses the central pool's action converges to one. -/
theorem propA5_pooling (κ : ℝ) (hκ : κck < κ) (hθ : Integrable (fun x => x ^ 2) Lθ)
    (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ)) (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x)
    (hψb : ∃ C, ∀ x, ψ x ≤ C)
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : P = law Lθ Lε (vLaw ψ))
    (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (heq : ∀ t, ∀ᵐ ω ∂P, ∃ S : Setting, S.g = (fun z => z ^ 2) ∧
      S.F = typeLaw P c t (hist P c t ω) ∧
      S.ℓ = (fun x => κ * (mfun ψ (beliefY P c t (hist P c t ω)) x -
        mfun ψ (beliefY P c t (hist P c t ω)) S.μ)) ∧
      ∃ φ : ℝ → Measure EReal, S.IsCPBE (c t (hist P c t ω)) φ ∧ S.D1Inf (c t (hist P c t ω)) φ)
    (B : ℝ) (hB : ∀ t, ∀ᵐ ω ∂P, ∫⁻ x, ENNReal.ofReal ((c t (hist P c t ω) x - x) ^ 2)
      ∂(typeLaw P c t (hist P c t ω)) ≤ ENNReal.ofReal B) :
    ∀ᵐ ω ∂P, ∃ (S : ℕ → Setting) (vlo vhi : ℕ → EReal) (c₀ : ℕ → ℝ),
      (∀ t, (S t).g = (fun z => z ^ 2) ∧ (S t).F = typeLaw P c t (hist P c t ω) ∧
        (S t).ℓ = (fun x => κ * (mfun ψ (beliefY P c t (hist P c t ω)) x -
          mfun ψ (beliefY P c t (hist P c t ω)) (S t).μ)) ∧
        (S t).IsCentralPoolingWith (c t (hist P c t ω)) (vlo t) (vhi t) (c₀ t)) ∧
      Tendsto (fun t => typeLaw P c t (hist P c t ω) (c t (hist P c t ω) ⁻¹' {c₀ t}))
        atTop (𝓝 1) := by
  subst hP
  have hκ0 : 0 < κ := lt_trans κck_pos hκ
  set CS := claimSetup Lθ Lε ψ hθ hψc hψpos c hc with hCS
  have hmono : ∀ t, ∀ᵐ ω ∂(law Lθ Lε (vLaw ψ)),
      Monotone (c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) :=
    fun t => (heq t).mono fun ω ⟨_, _, _, _, _, hE, _⟩ => hE.monotone
  obtain ⟨hup, hlo⟩ := claim_thresholds Lθ Lε ψ hθ hψc hψpos c hc hmono
  have hlevy := tendsto_ae_condExp (μ := law Lθ Lε (vLaw ψ)) (ℱ := CS.ℱ)
    (fun ω => thetaV ω ^ 2)
  filter_upwards [ae_all_iff.2 heq, ae_all_iff.2 hB,
    ae_all_iff.2 (typeLaw_eq_conv Lθ Lε ψ c hc),
    ae_all_iff.2 (beliefY_mean Lθ Lε ψ c hc), ae_all_iff.2 (beliefY_sq Lθ Lε ψ hθ c hc),
    ae_all_iff.2 (fun t => CS.condExp_Y t), ae_all_iff.2 (fun t => CS.condExp_Y_sq_le t),
    ae_all_iff.2 hup, ae_all_iff.2 hlo, hlevy]
    with ω hE hBω hcv h1 h2 hY hY2 hupω hloω hlevω
  choose S hSg hSF hSℓ φ hEq hD using hE
  choose vlo vhi c₀ hcp hode using fun t => propA3_i (S t) (hEq t) (hD t)
  obtain ⟨M, hM⟩ := hlevω.bddAbove_range
  have hSF' : ∀ t, (S t).F = Measure.conv
      (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) (vLaw ψ) :=
    fun t => (hSF t).trans (hcv t)
  have hB' : ∀ t, ∫⁻ x, ENNReal.ofReal
      ((c t (hist (law Lθ Lε (vLaw ψ)) c t ω) x - x) ^ 2) ∂(Measure.conv
        (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) (vLaw ψ)) ≤
      ENNReal.ofReal B := fun t => by rw [← hcv t]; exact hBω t
  have hη1 : ∀ t,
      Integrable id (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) ∧
      ∫ y, y ∂(beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) =
        CS.post t ω := fun t => ⟨(h1 t).1, (h1 t).2.trans (hY t)⟩
  have hη2 : ∀ t,
      Integrable (fun y => y ^ 2)
        (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) ∧
      ∫ y, y ^ 2 ∂(beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) ≤
        ((law Lθ Lε (vLaw ψ))[fun ω => thetaV ω ^ 2 | CS.ℱ t]) ω :=
    fun t => ⟨(h2 t).1, (h2 t).2.trans_le (hY2 t)⟩
  have hM' : ∀ t, ((law Lθ Lε (vLaw ψ))[fun ω => thetaV ω ^ 2 | CS.ℱ t]) ω ≤ M :=
    fun t => hM ⟨t, rfl⟩
  have hmono' : ∀ t, Monotone (c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) :=
    fun t => (hEq t).monotone
  have hhi := tail_hi_tendsto κ hκ hψc hψpos hψb hv2 (thetaV ω)
    (fun t => beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω))
    (fun t => CS.post t ω) (fun t => CS.postVar t ω)
    (fun t => ((law Lθ Lε (vLaw ψ))[fun ω => thetaV ω ^ 2 | CS.ℱ t]) ω) (fun t => rfl)
    hη1 hη2 M hM' S (fun t => c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) vlo vhi c₀ hSg hSℓ hmono'
    hcp hode B hB' (fun d hd => hupω d hd)
  have hlo' := tail_lo_tendsto κ hκ hψc hψpos hψb hv2 (thetaV ω)
    (fun t => beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω))
    (fun t => CS.post t ω) (fun t => CS.postVar t ω)
    (fun t => ((law Lθ Lε (vLaw ψ))[fun ω => thetaV ω ^ 2 | CS.ℱ t]) ω) (fun t => rfl)
    hη1 hη2 M hM' S (fun t => c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) vlo vhi c₀ hSg hSℓ hmono'
    hcp hode B hB' (fun d hd => hloω d hd)
  have hfin := AsmAux.pool_tendsto_one
    (fun t => Measure.conv
      (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) (vLaw ψ))
    (fun t x => by rw [← hSF' t]; exact (S t).hF.singleton_eq_zero x)
    (fun t => c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) vlo vhi c₀
    (fun t v h1 h2 => (hcp t).2.2.1 v h1 h2) hhi hlo'
  refine ⟨S, vlo, vhi, c₀, fun t => ⟨hSg t, hSF t, hSℓ t, hcp t⟩, ?_⟩
  simp only [hcv]
  exact hfin

end CC.LearnTheta
