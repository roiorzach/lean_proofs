import ConformityConcerns.Bridge.Corollaries
import ConformityConcerns.Bridge.AsyAux.SLIff
import ConformityConcerns.Bridge.AsyAux.Closed

/-!
# Social-learning criterion (proof of Proposition 2) and the asymptotic payoffs of
# Corollaries A2 and A3 as unconditional expectations

* The proof of Proposition 2 opens with: social learning about `θ` occurs if and only if
  `σ²_{θ,t} → 0` almost surely (likewise for `μ`). `socialLearning_theta_iff` and
  `socialLearning_mu_iff` prove this in the Gaussian model.
* The paper defines the asymptotic adaptation loss as `lim E(-(a_t - γ_t θ - v_t)²)` and the
  asymptotic utility as `lim E(u_t)`, with `E` the unconditional expectation. Here `u_t` is the
  adaptation term minus `κ ∫ (b - μ(h^t))² φ(db | h^t, a_t)`, where on path `φ(· | h^t, a_t)` is
  the public's posterior about `v_t`, the conditional law of `v_t` given `(h^t, a_t)`.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- Player `t`'s preference type `v_t = μ + ν_t`. -/
def vType (t : ℕ) (ω : Ωg) : ℝ := priv t ω 1

/-- The public history vector `h^t = (γ_0, …, γ_t; a_0, …, a_{t-1})`. -/
noncomputable def histVecB (κ : ℝ) (S₁ : M2) (G : Measure ℝ) (t : ℕ) (ω : Ωg) :
    (Fin (t + 1) → ℝ) × (Fin t → ℝ) :=
  ((fun i : Fin (t + 1) => gam ω i), (fun i : Fin t => eqAct κ S₁ G i ω))

/-- Expected adaptation payoff at date `t`: `E(-(a_t - γ_t θ - v_t)²)`. -/
noncomputable def expAdapt (κ : ℝ) (S₁ : M2) (G : Measure ℝ) (t : ℕ) : ℝ :=
  ∫ ω, -(eqAct κ S₁ G t ω - gam ω t * thetaV ω - vType t ω) ^ 2 ∂(lawG S₁ G)

/-- Expected utility at date `t`: the expected adaptation payoff minus `κ` times the expected
conformity term `∫ (b - μ(h^t))² φ(db | h^t, a_t)`, with `φ(· | h^t, a_t)` the conditional law
of `v_t` given `(h^t, a_t)`. -/
noncomputable def expUtility (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]
    (t : ℕ) : ℝ :=
  expAdapt κ S₁ G t - κ * ∫ ω, (∫ b, (b - postMu κ S₁ G t ω) ^ 2 ∂(condDistrib (vType t)
    (fun ω => (histVecB κ S₁ G t ω, eqAct κ S₁ G t ω)) (lawG S₁ G)
      (histVecB κ S₁ G t ω, eqAct κ S₁ G t ω))) ∂(lawG S₁ G)

/-- The expected adaptation payoff is minus the integral over the weights of the second moment
`adaptQ` of the adaptation error along the weight path. -/
lemma expAdapt_eq (S₁ : M2) (hS : S₁.PosSemidef) (G : Measure ℝ) [IsProbabilityMeasure G]
    (κ : ℝ) (t : ℕ) :
    expAdapt κ S₁ G t =
      -(∫⁻ γ, ENNReal.ofReal (adaptQ κ S₁ γ t) ∂(Measure.infinitePi fun _ : ℕ => G)).toReal := by
  have h : ∫ ω, (eqAct κ S₁ G t ω - gam ω t * thetaV ω - vType t ω) ^ 2 ∂(lawG S₁ G) =
      (∫⁻ γ, ENNReal.ofReal (adaptQ κ S₁ γ t) ∂(Measure.infinitePi fun _ : ℕ => G)).toReal :=
    integral_adapt κ S₁ G hS t
  unfold expAdapt
  rw [integral_neg, h]

/-- The expected conformity term is `E(v_t - μ(h^t))² = E(1 + σ²_{μ,t})`. -/
lemma expUtility_eq (S₁ : M2) (hS : S₁.PosSemidef) (G : Measure ℝ) [IsProbabilityMeasure G]
    (κ : ℝ) (t : ℕ) :
    expUtility κ S₁ G t = expAdapt κ S₁ G t - κ *
      (∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t 1 1 + 1) ∂(Measure.infinitePi fun _ : ℕ => G)).toReal := by
  have hc := integral_condDistrib_sq (μ := lawG S₁ G)
    (W := fun ω => (histVecB κ S₁ G t ω, eqAct κ S₁ G t ω)) (Y := vType t)
    (p := postMu κ S₁ G t) (measurable_histAct κ S₁ G t) (measurable_priv1 t)
    (sm_postMu_hist κ S₁ G t) (integrable_conf κ S₁ G hS t)
  have h2 : ∫ ω, (vType t ω - postMu κ S₁ G t ω) ^ 2 ∂(lawG S₁ G) =
      (∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t 1 1 + 1)
        ∂(Measure.infinitePi fun _ : ℕ => G)).toReal :=
    integral_conf κ S₁ G hS t
  unfold expUtility
  rw [hc, h2]

/-- **Proof of Proposition 2, first sentence (`θ`).** Social learning about `θ` occurs if and only
if `σ²_{θ,t} → 0` almost surely. -/
theorem socialLearning_theta_iff (S₁ : M2) (hS : S₁.PosSemidef) (G : Measure ℝ)
    [IsProbabilityMeasure G] (κ : ℝ) :
    SLOccurs (lawG S₁ G) thetaV (postTheta κ S₁ G) ↔
      ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => Sig κ S₁ ω t 0 0) atTop (𝓝 0) :=
  sl_iff_entry κ S₁ G hS 0

/-- **Proof of Proposition 2, first sentence (`μ`).** Social learning about `μ` occurs if and only
if `σ²_{μ,t} → 0` almost surely. -/
theorem socialLearning_mu_iff (S₁ : M2) (hS : S₁.PosSemidef) (G : Measure ℝ)
    [IsProbabilityMeasure G] (κ : ℝ) :
    SLOccurs (lawG S₁ G) muV (postMu κ S₁ G) ↔
      ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => Sig κ S₁ ω t 1 1) atTop (𝓝 0) :=
  sl_iff_entry κ S₁ G hS 1

/-- **Corollary A2, asymptotic payoffs as unconditional expectations.** With `θ` known
(`Σ₁ = diag(0, σ²_μ)`) and any law of the weights, the expected adaptation payoff and expected
utility of the signaling equilibrium converge to the closed forms of Corollary A2. -/
theorem corollaryA2_asymptotic (σμ2 : ℝ) (hσ : 0 < σμ2) (G : Measure ℝ)
    [IsProbabilityMeasure G] (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun t => expAdapt κ !![0, 0; 0, σμ2] G t) atTop
        (𝓝 (if κ ≤ κck then -((1 - √(1 - 4 * κ)) / 2) ^ 2 else -(1 + σμ2))) ∧
      Tendsto (fun t => expUtility κ !![0, 0; 0, σμ2] G t) atTop
        (𝓝 (if κ ≤ κck then -((1 - √(1 - 4 * κ)) / 2) else -((1 + κ) * (1 + σμ2)))) := by
  have hS : (!![0, 0; 0, σμ2] : M2).PosSemidef := psd_diag 0 σμ2 le_rfl hσ.le
  have hc0 : 0 ≤ (if κ ≤ κck then ((1 - √(1 - 4 * κ)) / 2) ^ 2 else 1) := by
    split_ifs <;> positivity
  have hA : ∀ t, expAdapt κ !![0, 0; 0, σμ2] G t =
      -((if κ ≤ κck then ((1 - √(1 - 4 * κ)) / 2) ^ 2 else 1) * (1 + yA2 σμ2 κ t)) := by
    intro t
    have hy := yA2_nonneg σμ2 hσ κ t
    rw [expAdapt_eq _ hS G κ t]
    simp_rw [adaptQ_A2 σμ2 hσ κ hκ _ t]
    rw [lintegral_const, measure_univ, mul_one,
      ENNReal.toReal_ofReal (mul_nonneg hc0 (by linarith))]
  have hC : ∀ t, (∫⁻ γ, ENNReal.ofReal (SigP κ !![0, 0; 0, σμ2] γ t 1 1 + 1)
      ∂(Measure.infinitePi fun _ : ℕ => G)).toReal = 1 + yA2 σμ2 κ t := by
    intro t
    have hy := yA2_nonneg σμ2 hσ κ t
    simp_rw [sigP11_A2 σμ2 hσ κ hκ _ t]
    rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal (by linarith), add_comm]
  have hU : ∀ t, expUtility κ !![0, 0; 0, σμ2] G t =
      -((if κ ≤ κck then ((1 - √(1 - 4 * κ)) / 2) ^ 2 else 1) * (1 + yA2 σμ2 κ t)) -
        κ * (1 + yA2 σμ2 κ t) := by
    intro t
    rw [expUtility_eq _ hS G κ t, hA t, hC t]
  simp only [hA, hU]
  by_cases h : κ ≤ κck
  · have hy : Tendsto (yA2 σμ2 κ) atTop (𝓝 0) := by
      have e : yA2 σμ2 κ = fun t : ℕ => σμ2 / (1 + t * σμ2) := funext fun t => by
        simp only [yA2, h, ↓reduceIte]
      rw [e]
      exact CorA2.tendsto_seq σμ2 hσ
    simp only [h, ↓reduceIte]
    obtain ⟨-, -, s2⟩ := CorA2.sqrt_facts hκ h
    have l1 := (tendsto_const_nhds (x := (1 : ℝ))).add hy
    constructor
    · have := (l1.const_mul (((1 - √(1 - 4 * κ)) / 2) ^ 2)).neg
      convert this using 2
      ring
    · have := ((l1.const_mul (((1 - √(1 - 4 * κ)) / 2) ^ 2)).neg).sub (l1.const_mul κ)
      convert this using 2
      nlinarith [s2]
  · have hy : ∀ t, yA2 σμ2 κ t = σμ2 := fun t => by simp only [yA2, h, ↓reduceIte]
    simp only [h, ↓reduceIte, hy, one_mul]
    constructor
    · exact tendsto_const_nhds
    · convert (tendsto_const_nhds (x := -((1 + κ) * (1 + σμ2)))) using 2
      ring

/-- **Corollary A3, asymptotic payoffs as unconditional expectations.** With `μ` known
(`Σ₁ = diag(σ²_θ, 0)`) and `γ_t = 1`, the asymptotic adaptation loss and the asymptotic utility,
as limits of unconditional expectations, exist; the first is weakly decreasing and the second
decreasing in `κ`. -/
theorem corollaryA3_asymptotic (σθ2 : ℝ) (hσ : 0 < σθ2) :
    ∃ AAL AU : ℝ → ℝ, AntitoneOn AAL (Ioi 0) ∧ StrictAntiOn AU (Ioi 0) ∧
      ∀ κ, 0 < κ →
        Tendsto (fun t => expAdapt κ !![σθ2, 0; 0, 0] (Measure.dirac 1) t) atTop (𝓝 (AAL κ)) ∧
        Tendsto (fun t => expUtility κ !![σθ2, 0; 0, 0] (Measure.dirac 1) t) atTop
          (𝓝 (AU κ)) := by
  obtain ⟨-, -, AAL, AU, hAAL, hAU, hlim⟩ := CC.corollaryA3 σθ2 hσ
  refine ⟨AAL, AU, hAAL, hAU, fun κ hκ => ?_⟩
  have hS : (!![σθ2, 0; 0, 0] : M2).PosSemidef := psd_diag σθ2 0 hσ.le le_rfl
  have hx : ∀ t, 0 < (CorA3.stepA κ)^[t] σθ2 := fun t => CorA3.iterate_stepA_pos κ σθ2 hσ t
  have hseq : ∀ t, SigmaSeq (fun _ => κ) !![σθ2, 0; 0, 0] (fun _ => 1) t =
      !![(CorA3.stepA κ)^[t] σθ2, 0; 0, 0] := fun t => CorA3.seq_eq σθ2 hσ κ hκ t
  have hPSD : ∀ t, (SigmaSeq (fun _ => κ) !![σθ2, 0; 0, 0] (fun _ => 1) t).PosSemidef :=
    fun t => by rw [hseq t]; exact psd_diag _ 0 (hx t).le le_rfl
  -- a signaling equilibrium of each period game
  choose a φ hE using fun t => (LG.lemma1 _ (gameAt_std (m := 0) (γ := 1) (hPSD t) hκ)).1
  obtain ⟨l1, l2⟩ := hlim κ hκ (fun _ => 0) a φ hE
  -- its values
  have hv : ∀ t,
      (gameAt 0 (SigmaSeq (fun _ => κ) !![σθ2, 0; 0, 0] (fun _ => 1) t) 1 κ).exAdapt (a t) =
        -((if κ * CorA3.s3 ((CorA3.stepA κ)^[t] σθ2) ^ 2 ≤ κck then
            ((1 - √(1 - 4 * κ * CorA3.s3 ((CorA3.stepA κ)^[t] σθ2) ^ 2)) / 2) ^ 2 else 1) *
          (1 + ((CorA3.stepA κ)^[t] σθ2) ^ 2 / (1 + (CorA3.stepA κ)^[t] σθ2))) -
          (CorA3.stepA κ)^[t] σθ2 / (1 + (CorA3.stepA κ)^[t] σθ2) ∧
      (gameAt 0 (SigmaSeq (fun _ => κ) !![σθ2, 0; 0, 0] (fun _ => 1) t) 1 κ).exUtility (a t)
          (φ t) =
        -((if κ * CorA3.s3 ((CorA3.stepA κ)^[t] σθ2) ^ 2 ≤ κck then
            ((1 - √(1 - 4 * κ * CorA3.s3 ((CorA3.stepA κ)^[t] σθ2) ^ 2)) / 2) ^ 2 else 1) *
          (1 + ((CorA3.stepA κ)^[t] σθ2) ^ 2 / (1 + (CorA3.stepA κ)^[t] σθ2)) + κ) -
          (CorA3.stepA κ)^[t] σθ2 / (1 + (CorA3.stepA κ)^[t] σθ2) := by
    intro t
    have hEt := hE t
    rw [hseq t] at hEt ⊢
    exact CorA3.values κ hκ 0 _ (hx t).le (a t) (φ t) hEt
  -- the expectations along the constant weight path
  have hae : ∀ f : (ℕ → ℝ) → ENNReal,
      (fun γ => f γ) =ᵐ[Measure.infinitePi fun _ : ℕ => Measure.dirac (1 : ℝ)]
        fun _ => f (fun _ => 1) := fun f => by
    filter_upwards [ae_eq_one_dirac] with γ hγ
    rw [hγ]
  have hmA : ∀ t, expAdapt κ !![σθ2, 0; 0, 0] (Measure.dirac 1) t =
      -(adaptQ κ !![σθ2, 0; 0, 0] (fun _ => 1) t) := by
    intro t
    have hnn : 0 ≤ adaptQ κ !![σθ2, 0; 0, 0] (fun _ => 1) t := by
      rw [adaptQ_A3 σθ2 hσ κ hκ t]
      have := hx t
      split_ifs <;> positivity
    rw [expAdapt_eq _ hS _ κ t,
      lintegral_congr_ae (hae fun γ => ENNReal.ofReal (adaptQ κ !![σθ2, 0; 0, 0] γ t)),
      lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hnn]
  have hmC : ∀ t, (∫⁻ γ, ENNReal.ofReal (SigP κ !![σθ2, 0; 0, 0] γ t 1 1 + 1)
      ∂(Measure.infinitePi fun _ : ℕ => Measure.dirac (1 : ℝ))).toReal = 1 := by
    intro t
    rw [lintegral_congr_ae (hae fun γ => ENNReal.ofReal (SigP κ !![σθ2, 0; 0, 0] γ t 1 1 + 1)),
      lintegral_const, measure_univ, mul_one, sigP11_A3 σθ2 hσ κ hκ t, zero_add,
      ENNReal.toReal_ofReal zero_le_one]
  constructor
  · refine Tendsto.congr (fun t => ?_) l1
    rw [(hv t).1, hmA t, adaptQ_A3 σθ2 hσ κ hκ t]
    ring
  · refine Tendsto.congr (fun t => ?_) l2
    rw [(hv t).2, expUtility_eq _ hS _ κ t, hmA t, hmC t, adaptQ_A3 σθ2 hσ κ hκ t]
    ring

end CC.Bridge
