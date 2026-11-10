import ConformityConcerns.Bridge.BeliefsCore
import ConformityConcerns.Bridge.Occurs

/-!
# Posterior means are the Kalman means; second moments of linear forms of the period-`t` errors

* `post_ae`: the posterior mean of `x_i` given the information at date `t` is (almost surely) the
  Kalman mean `m_{t,i}`;
* `fiber_law`: along a weight path, the error `x - m_t` and the period-`t` noise are independent,
  with laws `N(0, Σ_t)` and `N(0, I)`;
* `lintegral_sq_lin`: the second moment of a linear form in `(x - m_t, ε_t)` with coefficients
  depending on the weights is the integral over the weights of the corresponding quadratic form
  in `Σ_t`.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

set_option warn.classDefReducibility false

variable (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]

/-- The law of the weights. -/
lemma lawG_map_gam : (lawG S₁ G).map gam = Measure.infinitePi (fun _ : ℕ => G) := by
  have h : gam = Prod.snd ∘ Prod.snd := rfl
  unfold lawG
  rw [h, ← Measure.map_map measurable_snd measurable_snd, Measure.map_snd_prod, measure_univ,
    one_smul, Measure.map_snd_prod, measure_univ, one_smul]

lemma lint_gam {f : (ℕ → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ γ, f γ ∂(Measure.infinitePi fun _ : ℕ => G) = ∫⁻ ω, f (gam ω) ∂(lawG S₁ G) := by
  rw [← lawG_map_gam S₁ G, lintegral_map hf measurable_gam]

lemma ae_lawG_of_ae_gam {p : (ℕ → ℝ) → Prop}
    (h : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G), p γ) : ∀ᵐ ω ∂(lawG S₁ G), p (gam ω) := by
  rw [← lawG_map_gam S₁ G] at h
  exact ae_of_ae_map measurable_gam.aemeasurable h

lemma mtF_infoV (t : ℕ) (ω : Ωg) :
    mtF κ S₁ t (infoV κ S₁ t ω) = kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t := by
  unfold mtF infoV
  exact kmean_congr κ S₁ (fun s hs => extF_apply_lt _ (Nat.lt_succ_of_lt hs))
    (fun s hs => extF_apply_lt _ hs)

lemma integral_coord_mvG {m : E2} {S : M2} (hS : S.PosSemidef) (i : Fin 2) :
    ∫ y, y i ∂(multivariateGaussian m S) = m i := by
  have hmp := measurePreserving_eval_multivariateGaussian (μ := m) hS (i := i)
  have h := integral_map (μ := multivariateGaussian m S) hmp.measurable.aemeasurable
    (f := fun x : ℝ => x) aestronglyMeasurable_id
  rw [hmp.map_eq, integral_id_gaussianReal] at h
  exact h.symm

/-- The posterior mean of `x_i` is the Kalman mean. -/
theorem post_ae (hS₁ : S₁.PosSemidef) (i : Fin 2) (t : ℕ) :
    (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ t] =ᵐ[lawG S₁ G]
      fun ω => kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t i := by
  have hV := measurable_infoV κ S₁ t
  have h1 := condExp_ae_eq_integral_condDistrib (μ := lawG S₁ G) (X := infoV κ S₁ t)
    (Y := fun ω : Ωg => ω.1) hV measurable_fst.aemeasurable (f := fun y : E2 => y i)
    (br_meas_coord measurable_id i).stronglyMeasurable (integrable_coord_lawG S₁ G i)
  have h2 := beliefs_core κ S₁ t hS₁ G
  filter_upwards [h1, h2] with ω a b
  refine a.trans ?_
  have hpsd : (Sig κ S₁ ω t).PosSemidef := SigmaC_psd' (fun _ => κ) (gam ω) S₁ hS₁ t
  rw [b, integral_coord_mvG hpsd i, mtF_infoV]

/-- Along a weight path, the error `x - m_t` and the noise `ε_t` are independent with laws
`N(0, Σ_t)` and `N(0, I)`. -/
lemma fiber_law (hS₁ : S₁.PosSemidef) (γ : ℕ → ℝ) (t : ℕ) :
    (Qm S₁).map (fun p : E2 × (ℕ → E2) => (errF κ S₁ γ p.1 p.2 t, p.2 t)) =
      (multivariateGaussian 0 (SigP κ S₁ γ t)).prod (stdGaussian E2) := by
  have he := measurable_errF κ S₁ γ t
  have hξ : Measurable (fun p : E2 × (ℕ → E2) => p.2 t) :=
    (measurable_pi_apply t).comp measurable_snd
  have h1 : IndepFun (fun p : E2 × (ℕ → E2) => errF κ S₁ γ p.1 p.2 t) (fun p => p.2 t)
      (Qm S₁) := by
    have := (indep_past_noise S₁ t).comp
      (φ := fun q : E2 × (ℕ → E2) => errF κ S₁ γ q.1 q.2 t) (ψ := id)
      (measurable_errF κ S₁ γ t) measurable_id
    have e : (fun p : E2 × (ℕ → E2) => errF κ S₁ γ p.1 p.2 t) =
        (fun q : E2 × (ℕ → E2) => errF κ S₁ γ q.1 q.2 t) ∘
          (fun p : E2 × (ℕ → E2) => (p.1, truncE t p.2)) := by
      funext p
      simp only [Function.comp, errF_truncE]
    rw [e]
    exact this
  rw [(indepFun_iff_map_prod_eq_prod_map_map he.aemeasurable hξ.aemeasurable).1 h1,
    (kalman_fiber κ S₁ γ hS₁ t).2, law_noise S₁ t]

/-- Integrals of functions of the weights, the error `x - m_t` and the noise `ε_t`. -/
lemma lintegral_fiber (hS₁ : S₁.PosSemidef) (t : ℕ) (Φ : (ℕ → ℝ) × (E2 × E2) → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (gam ω, (ω.1 - kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t, ω.2.1 t))
        ∂(lawG S₁ G) =
      ∫⁻ γ, ∫⁻ q, Φ (γ, q) ∂((multivariateGaussian 0 (SigP κ S₁ γ t)).prod (stdGaussian E2))
        ∂(Measure.infinitePi fun _ : ℕ => G) := by
  have hk : Measurable (fun ω : Ωg => kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t) :=
    (measurable_kmean κ S₁ t).comp (measurable_gam.prodMk (measurable_obsSeq κ S₁))
  have hm : Measurable (fun ω : Ωg =>
      Φ (gam ω, (ω.1 - kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t, ω.2.1 t))) :=
    hΦ.comp (measurable_gam.prodMk ((measurable_fst.sub hk).prodMk
      ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd))))
  rw [lintegral_lawG S₁ G _ hm]
  congr 1
  funext γ
  have hΦγ : Measurable (fun q : E2 × E2 => Φ (γ, q)) :=
    hΦ.comp (measurable_const.prodMk measurable_id)
  have hg : Measurable (fun p : E2 × (ℕ → E2) => (errF κ S₁ γ p.1 p.2 t, p.2 t)) :=
    (measurable_errF κ S₁ γ t).prodMk ((measurable_pi_apply t).comp measurable_snd)
  rw [← fiber_law κ S₁ hS₁ γ t, lintegral_map hΦγ hg]
  rfl

/-- The quadratic form `(a, b) ↦ aᵀ Σ a + bᵀ b`. -/
def qf (S : M2) (a0 a1 b0 b1 : ℝ) : ℝ :=
  a0 * (S 0 0 * a0 + S 0 1 * a1) + a1 * (S 1 0 * a0 + S 1 1 * a1) + (b0 * b0 + b1 * b1)

lemma lintegral_sq_affine {S : M2} (hS : S.PosSemidef) (a0 a1 b0 b1 : ℝ) :
    ∫⁻ q : E2 × E2, ENNReal.ofReal ((a0 * q.1 0 + a1 * q.1 1 + (b0 * q.2 0 + b1 * q.2 1)) ^ 2)
        ∂((multivariateGaussian 0 S).prod (stdGaussian E2)) =
      ENNReal.ofReal (qf S a0 a1 b0 b1) := by
  let f : E2 × E2 → ℝ := fun q => a0 * q.1 0 + a1 * q.1 1 + (b0 * q.2 0 + b1 * q.2 1)
  have hf : ∀ ω : E2 × E2, f ω = 0 + (a0 * ω.1 0 + a1 * ω.1 1) + (b0 * ω.2 0 + b1 * ω.2 1) :=
    fun ω => by simp only [f]; ring
  have hL := cc_memLp_coord (m := 0) (S := S) hf
  have hmean : ∫ ω, f ω ∂((multivariateGaussian 0 S).prod (stdGaussian E2)) = 0 := by
    rw [cc_integral_coord hf]; simp
  have hvar := variance_of_integral_eq_zero hL.aestronglyMeasurable.aemeasurable hmean
  have hcov := cc_cov_coord (m := 0) hS hf hf
  rw [covariance_self hL.aestronglyMeasurable.aemeasurable, hvar] at hcov
  show ∫⁻ q : E2 × E2, ENNReal.ofReal (f q ^ 2) ∂_ = _
  rw [← ofReal_integral_eq_lintegral_ofReal hL.integrable_sq
    (ae_of_all _ fun _ => sq_nonneg _), hcov]
  rfl

/-- **Second moment of a linear form in `(x - m_t, ε_t)`.** -/
theorem lintegral_sq_lin (hS₁ : S₁.PosSemidef) (t : ℕ) {a0 a1 b0 b1 : (ℕ → ℝ) → ℝ}
    (h0 : Measurable a0) (h1 : Measurable a1) (h2 : Measurable b0) (h3 : Measurable b1) :
    ∫⁻ ω, ENNReal.ofReal
        ((a0 (gam ω) * (ω.1 0 - kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t 0) +
          a1 (gam ω) * (ω.1 1 - kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t 1) +
          (b0 (gam ω) * ω.2.1 t 0 + b1 (gam ω) * ω.2.1 t 1)) ^ 2) ∂(lawG S₁ G) =
      ∫⁻ γ, ENNReal.ofReal (qf (SigP κ S₁ γ t) (a0 γ) (a1 γ) (b0 γ) (b1 γ))
        ∂(Measure.infinitePi fun _ : ℕ => G) := by
  let Φ : (ℕ → ℝ) × (E2 × E2) → ℝ≥0∞ := fun z => ENNReal.ofReal
    ((a0 z.1 * z.2.1 0 + a1 z.1 * z.2.1 1 + (b0 z.1 * z.2.2 0 + b1 z.1 * z.2.2 1)) ^ 2)
  have c0 : Measurable (fun z : (ℕ → ℝ) × (E2 × E2) => z.2.1 0) :=
    br_meas_coord (measurable_fst.comp measurable_snd) 0
  have c1 : Measurable (fun z : (ℕ → ℝ) × (E2 × E2) => z.2.1 1) :=
    br_meas_coord (measurable_fst.comp measurable_snd) 1
  have d0 : Measurable (fun z : (ℕ → ℝ) × (E2 × E2) => z.2.2 0) :=
    br_meas_coord (measurable_snd.comp measurable_snd) 0
  have d1 : Measurable (fun z : (ℕ → ℝ) × (E2 × E2) => z.2.2 1) :=
    br_meas_coord (measurable_snd.comp measurable_snd) 1
  have hΦ : Measurable Φ := ENNReal.measurable_ofReal.comp
    (((((h0.comp measurable_fst).mul c0).add ((h1.comp measurable_fst).mul c1)).add
      (((h2.comp measurable_fst).mul d0).add ((h3.comp measurable_fst).mul d1))).pow_const 2)
  refine (lintegral_congr fun ω => ?_).trans ((lintegral_fiber κ S₁ G hS₁ t Φ hΦ).trans
    (lintegral_congr fun γ => ?_))
  · simp only [Φ, PiLp.sub_apply]
  · exact lintegral_sq_affine (SigmaC_psd' (fun _ => κ) γ S₁ hS₁ t) (a0 γ) (a1 γ) (b0 γ) (b1 γ)

end CC.Bridge
