import ConformityConcerns.BridgeK.Defs
import ConformityConcerns.Bridge.Kalman

/-!
# One Gaussian regression step with a general linear signal

On `Ω₂ = ℝ² × ℝ²` with law `N(0, Σ) ⊗ N(0, I)` (outcome `(e, ζ)`), the signal
`Z = a · e + b · ζ` has variance `V = aᵀ Σ a + bᵀ b`. The residual `e - Z k` of the regression of
`e` on `Z`, with `k = V⁻¹ Σ a`, is independent of `Z` and has law `N(0, Σ - V⁻¹ (Σ a)(Σ a)ᵀ)`
(`updG`). (When `V = 0`, `Σ a = 0` and all formulas hold with `0⁻¹ = 0`.)

A revealing action is the case `a = b = A_t` (`updG = kalman`), a disclosure of `x_i + √n ξ` the
case `a = e_i`, `b = √n e_i` (`updG = observeTheta / observeMu`), and an uninformative slot the
case `a = b = 0` (`updG = Σ`).
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

set_option warn.classDefReducibility false

/-- The signal `Z = a · e + b · ζ`. -/
def ZG (a b : Fin 2 → ℝ) (ω : Ω₂) : ℝ :=
  (a 0 * ω.1 0 + a 1 * ω.1 1) + (b 0 * ω.2 0 + b 1 * ω.2 1)

/-- `Var Z = aᵀ Σ a + bᵀ b`. -/
def VG (S : M2) (a b : Fin 2 → ℝ) : ℝ := a ⬝ᵥ (S *ᵥ a) + b ⬝ᵥ b

/-- The regression coefficient `k = V⁻¹ Σ a`. -/
noncomputable def kG (S : M2) (a b : Fin 2 → ℝ) : E2 := (VG S a b)⁻¹ • WithLp.toLp 2 (S *ᵥ a)

/-- The residual `e - Z k`. -/
noncomputable def resG (S : M2) (a b : Fin 2 → ℝ) (ω : Ω₂) : E2 := ω.1 - ZG a b ω • kG S a b

/-- The posterior covariance `Σ - V⁻¹ (Σ a)(Σ a)ᵀ`. -/
noncomputable def updG (S : M2) (a b : Fin 2 → ℝ) : M2 :=
  S - (VG S a b)⁻¹ • vecMulVec (S *ᵥ a) (S *ᵥ a)

variable {S : M2} {a b : Fin 2 → ℝ}

lemma measurable_ZG : Measurable (ZG a b) := by unfold ZG; fun_prop

lemma measurable_resG : Measurable (resG S a b) := by
  unfold resG ZG; fun_prop

lemma VG_eq (S : M2) (a b : Fin 2 → ℝ) : VG S a b =
    a 0 * (S 0 0 * a 0 + S 0 1 * a 1) + a 1 * (S 1 0 * a 0 + S 1 1 * a 1) +
      (b 0 * b 0 + b 1 * b 1) := by
  simp [VG, dotProduct, mulVec, Fin.sum_univ_two]

lemma kG_apply (j : Fin 2) : kG S a b j = (VG S a b)⁻¹ * (S j 0 * a 0 + S j 1 * a 1) := by
  simp [kG, mulVec, dotProduct, Fin.sum_univ_two]

lemma ZG_coord (ω : Ω₂) :
    ZG a b ω = 0 + (a 0 * ω.1 0 + a 1 * ω.1 1) + (b 0 * ω.2 0 + b 1 * ω.2 1) := by
  simp [ZG]

lemma inner_ZG_coord (y : ℝ) (ω : Ω₂) :
    ⟪y, ZG a b ω⟫ = 0 + ((y * a 0) * ω.1 0 + (y * a 1) * ω.1 1) +
      ((y * b 0) * ω.2 0 + (y * b 1) * ω.2 1) := by
  simp [ZG]; ring

lemma inner_resG_coord (t : E2) (ω : Ω₂) :
    ⟪t, resG S a b ω⟫ =
      0 + ((t 0 - (t 0 * kG S a b 0 + t 1 * kG S a b 1) * a 0) * ω.1 0 +
          (t 1 - (t 0 * kG S a b 0 + t 1 * kG S a b 1) * a 1) * ω.1 1) +
        ((-((t 0 * kG S a b 0 + t 1 * kG S a b 1) * b 0)) * ω.2 0 +
          (-((t 0 * kG S a b 0 + t 1 * kG S a b 1) * b 1)) * ω.2 1) := by
  simp [resG, ZG, PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma resG_affine (c : ℝ) (x y : Ω₂) :
    resG S a b (c • x + y) = c • (resG S a b x - resG S a b 0) + resG S a b y := by
  ext i; simp [resG, ZG]; ring

lemma ZG_affine (c : ℝ) (x y : Ω₂) :
    ZG a b (c • x + y) = c • (ZG a b x - ZG a b 0) + ZG a b y := by
  simp [ZG]; ring

/-- If `V = 0` then `Σ a = 0`. -/
lemma Sa_zero (hS : S.PosSemidef) (hV : VG S a b = 0) : S *ᵥ a = 0 := by
  have h1 : 0 ≤ a ⬝ᵥ (S *ᵥ a) := by
    have := hS.dotProduct_mulVec_nonneg a
    simpa using this
  have h2 : 0 ≤ b ⬝ᵥ b := by
    simp only [dotProduct, Fin.sum_univ_two]; nlinarith [sq_nonneg (b 0), sq_nonneg (b 1)]
  have h3 : a ⬝ᵥ (S *ᵥ a) = 0 := by unfold VG at hV; linarith
  exact (hS.dotProduct_mulVec_zero_iff (x := a)).1 (by simpa using h3)

lemma indep_resG (hS : S.PosSemidef) :
    IndepFun (resG S a b) (ZG a b) (periodLaw 0 S) := by
  refine cc_indepFun (periodLaw 0 S) (resG S a b) (ZG a b) resG_affine ZG_affine
    (fun x y => ?_)
  rw [cond_cov hS (inner_resG_coord x) (inner_ZG_coord y), kG_apply, kG_apply]
  set V := VG S a b with hVdef
  have hV := VG_eq S a b
  rw [← hVdef] at hV
  set s0 := S 0 0 * a 0 + S 0 1 * a 1
  set s1 := S 1 0 * a 0 + S 1 1 * a 1
  have key : ∀ q : ℝ, q = x 0 * s0 + x 1 * s1 → q - V⁻¹ * q * V = 0 := by
    intro q hq
    by_cases h0 : V = 0
    · have hz := Sa_zero hS (hVdef ▸ h0)
      have e0 : s0 = 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hz 0
      have e1 : s1 = 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hz 1
      rw [hq, e0, e1]; ring
    · field_simp; ring
  have := key (x 0 * s0 + x 1 * s1) rfl
  calc _ = y * ((x 0 * s0 + x 1 * s1) - V⁻¹ * (x 0 * s0 + x 1 * s1) * V) := by
          rw [hV]; ring
    _ = 0 := by rw [this, mul_zero]

lemma var_inner_resG (hS : S.PosSemidef) (t : E2) :
    Var[fun ω => ⟪t, resG S a b ω⟫; periodLaw 0 S] = t.ofLp ⬝ᵥ updG S a b *ᵥ t.ofLp := by
  have hm : AEMeasurable (fun ω => ⟪t, resG S a b ω⟫) (periodLaw 0 S) :=
    (cond_memLp (inner_resG_coord t)).aestronglyMeasurable.aemeasurable
  rw [← covariance_self hm, cond_cov hS (inner_resG_coord t) (inner_resG_coord t), kG_apply,
    kG_apply]
  have hs := cm_symm hS
  have hV := VG_eq S a b
  set V := VG S a b
  have hq : t.ofLp ⬝ᵥ updG S a b *ᵥ t.ofLp =
      t 0 * (S 0 0 * t 0 + S 0 1 * t 1) + t 1 * (S 1 0 * t 0 + S 1 1 * t 1) -
        V⁻¹ * (t 0 * (S 0 0 * a 0 + S 0 1 * a 1) + t 1 * (S 1 0 * a 0 + S 1 1 * a 1)) ^ 2 := by
    simp [updG, dotProduct, mulVec, vecMulVec, Fin.sum_univ_two]
    ring
  rw [hq]
  rw [hs] at hV ⊢
  rcases eq_or_ne V 0 with h0 | h0
  · rw [h0, _root_.inv_zero]; ring
  · have hinv : V⁻¹ * V = 1 := inv_mul_cancel₀ h0
    set q := t 0 * (S 0 0 * a 0 + S 0 1 * a 1) + t 1 * (S 0 1 * a 0 + S 1 1 * a 1)
    linear_combination (-(V⁻¹ ^ 2 * q ^ 2)) * hV + (V⁻¹ * q ^ 2) * hinv

lemma integral_inner_resG (t : E2) : ∫ ω, ⟪t, resG S a b ω⟫ ∂(periodLaw 0 S) = 0 := by
  rw [cond_integral (inner_resG_coord t)]
  simp

lemma updG_posSemidef (hS : S.PosSemidef) : (updG S a b).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · ext i j
    have h := hS.1.apply i j
    simp only [star_trivial] at h
    simp [updG, vecMulVec, h, mul_comm]
  · have h := var_inner_resG (a := a) (b := b) hS (WithLp.toLp 2 x)
    simp only at h
    rw [star_trivial, ← h]
    exact variance_nonneg _ _

lemma law_resG (hS : S.PosSemidef) :
    (periodLaw 0 S).map (resG S a b) = multivariateGaussian 0 (updG S a b) := by
  have hG : HasGaussianLaw (resG S a b) (periodLaw 0 S) :=
    cc_hasGaussianLaw_affine _ _ resG_affine
  apply Measure.ext_of_charFun
  funext t
  rw [hG.charFun_map_eq, charFun_multivariateGaussian (updG_posSemidef hS),
    integral_inner_resG, var_inner_resG hS]
  simp

/-- One step of the filter with a general linear signal: if `(e, Y) ⟂ ξ`, `e ⟂ Y`,
`e ~ N(0, Σ)` and `ξ ~ N(0, I)`, the residual of the regression of `e` on `Z = a · e + b · ξ` is
independent of `(Z, Y)` and has law `N(0, updG Σ a b)`. -/
lemma kstepG {Ω 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴] {P : Measure Ω}
    [IsProbabilityMeasure P] (hS : S.PosSemidef) (a b : Fin 2 → ℝ) {e ξ : Ω → E2} {Y : Ω → 𝒴}
    (he : Measurable e) (hξ : Measurable ξ) (hY : Measurable Y)
    (h1 : IndepFun (fun ω => (e ω, Y ω)) ξ P) (h2 : IndepFun e Y P)
    (hle : P.map e = multivariateGaussian 0 S) (hlξ : P.map ξ = stdGaussian E2) :
    IndepFun (fun ω => resG S a b (e ω, ξ ω)) (fun ω => (ZG a b (e ω, ξ ω), Y ω)) P ∧
      P.map (fun ω => resG S a b (e ω, ξ ω)) = multivariateGaussian 0 (updG S a b) := by
  have heξ : IndepFun e ξ P := h1.comp (φ := Prod.fst) (ψ := id) measurable_fst measurable_id
  have hlaw : P.map (fun ω => (e ω, ξ ω)) = periodLaw 0 S := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map he.aemeasurable hξ.aemeasurable).1 heξ, hle, hlξ]
    rfl
  have hR : Measurable (resG S a b) := measurable_resG
  have hZ : Measurable (ZG a b) := measurable_ZG
  have hp : Measurable (fun ω => (e ω, ξ ω)) := he.prodMk hξ
  have hind1 : IndepFun (fun ω => resG S a b (e ω, ξ ω)) (fun ω => ZG a b (e ω, ξ ω)) P :=
    Bridge.br_indep_of_map hp hR hZ (by rw [hlaw]; exact indep_resG hS)
  have hind2 : IndepFun (fun ω => (e ω, ξ ω)) Y P := Bridge.br_indep_regroup he hY hξ h1 h2
  have hind3 : IndepFun (fun ω => (resG S a b (e ω, ξ ω), ZG a b (e ω, ξ ω))) Y P :=
    hind2.comp (φ := fun p => (resG S a b p, ZG a b p)) (ψ := id) (hR.prodMk hZ) measurable_id
  refine ⟨Bridge.br_indep_assoc (hR.comp hp) (hZ.comp hp) hY hind3 hind1, ?_⟩
  have : (fun ω => resG S a b (e ω, ξ ω)) = resG S a b ∘ (fun ω => (e ω, ξ ω)) := rfl
  rw [this, ← Measure.map_map hR hp, hlaw, law_resG hS]

/-! ### The three kinds of slots -/

/-- An uninformative slot. -/
lemma updG_zero (S : M2) : updG S 0 0 = S := by simp [updG]

lemma ZG_zero (ω : Ω₂) : ZG 0 0 ω = 0 := by simp [ZG]

lemma kG_zero (S : M2) : kG S 0 0 = 0 := by simp [kG]

/-- A revealing action: `a = b = A`. -/
lemma VG_loadA (S : M2) (γ : ℝ) : VG S (loadA S γ) (loadA S γ) = varZ S γ := by
  simp [VG, varZ, add_mulVec, dotProduct_add]

lemma updG_loadA (S : M2) (γ : ℝ) : updG S (loadA S γ) (loadA S γ) = kalman S γ := by
  simp [updG, kalman, VG_loadA]

lemma kG_loadA (S : M2) (γ : ℝ) : kG S (loadA S γ) (loadA S γ) = regK S γ := by
  simp [kG, regK, VG_loadA]

lemma ZG_loadA (S : M2) (γ : ℝ) (ω : Ω₂) :
    ZG (loadA S γ) (loadA S γ) ω = Bridge.dotA (loadA S γ) (ω.1 + ω.2) := by
  simp [ZG, Bridge.dotA]; ring

/-- The loading `e_i` of a disclosure. -/
def eVec (i : Fin 2) : Fin 2 → ℝ := fun j => if j = i then 1 else 0

/-- The noise loading `√n e_i` of a disclosure. -/
noncomputable def nVec (i : Fin 2) (n : ℝ) : Fin 2 → ℝ := fun j => if j = i then √n else 0

lemma ZG_disc (i : Fin 2) (n : ℝ) (ω : Ω₂) : ZG (eVec i) (nVec i n) ω = ω.1 i + √n * ω.2 i := by
  fin_cases i <;> simp [ZG, eVec, nVec]

lemma updG_disc (S : M2) (i : Fin 2) {n : ℝ} (hn : 0 ≤ n) :
    updG S (eVec i) (nVec i n) = discCov (some (i, n)) S := by
  have hsq : √n * √n = n := Real.mul_self_sqrt hn
  fin_cases i
  · have he : eVec 0 = ![1, 0] := by funext j; fin_cases j <;> simp [eVec]
    have hV : VG S (eVec 0) (nVec 0 n) = S 0 0 + n := by
      simp [VG_eq, eVec, nVec, hsq]
    simp only [discCov, Fin.zero_eta, ite_true]
    rw [updG, hV, he]
    rfl
  · have he : eVec 1 = ![0, 1] := by funext j; fin_cases j <;> simp [eVec]
    have hV : VG S (eVec 1) (nVec 1 n) = S 1 1 + n := by
      simp [VG_eq, eVec, nVec, hsq]
    simp only [discCov, Fin.mk_one]
    rw [ite_eq_right (by decide), updG, hV, he]
    rfl

end CC.BridgeK
