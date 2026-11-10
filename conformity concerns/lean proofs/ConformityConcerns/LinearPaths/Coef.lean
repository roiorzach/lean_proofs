import ConformityConcerns.LinearPaths.Meas

/-!
# The coefficients of a pooling or revealing period strategy

At a history with public beliefs `N(m, S)` and weight `γ`, the regression of the period
strategy `a` on `Z` (under the type law `N(m, S + I)`) gives a slope and an intercept. If `a` is
pooling, the slope is `0` and the intercept is the pooled action; if `a` is revealing,
`a = k Z + b` with `k > 0`, they are `k` and `b`. Both are measurable in the history, so the
"next observation" `y = kco · Z + bco` has history-measurable coefficients.
-/

namespace CC.LinearPaths

open MeasureTheory ProbabilityTheory
open CC.Bridge
open scoped RealInnerProductSpace

/-- `Z = γ E(θ | h, s, v) + v` at a history with beliefs `N(m, S)` (the `Z` of `gameAt`). -/
noncomputable def Zg (m : E2) (S : M2) (γ : ℝ) (x : E2) : ℝ :=
  γ * (m 0 + gainK S 0 0 * (x 0 - m 0) + gainK S 0 1 * (x 1 - m 1)) + x 1

lemma gameAt_Z_eq (m : E2) (S : M2) (γ κ : ℝ) : (gameAt m S γ κ).Z = Zg m S γ := rfl

lemma gameAt_P_eq (m : E2) (S : M2) (γ κ : ℝ) :
    (gameAt m S γ κ).P = multivariateGaussian m (S + 1) := rfl

/-- `E(Z | h)`. -/
noncomputable def EZ (m : E2) (S : M2) (γ : ℝ) : ℝ :=
  ∫ x, Zg m S γ x ∂(multivariateGaussian m (S + 1))

/-- The regression slope `Cov(a, Z)/Var(Z)`. -/
noncomputable def slope (m : E2) (S : M2) (γ : ℝ) (a : E2 → ℝ) : ℝ :=
  (∫ x, a x * (Zg m S γ x - EZ m S γ) ∂(multivariateGaussian m (S + 1))) / varZ S γ

/-- The nonnegative slope. -/
noncomputable def kco (m : E2) (S : M2) (γ : ℝ) (a : E2 → ℝ) : ℝ := max (slope m S γ a) 0

/-- The regression intercept `E a - slope · E Z`. -/
noncomputable def bco (m : E2) (S : M2) (γ : ℝ) (a : E2 → ℝ) : ℝ :=
  ∫ x, a x ∂(multivariateGaussian m (S + 1)) - slope m S γ a * EZ m S γ

lemma kco_nonneg (m : E2) (S : M2) (γ : ℝ) (a : E2 → ℝ) : 0 ≤ kco m S γ a := le_max_right _ _

section Facts

variable {m : E2} {S : M2} {γ : ℝ}

lemma memLp_Zg (γ : ℝ) : MemLp (Zg m S γ) 2 (multivariateGaussian m (S + 1)) := by
  have e : Zg m S γ = fun ω : E2 =>
      γ * (m 0 + gainK S 0 0 * (ω 0 - m 0) + gainK S 0 1 * (ω 1 - m 1)) + ω 1 := rfl
  rw [e, inst_Z_affine]
  exact cc_memLp_aff _ _ _

lemma integral_Zg_sub (γ : ℝ) :
    ∫ x, (Zg m S γ x - EZ m S γ) ∂(multivariateGaussian m (S + 1)) = 0 := by
  rw [integral_sub ((memLp_Zg γ).integrable one_le_two) (integrable_const _), integral_const,
    probReal_univ, one_smul, EZ, sub_self]

lemma integral_Zg_sub_sq (hS : S.PosSemidef) (γ : ℝ) :
    ∫ x, (Zg m S γ x - EZ m S γ) ^ 2 ∂(multivariateGaussian m (S + 1)) = varZ S γ := by
  have hv : variance (Zg m S γ) (multivariateGaussian m (S + 1)) = varZ S γ :=
    inst_variance_Z (m := m) hS γ
  rw [← hv, variance_eq_integral ((memLp_Zg γ).aestronglyMeasurable.aemeasurable)]
  rfl

/-- A pooling strategy has slope `0`, and is `kco · Z + bco`. -/
lemma coef_pool {κ : ℝ} {a : E2 → ℝ} (h : (gameAt m S γ κ).IsPooling a) :
    slope m S γ a = 0 ∧ kco m S γ a = 0 ∧
      a =ᵐ[multivariateGaussian m (S + 1)] fun x => kco m S γ a * Zg m S γ x + bco m S γ a := by
  obtain ⟨c, hc⟩ := h
  rw [gameAt_P_eq] at hc
  have hnum : ∫ x, a x * (Zg m S γ x - EZ m S γ) ∂(multivariateGaussian m (S + 1)) = 0 := by
    have h1 : (fun x => a x * (Zg m S γ x - EZ m S γ)) =ᵐ[multivariateGaussian m (S + 1)]
        fun x => c * (Zg m S γ x - EZ m S γ) := hc.mono fun x hx => by simp [hx]
    rw [integral_congr_ae h1, integral_const_mul, integral_Zg_sub, mul_zero]
  have hs : slope m S γ a = 0 := by rw [slope, hnum, zero_div]
  have hk : kco m S γ a = 0 := by rw [kco, hs, max_self]
  have hb : bco m S γ a = c := by
    rw [bco, hs, zero_mul, sub_zero, integral_congr_ae hc, integral_const, probReal_univ,
      one_smul]
  exact ⟨hs, hk, hc.mono fun x hx => by simp [hx, hk, hb]⟩

/-- A revealing strategy `a = k Z + b` has slope `k > 0` and intercept `b`. -/
lemma coef_reveal (hS : S.PosSemidef) {κ : ℝ} {a : E2 → ℝ} (h : (gameAt m S γ κ).IsRevealing a) :
    0 < kco m S γ a ∧ slope m S γ a = kco m S γ a ∧
      a =ᵐ[multivariateGaussian m (S + 1)] fun x => kco m S γ a * Zg m S γ x + bco m S γ a := by
  obtain ⟨k, b, hk, hab⟩ := h
  rw [gameAt_P_eq, gameAt_Z_eq] at hab
  have hZ := memLp_Zg (m := m) (S := S) γ
  have hZs : MemLp (fun x => Zg m S γ x - EZ m S γ) 2 (multivariateGaussian m (S + 1)) :=
    hZ.sub (memLp_const _)
  have hnum : ∫ x, a x * (Zg m S γ x - EZ m S γ) ∂(multivariateGaussian m (S + 1)) =
      k * varZ S γ := by
    have e : ∀ x, (k * Zg m S γ x + b) * (Zg m S γ x - EZ m S γ) =
        k * (Zg m S γ x - EZ m S γ) ^ 2 + (k * EZ m S γ + b) * (Zg m S γ x - EZ m S γ) := by
      intro x; ring
    have h1 : (fun x => a x * (Zg m S γ x - EZ m S γ)) =ᵐ[multivariateGaussian m (S + 1)]
        fun x => (k * Zg m S γ x + b) * (Zg m S γ x - EZ m S γ) := hab.mono fun x hx => by simp [hx]
    rw [integral_congr_ae h1, integral_congr_ae
      (Filter.Eventually.of_forall e), integral_add ((hZs.integrable_sq).const_mul k)
      ((hZs.integrable one_le_two).const_mul _), integral_const_mul, integral_const_mul,
      integral_Zg_sub_sq hS, integral_Zg_sub, mul_zero, add_zero]
  have hv := cm_varZ_pos hS γ
  have hs : slope m S γ a = k := by
    rw [slope, hnum]
    field_simp
  have hkc : kco m S γ a = k := by rw [kco, hs, max_eq_left hk.le]
  have hb : bco m S γ a = b := by
    rw [bco, hs, integral_congr_ae hab, integral_add ((hZ.integrable one_le_two).const_mul k)
      (integrable_const b), integral_const_mul, integral_const, probReal_univ, one_smul, EZ]
    ring
  exact ⟨hkc ▸ hk, hs.trans hkc.symm, hab.mono fun x hx => by simp [hx, hkc, hb]⟩

end Facts

section Meas

variable {H : Type*} [MeasurableSpace H]

lemma measurable_Zg {β : Type*} [MeasurableSpace β] {m : β → E2} {S : β → M2} {γ : β → ℝ}
    {x : β → E2} (hm : Measurable m) (hS : Measurable S) (hγ : Measurable γ)
    (hx : Measurable x) : Measurable (fun q => Zg (m q) (S q) (γ q) (x q)) := by
  have p0 := br_meas_coord hx 0
  have p1 := br_meas_coord hx 1
  have m0 := br_meas_coord hm 0
  have m1 := br_meas_coord hm 1
  have k0 := br_meas_gainK hS 0 0
  have k1 := br_meas_gainK hS 0 1
  unfold Zg
  fun_prop

lemma measurable_add_one {S : H → M2} (hS : Measurable S) : Measurable (fun h => S h + 1) :=
  (Measurable.of_eval_matrix _ fun i j =>
    (measurable_id.eval_matrix (i := i) (j := j)).add measurable_const :
      Measurable (fun A : M2 => A + 1)).comp hS

/-- The type-law kernel `h ↦ N(m h, S h + I)`. -/
noncomputable def typeK (p : H → E2 × M2) (hp : Measurable p) : Kernel H E2 where
  toFun := Function.uncurry multivariateGaussian ∘ (fun h => ((p h).1, (p h).2 + 1))
  measurable' := measurable_multivariateGaussian.comp
    ((measurable_fst.comp hp).prodMk (measurable_add_one (measurable_snd.comp hp)))

instance (p : H → E2 × M2) (hp : Measurable p) : IsMarkovKernel (typeK p hp) :=
  ⟨fun h => by
    change IsProbabilityMeasure (multivariateGaussian (p h).1 ((p h).2 + 1))
    infer_instance⟩

lemma typeK_apply (p : H → E2 × M2) (hp : Measurable p) (h : H) :
    typeK p hp h = multivariateGaussian (p h).1 ((p h).2 + 1) := rfl

lemma measurable_EZ {p : H → E2 × M2} {γ : H → ℝ} (hp : Measurable p) (hγ : Measurable γ) :
    Measurable (fun h => EZ (p h).1 (p h).2 (γ h)) := by
  have hf : Measurable (fun q : H × E2 => Zg (p q.1).1 (p q.1).2 (γ q.1) q.2) :=
    measurable_Zg (measurable_fst.comp (hp.comp measurable_fst))
      (measurable_snd.comp (hp.comp measurable_fst)) (hγ.comp measurable_fst) measurable_snd
  exact (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := typeK p hp)).measurable

lemma measurable_slope {p : H → E2 × M2} {γ : H → ℝ} {a : H → E2 → ℝ} (hp : Measurable p)
    (hγ : Measurable γ) (ha : Measurable (Function.uncurry a)) :
    Measurable (fun h => slope (p h).1 (p h).2 (γ h) (a h)) := by
  have hf : Measurable (fun q : H × E2 =>
      a q.1 q.2 * (Zg (p q.1).1 (p q.1).2 (γ q.1) q.2 - EZ (p q.1).1 (p q.1).2 (γ q.1))) :=
    ha.mul ((measurable_Zg (measurable_fst.comp (hp.comp measurable_fst))
      (measurable_snd.comp (hp.comp measurable_fst)) (hγ.comp measurable_fst)
      measurable_snd).sub ((measurable_EZ hp hγ).comp measurable_fst))
  have hnum := (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := typeK p hp)).measurable
  exact hnum.div (br_meas_varZ (measurable_snd.comp hp) hγ)

lemma measurable_kco {p : H → E2 × M2} {γ : H → ℝ} {a : H → E2 → ℝ} (hp : Measurable p)
    (hγ : Measurable γ) (ha : Measurable (Function.uncurry a)) :
    Measurable (fun h => kco (p h).1 (p h).2 (γ h) (a h)) :=
  (measurable_slope hp hγ ha).max measurable_const

lemma measurable_bco {p : H → E2 × M2} {γ : H → ℝ} {a : H → E2 → ℝ} (hp : Measurable p)
    (hγ : Measurable γ) (ha : Measurable (Function.uncurry a)) :
    Measurable (fun h => bco (p h).1 (p h).2 (γ h) (a h)) := by
  have hint := (ha.stronglyMeasurable.integral_kernel_prod_right' (κ := typeK p hp)).measurable
  exact hint.sub ((measurable_slope hp hγ ha).mul (measurable_EZ hp hγ))

end Meas

end CC.LinearPaths
