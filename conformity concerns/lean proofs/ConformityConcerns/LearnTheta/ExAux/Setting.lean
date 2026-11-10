import ConformityConcerns.LearnTheta.ExAux.Conv
import ConformityConcerns.General.KnownMu
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# The period game at a fixed history as a `Setting`

At a history where the public belief about `Y_t` is `η` and `m = mfun ψ η` is `C²` with
`0 < m'' ≤ 2`, the period game is a `Setting`: quadratic adaptation loss, type distribution
`η ∗ G` (continuous, everywhere-positive density), norm `μ` the unique zero of `m'`
(`propA5_minimizer`, applied on the product space `η ⊗ G`), and conformity loss
`κ (m - m(μ))`.
-/

namespace CC.LearnTheta.ExAux

open MeasureTheory ProbabilityTheory Filter Set
open CC.General
open scoped ENNReal

variable {ψ : ℝ → ℝ}

lemma adaptLoss_sq' : AdaptLoss (fun z : ℝ => z ^ 2) where
  smooth := by fun_prop
  even := fun z => by ring
  strictConvex := Even.strictConvexOn_pow (by decide) (by norm_num)
  zero := by norm_num

/-- If `m'` is strictly increasing and vanishes at `μ`, then `μ` is the strict minimiser. -/
lemma lt_of_deriv_zero {m : ℝ → ℝ} (hm : ContDiff ℝ 2 m) (hdm : StrictMono (deriv m)) {μ : ℝ}
    (hμ : deriv m μ = 0) {b : ℝ} (hb : b ≠ μ) : m μ < m b := by
  have hmd : Differentiable ℝ m := hm.differentiable (by norm_num)
  rcases lt_or_gt_of_ne hb with h | h
  · obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_slope m h hmd.continuous.continuousOn
      hmd.differentiableOn
    have hneg : deriv m ξ < 0 := hμ ▸ hdm hξ.2
    rw [hd, div_lt_iff₀ (sub_pos.2 h)] at hneg
    linarith
  · obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_slope m h hmd.continuous.continuousOn
      hmd.differentiableOn
    have hpos : 0 < deriv m ξ := hμ ▸ hdm hξ.1
    rw [hd, lt_div_iff₀ (sub_pos.2 h)] at hpos
    linarith

/-- **The period game at a history with belief `η` is a `Setting`.** -/
theorem exists_setting (κ : ℝ) (hκ0 : 0 < κ) (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x)
    (hψb : ∃ C, ∀ x, ψ x ≤ C) (hv2 : Integrable (fun x => x ^ 2) (vLaw ψ))
    (hsymm : ∀ x, ψ (-x) = ψ x) (h3 : Integrable (fun x => |x| ^ 3) (vLaw ψ))
    [IsProbabilityMeasure (vLaw ψ)]
    (η : Measure ℝ) [IsProbabilityMeasure η] (hη2 : Integrable (fun y => y ^ 2) η)
    (hm : ContDiff ℝ 2 (mfun ψ η))
    (hm2 : ∀ x, 0 < iteratedDeriv 2 (mfun ψ η) x ∧ iteratedDeriv 2 (mfun ψ η) x ≤ 2)
    (F : Measure ℝ) (hF : F = η.conv (vLaw ψ)) :
    ∃ S : Setting, S.g = (fun z => z ^ 2) ∧ S.F = F ∧
      S.ℓ = (fun x => κ * (mfun ψ η x - mfun ψ η S.μ)) := by
  obtain ⟨C, hC⟩ := hψb
  have hψ : Measurable ψ := hψc.measurable
  have hmc : Continuous (mfun ψ η) := hm.continuous
  have hmf : Measurable (mfun ψ η) := hmc.measurable
  have hdens := conv_vLaw_eq hψ hψpos hC η
  have hFd : F = volume.withDensity (fun x => ENNReal.ofReal (convDens ψ η x)) := hF.trans hdens
  have hFprob : IsProbabilityMeasure F := by
    rw [hF]; unfold Measure.conv; infer_instance
  -- the minimiser of `m`
  have hsnd : (η.prod (vLaw ψ)).map Prod.snd = vLaw ψ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hfst : (η.prod (vLaw ψ)).map Prod.fst = η := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmin : ∃! xs : ℝ, deriv (mfun ψ η) xs = 0 := by
    refine propA5_minimizer (P := η.prod (vLaw ψ)) (fun p => p.2) (fun p => p.1)
      measurable_snd measurable_fst ?_ ?_ ?_ ?_ ?_ (mfun ψ η) hm hm2 ?_
    · exact (indepFun_prod (μ := η) (ν := vLaw ψ) (X := id) (Y := id) measurable_id
        measurable_id).symm
    · show (η.prod (vLaw ψ)).map Prod.snd = (η.prod (vLaw ψ)).map ((fun x => -x) ∘ Prod.snd)
      rw [← Measure.map_map measurable_neg measurable_snd, hsnd, vLaw_map_neg hψ hsymm]
    · rw [← hsnd] at h3; exact h3.comp_measurable measurable_snd
    · rw [← hfst] at hη2; exact hη2.comp_measurable measurable_fst
    · have e : (fun p : ℝ × ℝ => p.2 + p.1) = fun p => p.1 + p.2 :=
        funext fun p => add_comm _ _
      show Measure.map (fun p : ℝ × ℝ => p.2 + p.1) (η.prod (vLaw ψ)) ≪ volume
      rw [e]
      show η.conv (vLaw ψ) ≪ volume
      rw [hdens]; exact withDensity_absolutelyContinuous _ _
    · exact condExp_prod_eq_mfun hψ hψpos hC hv2 η hmf
  obtain ⟨μ, hμ, -⟩ := hmin
  have h2 : ∀ x, iteratedDeriv 2 (mfun ψ η) x = deriv (deriv (mfun ψ η)) x := fun x => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hdm : StrictMono (deriv (mfun ψ η)) :=
    strictMono_of_deriv_pos (fun x => by rw [← h2]; exact (hm2 x).1)
  have hmd : Differentiable ℝ (mfun ψ η) := hm.differentiable (by norm_num)
  have hlt : ∀ b, b ≠ μ → mfun ψ η μ < mfun ψ η b := fun b hb => lt_of_deriv_zero hm hdm hμ hb
  have hℓd : ∀ x, deriv (fun x => κ * (mfun ψ η x - mfun ψ η μ)) x =
      κ * deriv (mfun ψ η) x :=
    fun x => (((hmd x).hasDerivAt.sub_const (mfun ψ η μ)).const_mul κ).deriv
  have hℓ : ConfLoss (fun x => κ * (mfun ψ η x - mfun ψ η μ)) μ := {
    smooth := contDiff_const.mul (hm.sub contDiff_const)
    strictConvex := by
      refine StrictMono.strictConvexOn_univ_of_deriv
        (continuous_const.mul (hmc.sub continuous_const)) ?_
      intro a b hab
      rw [hℓd, hℓd]
      exact mul_lt_mul_of_pos_left (hdm hab) hκ0
    zero := by simp
    isMin := fun b => by
      rcases eq_or_ne b μ with rfl | hb
      · exact le_rfl
      · simp only [sub_self, mul_zero]
        exact (mul_pos hκ0 (sub_pos.2 (hlt b hb))).le }
  have hint : Integrable (fun x => κ * (mfun ψ η x - mfun ψ η μ)) F := by
    rw [hF]
    exact ((integrable_mfun_conv hψ hψpos hC hv2 η hmf).sub (integrable_const _)).const_mul κ
  have hpos : 0 < ∫ x, κ * (mfun ψ η x - mfun ψ η μ) ∂F := by
    have hnn : 0 ≤ fun x => κ * (mfun ψ η x - mfun ψ η μ) := fun x => by
      show (0 : ℝ) ≤ κ * (mfun ψ η x - mfun ψ η μ)
      rcases eq_or_ne x μ with rfl | hx
      · simp
      · exact (mul_pos hκ0 (sub_pos.2 (hlt x hx))).le
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hsupp : Function.support (fun x => κ * (mfun ψ η x - mfun ψ η μ)) = {μ}ᶜ := by
      ext x
      simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro h rfl; simp at h
      · intro hx; exact (mul_pos hκ0 (sub_pos.2 (hlt x hx))).ne'
    have h0 : F {μ} = 0 := by
      rw [hFd]; exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
    rw [hsupp, measure_compl (measurableSet_singleton μ) (measure_ne_top _ _), measure_univ, h0]
    simp
  let S : Setting :=
    { g := fun z => z ^ 2
      ℓ := fun x => κ * (mfun ψ η x - mfun ψ η μ)
      μ := μ
      F := F
      hg := adaptLoss_sq'
      hℓ := hℓ
      hF := ⟨hFprob, convDens ψ η, continuous_convDens hψc hψpos hC η,
        convDens_pos hψ hψpos hC η, hFd⟩
      integrable := hint
      Mpos := hpos }
  exact ⟨S, rfl, rfl, rfl⟩

end CC.LearnTheta.ExAux
