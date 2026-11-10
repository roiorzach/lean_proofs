import ConformityConcerns.LearnTheta.Defs
import ConformityConcerns.LearnTheta.SelAux.Tail
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Measurable ingredients of the choice of a revealing equilibrium

For a belief `η` (any measure; non-probability measures are replaced by `δ_0`):
* `dQ ψ η x`, the `limsup` of the difference quotients of `m = mfun ψ η` along `1/(n+1)`; it is
  `m'(x)` wherever `m` is differentiable;
* `xsSel ψ η`, the supremum of the rationals `q` with `dQ ψ η q < 0`; it is the zero of `m'` when
  `m'` is strictly increasing and vanishes somewhere.
All are jointly measurable in `(η, x)` for the Giry σ-algebra, and so are the iterates `wIter`
and their limit `wLim` built from a jointly measurable `Ψ`, and the glued rule `selRule`.
-/

namespace CC.LearnTheta.SelAux

open MeasureTheory ProbabilityTheory Filter Topology Set

/-! ### Normalising the belief -/

/-- `η` if it is a probability measure, `δ_0` otherwise. -/
noncomputable def normη (η : Measure ℝ) : Measure ℝ :=
  if η univ = 1 then η else Measure.dirac 0

lemma normη_of_prob (η : Measure ℝ) [IsProbabilityMeasure η] : normη η = η :=
  ite_eq_left measure_univ

instance normη_isProb (η : Measure ℝ) : IsProbabilityMeasure (normη η) := by
  unfold normη
  split_ifs with h
  · exact ⟨h⟩
  · infer_instance

lemma measurable_normη : Measurable normη :=
  Measurable.ite ((Measure.measurable_coe MeasurableSet.univ) (measurableSet_singleton 1))
    measurable_id measurable_const

/-- The kernel `η ↦ normη η` on `Measure ℝ`. -/
noncomputable def idK : Kernel (Measure ℝ) ℝ := ⟨normη, measurable_normη⟩

instance : IsMarkovKernel idK := ⟨fun η => normη_isProb η⟩

variable {ψ : ℝ → ℝ}

/-- `(η, x) ↦ m(x | normη η)` is measurable. -/
lemma measurable_mfun_norm (hψ : Measurable ψ) :
    Measurable fun p : Measure ℝ × ℝ => mfun ψ (normη p.1) p.2 := by
  have hN := StronglyMeasurable.integral_kernel_prod_right' (κ := idK.comap Prod.fst measurable_fst)
    (f := fun q : (Measure ℝ × ℝ) × ℝ => (q.1.2 - q.2) ^ 2 * ψ (q.1.2 - q.2))
    (((measurable_fst.snd.sub measurable_snd).pow_const 2).mul
      (hψ.comp (measurable_fst.snd.sub measurable_snd))).stronglyMeasurable
  have hD := StronglyMeasurable.integral_kernel_prod_right' (κ := idK.comap Prod.fst measurable_fst)
    (f := fun q : (Measure ℝ × ℝ) × ℝ => ψ (q.1.2 - q.2))
    (hψ.comp (measurable_fst.snd.sub measurable_snd)).stronglyMeasurable
  exact hN.measurable.div hD.measurable

/-! ### A measurable derivative -/

/-- The `limsup` of the difference quotients of `m = mfun ψ (normη η)` at `x` along `1/(n+1)`. -/
noncomputable def dQ (ψ : ℝ → ℝ) (η : Measure ℝ) (x : ℝ) : ℝ :=
  limsup (fun n : ℕ => ((n : ℝ) + 1) *
    (mfun ψ (normη η) (x + 1 / ((n : ℝ) + 1)) - mfun ψ (normη η) x)) atTop

lemma measurable_dQ (hψ : Measurable ψ) :
    Measurable fun p : Measure ℝ × ℝ => dQ ψ p.1 p.2 := by
  have hM := measurable_mfun_norm hψ
  exact Measurable.limsup (f := fun (n : ℕ) (p : Measure ℝ × ℝ) => ((n : ℝ) + 1) *
    (mfun ψ (normη p.1) (p.2 + 1 / ((n : ℝ) + 1)) - mfun ψ (normη p.1) p.2)) fun n =>
    measurable_const.mul ((hM.comp (measurable_fst.prodMk
      (measurable_snd.add_const (1 / ((n : ℝ) + 1))))).sub hM)

lemma dQ_eq {η : Measure ℝ} [IsProbabilityMeasure η] {x : ℝ}
    (hd : DifferentiableAt ℝ (mfun ψ η) x) : dQ ψ η x = deriv (mfun ψ η) x := by
  unfold dQ
  rw [normη_of_prob]
  apply Tendsto.limsup_eq
  have h1 := hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt
  have h2 : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add x
    · refine Eventually.of_forall fun n => ?_
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact (lt_add_of_pos_right x this).ne'
  refine (h1.comp h2).congr fun n => ?_
  simp only [Function.comp]
  rw [slope_def_field, add_sub_cancel_left, div_div_eq_mul_div, div_one, mul_comm]

/-! ### The zero of `m'` -/

/-- The supremum (in `EReal`, then in `ℝ`) of the rationals `q` with `dQ ψ η q < 0`. -/
noncomputable def xsSel (ψ : ℝ → ℝ) (η : Measure ℝ) : ℝ :=
  (⨆ q : ℚ, if dQ ψ η q < 0 then ((q : ℝ) : EReal) else ⊥).toReal

lemma measurable_xsSel (hψ : Measurable ψ) : Measurable (xsSel ψ) := by
  have hD := measurable_dQ hψ
  have hq : ∀ q : ℚ, Measurable fun η : Measure ℝ =>
      (if dQ ψ η q < 0 then ((q : ℝ) : EReal) else ⊥) := by
    intro q
    have h0 : Measurable fun η : Measure ℝ => (η, (q : ℝ)) := measurable_prodMk_right
    have h1' := hD.comp h0
    have h1 : Measurable fun η : Measure ℝ => dQ ψ η q := h1'
    have h2 : MeasurableSet {η : Measure ℝ | dQ ψ η q < 0} := by
      have := h1 (measurableSet_Iio (a := (0 : ℝ)))
      simpa only [Set.preimage, Set.mem_Iio] using this
    exact Measurable.ite h2 measurable_const measurable_const
  have h3 : Measurable fun η : Measure ℝ =>
      ⨆ q : ℚ, (if dQ ψ η q < 0 then ((q : ℝ) : EReal) else ⊥) := Measurable.iSup hq
  have h4 : Measurable fun η : Measure ℝ =>
      (⨆ q : ℚ, (if dQ ψ η q < 0 then ((q : ℝ) : EReal) else ⊥)).toReal :=
    measurable_ereal_toReal.comp h3
  exact h4

lemma xsSel_eq {η : Measure ℝ} {z : ℝ} (hmono : StrictMono (dQ ψ η)) (hz : dQ ψ η z = 0) :
    xsSel ψ η = z := by
  have hiff : ∀ q : ℝ, dQ ψ η q < 0 ↔ q < z := fun q => by
    rw [← hz]; exact hmono.lt_iff_lt
  have key : (⨆ q : ℚ, if dQ ψ η q < 0 then ((q : ℝ) : EReal) else ⊥) = (z : EReal) := by
    apply le_antisymm
    · refine iSup_le fun q => ?_
      split_ifs with h
      · exact EReal.coe_le_coe_iff.2 ((hiff q).1 h).le
      · exact bot_le
    · refine le_of_forall_lt fun y hy => ?_
      obtain ⟨q, hyq, hqz⟩ := EReal.exists_rat_btwn_of_lt hy
      have hq : dQ ψ η q < 0 := (hiff q).2 (EReal.coe_lt_coe_iff.1 hqz)
      refine lt_of_lt_of_le hyq (le_iSup_of_le q ?_)
      rw [ite_eq_left hq]
  unfold xsSel
  rw [key, EReal.toReal_coe]

/-! ### Parametric interval integrals and the iteration -/

lemma measurable_intervalIntegral_param {α : Type*} [MeasurableSpace α] {G : α → ℝ → ℝ}
    (hG : Measurable fun p : α × ℝ => G p.1 p.2) :
    Measurable fun p : α × ℝ => ∫ t in (0 : ℝ)..p.2, G p.1 t := by
  have h1 : ∀ p : α × ℝ, ∫ t in (0 : ℝ)..p.2, G p.1 t =
      (∫ t, (Ioc 0 p.2).indicator (G p.1) t) - ∫ t, (Ioc p.2 0).indicator (G p.1) t := by
    intro p
    rw [intervalIntegral, integral_indicator measurableSet_Ioc,
      integral_indicator measurableSet_Ioc]
  simp_rw [h1]
  have hGc : Measurable fun q : (α × ℝ) × ℝ => G q.1.1 q.2 :=
    hG.comp (measurable_fst.fst.prodMk measurable_snd)
  have hA : Measurable fun q : (α × ℝ) × ℝ => (Ioc 0 q.1.2).indicator (G q.1.1) q.2 := by
    simp only [Set.indicator_apply]
    exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd)) hGc measurable_const
  have hB : Measurable fun q : (α × ℝ) × ℝ => (Ioc q.1.2 0).indicator (G q.1.1) q.2 := by
    simp only [Set.indicator_apply]
    exact Measurable.ite ((measurableSet_lt measurable_fst.snd measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) hGc measurable_const
  exact (StronglyMeasurable.integral_prod_right' (ν := volume) hA.stronglyMeasurable).measurable.sub
    (StronglyMeasurable.integral_prod_right' (ν := volume) hB.stronglyMeasurable).measurable

lemma measurable_wIter {α : Type*} [MeasurableSpace α] {Ψ : α → ℝ → ℝ}
    (hΨ : Measurable fun p : α × ℝ => Ψ p.1 p.2) :
    ∀ n, Measurable fun p : α × ℝ => CC.ODE.Gap.wIter (Ψ p.1) id n p.2
  | 0 => measurable_snd
  | n + 1 => by
    have ih := measurable_wIter hΨ n
    show Measurable fun p : α × ℝ =>
      ∫ t in (0 : ℝ)..p.2, CC.ODE.Gap.rhs (Ψ p.1) id t (CC.ODE.Gap.wIter (Ψ p.1) id n t)
    exact measurable_intervalIntegral_param
      (G := fun a t => CC.ODE.Gap.rhs (Ψ a) id t (CC.ODE.Gap.wIter (Ψ a) id n t))
      (measurable_const.sub (hΨ.div ih))

lemma measurable_wLim {α : Type*} [MeasurableSpace α] {Ψ : α → ℝ → ℝ}
    (hΨ : Measurable fun p : α × ℝ => Ψ p.1 p.2) :
    Measurable fun p : α × ℝ => CC.ODE.Gap.wLim (Ψ p.1) id p.2 :=
  Measurable.iInf (f := fun n (p : α × ℝ) => CC.ODE.Gap.wIter (Ψ p.1) id n p.2)
    fun n => measurable_wIter hΨ n

/-- The glued rule is jointly measurable in a parameter on which `f` and `c` depend measurably. -/
lemma measurable_selRule {α : Type*} [MeasurableSpace α] (κ : ℝ) {F : α → ℝ → ℝ} {c : α → ℝ}
    (hF : Measurable fun p : α × ℝ => F p.1 p.2) (hc : Measurable c) :
    Measurable fun p : α × ℝ => selRule κ (F p.1) (c p.1) p.2 := by
  have hc1 : Measurable fun p : α × ℝ => c p.1 := hc.comp measurable_fst
  have hR := measurable_wLim (Ψ := fun a y => κ * F a (c a + y))
    ((hF.comp (measurable_fst.prodMk (hc1.add measurable_snd))).const_mul κ)
  have hL := measurable_wLim (Ψ := fun a y => -κ * F a (c a - y))
    ((hF.comp (measurable_fst.prodMk (hc1.sub measurable_snd))).const_mul (-κ))
  simp only [selRule, CC.General.Rev.glue, tailR, tailL]
  exact Measurable.ite (measurableSet_le hc1 measurable_snd)
    (measurable_snd.sub (hR.comp (measurable_fst.prodMk (measurable_snd.sub hc1))))
    (measurable_snd.add (hL.comp (measurable_fst.prodMk (hc1.sub measurable_snd))))

end CC.LearnTheta.SelAux
