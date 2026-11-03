import NoisyVD.Volunteer

/-!
# Non-vacuity: a concrete Volunteer's Dilemma satisfying all the hypotheses

Costs are standard normal (as in a QRE with Gaussian shocks), `π = 1/4`, `H = 2`, `L = -1`.  This
confirms that the hypotheses of Propositions `prop_volunteers` and Lemma `lemma_threshold_value` are
jointly satisfiable.
-/

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace NoisyVD

namespace Example

/-- The standard normal law as a probability measure with density `φ`. -/
noncomputable def normalMeasure : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (phi x)

lemma normal_apply (S : Set ℝ) (hS : MeasurableSet S) :
    normalMeasure S = ENNReal.ofReal (∫ x in S, phi x) := by
  unfold normalMeasure
  rw [withDensity_apply _ hS]
  rw [ofReal_integral_eq_lintegral_ofReal integrable_phi.integrableOn
    (Eventually.of_forall fun x => (phi_pos x).le)]

instance : IsProbabilityMeasure normalMeasure := by
  constructor
  rw [normal_apply _ MeasurableSet.univ, Measure.restrict_univ, integral_phi]
  simp

lemma normal_real (S : Set ℝ) (hS : MeasurableSet S) :
    normalMeasure.real S = ∫ x in S, phi x := by
  unfold Measure.real
  rw [normal_apply S hS, ENNReal.toReal_ofReal]
  exact setIntegral_nonneg hS fun x _ => (phi_pos x).le

/-- The prior with `Pr(ω = 1) = 1/4`. -/
noncomputable def priorMeasure : Measure Bool :=
  ENNReal.ofReal (1 / 4) • Measure.dirac true + ENNReal.ofReal (3 / 4) • Measure.dirac false

instance : IsProbabilityMeasure priorMeasure := by
  constructor
  simp only [priorMeasure, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- `u^p(a, ω) = a (3ω - 1)`: `H = 2`, `L = -1`. -/
noncomputable def env : Env Bool Bool where
  u := fun a ω => if a then (if ω then 2 else -1) else 0
  u_cont := continuous_of_discreteTopology
  prior := ⟨priorMeasure, inferInstance⟩
  cost := ⟨normalMeasure, inferInstance⟩

lemma F_eq : env.F = Phi := by
  funext x
  exact normal_real _ measurableSet_Iic

lemma pr_eq : VD.pr env = 1 / 4 := by
  show (priorMeasure {true}).toReal = 1 / 4
  simp only [priorMeasure, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp

lemma noise : env.Noise := by
  constructor
  · have h1 : env.F (-env.B - 1) ≤ env.Fm (-env.B) := Env.F_le_Fm env (by linarith)
    rw [F_eq] at h1
    exact lt_of_lt_of_le (Phi_pos _) h1
  · have h1 := Env.F_add_Ioi env env.B
    rw [F_eq] at h1
    have h2 := Phi_lt_one env.B
    linarith

lemma assumptions : VD.Assumptions env where
  H_pos := by norm_num [VD.H, env]
  L_neg := by norm_num [VD.L, env]
  pr_pos := by rw [pr_eq]; norm_num
  prior := by
    rw [VD.integral_bool, VD.integral_bool, pr_eq]
    norm_num [env]

lemma smooth : VD.Smooth env (phi 0) where
  hasDeriv := by rw [F_eq]; exact hasDerivAt_Phi 0
  cont := ⟨1, one_pos, fun x _ => by rw [F_eq]; exact continuous_Phi.continuousAt⟩

/-- The threshold characterisation holds in this example. -/
theorem threshold_applies :
    env.PiSQ < liminf env.PiT atTop ↔
      Fbar (VD.pr env) (VD.H env) (-VD.L env) (env.F 0 * (1 - env.F 0)) < phi 0 :=
  (VD.threshold_iff assumptions noise (phi_pos 0) smooth).2

end Example

end NoisyVD
