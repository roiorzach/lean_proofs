import ConformityConcerns.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Proposition A5 across histories: the model (`μ = 0` known, learning about `θ`, `γ_t = 1`)

Sample space `ω : ℕ → ℝ` with independent coordinates: `ω 0 = θ ~ Lθ`, `ω (2t+1) = ε_t ~ Lε`
(signal noise of player `t`) and `ω (2t+2) = v_t ~ G` (preference shock of player `t`), where
`G` has density `ψ`. Player `t` observes `s_t = θ + ε_t` and the public history `h^t` of the
`t` previous decisions; their one-dimensional type is `ṽ_t = v_t + Y_t`,
`Y_t = E(θ | s_t, h^t)` (Mathlib's conditional expectation given `σ(h^t, s_t)`).

A pure dynamic strategy profile `c t h x` gives player `t`'s decision after history `h` when
their type is `ṽ_t = x`.

At history `h`, `beliefY P c t h` is the public's conditional law of `Y_t` given `h^t = h` and
`typeLaw P c t h` the conditional law of `ṽ_t` (both `condDistrib`). The expected conformity loss
of being revealed as type `x` is `m(x | h^t) = E(v_t² | ṽ_t = x, h^t)`; as `v_t` has density `ψ`
and is independent of `(Y_t, h^t)`, Bayes' rule gives the version
`mfun ψ η x = ∫ (x-y)² ψ(x-y) dη(y) / ∫ ψ(x-y) dη(y)` with `η` the conditional law of `Y_t`.
-/

namespace CC.LearnTheta

open MeasureTheory ProbabilityTheory

set_option warn.classDefReducibility false

/-- `m(x | h^t) = E(v_t² | ṽ_t = x, h^t)` when `v_t` has density `ψ` and the conditional law of
`Y_t` given `h^t` is `η`. -/
noncomputable def mfun (ψ : ℝ → ℝ) (η : Measure ℝ) (x : ℝ) : ℝ :=
  (∫ y, (x - y) ^ 2 * ψ (x - y) ∂η) / ∫ y, ψ (x - y) ∂η

/-- The law of the preference shocks, with density `ψ`. -/
noncomputable def vLaw (ψ : ℝ → ℝ) : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ψ x))

/-- The sample space. -/
abbrev Ω := ℕ → ℝ

/-- The law of coordinate `i`: `θ` at `0`, `ε_t` at `2t+1`, `v_t` at `2t+2`. -/
noncomputable def lawSeq (Lθ Lε G : Measure ℝ) (i : ℕ) : Measure ℝ :=
  if i = 0 then Lθ else if i % 2 = 1 then Lε else G

instance lawSeq_isProb (Lθ Lε G : Measure ℝ) [IsProbabilityMeasure Lθ] [IsProbabilityMeasure Lε]
    [IsProbabilityMeasure G] (i : ℕ) : IsProbabilityMeasure (lawSeq Lθ Lε G i) := by
  unfold lawSeq; split_ifs <;> infer_instance

/-- The law of `(θ, ε_0, v_0, ε_1, v_1, …)`: independent coordinates. -/
noncomputable def law (Lθ Lε G : Measure ℝ) [IsProbabilityMeasure Lθ] [IsProbabilityMeasure Lε]
    [IsProbabilityMeasure G] : Measure Ω :=
  Measure.infinitePi (lawSeq Lθ Lε G)

instance law_isProb (Lθ Lε G : Measure ℝ) [IsProbabilityMeasure Lθ] [IsProbabilityMeasure Lε]
    [IsProbabilityMeasure G] : IsProbabilityMeasure (law Lθ Lε G) := by
  unfold law; infer_instance

/-- The fundamental `θ`. -/
def thetaV (ω : Ω) : ℝ := ω 0

/-- Player `t`'s signal noise `ε_t`. -/
def epsV (t : ℕ) (ω : Ω) : ℝ := ω (2 * t + 1)

/-- Player `t`'s preference shock `v_t`. -/
def vV (t : ℕ) (ω : Ω) : ℝ := ω (2 * t + 2)

/-- Everything realised before period `t`: `θ, ε_0, v_0, …, ε_{t-1}, v_{t-1}`. -/
def pastSigma (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (i : Fin (2 * t + 1)) => ω i) inferInstance

/-- A pure dynamic strategy profile: `c t h x` is player `t`'s decision after history `h` when
their one-dimensional type is `x`. -/
abbrev Profile := ∀ t : ℕ, (Fin t → ℝ) → ℝ → ℝ

/-- The realised public history `h^t` (the first `t` decisions). Player `t`'s decision is
`c t h^t (v_t + E(θ | h^t, s_t))`. -/
noncomputable def hist (P : Measure Ω) (c : Profile) : (t : ℕ) → Ω → (Fin t → ℝ)
  | 0 => fun _ => Fin.elim0
  | t + 1 => fun ω => Fin.snoc (hist P c t ω)
      (c t (hist P c t ω) (vV t ω +
        (P[thetaV | MeasurableSpace.comap (hist P c t) inferInstance ⊔
          MeasurableSpace.comap (fun ω => thetaV ω + epsV t ω) inferInstance]) ω))

/-- The σ-algebra of the public history `h^t`. -/
noncomputable def histSigma (P : Measure Ω) (c : Profile) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (hist P c t) inferInstance

/-- `Y_t = E(θ | h^t, s_t)`. -/
noncomputable def Ycond (P : Measure Ω) (c : Profile) (t : ℕ) : Ω → ℝ :=
  P[thetaV | histSigma P c t ⊔ MeasurableSpace.comap (fun ω => thetaV ω + epsV t ω) inferInstance]

/-- Player `t`'s one-dimensional type `ṽ_t = v_t + E(θ | h^t, s_t)`. -/
noncomputable def vtil (P : Measure Ω) (c : Profile) (t : ℕ) (ω : Ω) : ℝ :=
  vV t ω + Ycond P c t ω

/-- Player `t`'s realised decision. -/
noncomputable def act (P : Measure Ω) (c : Profile) (t : ℕ) (ω : Ω) : ℝ :=
  c t (hist P c t ω) (vtil P c t ω)

lemma hist_succ (P : Measure Ω) (c : Profile) (t : ℕ) (ω : Ω) :
    hist P c (t + 1) ω = Fin.snoc (hist P c t ω) (act P c t ω) := rfl

/-- The public's conditional law of `Y_t = E(θ | h^t, s_t)` given `h^t`. -/
noncomputable def beliefY (P : Measure Ω) [IsFiniteMeasure P] (c : Profile) (t : ℕ) :
    Kernel (Fin t → ℝ) ℝ :=
  condDistrib (Ycond P c t) (hist P c t) P

/-- The public's conditional law of player `t`'s type `ṽ_t` given `h^t`. -/
noncomputable def typeLaw (P : Measure Ω) [IsFiniteMeasure P] (c : Profile) (t : ℕ) :
    Kernel (Fin t → ℝ) ℝ :=
  condDistrib (vtil P c t) (hist P c t) P

/-- Histories at which the period-`t` decision reveals whether `ṽ_t > d`: the decision of type
`d` is below the decision of every (rational) higher type. -/
noncomputable def RevUp (P : Measure Ω) (c : Profile) (t : ℕ) (d : ℝ) : Set Ω :=
  {ω | ∀ q : ℚ, d < (q : ℝ) → c t (hist P c t ω) d < c t (hist P c t ω) q}

/-- Histories at which the period-`t` decision reveals whether `ṽ_t < d`. -/
noncomputable def RevDown (P : Measure Ω) (c : Profile) (t : ℕ) (d : ℝ) : Set Ω :=
  {ω | ∀ q : ℚ, (q : ℝ) < d → c t (hist P c t ω) q < c t (hist P c t ω) d}

end CC.LearnTheta
