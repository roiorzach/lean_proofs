import ConformityConcerns.LinearPaths.Filter

/-!
# Lemma 3 (last sentence) along any linear profile: public beliefs are Gaussian on path

Manuscript, Lemma 3: "If public beliefs about `(θ, μ)` at `h^t` are Gaussian (possibly
degenerate), then in any equilibrium satisfying Linearity and, if `s̃(h^t) = 0`, Social
Optimality, `a_t` is either constant or strictly increasing and affine in `Z_t`; in the latter
case, every action is on path and `φ(· | h^t, a_t)` is Gaussian with variance independent of
`a_t`. Public beliefs are Gaussian at every on-path history."

The period-level part is `CC.LG.lemma3`. Here the last sentence is proved for every measurable
profile that satisfies Linearity (and Social Optimality where `s̃ = 0`) at almost every on-path
history (`IsLinearProfile`), not only along the signaling equilibrium
(`CC.Bridge.beliefs_gaussian`). Whether a period is revealing or pooling may depend on the whole
history.

* `beliefs_gaussian_of_linear`: the manuscript's sentence. At every date, at almost every
  on-path history, the public posterior of `(θ, μ)` is Gaussian.
* `lemma3_onPath`: moreover, at almost every on-path history the period strategy is either
  constant or strictly increasing and affine in `Z_t`, in the period game at that history.
* `beliefs_gaussian_of_linear_param`: the form proved by induction. The posterior is
  `N(m_t(h^t), S_t(h^t))` for measurable maps `m_t`, `S_t` of the history, starting from the prior
  `N(0, Σ₁)`; after a pooling period they are unchanged, and after a revealing period they are
  updated as after observing `Z_t` (the regression of `(θ, μ)` on `Z_t`, `regC + Z_t • regK`, and
  `kalman`).
-/

namespace CC.LinearPaths

open MeasureTheory ProbabilityTheory
open CC.Bridge

variable {κ : ℝ} {S₁ : M2} {G : Measure ℝ} [IsProbabilityMeasure G] {σ : Profile}

/-- **Lemma 3 (last sentence), with the parameters of the posterior.** In a measurable profile
satisfying Linearity, and Social Optimality where `s̃(h^t) = 0`, there are measurable maps
`m_t`, `S_t` of the history, with `S_t` positive semidefinite, `m_0 = 0` and `S_0 = Σ₁`, such that
at every date, at almost every on-path history `h^t`:
* the public posterior of `(θ, μ)` is `N(m_t(h^t), S_t(h^t))`;
* if the period strategy is pooling, the parameters at `h^{t+1}` are those at `h^t`;
* if it is revealing, they are those after observing `Z_t`: mean `regC + Z_t • regK` and
  covariance `kalman S_t γ_t`. -/
theorem beliefs_gaussian_of_linear_param (hκ : 0 < κ) (hS₁ : S₁.PosSemidef)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (hE : IsLinearProfile κ S₁ G σ) :
    ∃ (m : ∀ t, Hist t → E2) (S : ∀ t, Hist t → M2),
      (∀ t, Measurable (m t)) ∧ (∀ t, Measurable (S t)) ∧ (∀ t h, (S t h).PosSemidef) ∧
      (∀ h, m 0 h = 0 ∧ S 0 h = S₁) ∧
      ∀ t, ∀ᵐ ω ∂(lawG S₁ G),
        let h := hist σ t ω
        let h' := hist σ (t + 1) ω
        let Γ := gameAt (m t h) (S t h) (gam ω t) κ
        post S₁ G σ t h = multivariateGaussian (m t h) (S t h) ∧
          (Γ.IsPooling (σ t h) → m (t + 1) h' = m t h ∧ S (t + 1) h' = S t h) ∧
          (Γ.IsRevealing (σ t h) →
            m (t + 1) h' =
                regC (m t h) (S t h) (gam ω t) + Γ.Z (priv t ω) • regK (S t h) (gam ω t) ∧
              S (t + 1) h' = kalman (S t h) (gam ω t)) := by
  refine ⟨fun t h => (par σ S₁ t h).1, fun t h => (par σ S₁ t h).2,
    fun t => measurable_fst.comp (measurable_par hσ t),
    fun t => measurable_snd.comp (measurable_par hσ t),
    fun t h => par_psd (σ := σ) hS₁ t h, fun h => ⟨rfl, rfl⟩, fun t => ?_⟩
  have hinv := inv_all hκ hS₁ hσ hE t
  filter_upwards [post_ae_of_inv hσ hinv, act_ae hκ hS₁ hσ (hE t) hinv] with ω hpost hact
  have hsucc : par σ S₁ (t + 1) (hist σ (t + 1) ω) =
      nextPar (par σ S₁ t (hist σ t ω)).1 (par σ S₁ t (hist σ t ω)).2 (gam ω t)
        (kt σ S₁ t (hist σ t ω)) (bt σ S₁ t (hist σ t ω)) (act σ t ω) := by
    rw [hist_succ, par_extH]
    rfl
  dsimp only
  refine ⟨hpost, fun hpool => ?_, fun hrev => ?_⟩
  · have hk : kt σ S₁ t (hist σ t ω) = 0 := (coef_pool hpool).2.1
    rw [hsucc, hk, nextPar_of_not_pos (lt_irrefl 0)]
    exact ⟨rfl, rfl⟩
  · have hk : 0 < kt σ S₁ t (hist σ t ω) :=
      (coef_reveal (par_psd (σ := σ) hS₁ t (hist σ t ω)) hrev).1
    have hz : (kt σ S₁ t (hist σ t ω) * Zg (par σ S₁ t (hist σ t ω)).1
        (par σ S₁ t (hist σ t ω)).2 (lastγ (hist σ t ω)) (priv t ω) + bt σ S₁ t (hist σ t ω) -
          bt σ S₁ t (hist σ t ω)) / kt σ S₁ t (hist σ t ω) =
        Zg (par σ S₁ t (hist σ t ω)).1 (par σ S₁ t (hist σ t ω)).2 (lastγ (hist σ t ω))
          (priv t ω) := by
      field_simp
      ring
    rw [hsucc, nextPar_pos hk, hact, hz]
    exact ⟨rfl, rfl⟩

/-- **Lemma 3 (last sentence): public beliefs are Gaussian at every on-path history.** In a
measurable profile satisfying Linearity, and Social Optimality where `s̃(h^t) = 0`, at every
date, at almost every on-path history the public posterior of `(θ, μ)` is Gaussian (possibly
degenerate). -/
theorem beliefs_gaussian_of_linear (hκ : 0 < κ) (hS₁ : S₁.PosSemidef)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (hE : IsLinearProfile κ S₁ G σ) (t : ℕ) :
    ∀ᵐ ω ∂(lawG S₁ G), ∃ (m : E2) (S : M2), S.PosSemidef ∧
      post S₁ G σ t (hist σ t ω) = multivariateGaussian m S := by
  obtain ⟨m, S, -, -, hpsd, -, h⟩ := beliefs_gaussian_of_linear_param hκ hS₁ hσ hE
  filter_upwards [h t] with ω hω
  dsimp only at hω
  exact ⟨m t (hist σ t ω), S t (hist σ t ω), hpsd t _, hω.1⟩

/-- **Lemma 3 along the path.** In a measurable profile satisfying Linearity, and Social
Optimality where `s̃(h^t) = 0`, at every date, at almost every on-path history public beliefs
are Gaussian, `N(m, S)`, and in the period game at that history the period strategy is either
constant or strictly increasing and affine in `Z_t` (almost surely in the private
information). -/
theorem lemma3_onPath (hκ : 0 < κ) (hS₁ : S₁.PosSemidef)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (hE : IsLinearProfile κ S₁ G σ) (t : ℕ) :
    ∀ᵐ ω ∂(lawG S₁ G), ∃ (m : E2) (S : M2), S.PosSemidef ∧
      post S₁ G σ t (hist σ t ω) = multivariateGaussian m S ∧
      ((gameAt m S (gam ω t) κ).IsPooling (σ t (hist σ t ω)) ∨
        (gameAt m S (gam ω t) κ).IsRevealing (σ t (hist σ t ω))) := by
  have hinv := inv_all hκ hS₁ hσ hE t
  filter_upwards [post_ae_of_inv hσ hinv, hE t] with ω hpost hlin
  have hpsd := par_psd (σ := σ) hS₁ t (hist σ t ω)
  refine ⟨_, _, hpsd, hpost, ?_⟩
  obtain ⟨φ, hEq, hSO⟩ := hlin _ _ hpsd hpost
  have hG := gameAt_std (m := (par σ S₁ t (hist σ t ω)).1) (γ := gam ω t) hpsd hκ
  rcases LG.lemma3 _ hG hEq hSO with hp | ⟨hr, -⟩
  · exact Or.inl hp
  · exact Or.inr hr

end CC.LinearPaths
