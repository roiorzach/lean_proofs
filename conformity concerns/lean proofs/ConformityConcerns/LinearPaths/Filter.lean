import ConformityConcerns.LinearPaths.Indep
import ConformityConcerns.LinearPaths.Step
import ConformityConcerns.LinearPaths.Coef

/-!
# The public filter along a linear profile

`par σ S₁ t h` are the posterior parameters at the history `h` of date `t`: the prior
`(0, Σ₁)` at date `0`, and then `nextPar` with the regression coefficients `kt`, `bt` of the
period strategy (so they depend on the history, including whether the period reveals).

The invariant (`inv_all`): the joint law of `(h^t, (θ, μ))` is `law(h^t) ⊗ N(par t h^t)`.
The step uses that, almost surely, the action is `a_t = kt · Z_t + bt` (`act_ae`): at almost
every on-path history the period strategy pools or reveals (Lemma 3), whence this form.
-/

namespace CC.LinearPaths

open MeasureTheory ProbabilityTheory
open CC.Bridge
open scoped ENNReal

/-- The weight `γ_t` recorded in a history of date `t`. -/
def lastγ {t : ℕ} (h : Hist t) : ℝ := h.1 (Fin.last t)

lemma measurable_lastγ (t : ℕ) : Measurable (lastγ : Hist t → ℝ) :=
  (measurable_pi_apply _).comp measurable_fst

variable (σ : Profile) (S₁ : M2)

/-- Posterior parameters along histories. -/
noncomputable def par : (t : ℕ) → Hist t → E2 × M2
  | 0 => fun _ => (0, S₁)
  | t + 1 => fun h' =>
      nextPar (par t (restr h')).1 (par t (restr h')).2 (lastγ (restr h'))
        (kco (par t (restr h')).1 (par t (restr h')).2 (lastγ (restr h')) (σ t (restr h')))
        (bco (par t (restr h')).1 (par t (restr h')).2 (lastγ (restr h')) (σ t (restr h')))
        (h'.2 (Fin.last t))

/-- The slope of the period-`t` strategy at `h`. -/
noncomputable def kt (t : ℕ) (h : Hist t) : ℝ :=
  kco (par σ S₁ t h).1 (par σ S₁ t h).2 (lastγ h) (σ t h)

/-- The intercept of the period-`t` strategy at `h`. -/
noncomputable def bt (t : ℕ) (h : Hist t) : ℝ :=
  bco (par σ S₁ t h).1 (par σ S₁ t h).2 (lastγ h) (σ t h)

lemma par_zero (h : Hist 0) : par σ S₁ 0 h = (0, S₁) := rfl

lemma par_extH {t : ℕ} (h : Hist t) (y g : ℝ) :
    par σ S₁ (t + 1) (extH h y g) =
      nextPar (par σ S₁ t h).1 (par σ S₁ t h).2 (lastγ h) (kt σ S₁ t h) (bt σ S₁ t h) y := by
  show nextPar (par σ S₁ t (restr (extH h y g))).1 _ _ _ _ _ = _
  rw [restr_extH, extH_last]
  rfl

variable {σ S₁}

theorem measurable_par (hσ : ∀ t, Measurable (Function.uncurry (σ t))) :
    ∀ t, Measurable (par σ S₁ t)
  | 0 => measurable_const
  | t + 1 => by
    have ih := measurable_par hσ t
    have hr := measurable_restr t
    have hp := ih.comp hr
    have hγ := (measurable_lastγ t).comp hr
    have ha : Measurable (Function.uncurry (fun h' : Hist (t + 1) => σ t (restr h'))) :=
      (hσ t).comp ((hr.comp measurable_fst).prodMk measurable_snd)
    exact measurable_nextPar (measurable_fst.comp hp) (measurable_snd.comp hp) hγ
      (measurable_kco hp hγ ha) (measurable_bco hp hγ ha)
      ((measurable_pi_apply _).comp measurable_snd)

lemma measurable_kt (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (t : ℕ) :
    Measurable (kt σ S₁ t) :=
  measurable_kco (measurable_par hσ t) (measurable_lastγ t) (hσ t)

lemma measurable_bt (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (t : ℕ) :
    Measurable (bt σ S₁ t) :=
  measurable_bco (measurable_par hσ t) (measurable_lastγ t) (hσ t)

theorem par_psd (hS₁ : S₁.PosSemidef) : ∀ t (h : Hist t), (par σ S₁ t h).2.PosSemidef
  | 0, _ => hS₁
  | t + 1, h' => nextPar_psd (par_psd hS₁ t (restr h')) _ _ _ _

variable {G : Measure ℝ} [IsProbabilityMeasure G]

/-- The invariant at date `t`: the posterior given `h^t` is `N(par t h^t)`. -/
def Inv (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (S₁ : M2) (G : Measure ℝ)
    [IsProbabilityMeasure G] (t : ℕ) : Prop :=
  (lawG S₁ G).map (fun ω => (hist σ t ω, ω.1)) =
    ((lawG S₁ G).map (hist σ t)) ⊗ₘ gaussK (par σ S₁ t) (measurable_par hσ t)

lemma post_ae_of_inv (hσ : ∀ t, Measurable (Function.uncurry (σ t))) {t : ℕ}
    (hinv : Inv hσ S₁ G t) :
    ∀ᵐ ω ∂(lawG S₁ G), post S₁ G σ t (hist σ t ω) =
      multivariateGaussian (par σ S₁ t (hist σ t ω)).1 (par σ S₁ t (hist σ t ω)).2 := by
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := lawG S₁ G)
    (measurable_hist hσ t) measurable_fst hinv
  filter_upwards [ae_of_ae_map (measurable_hist hσ t).aemeasurable h] with ω hω
  exact hω

theorem inv_zero (hσ : ∀ t, Measurable (Function.uncurry (σ t))) : Inv hσ S₁ G 0 := by
  have hK : gaussK (par σ S₁ 0) (measurable_par hσ 0) =
      Kernel.const (Hist 0) (multivariateGaussian 0 S₁) := by
    ext1 h; rfl
  rw [Inv, hK, Measure.compProd_const, law_base]

/-- **Almost surely the action is `kt · Z_t + bt`**, at every date where the invariant holds:
at almost every on-path history the period strategy pools or reveals (Lemma 3). -/
theorem act_ae {κ : ℝ} (hκ : 0 < κ) (hS₁ : S₁.PosSemidef)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t))) {t : ℕ}
    (hE : ∀ᵐ ω ∂(lawG S₁ G), LinearAt κ S₁ G σ t (hist σ t ω))
    (hinv : Inv hσ S₁ G t) :
    ∀ᵐ ω ∂(lawG S₁ G), act σ t ω = kt σ S₁ t (hist σ t ω) *
        Zg (par σ S₁ t (hist σ t ω)).1 (par σ S₁ t (hist σ t ω)).2 (lastγ (hist σ t ω))
          (priv t ω) + bt σ S₁ t (hist σ t ω) := by
  have hp := measurable_par (S₁ := S₁) hσ t
  have hH := measurable_hist hσ t
  have hk := measurable_kt (S₁ := S₁) hσ t
  have hb := measurable_bt (S₁ := S₁) hσ t
  -- the "good" histories: the period strategy is `kt · Z + bt` for almost every type
  set T : Set (Hist t × E2) := {q | σ t q.1 q.2 ≠ kt σ S₁ t q.1 *
      Zg (par σ S₁ t q.1).1 (par σ S₁ t q.1).2 (lastγ q.1) q.2 + bt σ S₁ t q.1} with hT
  have hZq : Measurable (fun q : Hist t × E2 =>
      Zg (par σ S₁ t q.1).1 (par σ S₁ t q.1).2 (lastγ q.1) q.2) :=
    measurable_Zg (measurable_fst.comp (hp.comp measurable_fst))
      (measurable_snd.comp (hp.comp measurable_fst))
      ((measurable_lastγ t).comp measurable_fst) measurable_snd
  have hTm : MeasurableSet T :=
    (measurableSet_eq_fun (hσ t) (((hk.comp measurable_fst).mul hZq).add
      (hb.comp measurable_fst))).compl
  have hGm : MeasurableSet {h : Hist t | typeK (par σ S₁ t) hp h (Prod.mk h ⁻¹' T) = 0} :=
    Kernel.measurable_kernel_prodMk_left hTm (measurableSet_singleton 0)
  have hgood : ∀ᵐ ω ∂(lawG S₁ G),
      typeK (par σ S₁ t) hp (hist σ t ω) (Prod.mk (hist σ t ω) ⁻¹' T) = 0 := by
    filter_upwards [post_ae_of_inv hσ hinv, hE] with ω hpost hlin
    set h := hist σ t ω
    obtain ⟨φ, hEq, hSO⟩ := hlin _ _ (par_psd (σ := σ) hS₁ t h) hpost
    have hG := gameAt_std (m := (par σ S₁ t h).1) (S := (par σ S₁ t h).2) (γ := h.1 (Fin.last t))
      (par_psd (σ := σ) hS₁ t h) hκ
    have hform : σ t h =ᵐ[multivariateGaussian (par σ S₁ t h).1 ((par σ S₁ t h).2 + 1)]
        fun x => kt σ S₁ t h * Zg (par σ S₁ t h).1 (par σ S₁ t h).2 (lastγ h) x + bt σ S₁ t h := by
      rcases LG.lemma3 _ hG hEq hSO with hpool | ⟨hrev, -⟩
      · exact (coef_pool hpool).2.2
      · exact (coef_reveal (par_psd (σ := σ) hS₁ t h) hrev).2.2
    exact ae_iff.1 hform
  have hgood' : ∀ᵐ h ∂((lawG S₁ G).map (hist σ t)),
      typeK (par σ S₁ t) hp h (Prod.mk h ⁻¹' T) = 0 :=
    (ae_map_iff hH.aemeasurable hGm).2 hgood
  -- the bad event has probability zero
  set Ψ : Ωg → (Hist t × E2) × (E2 × ℝ) := fun ω => ((hist σ t ω, ω.1), (ω.2.1 t, ω.2.2 (t + 1)))
    with hΨ
  have hΨm : Measurable Ψ :=
    (hH.prodMk measurable_fst).prodMk (((measurable_pi_apply t).comp (measurable_fst.comp
      measurable_snd)).prodMk ((measurable_pi_apply (t + 1)).comp
        (measurable_snd.comp measurable_snd)))
  set badQ : Set ((Hist t × E2) × (E2 × ℝ)) := {q | (q.1.1, q.1.2 + q.2.1) ∈ T} with hbadQ
  have hbadQm : MeasurableSet badQ :=
    ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).add
      (measurable_fst.comp measurable_snd))) hTm
  rw [ae_iff]
  have hset : {ω | ¬ act σ t ω = kt σ S₁ t (hist σ t ω) *
      Zg (par σ S₁ t (hist σ t ω)).1 (par σ S₁ t (hist σ t ω)).2 (lastγ (hist σ t ω))
        (priv t ω) + bt σ S₁ t (hist σ t ω)} = Ψ ⁻¹' badQ := rfl
  rw [hset, ← Measure.map_apply hΨm hbadQm, law_step hσ t, hinv,
    ← lintegral_indicator_one hbadQm, lintegral_decomp _ _ _ _ _ (measurable_one.indicator hbadQm)]
  have inner : ∀ (h : Hist t) (g : ℝ),
      ∫⁻ w, badQ.indicator (1 : (Hist t × E2) × (E2 × ℝ) → ℝ≥0∞) ((h, w.1), (w.2, g))
          ∂(periodLaw (par σ S₁ t h).1 (par σ S₁ t h).2) =
        typeK (par σ S₁ t) hp h (Prod.mk h ⁻¹' T) := by
    intro h g
    have hTh : MeasurableSet (Prod.mk h ⁻¹' T) := measurable_prodMk_left hTm
    have e : (fun w : Ω₂ => badQ.indicator (1 : (Hist t × E2) × (E2 × ℝ) → ℝ≥0∞)
        ((h, w.1), (w.2, g))) =
        (privInfo ⁻¹' (Prod.mk h ⁻¹' T)).indicator (1 : Ω₂ → ℝ≥0∞) := by
      funext w
      rfl
    rw [e, lintegral_indicator_one (measurable_privInfo hTh),
      ← Measure.map_apply measurable_privInfo hTh, privInfo_law (par_psd (σ := σ) hS₁ t h)]
    rfl
  simp_rw [inner, lintegral_const, measure_univ, mul_one]
  exact (lintegral_congr_ae hgood').trans lintegral_zero

theorem inv_succ {κ : ℝ} (hκ : 0 < κ) (hS₁ : S₁.PosSemidef)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t))) {t : ℕ}
    (hE : ∀ᵐ ω ∂(lawG S₁ G), LinearAt κ S₁ G σ t (hist σ t ω))
    (hinv : Inv hσ S₁ G t) : Inv hσ S₁ G (t + 1) := by
  have hp := measurable_par (S₁ := S₁) hσ t
  have hH := measurable_hist hσ t
  set ρ := (lawG S₁ G).map (hist σ t) with hρ
  set Ψ : Ωg → (Hist t × E2) × (E2 × ℝ) := fun ω => ((hist σ t ω, ω.1), (ω.2.1 t, ω.2.2 (t + 1)))
    with hΨ
  have hΨm : Measurable Ψ :=
    (hH.prodMk measurable_fst).prodMk (((measurable_pi_apply t).comp (measurable_fst.comp
      measurable_snd)).prodMk ((measurable_pi_apply (t + 1)).comp
        (measurable_snd.comp measurable_snd)))
  have hlaw : (lawG S₁ G).map Ψ = (ρ ⊗ₘ gaussK (par σ S₁ t) hp).prod ((stdGaussian E2).prod G) := by
    rw [hΨ, law_step hσ t, hinv]
  have hstep := step_law ρ (par σ S₁ t) hp (par_psd (σ := σ) hS₁ t) lastγ (kt σ S₁ t) (bt σ S₁ t)
    (measurable_lastγ t) (measurable_kt hσ t) (measurable_bt hσ t)
    (fun h => kco_nonneg _ _ _ _) (fun r : Hist t × ℝ × ℝ => extH r.1 r.2.1 r.2.2)
    (measurable_extH t) (par σ S₁ (t + 1)) (measurable_par hσ (t + 1))
    (fun h y g => par_extH σ S₁ h y g) G
  set Φ1 : (Hist t × E2) × (E2 × ℝ) → Hist (t + 1) := fun q =>
    extH q.1.1 (kt σ S₁ t q.1.1 * Zof (par σ S₁ t q.1.1).1 (par σ S₁ t q.1.1).2 (lastγ q.1.1)
      (q.1.2, q.2.1) + bt σ S₁ t q.1.1) q.2.2 with hΦ1
  have h11 : Measurable (fun q : (Hist t × E2) × (E2 × ℝ) => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hZm : Measurable (fun q : (Hist t × E2) × (E2 × ℝ) =>
      Zof (par σ S₁ t q.1.1).1 (par σ S₁ t q.1.1).2 (lastγ q.1.1) (q.1.2, q.2.1)) :=
    measurable_Zof_par (measurable_fst.comp (hp.comp h11)) (measurable_snd.comp (hp.comp h11))
      ((measurable_lastγ t).comp h11)
      ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
  have hYm : Measurable (fun q : (Hist t × E2) × (E2 × ℝ) =>
      kt σ S₁ t q.1.1 * Zof (par σ S₁ t q.1.1).1 (par σ S₁ t q.1.1).2 (lastγ q.1.1)
        (q.1.2, q.2.1) + bt σ S₁ t q.1.1) :=
    (((measurable_kt hσ t).comp h11).mul hZm).add ((measurable_bt hσ t).comp h11)
  have hΦ1m : Measurable Φ1 :=
    (measurable_extH t).comp (h11.prodMk (hYm.prodMk (measurable_snd.comp measurable_snd)))
  have hΦm : Measurable (fun q : (Hist t × E2) × (E2 × ℝ) => (Φ1 q, q.1.2)) :=
    hΦ1m.prodMk (measurable_snd.comp measurable_fst)
  have hae : ∀ᵐ ω ∂(lawG S₁ G), hist σ (t + 1) ω = Φ1 (Ψ ω) := by
    filter_upwards [act_ae hκ hS₁ hσ hE hinv] with ω hω
    rw [hist_succ, hω]
    rfl
  have e1 : (lawG S₁ G).map (fun ω => (hist σ (t + 1) ω, ω.1)) =
      ((ρ ⊗ₘ gaussK (par σ S₁ t) hp).prod ((stdGaussian E2).prod G)).map
        (fun q => (Φ1 q, q.1.2)) := by
    rw [← hlaw, Measure.map_map hΦm hΨm]
    exact Measure.map_congr (hae.mono fun ω hω => by simp only [Function.comp, hω]; rfl)
  have e2 : (lawG S₁ G).map (hist σ (t + 1)) =
      ((ρ ⊗ₘ gaussK (par σ S₁ t) hp).prod ((stdGaussian E2).prod G)).map Φ1 := by
    rw [← hlaw, Measure.map_map hΦ1m hΨm]
    exact Measure.map_congr hae
  rw [Inv, e1, e2]
  exact hstep

theorem inv_all {κ : ℝ} (hκ : 0 < κ) (hS₁ : S₁.PosSemidef)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (hE : IsLinearProfile κ S₁ G σ) :
    ∀ t, Inv hσ S₁ G t
  | 0 => inv_zero hσ
  | t + 1 => inv_succ hκ hS₁ hσ (hE t) (inv_all hκ hS₁ hσ hE t)

/-- The invariant at every date, when each date's linearity may use the invariant at that date. -/
theorem inv_all_of_step {κ : ℝ} (hκ : 0 < κ) (hS₁ : S₁.PosSemidef)
    (hσ : ∀ t, Measurable (Function.uncurry (σ t)))
    (hstep : ∀ t, Inv hσ S₁ G t → ∀ᵐ ω ∂(lawG S₁ G), LinearAt κ S₁ G σ t (hist σ t ω)) :
    ∀ t, Inv hσ S₁ G t
  | 0 => inv_zero hσ
  | t + 1 => inv_succ hκ hS₁ hσ (hstep t (inv_all_of_step hκ hS₁ hσ hstep t))
      (inv_all_of_step hκ hS₁ hσ hstep t)

end CC.LinearPaths
