import ConformityConcerns.LinearPaths.Meas

/-!
# Independence of the date-`t` noise and the next weight from the history

Under `lawG`, the history `h^t` and `(θ, μ)` are functions of the past (`trW t`), which is
independent of the noise `(ε_t, ν_t) ~ N(0, I)` and the next weight `γ_{t+1} ~ G`:
the joint law of `((h^t, (θ, μ)), ((ε_t, ν_t), γ_{t+1}))` is a product (`law_step`). At date `0`
the history is `γ_0`, independent of `(θ, μ) ~ N(0, Σ₁)` (`law_base`).
-/

namespace CC.LinearPaths

open MeasureTheory ProbabilityTheory
open CC.Bridge

/-- Truncation of an i.i.d. sequence before `n` is independent of its `n`-th coordinate. -/
lemma indep_trunc_eval {α : Type*} [MeasurableSpace α] [Zero α] (μ : Measure α)
    [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (fun f : ℕ → α => fun i => if i < n then f i else 0) (fun f => f n)
      (Measure.infinitePi fun _ : ℕ => μ) := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ => id)
    (fun _ => measurable_id)
  have h2 := h.indepFun_finset (Finset.range n) {n} (by simp) (fun i => measurable_pi_apply i)
  let φ : (Finset.range n → α) → (ℕ → α) := fun η i =>
    if hi : i < n then η ⟨i, Finset.mem_range.2 hi⟩ else 0
  let ψ : (({n} : Finset ℕ) → α) → α := fun η => η ⟨n, Finset.mem_singleton_self n⟩
  have hφ : Measurable φ := by
    refine Measurable.of_eval fun i => ?_
    by_cases hi : i < n
    · simp only [φ, hi, ↓reduceDIte]; exact measurable_pi_apply _
    · simp only [φ, hi, ↓reduceDIte]; exact measurable_const
  have hψ : Measurable ψ := measurable_pi_apply _
  have h3 := h2.comp hφ hψ
  have e1 : (fun f : ℕ → α => fun i => if i < n then f i else 0) =
      φ ∘ (fun a (i : Finset.range n) => (fun i (ω : ℕ → α) => id (ω i)) i a) := by
    funext f i
    simp only [Function.comp, φ, id]
    split_ifs <;> rfl
  rw [e1]
  exact h3

lemma measurable_truncF {α : Type*} [MeasurableSpace α] [Zero α] (n : ℕ) :
    Measurable (fun f : ℕ → α => fun i => if i < n then f i else 0) := by
  refine Measurable.of_eval fun i => ?_
  by_cases hi : i < n
  · simp only [hi, ↓reduceIte]; exact measurable_pi_apply i
  · simp only [hi, ↓reduceIte]; exact measurable_const

section Swap

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
  [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd]

/-- `((a, b), (c, d)) ↦ ((a, c), (b, d))` preserves product measures. -/
lemma mp_swap4 : MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have e1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have e2 := (MeasurePreserving.id μa).prod
    (MeasurePreserving.symm _ (measurePreserving_prodAssoc μb μc μd))
  have e3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have e4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have e5 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μc (μb.prod μd))
  have h := e5.comp (e4.comp (e3.comp (e2.comp e1)))
  convert h using 1
  funext p
  rfl

end Swap

variable {S₁ : M2} {G : Measure ℝ} [IsProbabilityMeasure G]

/-- The past `trW t` is independent of `((ε_t, ν_t), γ_{t+1})`, whose law is `N(0, I) ⊗ G`. -/
lemma law_trW_pair (t : ℕ) :
    (lawG S₁ G).map (fun ω => (trW t ω, (ω.2.1 t, ω.2.2 (t + 1)))) =
      ((lawG S₁ G).map (trW t)).prod ((stdGaussian E2).prod G) := by
  set με := Measure.infinitePi fun _ : ℕ => stdGaussian E2 with hμε
  set μγ := Measure.infinitePi fun _ : ℕ => G with hμγ
  set Tε : (ℕ → E2) → (ℕ → E2) := fun f i => if i < t then f i else 0 with hTε
  set Tγ : (ℕ → ℝ) → (ℕ → ℝ) := fun f i => if i < t + 1 then f i else 0 with hTγ
  have mTε : Measurable Tε := measurable_truncF t
  have mTγ : Measurable Tγ := measurable_truncF (t + 1)
  have pε : Measurable (fun f : ℕ → E2 => (Tε f, f t)) := mTε.prodMk (measurable_pi_apply t)
  have pγ : Measurable (fun f : ℕ → ℝ => (Tγ f, f (t + 1))) :=
    mTγ.prodMk (measurable_pi_apply (t + 1))
  have iε : με.map (fun f => (Tε f, f t)) = (με.map Tε).prod (stdGaussian E2) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map mTε.aemeasurable
      (measurable_pi_apply t).aemeasurable).1 (indep_trunc_eval _ t),
      Measure.infinitePi_map_eval]
  have iγ : μγ.map (fun f => (Tγ f, f (t + 1))) = (μγ.map Tγ).prod G := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map mTγ.aemeasurable
      (measurable_pi_apply (t + 1)).aemeasurable).1 (indep_trunc_eval _ (t + 1)),
      Measure.infinitePi_map_eval]
  set Q : Ωg → E2 × ((ℕ → E2) × E2) × ((ℕ → ℝ) × ℝ) :=
    fun ω => (ω.1, ((Tε ω.2.1, ω.2.1 t), (Tγ ω.2.2, ω.2.2 (t + 1)))) with hQ
  have mQ : Measurable Q := measurable_id.prodMap (pε.prodMap pγ)
  have hlawQ : (lawG S₁ G).map Q = (multivariateGaussian 0 S₁).prod
      (((με.map Tε).prod (stdGaussian E2)).prod ((μγ.map Tγ).prod G)) := by
    have h1 := Measure.map_prod_map με μγ pε pγ
    have h2 := Measure.map_prod_map (multivariateGaussian 0 S₁) (με.prod μγ) measurable_id
      (pε.prodMap pγ)
    rw [Measure.map_id] at h2
    rw [← iε, ← iγ, h1, h2]
    rfl
  set R : E2 × ((ℕ → E2) × E2) × ((ℕ → ℝ) × ℝ) → Ωg × (E2 × ℝ) :=
    fun q => ((q.1, (q.2.1.1, q.2.2.1)), (q.2.1.2, q.2.2.2)) with hR
  have mpR : MeasurePreserving R
      ((multivariateGaussian 0 S₁).prod
        (((με.map Tε).prod (stdGaussian E2)).prod ((μγ.map Tγ).prod G)))
      (((multivariateGaussian 0 S₁).prod ((με.map Tε).prod (μγ.map Tγ))).prod
        ((stdGaussian E2).prod G)) := by
    have h := (MeasurePreserving.symm _ (measurePreserving_prodAssoc (multivariateGaussian 0 S₁)
      ((με.map Tε).prod (μγ.map Tγ)) ((stdGaussian E2).prod G))).comp
      ((MeasurePreserving.id (multivariateGaussian 0 S₁)).prod
        (mp_swap4 (με.map Tε) (stdGaussian E2) (μγ.map Tγ) G))
    convert h using 1
    funext q
    rfl
  have ePair : (fun ω => (trW t ω, (ω.2.1 t, ω.2.2 (t + 1)))) = R ∘ Q := rfl
  have hpair : (lawG S₁ G).map (fun ω => (trW t ω, (ω.2.1 t, ω.2.2 (t + 1)))) =
      ((multivariateGaussian 0 S₁).prod ((με.map Tε).prod (μγ.map Tγ))).prod
        ((stdGaussian E2).prod G) := by
    rw [ePair, ← Measure.map_map mpR.measurable mQ, hlawQ, mpR.map_eq]
  have htr : (lawG S₁ G).map (trW t) =
      (multivariateGaussian 0 S₁).prod ((με.map Tε).prod (μγ.map Tγ)) := by
    have e : trW t = Prod.fst ∘ (fun ω => (trW t ω, (ω.2.1 t, ω.2.2 (t + 1)))) := rfl
    have mp : Measurable (fun ω : Ωg => (trW t ω, (ω.2.1 t, ω.2.2 (t + 1)))) :=
      (measurable_trW t).prodMk (((measurable_pi_apply t).comp (measurable_fst.comp
        measurable_snd)).prodMk ((measurable_pi_apply (t + 1)).comp
          (measurable_snd.comp measurable_snd)))
    rw [e, ← Measure.map_map measurable_fst mp, hpair, Measure.map_fst_prod,
      measure_univ, one_smul]
  rw [hpair, htr]

/-- The joint law of `((h^t, (θ, μ)), ((ε_t, ν_t), γ_{t+1}))` is a product. -/
lemma law_step {σ : Profile} (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (t : ℕ) :
    (lawG S₁ G).map (fun ω => ((hist σ t ω, ω.1), (ω.2.1 t, ω.2.2 (t + 1)))) =
      ((lawG S₁ G).map (fun ω => (hist σ t ω, ω.1))).prod ((stdGaussian E2).prod G) := by
  have hF : Measurable (fun ω : Ωg => (hist σ t ω, ω.1)) :=
    (measurable_hist hσ t).prodMk measurable_fst
  have hpair : Measurable (fun ω : Ωg => (trW t ω, (ω.2.1 t, ω.2.2 (t + 1)))) :=
    (measurable_trW t).prodMk (((measurable_pi_apply t).comp (measurable_fst.comp
      measurable_snd)).prodMk ((measurable_pi_apply (t + 1)).comp
        (measurable_snd.comp measurable_snd)))
  have e : (fun ω => ((hist σ t ω, ω.1), (ω.2.1 t, ω.2.2 (t + 1)))) =
      Prod.map (fun ω : Ωg => (hist σ t ω, ω.1)) id ∘
        (fun ω => (trW t ω, (ω.2.1 t, ω.2.2 (t + 1)))) := by
    funext ω
    simp only [Function.comp, Prod.map, id, hist_trW]
    rfl
  have e2 : (fun ω : Ωg => (hist σ t ω, ω.1)) = (fun ω : Ωg => (hist σ t ω, ω.1)) ∘ trW t := by
    funext ω
    simp only [Function.comp, hist_trW]
    rfl
  rw [e, ← Measure.map_map (hF.prodMap measurable_id) hpair, law_trW_pair,
    ← Measure.map_prod_map _ _ hF measurable_id, Measure.map_id,
    Measure.map_map hF (measurable_trW t), ← e2]

/-- At date `0` the history (the weight `γ_0`) is independent of `(θ, μ) ~ N(0, Σ₁)`. -/
lemma law_base (σ : Profile) :
    (lawG S₁ G).map (fun ω => (hist σ 0 ω, ω.1)) =
      ((lawG S₁ G).map (hist σ 0)).prod (multivariateGaussian 0 S₁) := by
  set rest := (Measure.infinitePi fun _ : ℕ => stdGaussian E2).prod
    (Measure.infinitePi fun _ : ℕ => G) with hrest
  let f0 : (ℕ → E2) × (ℕ → ℝ) → Hist 0 := fun r => ((fun i : Fin 1 => r.2 i), Fin.elim0)
  have mf0 : Measurable f0 :=
    (Measurable.of_eval fun i : Fin 1 => (measurable_pi_apply (i : ℕ)).comp measurable_snd).prodMk
      measurable_const
  have e1 : (fun ω : Ωg => (hist σ 0 ω, ω.1)) = Prod.swap ∘ Prod.map id f0 := rfl
  have e2 : hist σ 0 = f0 ∘ Prod.snd := rfl
  have hl : lawG S₁ G = (multivariateGaussian 0 S₁).prod rest := rfl
  rw [e1, ← Measure.map_map measurable_swap (measurable_id.prodMap mf0), hl,
    ← Measure.map_prod_map _ _ measurable_id mf0, Measure.map_id, Measure.prod_swap, e2,
    ← Measure.map_map mf0 measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

end CC.LinearPaths
