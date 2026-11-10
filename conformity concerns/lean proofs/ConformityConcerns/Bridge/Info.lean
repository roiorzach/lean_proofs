import ConformityConcerns.Bridge.Meas

/-!
# Observations, the Kalman mean, and the information filtration

* `obsF γ x ε t` is the period-`t` observation as a function of the weight path, the state and
  the noises (`obs κ S₁ t ω = obsF (gam ω) ω.1 ω.2.1 t`);
* `kmean γ y t` is the Kalman mean of `(θ, μ)` after the observations `y_0, …, y_{t-1}`;
* `infoSigma t` is a filtration and every measurable function of
  `(γ_0, …, γ_t, obs_0, …, obs_{t-1})` is `infoSigma t`-measurable.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix

set_option warn.classDefReducibility false

/-- `a · v`. -/
def dotA (a : Fin 2 → ℝ) (v : E2) : ℝ := a 0 * v 0 + a 1 * v 1

lemma dotA_add (a : Fin 2 → ℝ) (v w : E2) : dotA a (v + w) = dotA a v + dotA a w := by
  simp [dotA]; ring

lemma dotA_sub (a : Fin 2 → ℝ) (v w : E2) : dotA a (v - w) = dotA a v - dotA a w := by
  simp [dotA]; ring

lemma br_meas_E2 {β : Type*} [MeasurableSpace β] {f : β → E2}
    (h : ∀ i, Measurable (fun x => f x i)) : Measurable f := by
  have hf : f = fun x => WithLp.toLp 2 (fun i => f x i) := by funext x; rfl
  rw [hf]
  exact (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval h)

lemma br_meas_coord {β : Type*} [MeasurableSpace β] {f : β → E2} (hf : Measurable f) (i : Fin 2) :
    Measurable (fun x => f x i) := by
  have : (fun x => f x i) = (fun v : Fin 2 → ℝ => v i) ∘ WithLp.ofLp ∘ f := rfl
  rw [this]
  exact (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp hf)

lemma br_meas_regK {β : Type*} [MeasurableSpace β] {f : β → M2} {g : β → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun x => regK (f x) (g x)) := by
  refine br_meas_E2 fun i => ?_
  have hv := br_meas_varZ hf hg
  have h0 := br_meas_loadA hf hg 0
  have h1 := br_meas_loadA hf hg 1
  have ei0 := br_meas_entry hf i 0
  have ei1 := br_meas_entry hf i 1
  simp only [regK, PiLp.smul_apply, mulVec, dotProduct, Fin.sum_univ_two,
    smul_eq_mul]
  fun_prop

variable (κ : ℝ) (S₁ : M2)

/-- The period-`t` observation `A_t · (x + ε_t)` (`0` at a pooling date). -/
noncomputable def obsF (γ : ℕ → ℝ) (x : E2) (ε : ℕ → E2) (t : ℕ) : ℝ :=
  haveI := Classical.propDecidable (revP κ S₁ γ t)
  if revP κ S₁ γ t then dotA (loadA (SigP κ S₁ γ t) (γ t)) (x + ε t) else 0

lemma obs_eq (t : ℕ) (ω : Ωg) : obs κ S₁ t ω = obsF κ S₁ (gam ω) ω.1 ω.2.1 t := rfl

/-- The Kalman mean of `(θ, μ)` after observing `y_0, …, y_{t-1}` along the weight path `γ`. -/
noncomputable def kmean (γ : ℕ → ℝ) (y : ℕ → ℝ) : ℕ → E2
  | 0 => 0
  | t + 1 =>
    haveI := Classical.propDecidable (revP κ S₁ γ t)
    if revP κ S₁ γ t then
      kmean γ y t + (y t - dotA (loadA (SigP κ S₁ γ t) (γ t)) (kmean γ y t)) •
        regK (SigP κ S₁ γ t) (γ t)
    else kmean γ y t

lemma kmean_succ_rev {γ y : ℕ → ℝ} {t : ℕ} (h : revP κ S₁ γ t) :
    kmean κ S₁ γ y (t + 1) = kmean κ S₁ γ y t +
      (y t - dotA (loadA (SigP κ S₁ γ t) (γ t)) (kmean κ S₁ γ y t)) •
        regK (SigP κ S₁ γ t) (γ t) := by
  simp only [kmean]; rw [ite_eq_left h]

lemma kmean_succ_pool {γ y : ℕ → ℝ} {t : ℕ} (h : ¬ revP κ S₁ γ t) :
    kmean κ S₁ γ y (t + 1) = kmean κ S₁ γ y t := by
  simp only [kmean]; rw [ite_eq_right h]

lemma obsF_rev {γ : ℕ → ℝ} {x : E2} {ε : ℕ → E2} {t : ℕ} (h : revP κ S₁ γ t) :
    obsF κ S₁ γ x ε t = dotA (loadA (SigP κ S₁ γ t) (γ t)) (x + ε t) := by
  simp only [obsF]; rw [ite_eq_left h]

lemma obsF_pool {γ : ℕ → ℝ} {x : E2} {ε : ℕ → E2} {t : ℕ} (h : ¬ revP κ S₁ γ t) :
    obsF κ S₁ γ x ε t = 0 := by
  simp only [obsF]; rw [ite_eq_right h]

/-- The Kalman mean depends only on `γ_0, …, γ_{t-1}` and `y_0, …, y_{t-1}`. -/
lemma kmean_congr {γ γ' y y' : ℕ → ℝ} {t : ℕ} (hγ : ∀ s < t, γ s = γ' s)
    (hy : ∀ s < t, y s = y' s) : kmean κ S₁ γ y t = kmean κ S₁ γ' y' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun s hs => hγ s (Nat.lt_succ_of_lt hs)) (fun s hs => hy s (Nat.lt_succ_of_lt hs))
    have hS : SigP κ S₁ γ t = SigP κ S₁ γ' t :=
      SigP_congr κ S₁ (fun s hs => hγ s (Nat.lt_succ_of_lt hs))
    have hr : revP κ S₁ γ t ↔ revP κ S₁ γ' t :=
      revP_congr κ S₁ (fun s hs => hγ s (Nat.lt_succ_of_le hs))
    by_cases h : revP κ S₁ γ t
    · rw [kmean_succ_rev κ S₁ h, kmean_succ_rev κ S₁ (hr.1 h), ih', hS, hγ t (Nat.lt_succ_self t),
        hy t (Nat.lt_succ_self t)]
    · rw [kmean_succ_pool κ S₁ h, kmean_succ_pool κ S₁ (fun h' => h (hr.2 h')), ih']

/-- Truncation of a sequence after `t` terms. -/
def trunc (t : ℕ) (y : ℕ → ℝ) : ℕ → ℝ := fun i => if i < t then y i else 0

/-- Truncation of a noise sequence after `t` terms. -/
noncomputable def truncE (t : ℕ) (ε : ℕ → E2) : ℕ → E2 := fun i => if i < t then ε i else 0

lemma measurable_trunc (t : ℕ) : Measurable (trunc t) := by
  refine Measurable.of_eval fun i => ?_
  unfold trunc
  by_cases h : i < t
  · simp only [h, ite_true]; exact measurable_pi_apply i
  · simp only [h, ite_false]; exact measurable_const

lemma measurable_truncE (t : ℕ) : Measurable (truncE t) := by
  refine Measurable.of_eval fun i => ?_
  unfold truncE
  by_cases h : i < t
  · simp only [h, ite_true]; exact measurable_pi_apply i
  · simp only [h, ite_false]; exact measurable_const

lemma kmean_trunc (γ y : ℕ → ℝ) (t : ℕ) : kmean κ S₁ γ (trunc t y) t = kmean κ S₁ γ y t :=
  kmean_congr κ S₁ (fun _ _ => rfl) (fun s hs => by simp [trunc, hs])

/-! ### Measurability -/

lemma measurable_kmean (t : ℕ) :
    Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => kmean κ S₁ p.1 p.2 t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hS : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => SigP κ S₁ p.1 t) :=
      (measurable_SigP κ S₁ t).comp measurable_fst
    have hg : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 t) :=
      (measurable_pi_apply t).comp measurable_fst
    have hy : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 t) :=
      (measurable_pi_apply t).comp measurable_snd
    have hrev : MeasurableSet {p : (ℕ → ℝ) × (ℕ → ℝ) | revP κ S₁ p.1 t} :=
      measurable_fst (measurableSet_revP κ S₁ t)
    have h0 := br_meas_loadA hS hg 0
    have h1 := br_meas_loadA hS hg 1
    have hm0 := br_meas_coord ih 0
    have hm1 := br_meas_coord ih 1
    have hK := br_meas_regK hS hg
    have h : (fun p : (ℕ → ℝ) × (ℕ → ℝ) => kmean κ S₁ p.1 p.2 (t + 1)) = fun p =>
        haveI := Classical.propDecidable (revP κ S₁ p.1 t)
        if revP κ S₁ p.1 t then
          kmean κ S₁ p.1 p.2 t + (p.2 t - dotA (loadA (SigP κ S₁ p.1 t) (p.1 t))
            (kmean κ S₁ p.1 p.2 t)) • regK (SigP κ S₁ p.1 t) (p.1 t)
        else kmean κ S₁ p.1 p.2 t := by
      funext p; rfl
    rw [h]
    classical
    refine Measurable.ite hrev (ih.add ((hy.sub ?_).smul hK)) ih
    simp only [dotA]
    exact (h0.mul hm0).add (h1.mul hm1)

lemma measurable_gam : Measurable gam := measurable_snd.comp measurable_snd

lemma measurable_gam_apply (i : ℕ) : Measurable (fun ω : Ωg => gam ω i) :=
  (measurable_pi_apply i).comp measurable_gam

lemma measurable_obs (t : ℕ) : Measurable (fun ω : Ωg => obs κ S₁ t ω) := by
  have hS : Measurable (fun ω : Ωg => SigP κ S₁ (gam ω) t) :=
    (measurable_SigP κ S₁ t).comp measurable_gam
  have hg := measurable_gam_apply t
  have hrev : MeasurableSet {ω : Ωg | revP κ S₁ (gam ω) t} :=
    measurable_gam (measurableSet_revP κ S₁ t)
  have h0 := br_meas_loadA hS hg 0
  have h1 := br_meas_loadA hS hg 1
  have hp : Measurable (fun ω : Ωg => ω.1 + ω.2.1 t) :=
    measurable_fst.add ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd))
  have hp0 := br_meas_coord hp 0
  have hp1 := br_meas_coord hp 1
  have h : (fun ω : Ωg => obs κ S₁ t ω) = fun ω =>
      haveI := Classical.propDecidable (revP κ S₁ (gam ω) t)
      if revP κ S₁ (gam ω) t then
        dotA (loadA (SigP κ S₁ (gam ω) t) (gam ω t)) (ω.1 + ω.2.1 t) else 0 := by
    funext ω; rfl
  rw [h]
  classical
  exact Measurable.ite hrev ((h0.mul hp0).add (h1.mul hp1)) measurable_const

lemma measurable_obsSeq : Measurable (fun ω : Ωg => fun s => obs κ S₁ s ω) :=
  Measurable.of_eval fun s => measurable_obs κ S₁ s

/-! ### The information filtration -/

lemma br_of_eval {α ι : Type*} {m : MeasurableSpace α} {f : α → ι → ℝ}
    (h : ∀ i, Measurable[m] (fun x => f x i)) : Measurable[m] f := by
  let := m; exact Measurable.of_eval h

/-- Extension by zero of a finite sequence. -/
def extF (n : ℕ) (g : Fin n → ℝ) : ℕ → ℝ := fun i => if h : i < n then g ⟨i, h⟩ else 0

lemma measurable_extF (n : ℕ) : Measurable (extF n) := by
  refine Measurable.of_eval fun i => ?_
  unfold extF
  by_cases h : i < n
  · simp only [h, dite_eq_left]; exact measurable_pi_apply _
  · simp only [h, dite_eq_right, not_false_eq_true]; exact measurable_const

lemma extF_apply_lt {n : ℕ} (g : Fin n → ℝ) {i : ℕ} (h : i < n) : extF n g i = g ⟨i, h⟩ := dite_eq_left h

/-- Every measurable function of `(γ_0, …, γ_t, obs_0, …, obs_{t-1})` is `infoSigma t`-measurable. -/
lemma meas_info_of_dep {β : Type*} [MeasurableSpace β] (t : ℕ)
    (F : (ℕ → ℝ) × (ℕ → ℝ) → β) (hF : Measurable F)
    (hdep : ∀ γ γ' y y' : ℕ → ℝ, (∀ i ≤ t, γ i = γ' i) → (∀ i < t, y i = y' i) →
      F (γ, y) = F (γ', y')) :
    Measurable[infoSigma κ S₁ t] (fun ω => F (gam ω, fun s => obs κ S₁ s ω)) := by
  have h : (fun ω => F (gam ω, fun s => obs κ S₁ s ω)) =
      (fun q : (Fin (t + 1) → ℝ) × (Fin t → ℝ) => F (extF (t + 1) q.1, extF t q.2)) ∘
        (fun ω => ((fun i : Fin (t + 1) => gam ω i), (fun i : Fin t => obs κ S₁ i ω))) := by
    funext ω
    simp only [Function.comp]
    apply hdep
    · intro i hi; rw [extF_apply_lt _ (Nat.lt_succ_of_le hi)]
    · intro i hi; rw [extF_apply_lt _ hi]
  rw [h]
  exact (hF.comp (((measurable_extF _).comp measurable_fst).prodMk
    ((measurable_extF _).comp measurable_snd))).comp (comap_measurable _)

lemma measSet_info_of_dep (t : ℕ) (p : (ℕ → ℝ) × (ℕ → ℝ) → Prop) (hp : MeasurableSet {q | p q})
    (hdep : ∀ γ γ' y y' : ℕ → ℝ, (∀ i ≤ t, γ i = γ' i) → (∀ i < t, y i = y' i) →
      (p (γ, y) ↔ p (γ', y'))) :
    MeasurableSet[infoSigma κ S₁ t] {ω | p (gam ω, fun s => obs κ S₁ s ω)} := by
  have h := meas_info_of_dep κ S₁ t p (measurableSet_setOfPred.1 hp)
    (fun γ γ' y y' h1 h2 => propext (hdep γ γ' y y' h1 h2))
  have e : {ω | p (gam ω, fun s => obs κ S₁ s ω)} =
      (fun ω => p (gam ω, fun s => obs κ S₁ s ω)) ⁻¹' {True} := by
    ext ω; simp
  rw [e]
  exact h (measurableSet_singleton _)

lemma meas_info_gam {t i : ℕ} (hi : i ≤ t) :
    Measurable[infoSigma κ S₁ t] (fun ω => gam ω i) :=
  meas_info_of_dep κ S₁ t (fun p => p.1 i) ((measurable_pi_apply i).comp measurable_fst)
    (fun _ _ _ _ h1 _ => h1 i hi)

lemma meas_info_obs {t i : ℕ} (hi : i < t) :
    Measurable[infoSigma κ S₁ t] (fun ω => obs κ S₁ i ω) :=
  meas_info_of_dep κ S₁ t (fun p => p.2 i) ((measurable_pi_apply i).comp measurable_snd)
    (fun _ _ _ _ _ h2 => h2 i hi)

lemma meas_info_Sig (t : ℕ) : Measurable[infoSigma κ S₁ t] (fun ω => SigP κ S₁ (gam ω) t) :=
  meas_info_of_dep κ S₁ t (fun p => SigP κ S₁ p.1 t) ((measurable_SigP κ S₁ t).comp measurable_fst)
    (fun _ _ _ _ h1 _ => SigP_congr κ S₁ (fun s hs => h1 s hs.le))

lemma measSet_info_rev (t : ℕ) : MeasurableSet[infoSigma κ S₁ t] {ω | revP κ S₁ (gam ω) t} :=
  measSet_info_of_dep κ S₁ t (fun p => revP κ S₁ p.1 t)
    (measurable_fst (measurableSet_revP κ S₁ t)) (fun _ _ _ _ h1 _ => revP_congr κ S₁ h1)

lemma meas_info_kmean (t : ℕ) :
    Measurable[infoSigma κ S₁ t] (fun ω => kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t) :=
  meas_info_of_dep κ S₁ t (fun p => kmean κ S₁ p.1 p.2 t) (measurable_kmean κ S₁ t)
    (fun _ _ _ _ h1 h2 => kmean_congr κ S₁ (fun s hs => h1 s hs.le) h2)

lemma infoSigma_le (t : ℕ) : infoSigma κ S₁ t ≤ (inferInstance : MeasurableSpace Ωg) :=
  Measurable.comap_le ((Measurable.of_eval fun (i : Fin (t + 1)) => measurable_gam_apply i).prodMk
    (Measurable.of_eval fun (i : Fin t) => measurable_obs κ S₁ i))

lemma infoSigma_mono : Monotone (infoSigma κ S₁) := by
  intro s t hst
  exact Measurable.comap_le ((br_of_eval fun (i : Fin (s + 1)) =>
    meas_info_gam κ S₁ (Nat.le_trans (Nat.lt_succ_iff.1 i.2) hst)).prodMk
    (br_of_eval fun (i : Fin s) => meas_info_obs κ S₁ (Nat.lt_of_lt_of_le i.2 hst)))

/-- The information filtration. -/
noncomputable def infoFilt : Filtration ℕ (inferInstance : MeasurableSpace Ωg) :=
  ⟨infoSigma κ S₁, infoSigma_mono κ S₁, infoSigma_le κ S₁⟩

lemma infoFilt_apply (t : ℕ) : infoFilt κ S₁ t = infoSigma κ S₁ t := rfl

/-- All the information `σ(γ, obs)`. -/
lemma iSup_infoSigma_le :
    (⨆ t, infoSigma κ S₁ t) ≤
      MeasurableSpace.comap (fun ω : Ωg => (gam ω, fun s => obs κ S₁ s ω)) inferInstance := by
  refine iSup_le fun t => Measurable.comap_le ?_
  have hR : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      ((fun i : Fin (t + 1) => p.1 i), (fun i : Fin t => p.2 i))) :=
    (Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst).prodMk
      (Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_snd)
  exact hR.comp (comap_measurable _)

end CC.Bridge
