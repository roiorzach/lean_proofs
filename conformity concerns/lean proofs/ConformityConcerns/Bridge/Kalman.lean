import ConformityConcerns.Bridge.IndepTools

/-!
# The Kalman filter along a fixed weight path

Fix the weight path `γ`. Under `N(0, Σ₁) ⊗ N(0, I)^ℕ`, the error `x - m_t` of the Kalman mean is
independent of the observations before `t` and has law `N(0, Σ_t)` (`kalman_fiber`). The step is
one Gaussian regression (`indep_resZ`, `law_resZ` in `Gaussian/Conditioning.lean`).
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix

set_option warn.classDefReducibility false

lemma measurable_Zof (S : M2) (γ : ℝ) : Measurable (Zof 0 S γ) := by
  unfold Zof privInfo; fun_prop

lemma measurable_resZ (S : M2) (γ : ℝ) : Measurable (resZ 0 S γ) := by
  unfold resZ regC Zof privInfo; fun_prop

lemma Zof_zero (S : M2) (γ : ℝ) (ω : E2 × E2) :
    Zof 0 S γ ω = dotA (loadA S γ) (ω.1 + ω.2) := by
  simp [Zof, privInfo, dotA, loadA]; ring

lemma resZ_zero (S : M2) (γ : ℝ) (ω : E2 × E2) :
    resZ 0 S γ ω = ω.1 - Zof 0 S γ ω • regK S γ := by
  simp [resZ, regC]

/-- One step of the filter: if `(e, Y) ⟂ ξ`, `e ⟂ Y`, `e ~ N(0, Σ)` and `ξ ~ N(0, I)`, then the
residual of the regression of `e` on the innovation `Z` is independent of `(Z, Y)` and has law
`N(0, kalman Σ γ)`. -/
lemma kstep {Ω 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : M2} (hS : S.PosSemidef) (γ : ℝ) {e ξ : Ω → E2} {Y : Ω → 𝒴}
    (he : Measurable e) (hξ : Measurable ξ) (hY : Measurable Y)
    (h1 : IndepFun (fun ω => (e ω, Y ω)) ξ P) (h2 : IndepFun e Y P)
    (hle : P.map e = multivariateGaussian 0 S) (hlξ : P.map ξ = stdGaussian E2) :
    IndepFun (fun ω => resZ 0 S γ (e ω, ξ ω)) (fun ω => (Zof 0 S γ (e ω, ξ ω), Y ω)) P ∧
      P.map (fun ω => resZ 0 S γ (e ω, ξ ω)) = multivariateGaussian 0 (kalman S γ) := by
  have heξ : IndepFun e ξ P := h1.comp (φ := Prod.fst) (ψ := id) measurable_fst measurable_id
  have hlaw : P.map (fun ω => (e ω, ξ ω)) = periodLaw 0 S := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map he.aemeasurable hξ.aemeasurable).1 heξ, hle, hlξ]
    rfl
  have hR := measurable_resZ S γ
  have hZ := measurable_Zof S γ
  have hp : Measurable (fun ω => (e ω, ξ ω)) := he.prodMk hξ
  have hind1 : IndepFun (fun ω => resZ 0 S γ (e ω, ξ ω)) (fun ω => Zof 0 S γ (e ω, ξ ω)) P :=
    br_indep_of_map hp hR hZ (by rw [hlaw]; exact indep_resZ hS γ)
  have hind2 : IndepFun (fun ω => (e ω, ξ ω)) Y P := br_indep_regroup he hY hξ h1 h2
  have hind3 : IndepFun (fun ω => (resZ 0 S γ (e ω, ξ ω), Zof 0 S γ (e ω, ξ ω))) Y P :=
    hind2.comp (φ := fun p => (resZ 0 S γ p, Zof 0 S γ p)) (ψ := id) (hR.prodMk hZ) measurable_id
  refine ⟨br_indep_assoc (hR.comp hp) (hZ.comp hp) hY hind3 hind1, ?_⟩
  have : (fun ω => resZ 0 S γ (e ω, ξ ω)) = resZ 0 S γ ∘ (fun ω => (e ω, ξ ω)) := rfl
  rw [this, ← Measure.map_map hR hp, hlaw, law_resZ hS γ]

variable (κ : ℝ) (S₁ : M2)

/-- The error of the Kalman mean along the weight path `γ`. -/
noncomputable def errF (γ : ℕ → ℝ) (x : E2) (ε : ℕ → E2) (t : ℕ) : E2 :=
  x - kmean κ S₁ γ (obsF κ S₁ γ x ε) t

/-- The observations before `t` (extended by zero). -/
noncomputable def Ytr (γ : ℕ → ℝ) (x : E2) (ε : ℕ → E2) (t : ℕ) : ℕ → ℝ :=
  trunc t (obsF κ S₁ γ x ε)

variable (γ : ℕ → ℝ)

lemma measurable_obsF_fix (s : ℕ) :
    Measurable (fun p : E2 × (ℕ → E2) => obsF κ S₁ γ p.1 p.2 s) := by
  by_cases h : revP κ S₁ γ s
  · simp only [obsF, h, ite_true, dotA]
    have hp : Measurable (fun p : E2 × (ℕ → E2) => p.1 + p.2 s) :=
      measurable_fst.add ((measurable_pi_apply s).comp measurable_snd)
    exact (measurable_const.mul (br_meas_coord hp 0)).add
      (measurable_const.mul (br_meas_coord hp 1))
  · simp only [obsF, h, ite_false]; exact measurable_const

lemma measurable_obsSeqF_fix :
    Measurable (fun p : E2 × (ℕ → E2) => obsF κ S₁ γ p.1 p.2) :=
  Measurable.of_eval fun s => measurable_obsF_fix κ S₁ γ s

lemma measurable_kmean_fix (t : ℕ) : Measurable (fun y : ℕ → ℝ => kmean κ S₁ γ y t) :=
  (measurable_kmean κ S₁ t).comp (measurable_const.prodMk measurable_id)

lemma measurable_errF (t : ℕ) : Measurable (fun p : E2 × (ℕ → E2) => errF κ S₁ γ p.1 p.2 t) :=
  measurable_fst.sub ((measurable_kmean_fix κ S₁ γ t).comp (measurable_obsSeqF_fix κ S₁ γ))

lemma measurable_Ytr (t : ℕ) : Measurable (fun p : E2 × (ℕ → E2) => Ytr κ S₁ γ p.1 p.2 t) :=
  (measurable_trunc t).comp (measurable_obsSeqF_fix κ S₁ γ)

lemma obsF_truncE {x : E2} {ε : ℕ → E2} {t s : ℕ} (hs : s < t) :
    obsF κ S₁ γ x (truncE t ε) s = obsF κ S₁ γ x ε s := by
  simp [obsF, truncE, hs]

lemma errF_truncE (x : E2) (ε : ℕ → E2) (t : ℕ) :
    errF κ S₁ γ x (truncE t ε) t = errF κ S₁ γ x ε t := by
  unfold errF
  rw [kmean_congr κ S₁ (fun _ _ => rfl) (fun s hs => obsF_truncE κ S₁ γ hs)]

lemma Ytr_truncE (x : E2) (ε : ℕ → E2) (t : ℕ) :
    Ytr κ S₁ γ x (truncE t ε) t = Ytr κ S₁ γ x ε t := by
  funext i
  unfold Ytr trunc
  split_ifs with h
  · exact obsF_truncE κ S₁ γ h
  · rfl

lemma kmean_Ytr (x : E2) (ε : ℕ → E2) (t : ℕ) :
    kmean κ S₁ γ (Ytr κ S₁ γ x ε t) t = kmean κ S₁ γ (obsF κ S₁ γ x ε) t :=
  kmean_trunc κ S₁ γ _ t

/-- The observations up to `t` from the innovation at `t` and the observations before `t`. -/
noncomputable def Gnext (t : ℕ) (q : ℝ × (ℕ → ℝ)) : ℕ → ℝ := fun i =>
  if i < t then q.2 i else if i = t then
    q.1 + dotA (loadA (SigP κ S₁ γ t) (γ t)) (kmean κ S₁ γ q.2 t) else 0

lemma measurable_Gnext (t : ℕ) : Measurable (Gnext κ S₁ γ t) := by
  refine Measurable.of_eval fun i => ?_
  unfold Gnext
  by_cases h : i < t
  · simp only [h, ite_true]; exact (measurable_pi_apply i).comp measurable_snd
  · by_cases h' : i = t
    · simp only [h', lt_irrefl, ite_false, ite_true, dotA]
      have hk : Measurable (fun q : ℝ × (ℕ → ℝ) => kmean κ S₁ γ q.2 t) :=
        (measurable_kmean_fix κ S₁ γ t).comp measurable_snd
      exact measurable_fst.add ((measurable_const.mul (br_meas_coord hk 0)).add
        (measurable_const.mul (br_meas_coord hk 1)))
    · simp only [h, h', ite_false]; exact measurable_const

/-- **The Kalman filter along a fixed weight path.** The error `x - m_t` is independent of the
observations before `t` and has law `N(0, Σ_t)`. -/
theorem kalman_fiber (hS₁ : S₁.PosSemidef) (t : ℕ) :
    IndepFun (fun p : E2 × (ℕ → E2) => errF κ S₁ γ p.1 p.2 t)
        (fun p => Ytr κ S₁ γ p.1 p.2 t) (Qm S₁) ∧
      (Qm S₁).map (fun p : E2 × (ℕ → E2) => errF κ S₁ γ p.1 p.2 t) =
        multivariateGaussian 0 (SigP κ S₁ γ t) := by
  induction t with
  | zero =>
    have h1 : (fun p : E2 × (ℕ → E2) => errF κ S₁ γ p.1 p.2 0) = fun p => p.1 := by
      funext p; simp [errF, kmean]
    have h2 : (fun p : E2 × (ℕ → E2) => Ytr κ S₁ γ p.1 p.2 0) = fun _ => fun _ => 0 := by
      funext p i; simp [Ytr, trunc]
    rw [h1, h2]
    exact ⟨indepFun_const_right _ _, law_state S₁⟩
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set S := SigP κ S₁ γ t with hSdef
    have hpsd : S.PosSemidef := SigmaC_psd' (fun _ => κ) γ S₁ hS₁ t
    have he := measurable_errF κ S₁ γ t
    have hY := measurable_Ytr κ S₁ γ t
    have hξ : Measurable (fun p : E2 × (ℕ → E2) => p.2 t) :=
      (measurable_pi_apply t).comp measurable_snd
    have h1 : IndepFun (fun p : E2 × (ℕ → E2) => (errF κ S₁ γ p.1 p.2 t, Ytr κ S₁ γ p.1 p.2 t))
        (fun p => p.2 t) (Qm S₁) := by
      have := (indep_past_noise S₁ t).comp
        (φ := fun q : E2 × (ℕ → E2) => (errF κ S₁ γ q.1 q.2 t, Ytr κ S₁ γ q.1 q.2 t))
        (ψ := id) ((measurable_errF κ S₁ γ t).prodMk (measurable_Ytr κ S₁ γ t)) measurable_id
      have e : (fun p : E2 × (ℕ → E2) => (errF κ S₁ γ p.1 p.2 t, Ytr κ S₁ γ p.1 p.2 t)) =
          (fun q : E2 × (ℕ → E2) => (errF κ S₁ γ q.1 q.2 t, Ytr κ S₁ γ q.1 q.2 t)) ∘
            (fun p : E2 × (ℕ → E2) => (p.1, truncE t p.2)) := by
        funext p
        simp only [Function.comp, errF_truncE, Ytr_truncE]
      rw [e]
      exact this
    obtain ⟨K1, K2⟩ := kstep hpsd (γ t) he hξ hY h1 ih1 ih2 (law_noise S₁ t)
    by_cases hr : revP κ S₁ γ t
    · have eE : (fun p : E2 × (ℕ → E2) => errF κ S₁ γ p.1 p.2 (t + 1)) =
          fun p => resZ 0 S (γ t) (errF κ S₁ γ p.1 p.2 t, p.2 t) := by
        funext p
        rw [resZ_zero, Zof_zero]
        simp only [errF]
        rw [kmean_succ_rev κ S₁ hr, obsF_rev κ S₁ hr]
        rw [← hSdef]
        ext i
        simp [dotA]
        ring
      have eY : (fun p : E2 × (ℕ → E2) => Ytr κ S₁ γ p.1 p.2 (t + 1)) =
          fun p => Gnext κ S₁ γ t (Zof 0 S (γ t) (errF κ S₁ γ p.1 p.2 t, p.2 t),
            Ytr κ S₁ γ p.1 p.2 t) := by
        funext p i
        simp only [Gnext, Ytr]
        rw [kmean_trunc]
        simp only [trunc]
        by_cases h : i < t
        · simp [h, Nat.lt_succ_of_lt h]
        · by_cases h' : i = t
          · subst h'
            simp only [lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
            rw [obsF_rev κ S₁ hr, Zof_zero, ← hSdef]
            simp only [errF, dotA]
            simp
            ring
          · have h'' : ¬ i < t + 1 := by omega
            simp [h, h', h'']
      have hS' : SigP κ S₁ γ (t + 1) = kalman S (γ t) := SigmaC_succ_rev (fun _ => κ) γ S₁ hr
      rw [eE, eY, hS']
      exact ⟨K1.comp (φ := id) (ψ := Gnext κ S₁ γ t) measurable_id (measurable_Gnext κ S₁ γ t),
        K2⟩
    · have eE : (fun p : E2 × (ℕ → E2) => errF κ S₁ γ p.1 p.2 (t + 1)) =
          fun p => errF κ S₁ γ p.1 p.2 t := by
        funext p
        simp only [errF]
        rw [kmean_succ_pool κ S₁ hr]
      have eY : (fun p : E2 × (ℕ → E2) => Ytr κ S₁ γ p.1 p.2 (t + 1)) =
          fun p => Ytr κ S₁ γ p.1 p.2 t := by
        funext p i
        simp only [Ytr, trunc]
        by_cases h : i < t
        · simp [h, Nat.lt_succ_of_lt h]
        · by_cases h' : i = t
          · subst h'
            simp [obsF_pool κ S₁ hr]
          · have h'' : ¬ i < t + 1 := by omega
            simp [h, h'']
      rw [eE, eY]
      have hS' : SigP κ S₁ γ (t + 1) = SigP κ S₁ γ t := SigmaC_succ_pool (fun _ => κ) γ S₁ hr
      rw [hS']
      exact ⟨ih1, ih2⟩

end CC.Bridge
