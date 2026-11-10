import ConformityConcerns.BridgeK.Slots

/-!
# The Kalman filter along a fixed weight path, with disclosures

Fix the weight path `w`. Under `N(0, Σ₁) ⊗ N(0, I)^ℕ` (`Bridge.Qm`), the error `x - m_k` of the
Kalman mean before slot `k` is independent of the signals before `k` and has law `N(0, Cs k)`
(`kalman_fiberK`). Each slot is one Gaussian regression (`kstepG`).
-/

namespace CC.BridgeK

open MeasureTheory ProbabilityTheory Matrix

set_option warn.classDefReducibility false

variable (S₁ : M2) (D : Sched) (w : ℕ → ℝ × ℝ)

/-- The signals as a function of the state and the noises. -/
noncomputable def sigSeq (x : E2) (ξ : ℕ → E2) : ℕ → ℝ := fun k => sigF S₁ D w x ξ k

/-- The error of the Kalman mean before slot `k`. -/
noncomputable def errS (x : E2) (ξ : ℕ → E2) (k : ℕ) : E2 := x - km S₁ D w (sigSeq S₁ D w x ξ) k

/-- The signals before slot `k` (extended by zero). -/
noncomputable def YS (x : E2) (ξ : ℕ → E2) (k : ℕ) : ℕ → ℝ := Bridge.trunc k (sigSeq S₁ D w x ξ)

lemma measurable_sigF_fix (k : ℕ) :
    Measurable (fun p : E2 × (ℕ → E2) => sigF S₁ D w p.1 p.2 k) :=
  measurable_ZG.comp (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))

lemma measurable_sigSeq : Measurable (fun p : E2 × (ℕ → E2) => sigSeq S₁ D w p.1 p.2) :=
  Measurable.of_eval fun k => measurable_sigF_fix S₁ D w k

lemma measurable_errS (k : ℕ) : Measurable (fun p : E2 × (ℕ → E2) => errS S₁ D w p.1 p.2 k) :=
  measurable_fst.sub ((measurable_km_fix S₁ D w k).comp (measurable_sigSeq S₁ D w))

lemma measurable_YS (k : ℕ) : Measurable (fun p : E2 × (ℕ → E2) => YS S₁ D w p.1 p.2 k) :=
  (Bridge.measurable_trunc k).comp (measurable_sigSeq S₁ D w)

lemma sigF_truncE {x : E2} {ξ : ℕ → E2} {k j : ℕ} (hj : j < k) :
    sigF S₁ D w x (Bridge.truncE k ξ) j = sigF S₁ D w x ξ j := by
  simp [sigF, Bridge.truncE, hj]

lemma errS_truncE (x : E2) (ξ : ℕ → E2) (k : ℕ) :
    errS S₁ D w x (Bridge.truncE k ξ) k = errS S₁ D w x ξ k := by
  unfold errS
  congr 1
  exact km_congr S₁ D (fun _ _ => rfl) (fun j hj => sigF_truncE S₁ D w hj)

lemma YS_truncE (x : E2) (ξ : ℕ → E2) (k : ℕ) :
    YS S₁ D w x (Bridge.truncE k ξ) k = YS S₁ D w x ξ k := by
  funext i
  unfold YS Bridge.trunc
  split_ifs with h
  · exact sigF_truncE S₁ D w h
  · rfl

lemma km_YS (x : E2) (ξ : ℕ → E2) (k : ℕ) :
    km S₁ D w (YS S₁ D w x ξ k) k = km S₁ D w (sigSeq S₁ D w x ξ) k :=
  km_trunc S₁ D w _ k

/-- The signals up to slot `k` from the innovation at `k` and the signals before `k`. -/
noncomputable def GnextS (k : ℕ) (q : ℝ × (ℕ → ℝ)) : ℕ → ℝ := fun i =>
  if i < k then q.2 i else if i = k then
    q.1 + Bridge.dotA (ld S₁ D w k).1 (km S₁ D w q.2 k) else 0

lemma measurable_GnextS (k : ℕ) : Measurable (GnextS S₁ D w k) := by
  refine Measurable.of_eval fun i => ?_
  unfold GnextS
  by_cases h : i < k
  · simp only [h, ite_true]; exact (measurable_pi_apply i).comp measurable_snd
  · by_cases h' : i = k
    · simp only [h', lt_irrefl, ite_false, ite_true, Bridge.dotA]
      have hk : Measurable (fun q : ℝ × (ℕ → ℝ) => km S₁ D w q.2 k) :=
        (measurable_km_fix S₁ D w k).comp measurable_snd
      exact measurable_fst.add ((measurable_const.mul (Bridge.br_meas_coord hk 0)).add
        (measurable_const.mul (Bridge.br_meas_coord hk 1)))
    · simp only [h, h', ite_false]; exact measurable_const

/-- **The Kalman filter along a fixed weight path.** The error `x - m_k` is independent of the
signals before slot `k` and has law `N(0, Cs k)`. -/
theorem kalman_fiberK (hS₁ : S₁.PosSemidef) (hD : SchedOK D) (k : ℕ) :
    IndepFun (fun p : E2 × (ℕ → E2) => errS S₁ D w p.1 p.2 k)
        (fun p => YS S₁ D w p.1 p.2 k) (Bridge.Qm S₁) ∧
      (Bridge.Qm S₁).map (fun p : E2 × (ℕ → E2) => errS S₁ D w p.1 p.2 k) =
        multivariateGaussian 0 (Cs S₁ D w k) := by
  induction k with
  | zero =>
    have h1 : (fun p : E2 × (ℕ → E2) => errS S₁ D w p.1 p.2 0) = fun p => p.1 := by
      funext p; simp [errS, km]
    have h2 : (fun p : E2 × (ℕ → E2) => YS S₁ D w p.1 p.2 0) = fun _ => fun _ => 0 := by
      funext p i; simp [YS, Bridge.trunc]
    have h3 : Cs S₁ D w 0 = S₁ := by
      have h := Cs_even S₁ D w 0
      rw [mul_zero] at h
      rw [h]; rfl
    rw [h1, h2, h3]
    exact ⟨indepFun_const_right _ _, Bridge.law_state S₁⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set S := Cs S₁ D w k with hSdef
    set a := (ld S₁ D w k).1 with hadef
    set b := (ld S₁ D w k).2 with hbdef
    have hpsd : S.PosSemidef := Cs_psd S₁ D hD hS₁ w k
    have he := measurable_errS S₁ D w k
    have hY := measurable_YS S₁ D w k
    have hξ : Measurable (fun p : E2 × (ℕ → E2) => p.2 k) :=
      (measurable_pi_apply k).comp measurable_snd
    have h1 : IndepFun (fun p : E2 × (ℕ → E2) => (errS S₁ D w p.1 p.2 k, YS S₁ D w p.1 p.2 k))
        (fun p => p.2 k) (Bridge.Qm S₁) := by
      have := (Bridge.indep_past_noise S₁ k).comp
        (φ := fun q : E2 × (ℕ → E2) => (errS S₁ D w q.1 q.2 k, YS S₁ D w q.1 q.2 k))
        (ψ := id) (he.prodMk hY) measurable_id
      have e : (fun p : E2 × (ℕ → E2) => (errS S₁ D w p.1 p.2 k, YS S₁ D w p.1 p.2 k)) =
          (fun q : E2 × (ℕ → E2) => (errS S₁ D w q.1 q.2 k, YS S₁ D w q.1 q.2 k)) ∘
            (fun p : E2 × (ℕ → E2) => (p.1, Bridge.truncE k p.2)) := by
        funext p
        simp only [Function.comp, errS_truncE, YS_truncE]
      rw [e]
      exact this
    obtain ⟨K1, K2⟩ := kstepG hpsd a b he hξ hY h1 ih1 ih2 (Bridge.law_noise S₁ k)
    have eE : (fun p : E2 × (ℕ → E2) => errS S₁ D w p.1 p.2 (k + 1)) =
        fun p => resG S a b (errS S₁ D w p.1 p.2 k, p.2 k) := by
      funext p
      ext j
      simp only [errS, km, resG, ZG, sigSeq, sigF, Bridge.dotA, PiLp.sub_apply, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul, ← hSdef, ← hadef, ← hbdef]
      ring
    have eY : (fun p : E2 × (ℕ → E2) => YS S₁ D w p.1 p.2 (k + 1)) =
        fun p => GnextS S₁ D w k (ZG a b (errS S₁ D w p.1 p.2 k, p.2 k),
          YS S₁ D w p.1 p.2 k) := by
      funext p i
      simp only [GnextS, YS]
      rw [km_trunc]
      simp only [Bridge.trunc]
      by_cases h : i < k
      · simp [h, Nat.lt_succ_of_lt h]
      · by_cases h' : i = k
        · subst h'
          simp only [lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
          simp only [sigSeq, sigF, ZG, errS, Bridge.dotA, PiLp.sub_apply, ← hadef, ← hbdef]
          ring
        · have h'' : ¬ i < k + 1 := by omega
          simp [h, h', h'']
    rw [eE, eY, Cs_succ S₁ D hD]
    exact ⟨K1.comp (φ := id) (ψ := GnextS S₁ D w k) measurable_id (measurable_GnextS S₁ D w k),
      K2⟩

end CC.BridgeK
