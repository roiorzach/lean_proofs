import ConformityConcerns.LearnTheta.Defs
import ConformityConcerns.LearnTheta.Claim
import Mathlib.Probability.Independence.InfinitePi

/-!
# Proposition A5 across histories: properties of the model

* The history process is measurable and generates a filtration.
* The model satisfies the hypotheses of the Claim (`claimSetup`).
* Revelation: when the period strategy is monotone, on `RevUp` (resp. `RevDown`) the decision
  reveals whether `ṽ_t > d` (resp. `ṽ_t < d`).
* The kernels `beliefY` and `typeLaw` represent conditional expectations given `h^t`, and the
  conditional law of `ṽ_t` is the convolution of that of `Y_t` with the law of `v_t`.
-/

namespace CC.LearnTheta

open MeasureTheory ProbabilityTheory Filter Topology

section Aux

/-! ### Auxiliary measurability facts -/

lemma measurable_snoc_aux {α : Type*} {mα : MeasurableSpace α} {n : ℕ} {f : α → Fin n → ℝ}
    {g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => (Fin.snoc (f a) (g a) : Fin (n + 1) → ℝ)) := by
  refine measurable_pi_iff.2 fun i => ?_
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact hg
  | cast j => simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp hf

lemma measurable_pi_of {α ι : Type*} {mα : MeasurableSpace α} {g : α → ι → ℝ}
    (h : ∀ i, Measurable fun x => g x i) : Measurable g :=
  measurable_pi_iff.2 h

lemma measurable_fin_init {n : ℕ} :
    Measurable (fun h : Fin (n + 1) → ℝ => (Fin.init h : Fin n → ℝ)) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

lemma measurable_coord_fin {n i : ℕ} (hi : i < n) :
    Measurable[MeasurableSpace.comap (fun (ω : Ω) (j : Fin n) => ω j) inferInstance]
      (fun ω : Ω => ω i) := by
  have h : Measurable (fun f : Fin n → ℝ => f ⟨i, hi⟩) := measurable_pi_apply _
  exact h.comp (comap_measurable (fun (ω : Ω) (j : Fin n) => ω j))

lemma comap_fin_mono {m n : ℕ} (h : m ≤ n) :
    MeasurableSpace.comap (fun (ω : Ω) (j : Fin m) => ω j) inferInstance ≤
      MeasurableSpace.comap (fun (ω : Ω) (j : Fin n) => ω j) inferInstance :=
  Measurable.comap_le (measurable_pi_of fun j => measurable_coord_fin (lt_of_lt_of_le j.isLt h))

lemma pastSigma_le (t : ℕ) : pastSigma t ≤ (inferInstance : MeasurableSpace Ω) :=
  Measurable.comap_le (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

lemma pastSigma_mono {s t : ℕ} (h : s ≤ t) : pastSigma s ≤ pastSigma t :=
  comap_fin_mono (by omega)

lemma measurable_coord_past {t i : ℕ} (hi : i < 2 * t + 1) :
    Measurable[pastSigma t] (fun ω : Ω => ω i) :=
  measurable_coord_fin hi

lemma measurable_thetaV_add_epsV (t : ℕ) : Measurable (fun ω => thetaV ω + epsV t ω) :=
  (measurable_pi_apply 0).add (measurable_pi_apply (2 * t + 1))

lemma measurable_c_apply (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ)
    (x : ℝ) : Measurable (fun h : Fin t → ℝ => c t h x) :=
  (hc t).comp (measurable_id.prodMk measurable_const)

end Aux

section Hist

variable (P : Measure Ω) (c : Profile)

lemma hist_succ_eq (t : ℕ) :
    hist P c (t + 1) = fun ω => Fin.snoc (hist P c t ω) (act P c t ω) :=
  funext (hist_succ P c t)

lemma hist_eq_init (t : ℕ) (ω : Ω) : Fin.init (hist P c (t + 1) ω) = hist P c t ω := by
  rw [hist_succ, Fin.init_snoc]

lemma hist_last (t : ℕ) (ω : Ω) : hist P c (t + 1) ω (Fin.last t) = act P c t ω := by
  rw [hist_succ, Fin.snoc_last]

lemma measurable_hist (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ) :
    Measurable (hist P c t) := by
  induction t with
  | zero => exact measurable_pi_iff.2 fun i => i.elim0
  | succ t ih =>
    have hY : Measurable (Ycond P c t) :=
      stronglyMeasurable_condExp.measurable.mono
        (sup_le ih.comap_le (measurable_thetaV_add_epsV t).comap_le) le_rfl
    have hv : Measurable (vtil P c t) := (measurable_pi_apply _).add hY
    rw [hist_succ_eq]
    exact measurable_snoc_aux ih ((hc t).comp (ih.prodMk hv))

lemma histSigma_le (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ) :
    histSigma P c t ≤ (inferInstance : MeasurableSpace Ω) := by
  exact (measurable_hist P c hc t).comap_le

lemma histSigma_mono (t : ℕ) : histSigma P c t ≤ histSigma P c (t + 1) := by
  have h : Measurable[histSigma P c (t + 1)] (hist P c t) := by
    have e : hist P c t = fun ω => Fin.init (hist P c (t + 1) ω) :=
      funext fun ω => (hist_eq_init P c t ω).symm
    rw [e]
    exact measurable_fin_init.comp (comap_measurable _)
  exact h.comap_le

/-- The public-history filtration. -/
noncomputable def histFilt (hc : ∀ t, Measurable (Function.uncurry (c t))) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq := histSigma P c
  mono' := monotone_nat_of_le_succ (histSigma_mono P c)
  le' := histSigma_le P c hc

lemma histFilt_apply (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ) :
    histFilt P c hc t = histSigma P c t := rfl

lemma measurable_Ycond (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ) :
    Measurable (Ycond P c t) :=
  stronglyMeasurable_condExp.measurable.mono
    (sup_le (histSigma_le P c hc t) (measurable_thetaV_add_epsV t).comap_le) le_rfl

/-- The history `h^t` is a function of `θ` and the shocks of the periods before `t`. -/
lemma measurable_hist_past (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ) :
    Measurable[pastSigma t] (hist P c t) := by
  induction t with
  | zero => exact measurable_pi_of fun i => i.elim0
  | succ t ih =>
    have ih' : Measurable[pastSigma (t + 1)] (hist P c t) :=
      ih.mono (pastSigma_mono (Nat.le_succ t)) le_rfl
    have hs : Measurable[pastSigma (t + 1)] (fun ω => thetaV ω + epsV t ω) :=
      (measurable_coord_past (by omega : 0 < 2 * (t + 1) + 1)).add
        (measurable_coord_past (by omega : 2 * t + 1 < 2 * (t + 1) + 1))
    have hY : Measurable[pastSigma (t + 1)] (Ycond P c t) :=
      stronglyMeasurable_condExp.measurable.mono (sup_le ih'.comap_le hs.comap_le) le_rfl
    have hv : Measurable[pastSigma (t + 1)] (vtil P c t) :=
      (measurable_coord_past (by omega : 2 * t + 2 < 2 * (t + 1) + 1)).add hY
    rw [hist_succ_eq]
    exact measurable_snoc_aux ih' ((hc t).comp (ih'.prodMk hv))

lemma histSigma_le_pastSigma (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ) :
    histSigma P c t ≤ pastSigma t :=
  (measurable_hist_past P c hc t).comap_le

/-- `(h^t, Y_t)` is a function of `θ`, the shocks before `t` and `ε_t`. -/
lemma measurable_hist_Ycond_past (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ) :
    Measurable[pastSigma t ⊔ MeasurableSpace.comap (epsV t) inferInstance]
      (fun ω => (hist P c t ω, Ycond P c t ω)) := by
  have h1 : Measurable[pastSigma t ⊔ MeasurableSpace.comap (epsV t) inferInstance]
      (hist P c t) := (measurable_hist_past P c hc t).mono le_sup_left le_rfl
  have h2 : Measurable[pastSigma t ⊔ MeasurableSpace.comap (epsV t) inferInstance]
      (fun ω => thetaV ω + epsV t ω) :=
    ((measurable_coord_past (by omega : 0 < 2 * t + 1)).mono le_sup_left le_rfl).add
      ((comap_measurable (epsV t)).mono le_sup_right le_rfl)
  have h3 : Measurable[pastSigma t ⊔ MeasurableSpace.comap (epsV t) inferInstance]
      (Ycond P c t) :=
    stronglyMeasurable_condExp.measurable.mono (sup_le h1.comap_le h2.comap_le) le_rfl
  exact h1.prodMk h3

end Hist

section Coords

/-! ### The coordinates of the sample space -/

variable (Lθ Lε G : Measure ℝ) [IsProbabilityMeasure Lθ] [IsProbabilityMeasure Lε]
  [IsProbabilityMeasure G]

lemma map_coord (i : ℕ) : (law Lθ Lε G).map (fun ω : Ω => ω i) = lawSeq Lθ Lε G i :=
  Measure.infinitePi_map_eval _ i

lemma iIndepFun_coords : iIndepFun (fun i (ω : Ω) => ω i) (law Lθ Lε G) :=
  iIndepFun_infinitePi (P := lawSeq Lθ Lε G) (X := fun _ x => x) (fun _ => measurable_id)

/-- Coordinate `n` is independent of the coordinates `0, …, n-1`. -/
lemma indep_coord_fin (n : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : Ω => ω n) inferInstance)
      (MeasurableSpace.comap (fun (ω : Ω) (j : Fin n) => ω j) inferInstance) (law Lθ Lε G) := by
  have h := (iIndepFun_coords Lθ Lε G).indepFun_finset {n} (Finset.range n) (by simp)
    (fun i => measurable_pi_apply i)
  rw [IndepFun_iff_Indep] at h
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · have h1 : Measurable (fun f : ({n} : Finset ℕ) → ℝ => f ⟨n, Finset.mem_singleton_self n⟩) :=
      measurable_pi_apply _
    exact Measurable.comap_le
      (h1.comp (comap_measurable (fun (ω : Ω) (i : ({n} : Finset ℕ)) => ω i)))
  · refine Measurable.comap_le (measurable_pi_of fun j => ?_)
    have h1 : Measurable (fun f : (Finset.range n) → ℝ => f ⟨j, Finset.mem_range.2 j.isLt⟩) :=
      measurable_pi_apply _
    exact h1.comp (comap_measurable (fun (ω : Ω) (i : Finset.range n) => ω i))

lemma indep_eps (t : ℕ) :
    Indep (MeasurableSpace.comap (epsV t) inferInstance) (pastSigma t) (law Lθ Lε G) :=
  indep_coord_fin Lθ Lε G (2 * t + 1)

lemma indep_v (t : ℕ) :
    Indep (MeasurableSpace.comap (vV t) inferInstance)
      (pastSigma t ⊔ MeasurableSpace.comap (epsV t) inferInstance) (law Lθ Lε G) :=
  indep_of_indep_of_le_right (indep_coord_fin Lθ Lε G (2 * t + 2))
    (sup_le (comap_fin_mono (by omega))
      (measurable_coord_fin (by omega : 2 * t + 1 < 2 * t + 2)).comap_le)

lemma map_thetaV : (law Lθ Lε G).map thetaV = Lθ := by
  rw [show thetaV = fun ω : Ω => ω 0 from rfl, map_coord]
  simp [lawSeq]

lemma map_epsV (t : ℕ) : (law Lθ Lε G).map (epsV t) = Lε := by
  rw [show epsV t = fun ω : Ω => ω (2 * t + 1) from rfl, map_coord]
  have h1 : 2 * t + 1 ≠ 0 := by omega
  have h2 : (2 * t + 1) % 2 = 1 := by omega
  simp only [lawSeq, h1, h2, ↓reduceIte]

lemma map_vV (t : ℕ) : (law Lθ Lε G).map (vV t) = G := by
  rw [show vV t = fun ω : Ω => ω (2 * t + 2) from rfl, map_coord]
  have h1 : 2 * t + 2 ≠ 0 := by omega
  have h2 : ¬ (2 * t + 2) % 2 = 1 := by omega
  simp only [lawSeq, h1, h2, ↓reduceIte]

lemma memLp_thetaV (hθ : Integrable (fun x => x ^ 2) Lθ) :
    MemLp thetaV 2 (law Lθ Lε G) := by
  have h2 : MemLp id 2 ((law Lθ Lε G).map thetaV) := by
    rw [map_thetaV]
    exact (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 hθ
  exact h2.comp_of_map (measurable_pi_apply 0).aemeasurable

end Coords

section Setup

variable (Lθ Lε : Measure ℝ) (ψ : ℝ → ℝ) [IsProbabilityMeasure Lθ] [IsProbabilityMeasure Lε]
  [IsProbabilityMeasure (vLaw ψ)]

/-- The model satisfies the hypotheses of the Claim. -/
noncomputable def claimSetup (hθ : Integrable (fun x => x ^ 2) Lθ) (hψc : Continuous ψ)
    (hψpos : ∀ x, 0 < ψ x) (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t))) :
    ClaimSetup (law Lθ Lε (vLaw ψ)) where
  ℱ := histFilt (law Lθ Lε (vLaw ψ)) c hc
  𝒜 := pastSigma
  θ := thetaV
  ε := epsV
  v := vV
  Lε := Lε
  ψ := ψ
  A_le := pastSigma_le
  F_le_A := histSigma_le_pastSigma (law Lθ Lε (vLaw ψ)) c hc
  θ_meas := fun t => measurable_coord_past (by omega : 0 < 2 * t + 1)
  θ_sq := memLp_thetaV Lθ Lε (vLaw ψ) hθ
  ε_meas := fun t => measurable_pi_apply _
  v_meas := fun t => measurable_pi_apply _
  ε_indep := indep_eps Lθ Lε (vLaw ψ)
  v_indep := indep_v Lθ Lε (vLaw ψ)
  ε_law := map_epsV Lθ Lε (vLaw ψ)
  v_law := map_vV Lθ Lε (vLaw ψ)
  ψ_cont := hψc
  ψ_pos := hψpos

variable (hθ : Integrable (fun x => x ^ 2) Lθ) (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x)
  (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))

lemma claimSetup_ℱ (t : ℕ) :
    (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).ℱ t = histSigma (law Lθ Lε (vLaw ψ)) c t := rfl

lemma claimSetup_θ : (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).θ = thetaV := rfl

lemma claimSetup_Y (t : ℕ) :
    (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).Y t = Ycond (law Lθ Lε (vLaw ψ)) c t := rfl

lemma claimSetup_vt (t : ℕ) :
    (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).vt t = vtil (law Lθ Lε (vLaw ψ)) c t := rfl

lemma claimSetup_post (t : ℕ) :
    (claimSetup Lθ Lε ψ hθ hψc hψpos c hc).post t =
      (law Lθ Lε (vLaw ψ))[thetaV | histSigma (law Lθ Lε (vLaw ψ)) c t] := rfl

end Setup

section RevealAux

lemma measurableSet_revUpSet (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (t : ℕ) (d : ℝ) :
    MeasurableSet {h : Fin t → ℝ | ∀ q : ℚ, d < (q : ℝ) → c t h d < c t h q} := by
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : d < (q : ℝ)
  · simp only [hq, true_implies]
    exact measurableSet_lt (measurable_c_apply c hc t d) (measurable_c_apply c hc t q)
  · simp only [hq, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

lemma measurableSet_revDownSet (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (t : ℕ) (d : ℝ) :
    MeasurableSet {h : Fin t → ℝ | ∀ q : ℚ, (q : ℝ) < d → c t h q < c t h d} := by
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : (q : ℝ) < d
  · simp only [hq, true_implies]
    exact measurableSet_lt (measurable_c_apply c hc t q) (measurable_c_apply c hc t d)
  · simp only [hq, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

end RevealAux

section Reveal

variable (P : Measure Ω) (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))

include hc in
lemma measurableSet_revUp (t : ℕ) (d : ℝ) : MeasurableSet[histSigma P c t] (RevUp P c t d) := by
  exact comap_measurable (hist P c t) (measurableSet_revUpSet c hc t d)

include hc in
lemma measurableSet_revDown (t : ℕ) (d : ℝ) :
    MeasurableSet[histSigma P c t] (RevDown P c t d) := by
  exact comap_measurable (hist P c t) (measurableSet_revDownSet c hc t d)

include hc in
/-- On `RevUp`, a monotone period strategy reveals whether `ṽ_t > d`. -/
lemma reveal_up (t : ℕ) (d : ℝ) (hmono : ∀ᵐ ω ∂P, Monotone (c t (hist P c t ω))) :
    ∃ A : Set Ω, MeasurableSet[histSigma P c (t + 1)] A ∧
      A =ᵐ[P] ({ω | d < vtil P c t ω} ∩ RevUp P c t d) := by
  have hS : MeasurableSet ({h' : Fin (t + 1) → ℝ | c t (Fin.init h') d < h' (Fin.last t)} ∩
      {h' | ∀ q : ℚ, d < (q : ℝ) → c t (Fin.init h') d < c t (Fin.init h') q}) :=
    (measurableSet_lt ((measurable_c_apply c hc t d).comp measurable_fin_init)
      (measurable_pi_apply _)).inter
      ((measurableSet_revUpSet c hc t d).preimage measurable_fin_init)
  refine ⟨_, comap_measurable (hist P c (t + 1)) hS, ?_⟩
  filter_upwards [hmono] with ω hω
  have e1 := hist_eq_init P c t ω
  have e2 := hist_last P c t ω
  apply propext
  show (c t (Fin.init (hist P c (t + 1) ω)) d < hist P c (t + 1) ω (Fin.last t) ∧
      ∀ q : ℚ, d < (q : ℝ) → c t (Fin.init (hist P c (t + 1) ω)) d <
        c t (Fin.init (hist P c (t + 1) ω)) q) ↔
    (d < vtil P c t ω ∧ ∀ q : ℚ, d < (q : ℝ) → c t (hist P c t ω) d < c t (hist P c t ω) q)
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra hx
    exact absurd (hω (not_lt.1 hx)) (not_le.2 h1)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
    exact (h2 q hq1).trans_le (hω hq2.le)

include hc in
/-- On `RevDown`, a monotone period strategy reveals whether `ṽ_t < d`. -/
lemma reveal_down (t : ℕ) (d : ℝ) (hmono : ∀ᵐ ω ∂P, Monotone (c t (hist P c t ω))) :
    ∃ A : Set Ω, MeasurableSet[histSigma P c (t + 1)] A ∧
      A =ᵐ[P] ({ω | vtil P c t ω < d} ∩ RevDown P c t d) := by
  have hS : MeasurableSet ({h' : Fin (t + 1) → ℝ | h' (Fin.last t) < c t (Fin.init h') d} ∩
      {h' | ∀ q : ℚ, (q : ℝ) < d → c t (Fin.init h') q < c t (Fin.init h') d}) :=
    (measurableSet_lt (measurable_pi_apply _)
      ((measurable_c_apply c hc t d).comp measurable_fin_init)).inter
      ((measurableSet_revDownSet c hc t d).preimage measurable_fin_init)
  refine ⟨_, comap_measurable (hist P c (t + 1)) hS, ?_⟩
  filter_upwards [hmono] with ω hω
  have e1 := hist_eq_init P c t ω
  have e2 := hist_last P c t ω
  apply propext
  show (hist P c (t + 1) ω (Fin.last t) < c t (Fin.init (hist P c (t + 1) ω)) d ∧
      ∀ q : ℚ, (q : ℝ) < d → c t (Fin.init (hist P c (t + 1) ω)) q <
        c t (Fin.init (hist P c (t + 1) ω)) d) ↔
    (vtil P c t ω < d ∧ ∀ q : ℚ, (q : ℝ) < d → c t (hist P c t ω) q < c t (hist P c t ω) d)
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra hx
    exact absurd (hω (not_lt.1 hx)) (not_le.2 h1)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
    exact (hω hq1.le).trans_lt (h2 q hq2)

end Reveal

section KernelAux

/-- The kernel `b ↦ η b ∗ ν`. -/
noncomputable def convKernel {β : Type*} [MeasurableSpace β] (η : Kernel β ℝ) (ν : Measure ℝ) :
    Kernel β ℝ :=
  (η ×ₖ Kernel.const β ν).map (fun p : ℝ × ℝ => p.1 + p.2)

instance convKernel_isFinite {β : Type*} [MeasurableSpace β] (η : Kernel β ℝ) [IsFiniteKernel η]
    (ν : Measure ℝ) [IsFiniteMeasure ν] : IsFiniteKernel (convKernel η ν) := by
  unfold convKernel; infer_instance

lemma convKernel_apply {β : Type*} [MeasurableSpace β] (η : Kernel β ℝ) [IsSFiniteKernel η]
    (ν : Measure ℝ) [SFinite ν] (b : β) : convKernel η ν b = Measure.conv (η b) ν := by
  rw [convKernel, Kernel.map_apply _ measurable_add, Kernel.prod_apply, Kernel.const_apply]
  rfl

/-- If `V` is independent of `(X, Y)`, the conditional law of `V + Y` given `X` is the
convolution of the conditional law of `Y` given `X` with the law of `V`. -/
lemma condDistrib_add_of_indep {β Ω' : Type*} [MeasurableSpace β] [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] {X : Ω' → β} {Y V : Ω' → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hV : Measurable V)
    (hind : IndepFun (fun ω => (X ω, Y ω)) V P) :
    ∀ᵐ ω ∂P, condDistrib (fun ω => V ω + Y ω) X P (X ω) =
      Measure.conv (condDistrib Y X P (X ω)) (P.map V) := by
  have hmap3 := (indepFun_iff_map_prod_eq_prod_map_map (hX.prodMk hY).aemeasurable
    hV.aemeasurable).1 hind
  rw [← compProd_map_condDistrib hX.aemeasurable hY.aemeasurable] at hmap3
  have heq : P.map (fun ω => (X ω, V ω + Y ω)) =
      P.map X ⊗ₘ convKernel (condDistrib Y X P) (P.map V) := by
    ext s hs
    have hg : Measurable (fun p : (β × ℝ) × ℝ => (p.1.1, p.2 + p.1.2)) := by fun_prop
    have hs' : MeasurableSet ((fun p : (β × ℝ) × ℝ => (p.1.1, p.2 + p.1.2)) ⁻¹' s) := hg hs
    have e1 : P.map (fun ω => (X ω, V ω + Y ω)) =
        (P.map (fun ω => ((X ω, Y ω), V ω))).map
          (fun p : (β × ℝ) × ℝ => (p.1.1, p.2 + p.1.2)) := by
      rw [Measure.map_map hg ((hX.prodMk hY).prodMk hV)]; rfl
    rw [e1, Measure.map_apply hg hs, hmap3, Measure.prod_apply hs',
      Measure.lintegral_compProd (measurable_measure_prodMk_left hs'),
      Measure.compProd_apply hs]
    refine lintegral_congr fun b => ?_
    rw [convKernel_apply, Measure.conv, Measure.map_apply measurable_add
      (measurable_prodMk_left hs), Measure.prod_apply (measurable_add (measurable_prodMk_left hs))]
    refine lintegral_congr fun y => ?_
    congr 1
    ext v
    simp only [Set.mem_preimage]
    rw [add_comm]
  have hae := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (Y := fun ω => V ω + Y ω) hX (hV.add hY) heq
  filter_upwards [ae_of_ae_map hX.aemeasurable hae] with ω hω
  rw [hω, convKernel_apply]

end KernelAux

section Kernels

variable (Lθ Lε : Measure ℝ) (ψ : ℝ → ℝ) [IsProbabilityMeasure Lθ] [IsProbabilityMeasure Lε]
  [IsProbabilityMeasure (vLaw ψ)]
  (hθ : Integrable (fun x => x ^ 2) Lθ) (hψc : Continuous ψ) (hψpos : ∀ x, 0 < ψ x)
  (c : Profile) (hc : ∀ t, Measurable (Function.uncurry (c t)))

include hc in
/-- The first moment of the conditional law of `Y_t` is `E(Y_t | h^t)`. -/
lemma beliefY_mean (t : ℕ) :
    ∀ᵐ ω ∂(law Lθ Lε (vLaw ψ)),
      Integrable id (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) ∧
      ∫ y, y ∂(beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) =
        ((law Lθ Lε (vLaw ψ))[Ycond (law Lθ Lε (vLaw ψ)) c t |
          histSigma (law Lθ Lε (vLaw ψ)) c t]) ω := by
  have hX := measurable_hist (law Lθ Lε (vLaw ψ)) c hc t
  have hY := measurable_Ycond (law Lθ Lε (vLaw ψ)) c hc t
  have hYi : Integrable (Ycond (law Lθ Lε (vLaw ψ)) c t) (law Lθ Lε (vLaw ψ)) :=
    integrable_condExp
  have h1 := condExp_ae_eq_integral_condDistrib' hX hYi
  have hint : Integrable (fun p : (Fin t → ℝ) × ℝ => p.2)
      ((law Lθ Lε (vLaw ψ)).map fun ω =>
        (hist (law Lθ Lε (vLaw ψ)) c t ω, Ycond (law Lθ Lε (vLaw ψ)) c t ω)) :=
    (integrable_map_measure measurable_snd.aestronglyMeasurable
      (hX.prodMk hY).aemeasurable).2 hYi
  have h2 := hint.condDistrib_ae hX.aemeasurable hY.aemeasurable
  filter_upwards [h1, h2] with ω h1 h2
  exact ⟨h2, h1.symm⟩

include hθ hc in
/-- The second moment of the conditional law of `Y_t` is `E(Y_t² | h^t)`. -/
lemma beliefY_sq (t : ℕ) :
    ∀ᵐ ω ∂(law Lθ Lε (vLaw ψ)),
      Integrable (fun y => y ^ 2)
          (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) ∧
      ∫ y, y ^ 2 ∂(beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω)) =
        ((law Lθ Lε (vLaw ψ))[fun ω => Ycond (law Lθ Lε (vLaw ψ)) c t ω ^ 2 |
          histSigma (law Lθ Lε (vLaw ψ)) c t]) ω := by
  have hX := measurable_hist (law Lθ Lε (vLaw ψ)) c hc t
  have hY := measurable_Ycond (law Lθ Lε (vLaw ψ)) c hc t
  have hY2 : MemLp (Ycond (law Lθ Lε (vLaw ψ)) c t) 2 (law Lθ Lε (vLaw ψ)) :=
    (memLp_thetaV Lθ Lε (vLaw ψ) hθ).condExp (by norm_num)
  have h1 := condExp_ae_eq_integral_condDistrib hX hY.aemeasurable (f := fun y : ℝ => y ^ 2)
    (measurable_id.pow_const 2).stronglyMeasurable hY2.integrable_sq
  have hint : Integrable (fun p : (Fin t → ℝ) × ℝ => p.2 ^ 2)
      ((law Lθ Lε (vLaw ψ)).map fun ω =>
        (hist (law Lθ Lε (vLaw ψ)) c t ω, Ycond (law Lθ Lε (vLaw ψ)) c t ω)) :=
    (integrable_map_measure (measurable_snd.pow_const 2).aestronglyMeasurable
      (hX.prodMk hY).aemeasurable).2 hY2.integrable_sq
  have h2 := hint.condDistrib_ae hX.aemeasurable hY.aemeasurable
  filter_upwards [h1, h2] with ω h1 h2
  exact ⟨h2, h1.symm⟩

include hc in
/-- The conditional law of `ṽ_t = v_t + Y_t` given `h^t` is the convolution of the conditional
law of `Y_t` with the law of `v_t` (as `v_t` is independent of `(h^t, Y_t)`). -/
lemma typeLaw_eq_conv (t : ℕ) :
    ∀ᵐ ω ∂(law Lθ Lε (vLaw ψ)),
      typeLaw (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω) =
        Measure.conv (beliefY (law Lθ Lε (vLaw ψ)) c t (hist (law Lθ Lε (vLaw ψ)) c t ω))
          (vLaw ψ) := by
  have hX := measurable_hist (law Lθ Lε (vLaw ψ)) c hc t
  have hY := measurable_Ycond (law Lθ Lε (vLaw ψ)) c hc t
  have hV : Measurable (vV t) := measurable_pi_apply _
  have hind : IndepFun (fun ω => (hist (law Lθ Lε (vLaw ψ)) c t ω,
      Ycond (law Lθ Lε (vLaw ψ)) c t ω)) (vV t) (law Lθ Lε (vLaw ψ)) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (indep_v Lθ Lε (vLaw ψ) t).symm
      (measurable_hist_Ycond_past (law Lθ Lε (vLaw ψ)) c hc t).comap_le
  have h := condDistrib_add_of_indep (law Lθ Lε (vLaw ψ)) hX hY hV hind
  rw [map_vV] at h
  exact h

end Kernels

end CC.LearnTheta
