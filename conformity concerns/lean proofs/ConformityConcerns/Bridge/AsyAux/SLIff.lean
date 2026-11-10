import ConformityConcerns.Bridge.AsyAux.Fiber
import ConformityConcerns.Bridge.SL

/-!
# Social learning about `x_i` occurs iff `(Σ_t)_{ii} → 0` almost surely

* If `(Σ_t)_{ii} → 0` a.s., the posterior mean converges to `x_i` in `L²`, hence a.s. by Lévy's
  upward theorem (as in `occurs_core`).
* Conversely, social learning gives convergence in probability of the posterior mean to `x_i`
  (integrating the conditional statements against the law of `x_i`). Along a weight path the
  error `x_i - m_{t,i}` is `N(0, (Σ_t)_{ii})`, whose probability of exceeding `1` in absolute value
  is nondecreasing in the variance and positive for a positive variance; as `(Σ_t)_{ii}` is
  nonincreasing, it tends to `0` for almost every weight path.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

set_option warn.classDefReducibility false

/-! ### From the conditional definition to convergence in probability -/

section Cond

variable {P : Measure Ωg} [IsProbabilityMeasure P] {X : Ωg → ℝ}

lemma measure_eq_lintegral_condDistrib (hX : Measurable X) {A : Set Ωg} (hA : MeasurableSet A) :
    P A = ∫⁻ r, condDistrib id X P r A ∂(P.map X) := by
  have hc := compProd_map_condDistrib (μ := P) (Y := id) hX.aemeasurable aemeasurable_id
  have h1 : ((P.map X) ⊗ₘ condDistrib id X P) (Set.univ ×ˢ A) = P A := by
    rw [hc, Measure.map_apply (hX.prodMk measurable_id) (MeasurableSet.univ.prod hA)]
    congr 1
    ext ω
    simp
  rw [← h1, Measure.compProd_apply_prod MeasurableSet.univ hA, Measure.restrict_univ]

/-- Social learning gives unconditional convergence in probability. -/
lemma tendstoInMeasure_of_slOccurs (hX : Measurable X) {post : ℕ → Ωg → ℝ}
    (hpost : ∀ n, Measurable (post n)) (h : SLOccurs P X post) :
    TendstoInMeasure P post atTop X := by
  intro ε hε
  have hA : ∀ n, MeasurableSet {ω | ε ≤ edist (post n ω) (X ω)} := fun n =>
    measurableSet_le measurable_const ((hpost n).edist hX)
  have e : ∀ n, P {ω | ε ≤ edist (post n ω) (X ω)} =
      ∫⁻ r, condDistrib id X P r {ω | ε ≤ edist (post n ω) (X ω)} ∂(P.map X) := fun n =>
    measure_eq_lintegral_condDistrib hX (hA n)
  rw [tendsto_congr e]
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := P.map X)
    (F := fun n r => condDistrib id X P r {ω | ε ≤ edist (post n ω) (X ω)}) (f := fun _ => 0)
    (fun _ => 1) (fun n => Kernel.measurable_coe _ (hA n))
    (fun n => Eventually.of_forall fun r => prob_le_one)
    (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.one_ne_top (measure_ne_top _ _))
    (by
      unfold SLOccurs at h
      filter_upwards [h, br_ae_condDistrib_eq hX] with r hr hXr
      refine (hr ε hε).congr fun n => measure_congr ?_
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hXr] with ω hω
      simp only [hω])
  simpa using hlim

end Cond

/-! ### The probability that a centred Gaussian exceeds `1` in absolute value -/

/-- `P(|N(0, s)| ≥ 1)`. -/
noncomputable def tailG (s : ℝ) : ℝ≥0∞ := gaussianReal 0 s.toNNReal {x | 1 ≤ |x|}

lemma measurableSet_one_le_abs : MeasurableSet {x : ℝ | 1 ≤ |x|} :=
  measurableSet_le measurable_const continuous_abs.measurable

lemma tailG_eq {s : ℝ} (hs : 0 ≤ s) : tailG s = gaussianReal 0 1 {x | 1 ≤ |√s * x|} := by
  have h := gaussianReal_map_const_mul (μ := 0) (v := 1) (√s)
  have hv : NNReal.mk (√s ^ 2) (sq_nonneg _) * 1 = s.toNNReal := by
    apply NNReal.eq
    simp [Real.sq_sqrt hs, hs]
  rw [mul_zero, hv] at h
  unfold tailG
  rw [← h, Measure.map_apply (measurable_const_mul _) measurableSet_one_le_abs]
  rfl

lemma abs_sqrt_mul (c x : ℝ) : |√c * x| = √c * |x| := by
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg c)]

lemma tailG_mono {δ s : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ s) : tailG δ ≤ tailG s := by
  rw [tailG_eq hδ, tailG_eq (hδ.trans h)]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_ofPred_eq, abs_sqrt_mul] at hx ⊢
  exact hx.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (abs_nonneg x))

lemma tailG_pos {δ : ℝ} (hδ : 0 < δ) : 0 < tailG δ := by
  rw [tailG_eq hδ.le]
  have hs : 0 < √δ := Real.sqrt_pos.2 hδ
  have hsub : Set.Ioi (1 / √δ) ⊆ {x : ℝ | 1 ≤ |√δ * x|} := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [Set.mem_ofPred_eq]
    have h1 : 1 < √δ * x := by
      rw [div_lt_iff₀ hs] at hx; linarith
    rw [abs_of_pos (by linarith)]
    exact h1.le
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)
    (measure_mono_null hsub h0)
  rw [Real.volume_Ioi] at this
  exact ENNReal.top_ne_zero this

/-! ### The Gaussian model -/

variable (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]

lemma lawG_tail (hS₁ : S₁.PosSemidef) (i : Fin 2) (t : ℕ) :
    lawG S₁ G {ω | 1 ≤ edist (kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t i) (ω.1 i)} =
      ∫⁻ γ, tailG (SigP κ S₁ γ t i i) ∂(Measure.infinitePi fun _ : ℕ => G) := by
  have hk : Measurable (fun ω : Ωg => kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t) :=
    (measurable_kmean κ S₁ t).comp (measurable_gam.prodMk (measurable_obsSeq κ S₁))
  have hB : MeasurableSet
      {ω : Ωg | 1 ≤ edist (kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t i) (ω.1 i)} :=
    measurableSet_le measurable_const ((br_meas_coord hk i).edist (br_meas_coord measurable_fst i))
  rw [measure_lawG S₁ G hB]
  congr 1
  funext γ
  have hcoord : Measurable (fun u : E2 => u i) := br_meas_coord measurable_id i
  have hC : MeasurableSet {u : E2 | 1 ≤ |u i|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp hcoord)
  have hset : (fun p : E2 × (ℕ → E2) => ((p.1, (p.2, γ)) : Ωg)) ⁻¹'
      {ω : Ωg | 1 ≤ edist (kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t i) (ω.1 i)} =
      (fun p => errF κ S₁ γ p.1 p.2 t) ⁻¹' {u : E2 | 1 ≤ |u i|} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, edist_dist, Real.dist_eq,
      ENNReal.one_le_ofReal]
    rw [abs_sub_comm]
    rfl
  rw [hset, ← Measure.map_apply (measurable_errF κ S₁ γ t) hC, (kalman_fiber κ S₁ γ hS₁ t).2]
  have hC' : {u : E2 | 1 ≤ |u i|} = (fun u : E2 => u i) ⁻¹' {x : ℝ | 1 ≤ |x|} := rfl
  rw [hC', ← Measure.map_apply hcoord measurableSet_one_le_abs,
    (measurePreserving_eval_multivariateGaussian (SigmaC_psd' (fun _ => κ) γ S₁ hS₁ t)).map_eq]
  simp [tailG]

lemma SigP_anti (hS₁ : S₁.PosSemidef) (i : Fin 2) (γ : ℕ → ℝ) :
    Antitone (fun t => SigP κ S₁ γ t i i) := by
  fin_cases i
  · exact SigmaC_anti00 (κ := fun _ => κ) (γ := γ) hS₁
  · exact SigmaC_anti11 (κ := fun _ => κ) (γ := γ) hS₁

/-- **Only if.** -/
theorem sl_only_if (hS₁ : S₁.PosSemidef) (i : Fin 2)
    (h : SLOccurs (lawG S₁ G) (fun ω => ω.1 i)
      (fun t => (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ t])) :
    ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => Sig κ S₁ ω t i i) atTop (𝓝 0) := by
  have hx : Measurable (fun ω : Ωg => ω.1 i) := br_meas_coord measurable_fst i
  have hpost : ∀ n, Measurable ((lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ n]) := fun n =>
    stronglyMeasurable_condExp.measurable.mono (infoSigma_le κ S₁ n) le_rfl
  have h1 := tendstoInMeasure_of_slOccurs hx hpost h
  have h2 : TendstoInMeasure (lawG S₁ G)
      (fun n ω => kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) n i) atTop (fun ω => ω.1 i) :=
    h1.congr_left (fun n => post_ae κ S₁ G hS₁ i n)
  have h3 := h2 1 one_pos
  simp_rw [lawG_tail κ S₁ G hS₁ i] at h3
  have hA : ∀ δ : ℝ, 0 < δ →
      (Measure.infinitePi fun _ : ℕ => G) {γ | ∀ t, δ ≤ SigP κ S₁ γ t i i} = 0 := by
    intro δ hδ
    have hAm : MeasurableSet {γ : ℕ → ℝ | ∀ t, δ ≤ SigP κ S₁ γ t i i} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun t =>
        measurableSet_le measurable_const (br_meas_entry (measurable_SigP κ S₁ t) i i)
    have hle : ∀ n, tailG δ * (Measure.infinitePi fun _ : ℕ => G)
        {γ | ∀ t, δ ≤ SigP κ S₁ γ t i i} ≤
        ∫⁻ γ, tailG (SigP κ S₁ γ n i i) ∂(Measure.infinitePi fun _ : ℕ => G) := by
      intro n
      rw [← lintegral_indicator_const hAm]
      refine lintegral_mono fun γ => ?_
      by_cases hγ : γ ∈ {γ : ℕ → ℝ | ∀ t, δ ≤ SigP κ S₁ γ t i i}
      · rw [Set.indicator_of_mem hγ]
        exact tailG_mono hδ.le (hγ n)
      · rw [Set.indicator_of_notMem hγ]
        exact zero_le
    have h0 := le_antisymm (ge_of_tendsto' h3 hle) zero_le
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (tailG_pos hδ).ne'
    · exact h
  have hae : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G),
      Tendsto (fun t => SigP κ S₁ γ t i i) atTop (𝓝 0) := by
    have hall : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G), ∀ n : ℕ,
        γ ∉ {γ : ℕ → ℝ | ∀ t, 1 / ((n : ℝ) + 1) ≤ SigP κ S₁ γ t i i} :=
      ae_all_iff.2 fun n => measure_eq_zero_iff_ae_notMem.1 (hA _ (by positivity))
    filter_upwards [hall] with γ hγ
    have hanti := SigP_anti κ S₁ hS₁ i γ
    have hnn : ∀ t, 0 ≤ SigP κ S₁ γ t i i := fun t =>
      (SigmaC_psd' (fun _ => κ) γ S₁ hS₁ t).diag_nonneg
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun t => lt_of_lt_of_le ha (hnn t),
      fun a ha => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ha
    have := hγ n
    simp only [not_forall, not_le] at this
    obtain ⟨t0, ht0⟩ := this
    exact eventually_atTop.2 ⟨t0, fun t ht => lt_of_le_of_lt (hanti ht) (ht0.trans hn)⟩
  exact ae_lawG_of_ae_gam S₁ G hae

/-! ### If -/

lemma tendsto_lintegral_Sig_entry (hS₁ : S₁.PosSemidef) (i : Fin 2)
    (hlim : ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => Sig κ S₁ ω t i i) atTop (𝓝 0)) :
    Tendsto (fun t => ∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t i i)
      ∂(Measure.infinitePi fun _ : ℕ => G)) atTop (𝓝 0) := by
  have e : ∀ t, ∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t i i) ∂(Measure.infinitePi fun _ : ℕ => G) =
      ∫⁻ ω, ENNReal.ofReal (Sig κ S₁ ω t i i) ∂(lawG S₁ G) := fun t =>
    lint_gam S₁ G (ENNReal.measurable_ofReal.comp (br_meas_entry (measurable_SigP κ S₁ t) i i))
  rw [tendsto_congr e]
  have h := tendsto_lintegral_of_dominated_convergence (μ := lawG S₁ G)
    (F := fun t ω => ENNReal.ofReal (Sig κ S₁ ω t i i)) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal (S₁ i i))
    (fun t => ENNReal.measurable_ofReal.comp
      ((br_meas_entry (measurable_SigP κ S₁ t) i i).comp measurable_gam))
    (fun t => Eventually.of_forall fun ω =>
      ENNReal.ofReal_le_ofReal (SigP_anti κ S₁ hS₁ i (gam ω) (Nat.zero_le t)))
    (by simp)
    (by
      filter_upwards [hlim] with ω hω
      simpa using ENNReal.tendsto_ofReal hω)
  simpa using h

/-- **If** (as `occurs_core`, from the diagonal entry only). -/
theorem occurs_entry (hS₁ : S₁.PosSemidef) (i : Fin 2)
    (hlim : ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => Sig κ S₁ ω t i i) atTop (𝓝 0)) :
    ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ t] ω)
      atTop (𝓝 (ω.1 i)) := by
  set P := lawG S₁ G with hP
  let mi : ℕ → Ωg → ℝ := fun t ω => kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t i
  have hmi : ∀ t, Measurable (mi t) := fun t =>
    br_meas_coord ((measurable_kmean κ S₁ t).comp
      (measurable_gam.prodMk (measurable_obsSeq κ S₁))) i
  have hmi_info : ∀ t, Measurable[infoSigma κ S₁ t] (mi t) := fun t =>
    meas_info_of_dep κ S₁ t (fun p => kmean κ S₁ p.1 p.2 t i)
      (br_meas_coord (measurable_kmean κ S₁ t) i)
      (fun _ _ _ _ h1 h2 => by
        simp only
        rw [kmean_congr κ S₁ (fun s hs => h1 s hs.le) h2])
  have hx : Measurable (fun ω : Ωg => ω.1 i) := br_meas_coord measurable_fst i
  have hTM : TendstoInMeasure P mi atTop (fun ω => ω.1 i) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero ?_
    have e : ∀ t, eLpNorm (mi t - fun ω => ω.1 i) 2 P =
        (∫⁻ γ, ENNReal.ofReal (SigP κ S₁ γ t i i)
          ∂(Measure.infinitePi fun _ : ℕ => G)) ^ (1 / (2 : ℝ)) := by
      intro t
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        ((hmi t).sub hx).aestronglyMeasurable, ← lintegral_err_sq κ S₁ G hS₁ i t]
      congr 1
      refine lintegral_congr fun ω => ?_
      simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
      rw [enorm_sub_rev]
      norm_cast
    simp_rw [e]
    have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp
      (tendsto_lintegral_Sig_entry κ S₁ G hS₁ i hlim)
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  obtain ⟨ns, -, hae⟩ := hTM.exists_seq_tendsto_ae
  let θh : Ωg → ℝ := fun ω => limUnder atTop (fun k => mi (ns k) ω)
  have hθh_sm : StronglyMeasurable[⨆ t, infoSigma κ S₁ t] θh :=
    br_limUnder_sm fun k => ((hmi_info (ns k)).mono (le_iSup (infoSigma κ S₁) (ns k))
      le_rfl).stronglyMeasurable
  have hθh_ae : θh =ᵐ[P] fun ω => ω.1 i := by
    filter_upwards [hae] with ω h
    exact h.limUnder_eq
  have hint : Integrable θh P := (integrable_coord_lawG S₁ G i).congr hθh_ae.symm
  have h1 := hint.tendsto_ae_condExp (ℱ := infoFilt κ S₁) hθh_sm
  have h2 : ∀ t, P[fun ω => ω.1 i | infoSigma κ S₁ t] =ᵐ[P] P[θh | infoFilt κ S₁ t] :=
    fun t => condExp_congr_ae hθh_ae.symm
  filter_upwards [h1, ae_all_iff.2 h2, hθh_ae] with ω a b c
  rw [← c]
  exact a.congr (fun t => (b t).symm)

/-- Social learning about `x_i` occurs iff `(Σ_t)_{ii} → 0` almost surely. -/
theorem sl_iff_entry (hS₁ : S₁.PosSemidef) (i : Fin 2) :
    SLOccurs (lawG S₁ G) (fun ω => ω.1 i)
        (fun t => (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ t]) ↔
      ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => Sig κ S₁ ω t i i) atTop (𝓝 0) := by
  refine ⟨sl_only_if κ S₁ G hS₁ i, fun h => ?_⟩
  have hx : Measurable (fun ω : Ωg => ω.1 i) := br_meas_coord measurable_fst i
  have hpost : ∀ n, Measurable ((lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ n]) := fun n =>
    stronglyMeasurable_condExp.measurable.mono (infoSigma_le κ S₁ n) le_rfl
  exact slOccurs_of_ae hx hpost (occurs_entry κ S₁ G hS₁ i h)

end CC.Bridge
