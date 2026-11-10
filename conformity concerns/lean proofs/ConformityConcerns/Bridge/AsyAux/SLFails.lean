import ConformityConcerns.Bridge.AsyAux.SLIff
import ConformityConcerns.Bridge.Fails

/-!
# If `(Σ_t)_{ii}` does not tend to `0` almost surely, social learning about `x_i` fails

The first paragraph of the proof of Proposition 2: "Otherwise, with positive probability the
posterior of `θ` is Gaussian with positive variance in the limit, so on this event `θ(h^t)`
almost surely converges to a limit other than `θ`. Because this event depends only on the
sequence of `γ_t`, which is independent of `θ`, social learning about `θ` fails."

Along a weight path with `(Σ_t)_{ii} ≥ q > 0`, the error `x_i - m_{t,i}` is `N(0, (Σ_t)_{ii})`, so
its probability of being below `δ` in absolute value is small uniformly in `t` when `δ` is small.
Hence the limit of the posterior mean differs from `x_i` almost surely along that path.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

set_option warn.classDefReducibility false

/-! ### Conditioning on an event independent of `X` -/

section Cond

variable {P : Measure Ωg} [IsProbabilityMeasure P] {X : Ωg → ℝ}

/-- If the posterior mean converges almost surely to `L` and, on an event `B` of positive
conditional probability given almost every `X = r`, `L ≠ X` almost surely, social learning
fails. -/
theorem slFails_of_event (hX : Measurable X) {post : ℕ → Ωg → ℝ} {L : Ωg → ℝ}
    (h1 : ∀ᵐ ω ∂P, Tendsto (fun n => post n ω) atTop (𝓝 (L ω))) {B : Set Ωg}
    (hpos : ∀ᵐ r ∂(P.map X), condDistrib id X P r B ≠ 0)
    (h2 : P (B ∩ {ω | L ω = X ω}) = 0) : SLFails P X post := by
  unfold SLFails
  have h2' : ∀ᵐ ω ∂P, ¬ (ω ∈ B ∧ L ω = X ω) := by
    rw [ae_iff]
    simpa [Set.inter_def] using h2
  filter_upwards [br_ae_condDistrib hX h1, br_ae_condDistrib hX h2', br_ae_condDistrib_eq hX,
    hpos] with r a1 a2 a3 a4
  intro hT
  obtain ⟨ns, hns, hae⟩ := hT.exists_seq_tendsto_ae
  apply a4
  rw [← compl_compl B]
  refine (ae_iff (p := fun ω => ω ∉ B) |>.1 ?_)
  filter_upwards [hae, a1, a2, a3] with ω b1 b2 b3 b4
  intro hB
  have hL : L ω = r := tendsto_nhds_unique (b2.comp hns.tendsto_atTop) b1
  exact b3 ⟨hB, hL.trans b4.symm⟩

end Cond

/-! ### Small balls of Gaussians with variance bounded below -/

/-- The sets `{x : |x| < 1/(n+1)}`. -/
def ballN (n : ℕ) : Set ℝ := {x | |x| < 1 / ((n : ℝ) + 1)}

lemma measurableSet_ballN (n : ℕ) : MeasurableSet (ballN n) :=
  measurableSet_lt continuous_abs.measurable measurable_const

lemma small_ball_le {q s δ : ℝ} (hq : 0 < q) (h : q ≤ s) :
    gaussianReal 0 s.toNNReal {x | |x| < δ} ≤ gaussianReal 0 1 {x | |x| < δ / √q} := by
  have hs : 0 ≤ s := hq.le.trans h
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := 1) (√s)
  have hv : NNReal.mk (√s ^ 2) (sq_nonneg _) * 1 = s.toNNReal := by
    apply NNReal.eq
    simp [Real.sq_sqrt hs, hs]
  rw [mul_zero, hv] at hmap
  have hm : MeasurableSet {x : ℝ | |x| < δ} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  rw [← hmap, Measure.map_apply (measurable_const_mul _) hm]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, abs_sqrt_mul] at hx ⊢
  have hq' : 0 < √q := Real.sqrt_pos.2 hq
  rw [lt_div_iff₀ hq']
  have hle : √q ≤ √s := Real.sqrt_le_sqrt h
  calc |x| * √q ≤ |x| * √s := mul_le_mul_of_nonneg_left hle (abs_nonneg x)
    _ = √s * |x| := mul_comm _ _
    _ < δ := hx

lemma tendsto_gaussian_shrink {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n : ℕ => gaussianReal 0 1 {x : ℝ | |x| < (1 / ((n : ℝ) + 1)) / √q}) atTop (𝓝 0) := by
  have hq' : 0 < √q := Real.sqrt_pos.2 hq
  set A : ℕ → Set ℝ := fun n => {x : ℝ | |x| < (1 / ((n : ℝ) + 1)) / √q} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_lt continuous_abs.measurable measurable_const
  have hanti : Antitone A := by
    intro m n hmn x hx
    simp only [hA, Set.mem_ofPred_eq] at hx ⊢
    refine hx.trans_le (div_le_div_of_nonneg_right ?_ hq'.le)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hinter : ⋂ n, A n = {0} := by
    ext x
    simp only [Set.mem_iInter, hA, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hx
      have hpos : 0 < |x| * √q := mul_pos (abs_pos.2 hx) hq'
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      have := h n
      rw [lt_div_iff₀ hq'] at this
      linarith
    · rintro rfl n
      simp only [abs_zero]
      positivity
  have h := tendsto_measure_iInter_atTop (μ := gaussianReal 0 1)
    (fun n => (hAm n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at h
  have hnull := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) one_ne_zero
  rwa [measure_singleton] at h

/-! ### The Gaussian model -/

variable (κ : ℝ) (S₁ : M2) (G : Measure ℝ) [IsProbabilityMeasure G]

/-- An almost sure property under `lawG` holds, for almost every weight path, almost surely
along the path. -/
lemma ae_fiber {p : Ωg → Prop} (h : ∀ᵐ ω ∂(lawG S₁ G), p ω) :
    ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G),
      ∀ᵐ q ∂(Qm S₁), p ((q.1, (q.2, γ)) : Ωg) := by
  set N := toMeasurable (lawG S₁ G) {ω | ¬ p ω} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have h0 : lawG S₁ G N = 0 := by rw [hN, measure_toMeasurable]; exact ae_iff.1 h
  rw [measure_lawG S₁ G hNm, lintegral_eq_zero_iff'] at h0
  · filter_upwards [h0] with γ hγ
    refine measure_mono_null (fun q hq => ?_) hγ
    exact subset_toMeasurable (lawG S₁ G) {ω | ¬ p ω} hq
  · have hm : Measurable (fun z : (ℕ → ℝ) × (E2 × (ℕ → E2)) => ((z.2.1, (z.2.2, z.1)) : Ωg)) :=
      (measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
    exact (measurable_measure_prodMk_left (hm hNm)).aemeasurable

/-- Along a weight path whose variance is bounded below, the limit of the Kalman mean differs
from `x_i` almost surely. -/
lemma fiber_null (hS₁ : S₁.PosSemidef) (i : Fin 2) (γ : ℕ → ℝ) {q : ℝ} (hq : 0 < q)
    (hle : ∀ t, q ≤ SigP κ S₁ γ t i i) {L : E2 × (ℕ → E2) → ℝ}
    (hlim : ∀ᵐ p ∂(Qm S₁), Tendsto (fun t => kmean κ S₁ γ (obsF κ S₁ γ p.1 p.2) t i) atTop
      (𝓝 (L p))) :
    Qm S₁ {p | L p = p.1 i} = 0 := by
  have hcoord : Measurable (fun u : E2 => u i) := br_meas_coord measurable_id i
  -- the probability that the error at date `t` is below `δ`
  have hball : ∀ (δ : ℝ) (t : ℕ), Qm S₁ {p | |errF κ S₁ γ p.1 p.2 t i| < δ} ≤
      gaussianReal 0 1 {x : ℝ | |x| < δ / √q} := by
    intro δ t
    have hC : MeasurableSet {u : E2 | |u i| < δ} :=
      measurableSet_lt (continuous_abs.measurable.comp hcoord) measurable_const
    have hset : {p : E2 × (ℕ → E2) | |errF κ S₁ γ p.1 p.2 t i| < δ} =
        (fun p => errF κ S₁ γ p.1 p.2 t) ⁻¹' {u : E2 | |u i| < δ} := rfl
    have hD : MeasurableSet {x : ℝ | |x| < δ} :=
      measurableSet_lt continuous_abs.measurable measurable_const
    rw [hset, ← Measure.map_apply (measurable_errF κ S₁ γ t) hC, (kalman_fiber κ S₁ γ hS₁ t).2]
    have hC' : {u : E2 | |u i| < δ} = (fun u : E2 => u i) ⁻¹' {x : ℝ | |x| < δ} := rfl
    rw [hC', ← Measure.map_apply hcoord hD,
      (measurePreserving_eval_multivariateGaussian (SigmaC_psd' (fun _ => κ) γ S₁ hS₁ t)).map_eq]
    simpa using small_ball_le (δ := δ) hq (hle t)
  -- the bound for every `δ`
  have hbound : ∀ n : ℕ, Qm S₁ {p | L p = p.1 i} ≤
      gaussianReal 0 1 {x : ℝ | |x| < (1 / ((n : ℝ) + 1)) / √q} := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    set B : ℕ → Set (E2 × (ℕ → E2)) := fun T =>
      {p | ∀ t, T ≤ t → |errF κ S₁ γ p.1 p.2 t i| < δ} with hB
    have hmono : Monotone B := fun a b hab p hp t ht => hp t (hab.trans ht)
    have hcover : {p | L p = p.1 i} ≤ᵐ[Qm S₁] ⋃ T, B T := by
      filter_upwards [hlim] with p hp hL
      have hL' : L p = p.1 i := hL
      have herr : Tendsto (fun t => errF κ S₁ γ p.1 p.2 t i) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := p.1 i)).sub hp
        rw [hL', sub_self] at this
        exact this
      have hev := (Metric.tendsto_nhds.1 herr) δ hδpos
      obtain ⟨T, hT⟩ := eventually_atTop.1 hev
      refine Set.mem_iUnion.2 ⟨T, fun t ht => ?_⟩
      simpa [Real.dist_eq] using hT t ht
    calc Qm S₁ {p | L p = p.1 i} ≤ Qm S₁ (⋃ T, B T) := measure_mono_ae hcover
      _ = ⨆ T, Qm S₁ (B T) := hmono.measure_iUnion
      _ ≤ _ := iSup_le fun T =>
          (measure_mono (show B T ⊆ {p | |errF κ S₁ γ p.1 p.2 T i| < δ} from
            fun p hp => hp T le_rfl)).trans (hball δ T)
  have hlimit := tendsto_gaussian_shrink hq
  exact le_antisymm (ge_of_tendsto' hlimit hbound) bot_le

/-- The conditional probability of an event of the weights, given `x_i`, is its probability. -/
lemma condDistrib_gam_event (i : Fin 2) {A : Set (ℕ → ℝ)} (hA : MeasurableSet A) :
    ∀ᵐ r ∂((lawG S₁ G).map (fun ω : Ωg => ω.1 i)),
      condDistrib id (fun ω : Ωg => ω.1 i) (lawG S₁ G) r (gam ⁻¹' A) =
        (Measure.infinitePi fun _ : ℕ => G) A := by
  set P := lawG S₁ G with hP
  have hX : Measurable (fun ω : Ωg => ω.1 i) := br_meas_coord measurable_fst i
  have hBm : MeasurableSet (gam ⁻¹' A) := measurable_gam hA
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Kernel.measurable_coe _ hBm) measurable_const ?_
  intro C hC _
  have hc := compProd_map_condDistrib (μ := P) (Y := id) hX.aemeasurable aemeasurable_id
  have h1 : ((P.map fun ω : Ωg => ω.1 i) ⊗ₘ condDistrib id (fun ω : Ωg => ω.1 i) P) (C ×ˢ (gam ⁻¹' A)) =
      P ((fun ω : Ωg => ω.1 i) ⁻¹' C ∩ gam ⁻¹' A) := by
    rw [hc, Measure.map_apply (hX.prodMk measurable_id) (hC.prod hBm)]
    rfl
  rw [Measure.compProd_apply_prod hC hBm] at h1
  have hrect2 : (fun ω : Ωg => ω.1 i) ⁻¹' C =
      ((fun x : E2 => x i) ⁻¹' C) ×ˢ (Set.univ : Set ((ℕ → E2) × (ℕ → ℝ))) := by
    ext ω
    simp
  have hrect : (fun ω : Ωg => ω.1 i) ⁻¹' C ∩ gam ⁻¹' A =
      ((fun x : E2 => x i) ⁻¹' C) ×ˢ (Set.univ ×ˢ A) := by
    ext ω
    simp [gam]
  rw [h1, setLIntegral_const, Measure.map_apply hX hC, hrect, hrect2, hP]
  unfold lawG
  simp only [Measure.prod_prod, measure_univ, one_mul, mul_one]
  rw [mul_comm]

/-- **The first paragraph of the proof of Proposition 2, second half.** If `(Σ_t)_{ii}` does not
tend to `0` almost surely, social learning about `x_i` fails. -/
theorem sl_fails_entry (hS₁ : S₁.PosSemidef) (i : Fin 2)
    (h : ¬ ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => Sig κ S₁ ω t i i) atTop (𝓝 0)) :
    SLFails (lawG S₁ G) (fun ω => ω.1 i)
      (fun t => (lawG S₁ G)[fun ω => ω.1 i | infoSigma κ S₁ t]) := by
  set P := lawG S₁ G with hP
  have hX : Measurable (fun ω : Ωg => ω.1 i) := br_meas_coord measurable_fst i
  -- the paths whose variance stays bounded below
  set Bad : Set (ℕ → ℝ) := {γ | ∃ n : ℕ, ∀ t, 1 / ((n : ℝ) + 1) ≤ SigP κ S₁ γ t i i} with hBad
  have hBadm : MeasurableSet Bad := by
    have : Bad = ⋃ n : ℕ, ⋂ t, {γ | 1 / ((n : ℝ) + 1) ≤ SigP κ S₁ γ t i i} := by
      ext γ
      simp [hBad]
    rw [this]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun t =>
      measurableSet_le measurable_const (br_meas_entry (measurable_SigP κ S₁ t) i i)
  have hBadpos : (Measure.infinitePi fun _ : ℕ => G) Bad ≠ 0 := by
    intro h0
    apply h
    have hae : ∀ᵐ γ ∂(Measure.infinitePi fun _ : ℕ => G), γ ∉ Bad := by
      rw [ae_iff]; simpa using h0
    have := ae_lawG_of_ae_gam S₁ G hae
    filter_upwards [this] with ω hω
    have hanti := SigP_anti κ S₁ hS₁ i (gam ω)
    have hnn : ∀ t, 0 ≤ SigP κ S₁ (gam ω) t i i := fun t =>
      (SigmaC_psd' (fun _ => κ) (gam ω) S₁ hS₁ t).diag_nonneg
    show Tendsto (fun t => SigP κ S₁ (gam ω) t i i) atTop (𝓝 0)
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun t => lt_of_lt_of_le ha (hnn t), fun a ha => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ha
    have hω' : ¬ ∀ t, 1 / ((n : ℝ) + 1) ≤ SigP κ S₁ (gam ω) t i i := fun hc => hω ⟨n, hc⟩
    simp only [not_forall, not_le] at hω'
    obtain ⟨t0, ht0⟩ := hω'
    exact eventually_atTop.2 ⟨t0, fun t ht => lt_of_le_of_lt (hanti ht) (ht0.trans hn)⟩
  -- the limit of the posterior mean, as a function of the weights and the observations
  set L := P[fun ω : Ωg => ω.1 i | ⨆ t, infoSigma κ S₁ t] with hLdef
  have hsm : StronglyMeasurable[⨆ t, infoSigma κ S₁ t] L := stronglyMeasurable_condExp
  have hsm' := hsm.mono (iSup_infoSigma_le κ S₁)
  obtain ⟨g, hg, hLg⟩ := hsm'.exists_eq_measurable_comp
  have hΓ : Measurable (fun ω : Ωg => (gam ω, fun s => obs κ S₁ s ω)) :=
    measurable_gam.prodMk (measurable_obsSeq κ S₁)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun t => P[fun ω : Ωg => ω.1 i | infoSigma κ S₁ t] ω) atTop
      (𝓝 (L ω)) := tendsto_ae_condExp (ℱ := infoFilt κ S₁) _
  have hk : ∀ᵐ ω ∂P, Tendsto (fun t => kmean κ S₁ (gam ω) (fun s => obs κ S₁ s ω) t i) atTop
      (𝓝 (g (gam ω, fun s => obs κ S₁ s ω))) := by
    filter_upwards [hlim, ae_all_iff.2 (fun t => post_ae κ S₁ G hS₁ i t)] with ω a b
    have e : L ω = g (gam ω, fun s => obs κ S₁ s ω) := by rw [hLg]; rfl
    rw [← e]
    exact a.congr (fun t => b t)
  have hfib := ae_fiber S₁ G hk
  -- `L ≠ x_i` on the bad paths
  have hE : P (gam ⁻¹' Bad ∩ {ω | L ω = ω.1 i}) = 0 := by
    have hset : gam ⁻¹' Bad ∩ {ω | L ω = ω.1 i} =
        gam ⁻¹' Bad ∩ {ω : Ωg | g (gam ω, fun s => obs κ S₁ s ω) = ω.1 i} := by
      rw [hLg]; rfl
    have hm : MeasurableSet (gam ⁻¹' Bad ∩ {ω : Ωg | g (gam ω, fun s => obs κ S₁ s ω) = ω.1 i}) :=
      (measurable_gam hBadm).inter (measurableSet_eq_fun (hg.measurable.comp hΓ) hX)
    rw [hset, hP, measure_lawG S₁ G hm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hfib] with γ hγ
    by_cases hb : γ ∈ Bad
    · obtain ⟨n, hn⟩ := hb
      have hq : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have key := fiber_null κ S₁ hS₁ i γ hq hn
        (L := fun p => g (γ, obsF κ S₁ γ p.1 p.2)) hγ
      refine measure_mono_null (fun p hp => ?_) key
      exact hp.2
    · refine measure_mono_null (fun p hp => ?_) (measure_empty (μ := Qm S₁))
      exact hb hp.1
  refine slFails_of_event hX hlim (B := gam ⁻¹' Bad) ?_ hE
  filter_upwards [condDistrib_gam_event S₁ G i hBadm] with r hr
  rw [hr]
  exact hBadpos

/-- **Proof of Proposition 2, first paragraph (`θ`).** If `σ²_{θ,t}` does not tend to `0` almost
surely, social learning about `θ` fails. -/
theorem socialLearning_theta_fails (hS₁ : S₁.PosSemidef)
    (h : ¬ ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => Sig κ S₁ ω t 0 0) atTop (𝓝 0)) :
    SLFails (lawG S₁ G) thetaV (postTheta κ S₁ G) :=
  sl_fails_entry κ S₁ G hS₁ 0 h

/-- **Proof of Proposition 2, first paragraph (`μ`).** If `σ²_{μ,t}` does not tend to `0` almost
surely, social learning about `μ` fails. -/
theorem socialLearning_mu_fails (hS₁ : S₁.PosSemidef)
    (h : ¬ ∀ᵐ ω ∂(lawG S₁ G), Tendsto (fun t => Sig κ S₁ ω t 1 1) atTop (𝓝 0)) :
    SLFails (lawG S₁ G) muV (postMu κ S₁ G) :=
  sl_fails_entry κ S₁ G hS₁ 1 h

end CC.Bridge
