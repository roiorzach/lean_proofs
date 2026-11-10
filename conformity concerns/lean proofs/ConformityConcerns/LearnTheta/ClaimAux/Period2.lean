import ConformityConcerns.LearnTheta.ClaimAux.Period

/-!
# One period of the Claim of Proposition A5: the conditional inequalities

With `J = E_m j`, `M = E_m g(Y - θ_m)`, `N = E_m[(θ - θ_m)(k(θ) - k(θ_m))]`,
`L = E_m g(θ - θ_m)` and `D = E_m |E_{m'} θ - θ_m|`:

* `condExp_J_le`: on the revealed set `Rev ∈ m`, `J ≤ D`;
* `condExp_J_ge`: on `{|θ_m| ≤ R}`, `c M ≤ J` when `ψ ≥ c` on `[d - R - 1, d + R + 1]`;
* `condExp_N_le`: `N ≤ (π/2)/(n+1) + (π/2)(n+1) M`;
* `condExp_N_ge`: on `{|θ_m| ≤ R}`, `c'_R L ≤ N`;
* `ae_ne`: `v + Y ≠ d` almost surely.
-/

namespace CC.LearnTheta.ClaimAux

open MeasureTheory ProbabilityTheory Filter Topology Real

section Period

variable {Ω : Type*} {m 𝒜 m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {θ ε v : Ω → ℝ}

namespace PeriodHyp

variable (H : PeriodHyp m 𝒜 mΩ P θ ε v)
include H

lemma atan_measΩ : Measurable (fun ω => arctan (θ ω + ε ω)) :=
  continuous_arctan.measurable.comp (H.θ_measΩ.add H.ε_meas)

/-- **The `ε`-step.** -/
lemma setIntegral_eps [IsProbabilityMeasure P] {L : Measure ℝ} (hL : P.map ε = L) {s : Set Ω}
    (hs : MeasurableSet[m] s) :
    ∫ ω in s, nfun P m θ L ω ∂P =
      ∫ ω in s, (Yp P m θ ε ω - (P[θ | m]) ω) * arctan (θ ω + ε ω) ∂P := by
  have hLp : IsProbabilityMeasure L := hL ▸ inferInstance
  set Y := Yp P m θ ε with hY
  set θm := P[θ | m] with hθm
  have hsΩ : MeasurableSet s := H.m_le _ hs
  have hθm𝒜 : Measurable[𝒜] θm := stronglyMeasurable_condExp.measurable.mono H.m_le_A le_rfl
  have hs𝒜 : MeasurableSet[𝒜] s := H.m_le_A _ hs
  have hf : Integrable (fun ω => θ ω - θm ω) P := H.θ_int.sub integrable_condExp
  have hatan_b : ∀ᵐ ω ∂P, ‖arctan (θ ω + ε ω)‖ ≤ π / 2 := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact abs_arctan_le _
  have hk_b : ∀ᵐ ω ∂P, ‖kfun L (θ ω)‖ ≤ π / 2 := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact abs_kfun_le L _
  have hfa : Integrable (s.indicator (fun ω => (θ ω - θm ω) * arctan (θ ω + ε ω))) P :=
    (hf.mul_bdd H.atan_measΩ.aestronglyMeasurable hatan_b).indicator hsΩ
  have hfk : Integrable (s.indicator (fun ω => (θ ω - θm ω) * kfun L (θ ω))) P :=
    (hf.mul_bdd ((measurable_kfun L).comp H.θ_measΩ).aestronglyMeasurable hk_b).indicator hsΩ
  -- Step 1: freezing `ε`.
  have step1 : ∫ ω, s.indicator (fun ω => (θ ω - θm ω) * kfun L (θ ω)) ω ∂P =
      ∫ ω, s.indicator (fun ω => (θ ω - θm ω) * arctan (θ ω + ε ω)) ω ∂P := by
    have hW : Measurable[𝒜] (fun ω => (s.indicator (fun ω => θ ω - θm ω) ω, θ ω)) :=
      ((H.θ_meas.sub hθm𝒜).indicator hs𝒜).prodMk H.θ_meas
    have hF : Measurable (fun p : (ℝ × ℝ) × ℝ => p.1.1 * arctan (p.1.2 + p.2)) :=
      measurable_fst.fst.mul (continuous_arctan.measurable.comp
        (measurable_fst.snd.add measurable_snd))
    have e1 : (fun ω => (fun p : (ℝ × ℝ) × ℝ => p.1.1 * arctan (p.1.2 + p.2))
        ((s.indicator (fun ω => θ ω - θm ω) ω, θ ω), ε ω)) =
        s.indicator (fun ω => (θ ω - θm ω) * arctan (θ ω + ε ω)) := by
      ext ω
      by_cases hω : ω ∈ s <;> simp [hω]
    have hint : Integrable (fun ω => (fun p : (ℝ × ℝ) × ℝ => p.1.1 * arctan (p.1.2 + p.2))
        ((s.indicator (fun ω => θ ω - θm ω) ω, θ ω), ε ω)) P := by
      rw [e1]; exact hfa
    have key := integral_freeze H.A_le H.ε_meas H.ε_indep hW hF hint
    rw [e1] at key
    rw [key, hL]
    congr 1
    ext ω
    simp only
    rw [integral_const_mul]
    by_cases hω : ω ∈ s <;> simp [hω, kfun]
  -- Step 2: replace `θ` by `Y` and drop the `k(θ_m)` term.
  set φa := s.indicator (fun ω => arctan (θ ω + ε ω)) with hφa
  set φk := s.indicator (fun ω => kfun L (θm ω)) with hφk
  have hφam : StronglyMeasurable[gsig m θ ε] φa :=
    (continuous_arctan.measurable.comp s_meas_g).stronglyMeasurable.indicator (m_le_g _ hs)
  have hφkm : StronglyMeasurable[m] φk :=
    ((measurable_kfun L).comp stronglyMeasurable_condExp.measurable).stronglyMeasurable.indicator
      hs
  have hφab : ∀ ω, |φa ω| ≤ π / 2 :=
    abs_indicator_le (by positivity) fun ω => abs_arctan_le _
  have hφkb : ∀ ω, |φk ω| ≤ π / 2 :=
    abs_indicator_le (by positivity) fun ω => abs_kfun_le L _
  have hφkn : StronglyMeasurable[m] (fun ω => -φk ω) := hφkm.neg
  have i2 : ∫ ω, φa ω * (θ ω - Y ω) ∂P = 0 :=
    integral_mul_sub_condExp H.g_le H.θ_int hφam hφab
  have i3 : ∫ ω, (-φk ω) * (θ ω - θm ω) ∂P = 0 :=
    integral_mul_sub_condExp H.m_le H.θ_int hφkn (fun ω => by rw [abs_neg]; exact hφkb ω)
  have hb2 : ∀ᵐ ω ∂P, ‖φa ω‖ ≤ π / 2 := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hφab ω
  have hb3 : ∀ᵐ ω ∂P, ‖-φk ω‖ ≤ π / 2 := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_neg]; exact hφkb ω
  have hθY : Integrable (fun ω => θ ω - Y ω) P := H.θ_int.sub integrable_condExp
  have a1 : Integrable (fun ω => s.indicator (fun ω => (θ ω - θm ω) * kfun L (θ ω)) ω -
      s.indicator (fun ω => (θ ω - θm ω) * arctan (θ ω + ε ω)) ω) P := hfk.sub hfa
  have a2 : Integrable (fun ω => φa ω * (θ ω - Y ω)) P :=
    hθY.bdd_mul (hφam.mono H.g_le).aestronglyMeasurable hb2
  have a3 : Integrable (fun ω => (-φk ω) * (θ ω - θm ω)) P :=
    hf.bdd_mul (hφkn.mono H.m_le).aestronglyMeasurable hb3
  have i1 : ∫ ω, (s.indicator (fun ω => (θ ω - θm ω) * kfun L (θ ω)) ω -
      s.indicator (fun ω => (θ ω - θm ω) * arctan (θ ω + ε ω)) ω) ∂P = 0 := by
    rw [integral_sub hfk hfa, step1, sub_self]
  have hn : Integrable (s.indicator (nfun P m θ L)) P := (H.integrable_n L).indicator hsΩ
  have hq : Integrable (s.indicator (fun ω => (Y ω - θm ω) * arctan (θ ω + ε ω))) P :=
    ((integrable_condExp.sub integrable_condExp).mul_bdd H.atan_measΩ.aestronglyMeasurable
      hatan_b).indicator hsΩ
  have key : ∀ ω, s.indicator (nfun P m θ L) ω -
      s.indicator (fun ω => (Y ω - θm ω) * arctan (θ ω + ε ω)) ω =
      (s.indicator (fun ω => (θ ω - θm ω) * kfun L (θ ω)) ω -
        s.indicator (fun ω => (θ ω - θm ω) * arctan (θ ω + ε ω)) ω) +
      φa ω * (θ ω - Y ω) + (-φk ω) * (θ ω - θm ω) := by
    intro ω
    by_cases hω : ω ∈ s
    · simp only [hφa, hφk, Set.indicator_of_mem hω, nfun, hθm]
      ring
    · simp only [hφa, hφk, Set.indicator_of_notMem hω]
      ring
  rw [← integral_indicator hsΩ, ← integral_indicator hsΩ]
  have : ∫ ω, s.indicator (nfun P m θ L) ω ∂P -
      ∫ ω, s.indicator (fun ω => (Y ω - θm ω) * arctan (θ ω + ε ω)) ω ∂P = 0 := by
    rw [← integral_sub hn hq, integral_congr_ae (Eventually.of_forall key)]
    exact integral_add3_eq_zero a1 a2 a3 i1 i2 i3
  linarith

/-- `N ≤ (π/2)/(n+1) + (π/2)(n+1) M`. -/
lemma condExp_N_le [IsProbabilityMeasure P] {L : Measure ℝ} (hL : P.map ε = L) (n : ℕ) :
    ∀ᵐ ω ∂P, (P[nfun P m θ L | m]) ω ≤
      π / 2 / ((n : ℝ) + 1) + π / 2 * ((n : ℝ) + 1) * (P[gYfun P m θ ε | m]) ω := by
  have hLp : IsProbabilityMeasure L := hL ▸ inferInstance
  have hatan_b : ∀ᵐ ω ∂P, ‖arctan (θ ω + ε ω)‖ ≤ π / 2 := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact abs_arctan_le _
  have hq : Integrable (fun ω => (Yp P m θ ε ω - (P[θ | m]) ω) * arctan (θ ω + ε ω)) P :=
    ((integrable_condExp.sub integrable_condExp).mul_bdd H.atan_measΩ.aestronglyMeasurable
      hatan_b)
  have e : P[nfun P m θ L | m] =ᵐ[P]
      P[fun ω => (Yp P m θ ε ω - (P[θ | m]) ω) * arctan (θ ω + ε ω) | m] :=
    condExp_congr_setIntegral H.m_le (H.integrable_n L) hq fun s hs => H.setIntegral_eps hL hs
  have hmono : P[fun ω => (Yp P m θ ε ω - (P[θ | m]) ω) * arctan (θ ω + ε ω) | m] ≤ᵐ[P]
      P[fun ω => π / 2 / ((n : ℝ) + 1) + π / 2 * ((n : ℝ) + 1) * gYfun P m θ ε ω | m] := by
    refine condExp_mono hq ((integrable_const _).add (H.integrable_gY.const_mul _))
      (Eventually.of_forall fun ω => ?_)
    simp only [gYfun]
    set x := Yp P m θ ε ω - (P[θ | m]) ω
    have h1 : x * arctan (θ ω + ε ω) ≤ |x| * (π / 2) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_arctan_le _) (abs_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right (abs_le_gfun x n) (by positivity : (0 : ℝ) ≤ π / 2)
    calc x * arctan (θ ω + ε ω) ≤ |x| * (π / 2) := h1
      _ ≤ (1 / ((n : ℝ) + 1) + ((n : ℝ) + 1) * gfun x) * (π / 2) := h2
      _ = π / 2 / ((n : ℝ) + 1) + π / 2 * ((n : ℝ) + 1) * gfun x := by ring
  have aff := condExp_affine1 H.m_le H.integrable_gY (π / 2 / ((n : ℝ) + 1))
    (π / 2 * ((n : ℝ) + 1))
  filter_upwards [e, hmono, aff] with ω h1 h2 h3
  rw [h1]
  rw [h3] at h2
  exact h2

/-- On `{|θ_m| ≤ R}`, `c M ≤ J`. -/
lemma condExp_J_ge [IsProbabilityMeasure P] {G : Measure ℝ} (hG : P.map v = G) {ψ : ℝ → ℝ}
    (hGψ : G = volume.withDensity (fun x => ENNReal.ofReal (ψ x))) (d : ℝ) {R c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ x ∈ Set.Icc (d - R - 1) (d + R + 1), c ≤ ψ x) :
    ∀ᵐ ω ∂P, |(P[θ | m]) ω| ≤ R →
      c * (P[gYfun P m θ ε | m]) ω ≤ (P[jfun P m θ ε G d | m]) ω := by
  have hGp : IsProbabilityMeasure G := hG ▸ inferInstance
  have hS : MeasurableSet[m] {ω | |(P[θ | m]) ω| ≤ R} :=
    measurableSet_le (continuous_abs.measurable.comp stronglyMeasurable_condExp.measurable)
      measurable_const
  have h1 := condExp_le_on H.m_le (H.integrable_gY.const_mul c) (H.integrable_j G d) hS
    (fun ω hω => mul_sub_ge_gfun (hfun_mono G d) (hfun_inc G hGψ hc0 hc) hω _)
  have h2 := condExp_smul (μ := P) c (gYfun P m θ ε) m
  filter_upwards [h1, h2] with ω a b hω
  have := a hω
  rw [show (fun ω => c * gYfun P m θ ε ω) = c • gYfun P m θ ε from rfl, b] at this
  exact this

/-- On `{|θ_m| ≤ R}`, `c'_R L ≤ N`. -/
lemma condExp_N_ge [IsProbabilityMeasure P] {L : Measure ℝ} (hL : P.map ε = L) (R : ℝ) :
    ∀ᵐ ω ∂P, |(P[θ | m]) ω| ≤ R →
      kconst L R * (P[gθfun P m θ | m]) ω ≤ (P[nfun P m θ L | m]) ω := by
  have hLp : IsProbabilityMeasure L := hL ▸ inferInstance
  have hS : MeasurableSet[m] {ω | |(P[θ | m]) ω| ≤ R} :=
    measurableSet_le (continuous_abs.measurable.comp stronglyMeasurable_condExp.measurable)
      measurable_const
  have h1 := condExp_le_on H.m_le (H.integrable_gθ.const_mul (kconst L R)) (H.integrable_n L) hS
    (fun ω hω => mul_sub_ge_gfun (kfun_mono L) (kfun_inc L R) hω _)
  have h2 := condExp_smul (μ := P) (kconst L R) (gθfun P m θ) m
  filter_upwards [h1, h2] with ω a b hω
  have := a hω
  rw [show (fun ω => kconst L R * gθfun P m θ ω) = kconst L R • gθfun P m θ from rfl, b] at this
  exact this

/-- `v + Y ≠ d` almost surely. -/
lemma ae_ne [IsProbabilityMeasure P] {ψ : ℝ → ℝ}
    (hG : P.map v = volume.withDensity (fun x => ENNReal.ofReal (ψ x))) (d : ℝ) :
    ∀ᵐ ω ∂P, v ω + Yp P m θ ε ω ≠ d := by
  set Y := Yp P m θ ε with hY
  have hY𝒦 : Measurable[𝒜 ⊔ MeasurableSpace.comap ε inferInstance] Y :=
    stronglyMeasurable_condExp.measurable.mono H.g_le_K le_rfl
  have hF : Measurable (fun p : ℝ × ℝ => if p.2 + p.1 = d then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun (measurable_snd.add measurable_fst) measurable_const)
      measurable_const measurable_const
  have hE : MeasurableSet {ω | v ω + Y ω = d} :=
    measurableSet_eq_fun (H.v_meas.add H.Y_measΩ) measurable_const
  have e2 : (fun ω => (fun p : ℝ × ℝ => if p.2 + p.1 = d then (1 : ℝ) else 0) (Y ω, v ω)) =
      {ω | v ω + Y ω = d}.indicator 1 := by
    ext ω
    by_cases h : v ω + Y ω = d <;> simp [h]
  have hint : Integrable (fun ω => (fun p : ℝ × ℝ => if p.2 + p.1 = d then (1 : ℝ) else 0)
      (Y ω, v ω)) P := by
    rw [e2]; exact (integrable_const 1).indicator hE
  have key := integral_freeze H.K_le H.v_meas H.v_indep hY𝒦 hF hint
  have inner : ∀ y : ℝ, ∫ x, (if x + y = d then (1 : ℝ) else 0) ∂(P.map v) = 0 := by
    intro y
    have e : (fun x : ℝ => if x + y = d then (1 : ℝ) else 0) = ({d - y} : Set ℝ).indicator 1 := by
      ext x
      by_cases h : x + y = d
      · have : x = d - y := by linarith
        simp [this]
      · have : x ≠ d - y := fun hx => h (by rw [hx]; ring)
        simp [this, h]
    rw [e, integral_indicator_one (measurableSet_singleton _), hG, measureReal_def,
      withDensity_apply _ (measurableSet_singleton _),
      Measure.restrict_eq_zero.2 Real.volume_singleton, lintegral_zero_measure,
      ENNReal.toReal_zero]
  simp only [inner, integral_zero] at key
  rw [e2, integral_indicator_one hE, measureReal_eq_zero_iff] at key
  exact measure_eq_zero_iff_ae_notMem.1 key

/-- **On the revealed set, `J ≤ D`.** -/
lemma condExp_J_le [IsProbabilityMeasure P] {G : Measure ℝ} (hG : P.map v = G) (d : ℝ)
    (hmm' : m ≤ m') (hm' : m' ≤ mΩ) {Rev A : Set Ω} (hRev : MeasurableSet[m] Rev)
    (hA : MeasurableSet[m'] A) (hAeq : A =ᵐ[P] ({ω | d < v ω + Yp P m θ ε ω} ∩ Rev)) :
    ∀ᵐ ω ∂P, ω ∈ Rev →
      (P[jfun P m θ ε G d | m]) ω ≤ (P[fun ω => |(P[θ | m']) ω - (P[θ | m]) ω| | m]) ω := by
  have hGp : IsProbabilityMeasure G := hG ▸ inferInstance
  have hRevΩ : MeasurableSet Rev := H.m_le _ hRev
  have hAΩ : MeasurableSet A := hm' _ hA
  have hf : Integrable (fun ω => θ ω - (P[θ | m]) ω) P := H.θ_int.sub integrable_condExp
  have e1 := condExp_indicator (m := m) (H.integrable_j G d) hRev
  have e2 : P[Rev.indicator (jfun P m θ ε G d) | m] =ᵐ[P]
      P[A.indicator (fun ω => θ ω - (P[θ | m]) ω) | m] := by
    refine condExp_congr_setIntegral H.m_le ((H.integrable_j G d).indicator hRevΩ)
      (hf.indicator hAΩ) fun s hs => ?_
    rw [setIntegral_indicator hRevΩ, ← H.setIntegral_reveal hG d (hs.inter hRev),
      ← setIntegral_indicator hRevΩ]
    refine setIntegral_congr_ae (H.m_le _ hs) ?_
    filter_upwards [hAeq] with ω hω _
    by_cases hA' : ω ∈ A
    · have h' : ω ∈ {ω | d < v ω + Yp P m θ ε ω} ∩ Rev := Eq.mp hω hA'
      rw [Set.indicator_of_mem hA', Set.indicator_of_mem h'.2, Set.indicator_of_mem h'.1]
    · have h' : ω ∉ {ω | d < v ω + Yp P m θ ε ω} ∩ Rev := fun h => hA' (Eq.mpr hω h)
      rw [Set.indicator_of_notMem hA']
      by_cases hR : ω ∈ Rev
      · rw [Set.indicator_of_mem hR, Set.indicator_of_notMem (fun hD => h' ⟨hD, hR⟩)]
      · rw [Set.indicator_of_notMem hR]
  have e3 := condExp_indicator_sub_le (g := P[θ | m]) hmm' hm' H.θ_int integrable_condExp hA
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hω
  calc (P[jfun P m θ ε G d | m]) ω = Rev.indicator (P[jfun P m θ ε G d | m]) ω :=
        (Set.indicator_of_mem hω _).symm
    _ = (P[Rev.indicator (jfun P m θ ε G d) | m]) ω := h1.symm
    _ = (P[A.indicator (fun ω => θ ω - (P[θ | m]) ω) | m]) ω := h2
    _ ≤ _ := h3

end PeriodHyp

end Period

end CC.LearnTheta.ClaimAux
