import ConformityConcerns.LearnTheta.ClaimAux.Ineq
import ConformityConcerns.LearnTheta.ClaimAux.Cond
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# One period of the Claim of Proposition A5

For one period (public information `m = ℱ_t`, everything realised `𝒜 = 𝒜_t`, signal noise `ε`,
preference shock `v`), with `Y = E(θ | m ⊔ σ(θ + ε))` and `θ_m = E(θ | m)`:

* `h_d(y) = G(Ioi (d - y))` and `k(x) = ∫ arctan (x + e) dL(e)`, both monotone, with increments
  bounded below on bounded intervals;
* revelation identity: `∫_s 1{d < v + Y}(θ - θ_m) = ∫_s (Y - θ_m)(h_d(Y) - h_d(θ_m))`, `s ∈ m`;
* the `ε`-step: `E_m[(θ - θ_m)(k(θ) - k(θ_m))] = E_m[(Y - θ_m) arctan(θ + ε)]`;
* lower bounds by `g(Y - θ_m)` and `g(θ - θ_m)` on `{|θ_m| ≤ R}`;
* `P(v + Y = d) = 0`.
-/

namespace CC.LearnTheta.ClaimAux

open MeasureTheory ProbabilityTheory Filter Topology Real

set_option warn.classDefReducibility false

/-! ### The functions `h_d` and `k` -/

/-- `h_d(y) = G(Ioi (d - y))`. -/
noncomputable def hfun (G : Measure ℝ) (d y : ℝ) : ℝ := G.real (Set.Ioi (d - y))

section hfun

variable (G : Measure ℝ) [IsProbabilityMeasure G] (d : ℝ)

lemma hfun_mono : Monotone (hfun G d) := fun a b hab =>
  measureReal_mono (Set.Ioi_subset_Ioi (by linarith))

omit [IsProbabilityMeasure G] in
lemma hfun_nonneg (y : ℝ) : 0 ≤ hfun G d y := measureReal_nonneg

lemma hfun_le_one (y : ℝ) : hfun G d y ≤ 1 := measureReal_le_one

lemma abs_hfun_sub_le (y z : ℝ) : |hfun G d y - hfun G d z| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hfun_nonneg G d y, hfun_le_one G d y, hfun_nonneg G d z,
    hfun_le_one G d z]

lemma abs_hfun_le (y : ℝ) : |hfun G d y| ≤ 1 := by
  rw [abs_of_nonneg (hfun_nonneg G d y)]; exact hfun_le_one G d y

lemma measurable_hfun : Measurable (hfun G d) := (hfun_mono G d).measurable

omit [IsProbabilityMeasure G] in
lemma integral_ite_lt (a y : ℝ) :
    ∫ x, (if d < x + y then a else 0) ∂G = hfun G d y * a := by
  have e : (fun x => if d < x + y then a else 0) = (Set.Ioi (d - y)).indicator (fun _ => a) := by
    ext x
    simp only [Set.indicator_apply, Set.mem_Ioi, sub_lt_iff_lt_add]
  rw [e, integral_indicator measurableSet_Ioi, setIntegral_const, smul_eq_mul]
  rfl

end hfun

lemma hfun_inc {ψ : ℝ → ℝ} (G : Measure ℝ) [IsFiniteMeasure G]
    (hG : G = volume.withDensity (fun x => ENNReal.ofReal (ψ x))) {d R c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x ∈ Set.Icc (d - R - 1) (d + R + 1), c ≤ ψ x) (a b : ℝ) (hab : a ≤ b)
    (ha : |a| ≤ R + 1) (hb : |b| ≤ R + 1) : c * (b - a) ≤ hfun G d b - hfun G d a := by
  have e : hfun G d b - hfun G d a = G.real (Set.Ioc (d - b) (d - a)) := by
    unfold hfun
    rw [← Set.Ioi_sdiff_Ioi, measureReal_sdiff (Set.Ioi_subset_Ioi (by linarith)) measurableSet_Ioi]
  rw [e]
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  obtain ⟨hb1, hb2⟩ := abs_le.1 hb
  have hlow : ENNReal.ofReal (c * (b - a)) ≤ G (Set.Ioc (d - b) (d - a)) := by
    rw [hG, withDensity_apply _ measurableSet_Ioc]
    calc ENNReal.ofReal (c * (b - a))
        = ∫⁻ _ in Set.Ioc (d - b) (d - a), ENNReal.ofReal c := by
          rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul hc0]
          congr 1; ring
      _ ≤ ∫⁻ x in Set.Ioc (d - b) (d - a), ENNReal.ofReal (ψ x) := by
          refine setLIntegral_mono' measurableSet_Ioc fun x hx =>
            ENNReal.ofReal_le_ofReal (hc x ⟨?_, ?_⟩)
          · linarith [hx.1]
          · linarith [hx.2]
  have := ENNReal.toReal_mono (measure_ne_top G _) hlow
  rwa [ENNReal.toReal_ofReal (mul_nonneg hc0 (by linarith))] at this

/-- `k(x) = ∫ arctan (x + e) dL(e)`. -/
noncomputable def kfun (L : Measure ℝ) (x : ℝ) : ℝ := ∫ e, arctan (x + e) ∂L

/-- `c'_R = ∫ 1 / (1 + (R + 1 + |e|)²) dL(e)`. -/
noncomputable def kconst (L : Measure ℝ) (R : ℝ) : ℝ := ∫ e, 1 / (1 + (R + 1 + |e|) ^ 2) ∂L

section kfun

variable (L : Measure ℝ) [IsProbabilityMeasure L]

lemma abs_arctan_le (x : ℝ) : |arctan x| ≤ π / 2 :=
  abs_le.2 ⟨(neg_pi_div_two_lt_arctan _).le, (arctan_lt_pi_div_two _).le⟩

lemma integrable_arctan_add (x : ℝ) : Integrable (fun e => arctan (x + e)) L := by
  refine Integrable.of_bound
    (continuous_arctan.comp (continuous_const.add continuous_id)).aestronglyMeasurable (π / 2)
    (Eventually.of_forall fun e => ?_)
  rw [Real.norm_eq_abs]
  exact abs_arctan_le _

lemma kfun_mono : Monotone (kfun L) := fun a b hab =>
  integral_mono (integrable_arctan_add L a) (integrable_arctan_add L b) fun e =>
    arctan_mono (by linarith)

lemma abs_kfun_le (x : ℝ) : |kfun L x| ≤ π / 2 := by
  have := norm_integral_le_of_norm_le_const (μ := L) (f := fun e => arctan (x + e)) (C := π / 2)
    (Eventually.of_forall fun e => by rw [Real.norm_eq_abs]; exact abs_arctan_le _)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

lemma abs_kfun_sub_le (x y : ℝ) : |kfun L x - kfun L y| ≤ π := by
  have h1 := abs_kfun_le L x
  have h2 := abs_kfun_le L y
  calc |kfun L x - kfun L y| ≤ |kfun L x| + |kfun L y| := abs_sub _ _
    _ ≤ π / 2 + π / 2 := add_le_add h1 h2
    _ = π := by ring

lemma measurable_kfun : Measurable (kfun L) := (kfun_mono L).measurable

lemma continuous_kden (R : ℝ) : Continuous fun e : ℝ => 1 / (1 + (R + 1 + |e|) ^ 2) :=
  continuous_const.div (continuous_const.add ((continuous_const.add continuous_abs).pow 2))
    (fun e => by positivity)

lemma integrable_kden (R : ℝ) : Integrable (fun e : ℝ => 1 / (1 + (R + 1 + |e|) ^ 2)) L := by
  refine Integrable.of_bound (continuous_kden R).aestronglyMeasurable 1
    (Eventually.of_forall fun e => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (R + 1 + |e|)]

lemma kconst_pos (R : ℝ) : 0 < kconst L R := by
  unfold kconst
  rw [integral_pos_iff_support_of_nonneg (fun e => by positivity) (integrable_kden L R)]
  have : Function.support (fun e : ℝ => 1 / (1 + (R + 1 + |e|) ^ 2)) = Set.univ := by
    ext e
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    positivity
  rw [this, measure_univ]
  exact one_pos

lemma kfun_inc (R : ℝ) (a b : ℝ) (hab : a ≤ b) (ha : |a| ≤ R + 1) (hb : |b| ≤ R + 1) :
    kconst L R * (b - a) ≤ kfun L b - kfun L a := by
  unfold kfun kconst
  rw [← integral_sub (integrable_arctan_add L b) (integrable_arctan_add L a), ← integral_mul_const]
  refine integral_mono ((integrable_kden L R).mul_const _)
    ((integrable_arctan_add L b).sub (integrable_arctan_add L a)) fun e => ?_
  have hae : |a + e| ≤ R + 1 + |e| := (abs_add_le a e).trans (by linarith)
  have hbe : |b + e| ≤ R + 1 + |e| := (abs_add_le b e).trans (by linarith)
  have := arctan_sub_ge (a := a + e) (b := b + e) (M := R + 1 + |e|) (by linarith) hae hbe
  calc 1 / (1 + (R + 1 + |e|) ^ 2) * (b - a) = ((b + e) - (a + e)) / (1 + (R + 1 + |e|) ^ 2) := by
        ring
    _ ≤ _ := this

end kfun

/-! ### One period -/

/-- `σ(h^t, s_t)`. -/
def gsig {Ω : Type*} (m : MeasurableSpace Ω) (θ ε : Ω → ℝ) : MeasurableSpace Ω :=
  m ⊔ MeasurableSpace.comap (fun ω => θ ω + ε ω) inferInstance

/-- The hypotheses of one period. -/
structure PeriodHyp {Ω : Type*} (m 𝒜 : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (P : Measure Ω) (θ ε v : Ω → ℝ) : Prop where
  m_le_A : m ≤ 𝒜
  A_le : 𝒜 ≤ mΩ
  θ_meas : Measurable[𝒜] θ
  θ_int : Integrable θ P
  ε_meas : Measurable ε
  v_meas : Measurable v
  ε_indep : Indep (MeasurableSpace.comap ε inferInstance) 𝒜 P
  v_indep : Indep (MeasurableSpace.comap v inferInstance)
    (𝒜 ⊔ MeasurableSpace.comap ε inferInstance) P

/-- `|1_s φ| ≤ C`. -/
lemma abs_indicator_le {Ω : Type*} {s : Set Ω} {φ : Ω → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (h : ∀ ω, |φ ω| ≤ C) (ω : Ω) : |s.indicator φ ω| ≤ C := by
  by_cases hω : ω ∈ s
  · rw [Set.indicator_of_mem hω]; exact h ω
  · rw [Set.indicator_of_notMem hω, abs_zero]; exact hC0

/-- `E[φ (f - E(f | m))] = 0` for bounded `m`-measurable `φ`. -/
lemma integral_mul_sub_condExp {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ mΩ) {f φ : Ω → ℝ} (hf : Integrable f P)
    (hφ : StronglyMeasurable[m] φ) {C : ℝ} (hC : ∀ ω, |φ ω| ≤ C) :
    ∫ ω, φ ω * (f ω - (P[f | m]) ω) ∂P = 0 := by
  have hφ' : AEStronglyMeasurable φ P := (hφ.mono hm).aestronglyMeasurable
  have hb : ∀ᵐ ω ∂P, ‖φ ω‖ ≤ C := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω
  simp_rw [mul_sub]
  rw [integral_sub (hf.bdd_mul hφ' hb) (integrable_condExp.bdd_mul hφ' hb),
    integral_mul_condExp hm hf hφ hC, sub_self]

/-- `∫ (f + g + h) = 0` when each integral vanishes. -/
lemma integral_add3_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {f g h : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P) (hh : Integrable h P)
    (h1 : ∫ ω, f ω ∂P = 0) (h2 : ∫ ω, g ω ∂P = 0) (h3 : ∫ ω, h ω ∂P = 0) :
    ∫ ω, f ω + g ω + h ω ∂P = 0 := by
  calc ∫ ω, f ω + g ω + h ω ∂P = ∫ ω, f ω + g ω ∂P + ∫ ω, h ω ∂P := integral_add (hf.add hg) hh
    _ = ∫ ω, f ω ∂P + ∫ ω, g ω ∂P + ∫ ω, h ω ∂P := by rw [integral_add hf hg]
    _ = 0 := by rw [h1, h2, h3]; ring

section Period

variable {Ω : Type*} {m 𝒜 m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {θ ε v : Ω → ℝ}

/-- `Y = E(θ | m ⊔ σ(θ + ε))`. -/
noncomputable def Yp (P : Measure Ω) (m : MeasurableSpace Ω) (θ ε : Ω → ℝ) : Ω → ℝ :=
  P[θ | gsig m θ ε]

/-- `j = (Y - θ_m)(h_d(Y) - h_d(θ_m))`. -/
noncomputable def jfun (P : Measure Ω) (m : MeasurableSpace Ω) (θ ε : Ω → ℝ) (G : Measure ℝ)
    (d : ℝ) (ω : Ω) : ℝ :=
  (Yp P m θ ε ω - (P[θ | m]) ω) * (hfun G d (Yp P m θ ε ω) - hfun G d ((P[θ | m]) ω))

/-- `g(Y - θ_m)`. -/
noncomputable def gYfun (P : Measure Ω) (m : MeasurableSpace Ω) (θ ε : Ω → ℝ) (ω : Ω) : ℝ :=
  gfun (Yp P m θ ε ω - (P[θ | m]) ω)

/-- `(θ - θ_m)(k(θ) - k(θ_m))`. -/
noncomputable def nfun (P : Measure Ω) (m : MeasurableSpace Ω) (θ : Ω → ℝ) (L : Measure ℝ)
    (ω : Ω) : ℝ :=
  (θ ω - (P[θ | m]) ω) * (kfun L (θ ω) - kfun L ((P[θ | m]) ω))

/-- `g(θ - θ_m)`. -/
noncomputable def gθfun (P : Measure Ω) (m : MeasurableSpace Ω) (θ : Ω → ℝ) (ω : Ω) : ℝ :=
  gfun (θ ω - (P[θ | m]) ω)

namespace PeriodHyp

variable (H : PeriodHyp m 𝒜 mΩ P θ ε v)
include H

lemma K_le : 𝒜 ⊔ MeasurableSpace.comap ε inferInstance ≤ mΩ :=
  sup_le H.A_le H.ε_meas.comap_le

omit H in
lemma s_meas_g : Measurable[gsig m θ ε] (fun ω => θ ω + ε ω) :=
  (comap_measurable (fun ω => θ ω + ε ω)).mono le_sup_right le_rfl

lemma g_le_K : gsig m θ ε ≤ 𝒜 ⊔ MeasurableSpace.comap ε inferInstance := by
  refine sup_le (H.m_le_A.trans le_sup_left) (Measurable.comap_le ?_)
  exact (H.θ_meas.mono le_sup_left le_rfl).add ((comap_measurable ε).mono le_sup_right le_rfl)

lemma g_le : gsig m θ ε ≤ mΩ := H.g_le_K.trans H.K_le

lemma m_le : m ≤ mΩ := H.m_le_A.trans H.A_le

omit H in
lemma m_le_g : m ≤ gsig m θ ε := le_sup_left

lemma θ_measΩ : Measurable θ := H.θ_meas.mono H.A_le le_rfl

lemma Y_measΩ : Measurable (Yp P m θ ε) :=
  stronglyMeasurable_condExp.measurable.mono H.g_le le_rfl

lemma θm_measΩ : Measurable (P[θ | m]) :=
  stronglyMeasurable_condExp.measurable.mono H.m_le le_rfl

omit H in
lemma Y_int : Integrable (Yp P m θ ε) P := integrable_condExp

omit H in
lemma θm_int : Integrable (P[θ | m]) P := integrable_condExp

lemma integrable_gY : Integrable (gYfun P m θ ε) P := by
  refine Integrable.mono' ((Y_int (P := P) (m := m) (θ := θ) (ε := ε)).sub
    (θm_int (P := P) (m := m) (θ := θ))).abs
    (continuous_gfun.measurable.comp (H.Y_measΩ.sub H.θm_measΩ)).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, gYfun, abs_of_nonneg (gfun_nonneg _)]
  exact gfun_le_abs _

lemma integrable_gθ : Integrable (gθfun P m θ) P := by
  refine Integrable.mono' (H.θ_int.sub (θm_int (P := P) (m := m) (θ := θ))).abs
    (continuous_gfun.measurable.comp (H.θ_measΩ.sub H.θm_measΩ)).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, gθfun, abs_of_nonneg (gfun_nonneg _)]
  exact gfun_le_abs _

lemma integrable_j (G : Measure ℝ) [IsProbabilityMeasure G] (d : ℝ) :
    Integrable (jfun P m θ ε G d) P :=
  ((Y_int (P := P) (m := m) (θ := θ) (ε := ε)).sub (θm_int (P := P) (m := m) (θ := θ))).mul_bdd
    (((measurable_hfun G d).comp H.Y_measΩ).sub
      ((measurable_hfun G d).comp H.θm_measΩ)).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_hfun_sub_le G d _ _)

lemma integrable_n (L : Measure ℝ) [IsProbabilityMeasure L] : Integrable (nfun P m θ L) P :=
  (H.θ_int.sub (θm_int (P := P) (m := m) (θ := θ))).mul_bdd
    (((measurable_kfun L).comp H.θ_measΩ).sub
      ((measurable_kfun L).comp H.θm_measΩ)).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_kfun_sub_le L _ _)

/-- **Revelation identity.** -/
lemma setIntegral_reveal [IsProbabilityMeasure P] {G : Measure ℝ} (hG : P.map v = G) (d : ℝ)
    {s : Set Ω} (hs : MeasurableSet[m] s) :
    ∫ ω in s, {ω | d < v ω + Yp P m θ ε ω}.indicator (fun ω => θ ω - (P[θ | m]) ω) ω ∂P =
      ∫ ω in s, jfun P m θ ε G d ω ∂P := by
  have hGp : IsProbabilityMeasure G := hG ▸ inferInstance
  set Y := Yp P m θ ε with hY
  set θm := P[θ | m] with hθm
  have hsΩ : MeasurableSet s := H.m_le _ hs
  have hY𝒦 : Measurable[𝒜 ⊔ MeasurableSpace.comap ε inferInstance] Y :=
    stronglyMeasurable_condExp.measurable.mono H.g_le_K le_rfl
  have hθm𝒦 : Measurable[𝒜 ⊔ MeasurableSpace.comap ε inferInstance] θm :=
    stronglyMeasurable_condExp.measurable.mono (H.m_le_A.trans le_sup_left) le_rfl
  have hθ𝒦 : Measurable[𝒜 ⊔ MeasurableSpace.comap ε inferInstance] θ :=
    H.θ_meas.mono le_sup_left le_rfl
  have hs𝒦 : MeasurableSet[𝒜 ⊔ MeasurableSpace.comap ε inferInstance] s :=
    (H.m_le_A.trans le_sup_left) _ hs
  have hD : MeasurableSet {ω | d < v ω + Y ω} :=
    measurableSet_lt measurable_const (H.v_meas.add H.Y_measΩ)
  have hf : Integrable (fun ω => θ ω - θm ω) P := H.θ_int.sub integrable_condExp
  -- Step 1: freezing `v`.
  have step1 : ∫ ω in s, {ω | d < v ω + Y ω}.indicator (fun ω => θ ω - θm ω) ω ∂P =
      ∫ ω in s, hfun G d (Y ω) * (θ ω - θm ω) ∂P := by
    rw [← integral_indicator hsΩ, ← integral_indicator hsΩ]
    have hW : Measurable[𝒜 ⊔ MeasurableSpace.comap ε inferInstance]
        (fun ω => (s.indicator (fun ω => θ ω - θm ω) ω, Y ω)) :=
      ((hθ𝒦.sub hθm𝒦).indicator hs𝒦).prodMk hY𝒦
    have hF : Measurable (fun p : (ℝ × ℝ) × ℝ => if d < p.2 + p.1.2 then p.1.1 else 0) :=
      Measurable.ite (measurableSet_lt measurable_const (measurable_snd.add measurable_fst.snd))
        measurable_fst.fst measurable_const
    have e1 : (fun ω => (fun p : (ℝ × ℝ) × ℝ => if d < p.2 + p.1.2 then p.1.1 else 0)
        ((s.indicator (fun ω => θ ω - θm ω) ω, Y ω), v ω)) =
        s.indicator ({ω | d < v ω + Y ω}.indicator (fun ω => θ ω - θm ω)) := by
      ext ω
      by_cases hω : ω ∈ s <;> by_cases hd : d < v ω + Y ω <;>
        simp [hω, hd]
    have hint : Integrable (fun ω => (fun p : (ℝ × ℝ) × ℝ => if d < p.2 + p.1.2 then p.1.1 else 0)
        ((s.indicator (fun ω => θ ω - θm ω) ω, Y ω), v ω)) P := by
      rw [e1]; exact (hf.indicator hD).indicator hsΩ
    have key := integral_freeze H.K_le H.v_meas H.v_indep hW hF hint
    rw [e1] at key
    rw [key, hG]
    congr 1
    ext ω
    simp only
    rw [integral_ite_lt]
    by_cases hω : ω ∈ s <;> simp [hω]
  rw [step1, ← integral_indicator hsΩ, ← integral_indicator hsΩ]
  -- Step 2: replace `θ` by `Y` and by `θ_m`.
  set φ1 := s.indicator (fun ω => hfun G d (Y ω)) with hφ1
  set φ2 := s.indicator (fun ω => hfun G d (θm ω)) with hφ2
  have hφ1m : StronglyMeasurable[gsig m θ ε] φ1 :=
    ((measurable_hfun G d).comp stronglyMeasurable_condExp.measurable).stronglyMeasurable.indicator
      (m_le_g _ hs)
  have hφ2m : StronglyMeasurable[m] φ2 :=
    ((measurable_hfun G d).comp stronglyMeasurable_condExp.measurable).stronglyMeasurable.indicator
      hs
  have hφ1b : ∀ ω, |φ1 ω| ≤ 1 := abs_indicator_le zero_le_one fun ω => abs_hfun_le G d _
  have hφ2b : ∀ ω, |φ2 ω| ≤ 1 := abs_indicator_le zero_le_one fun ω => abs_hfun_le G d _
  have hφ1n : StronglyMeasurable[gsig m θ ε] (fun ω => -φ1 ω) := hφ1m.neg
  have hφ2n : StronglyMeasurable[m] (fun ω => -φ2 ω) := hφ2m.neg
  have i1 : ∫ ω, (-φ1 ω) * (θ ω - Y ω) ∂P = 0 :=
    integral_mul_sub_condExp H.g_le H.θ_int hφ1n (fun ω => by rw [abs_neg]; exact hφ1b ω)
  have i2 : ∫ ω, φ2 ω * (θ ω - Y ω) ∂P = 0 :=
    integral_mul_sub_condExp H.g_le H.θ_int (hφ2m.mono m_le_g) hφ2b
  have i3 : ∫ ω, (-φ2 ω) * (θ ω - θm ω) ∂P = 0 :=
    integral_mul_sub_condExp H.m_le H.θ_int hφ2n (fun ω => by rw [abs_neg]; exact hφ2b ω)
  have hb1 : ∀ᵐ ω ∂P, ‖-φ1 ω‖ ≤ 1 := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_neg]; exact hφ1b ω
  have hb2 : ∀ᵐ ω ∂P, ‖φ2 ω‖ ≤ 1 := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hφ2b ω
  have hb3 : ∀ᵐ ω ∂P, ‖-φ2 ω‖ ≤ 1 := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_neg]; exact hφ2b ω
  have hθY : Integrable (fun ω => θ ω - Y ω) P := H.θ_int.sub integrable_condExp
  have a1 : Integrable (fun ω => (-φ1 ω) * (θ ω - Y ω)) P :=
    hθY.bdd_mul (hφ1n.mono H.g_le).aestronglyMeasurable hb1
  have a2 : Integrable (fun ω => φ2 ω * (θ ω - Y ω)) P :=
    hθY.bdd_mul (hφ2m.mono H.m_le).aestronglyMeasurable hb2
  have a3 : Integrable (fun ω => (-φ2 ω) * (θ ω - θm ω)) P :=
    hf.bdd_mul (hφ2n.mono H.m_le).aestronglyMeasurable hb3
  have hk : Integrable (s.indicator (fun ω => hfun G d (Y ω) * (θ ω - θm ω))) P :=
    (hf.bdd_mul ((measurable_hfun G d).comp H.Y_measΩ).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact abs_hfun_le G d _)).indicator hsΩ
  have hj : Integrable (s.indicator (jfun P m θ ε G d)) P := (H.integrable_j G d).indicator hsΩ
  have key : ∀ ω, s.indicator (jfun P m θ ε G d) ω -
      s.indicator (fun ω => hfun G d (Y ω) * (θ ω - θm ω)) ω =
      (-φ1 ω) * (θ ω - Y ω) + φ2 ω * (θ ω - Y ω) + (-φ2 ω) * (θ ω - θm ω) := by
    intro ω
    by_cases hω : ω ∈ s
    · simp only [hφ1, hφ2, Set.indicator_of_mem hω, jfun, hY]
      ring
    · simp only [hφ1, hφ2, Set.indicator_of_notMem hω]
      ring
  have : ∫ ω, s.indicator (jfun P m θ ε G d) ω ∂P -
      ∫ ω, s.indicator (fun ω => hfun G d (Y ω) * (θ ω - θm ω)) ω ∂P = 0 := by
    rw [← integral_sub hj hk, integral_congr_ae (Eventually.of_forall key)]
    exact integral_add3_eq_zero a1 a2 a3 i1 i2 i3
  linarith

end PeriodHyp

end Period

end CC.LearnTheta.ClaimAux
