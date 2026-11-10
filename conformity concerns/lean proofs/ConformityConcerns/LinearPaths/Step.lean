import ConformityConcerns.Bridge.BeliefsCore

/-!
# One step of public updating

At a history `h` with public beliefs `N(m, S)`, the period outcome `((θ, μ), (ε, ν))` has law
`periodLaw m S`. If the public observes `y = k Z + b` with `k ≥ 0`, the posterior of `(θ, μ)` is
`N(nextPar m S γ k b y)`: after observing `Z` if `k > 0` (`posterior_after_reveal`), and
unchanged if `k = 0` (`fiber_law`). `step_law` integrates this over the history (with an
independent next weight `g`) to get the posterior at the next history.
-/

namespace CC.LinearPaths

open MeasureTheory ProbabilityTheory
open CC.Bridge
open scoped ENNReal

/-- Posterior parameters after observing `y = k Z + b`: as after observing `Z` if `k > 0`,
unchanged otherwise. -/
noncomputable def nextPar (m : E2) (S : M2) (γ k b y : ℝ) : E2 × M2 :=
  if 0 < k then (regC m S γ + ((y - b) / k) • regK S γ, kalman S γ) else (m, S)

lemma nextPar_pos {m : E2} {S : M2} {γ k b y : ℝ} (hk : 0 < k) :
    nextPar m S γ k b y = (regC m S γ + ((y - b) / k) • regK S γ, kalman S γ) := by
  simp only [nextPar, hk, ↓reduceIte]

lemma nextPar_of_not_pos {m : E2} {S : M2} {γ k b y : ℝ} (hk : ¬ 0 < k) :
    nextPar m S γ k b y = (m, S) := by
  simp only [nextPar, hk, ↓reduceIte]

lemma nextPar_psd {m : E2} {S : M2} (hS : S.PosSemidef) (γ k b y : ℝ) :
    (nextPar m S γ k b y).2.PosSemidef := by
  unfold nextPar
  split_ifs
  · exact cond_kalman_posSemidef hS γ
  · exact hS

section Meas

variable {β : Type*} [MeasurableSpace β]

lemma measurable_regC {m : β → E2} {S : β → M2} {γ : β → ℝ} (hm : Measurable m)
    (hS : Measurable S) (hγ : Measurable γ) : Measurable (fun x => regC (m x) (S x) (γ x)) := by
  unfold regC
  exact hm.sub (((hγ.mul (br_meas_coord hm 0)).add (br_meas_coord hm 1)).smul
    (br_meas_regK hS hγ))

lemma measurable_nextPar {m : β → E2} {S : β → M2} {γ k b y : β → ℝ} (hm : Measurable m)
    (hS : Measurable S) (hγ : Measurable γ) (hk : Measurable k) (hb : Measurable b)
    (hy : Measurable y) :
    Measurable (fun x => nextPar (m x) (S x) (γ x) (k x) (b x) (y x)) := by
  unfold nextPar
  refine Measurable.ite (measurableSet_lt measurable_const hk) ?_ (hm.prodMk hS)
  exact ((measurable_regC hm hS hγ).add (((hy.sub hb).div hk).smul (br_meas_regK hS hγ))).prodMk
    (br_meas_kalman hS hγ)

lemma measurable_Zof_par {m : β → E2} {S : β → M2} {γ : β → ℝ} {w : β → Ω₂}
    (hm : Measurable m) (hS : Measurable S) (hγ : Measurable γ) (hw : Measurable w) :
    Measurable (fun x => Zof (m x) (S x) (γ x) (w x)) := by
  have hpi : Measurable (fun x => privInfo (w x)) := measurable_privInfo.comp hw
  have p0 := br_meas_coord hpi 0
  have p1 := br_meas_coord hpi 1
  have m0 := br_meas_coord hm 0
  have m1 := br_meas_coord hm 1
  have k0 := br_meas_gainK hS 0 0
  have k1 := br_meas_gainK hS 0 1
  unfold Zof
  fun_prop

end Meas

/-- The Gaussian kernel `h ↦ N(p h)`. -/
noncomputable def gaussK {H : Type*} [MeasurableSpace H] (p : H → E2 × M2) (hp : Measurable p) :
    Kernel H E2 where
  toFun h := multivariateGaussian (p h).1 (p h).2
  measurable' := measurable_multivariateGaussian.comp hp

instance {H : Type*} [MeasurableSpace H] (p : H → E2 × M2) (hp : Measurable p) :
    IsMarkovKernel (gaussK p hp) :=
  ⟨fun h => by
    change IsProbabilityMeasure (multivariateGaussian (p h).1 (p h).2)
    infer_instance⟩

lemma gaussK_apply {H : Type*} [MeasurableSpace H] (p : H → E2 × M2) (hp : Measurable p)
    (h : H) : gaussK p hp h = multivariateGaussian (p h).1 (p h).2 := rfl

/-- **Bayes' rule in one period.** Observing `y = k Z + b` (`k ≥ 0`), the posterior of `(θ, μ)` is
`N(nextPar m S γ k b y)`. -/
theorem fiber_law {m : E2} {S : M2} (hS : S.PosSemidef) (γ k b : ℝ) (hk : 0 ≤ k) {A : Set ℝ}
    {B : Set E2} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    periodLaw m S {w | k * Zof m S γ w + b ∈ A ∧ w.1 ∈ B} =
      ∫⁻ w, A.indicator (fun y => multivariateGaussian (nextPar m S γ k b y).1
        (nextPar m S γ k b y).2 B) (k * Zof m S γ w + b) ∂(periodLaw m S) := by
  have hZ : Measurable (Zof m S γ) :=
    measurable_Zof_par measurable_const measurable_const measurable_const measurable_id
  have hYm : Measurable (fun w => k * Zof m S γ w + b) := (measurable_const.mul hZ).add_const b
  have hN : Measurable (fun y => multivariateGaussian (nextPar m S γ k b y).1
      (nextPar m S γ k b y).2 B) :=
    (Measure.measurable_coe hB).comp (measurable_multivariateGaussian.comp
      (measurable_nextPar measurable_const measurable_const measurable_const measurable_const
        measurable_const measurable_id))
  rcases hk.lt_or_eq with hk | hk
  · set Y : Ω₂ → ℝ := fun w => k * Zof m S γ w + b with hY
    set Rr := resZ m S γ with hRr
    set M : ℝ → E2 := fun y => regC m S γ + ((y - b) / k) • regK S γ with hM
    have hRm : Measurable Rr := by
      simp only [hRr]
      exact (measurable_fst.sub measurable_const).sub (hZ.smul measurable_const)
    have hMm : Measurable M :=
      measurable_const.add (((measurable_id.sub measurable_const).div_const k).smul
        measurable_const)
    have hindY : IndepFun Rr Y (periodLaw m S) :=
      (indep_resZ hS γ).comp measurable_id ((measurable_const.mul measurable_id).add_const b)
    have hprod : (periodLaw m S).map (fun w => (Y w, Rr w)) =
        ((periodLaw m S).map Y).prod (multivariateGaussian 0 (kalman S γ)) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hRm.aemeasurable).1
        hindY.symm, law_resZ hS γ]
    have hw : ∀ w : Ω₂, w.1 = Rr w + M (Y w) := by
      intro w
      have hz : (k * Zof m S γ w + b - b) / k = Zof m S γ w := by field_simp; ring
      simp only [hRr, resZ, hM, hY, hz]
      abel
    set D : Set (ℝ × E2) := {q | q.1 ∈ A ∧ q.2 + M q.1 ∈ B} with hD
    have hDm : MeasurableSet D :=
      (measurable_fst hA).inter ((measurable_snd.add (hMm.comp measurable_fst)) hB)
    have hset : {w : Ω₂ | k * Zof m S γ w + b ∈ A ∧ w.1 ∈ B} = (fun w => (Y w, Rr w)) ⁻¹' D := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, hD]
      rw [← hw w]
    rw [hset, ← Measure.map_apply (hYm.prodMk hRm) hDm, hprod, Measure.prod_apply hDm,
      ← lintegral_map (hN.indicator hA) hYm]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ A
    · have hpre : Prod.mk y ⁻¹' D = (fun u : E2 => u + M y) ⁻¹' B := by
        ext u; simp [hD, hy]
      rw [hpre, Set.indicator_of_mem hy, ← Measure.map_apply (measurable_add_const _) hB,
        mvG_map_add, nextPar_pos hk]
    · have hpre : Prod.mk y ⁻¹' D = ∅ := by
        ext u; simp [hD, hy]
      rw [hpre, Set.indicator_of_notMem hy, measure_empty]
  · subst hk
    have hnp : ∀ y, nextPar m S γ 0 b y = (m, S) := fun y => nextPar_of_not_pos (lt_irrefl 0)
    simp only [zero_mul, zero_add, hnp]
    by_cases hb : b ∈ A
    · have hs : {w : Ω₂ | b ∈ A ∧ w.1 ∈ B} = B ×ˢ Set.univ := by
        ext w; simp [hb]
      rw [hs, Set.indicator_of_mem hb, lintegral_const, measure_univ, mul_one, periodLaw,
        Measure.prod_prod, measure_univ, mul_one]
    · have hs : {w : Ω₂ | b ∈ A ∧ w.1 ∈ B} = ∅ := by
        ext w; simp [hb]
      rw [hs, Set.indicator_of_notMem hb, lintegral_zero, measure_empty]

variable {H : Type*} [MeasurableSpace H]

/-- Integrals against `(ρ ⊗ₘ N(p ·)) ⊗ (N(0, I) ⊗ G)` as iterated integrals: over the history,
the next weight, and then the period outcome `((θ, μ), (ε, ν)) ~ periodLaw`. -/
theorem lintegral_decomp (ρ : Measure H) [IsProbabilityMeasure ρ] (p : H → E2 × M2)
    (hp : Measurable p) (G : Measure ℝ) [IsProbabilityMeasure G]
    (f : (H × E2) × (E2 × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂((ρ ⊗ₘ gaussK p hp).prod ((stdGaussian E2).prod G)) =
      ∫⁻ h, ∫⁻ g, ∫⁻ w, f ((h, w.1), (w.2, g)) ∂(periodLaw (p h).1 (p h).2) ∂G ∂ρ := by
  rw [lintegral_prod _ hf.aemeasurable, Measure.lintegral_compProd hf.lintegral_prod_right']
  refine lintegral_congr fun h => ?_
  have hF : Measurable (fun q : (E2 × E2) × ℝ => f ((h, q.1.1), (q.1.2, q.2))) :=
    hf.comp ((measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hF2 : Measurable (fun w : E2 × E2 => ∫⁻ g, f ((h, w.1), (w.2, g)) ∂G) :=
    hF.lintegral_prod_right'
  calc ∫⁻ x, ∫⁻ r, f ((h, x), r) ∂((stdGaussian E2).prod G) ∂(gaussK p hp h)
      = ∫⁻ x, ∫⁻ e, ∫⁻ g, f ((h, x), (e, g)) ∂G ∂(stdGaussian E2) ∂(gaussK p hp h) := by
        refine lintegral_congr fun x => ?_
        exact lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable
    _ = ∫⁻ w, ∫⁻ g, f ((h, w.1), (w.2, g)) ∂G ∂(periodLaw (p h).1 (p h).2) := by
        rw [periodLaw, lintegral_prod _ hF2.aemeasurable]
        rfl
    _ = ∫⁻ g, ∫⁻ w, f ((h, w.1), (w.2, g)) ∂(periodLaw (p h).1 (p h).2) ∂G :=
        lintegral_lintegral_swap hF.aemeasurable

/-- **The posterior at the next history.** Let the history `h ~ ρ` have posterior `N(p h)`, let
`y = k h · Z + b h` (`k ≥ 0`) be observed and `g ~ G` independent; if the next history is
`E (h, y, g)` and `p'` gives `nextPar` there, then `N(p' ·)` is the posterior given the next
history. -/
theorem step_law {H' : Type*} [MeasurableSpace H'] (ρ : Measure H) [IsProbabilityMeasure ρ]
    (p : H → E2 × M2) (hp : Measurable p) (hpsd : ∀ h, (p h).2.PosSemidef)
    (γ k b : H → ℝ) (hγ : Measurable γ) (hk : Measurable k) (hb : Measurable b)
    (hk0 : ∀ h, 0 ≤ k h) (E : H × ℝ × ℝ → H') (hE : Measurable E)
    (p' : H' → E2 × M2) (hp' : Measurable p')
    (hc : ∀ h y g, p' (E (h, y, g)) = nextPar (p h).1 (p h).2 (γ h) (k h) (b h) y)
    (G : Measure ℝ) [IsProbabilityMeasure G] :
    ((ρ ⊗ₘ gaussK p hp).prod ((stdGaussian E2).prod G)).map
        (fun q => (E (q.1.1, k q.1.1 * Zof (p q.1.1).1 (p q.1.1).2 (γ q.1.1) (q.1.2, q.2.1) +
          b q.1.1, q.2.2), q.1.2)) =
      (((ρ ⊗ₘ gaussK p hp).prod ((stdGaussian E2).prod G)).map
        (fun q => E (q.1.1, k q.1.1 * Zof (p q.1.1).1 (p q.1.1).2 (γ q.1.1) (q.1.2, q.2.1) +
          b q.1.1, q.2.2))) ⊗ₘ gaussK p' hp' := by
  set ν := (ρ ⊗ₘ gaussK p hp).prod ((stdGaussian E2).prod G) with hν
  set Y : (H × E2) × (E2 × ℝ) → ℝ :=
    fun q => k q.1.1 * Zof (p q.1.1).1 (p q.1.1).2 (γ q.1.1) (q.1.2, q.2.1) + b q.1.1 with hYdef
  have h11 : Measurable (fun q : (H × E2) × (E2 × ℝ) => q.1.1) := measurable_fst.comp measurable_fst
  have hYm : Measurable Y :=
    ((hk.comp h11).mul (measurable_Zof_par (measurable_fst.comp (hp.comp h11))
      (measurable_snd.comp (hp.comp h11)) (hγ.comp h11)
      ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)))).add
      (hb.comp h11)
  have hΦ1 : Measurable (fun q : (H × E2) × (E2 × ℝ) => E (q.1.1, Y q, q.2.2)) :=
    hE.comp (h11.prodMk (hYm.prodMk (measurable_snd.comp measurable_snd)))
  have hΦ : Measurable (fun q : (H × E2) × (E2 × ℝ) => (E (q.1.1, Y q, q.2.2), q.1.2)) :=
    hΦ1.prodMk (measurable_snd.comp measurable_fst)
  refine Measure.ext_prod fun {A} {B} hA hB => ?_
  have hfm2 : Measurable (((fun q : (H × E2) × (E2 × ℝ) => E (q.1.1, Y q, q.2.2)) ⁻¹' A).indicator
      (fun q => gaussK p' hp' (E (q.1.1, Y q, q.2.2)) B)) :=
    ((Kernel.measurable_coe _ hB).comp hΦ1).indicator (hΦ1 hA)
  rw [Measure.map_apply hΦ (hA.prod hB), Measure.compProd_apply_prod hA hB,
    setLIntegral_map hA (Kernel.measurable_coe _ hB) hΦ1,
    ← lintegral_indicator_one (hΦ (hA.prod hB)), ← lintegral_indicator (hΦ1 hA),
    lintegral_decomp ρ p hp G _ ((measurable_one).indicator (hΦ (hA.prod hB))),
    hν, lintegral_decomp ρ p hp G _ hfm2]
  refine lintegral_congr fun h => lintegral_congr fun g => ?_
  set A' : Set ℝ := {y | E (h, y, g) ∈ A} with hA'
  have hA'm : MeasurableSet A' :=
    hE.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)) hA
  have e1 : ∀ w : Ω₂, ((fun q : (H × E2) × (E2 × ℝ) => (E (q.1.1, Y q, q.2.2), q.1.2)) ⁻¹'
      (A ×ˢ B)).indicator 1 ((h, w.1), (w.2, g)) =
      {w : Ω₂ | k h * Zof (p h).1 (p h).2 (γ h) w + b h ∈ A' ∧ w.1 ∈ B}.indicator
        (1 : Ω₂ → ℝ≥0∞) w := by
    intro w
    simp only [Set.mem_ofPred_eq, hA', hYdef]
    rfl
  have e2 : ∀ w : Ω₂, ((fun q : (H × E2) × (E2 × ℝ) => E (q.1.1, Y q, q.2.2)) ⁻¹' A).indicator
      (fun q => gaussK p' hp' (E (q.1.1, Y q, q.2.2)) B) ((h, w.1), (w.2, g)) =
      A'.indicator (fun y => multivariateGaussian (nextPar (p h).1 (p h).2 (γ h) (k h) (b h) y).1
        (nextPar (p h).1 (p h).2 (γ h) (k h) (b h) y).2 B)
        (k h * Zof (p h).1 (p h).2 (γ h) w + b h) := by
    intro w
    by_cases hw : E (h, k h * Zof (p h).1 (p h).2 (γ h) w + b h, g) ∈ A
    · rw [Set.indicator_of_mem (show ((h, w.1), (w.2, g)) ∈
          (fun q : (H × E2) × (E2 × ℝ) => E (q.1.1, Y q, q.2.2)) ⁻¹' A from hw),
        Set.indicator_of_mem (show k h * Zof (p h).1 (p h).2 (γ h) w + b h ∈ A' from hw)]
      show gaussK p' hp' (E (h, k h * Zof (p h).1 (p h).2 (γ h) w + b h, g)) B = _
      rw [gaussK_apply, hc]
    · rw [Set.indicator_of_notMem (show ((h, w.1), (w.2, g)) ∉
          (fun q : (H × E2) × (E2 × ℝ) => E (q.1.1, Y q, q.2.2)) ⁻¹' A from hw),
        Set.indicator_of_notMem (show k h * Zof (p h).1 (p h).2 (γ h) w + b h ∉ A' from hw)]
  simp_rw [e1, e2]
  have hZ : Measurable (Zof (p h).1 (p h).2 (γ h)) :=
    measurable_Zof_par measurable_const measurable_const measurable_const measurable_id
  have hsm : MeasurableSet {w : Ω₂ | k h * Zof (p h).1 (p h).2 (γ h) w + b h ∈ A' ∧ w.1 ∈ B} :=
    ((measurable_const.mul hZ).add_const _ hA'm).inter (measurable_fst hB)
  rw [lintegral_indicator_one hsm]
  exact fiber_law (hpsd h) (γ h) (k h) (b h) (hk0 h) hA'm hB

end CC.LinearPaths
