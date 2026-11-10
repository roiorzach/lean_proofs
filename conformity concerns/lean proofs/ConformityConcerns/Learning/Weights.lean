import ConformityConcerns.Learning.NoLearning
import ConformityConcerns.Learning.Assembly
import Mathlib.Probability.Independence.Basic

/-!
# Propositions A4 and A6 with the weights `γ_t` in the public history

In the paper the public history is `h^t = (γ_1, a_1, …, a_{t-1}, γ_t)`. With `θ` known the weights
do not affect payoffs, so they can matter only as public randomization. `Learning/Assembly.lean`
omits them. Here they are included: `γ_t` are i.i.d. with any law `G`, independent of `(μ, (ν_t)_t)`,
and strategies may depend on them.

* A profile `c t h v` depends on the history `h = (a_0, …, a_{t-1}; γ_0, …, γ_t)`.
* If every period pools at every history, `μ(h^t) = E μ` almost surely (`pooling_post_ae`).
* The revealing equilibrium does not use the weights. Its posterior means are those computed
  without them (`postW_reveal`), since the weights are independent of `(μ, (ν_t)_t)`.
-/

namespace CC.Learning

open MeasureTheory ProbabilityTheory Filter Topology
open CC.General

/-! ### Conditioning on an independent coordinate -/

section Product

variable {α β E F : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E]
  [MeasurableSpace F] {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P]
  [IsProbabilityMeasure Q]

/-- If `z.2` is independent of `z.1`, adding a function of `z.2` to the conditioning variables
does not change the conditional expectation of a function of `z.1`. -/
theorem condExp_comap_prod {A : α → E} {B : β → F} (hA : Measurable A) (hB : Measurable B)
    {f : α → ℝ} (hf : Integrable f P) :
    (P.prod Q)[fun z : α × β => f z.1 |
        MeasurableSpace.comap (fun z : α × β => (A z.1, B z.2)) inferInstance] =ᵐ[P.prod Q]
      fun z => (P[f | MeasurableSpace.comap A inferInstance]) z.1 := by
  have hmA_le : MeasurableSpace.comap A inferInstance ≤ (inferInstance : MeasurableSpace α) :=
    hA.comap_le
  have hφ : Measurable (fun z : α × β => (A z.1, B z.2)) :=
    (hA.comp measurable_fst).prodMk (hB.comp measurable_snd)
  have hfi : Integrable (fun z : α × β => f z.1) (P.prod Q) := hf.comp_fst Q
  have hg : Integrable (P[f | MeasurableSpace.comap A inferInstance]) P := integrable_condExp
  have hgi : Integrable (fun z : α × β => (P[f | MeasurableSpace.comap A inferInstance]) z.1) (P.prod Q) := hg.comp_fst Q
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hφ.comap_le hfi
    (fun s _ _ => hgi.integrableOn) ?_ ?_
  · rintro s ⟨T, hT, rfl⟩ -
    -- rectangles
    have hrect : ∀ U V, MeasurableSet U → MeasurableSet V →
        ∫ z in (fun z : α × β => (A z.1, B z.2)) ⁻¹' (U ×ˢ V), (P[f | MeasurableSpace.comap A inferInstance]) z.1 ∂(P.prod Q) =
          ∫ z in (fun z : α × β => (A z.1, B z.2)) ⁻¹' (U ×ˢ V), f z.1 ∂(P.prod Q) := by
      intro U V hU hV
      have hset : (fun z : α × β => (A z.1, B z.2)) ⁻¹' (U ×ˢ V) = (A ⁻¹' U) ×ˢ (B ⁻¹' V) := rfl
      rw [hset, setIntegral_prod _ hgi.integrableOn, setIntegral_prod _ hfi.integrableOn]
      simp only [setIntegral_const, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul,
        setIntegral_condExp hmA_le hf ⟨U, hU, rfl⟩]
    refine MeasurableSpace.induction_on_inter
      (C := fun T _ => ∫ z in (fun z : α × β => (A z.1, B z.2)) ⁻¹' T, (P[f | MeasurableSpace.comap A inferInstance]) z.1 ∂(P.prod Q) =
        ∫ z in (fun z : α × β => (A z.1, B z.2)) ⁻¹' T, f z.1 ∂(P.prod Q))
      generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ T hT
    · simp
    · rintro _ ⟨U, hU, V, hV, rfl⟩
      exact hrect U V hU hV
    · intro T hTm hEq
      have hm : MeasurableSet ((fun z : α × β => (A z.1, B z.2)) ⁻¹' T) := hφ hTm
      have huniv := hrect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
      simp only [Set.univ_prod_univ, Set.preimage_univ, setIntegral_univ] at huniv
      have h1 := integral_add_compl hm hgi
      have h2 := integral_add_compl hm hfi
      rw [Set.preimage_compl]
      linarith
    · intro Ts hd hTm hEq
      have hm : ∀ i, MeasurableSet ((fun z : α × β => (A z.1, B z.2)) ⁻¹' Ts i) := fun i => hφ (hTm i)
      have hdis : Pairwise (Function.onFun Disjoint
          fun i => (fun z : α × β => (A z.1, B z.2)) ⁻¹' Ts i) :=
        fun i j hij => (hd hij).preimage _
      rw [Set.preimage_iUnion]
      have h1 := hasSum_integral_iUnion hm hdis hgi.integrableOn
      have h2 := hasSum_integral_iUnion hm hdis hfi.integrableOn
      simp only [hEq] at h1
      exact h1.unique h2
  · have hsm : StronglyMeasurable[MeasurableSpace.comap A inferInstance] (P[f | MeasurableSpace.comap A inferInstance]) := stronglyMeasurable_condExp
    obtain ⟨g, hg', hgA⟩ := hsm.exists_eq_measurable_comp
    have hgE : StronglyMeasurable[MeasurableSpace.comap
        (fun z : α × β => (A z.1, B z.2)) inferInstance] (fun z : α × β => g (A z.1)) :=
      (hg'.comp_measurable measurable_fst).comp_measurable (Measurable.of_comap_le le_rfl)
    refine hgE.aestronglyMeasurable.congr (Eventually.of_forall fun z => ?_)
    show g (A z.1) = (P[f | MeasurableSpace.comap A inferInstance]) z.1
    rw [hgA]
    rfl

end Product

/-! ### The model with weights -/

/-- The weights `(γ_t)_t`. -/
abbrev Wts := ℕ → ℝ

variable (Lμ Lν G : Measure ℝ)

/-- The law of `((μ, (ν_t)_t), (γ_t)_t)`. -/
noncomputable def lawW : Measure (Ω × Wts) :=
  (law Lμ Lν).prod (Measure.infinitePi fun _ : ℕ => G)

/-- The law of `((ν_t)_t, (γ_t)_t)`. -/
noncomputable def noiseW : Measure ((ℕ → ℝ) × Wts) :=
  (Measure.infinitePi fun _ : ℕ => Lν).prod (Measure.infinitePi fun _ : ℕ => G)

/-- A public history `(a_0, …, a_{t-1}; γ_0, …, γ_t)`. -/
abbrev HistW (t : ℕ) := (Fin t → ℝ) × (Fin (t + 1) → ℝ)

/-- A pure strategy profile with the weights in the public history. -/
abbrev ProfileW := ∀ t : ℕ, HistW t → ℝ → ℝ

/-- The realised actions. -/
def actsW (c : ProfileW) : (t : ℕ) → Ω × Wts → (Fin t → ℝ)
  | 0 => fun _ => Fin.elim0
  | t + 1 => fun z => Fin.snoc (actsW c t z) (c t (actsW c t z, fun i => z.2 i) (vt t z.1))

/-- The realised action of player `t`. -/
def playW (c : ProfileW) (t : ℕ) (z : Ω × Wts) : ℝ :=
  c t (actsW c t z, fun i => z.2 i) (vt t z.1)

set_option warn.classDefReducibility false in
/-- The σ-algebra of the public history `(a_0, …, a_{t-1}; γ_0, …, γ_t)`. -/
def histSigmaW (act : ℕ → Ω × Wts → ℝ) (t : ℕ) : MeasurableSpace (Ω × Wts) :=
  MeasurableSpace.comap (fun z : Ω × Wts => ((fun i : Fin t => act i z), fun i : Fin (t + 1) => z.2 i))
    inferInstance

/-- The public posterior mean `μ(h^t)`, with the weights in the history. -/
noncomputable def postW (P : Measure (Ω × Wts)) (act : ℕ → Ω × Wts → ℝ) (t : ℕ) : Ω × Wts → ℝ :=
  P[fun z => muV z.1 | histSigmaW act t]

/-- Social learning about preferences occurs (paper's definition, weights in the history). -/
def SLOccursW (post : ℕ → Ω × Wts → ℝ) : Prop :=
  ∀ᵐ m ∂Lμ, TendstoInMeasure (noiseW Lν G)
    (fun t (q : (ℕ → ℝ) × Wts) => post t ((m, q.1), q.2)) atTop (fun _ => m)

/-- Social learning about preferences fails (paper's definition, weights in the history). -/
def SLFailsW (post : ℕ → Ω × Wts → ℝ) : Prop :=
  ∀ᵐ m ∂Lμ, ¬ TendstoInMeasure (noiseW Lν G)
    (fun t (q : (ℕ → ℝ) × Wts) => post t ((m, q.1), q.2)) atTop (fun _ => m)

variable [IsProbabilityMeasure Lμ] [IsProbabilityMeasure Lν] [IsProbabilityMeasure G]

instance : IsProbabilityMeasure (law Lμ Lν) := by unfold law; infer_instance
instance : IsProbabilityMeasure (lawW Lμ Lν G) := by unfold lawW; infer_instance
instance : IsProbabilityMeasure (noiseW Lν G) := by unfold noiseW; infer_instance

/-- An almost sure property under `lawW` holds, for almost every `μ`, almost surely in the rest. -/
lemma ae_ae_lawW {p : Ω × Wts → Prop} (h : ∀ᵐ z ∂(lawW Lμ Lν G), p z) :
    ∀ᵐ m ∂Lμ, ∀ᵐ q ∂(noiseW Lν G), p ((m, q.1), q.2) := by
  have e : Lμ.prod (noiseW Lν G) = (lawW Lμ Lν G).map MeasurableEquiv.prodAssoc := by
    unfold lawW noiseW law
    rw [Measure.prodAssoc_prod]
  have h2 : ∀ᵐ y ∂(Lμ.prod (noiseW Lν G)), p ((y.1, y.2.1), y.2.2) := by
    rw [e, MeasurableEquiv.prodAssoc.measurableEmbedding.ae_map_iff]
    filter_upwards [h] with z hz
    exact hz
  exact Measure.ae_ae_of_ae_prod h2

omit [IsProbabilityMeasure Lν] in
/-- Adding an independent coordinate does not change convergence in measure. -/
lemma tendstoInMeasure_prod_iff {f : ℕ → (ℕ → ℝ) → ℝ} {c : ℝ} :
    TendstoInMeasure (noiseW Lν G) (fun t (q : (ℕ → ℝ) × Wts) => f t q.1) atTop (fun _ => c) ↔
      TendstoInMeasure (Measure.infinitePi fun _ : ℕ => Lν) f atTop (fun _ => c) := by
  have key : ∀ (ε : ENNReal) (t : ℕ), noiseW Lν G {q | ε ≤ edist (f t q.1) c} =
      (Measure.infinitePi fun _ : ℕ => Lν) {n | ε ≤ edist (f t n) c} := by
    intro ε t
    have : {q : (ℕ → ℝ) × Wts | ε ≤ edist (f t q.1) c} =
        {n | ε ≤ edist (f t n) c} ×ˢ Set.univ := by
      ext q; simp
    rw [this, noiseW, Measure.prod_prod, measure_univ, mul_one]
  constructor
  · intro h ε hε
    simpa only [key] using h ε hε
  · intro h ε hε
    simpa only [key] using h ε hε

/-! ### The revealing profile -/

/-- In a process that depends only on `(μ, (ν_t)_t)`, the posterior mean given the history with
the weights is the posterior mean given the history without them. -/
theorem postW_reveal (act : ℕ → Ω → ℝ) (hact : ∀ t, Measurable (act t)) (hμ : Integrable muV (law Lμ Lν))
    (t : ℕ) :
    postW (lawW Lμ Lν G) (fun t z => act t z.1) t =ᵐ[lawW Lμ Lν G]
      fun z => postMean (law Lμ Lν) act t z.1 := by
  have hA : Measurable (fun ω (i : Fin t) => act i ω) := measurable_pi_iff.2 fun i => hact i
  have hB : Measurable (fun (g : Wts) (i : Fin (t + 1)) => g i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  exact condExp_comap_prod (P := law Lμ Lν) (Q := Measure.infinitePi fun _ : ℕ => G) hA hB hμ

/-- Social learning without the weights gives social learning with them. -/
theorem slOccursW_of (act : ℕ → Ω → ℝ) (hact : ∀ t, Measurable (act t))
    (hμ : Integrable muV (law Lμ Lν))
    (h : SocialLearningOccurs Lμ Lν (postMean (law Lμ Lν) act)) :
    SLOccursW Lμ Lν G (postW (lawW Lμ Lν G) (fun t z => act t z.1)) := by
  have hae : ∀ᵐ m ∂Lμ, ∀ t, ∀ᵐ q ∂(noiseW Lν G),
      postW (lawW Lμ Lν G) (fun t z => act t z.1) t ((m, q.1), q.2) =
        postMean (law Lμ Lν) act t (m, q.1) :=
    ae_all_iff.2 fun t => ae_ae_lawW Lμ Lν G (postW_reveal Lμ Lν G act hact hμ t)
  filter_upwards [h, hae] with m hm hq
  have h1 := (tendstoInMeasure_prod_iff Lν G (f := fun t n => postMean (law Lμ Lν) act t (m, n))
    (c := m)).2 hm
  exact h1.congr_left fun t => (hq t).mono fun q hq' => hq'.symm

/-! ### Pooling profiles -/

/-- At pooling histories the actions depend only on the weights. -/
lemma actsW_of_pool (c : ProfileW) (hpool : ∀ t (h : HistW t) (v w : ℝ), c t h v = c t h w) :
    ∀ (t : ℕ) (z z' : Ω × Wts), z.2 = z'.2 → actsW c t z = actsW c t z' := by
  intro t
  induction t with
  | zero => intro z z' _; funext i; exact i.elim0
  | succ t ih =>
    intro z z' h
    have e : ∀ z : Ω × Wts, actsW c (t + 1) z =
        Fin.snoc (actsW c t z) (c t (actsW c t z, fun i => z.2 i) (vt t z.1)) := fun _ => rfl
    rw [e z, e z', ih z z' h, h, hpool t _ (vt t z.1) (vt t z'.1)]

lemma playW_of_pool (c : ProfileW) (hpool : ∀ t (h : HistW t) (v w : ℝ), c t h v = c t h w)
    (t : ℕ) (z z' : Ω × Wts) (h : z.2 = z'.2) : playW c t z = playW c t z' := by
  unfold playW
  rw [actsW_of_pool c hpool t z z' h, h, hpool t _ (vt t z.1) (vt t z'.1)]

lemma measurable_actsW (c : ProfileW) (hc : ∀ t, Measurable (Function.uncurry (c t))) :
    ∀ t, Measurable (actsW c t)
  | 0 => measurable_const
  | t + 1 => by
    have ih := measurable_actsW c hc t
    have hg : Measurable (fun z : Ω × Wts => fun i : Fin (t + 1) => z.2 i) :=
      measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp measurable_snd
    have ha : Measurable (fun z : Ω × Wts => c t (actsW c t z, fun i => z.2 i) (vt t z.1)) :=
      (hc t).comp ((ih.prodMk hg).prodMk ((measurable_vt t).comp measurable_fst))
    refine measurable_pi_iff.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have e : (fun z : Ω × Wts => actsW c (t + 1) z (Fin.last t)) =
          fun z => c t (actsW c t z, fun i => z.2 i) (vt t z.1) := by
        funext z; simp [actsW]
      rw [e]; exact ha
    · have e : (fun z : Ω × Wts => actsW c (t + 1) z j.castSucc) = fun z => actsW c t z j := by
        funext z; simp [actsW]
      rw [e]; exact (measurable_pi_apply j).comp ih

lemma measurable_playW (c : ProfileW) (hc : ∀ t, Measurable (Function.uncurry (c t))) (t : ℕ) :
    Measurable (playW c t) := by
  have hg : Measurable (fun z : Ω × Wts => fun i : Fin (t + 1) => z.2 i) :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp measurable_snd
  exact (hc t).comp (((measurable_actsW c hc t).prodMk hg).prodMk
    ((measurable_vt t).comp measurable_fst))

/-- If every period pools at every history, `μ(h^t) = E μ` almost surely. -/
theorem pooling_post_ae (c : ProfileW)
    (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (hpool : ∀ t (h : HistW t) (v w : ℝ), c t h v = c t h w) (t : ℕ) :
    postW (lawW Lμ Lν G) (playW c) t =ᵐ[lawW Lμ Lν G] fun _ => ∫ x, x ∂Lμ := by
  -- the history is a function of the weights
  let ω0 : Ω := (0, fun _ => 0)
  let B : Wts → (Fin t → ℝ) × (Fin (t + 1) → ℝ) :=
    fun g => ((fun i : Fin t => playW c i (ω0, g)), fun i : Fin (t + 1) => g i)
  have hB : Measurable B := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_)
      (measurable_pi_iff.2 fun i => measurable_pi_apply _)
    exact (measurable_playW c hc i).comp (measurable_const.prodMk measurable_id)
  have hE : histSigmaW (playW c) t = MeasurableSpace.comap (B ∘ Prod.snd) inferInstance := by
    unfold histSigmaW
    congr 1
    funext z
    refine Prod.ext (funext fun i => ?_) rfl
    exact playW_of_pool c hpool i z (ω0, z.2) rfl
  have hind : IndepFun (fun z : Ω × Wts => z.1) (fun z : Ω × Wts => B z.2) (lawW Lμ Lν G) :=
    indepFun_prod (X := id) (Y := B) measurable_id hB
  have hf : StronglyMeasurable[MeasurableSpace.comap (fun z : Ω × Wts => z.1) inferInstance]
      (fun z : Ω × Wts => muV z.1) :=
    (measurable_muV.stronglyMeasurable).comp_measurable (Measurable.of_comap_le le_rfl)
  have h1 := condExp_indep_eq (μ := lawW Lμ Lν G) (m₁ :=
      MeasurableSpace.comap (fun z : Ω × Wts => z.1) inferInstance)
    (m₂ := MeasurableSpace.comap (B ∘ Prod.snd) inferInstance)
    measurable_fst.comap_le (hB.comp measurable_snd).comap_le hf hind
  have hint : ∫ z, muV z.1 ∂(lawW Lμ Lν G) = ∫ x, x ∂Lμ := by
    have hmap1 : (lawW Lμ Lν G).map (fun z : Ω × Wts => z.1.1) = Lμ := by
      have : (fun z : Ω × Wts => z.1.1) = Prod.fst ∘ Prod.fst := rfl
      unfold lawW law
      rw [this, ← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod, measure_univ,
        one_smul, Measure.map_fst_prod, measure_univ, one_smul]
    have h := integral_map (μ := lawW Lμ Lν G) (φ := fun z : Ω × Wts => z.1.1)
      (f := fun x : ℝ => x) (measurable_fst.comp measurable_fst).aemeasurable
      aestronglyMeasurable_id
    rw [hmap1] at h
    exact h.symm
  unfold postW
  rw [hE]
  filter_upwards [h1] with z hz
  rw [hz, hint]

/-- A sequence that is almost surely constant equal to `e ≠ m` does not converge in measure
to `m`. -/
lemma not_tendsto_of_const {f : ℕ → (ℕ → ℝ) × Wts → ℝ} {e m : ℝ} (hm : m ≠ e)
    (h : ∀ t, ∀ᵐ q ∂(noiseW Lν G), f t q = e) :
    ¬ TendstoInMeasure (noiseW Lν G) f atTop (fun _ => m) := by
  intro hT
  have hε : 0 < edist e m := edist_pos.2 (Ne.symm hm)
  have h1 := hT _ hε
  have hc : ∀ t, noiseW Lν G {q | edist e m ≤ edist (f t q) m} = 1 := by
    intro t
    have : {q | edist e m ≤ edist (f t q) m} =ᵐ[noiseW Lν G] Set.univ := by
      filter_upwards [h t] with q hq
      simp [hq]
    rw [measure_congr this, measure_univ]
  simp only [hc] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

/-- In a profile that pools at every history, social learning does not occur, provided `μ` is
not almost surely constant. -/
theorem not_occursW_pooling (hnd : ∀ x, Lμ {x} < 1) (c : ProfileW)
    (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (hpool : ∀ t (h : HistW t) (v w : ℝ), c t h v = c t h w) :
    ¬ SLOccursW Lμ Lν G (postW (lawW Lμ Lν G) (playW c)) := by
  intro hocc
  have hae : ∀ᵐ m ∂Lμ, ∀ t, ∀ᵐ q ∂(noiseW Lν G),
      postW (lawW Lμ Lν G) (playW c) t ((m, q.1), q.2) = ∫ x, x ∂Lμ :=
    ae_all_iff.2 fun t => ae_ae_lawW Lμ Lν G (pooling_post_ae Lμ Lν G c hc hpool t)
  have hm : ∀ᵐ m ∂Lμ, m = ∫ x, x ∂Lμ := by
    filter_upwards [hocc, hae] with m hT hq
    by_contra hne
    exact not_tendsto_of_const Lν G hne hq hT
  have hcompl : Lμ {∫ x, x ∂Lμ}ᶜ = 0 := by
    rw [ae_iff] at hm
    simpa [Set.compl_def] using hm
  exact (hnd _).ne ((prob_compl_eq_zero_iff (measurableSet_singleton _)).1 hcompl)

/-- In a profile that pools at every history, social learning fails, if `μ` is atomless. -/
theorem failsW_pooling (hatom : ∀ x, Lμ {x} = 0) (c : ProfileW)
    (hc : ∀ t, Measurable (Function.uncurry (c t)))
    (hpool : ∀ t (h : HistW t) (v w : ℝ), c t h v = c t h w) :
    SLFailsW Lμ Lν G (postW (lawW Lμ Lν G) (playW c)) := by
  have hae : ∀ᵐ m ∂Lμ, ∀ t, ∀ᵐ q ∂(noiseW Lν G),
      postW (lawW Lμ Lν G) (playW c) t ((m, q.1), q.2) = ∫ x, x ∂Lμ :=
    ae_all_iff.2 fun t => ae_ae_lawW Lμ Lν G (pooling_post_ae Lμ Lν G c hc hpool t)
  have hne : ∀ᵐ m ∂Lμ, m ≠ ∫ x, x ∂Lμ := by
    rw [ae_iff]
    simpa using hatom _
  filter_upwards [hae, hne] with m hq hm
  exact not_tendsto_of_const Lν G hm hq

/-! ### Propositions A4 and A6 -/

/-- **Proposition A4 with the weights in the public history.** If `κ ≤ κck` there is an equilibrium
satisfying `D1^∞`, fully revealing at every history, whose norm is the posterior mean given the
history (with the weights), in which social learning about preferences occurs. If `κ > κck`, every
measurable equilibrium satisfying `D1^∞` is fully pooling at every history and social learning does
not occur. -/
theorem propA4_weights (κ : ℝ) (hκ : 0 < κ) (hμ : Integrable id Lμ) (hnd : ∀ x, Lμ {x} < 1)
    (hν : Integrable id Lν) (hν0 : ∫ x, x ∂Lν = 0) :
    let P := lawW Lμ Lν G
    let post : ℕ → Ω → ℝ := fun t => (law Lμ Lν)[muV | typeSigma t]
    (κ ≤ κck → ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
      (∀ S : Setting, S.g = (fun z => z ^ 2) → S.ℓ = (fun b => κ * (b - S.μ) ^ 2) →
        ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
          S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ) ∧
      (∀ t, postW P (fun t z => revealAct Φ post t z.1) t =ᵐ[P] fun z => post t z.1) ∧
      SLOccursW Lμ Lν G (postW P (fun t z => revealAct Φ post t z.1))) ∧
    (κck < κ → ∀ c : ProfileW, (∀ t, Measurable (Function.uncurry (c t))) →
      (∀ t (h : HistW t), ∃ S : Setting, S.g = (fun z => z ^ 2) ∧
        S.ℓ = (fun b => κ * (b - S.μ) ^ 2) ∧ ∃ φ : ℝ → Measure EReal, S.IsCPBE (c t h) φ ∧
          S.D1Inf (c t h) φ) →
      (∀ t (h : HistW t) (v w : ℝ), c t h v = c t h w) ∧
        ¬ SLOccursW Lμ Lν G (postW P (playW c))) := by
  intro P post
  have hμ' := integrable_muV Lμ Lν hμ
  refine ⟨fun hκ' => ?_, fun hκ' c hc hE => ?_⟩
  · obtain ⟨Φ, hΦ, hΦc, -, hΦeq⟩ := propA4_revealing κ hκ hκ'
    obtain ⟨-, h2, -, h4⟩ := learning_revealing Lμ Lν hμ hν hν0 Φ hΦ hΦc
    have hpm : ∀ t, Measurable (post t) := fun t =>
      (stronglyMeasurable_condExp.measurable).mono (typeSigma_le t) le_rfl
    have hact : ∀ t, Measurable (revealAct Φ post t) := fun t =>
      (hpm t).add (hΦc.measurable.comp ((measurable_vt t).sub (hpm t)))
    refine ⟨Φ, hΦ, hΦeq, fun t => ?_, slOccursW_of Lμ Lν G _ hact hμ' h4⟩
    have := postW_reveal Lμ Lν G _ hact hμ' t
    rwa [h2 t] at this
  · have hpool : ∀ t (h : HistW t) (v w : ℝ), c t h v = c t h w := by
      intro t h v w
      obtain ⟨S, hg, hℓ, φ, hEq, hD⟩ := hE t h
      obtain ⟨k, hk⟩ := propA4_pooling κ hκ' S hg hℓ (c t h) φ hEq hD
      rw [hk v, hk w]
    exact ⟨hpool, not_occursW_pooling Lμ Lν G hnd c hc hpool⟩

/-- **Proposition A6 with the weights in the public history.** -/
theorem propA6_weights (g f : ℝ → ℝ) (hg : AdaptLoss g) (hf : AdaptLoss f) (hμ : Integrable id Lμ)
    (hatom : ∀ x, Lμ {x} = 0) (hν : Integrable id Lν) (hν0 : ∫ x, x ∂Lν = 0) :
    let P := lawW Lμ Lν G
    let post : ℕ → Ω → ℝ := fun t => (law Lμ Lν)[muV | typeSigma t]
    ((∀ C : ℝ, ∃ ε > 0, ∀ᶠ x in atTop, 1 + ε ≤ deriv f x / deriv g (x + C)) →
      ∀ c : ProfileW, (∀ t, Measurable (Function.uncurry (c t))) →
        (∀ t (h : HistW t), ∃ S : Setting, S.g = g ∧ S.ℓ = (fun b => f (b - S.μ)) ∧
          ∃ φ : ℝ → Measure EReal, S.IsCPBE (c t h) φ ∧ S.D1Inf (c t h) φ) →
        (∀ t (h : HistW t) (v w : ℝ), c t h v = c t h w) ∧
          SLFailsW Lμ Lν G (postW P (playW c))) ∧
    ((∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ x, 0 < x → deriv f x ≤ (1 - β) * deriv g (β * x)) →
      ∃ Φ : ℝ → ℝ, StrictMono Φ ∧
        (∀ S : Setting, S.g = g → S.ℓ = (fun b => f (b - S.μ)) →
          ∃ φ : ℝ → Measure EReal, S.IsCPBE (fun v => S.μ + Φ (v - S.μ)) φ ∧
            S.D1Inf (fun v => S.μ + Φ (v - S.μ)) φ) ∧
        (∀ t, postW P (fun t z => revealAct Φ post t z.1) t =ᵐ[P] fun z => post t z.1) ∧
        ∀ᵐ z ∂P, Tendsto (fun t => postW P (fun t z => revealAct Φ post t z.1) t z) atTop
          (𝓝 (muV z.1))) := by
  intro P post
  have hμ' := integrable_muV Lμ Lν hμ
  refine ⟨fun hcond c hc hE => ?_, fun ⟨β, hβ0, hβ1, hcond⟩ => ?_⟩
  · have hpool : ∀ t (h : HistW t) (v w : ℝ), c t h v = c t h w := by
      intro t h v w
      obtain ⟨S, hgS, hℓ, φ, hEq, hD⟩ := hE t h
      obtain ⟨k, hk⟩ := propA6_i_period f hf S hℓ
        (fun C => by simpa [hgS] using hcond C) (c t h) φ hEq hD
      rw [hk v, hk w]
    exact ⟨hpool, failsW_pooling Lμ Lν G hatom c hc hpool⟩
  · obtain ⟨Φ, hΦ, hΦc, -, hΦeq⟩ := propA6_ii_period g f hg hf β hβ0 hβ1 hcond
    obtain ⟨-, h2, h3, -⟩ := learning_revealing Lμ Lν hμ hν hν0 Φ hΦ hΦc
    have hpm : ∀ t, Measurable (post t) := fun t =>
      (stronglyMeasurable_condExp.measurable).mono (typeSigma_le t) le_rfl
    have hact : ∀ t, Measurable (revealAct Φ post t) := fun t =>
      (hpm t).add (hΦc.measurable.comp ((measurable_vt t).sub (hpm t)))
    have hr := fun t => postW_reveal Lμ Lν G _ hact hμ' t
    refine ⟨Φ, hΦ, hΦeq, fun t => ?_, ?_⟩
    · have := hr t
      rwa [h2 t] at this
    · have hP : ∀ᵐ z ∂P, Tendsto (fun t => postMean (law Lμ Lν) (revealAct Φ post) t z.1) atTop
          (𝓝 (muV z.1)) := by
        have hfst : P.map Prod.fst = law Lμ Lν := by
          show (lawW Lμ Lν G).map Prod.fst = _
          unfold lawW
          rw [Measure.map_fst_prod, measure_univ, one_smul]
        have h3' : ∀ᵐ ω ∂(P.map Prod.fst), Tendsto
            (fun t => postMean (law Lμ Lν) (revealAct Φ post) t ω) atTop (𝓝 (muV ω)) := by
          rw [hfst]; exact h3
        exact ae_of_ae_map measurable_fst.aemeasurable h3'
      filter_upwards [hP, ae_all_iff.2 hr] with z h1 h2'
      exact h1.congr fun t => (h2' t).symm

end CC.Learning
