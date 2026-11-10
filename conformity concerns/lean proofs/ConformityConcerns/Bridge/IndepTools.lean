import ConformityConcerns.Bridge.Info
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independence tools

* regrouping independent triples (`br_indep_assoc` and variants);
* an atomless random variable independent of another one differs from it almost surely;
* under `N(0, Σ₁) ⊗ N(0, I)^ℕ`, the state together with the noises before `t` is independent of the
  noise at `t`.
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix

set_option warn.classDefReducibility false

section Triple

variable {Ω α β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace δ] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → α} {Y : Ω → β}
  {Z : Ω → δ}

/-- If `(X, Y) ⟂ Z` and `X ⟂ Y` then `X ⟂ (Y, Z)`. -/
lemma br_indep_assoc (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h1 : IndepFun (fun ω => (X ω, Y ω)) Z P) (h2 : IndepFun X Y P) :
    IndepFun X (fun ω => (Y ω, Z ω)) P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable (hY.prodMk hZ).aemeasurable]
  have hYZ : IndepFun Y Z P := h1.comp (φ := Prod.snd) (ψ := id) measurable_snd measurable_id
  have e1 := (indepFun_iff_map_prod_eq_prod_map_map (hX.prodMk hY).aemeasurable
    hZ.aemeasurable).1 h1
  have e2 := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 h2
  have e3 := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).1 hYZ
  rw [e3]
  have : (fun ω => (X ω, (Y ω, Z ω))) =
      MeasurableEquiv.prodAssoc ∘ (fun ω => ((X ω, Y ω), Z ω)) := rfl
  rw [this, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable ((hX.prodMk hY).prodMk hZ),
    e1, e2, Measure.prodAssoc_prod]

/-- If `(X, Y) ⟂ Z` and `X ⟂ Y` then `(X, Z) ⟂ Y`. -/
lemma br_indep_regroup (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h1 : IndepFun (fun ω => (X ω, Y ω)) Z P) (h2 : IndepFun X Y P) :
    IndepFun (fun ω => (X ω, Z ω)) Y P := by
  have h1' : IndepFun (fun ω => (Y ω, X ω)) Z P :=
    h1.comp (φ := Prod.swap) (ψ := id) measurable_swap measurable_id
  exact (br_indep_assoc hY hX hZ h1' h2.symm).symm

/-- If `X ⟂ (Y, Z)` and `Y ⟂ Z` then `(X, Y) ⟂ Z`. -/
lemma br_indep_assoc' (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h1 : IndepFun X (fun ω => (Y ω, Z ω)) P) (h2 : IndepFun Y Z P) :
    IndepFun (fun ω => (X ω, Y ω)) Z P := by
  have h1' : IndepFun (fun ω => (Z ω, Y ω)) X P :=
    h1.symm.comp (φ := Prod.swap) (ψ := id) measurable_swap measurable_id
  have h3 := (br_indep_assoc hZ hY hX h1' h2.symm).symm
  exact h3.comp (φ := Prod.swap) (ψ := id) measurable_swap measurable_id

end Triple

/-- Independence transported along a measurable map. -/
lemma br_indep_of_map {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β] {P : Measure Ω} {h : Ω → Ω'} (hh : Measurable h)
    {f : Ω' → α} {g : Ω' → β} (hf : Measurable f) (hg : Measurable g)
    (H : IndepFun f g (P.map h)) : IndepFun (fun ω => f (h ω)) (fun ω => g (h ω)) P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at H ⊢
  intro s t hs ht
  have := H s t hs ht
  rwa [Measure.map_apply hh ((hf hs).inter (hg ht)), Measure.map_apply hh (hf hs),
    Measure.map_apply hh (hg ht)] at this

/-- An atomless random variable independent of another one differs from it almost surely. -/
lemma br_prob_eq_zero_of_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W V : Ω → ℝ} (hW : Measurable W) (hV : Measurable V)
    (h : IndepFun W V P) (hna : ∀ y, P.map W {y} = 0) : P {ω | W ω = V ω} = 0 := by
  have e := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hV.aemeasurable).1 h
  have hD : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_diagonal
  have hs : {ω | W ω = V ω} = (fun ω => (W ω, V ω)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := rfl
  rw [hs, ← Measure.map_apply (hW.prodMk hV) hD, e, Measure.prod_apply_symm hD]
  have h0 : ∀ y : ℝ, (P.map W) ((fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
    intro y
    have : (fun x : ℝ => (x, y)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {y} := by ext; simp
    rw [this, hna]
  simp [hna]

/-- The law of the state and the noises (the weight path is fixed). -/
noncomputable def Qm (S₁ : M2) : Measure (E2 × (ℕ → E2)) :=
  (multivariateGaussian 0 S₁).prod (Measure.infinitePi fun _ : ℕ => stdGaussian E2)

instance (S₁ : M2) : IsProbabilityMeasure (Qm S₁) := by unfold Qm; infer_instance

lemma indep_noise (t : ℕ) :
    IndepFun (fun ε : ℕ → E2 => truncE t ε) (fun ε => ε t)
      (Measure.infinitePi fun _ : ℕ => stdGaussian E2) := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => stdGaussian E2) (X := fun _ => id)
    (fun _ => measurable_id)
  have h2 := h.indepFun_finset (Finset.range t) {t} (by simp) (fun i => measurable_pi_apply i)
  let φ : (Finset.range t → E2) → (ℕ → E2) := fun η i =>
    if hi : i < t then η ⟨i, Finset.mem_range.2 hi⟩ else 0
  let ψ : (({t} : Finset ℕ) → E2) → E2 := fun η => η ⟨t, Finset.mem_singleton_self t⟩
  have hφ : Measurable φ := by
    refine Measurable.of_eval fun i => ?_
    by_cases hi : i < t
    · simp only [φ, hi, dite_eq_left]; exact measurable_pi_apply _
    · simp only [φ, hi, dite_eq_right, not_false_eq_true]; exact measurable_const
  have hψ : Measurable ψ := measurable_pi_apply _
  have h3 := h2.comp hφ hψ
  have e1 : (fun ε : ℕ → E2 => truncE t ε) =
      φ ∘ (fun a (i : Finset.range t) => (fun i (ω : ℕ → E2) => id (ω i)) i a) := by
    funext ε i
    simp only [truncE, Function.comp, φ, id]
    split_ifs <;> rfl
  rw [e1]
  exact h3

lemma indep_past_noise (S₁ : M2) (t : ℕ) :
    IndepFun (fun ω' : E2 × (ℕ → E2) => (ω'.1, truncE t ω'.2)) (fun ω' => ω'.2 t) (Qm S₁) := by
  have hT := measurable_truncE t
  have hE : Measurable (fun ε : ℕ → E2 => ε t) := measurable_pi_apply t
  refine br_indep_assoc' measurable_fst (hT.comp measurable_snd) (hE.comp measurable_snd) ?_ ?_
  · exact indepFun_prod (X := id) measurable_id (hT.prodMk hE)
  · refine br_indep_of_map (P := Qm S₁) measurable_snd hT hE ?_
    unfold Qm
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact indep_noise t

lemma law_noise (S₁ : M2) (t : ℕ) :
    (Qm S₁).map (fun ω' : E2 × (ℕ → E2) => ω'.2 t) = stdGaussian E2 := by
  have : (fun ω' : E2 × (ℕ → E2) => ω'.2 t) = (fun ε : ℕ → E2 => ε t) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply t) measurable_snd]
  unfold Qm
  rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]

lemma law_state (S₁ : M2) :
    (Qm S₁).map (fun ω' : E2 × (ℕ → E2) => ω'.1) = multivariateGaussian 0 S₁ := by
  unfold Qm
  have : (fun ω' : E2 × (ℕ → E2) => ω'.1) = Prod.fst := rfl
  rw [this, Measure.map_fst_prod, measure_univ, one_smul]

end CC.Bridge
