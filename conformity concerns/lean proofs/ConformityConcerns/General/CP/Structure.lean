import ConformityConcerns.General.CP.PoolAbove

/-!
# The central pooling structure

Every nondegenerate pool contains `μ`, so there is at most one; with `vlo`/`vhi` the infimum and
supremum (in `EReal`) of the central pool (or `vlo = vhi = μ` if there is none), the action rule
is a central pooling strategy, and every type in a tail is separating.
-/

namespace CC.General

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Setting

variable {S : Setting} {a : ℝ → ℝ} {φ : ℝ → Measure EReal}

/-- Types in the tails of a central pooling strategy are separating. -/
lemma sep_of_centralPooling {vlo vhi : EReal} {c : ℝ} (hcp : S.IsCentralPoolingWith a vlo vhi c)
    {v : ℝ} (hv : (v : EReal) < vlo ∨ vhi < (v : EReal)) : a ⁻¹' {a v} = {v} := by
  ext w
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro hw
    by_contra hne
    have hnt : (a ⁻¹' {a v}).Nontrivial := ⟨w, hw, v, rfl, hne⟩
    exact hcp.2.2.2.1 v hv (hcp.2.2.2.2.1 _ hnt)
  · rintro rfl; rfl

namespace IsCPBE

variable (h : S.IsCPBE a φ) (hD : S.D1Inf a φ)
include h hD

lemma centralPooling : ∃ vlo vhi : EReal, ∃ c : ℝ, S.IsCentralPoolingWith a vlo vhi c := by
  by_cases hex : ∃ x, (a ⁻¹' {x}).Nontrivial
  · have hfib : ∀ x, (a ⁻¹' {x}).Nontrivial → x = a S.μ := by
      intro x hx
      obtain ⟨w, hw⟩ := hx.nonempty
      have hw' : a w = x := hw
      subst hw'
      exact (h.pool_contains_mu hD hx).symm
    set c := a S.μ with hc
    set E : Set EReal := (fun r : ℝ => (r : EReal)) '' (a ⁻¹' {c}) with hE
    have hμE : (S.μ : EReal) ∈ E := ⟨S.μ, rfl, rfl⟩
    have hmemE : ∀ v : ℝ, a v = c → (v : EReal) ∈ E := fun v hv => ⟨v, hv, rfl⟩
    refine ⟨sInf E, sSup E, c, sInf_le hμE, le_sSup hμE, ?_, ?_, hfib, ?_, ?_⟩
    · intro v h1 h2
      obtain ⟨_, ⟨w₁, hw₁, rfl⟩, hlt₁⟩ := sInf_lt_iff.1 h1
      obtain ⟨_, ⟨w₂, hw₂, rfl⟩, hlt₂⟩ := lt_sSup_iff.1 h2
      exact h.mem_of_between (v := S.μ) hw₁ hw₂ (EReal.coe_lt_coe_iff.1 hlt₁).le
        (EReal.coe_lt_coe_iff.1 hlt₂).le
    · intro v hv hav
      rcases hv with hv | hv
      · exact absurd (sInf_le (hmemE v hav)) (not_le.2 hv)
      · exact absurd (le_sSup (hmemE v hav)) (not_le.2 hv)
    · intro v hv w hw hvw
      simp only [mem_ofPred_eq] at hv hw
      refine lt_of_le_of_ne (h.monotone hvw.le) fun heq => ?_
      have hnt : (a ⁻¹' {a v}).Nontrivial := ⟨v, rfl, w, heq.symm, hvw.ne⟩
      exact absurd (sInf_le (hmemE v (hfib _ hnt))) (not_le.2 hv)
    · intro v hv w hw hvw
      simp only [mem_ofPred_eq] at hv hw
      refine lt_of_le_of_ne (h.monotone hvw.le) fun heq => ?_
      have hnt : (a ⁻¹' {a v}).Nontrivial := ⟨v, rfl, w, heq.symm, hvw.ne⟩
      exact absurd (le_sSup (hmemE v (hfib _ hnt))) (not_le.2 hv)
  · simp only [not_exists] at hex
    have hinj : Function.Injective a := by
      intro v w hvw
      by_contra hne
      exact hex (a v) ⟨v, rfl, w, hvw.symm, hne⟩
    have hsm := h.monotone.strictMono_of_injective hinj
    refine ⟨S.μ, S.μ, a S.μ, le_rfl, le_rfl, ?_, ?_, ?_, hsm.strictMonoOn _, hsm.strictMonoOn _⟩
    · intro v h1 h2; exact absurd (h1.trans h2) (lt_irrefl _)
    · intro v hv hav
      have := hinj hav
      subst this
      rcases hv with hv | hv <;> exact lt_irrefl _ hv
    · intro x hx; exact absurd hx (hex x)

end IsCPBE

end Setting

end CC.General
