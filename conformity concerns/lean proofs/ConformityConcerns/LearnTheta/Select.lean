import ConformityConcerns.LearnTheta.Defs
import ConformityConcerns.General.KnownMu
import ConformityConcerns.LearnTheta.SelAux.Meas

/-!
# Proposition A5, `κ ≤ κck`: a measurable choice of fully revealing equilibrium

For each belief `η` about `Y_t = E(θ | h^t, s_t)`, the expected conformity loss of a revealed
type is `m = mfun ψ η`. When `m` is `C²` with `0 < m'' ≤ 2` and `κ ≤ κck`, the period game has a
fully revealing equilibrium satisfying `D1^∞` (`CC.General.propA5_period`). `revealSel κ ψ η` is
one such strategy, chosen so that `(η, x) ↦ revealSel κ ψ η x` is measurable (for the Giry
σ-algebra on `Measure ℝ`). This makes the profile that plays it at every history measurable.
-/

namespace CC.LearnTheta

open MeasureTheory ProbabilityTheory Filter Topology
open CC.General

/-- A fully revealing strategy for the period game whose belief about `Y_t` is `η`. With
`m = mfun ψ η`, `dQ ψ η` is a measurable version of `m'` and `xsSel ψ η` its zero `x*`; the
strategy glues at `x*` the explicit tail solutions (limits of the monotone iteration of
`ODE/Existence.lean`) of Lemma A3 (iii) and Corollary A1 (iii) with `f = m'/2`. When `dQ ψ η`
does not vanish at `xsSel ψ η` (then `m` has no minimiser), it is the identity. -/
noncomputable def revealSel (κ : ℝ) (ψ : ℝ → ℝ) (η : Measure ℝ) (x : ℝ) : ℝ :=
  if SelAux.dQ ψ η (SelAux.xsSel ψ η) = 0 then
    SelAux.selRule κ (fun y => SelAux.dQ ψ η y / 2) (SelAux.xsSel ψ η) x
  else x

/-- The choice is jointly measurable in the belief and the type. -/
theorem measurable_revealSel (κ : ℝ) (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (_hψb : ∃ C, ∀ x, ψ x ≤ C) :
    Measurable (fun p : Measure ℝ × ℝ => revealSel κ ψ p.1 p.2) := by
  have hψ : Measurable ψ := hψc.measurable
  have hD := SelAux.measurable_dQ hψ
  have hxs := SelAux.measurable_xsSel hψ
  have h0 : Measurable fun p : Measure ℝ × ℝ => (p.1, SelAux.xsSel ψ p.1) :=
    measurable_fst.prodMk (hxs.comp measurable_fst)
  have h1' := hD.comp h0
  have h1 : Measurable fun p : Measure ℝ × ℝ => SelAux.dQ ψ p.1 (SelAux.xsSel ψ p.1) := h1'
  have hA : MeasurableSet {p : Measure ℝ × ℝ | SelAux.dQ ψ p.1 (SelAux.xsSel ψ p.1) = 0} := by
    have := h1 (measurableSet_singleton (0 : ℝ))
    simpa only [Set.preimage, Set.mem_singleton_iff] using this
  have hF : Measurable fun p : Measure ℝ × ℝ => SelAux.dQ ψ p.1 p.2 / 2 := hD.div_const 2
  have hS := SelAux.measurable_selRule κ (F := fun η y => SelAux.dQ ψ η y / 2)
    (c := SelAux.xsSel ψ) hF hxs
  have hR : Measurable fun p : Measure ℝ × ℝ =>
      if SelAux.dQ ψ p.1 (SelAux.xsSel ψ p.1) = 0 then
        SelAux.selRule κ (fun y => SelAux.dQ ψ p.1 y / 2) (SelAux.xsSel ψ p.1) p.2
      else p.2 :=
    Measurable.ite hA hS measurable_snd
  exact hR

/-- When `m = mfun ψ η` is `C²` with `0 < m'' ≤ 2` and `0 < κ ≤ κck`, `revealSel κ ψ η` is
strictly increasing and is a compactified perfect Bayesian equilibrium satisfying `D1^∞` of every
period game with quadratic adaptation loss and conformity loss `κ (m - m(μ))`. -/
theorem revealSel_spec (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ κck) (ψ : ℝ → ℝ) (η : Measure ℝ)
    [IsProbabilityMeasure η] (hm : ContDiff ℝ 2 (mfun ψ η))
    (hm2 : ∀ x, 0 < iteratedDeriv 2 (mfun ψ η) x ∧ iteratedDeriv 2 (mfun ψ η) x ≤ 2) :
    StrictMono (revealSel κ ψ η) ∧
      ∀ S : Setting, S.g = (fun z => z ^ 2) →
        S.ℓ = (fun x => κ * (mfun ψ η x - mfun ψ η S.μ)) →
        ∃ φ : ℝ → Measure EReal, S.IsCPBE (revealSel κ ψ η) φ ∧ S.D1Inf (revealSel κ ψ η) φ := by
  have hmd : Differentiable ℝ (mfun ψ η) := hm.differentiable (by norm_num)
  have hD : ∀ x, SelAux.dQ ψ η x = deriv (mfun ψ η) x := fun x => SelAux.dQ_eq (hmd x)
  have hm1 : ContDiff ℝ 1 (deriv (mfun ψ η)) := hm.deriv'
  have h2 : ∀ x, iteratedDeriv 2 (mfun ψ η) x = deriv (deriv (mfun ψ η)) x := fun x => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hdm : StrictMono (deriv (mfun ψ η)) :=
    strictMono_of_deriv_pos (fun x => by rw [← h2]; exact (hm2 x).1)
  have hDm : StrictMono (SelAux.dQ ψ η) := fun x y hxy => by
    rw [hD, hD]; exact hdm hxy
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun x => deriv (mfun ψ η) x / 2 := ⟨_, rfl⟩
  have hfeq : (fun y => SelAux.dQ ψ η y / 2) = f := by
    rw [hfdef]; funext y; rw [hD]
  have hfm : StrictMono f := fun x y hxy => by
    simp only [hfdef]; linarith [hdm hxy]
  have hf1 : ContDiff ℝ 1 f := by rw [hfdef]; exact hm1.div_const 2
  have hfd : ∀ x, deriv f x = iteratedDeriv 2 (mfun ψ η) x / 2 := fun x => by
    rw [hfdef, deriv_div_const, h2]
  have hsup : ∀ v, κ * deriv f v ≤ κck := fun v => by
    rw [hfd]
    have h' : iteratedDeriv 2 (mfun ψ η) v / 2 ≤ 1 := by linarith [(hm2 v).2]
    calc κ * (iteratedDeriv 2 (mfun ψ η) v / 2) ≤ κ * 1 := mul_le_mul_of_nonneg_left h' hκ0.le
      _ ≤ κck := by linarith
  have hmain : SelAux.dQ ψ η (SelAux.xsSel ψ η) = 0 →
      revealSel κ ψ η = SelAux.selRule κ f (SelAux.xsSel ψ η) ∧ f (SelAux.xsSel ψ η) = 0 := by
    intro h
    refine ⟨funext fun x => ?_, ?_⟩
    · unfold revealSel
      rw [ite_eq_left h, hfeq]
    · rw [← hfeq]; simp only [h, zero_div]
  constructor
  · by_cases h : SelAux.dQ ψ η (SelAux.xsSel ψ η) = 0
    · obtain ⟨heq, hfc⟩ := hmain h
      obtain ⟨hcont, hode⟩ := SelAux.selRule_ode κ hκ0 f hfm hf1 hfc hsup
      rw [heq]
      exact Rev.strictMono_of_hasDerivAt_pos_off _ hcont (fun r hr => (hode r hr).1)
        (fun r hr => (hode r hr).2)
    · have hid : revealSel κ ψ η = id := funext fun x => by
        unfold revealSel
        rw [ite_eq_right h]
        rfl
      rw [hid]
      exact strictMono_id
  · intro S hg hℓ
    have hmin : ∀ b, mfun ψ η S.μ ≤ mfun ψ η b := fun b => by
      have h1 := S.hℓ.isMin b
      simp only [hℓ, sub_self, mul_zero] at h1
      have h3 := (mul_nonneg_iff_of_pos_left hκ0).1 h1
      linarith
    have hμ : deriv (mfun ψ η) S.μ = 0 :=
      IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall hmin)
    have hc : SelAux.xsSel ψ η = S.μ := SelAux.xsSel_eq hDm (by rw [hD, hμ])
    obtain ⟨heq, hfc⟩ := hmain (by rw [hc, hD, hμ])
    rw [hc] at heq hfc
    obtain ⟨hcont, hode⟩ := SelAux.selRule_ode κ hκ0 f hfm hf1 hfc hsup
    have hℓ' : ∀ v, deriv S.ℓ v = κ * deriv (mfun ψ η) v := fun v => by
      rw [hℓ]; exact (((hmd v).hasDerivAt.sub_const (mfun ψ η S.μ)).const_mul κ).deriv
    have hg' : ∀ z, deriv S.g z = 2 * z := fun z => by rw [hg]; exact Rev.deriv_sq_fun z
    have hval : ∀ v w, deriv S.ℓ v / deriv S.g (v - w) = κ * f v / (v - w) := by
      intro v w; rw [hℓ', hg']; simp only [hfdef]; rw [mul_div_assoc', div_div]
    rw [heq]
    -- there are no off-path actions
    have hmono := Rev.strictMono_of_hasDerivAt_pos_off _ hcont (fun r hr => (hode r hr).1)
      (fun r hr => (hode r hr).2)
    have hs := Rev.surjective_of_ode hκ0 hfm hfc hcont
      (SelAux.selRule_self κ hκ0 f hfm hf1 hfc hsup) hmono hode
    obtain ⟨-, φ, hE, hD1⟩ := Rev.exists_revealing_surjective S hcont
      (fun r hr => by rw [hval]; exact (hode r hr).1) (fun r hr => by rw [hval]; exact (hode r hr).2)
      hs
    exact ⟨φ, hE, hD1⟩

end CC.LearnTheta
