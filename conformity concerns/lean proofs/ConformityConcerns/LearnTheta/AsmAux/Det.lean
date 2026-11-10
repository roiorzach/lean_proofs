import ConformityConcerns.General.CentralPooling
import ConformityConcerns.General.RevCalc
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Deterministic helpers for the assembly of Proposition A5 across histories

* Facts about a conformity loss of the form `κ (m - m μ)`.
* Revelation by a monotone central pooling strategy at thresholds outside the pool.
* A second-moment (Markov) bound for a convolution, used to bound the pool's cutoffs.
* The squared deviation of a measure from a point.
* The squeeze giving `Pr(a_t = c₀) → 1`, for the central pool's action `c₀`, from vanishing tails.
-/

namespace CC.LearnTheta.AsmAux

open MeasureTheory Filter Topology Set CC.General
open scoped ENNReal

section Loss

variable {S : CC.General.Setting} {κ : ℝ} {m : ℝ → ℝ}

lemma m_eq (hκ : 0 < κ) (hℓ : S.ℓ = fun x => κ * (m x - m S.μ)) :
    m = fun x => S.ℓ x / κ + m S.μ := by
  funext x; rw [hℓ]; field_simp; ring

lemma m_contDiff (hκ : 0 < κ) (hℓ : S.ℓ = fun x => κ * (m x - m S.μ)) : ContDiff ℝ 2 m := by
  rw [m_eq hκ hℓ]; exact (S.hℓ.smooth.div_const κ).add contDiff_const

lemma m_differentiable (hκ : 0 < κ) (hℓ : S.ℓ = fun x => κ * (m x - m S.μ)) :
    Differentiable ℝ m :=
  (m_contDiff hκ hℓ).differentiable (by norm_num)

lemma m_min (hκ : 0 < κ) (hℓ : S.ℓ = fun x => κ * (m x - m S.μ)) (x : ℝ) : m S.μ ≤ m x := by
  have h := S.hℓ.isMin x
  rw [hℓ] at h
  simp only [sub_self, mul_zero] at h
  by_contra hlt
  replace hlt := not_le.1 hlt
  have : κ * (m x - m S.μ) < 0 := mul_neg_of_pos_of_neg hκ (by linarith)
  linarith

lemma m_strictConvex (hκ : 0 < κ) (hℓ : S.ℓ = fun x => κ * (m x - m S.μ)) :
    StrictConvexOn ℝ univ m := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have h := S.hℓ.strictConvex.2 (mem_univ x) (mem_univ y) hxy ha hb hab
  rw [hℓ] at h
  simp only [smul_eq_mul] at h ⊢
  have hb' : b = 1 - a := by linarith
  subst hb'
  have key : κ * m (a * x + (1 - a) * y) < κ * (a * m x + (1 - a) * m y) := by linarith
  exact lt_of_mul_lt_mul_left key hκ.le

lemma deriv_ℓ (hκ : 0 < κ) (hℓ : S.ℓ = fun x => κ * (m x - m S.μ)) (x : ℝ) :
    deriv S.ℓ x = κ * deriv m x := by
  have hd := m_differentiable hκ hℓ
  rw [hℓ]
  exact (((hd x).hasDerivAt.sub_const (m S.μ)).const_mul κ).deriv

lemma deriv_g (hg : S.g = fun z => z ^ 2) (z : ℝ) : deriv S.g z = 2 * z := by
  rw [hg]; exact Rev.deriv_sq_fun z

lemma deriv_m_eq_zero (hκ : 0 < κ) (hℓ : S.ℓ = fun x => κ * (m x - m S.μ)) :
    deriv m S.μ = 0 :=
  IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun x => m_min hκ hℓ x)

end Loss

section Reveal

variable {S : CC.General.Setting} {a : ℝ → ℝ} {vlo vhi : EReal} {c₀ : ℝ}

/-- A monotone central pooling strategy reveals whether the type exceeds any `d ≥ vhi`. -/
lemma reveal_hi (hmono : Monotone a) (hcp : S.IsCentralPoolingWith a vlo vhi c₀) {d : ℝ}
    (hd : vhi ≤ (d : EReal)) {q : ℝ} (hq : d < q) : a d < a q := by
  rcases (hmono hq.le).lt_or_eq with h | h
  · exact h
  · exfalso
    have hqv : vhi < (q : EReal) := lt_of_le_of_lt hd (EReal.coe_lt_coe_iff.2 hq)
    apply hcp.2.2.2.1 q (Or.inr hqv)
    exact hcp.2.2.2.2.1 (a q) ⟨d, h, q, rfl, hq.ne⟩

/-- A monotone central pooling strategy reveals whether the type is below any `d ≤ vlo`. -/
lemma reveal_lo (hmono : Monotone a) (hcp : S.IsCentralPoolingWith a vlo vhi c₀) {d : ℝ}
    (hd : (d : EReal) ≤ vlo) {q : ℝ} (hq : q < d) : a q < a d := by
  rcases (hmono hq.le).lt_or_eq with h | h
  · exact h
  · exfalso
    have hqv : (q : EReal) < vlo := lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hq) hd
    apply hcp.2.2.2.1 q (Or.inl hqv)
    exact hcp.2.2.2.2.1 (a q) ⟨q, rfl, d, h.symm, hq.ne⟩

end Reveal

section Moments

/-- Second moment of a convolution of probability measures. -/
lemma lintegral_sq_conv_le (η G : Measure ℝ) [IsProbabilityMeasure η] [IsProbabilityMeasure G] :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(η.conv G) ≤
      2 * ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂η + 2 * ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂G := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (x ^ 2) := by fun_prop
  rw [Measure.lintegral_conv hm]
  have hpt : ∀ y u : ℝ, ENNReal.ofReal ((y + u) ^ 2) ≤
      2 * ENNReal.ofReal (y ^ 2) + 2 * ENNReal.ofReal (u ^ 2) := by
    intro y u
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (y - u)])
  calc ∫⁻ y, ∫⁻ u, ENNReal.ofReal ((y + u) ^ 2) ∂G ∂η
      ≤ ∫⁻ y, ∫⁻ u, (2 * ENNReal.ofReal (y ^ 2) + 2 * ENNReal.ofReal (u ^ 2)) ∂G ∂η :=
        lintegral_mono fun y => lintegral_mono fun u => hpt y u
    _ = ∫⁻ y, (2 * ENNReal.ofReal (y ^ 2) + 2 * ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂G) ∂η := by
        congr 1; funext y
        rw [lintegral_add_left (by fun_prop), lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hm]
    _ = 2 * ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂η + 2 * ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂G := by
        rw [lintegral_add_left (by fun_prop), lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hm]

/-- The second moment as a lower integral of an integrable square. -/
lemma lintegral_sq_eq (η : Measure ℝ) (h2 : Integrable (fun y => y ^ 2) η) :
    ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂η = ENNReal.ofReal (∫ y, y ^ 2 ∂η) :=
  (ofReal_integral_eq_lintegral_ofReal h2 (Filter.Eventually.of_forall fun y => sq_nonneg y)).symm

/-- Markov: if the upper tail `(vhi, ∞)` has mass at least `δ` and the second moment is at most
`K < d² δ` (`d ≥ 0`), then `vhi ≤ d`. -/
lemma le_of_tail_hi {F : Measure ℝ} {vhi : EReal} {δ : ℝ} {K : ℝ≥0∞} {d : ℝ} (hd : 0 ≤ d)
    (hK : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂F ≤ K)
    (hδK : K < ENNReal.ofReal (d ^ 2) * ENNReal.ofReal δ)
    (hmass : ENNReal.ofReal δ ≤ F {x | vhi < (x : EReal)}) : vhi ≤ (d : EReal) := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hsub : {x : ℝ | vhi < (x : EReal)} ⊆
      {x | ENNReal.ofReal (d ^ 2) ≤ ENNReal.ofReal (x ^ 2)} := by
    intro x hx
    have hdx : d < x := EReal.coe_lt_coe_iff.1 (lt_trans hlt hx)
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have h1 := mul_meas_ge_le_lintegral₀ (μ := F) (f := fun x => ENNReal.ofReal (x ^ 2))
    (by fun_prop) (ENNReal.ofReal (d ^ 2))
  have : ENNReal.ofReal (d ^ 2) * ENNReal.ofReal δ ≤ K :=
    calc ENNReal.ofReal (d ^ 2) * ENNReal.ofReal δ
        ≤ ENNReal.ofReal (d ^ 2) * F {x | vhi < (x : EReal)} := by gcongr
      _ ≤ ENNReal.ofReal (d ^ 2) * F {x | ENNReal.ofReal (d ^ 2) ≤ ENNReal.ofReal (x ^ 2)} := by
        gcongr
      _ ≤ _ := h1
      _ ≤ K := hK
  exact absurd hδK (not_lt.2 this)

/-- Markov, lower tail. -/
lemma le_of_tail_lo {F : Measure ℝ} {vlo : EReal} {δ : ℝ} {K : ℝ≥0∞} {d : ℝ} (hd : 0 ≤ d)
    (hK : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂F ≤ K)
    (hδK : K < ENNReal.ofReal (d ^ 2) * ENNReal.ofReal δ)
    (hmass : ENNReal.ofReal δ ≤ F {x | (x : EReal) < vlo}) : ((-d : ℝ) : EReal) ≤ vlo := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hsub : {x : ℝ | (x : EReal) < vlo} ⊆
      {x | ENNReal.ofReal (d ^ 2) ≤ ENNReal.ofReal (x ^ 2)} := by
    intro x hx
    have hdx : x < -d := EReal.coe_lt_coe_iff.1 (lt_trans hx hlt)
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have h1 := mul_meas_ge_le_lintegral₀ (μ := F) (f := fun x => ENNReal.ofReal (x ^ 2))
    (by fun_prop) (ENNReal.ofReal (d ^ 2))
  have : ENNReal.ofReal (d ^ 2) * ENNReal.ofReal δ ≤ K :=
    calc ENNReal.ofReal (d ^ 2) * ENNReal.ofReal δ
        ≤ ENNReal.ofReal (d ^ 2) * F {x | (x : EReal) < vlo} := by gcongr
      _ ≤ ENNReal.ofReal (d ^ 2) * F {x | ENNReal.ofReal (d ^ 2) ≤ ENNReal.ofReal (x ^ 2)} := by
        gcongr
      _ ≤ _ := h1
      _ ≤ K := hK
  exact absurd hδK (not_lt.2 this)

/-- A natural number `n` with `K < n² δ`. -/
lemma exists_nat_sq_mul_gt {K : ℝ≥0∞} (hK : K ≠ ∞) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, K < ENNReal.ofReal ((n : ℝ) ^ 2) * ENNReal.ofReal δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (K.toReal / δ)
  refine ⟨n, ?_⟩
  have h0 : 0 ≤ K.toReal / δ := div_nonneg ENNReal.toReal_nonneg hδ.le
  have hn1 : (1 : ℝ) ≤ n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt h0 hn
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast this.ne')
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_toReal hK,
    ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  rw [div_lt_iff₀ hδ] at hn
  nlinarith

/-- The squared deviation from `c` of a measure with finite second moment. -/
lemma integral_sq_dev (η : Measure ℝ) [IsProbabilityMeasure η] (h1 : Integrable id η)
    (h2 : Integrable (fun y => y ^ 2) η) (c : ℝ) :
    Integrable (fun y => (y - c) ^ 2) η ∧
      ∫ y, (y - c) ^ 2 ∂η = ∫ y, y ^ 2 ∂η - 2 * c * ∫ y, y ∂η + c ^ 2 := by
  have e : (fun y : ℝ => (y - c) ^ 2) = fun y => y ^ 2 - 2 * c * y + c ^ 2 := by
    funext y; ring
  have hi1 : Integrable (fun y : ℝ => 2 * c * y) η := h1.const_mul (2 * c)
  have hi : Integrable (fun y : ℝ => y ^ 2 - 2 * c * y) η := h2.sub hi1
  refine ⟨by rw [e]; exact hi.add (integrable_const _), ?_⟩
  rw [e, integral_add hi (integrable_const _), integral_sub h2 hi1, integral_const_mul]
  simp

end Moments

section Squeeze

/-- From vanishing tails of the pool to `Pr(a_t = c₀) → 1` for the pool's action `c₀`. -/
lemma pool_tendsto_one (F : ℕ → Measure ℝ) [∀ t, IsProbabilityMeasure (F t)]
    (hatom : ∀ t x, F t {x} = 0) (a : ℕ → ℝ → ℝ) (vlo vhi : ℕ → EReal) (c₀ : ℕ → ℝ)
    (hpool : ∀ t (v : ℝ), vlo t < (v : EReal) → (v : EReal) < vhi t → a t v = c₀ t)
    (hhi : Tendsto (fun t => F t {x | vhi t < (x : EReal)}) atTop (𝓝 0))
    (hlo : Tendsto (fun t => F t {x | (x : EReal) < vlo t}) atTop (𝓝 0)) :
    Tendsto (fun t => F t (a t ⁻¹' {c₀ t})) atTop (𝓝 1) := by
  have hlow : Tendsto (fun t => 1 - (F t {x | (x : EReal) < vlo t} + F t {x | vhi t < (x : EReal)}))
      atTop (𝓝 1) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds (hlo.add hhi) (Or.inl ENNReal.one_ne_top)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun t => ?_)
    (fun t => prob_le_one)
  rw [tsub_le_iff_right]
  have hsub : (univ : Set ℝ) ⊆ ((a t ⁻¹' {c₀ t} ∪ {x | (x : EReal) < vlo t}) ∪
      {x | vhi t < (x : EReal)}) ∪ ({x | (x : EReal) = vlo t} ∪ {x | (x : EReal) = vhi t}) := by
    intro x _
    rcases lt_trichotomy (x : EReal) (vlo t) with h | h | h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inr (Or.inl h)
    · rcases lt_trichotomy (x : EReal) (vhi t) with h' | h' | h'
      · exact Or.inl (Or.inl (Or.inl (hpool t x h h')))
      · exact Or.inr (Or.inr h')
      · exact Or.inl (Or.inr h')
  have hnull : ∀ e : EReal, F t {x | (x : EReal) = e} = 0 := by
    intro e
    refine measure_mono_null (fun x hx => ?_) (hatom t e.toReal)
    change (x : EReal) = e at hx
    simp [← hx]
  calc (1 : ℝ≥0∞) = F t univ := measure_univ.symm
    _ ≤ F t (((a t ⁻¹' {c₀ t} ∪ {x | (x : EReal) < vlo t}) ∪ {x | vhi t < (x : EReal)}) ∪
        ({x | (x : EReal) = vlo t} ∪ {x | (x : EReal) = vhi t})) := measure_mono hsub
    _ ≤ F t ((a t ⁻¹' {c₀ t} ∪ {x | (x : EReal) < vlo t}) ∪ {x | vhi t < (x : EReal)}) +
        (F t {x | (x : EReal) = vlo t} + F t {x | (x : EReal) = vhi t}) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ = F t ((a t ⁻¹' {c₀ t} ∪ {x | (x : EReal) < vlo t}) ∪ {x | vhi t < (x : EReal)}) := by
        rw [hnull, hnull, add_zero, add_zero]
    _ ≤ F t (a t ⁻¹' {c₀ t}) + F t {x | (x : EReal) < vlo t} + F t {x | vhi t < (x : EReal)} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = _ := by rw [add_assoc]

/-- A sequence in `[0, ∞]` tends to `0` if it is not frequently above any `δ > 0`. -/
lemma tendsto_zero_of_not_frequently {u : ℕ → ℝ≥0∞}
    (h : ∀ δ : ℝ, 0 < δ → ¬ ∃ᶠ t in atTop, ENNReal.ofReal δ ≤ u t) :
    Tendsto u atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ∞
  · exact Filter.Eventually.of_forall fun t => htop ▸ le_top
  have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  have := Filter.not_frequently.1 (h _ hδ)
  filter_upwards [this] with t ht
  rw [ENNReal.ofReal_toReal htop] at ht
  exact (not_le.1 ht).le

end Squeeze

end CC.LearnTheta.AsmAux
