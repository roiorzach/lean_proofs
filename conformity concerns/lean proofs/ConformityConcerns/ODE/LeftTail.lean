import ConformityConcerns.ODE.Tail

/-!
# Corollary A1 (Left-tail solutions)

Statements (i)–(iv) of Lemma A3 for left-tail solutions of `a'(v) = Ψ(c - v)/Γ(a(v) - v)`.
In (iii)–(iv), `Γ(x) = x` and `Ψ(x) = -κ f(c - x)`, so that the equation reads
`a'(v) = κ f(v)/(v - a(v))`.
-/

namespace CC.ODE

open Set Filter Topology

variable {Ψ Γ : ℝ → ℝ} {c : ℝ}

/-! ### The reflection `x = 2c - v`, `ã(x) = 2c - a(2c - x)` -/

/-- A left-tail solution on `(-∞, d]` reflects to a right-tail solution on `[d', ∞)`,
`d + d' = 2c`. -/
lemma isRightTailSol_of_left {a : ℝ → ℝ} {d d' : ℝ} (hdd : d + d' = 2 * c)
    (ha : IsLeftTailSol Ψ Γ c d a) :
    IsRightTailSol Ψ Γ c d' (fun x => 2 * c - a (2 * c - x)) := by
  obtain ⟨hcont, hC1, hgt, hder⟩ := ha
  refine ⟨?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact continuousOn_const.sub (hcont.comp (continuousOn_const.sub continuousOn_id)
      fun x (hx : d' ≤ x) => mem_Iic.2 (show 2 * c - id x ≤ d by simp only [id]; linarith))
  · exact contDiffOn_const.sub (hC1.comp (contDiffOn_const.sub contDiffOn_id)
      fun x (hx : d' < x) => mem_Iio.2 (show 2 * c - id x < d by simp only [id]; linarith))
  · have := hgt (2 * c - x) (by linarith)
    linarith
  · have h2 := ((hder (2 * c - x) (by linarith)).comp_const_sub (2 * c) x).const_sub (2 * c)
    refine h2.congr_deriv ?_
    rw [neg_neg]
    congr 2 <;> ring

/-- A right-tail solution on `[d', ∞)` reflects to a left-tail solution on `(-∞, d]`,
`d + d' = 2c`. -/
lemma isLeftTailSol_of_right {b : ℝ → ℝ} {d d' : ℝ} (hdd : d + d' = 2 * c)
    (hb : IsRightTailSol Ψ Γ c d' b) :
    IsLeftTailSol Ψ Γ c d (fun v => 2 * c - b (2 * c - v)) := by
  obtain ⟨hcont, hC1, hlt, hder⟩ := hb
  refine ⟨?_, ?_, fun v hv => ?_, fun v hv => ?_⟩
  · exact continuousOn_const.sub (hcont.comp (continuousOn_const.sub continuousOn_id)
      fun x (hx : x ≤ d) => mem_Ici.2 (show d' ≤ 2 * c - id x by simp only [id]; linarith))
  · exact contDiffOn_const.sub (hC1.comp (contDiffOn_const.sub contDiffOn_id)
      fun x (hx : x < d) => mem_Ioi.2 (show d' < 2 * c - id x by simp only [id]; linarith))
  · have := hlt (2 * c - v) (by linarith)
    linarith
  · have h2 := ((hder (2 * c - v) (by linarith)).comp_const_sub (2 * c) v).const_sub (2 * c)
    refine h2.congr_deriv ?_
    rw [neg_neg]
    congr 2 <;> ring

/-- The reflected function `f̃(x) = -f(2c - x)`. -/
lemma reflect_props (κ : ℝ) (f : ℝ → ℝ) (hf : StrictMono f) (hf1 : ContDiff ℝ 1 f)
    (hfc : f c = 0) :
    StrictMono (fun x => -f (2 * c - x)) ∧ ContDiff ℝ 1 (fun x => -f (2 * c - x)) ∧
      (fun x => -f (2 * c - x)) c = 0 ∧
      (∀ x, deriv (fun x => -f (2 * c - x)) x = deriv f (2 * c - x)) ∧
      (fun x => κ * (fun x => -f (2 * c - x)) (c + x)) = fun x => -κ * f (c - x) := by
  refine ⟨fun x y hxy => neg_lt_neg (hf (by linarith)), (hf1.comp (contDiff_const.sub
    contDiff_id)).neg, ?_, fun x => ?_, ?_⟩
  · simp only
    rw [show 2 * c - c = c by ring, hfc, neg_zero]
  · rw [deriv.fun_neg, deriv_comp_const_sub, neg_neg]
  · funext x
    simp only
    rw [show 2 * c - (c + x) = c - x by ring]
    ring

/-- **Corollary A1 (i).** -/
theorem corollaryA1_i (h : TailData Ψ Γ)
    (hlim : ∀ C : ℝ, ∃ ε > 0, ∀ᶠ x in atTop, 1 + ε ≤ Ψ x / Γ (x + C)) :
    ∀ d, d ≤ c → ∀ a, ¬ IsLeftTailSol Ψ Γ c d a := by
  intro d hd a ha
  exact lemmaA3_i h hlim (2 * c - d) (by linarith) _
    (isRightTailSol_of_left (d' := 2 * c - d) (by ring) ha)

/-- **Corollary A1 (ii).** -/
theorem corollaryA1_ii (h : TailData Ψ Γ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΨ : ∀ x, 0 < x → Ψ x ≤ (1 - β) * Γ (β * x)) :
    ∃ a, IsLeftTailSol Ψ Γ c c a ∧ a c = c ∧ ∀ v, v < c → 0 < deriv a v := by
  obtain ⟨b, hb, hbc, -⟩ := lemmaA3_ii (c := c) h β hβ0 hβ1 hΨ
  have ha := isLeftTailSol_of_right (d := c) (by ring) hb
  refine ⟨_, ha, ?_, fun v hv => ?_⟩
  · show 2 * c - b (2 * c - c) = c
    rw [show 2 * c - c = c by ring, hbc]
    ring
  · rw [(ha.2.2.2 v hv).deriv]
    exact div_pos (h.Ψ_pos _ (by linarith)) (h.Γ_pos _ (by linarith [ha.2.2.1 v hv]))

/-- **Corollary A1 (iii).** -/
theorem corollaryA1_iii (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℝ) (hf : StrictMono f)
    (hf1 : ContDiff ℝ 1 f) (hfc : f c = 0) (hsup : ∀ v, v ≤ c → κ * deriv f v ≤ κck) :
    ∃ a, IsLeftTailSol (fun x => -κ * f (c - x)) id c c a ∧ a c = c := by
  obtain ⟨hgm, hg1, hgc, hgd, hΨeq⟩ := reflect_props (c := c) κ f hf hf1 hfc
  obtain ⟨b, hb, hbc⟩ := lemmaA3_iii κ hκ _ hgm hg1 hgc
    (fun v hv => by rw [hgd]; exact hsup _ (by linarith))
  rw [hΨeq] at hb
  refine ⟨_, isLeftTailSol_of_right (d := c) (by ring) hb, ?_⟩
  show 2 * c - b (2 * c - c) = c
  rw [show 2 * c - c = c by ring, hbc]
  ring

/-- **Corollary A1 (iv).** -/
theorem corollaryA1_iv (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℝ) (hf : StrictMono f)
    (hf1 : ContDiff ℝ 1 f) (hfc : f c = 0) (d : ℝ) (hd : d ≤ c)
    (hinf : ∃ m : ℝ, κck < κ * m ∧ ∀ v, v ≤ d → m ≤ deriv f v) :
    ∀ a, ¬ (IsLeftTailSol (fun x => -κ * f (c - x)) id c d a ∧ d ≤ a d) := by
  rintro a ⟨ha, hda⟩
  obtain ⟨hgm, hg1, hgc, hgd, hΨeq⟩ := reflect_props (c := c) κ f hf hf1 hfc
  obtain ⟨m, hm, hmf⟩ := hinf
  have hb := isRightTailSol_of_left (d' := 2 * c - d) (by ring) ha
  rw [← hΨeq] at hb
  refine lemmaA3_iv κ hκ _ hgm hg1 hgc (2 * c - d) (by linarith)
    ⟨m, hm, fun v hv => by rw [hgd]; exact hmf _ (by linarith)⟩ _ ⟨hb, ?_⟩
  show 2 * c - a (2 * c - (2 * c - d)) ≤ 2 * c - d
  rw [show 2 * c - (2 * c - d) = d by ring]
  linarith

/-- The left-tail equation with `Ψ(x) = -κ f(c - x)` and `Γ = id` is `a'(v) = κ f(v)/(v - a(v))`. -/
lemma corollaryA1_equation (κ : ℝ) (f : ℝ → ℝ) (a : ℝ → ℝ) (v : ℝ) :
    (fun x => -κ * f (c - x)) (c - v) / id (a v - v) = κ * f v / (v - a v) := by
  simp only [id, sub_sub_cancel]
  rw [show a v - v = -(v - a v) by ring, div_neg, neg_mul, neg_div, neg_neg]

end CC.ODE
