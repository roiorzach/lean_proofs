import WhoVsWhen.Model

/-!
# Remark 1: the benchmarks

The main result is `remark1`. It compares the headquarters' expected loss (the sum of the two
units' expected losses) across the three timings. The decisions are those of Lemma 1, and the
expected losses come from Lemmas 3 and 4.

* **Public information** is the case where each message reveals its sender's state
  (`Fᵢ = σ(θᵢ)`), so each unit's decision uses the true states.
* **Private information without communication** is the case of uninformative messages (`Fᵢ = ⊥`),
  which gives `cᵢ = σᵢ²`.

The comparisons reduce to polynomial inequalities on `(0, 1)²`. Each is proved with an explicit
certificate: `negF_pos`, `P1_pos`, and `negQ_pos`, the last by a Bernstein-basis expansion with
nonnegative coefficients.
-/

namespace WhoVsWhen

open MeasureTheory

namespace Env

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (E : Env Ω P)

/-- The headquarters' expected loss under sequential decision-making, unit 1 leading. -/
noncomputable def totSeq₁ (r₁ r₂ : ℝ) : ℝ :=
  ∫ ω, L r₁ (E.seqD₁ r₁ r₂ ω) (E.seqD₂ r₁ r₂ ω) (E.θ₁ ω) ∂P
    + ∫ ω, L r₂ (E.seqD₂ r₁ r₂ ω) (E.seqD₁ r₁ r₂ ω) (E.θ₂ ω) ∂P

/-- The headquarters' expected loss under sequential decision-making, unit 2 leading. -/
noncomputable def totSeq₂ (r₁ r₂ : ℝ) : ℝ :=
  ∫ ω, L r₂ (E.swap.seqD₁ r₂ r₁ ω) (E.swap.seqD₂ r₂ r₁ ω) (E.θ₂ ω) ∂P
    + ∫ ω, L r₁ (E.swap.seqD₂ r₂ r₁ ω) (E.swap.seqD₁ r₂ r₁ ω) (E.θ₁ ω) ∂P

/-- The headquarters' expected loss under concurrent decision-making. -/
noncomputable def totConc (r₁ r₂ : ℝ) : ℝ :=
  ∫ ω, L r₁ (E.concD₁ r₁ r₂ ω) (E.concD₂ r₁ r₂ ω) (E.θ₁ ω) ∂P
    + ∫ ω, L r₂ (E.concD₂ r₁ r₂ ω) (E.concD₁ r₁ r₂ ω) (E.θ₂ ω) ∂P

end Env

variable {r₁ r₂ : ℝ}

/-! ### Public information -/

/-- Total public-information loss per unit of `(θ₁ - θ₂)²` under concurrent decision-making. -/
noncomputable def κConc (r₁ r₂ : ℝ) : ℝ :=
  ((1 - r₁) * β r₁ r₂ + (1 - r₂) * β r₂ r₁) / Dn r₁ r₂ ^ 2

/-- Total public-information loss per unit of `(θ₁ - θ₂)²` under sequential decision-making with
leader weight `rL` and follower weight `rF`. -/
noncomputable def κSeq (rL rF : ℝ) : ℝ :=
  (1 - rL) * γ rL rF + (1 - rF) * rF * (1 - γ rL rF) ^ 2

lemma κConc_symm (r₁ r₂ : ℝ) : κConc r₂ r₁ = κConc r₁ r₂ := by
  unfold κConc Dn; ring_nf

/-- The certificate `2 - a - 3ab + ab² + 2a²b - a²b² > 0` on `(0, 1)²`. -/
lemma negF_pos {a b : ℝ} (ha : Unit01 a) (hb : Unit01 b) :
    0 < 2 - a - 3 * a * b + a * b ^ 2 + 2 * a ^ 2 * b - a ^ 2 * b ^ 2 := by
  have key : 2 - a - 3 * a * b + a * b ^ 2 + 2 * a ^ 2 * b - a ^ 2 * b ^ 2 =
      2 * (1 - a) ^ 2 * (1 - b) ^ 2 + 4 * (1 - a) ^ 2 * b * (1 - b) + 2 * (1 - a) ^ 2 * b ^ 2 + 3 * a * (1 - a) * (1 - b) ^ 2 + 3 * a * (1 - a) * b * (1 - b) + a * (1 - a) * b ^ 2 + a ^ 2 * (1 - b) ^ 2 + a ^ 2 * b * (1 - b) := by ring
  rw [key]
  have hu : 0 < 1 - a := by linarith [ha.2]
  have hv : 0 < 1 - b := by linarith [hb.2]
  have := ha.1; have := hb.1
  generalize 1 - a = u at hu ⊢
  generalize 1 - b = v at hv ⊢
  positivity

/-- `κSeq - κConc` in closed form. -/
lemma κSeq_sub_κConc (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) :
    κSeq r₁ r₂ - κConc r₁ r₂ =
      r₁ * r₂ ^ 2 * (1 - r₁) ^ 2 * (1 - r₂) ^ 2 *
        (2 - r₁ - 3 * r₁ * r₂ + r₁ * r₂ ^ 2 + 2 * r₁ ^ 2 * r₂ - r₁ ^ 2 * r₂ ^ 2) /
        (Dn r₁ r₂ ^ 2 * ((1 - r₁) + β r₁ r₂) ^ 2) := by
  have hD := Dn_pos h₁ h₂
  have hden := den_γ_pos h₁ h₂
  unfold κSeq κConc γ
  field_simp
  unfold β Dn; ring

/-- Under public information, concurrent decision-making has a strictly lower total loss
coefficient than sequential decision-making with unit 1 leading. -/
lemma κConc_lt_κSeq (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) : κConc r₁ r₂ < κSeq r₁ r₂ := by
  have hD := Dn_pos h₁ h₂
  have hden := den_γ_pos h₁ h₂
  have hF := negF_pos h₁ h₂
  have h := κSeq_sub_κConc h₁ h₂
  have : 0 < κSeq r₁ r₂ - κConc r₁ r₂ := by
    rw [h]
    have := h₁.1; have := h₂.1
    have : 0 < 1 - r₁ := by linarith [h₁.2]
    have : 0 < 1 - r₂ := by linarith [h₂.2]
    positivity
  linarith

/-- Public information: the expected total losses are `κ · (σ₁² + σ₂²)`, and concurrent
decision-making is strictly better than either sequential order whenever `σ₁² + σ₂² > 0`. -/
lemma public_model_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (E : Env Ω P)
    (hF₁ : E.F₁ = MeasurableSpace.comap E.θ₁ inferInstance)
    (hF₂ : E.F₂ = MeasurableSpace.comap E.θ₂ inferInstance)
    (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) (hs : 0 < E.s₁ + E.s₂) :
    (∫ ω, L r₁ (E.concD₁ r₁ r₂ ω) (E.concD₂ r₁ r₂ ω) (E.θ₁ ω) ∂P
      + ∫ ω, L r₂ (E.concD₂ r₁ r₂ ω) (E.concD₁ r₁ r₂ ω) (E.θ₂ ω) ∂P) <
      (∫ ω, L r₁ (E.seqD₁ r₁ r₂ ω) (E.seqD₂ r₁ r₂ ω) (E.θ₁ ω) ∂P
        + ∫ ω, L r₂ (E.seqD₂ r₁ r₂ ω) (E.seqD₁ r₁ r₂ ω) (E.θ₂ ω) ∂P) ∧
    (∫ ω, L r₁ (E.concD₁ r₁ r₂ ω) (E.concD₂ r₁ r₂ ω) (E.θ₁ ω) ∂P
      + ∫ ω, L r₂ (E.concD₂ r₁ r₂ ω) (E.concD₁ r₁ r₂ ω) (E.θ₂ ω) ∂P) <
      (∫ ω, L r₂ (E.swap.seqD₁ r₂ r₁ ω) (E.swap.seqD₂ r₂ r₁ ω) (E.θ₂ ω) ∂P
        + ∫ ω, L r₁ (E.swap.seqD₂ r₂ r₁ ω) (E.swap.seqD₁ r₂ r₁ ω) (E.θ₁ ω) ∂P) := by
  have c1 := E.c₁_eq_of_full hF₁
  have c2 := E.c₂_eq_of_full hF₂
  rw [E.conc_loss_eq h₁ h₂, E.conc_loss_eq₂ h₁ h₂, E.leader_loss_eq h₁ h₂, E.follower_loss_eq]
  have l2 := E.swap.leader_loss_eq h₂ h₁
  have f2 := E.swap.follower_loss_eq (r₁ := r₂) (r₂ := r₁)
  simp only [Env.swap_θ₁, Env.swap_θ₂, Env.swap_s₁, Env.swap_s₂, Env.swap_c₂] at l2 f2
  rw [l2, f2, c1, c2]
  have hD := Dn_pos h₁ h₂
  have hD' : Dn r₂ r₁ = Dn r₁ r₂ := by unfold Dn; ring
  have conc : concLossF r₁ r₂ E.s₁ E.s₂ 0 0 + concLossF r₂ r₁ E.s₂ E.s₁ 0 0 =
      κConc r₁ r₂ * (E.s₁ + E.s₂) := by
    unfold concLossF κConc; rw [hD']; field_simp; ring
  have seq1 : leaderLossF r₁ r₂ E.s₁ E.s₂ 0 + followerLossF r₁ r₂ E.s₁ E.s₂ 0 =
      κSeq r₁ r₂ * (E.s₁ + E.s₂) := by unfold leaderLossF followerLossF κSeq; ring
  have seq2 : leaderLossF r₂ r₁ E.s₂ E.s₁ 0 + followerLossF r₂ r₁ E.s₂ E.s₁ 0 =
      κSeq r₂ r₁ * (E.s₁ + E.s₂) := by unfold leaderLossF followerLossF κSeq; ring
  rw [conc, seq1, seq2]
  refine ⟨mul_lt_mul_of_pos_right (κConc_lt_κSeq h₁ h₂) hs, ?_⟩
  rw [← κConc_symm]; exact mul_lt_mul_of_pos_right (κConc_lt_κSeq h₂ h₁) hs

/-! ### Private information without communication -/

/-- Total expected loss without communication (`cᵢ = σᵢ²`), sequential, leader weight `rL`. -/
noncomputable def TnoCseq (rL rF sL sF : ℝ) : ℝ :=
  leaderLossF rL rF sL sF sF + followerLossF rL rF sL sF sF

/-- Total expected loss without communication, concurrent. -/
noncomputable def TnoCconc (r₁ r₂ s₁ s₂ : ℝ) : ℝ :=
  concLossF r₁ r₂ s₁ s₂ s₁ s₂ + concLossF r₂ r₁ s₂ s₁ s₂ s₁

lemma TnoCconc_symm (r₁ r₂ s₁ s₂ : ℝ) : TnoCconc r₂ r₁ s₂ s₁ = TnoCconc r₁ r₂ s₁ s₂ := by
  unfold TnoCconc; ring

/-- The gain from letting unit 1 lead instead of deciding concurrently, per unit of `σ₁²`. -/
noncomputable def hgain (a b : ℝ) : ℝ :=
  a * (1 - a) + b * (1 - a) ^ 2 - (1 - a) * γ a b - b * (1 - b) * (1 - γ a b) ^ 2

/-- Without communication, concurrent minus sequential (unit 1 leading) is `σ₁² · hgain r₁ r₂`:
the `σ₂²` terms cancel. -/
lemma TnoC_conc_sub_seq (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) (s₁ s₂ : ℝ) :
    TnoCconc r₁ r₂ s₁ s₂ - TnoCseq r₁ r₂ s₁ s₂ = s₁ * hgain r₁ r₂ := by
  have hD := Dn_pos h₁ h₂
  have hD' : Dn r₂ r₁ = Dn r₁ r₂ := by unfold Dn; ring
  have hden := den_γ_pos h₁ h₂
  unfold TnoCconc TnoCseq concLossF leaderLossF followerLossF hgain
  rw [hD']
  unfold γ
  field_simp
  unfold β Dn; ring

/-- The numerator polynomial of `hgain`. -/
def P1 (a b : ℝ) : ℝ :=
  a ^ 2 * b ^ 4 - 5 * a ^ 2 * b ^ 3 + 8 * a ^ 2 * b ^ 2 - 4 * a ^ 2 * b + 2 * a * b ^ 2
    - 5 * a * b + 2 * a + b

lemma hgain_eq {a b : ℝ} (ha : Unit01 a) (hb : Unit01 b) :
    hgain a b = b * (1 - a) ^ 2 * P1 a b / ((1 - a) + β a b) ^ 2 := by
  have hden := den_γ_pos ha hb
  unfold hgain γ P1
  field_simp
  unfold β; ring

/-- `P1 a b > 0` whenever `0 < a ≤ b < 1`. -/
lemma P1_pos {a b : ℝ} (ha : Unit01 a) (hb : Unit01 b) (hab : a ≤ b) : 0 < P1 a b := by
  have key : P1 a b = (b - a) + a * (1 - b) ^ 2 * (3 * (1 - b) * (1 + b) + b + b ^ 3)
      + a * (b - a) * b * (1 - b) * (1 + (1 - b)) ^ 2 := by unfold P1; ring
  rw [key]
  have hw : 0 ≤ b - a := by linarith
  have hv : 0 < 1 - b := by linarith [hb.2]
  have := ha.1; have := hb.1
  generalize b - a = w at hw ⊢
  generalize 1 - b = v at hv ⊢
  positivity

lemma hgain_pos {a b : ℝ} (ha : Unit01 a) (hb : Unit01 b) (hab : a ≤ b) : 0 < hgain a b := by
  rw [hgain_eq ha hb]
  have := P1_pos ha hb hab
  have := den_γ_pos ha hb
  have := hb.1
  have : 0 < 1 - a := by linarith [ha.2]
  positivity

/-- No communication, closed forms: letting the unit with the lower `r` lead beats concurrent
decision-making, for any volatilities. -/
lemma noComm_never_conc (h₁ : Unit01 r₁) (h₂ : Unit01 r₂)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    (r₁ ≤ r₂ → TnoCseq r₁ r₂ s₁ s₂ < TnoCconc r₁ r₂ s₁ s₂) ∧
      (r₂ ≤ r₁ → TnoCseq r₂ r₁ s₂ s₁ < TnoCconc r₁ r₂ s₁ s₂) := by
  constructor
  · intro h
    have e := TnoC_conc_sub_seq h₁ h₂ s₁ s₂
    have := mul_pos hs₁ (hgain_pos h₁ h₂ h)
    linarith
  · intro h
    have e := TnoC_conc_sub_seq h₂ h₁ s₂ s₁
    have hsym := TnoCconc_symm r₁ r₂ s₁ s₂
    have := mul_pos hs₂ (hgain_pos h₂ h₁ h)
    linarith

/-- The degree-14 polynomial `Q` with `hgain a b - hgain b a = (a - b) Q(a, b) / (…)`. -/
def negQ (a b : ℝ) : ℝ :=
  - a ^ 7 * b ^ 7 + 5 * a ^ 7 * b ^ 6 - 8 * a ^ 7 * b ^ 5 + 4 * a ^ 7 * b ^ 4 + 5 * a ^ 6 * b ^ 7 - 25 * a ^ 6 * b ^ 6 + 38 * a ^ 6 * b ^ 5 - 15 * a ^ 6 * b ^ 4 - 2 * a ^ 6 * b ^ 3 - 8 * a ^ 5 * b ^ 7 + 38 * a ^ 5 * b ^ 6 - 45 * a ^ 5 * b ^ 5 - 7 * a ^ 5 * b ^ 4 + 16 * a ^ 5 * b ^ 3 + 4 * a ^ 4 * b ^ 7 - 15 * a ^ 4 * b ^ 6 - 7 * a ^ 4 * b ^ 5 + 58 * a ^ 4 * b ^ 4 - 22 * a ^ 4 * b ^ 3 - 3 * a ^ 4 * b ^ 2 - 2 * a ^ 3 * b ^ 6 + 16 * a ^ 3 * b ^ 5 - 22 * a ^ 3 * b ^ 4 - 23 * a ^ 3 * b ^ 3 + 11 * a ^ 3 * b ^ 2 - 3 * a ^ 2 * b ^ 4 + 11 * a ^ 2 * b ^ 3 + 11 * a ^ 2 * b ^ 2 - 4 * a ^ 2 * b - 4 * a * b ^ 2 - 3 * a * b + a + b

/-- `-Q > 0` on `(0, 1)²`, by a Bernstein-basis certificate with nonnegative integer
coefficients. -/
lemma negQ_pos {a b : ℝ} (ha : Unit01 a) (hb : Unit01 b) : 0 < negQ a b := by
  have key : negQ a b = (1 - a) ^ 7 * b * (1 - b) ^ 6 + 6 * (1 - a) ^ 7 * b ^ 2 * (1 - b) ^ 5 + 15 * (1 - a) ^ 7 * b ^ 3 * (1 - b) ^ 4 + 20 * (1 - a) ^ 7 * b ^ 4 * (1 - b) ^ 3 + 15 * (1 - a) ^ 7 * b ^ 5 * (1 - b) ^ 2 + 6 * (1 - a) ^ 7 * b ^ 6 * (1 - b) + (1 - a) ^ 7 * b ^ 7 + a * (1 - a) ^ 6 * (1 - b) ^ 7 + 11 * a * (1 - a) ^ 6 * b * (1 - b) ^ 6 + 41 * a * (1 - a) ^ 6 * b ^ 2 * (1 - b) ^ 5 + 75 * a * (1 - a) ^ 6 * b ^ 3 * (1 - b) ^ 4 + 75 * a * (1 - a) ^ 6 * b ^ 4 * (1 - b) ^ 3 + 41 * a * (1 - a) ^ 6 * b ^ 5 * (1 - b) ^ 2 + 11 * a * (1 - a) ^ 6 * b ^ 6 * (1 - b) + a * (1 - a) ^ 6 * b ^ 7 + 6 * a ^ 2 * (1 - a) ^ 5 * (1 - b) ^ 7 + 41 * a ^ 2 * (1 - a) ^ 5 * b * (1 - b) ^ 6 + 107 * a ^ 2 * (1 - a) ^ 5 * b ^ 2 * (1 - b) ^ 5 + 141 * a ^ 2 * (1 - a) ^ 5 * b ^ 3 * (1 - b) ^ 4 + 101 * a ^ 2 * (1 - a) ^ 5 * b ^ 4 * (1 - b) ^ 3 + 38 * a ^ 2 * (1 - a) ^ 5 * b ^ 5 * (1 - b) ^ 2 + 6 * a ^ 2 * (1 - a) ^ 5 * b ^ 6 * (1 - b) + 15 * a ^ 3 * (1 - a) ^ 4 * (1 - b) ^ 7 + 75 * a ^ 3 * (1 - a) ^ 4 * b * (1 - b) ^ 6 + 141 * a ^ 3 * (1 - a) ^ 4 * b ^ 2 * (1 - b) ^ 5 + 137 * a ^ 3 * (1 - a) ^ 4 * b ^ 3 * (1 - b) ^ 4 + 76 * a ^ 3 * (1 - a) ^ 4 * b ^ 4 * (1 - b) ^ 3 + 22 * a ^ 3 * (1 - a) ^ 4 * b ^ 5 * (1 - b) ^ 2 + 2 * a ^ 3 * (1 - a) ^ 4 * b ^ 6 * (1 - b) + 20 * a ^ 4 * (1 - a) ^ 3 * (1 - b) ^ 7 + 75 * a ^ 4 * (1 - a) ^ 3 * b * (1 - b) ^ 6 + 101 * a ^ 4 * (1 - a) ^ 3 * b ^ 2 * (1 - b) ^ 5 + 76 * a ^ 4 * (1 - a) ^ 3 * b ^ 3 * (1 - b) ^ 4 + 34 * a ^ 4 * (1 - a) ^ 3 * b ^ 4 * (1 - b) ^ 3 + 8 * a ^ 4 * (1 - a) ^ 3 * b ^ 5 * (1 - b) ^ 2 + 15 * a ^ 5 * (1 - a) ^ 2 * (1 - b) ^ 7 + 41 * a ^ 5 * (1 - a) ^ 2 * b * (1 - b) ^ 6 + 38 * a ^ 5 * (1 - a) ^ 2 * b ^ 2 * (1 - b) ^ 5 + 22 * a ^ 5 * (1 - a) ^ 2 * b ^ 3 * (1 - b) ^ 4 + 8 * a ^ 5 * (1 - a) ^ 2 * b ^ 4 * (1 - b) ^ 3 + 2 * a ^ 5 * (1 - a) ^ 2 * b ^ 5 * (1 - b) ^ 2 + 6 * a ^ 6 * (1 - a) * (1 - b) ^ 7 + 11 * a ^ 6 * (1 - a) * b * (1 - b) ^ 6 + 6 * a ^ 6 * (1 - a) * b ^ 2 * (1 - b) ^ 5 + 2 * a ^ 6 * (1 - a) * b ^ 3 * (1 - b) ^ 4 + a ^ 7 * (1 - b) ^ 7 + a ^ 7 * b * (1 - b) ^ 6 := by
    unfold negQ; ring
  rw [key]
  have hu : 0 < 1 - a := by linarith [ha.2]
  have hv : 0 < 1 - b := by linarith [hb.2]
  have := ha.1; have := hb.1
  generalize 1 - a = u at hu ⊢
  generalize 1 - b = v at hv ⊢
  positivity

lemma hgain_sub_swap {a b : ℝ} (ha : Unit01 a) (hb : Unit01 b) :
    hgain a b - hgain b a =
      (b - a) * negQ a b / (((1 - a) + β a b) ^ 2 * ((1 - b) + β b a) ^ 2) := by
  have h1 := den_γ_pos ha hb
  have h2 := den_γ_pos hb ha
  rw [hgain_eq ha hb, hgain_eq hb ha]
  unfold P1 negQ
  field_simp
  unfold β; ring

/-- No communication, closed forms, equal volatilities: if `r₁ < r₂`, unit 1 leading beats both
unit 2 leading and concurrent decision-making. -/
lemma noComm_equalVol (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) {s : ℝ} (hs : 0 < s)
    (hr : r₁ < r₂) :
    TnoCseq r₁ r₂ s s < TnoCseq r₂ r₁ s s ∧ TnoCseq r₁ r₂ s s < TnoCconc r₁ r₂ s s := by
  have e1 := TnoC_conc_sub_seq h₁ h₂ s s
  have e2 := TnoC_conc_sub_seq h₂ h₁ s s
  rw [TnoCconc_symm] at e2
  have hd := hgain_sub_swap h₁ h₂
  have hq := negQ_pos h₁ h₂
  have hpos : 0 < hgain r₁ r₂ - hgain r₂ r₁ := by
    rw [hd]
    have := den_γ_pos h₁ h₂
    have := den_γ_pos h₂ h₁
    have : 0 < r₂ - r₁ := by linarith
    positivity
  have := hgain_pos h₁ h₂ hr.le
  constructor <;> nlinarith

/-- With uninformative messages (`F₁ = F₂ = ⊥`) the expected total losses of Lemmas 3 and 4 are
`TnoCseq` and `TnoCconc`. -/
lemma noComm_model {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (E : Env Ω P) (hF₁ : E.F₁ = ⊥) (hF₂ : E.F₂ = ⊥)
    (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) :
    (∫ ω, L r₁ (E.seqD₁ r₁ r₂ ω) (E.seqD₂ r₁ r₂ ω) (E.θ₁ ω) ∂P
        + ∫ ω, L r₂ (E.seqD₂ r₁ r₂ ω) (E.seqD₁ r₁ r₂ ω) (E.θ₂ ω) ∂P) =
      TnoCseq r₁ r₂ E.s₁ E.s₂ ∧
    (∫ ω, L r₂ (E.swap.seqD₁ r₂ r₁ ω) (E.swap.seqD₂ r₂ r₁ ω) (E.θ₂ ω) ∂P
        + ∫ ω, L r₁ (E.swap.seqD₂ r₂ r₁ ω) (E.swap.seqD₁ r₂ r₁ ω) (E.θ₁ ω) ∂P) =
      TnoCseq r₂ r₁ E.s₂ E.s₁ ∧
    (∫ ω, L r₁ (E.concD₁ r₁ r₂ ω) (E.concD₂ r₁ r₂ ω) (E.θ₁ ω) ∂P
        + ∫ ω, L r₂ (E.concD₂ r₁ r₂ ω) (E.concD₁ r₁ r₂ ω) (E.θ₂ ω) ∂P) =
      TnoCconc r₁ r₂ E.s₁ E.s₂ := by
  have c1 := E.c₁_eq_of_bot hF₁
  have c2 := E.c₂_eq_of_bot hF₂
  have l2 := E.swap.leader_loss_eq h₂ h₁
  have f2 := E.swap.follower_loss_eq (r₁ := r₂) (r₂ := r₁)
  simp only [Env.swap_θ₁, Env.swap_θ₂, Env.swap_s₁, Env.swap_s₂, Env.swap_c₂] at l2 f2
  refine ⟨?_, ?_, ?_⟩
  · rw [E.leader_loss_eq h₁ h₂, E.follower_loss_eq, c2]; rfl
  · rw [l2, f2, c1]; rfl
  · rw [E.conc_loss_eq h₁ h₂, E.conc_loss_eq₂ h₁ h₂, c1, c2]; rfl

/-! ### Remark 1 -/

/-- **Remark 1** (with the equal-volatility condition of Appendix A.5 made explicit).

1. With public information, concurrent decision-making is strictly better than either sequential
   order.
2. With private information but no communication, concurrent decision-making is never optimal:
   one of the sequential orders is strictly better.
3. With private information but no communication and equal volatilities, the optimal structure
   has the unit that cares more about coordination move second. -/
theorem remark1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h₁ : Unit01 r₁) (h₂ : Unit01 r₂) :
    (∀ E : Env Ω P, E.F₁ = MeasurableSpace.comap E.θ₁ inferInstance →
      E.F₂ = MeasurableSpace.comap E.θ₂ inferInstance → 0 < E.s₁ + E.s₂ →
      E.totConc r₁ r₂ < E.totSeq₁ r₁ r₂ ∧ E.totConc r₁ r₂ < E.totSeq₂ r₁ r₂) ∧
    (∀ E : Env Ω P, E.F₁ = ⊥ → E.F₂ = ⊥ → 0 < E.s₁ → 0 < E.s₂ →
      E.totSeq₁ r₁ r₂ < E.totConc r₁ r₂ ∨ E.totSeq₂ r₁ r₂ < E.totConc r₁ r₂) ∧
    (∀ E : Env Ω P, E.F₁ = ⊥ → E.F₂ = ⊥ → 0 < E.s₁ → E.s₁ = E.s₂ →
      (r₁ < r₂ → E.totSeq₁ r₁ r₂ < E.totSeq₂ r₁ r₂ ∧ E.totSeq₁ r₁ r₂ < E.totConc r₁ r₂) ∧
      (r₂ < r₁ → E.totSeq₂ r₁ r₂ < E.totSeq₁ r₁ r₂ ∧ E.totSeq₂ r₁ r₂ < E.totConc r₁ r₂)) := by
  refine ⟨fun E hF₁ hF₂ hs => public_model_lt E hF₁ hF₂ h₁ h₂ hs, ?_, ?_⟩
  · intro E hF₁ hF₂ hs₁ hs₂
    obtain ⟨e1, e2, e3⟩ := noComm_model E hF₁ hF₂ h₁ h₂
    unfold Env.totSeq₁ Env.totSeq₂ Env.totConc
    rw [e1, e2, e3]
    rcases le_total r₁ r₂ with h | h
    · exact Or.inl ((noComm_never_conc h₁ h₂ hs₁ hs₂).1 h)
    · exact Or.inr ((noComm_never_conc h₁ h₂ hs₁ hs₂).2 h)
  · intro E hF₁ hF₂ hs hss
    obtain ⟨e1, e2, e3⟩ := noComm_model E hF₁ hF₂ h₁ h₂
    unfold Env.totSeq₁ Env.totSeq₂ Env.totConc
    rw [e1, e2, e3, ← hss]
    refine ⟨fun hr => noComm_equalVol h₁ h₂ hs hr, fun hr => ?_⟩
    have := noComm_equalVol h₂ h₁ hs hr
    rwa [TnoCconc_symm r₁ r₂ E.s₁ E.s₁] at this

end WhoVsWhen
