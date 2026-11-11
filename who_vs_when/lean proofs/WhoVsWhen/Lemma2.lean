import WhoVsWhen.Lemma1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Lemma 2: information loss

The information loss about state `i` is `cᵢ = Var(θᵢ - 𝔼(θᵢ | mᵢ))` in the limit partition.
The argument has four steps, each proved here.

1. **The sender's payoff.** Inducing a posterior mean `μ` gives the sender (the follower under
   sequential decision-making, or either unit under concurrent decision-making) an expected loss
   of the form `A μ² - 2 B k μ + C(k)` with `A > 0`, where `k` is its type
   (`followerMsgLoss_eq`, `concMsgLoss_eq`).
2. **Indifference.** A boundary type `k` is indifferent between two adjacent cells if and only if
   the cell means satisfy `A (μ + μ') = 2 B k`. With uniform cell means `(kₙ₋₁ + kₙ)/2` this is
   the difference equation of footnote 9, `kₙ₊₁ - kₙ = kₙ - kₙ₋₁ + (4/φ) kₙ`, with
   `φ_{2,sequential} = β₁/(1 - r₁)` (`follower_indiff_iff`) and
   `φ_{i,concurrent} = rⱼ (1 - rᵢ)/(1 - rⱼ)` (`conc_indiff_iff`).
3. **The limit partition.** As the number of cells grows, the partition becomes the geometric one
   with boundaries `± θ̄ yᵐ`, where `y ∈ (0, 1)` solves `y + 1/y = 2 + 4/φ`. This is the only
   solution of the difference equation that starts at `θ̄` and accumulates at `0`
   (`limitPartition_unique`).
4. **The information loss.** The loss in that partition is `σ² / (3φ + 4)` with `σ² = θ̄²/3`
   (`infoLoss_geometric`).

The main result `lemma2` assembles these steps. The leader's state is revealed by its decision
(`leader_decision_injective`), which is the meaning of `φ_{1,sequential} = ∞`.

**Convention.** For a partition of `[-θ̄, θ̄]` into cells, the information loss
`𝔼[(θ - 𝔼(θ | m))²]` is computed cell by cell as `∑_cells P(cell) · Var(θ | cell)`, which is what
the expectation equals when the message names the cell. For the uniform distribution,
`P(cell) Var(θ | cell) = (1/(2θ̄)) ∫_cell (θ - mean)² dθ` (`cellLoss`).
-/

namespace WhoVsWhen

open MeasureTheory Filter Topology intervalIntegral

/-! ### Uniform distribution: cell means and cell variances -/

/-- The conditional mean of a uniformly distributed state on the cell `[a, b]`. -/
noncomputable def cellMean (a b : ℝ) : ℝ := (∫ x in a..b, x) / (b - a)

lemma cellMean_eq {a b : ℝ} (h : a ≠ b) : cellMean a b = (a + b) / 2 := by
  unfold cellMean; rw [integral_id]
  have : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp; ring

/-- `∫_a^b (θ - 𝔼(θ | cell))² dθ`; divided by `2θ̄` it is `P(cell) · Var(θ | cell)` for the
uniform distribution on `[-θ̄, θ̄]`. -/
noncomputable def cellLoss (a b : ℝ) : ℝ := ∫ x in a..b, (x - cellMean a b) ^ 2

lemma cellLoss_eq {a b : ℝ} (h : a ≠ b) : cellLoss a b = (b - a) ^ 3 / 12 := by
  unfold cellLoss; rw [cellMean_eq h]
  have := intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ 2) (a := a) (b := b)
    ((a + b) / 2)
  rw [this, integral_pow]; ring

/-- The variance `σ² = (1/(2θ̄)) ∫_{-θ̄}^{θ̄} θ² dθ` of the uniform distribution on `[-θ̄, θ̄]`. -/
noncomputable def uniformVar (θbar : ℝ) : ℝ := 1 / (2 * θbar) * ∫ x in (-θbar)..θbar, x ^ 2

lemma uniformVar_eq {θbar : ℝ} (h : 0 < θbar) : uniformVar θbar = θbar ^ 2 / 3 := by
  unfold uniformVar; rw [integral_pow]; field_simp; ring

/-! ### Step 1–2: indifference conditions and the difference equation -/

/-- A sender whose expected loss from inducing posterior mean `μ` is `A μ² - 2 B k μ + C` is
indifferent between two distinct posterior means `μ ≠ μ'` iff `A (μ + μ') = 2 B k`. -/
lemma quad_indiff_iff {A B C k μ μ' : ℝ} (hμ : μ ≠ μ') :
    A * μ ^ 2 - 2 * B * k * μ + C = A * μ' ^ 2 - 2 * B * k * μ' + C ↔
      A * (μ + μ') = 2 * B * k := by
  have hne : μ - μ' ≠ 0 := sub_ne_zero.mpr hμ
  constructor
  · intro h
    have : (μ - μ') * (A * (μ + μ') - 2 * B * k) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hne
    · linarith
  · intro h; linear_combination (μ - μ') * h

/-- With uniform cell means, `A (μₙ + μₙ₊₁) = 2 B kₙ` is the difference equation
`kₙ₊₁ - kₙ = kₙ - kₙ₋₁ + 4 (B/A - 1) kₙ`. -/
lemma cells_indiff_iff {A B kl k ku : ℝ} (hA : A ≠ 0) :
    A * ((kl + k) / 2 + (k + ku) / 2) = 2 * B * k ↔ ku - k = k - kl + 4 * (B / A - 1) * k := by
  have hAA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  constructor
  · intro h; rw [div_eq_mul_inv]; linear_combination (2 / A) * h - (kl + 2 * k + ku) * hAA
  · intro h; rw [div_eq_mul_inv] at h; linear_combination (A / 2) * h + (2 * B * k) * hAA

/-- The follower's expected loss (sequential decision-making, unit 1 leads) from sending a
message that leads the leader to posterior mean `μ`, when its own state is `θ₂`. The leader then
plays `d₁ = (1 - γ₁) θ₁ + γ₁ μ` (Lemma 1) and the follower best-responds. The expectation is over
the leader's state `θ₁ ∼ ν₁`. -/
noncomputable def followerMsgLoss (r₁ r₂ : ℝ) (ν₁ : Measure ℝ) (θ₂ μ : ℝ) : ℝ :=
  ∫ θ₁, L r₂ ((1 - r₂) * θ₂ + r₂ * ((1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * μ))
    ((1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * μ) θ₂ ∂ν₁

lemma followerMsgLoss_eq {ν₁ : Measure ℝ} [IsProbabilityMeasure ν₁]
    (h1 : Integrable (fun x : ℝ => x) ν₁) (h2 : Integrable (fun x : ℝ => x ^ 2) ν₁)
    (hmean : ∫ x, x ∂ν₁ = 0) (r₁ r₂ θ₂ μ : ℝ) :
    followerMsgLoss r₁ r₂ ν₁ θ₂ μ =
      (1 - r₂) * r₂ * ((1 - γ r₁ r₂) ^ 2 * ∫ x, x ^ 2 ∂ν₁ + (γ r₁ r₂ * μ - θ₂) ^ 2) := by
  unfold followerMsgLoss
  have hpt : ∀ θ₁, L r₂ ((1 - r₂) * θ₂ + r₂ * ((1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * μ))
      ((1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * μ) θ₂ =
      (1 - r₂) * r₂ * (γ r₁ r₂ * μ - θ₂) ^ 2
        + (2 * (1 - r₂) * r₂ * (1 - γ r₁ r₂) * (γ r₁ r₂ * μ - θ₂)) * θ₁
        + ((1 - r₂) * r₂ * (1 - γ r₁ r₂) ^ 2) * θ₁ ^ 2 := by
    intro θ₁; rw [follower_value]; ring
  simp_rw [hpt]; rw [integral_quad h1 h2, hmean]; ring

/-- Indifference of the follower. A follower of type `k` on the boundary
of two adjacent cells `[kl, k]` and `[k, ku]` (`kl ≠ ku`), whose uniform means are the leader's
posterior means, is indifferent between them iff
`ku - k = k - kl + (4 / φ_{2,sequential}) k`. -/
lemma follower_indiff_iff {ν₁ : Measure ℝ} [IsProbabilityMeasure ν₁]
    (h1 : Integrable (fun x : ℝ => x) ν₁) (h2 : Integrable (fun x : ℝ => x ^ 2) ν₁)
    (hmean : ∫ x, x ∂ν₁ = 0) {r₁ r₂ : ℝ} (hr₁ : Unit01 r₁) (hr₂ : Unit01 r₂)
    {kl k ku : ℝ} (hl : kl ≠ k) (hu : k ≠ ku) (hlu : kl ≠ ku) :
    followerMsgLoss r₁ r₂ ν₁ k (cellMean kl k) = followerMsgLoss r₁ r₂ ν₁ k (cellMean k ku) ↔
      ku - k = k - kl + 4 / φSeq r₁ r₂ * k := by
  have hγ := γ_pos hr₁ hr₂
  have hγ1 := γ_lt_one hr₁ hr₂
  have hc : 0 < (1 - r₂) * r₂ := mul_pos (by linarith [hr₂.2]) hr₂.1
  rw [followerMsgLoss_eq h1 h2 hmean, followerMsgLoss_eq h1 h2 hmean, cellMean_eq hl,
    cellMean_eq hu]
  have hform : ∀ μ, (1 - r₂) * r₂ * ((1 - γ r₁ r₂) ^ 2 * ∫ x, x ^ 2 ∂ν₁ + (γ r₁ r₂ * μ - k) ^ 2) =
      ((1 - r₂) * r₂ * γ r₁ r₂ ^ 2) * μ ^ 2 - 2 * ((1 - r₂) * r₂ * γ r₁ r₂) * k * μ
        + (1 - r₂) * r₂ * ((1 - γ r₁ r₂) ^ 2 * ∫ x, x ^ 2 ∂ν₁ + k ^ 2) := by
    intro μ; ring
  have hμ : (kl + k) / 2 ≠ (k + ku) / 2 := by intro h; apply hlu; linarith
  have hA : (1 - r₂) * r₂ * γ r₁ r₂ ^ 2 ≠ 0 := by positivity
  rw [hform, hform, quad_indiff_iff hμ, cells_indiff_iff hA]
  have : (1 - r₂) * r₂ * γ r₁ r₂ / ((1 - r₂) * r₂ * γ r₁ r₂ ^ 2) - 1 = 1 / φSeq r₁ r₂ := by
    rw [φSeq_eq_γ hr₁ hr₂]
    have : (1 - γ r₁ r₂) ≠ 0 := by linarith
    have : γ r₁ r₂ ≠ 0 := hγ.ne'
    have : (1 - r₂) ≠ 0 := by linarith [hr₂.2]
    have : r₂ ≠ 0 := hr₂.1.ne'
    field_simp
  rw [this]; constructor <;> intro h <;> linear_combination h

/-! The concurrent sender. -/

section Concurrent

variable {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]

/-- Integral of a quadratic polynomial in two variables against a probability measure whose
coordinates are square-integrable. -/
lemma integral_quad2 (hx : MemLp (fun p : ℝ × ℝ => p.1) 2 ρ) (hy : MemLp (fun p : ℝ × ℝ => p.2) 2 ρ)
    (c0 c1 c2 c3 c4 c5 : ℝ) :
    ∫ p, (c0 + c1 * p.1 + c2 * p.2 + c3 * p.1 ^ 2 + c4 * p.2 ^ 2 + c5 * (p.1 * p.2)) ∂ρ =
      c0 + c1 * (∫ p, p.1 ∂ρ) + c2 * (∫ p, p.2 ∂ρ) + c3 * (∫ p, p.1 ^ 2 ∂ρ)
        + c4 * (∫ p, p.2 ^ 2 ∂ρ) + c5 * (∫ p, p.1 * p.2 ∂ρ) := by
  have i1 : Integrable (fun p : ℝ × ℝ => p.1) ρ := hx.integrable one_le_two
  have i2 : Integrable (fun p : ℝ × ℝ => p.2) ρ := hy.integrable one_le_two
  have i3 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ρ := hx.integrable_sq
  have i4 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) ρ := hy.integrable_sq
  have i5 : Integrable (fun p : ℝ × ℝ => p.1 * p.2) ρ := hx.integrable_mul hy
  have j1 : Integrable (fun p : ℝ × ℝ => c0 + c1 * p.1) ρ := (integrable_const c0).add (i1.const_mul c1)
  have j2 : Integrable (fun p : ℝ × ℝ => c0 + c1 * p.1 + c2 * p.2) ρ := j1.add (i2.const_mul c2)
  have j3 : Integrable (fun p : ℝ × ℝ => c0 + c1 * p.1 + c2 * p.2 + c3 * p.1 ^ 2) ρ :=
    j2.add (i3.const_mul c3)
  have j4 : Integrable (fun p : ℝ × ℝ => c0 + c1 * p.1 + c2 * p.2 + c3 * p.1 ^ 2 + c4 * p.2 ^ 2) ρ :=
    j3.add (i4.const_mul c4)
  rw [integral_add j4 (i5.const_mul c5), integral_add j3 (i4.const_mul c4),
    integral_add j2 (i3.const_mul c3), integral_add j1 (i2.const_mul c2),
    integral_add (integrable_const c0) (i1.const_mul c1)]
  simp [MeasureTheory.integral_const_mul]

/-- Unit `i`'s expected loss under concurrent decision-making from sending a message that induces
posterior mean `μ` about its state, when its state is `θᵢ`. Both units use the linear equilibrium
rules (Lemma 1); the expectation is over the joint law `ρ` of the other unit's state and the
posterior mean its message induces, `(θⱼ, μⱼ)`. -/
noncomputable def concMsgLoss (ri rj : ℝ) (ρ : Measure (ℝ × ℝ)) (θi μ : ℝ) : ℝ :=
  ∫ p, L ri (concRule ri rj θi μ p.2) (concRule rj ri p.1 p.2 μ) θi ∂ρ

/-- The part of the concurrent sender's expected loss that does not depend on its message. -/
noncomputable def concMsgConst (ri rj : ℝ) (ρ : Measure (ℝ × ℝ)) : ℝ :=
  (1 - ri) * bOth ri rj ^ 2 * (∫ p, p.2 ^ 2 ∂ρ)
    + ri * ((1 - rj) ^ 2 * (∫ p, p.1 ^ 2 ∂ρ)
      + 2 * (1 - rj) * (eOwn rj ri - bOth ri rj) * (∫ p, p.1 * p.2 ∂ρ)
      + (eOwn rj ri - bOth ri rj) ^ 2 * (∫ p, p.2 ^ 2 ∂ρ))

lemma concMsgLoss_eq (hx : MemLp (fun p : ℝ × ℝ => p.1) 2 ρ)
    (hy : MemLp (fun p : ℝ × ℝ => p.2) 2 ρ) (hm1 : ∫ p, p.1 ∂ρ = 0) (hm2 : ∫ p, p.2 ∂ρ = 0)
    (ri rj θi μ : ℝ) :
    concMsgLoss ri rj ρ θi μ =
      (1 - ri) * (ri * θi - eOwn ri rj * μ) ^ 2
        + ri * ((bOth rj ri - eOwn ri rj) * μ - (1 - ri) * θi) ^ 2 + concMsgConst ri rj ρ := by
  unfold concMsgLoss concMsgConst
  set X := ri * θi - eOwn ri rj * μ
  set Y := (bOth rj ri - eOwn ri rj) * μ - (1 - ri) * θi
  have hpt : ∀ p : ℝ × ℝ, L ri (concRule ri rj θi μ p.2) (concRule rj ri p.1 p.2 μ) θi =
      ((1 - ri) * X ^ 2 + ri * Y ^ 2) + (ri * 2 * Y * (1 - rj)) * p.1
        + ((1 - ri) * (-2 * X * bOth ri rj) + ri * 2 * Y * (eOwn rj ri - bOth ri rj)) * p.2
        + (ri * (1 - rj) ^ 2) * p.1 ^ 2
        + ((1 - ri) * bOth ri rj ^ 2 + ri * (eOwn rj ri - bOth ri rj) ^ 2) * p.2 ^ 2
        + (ri * 2 * (1 - rj) * (eOwn rj ri - bOth ri rj)) * (p.1 * p.2) := by
    intro p; simp only [X, Y]; unfold L concRule; ring
  simp_rw [hpt]; rw [integral_quad2 hx hy, hm1, hm2]; ring

/-- Indifference of a concurrent sender. Unit `i` of type `k` on the
boundary of adjacent cells `[kl, k]`, `[k, ku]` is indifferent between them iff
`ku - k = k - kl + (4 / φ_{i,concurrent}) k`. -/
lemma conc_indiff_iff (hx : MemLp (fun p : ℝ × ℝ => p.1) 2 ρ)
    (hy : MemLp (fun p : ℝ × ℝ => p.2) 2 ρ) (hm1 : ∫ p, p.1 ∂ρ = 0) (hm2 : ∫ p, p.2 ∂ρ = 0)
    {ri rj : ℝ} (hi : Unit01 ri) (hj : Unit01 rj)
    {kl k ku : ℝ} (hl : kl ≠ k) (hu : k ≠ ku) (hlu : kl ≠ ku) :
    concMsgLoss ri rj ρ k (cellMean kl k) = concMsgLoss ri rj ρ k (cellMean k ku) ↔
      ku - k = k - kl + 4 / φConc ri rj * k := by
  rw [concMsgLoss_eq hx hy hm1 hm2, concMsgLoss_eq hx hy hm1 hm2, cellMean_eq hl, cellMean_eq hu]
  have hD := Dn_pos hi hj
  have hD' : Dn rj ri = Dn ri rj := by unfold Dn; ring
  have hform : ∀ μ, (1 - ri) * (ri * k - eOwn ri rj * μ) ^ 2
      + ri * ((bOth rj ri - eOwn ri rj) * μ - (1 - ri) * k) ^ 2 + concMsgConst ri rj ρ =
      ((1 - ri) * eOwn ri rj ^ 2 + ri * (bOth rj ri - eOwn ri rj) ^ 2) * μ ^ 2
        - 2 * (ri * (1 - ri) * bOth rj ri) * k * μ
        + ((1 - ri) * (ri * k) ^ 2 + ri * ((1 - ri) * k) ^ 2 + concMsgConst ri rj ρ) := by
    intro μ; ring
  have hμ : (kl + k) / 2 ≠ (k + ku) / 2 := by intro h; apply hlu; linarith
  have hD0 : Dn ri rj ≠ 0 := hD.ne'
  have hA' : (1 - ri) * eOwn ri rj ^ 2 + ri * (bOth rj ri - eOwn ri rj) ^ 2 =
      ri * rj ^ 2 * (1 - ri) ^ 3 / Dn ri rj ^ 2 := by
    unfold eOwn bOth; rw [hD']; field_simp; ring
  have hB' : ri * (1 - ri) * bOth rj ri = ri * rj * (1 - ri) ^ 2 / Dn ri rj := by
    unfold bOth; rw [hD']; field_simp
  have hA : (1 - ri) * eOwn ri rj ^ 2 + ri * (bOth rj ri - eOwn ri rj) ^ 2 ≠ 0 := by
    rw [hA']; have := hi.1; have := hj.1; have : 0 < 1 - ri := by linarith [hi.2]
    positivity
  rw [hform, hform, quad_indiff_iff hμ, cells_indiff_iff hA]
  have : ri * (1 - ri) * bOth rj ri /
      ((1 - ri) * eOwn ri rj ^ 2 + ri * (bOth rj ri - eOwn ri rj) ^ 2) - 1 = 1 / φConc ri rj := by
    rw [hA', hB']; unfold φConc
    have : ri ≠ 0 := hi.1.ne'
    have : rj ≠ 0 := hj.1.ne'
    have h1i : (1 : ℝ) - ri ≠ 0 := by linarith [hi.2]
    have h1j : (1 : ℝ) - rj ≠ 0 := by linarith [hj.2]
    field_simp; unfold Dn; ring
  rw [this]; constructor <;> intro h <;> linear_combination h

end Concurrent

/-! ### Step 3: the limit partition -/

/-- The ratio `y ∈ (0, 1)` of the limit partition, the smaller root of `y + 1/y = 2 + 4/φ`. -/
noncomputable def yRatio (φ : ℝ) : ℝ := (1 + 2 / φ) - Real.sqrt ((1 + 2 / φ) ^ 2 - 1)

section Ratio

variable {φ : ℝ} (hφ : 0 < φ)
include hφ

lemma yRatio_aux : 1 < 1 + 2 / φ := by
  have : 0 < 2 / φ := by positivity
  linarith

lemma yRatio_pos : 0 < yRatio φ := by
  have ht := yRatio_aux hφ
  unfold yRatio
  have : Real.sqrt ((1 + 2 / φ) ^ 2 - 1) < 1 + 2 / φ := by
    rw [Real.sqrt_lt' (by linarith)]; linarith
  linarith

lemma yRatio_lt_one : yRatio φ < 1 := by
  have ht := yRatio_aux hφ
  unfold yRatio
  have : 2 / φ < Real.sqrt ((1 + 2 / φ) ^ 2 - 1) := by
    rw [Real.lt_sqrt (by positivity)]
    have h2 : 0 < 2 / φ := by positivity
    nlinarith
  linarith

/-- `y` solves `y² - (2 + 4/φ) y + 1 = 0`, i.e. `y + 1/y = 2 + 4/φ`. -/
lemma yRatio_quadratic : yRatio φ ^ 2 + 1 = (2 + 4 / φ) * yRatio φ := by
  have ht := yRatio_aux hφ
  have hs : Real.sqrt ((1 + 2 / φ) ^ 2 - 1) ^ 2 = (1 + 2 / φ) ^ 2 - 1 :=
    Real.sq_sqrt (by nlinarith)
  unfold yRatio; linear_combination hs

end Ratio

/-- The geometric limit partition: positive boundaries `θ̄ yᵐ`, `m = 0, 1, 2, …`. -/
noncomputable def geomPartition (θbar φ : ℝ) : ℕ → ℝ := fun m => θbar * yRatio φ ^ m

/-- The difference equation of footnote 9 written for the positive boundaries `a 0 = θ̄ > a 1 > ⋯`
of a partition, indexed from the top: `a (m-1) - a m = a m - a (m+1) + (4/φ) a m`. -/
def DiffEq (φ : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ m, a m - a (m + 1) = a (m + 1) - a (m + 2) + 4 / φ * a (m + 1)

/-- The geometric limit partition `a m = θ̄ yᵐ` solves the difference equation. -/
lemma geometric_diffEq {φ : ℝ} (hφ : 0 < φ) (θbar : ℝ) :
    DiffEq φ (fun m => θbar * yRatio φ ^ m) := by
  intro m
  have hq := yRatio_quadratic hφ
  simp only [pow_succ]
  linear_combination (θbar * yRatio φ ^ m) * hq

/-- The limit partition is unique. A sequence of boundaries that starts at `θ̄`, solves the
difference equation, and accumulates at `0` is the geometric one, `a m = θ̄ yᵐ`. -/
lemma limitPartition_unique {φ : ℝ} (hφ : 0 < φ) {θbar : ℝ} {a : ℕ → ℝ} (h0 : a 0 = θbar)
    (hd : DiffEq φ a) (hlim : Tendsto a atTop (𝓝 0)) : ∀ m, a m = θbar * yRatio φ ^ m := by
  set y := yRatio φ
  have hy0 := yRatio_pos hφ
  have hy1 := yRatio_lt_one hφ
  have hq := yRatio_quadratic hφ
  set x := y⁻¹
  have hxy : x * y = 1 := inv_mul_cancel₀ hy0.ne'
  have hxne : x - y ≠ 0 := by
    have : 1 < x := by rw [one_lt_inv₀ hy0]; exact hy1
    linarith
  -- Coefficients of the general solution `a m = P xᵐ + Q yᵐ`.
  set P := (a 1 - a 0 * y) / (x - y)
  set Q := (a 0 * x - a 1) / (x - y)
  have hsum : x + y = 2 + 4 / φ := by
    have h : (x + y) * y = (2 + 4 / φ) * y := by linear_combination hxy + hq
    exact mul_right_cancel₀ hy0.ne' h
  have hgen : ∀ m, a m = P * x ^ m + Q * y ^ m ∧ a (m + 1) = P * x ^ (m + 1) + Q * y ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero, mul_one, zero_add, pow_one]
      constructor
      · simp only [P, Q]; field_simp; ring
      · simp only [P, Q]; field_simp; ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hrec : a (n + 1 + 1) = (2 + 4 / φ) * a (n + 1) - a n := by
        linear_combination hd n
      rw [hrec, ih.1, ih.2, ← hsum]
      linear_combination (P * x ^ n + Q * y ^ n) * hxy
  -- `P = (a m - Q yᵐ) yᵐ → 0`, so `P = 0`.
  have hP : P = 0 := by
    have hyn : Tendsto (fun m : ℕ => y ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hy0.le hy1
    have hconst : ∀ m : ℕ, P = (a m - Q * y ^ m) * y ^ m := by
      intro m
      rw [(hgen m).1]
      have : x ^ m * y ^ m = 1 := by rw [← mul_pow, hxy, one_pow]
      linear_combination -P * this
    have hlim2 : Tendsto (fun m : ℕ => (a m - Q * y ^ m) * y ^ m) atTop (𝓝 ((0 - Q * 0) * 0)) :=
      (hlim.sub (hyn.const_mul Q)).mul hyn
    simp only [mul_zero, sub_zero] at hlim2
    have : Tendsto (fun _ : ℕ => P) atTop (𝓝 0) := by
      refine hlim2.congr ?_; intro m; exact (hconst m).symm
    exact tendsto_nhds_unique tendsto_const_nhds this
  intro m
  have hQ : Q = θbar := by
    have := (hgen 0).1; simp only [pow_zero, mul_one, hP, zero_add] at this
    rw [← h0, this]
  rw [(hgen m).1, hP, hQ]; ring

/-! ### Step 4: the information loss of the limit partition -/

/-- The information loss `𝔼[(θ - 𝔼(θ | m))²]` of a partition of `[-θ̄, θ̄]` with positive boundaries
`θ̄ = a 0 > a 1 > ⋯ → 0` and negative boundaries `-θ̄ = -a' 0 < -a' 1 < ⋯ → 0`, when `θ` is uniform
on `[-θ̄, θ̄]`: the sum over cells of `P(cell) · Var(θ | cell)`. -/
noncomputable def infoLoss (θbar : ℝ) (a a' : ℕ → ℝ) : ℝ :=
  1 / (2 * θbar) *
    ((∑' m, cellLoss (a (m + 1)) (a m)) + ∑' m, cellLoss (-a' m) (-a' (m + 1)))

lemma tsum_cellLoss_geometric {φ : ℝ} (hφ : 0 < φ) {θbar : ℝ} (hθ : 0 < θbar) :
    ∑' m, cellLoss (θbar * yRatio φ ^ (m + 1)) (θbar * yRatio φ ^ m) =
      θbar ^ 3 * (1 - yRatio φ) ^ 3 / 12 / (1 - yRatio φ ^ 3) := by
  set y := yRatio φ
  have hy0 := yRatio_pos hφ
  have hy1 := yRatio_lt_one hφ
  have hterm : ∀ m : ℕ, cellLoss (θbar * y ^ (m + 1)) (θbar * y ^ m) =
      θbar ^ 3 * (1 - y) ^ 3 / 12 * (y ^ 3) ^ m := by
    intro m
    have hlt : θbar * y ^ (m + 1) < θbar * y ^ m :=
      mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ hy0 hy1 (Nat.lt_succ_self m)) hθ
    rw [cellLoss_eq hlt.ne, ← pow_mul]; ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by
    have : y ^ 3 < 1 ^ 3 := by gcongr
    simpa using this)]
  ring

/-- The information loss of the limit partition is `σ² / (3φ + 4)` with `σ² = θ̄²/3`. -/
lemma infoLoss_geometric {φ : ℝ} (hφ : 0 < φ) {θbar : ℝ} (hθ : 0 < θbar) :
    infoLoss θbar (fun m => θbar * yRatio φ ^ m) (fun m => θbar * yRatio φ ^ m) =
      uniformVar θbar * V φ := by
  unfold infoLoss
  have hneg : ∀ m : ℕ, cellLoss (-(θbar * yRatio φ ^ m)) (-(θbar * yRatio φ ^ (m + 1))) =
      cellLoss (θbar * yRatio φ ^ (m + 1)) (θbar * yRatio φ ^ m) := by
    intro m
    have hy0 := yRatio_pos hφ
    have hy1 := yRatio_lt_one hφ
    have hlt : θbar * yRatio φ ^ (m + 1) < θbar * yRatio φ ^ m := by
      rw [pow_succ]; have : 0 < θbar * yRatio φ ^ m := by positivity
      nlinarith
    rw [cellLoss_eq (neg_lt_neg hlt).ne, cellLoss_eq hlt.ne]; ring
  simp only
  simp_rw [hneg]
  have hy0 := yRatio_pos hφ
  have hy1 := yRatio_lt_one hφ
  have hq := yRatio_quadratic hφ
  rw [tsum_cellLoss_geometric hφ hθ, uniformVar_eq hθ]
  generalize yRatio φ = y at hy0 hy1 hq ⊢
  have hq' : (1 - y) ^ 2 * φ = 4 * y := by
    have h := hq; field_simp at h; linear_combination h
  have hne : (1 : ℝ) - y ≠ 0 := by linarith
  have hne2 : 0 < (1 : ℝ) + y + y ^ 2 := by positivity
  have hV : V φ = (1 - y) ^ 2 / (4 * (1 + y + y ^ 2)) := by
    unfold V
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-3) * hq'
  rw [hV, show (1 : ℝ) - y ^ 3 = (1 - y) * (1 + y + y ^ 2) by ring]
  field_simp
  ring

/-! ### Lemma 2 -/

/-- The sequential case of Lemma 2, with the hypotheses spelled out. Let `θ₂` be uniform on
`[-θ̄, θ̄]` and let the leader's state have any distribution `ν₁` with mean zero and finite
variance. Take a partition of `[-θ̄, θ̄]` whose positive boundaries `θ̄ = a 0 > a 1 > ⋯` and negative
boundaries `-θ̄ = -a' 0 < -a' 1 < ⋯` accumulate at `0`, and suppose every interior boundary type is
indifferent between its two adjacent cells (the truth-telling condition). Then the information
loss is `c₂ = σ₂² / (3 φ_{2,sequential} + 4)`. -/
lemma infoLoss_seq {ν₁ : Measure ℝ} [IsProbabilityMeasure ν₁]
    (h1 : Integrable (fun x : ℝ => x) ν₁) (h2 : Integrable (fun x : ℝ => x ^ 2) ν₁)
    (hmean : ∫ x, x ∂ν₁ = 0) {r₁ r₂ : ℝ} (hr₁ : Unit01 r₁) (hr₂ : Unit01 r₂)
    {θbar : ℝ} (hθ : 0 < θbar) {a a' : ℕ → ℝ} (ha0 : a 0 = θbar) (ha'0 : a' 0 = θbar)
    (ha : StrictAnti a) (ha' : StrictAnti a')
    (hlim : Tendsto a atTop (𝓝 0)) (hlim' : Tendsto a' atTop (𝓝 0))
    (hind : ∀ m, followerMsgLoss r₁ r₂ ν₁ (a (m + 1)) (cellMean (a (m + 2)) (a (m + 1))) =
      followerMsgLoss r₁ r₂ ν₁ (a (m + 1)) (cellMean (a (m + 1)) (a m)))
    (hind' : ∀ m, followerMsgLoss r₁ r₂ ν₁ (-a' (m + 1)) (cellMean (-a' m) (-a' (m + 1))) =
      followerMsgLoss r₁ r₂ ν₁ (-a' (m + 1)) (cellMean (-a' (m + 1)) (-a' (m + 2)))) :
    infoLoss θbar a a' = uniformVar θbar * V (φSeq r₁ r₂) := by
  have hφ := φSeq_pos hr₁ hr₂
  have hda : DiffEq (φSeq r₁ r₂) a := by
    intro m
    have h := (follower_indiff_iff h1 h2 hmean hr₁ hr₂
      (ha (Nat.lt_succ_self (m + 1))).ne (ha (Nat.lt_succ_self m)).ne
      (ha (by omega : m < m + 2)).ne).mp (hind m)
    linear_combination h
  have hda' : DiffEq (φSeq r₁ r₂) a' := by
    intro m
    have h := (follower_indiff_iff h1 h2 hmean hr₁ hr₂
      (neg_lt_neg (ha' (Nat.lt_succ_self m))).ne
      (neg_lt_neg (ha' (Nat.lt_succ_self (m + 1)))).ne
      (neg_lt_neg (ha' (by omega : m < m + 2))).ne).mp (hind' m)
    linear_combination -h
  have hA := limitPartition_unique hφ ha0 hda hlim
  have hA' := limitPartition_unique hφ ha'0 hda' hlim'
  have e1 : a = fun m => θbar * yRatio (φSeq r₁ r₂) ^ m := funext hA
  have e2 : a' = fun m => θbar * yRatio (φSeq r₁ r₂) ^ m := funext hA'
  rw [e1, e2]
  exact infoLoss_geometric hφ hθ

/-- The concurrent case of Lemma 2, with the hypotheses spelled out. Let `θᵢ` be uniform on `[-θ̄, θ̄]` and let `ρ` be the
joint law of the other unit's state and the posterior mean its message induces, `(θⱼ, μⱼ)`, with
square-integrable coordinates and mean zero. For a partition that accumulates at `0` and makes
every interior boundary type of unit `i` indifferent between its two adjacent cells, the
information loss is `cᵢ = σᵢ² / (3 φ_{i,concurrent} + 4)`. -/
lemma infoLoss_conc {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]
    (hx : MemLp (fun p : ℝ × ℝ => p.1) 2 ρ) (hy : MemLp (fun p : ℝ × ℝ => p.2) 2 ρ)
    (hm1 : ∫ p, p.1 ∂ρ = 0) (hm2 : ∫ p, p.2 ∂ρ = 0) {ri rj : ℝ} (hi : Unit01 ri) (hj : Unit01 rj)
    {θbar : ℝ} (hθ : 0 < θbar) {a a' : ℕ → ℝ} (ha0 : a 0 = θbar) (ha'0 : a' 0 = θbar)
    (ha : StrictAnti a) (ha' : StrictAnti a')
    (hlim : Tendsto a atTop (𝓝 0)) (hlim' : Tendsto a' atTop (𝓝 0))
    (hind : ∀ m, concMsgLoss ri rj ρ (a (m + 1)) (cellMean (a (m + 2)) (a (m + 1))) =
      concMsgLoss ri rj ρ (a (m + 1)) (cellMean (a (m + 1)) (a m)))
    (hind' : ∀ m, concMsgLoss ri rj ρ (-a' (m + 1)) (cellMean (-a' m) (-a' (m + 1))) =
      concMsgLoss ri rj ρ (-a' (m + 1)) (cellMean (-a' (m + 1)) (-a' (m + 2)))) :
    infoLoss θbar a a' = uniformVar θbar * V (φConc ri rj) := by
  have hφ := φConc_pos hi hj
  have hda : DiffEq (φConc ri rj) a := by
    intro m
    have h := (conc_indiff_iff hx hy hm1 hm2 hi hj
      (ha (Nat.lt_succ_self (m + 1))).ne (ha (Nat.lt_succ_self m)).ne
      (ha (by omega : m < m + 2)).ne).mp (hind m)
    linear_combination h
  have hda' : DiffEq (φConc ri rj) a' := by
    intro m
    have h := (conc_indiff_iff hx hy hm1 hm2 hi hj
      (neg_lt_neg (ha' (Nat.lt_succ_self m))).ne
      (neg_lt_neg (ha' (Nat.lt_succ_self (m + 1)))).ne
      (neg_lt_neg (ha' (by omega : m < m + 2))).ne).mp (hind' m)
    linear_combination -h
  have hA := limitPartition_unique hφ ha0 hda hlim
  have hA' := limitPartition_unique hφ ha'0 hda' hlim'
  have e1 : a = fun m => θbar * yRatio (φConc ri rj) ^ m := funext hA
  have e2 : a' = fun m => θbar * yRatio (φConc ri rj) ^ m := funext hA'
  rw [e1, e2]
  exact infoLoss_geometric hφ hθ

/-- The limit partition exists. The geometric partition is strictly decreasing, starts at
`θ̄`, accumulates at `0`, and solves the difference equation, so the hypotheses of Lemma 2 can be
met. -/
lemma limitPartition_exists {φ : ℝ} (hφ : 0 < φ) {θbar : ℝ} (hθ : 0 < θbar) :
    geomPartition θbar φ 0 = θbar ∧ StrictAnti (geomPartition θbar φ) ∧
      Tendsto (geomPartition θbar φ) atTop (𝓝 0) ∧ DiffEq φ (geomPartition θbar φ) := by
  have hy0 := yRatio_pos hφ
  have hy1 := yRatio_lt_one hφ
  refine ⟨by simp [geomPartition], ?_, ?_, geometric_diffEq hφ θbar⟩
  · intro m n hmn
    exact mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ hy0 hy1 hmn) hθ
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hy0.le hy1).const_mul θbar
    rw [mul_zero] at this
    exact this

/-! ### Truthful limit partitions and Lemma 2 -/

/-- A partition of `[-θ̄, θ̄]` that is the limit of the truthful partitions: positive boundaries
`θ̄ = a 0 > a 1 > ⋯` and negative boundaries `-θ̄ = -a' 0 < -a' 1 < ⋯`, both accumulating at `0`. Every
interior boundary type `k` is indifferent between its two adjacent cells, where `U k μ` is the
sender's expected loss from inducing the posterior mean `μ`. -/
def TruthfulLimitPartition (U : ℝ → ℝ → ℝ) (θbar : ℝ) (a a' : ℕ → ℝ) : Prop :=
  a 0 = θbar ∧ a' 0 = θbar ∧ StrictAnti a ∧ StrictAnti a' ∧
    Tendsto a atTop (𝓝 0) ∧ Tendsto a' atTop (𝓝 0) ∧
    (∀ m, U (a (m + 1)) (cellMean (a (m + 2)) (a (m + 1))) =
      U (a (m + 1)) (cellMean (a (m + 1)) (a m))) ∧
    (∀ m, U (-a' (m + 1)) (cellMean (-a' m) (-a' (m + 1))) =
      U (-a' (m + 1)) (cellMean (-a' (m + 1)) (-a' (m + 2))))

/-- A geometric partition with ratio `yRatio φ` is a truthful limit partition for any sender whose
indifference condition is the difference equation with parameter `φ`. -/
lemma geom_truthful {U : ℝ → ℝ → ℝ} {φ θbar : ℝ} (hφ : 0 < φ) (hθ : 0 < θbar)
    (hU : ∀ kl k ku : ℝ, kl ≠ k → k ≠ ku → kl ≠ ku →
      (U k (cellMean kl k) = U k (cellMean k ku) ↔ ku - k = k - kl + 4 / φ * k)) :
    TruthfulLimitPartition U θbar (geomPartition θbar φ) (geomPartition θbar φ) := by
  obtain ⟨h0, hanti, hlim, hdiff⟩ := limitPartition_exists hφ hθ
  refine ⟨h0, h0, hanti, hanti, hlim, hlim, fun m => ?_, fun m => ?_⟩
  · rw [hU _ _ _ (hanti (Nat.lt_succ_self (m + 1))).ne (hanti (Nat.lt_succ_self m)).ne
      (hanti (by omega : m < m + 2)).ne]
    linear_combination hdiff m
  · rw [hU _ _ _ (neg_lt_neg (hanti (Nat.lt_succ_self m))).ne
      (neg_lt_neg (hanti (Nat.lt_succ_self (m + 1)))).ne
      (neg_lt_neg (hanti (by omega : m < m + 2))).ne]
    linear_combination -hdiff m

/-- The leader's decision is strictly increasing in its state, so the follower, who knows `μ₂`,
recovers `θ₁` from `d₁`. -/
lemma leader_decision_injective {r₁ r₂ : ℝ} (hr₁ : Unit01 r₁) (hr₂ : Unit01 r₂) (μ₂ : ℝ) :
    Function.Injective fun θ₁ : ℝ => (1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * μ₂ := by
  intro x y h
  have : 1 - γ r₁ r₂ ≠ 0 := by linarith [γ_lt_one hr₁ hr₂]
  simp only at h
  have := mul_left_cancel₀ this (by linarith : (1 - γ r₁ r₂) * x = (1 - γ r₁ r₂) * y)
  exact this

/-- `V(φ) → 0` as `φ → ∞`. -/
lemma V_tendsto_zero : Tendsto V atTop (𝓝 0) := by
  unfold V
  have : Tendsto (fun φ : ℝ => 4 + 3 * φ) atTop atTop :=
    tendsto_atTop_add_const_left _ 4 (tendsto_id.const_mul_atTop (by norm_num))
  refine Tendsto.congr (fun x => ?_) this.inv_tendsto_atTop
  simp [one_div]

/-- **Lemma 2.** Equilibrium information loss with `θ` uniform on `[-θ̄, θ̄]`, so `σ² = θ̄²/3`
(`uniformVar`).

1. Sequential decision-making, unit 1 leading. For any truthful limit partition of the
   follower's state, `c₂ = σ₂² · 1/(3φ + 4)` with `φ_{2,sequential} = β₁/(1 - r₁)`. The follower's
   expected loss averages over the leader's state, which may have any mean-zero distribution `ν₁`
   with finite variance.
2. Concurrent decision-making. For any truthful limit partition of unit `i`'s state,
   `cᵢ = σᵢ² · 1/(3φ + 4)` with `φ_{i,concurrent} = rⱼ(1 - rᵢ)/(1 - rⱼ)`. Unit `i`'s expected loss
   averages over the joint law `ρ` of `(θⱼ, μⱼ)`, which may be any law with mean-zero,
   square-integrable coordinates.
3. `φ_{1,sequential} = ∞`. The leader's decision reveals its state, so its information loss is
   `0`, the limit of `σ² V(φ)` as `φ → ∞`. -/
theorem lemma2 :
    (∀ (ν₁ : Measure ℝ) [IsProbabilityMeasure ν₁], Integrable (fun x : ℝ => x) ν₁ →
      Integrable (fun x : ℝ => x ^ 2) ν₁ → ∫ x, x ∂ν₁ = 0 →
      ∀ r₁ r₂ : ℝ, Unit01 r₁ → Unit01 r₂ → ∀ θbar : ℝ, 0 < θbar → ∀ a a' : ℕ → ℝ,
      TruthfulLimitPartition (followerMsgLoss r₁ r₂ ν₁) θbar a a' →
      infoLoss θbar a a' = uniformVar θbar * (1 / (3 * (β r₁ r₂ / (1 - r₁)) + 4))) ∧
    (∀ (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ], MemLp (fun p : ℝ × ℝ => p.1) 2 ρ →
      MemLp (fun p : ℝ × ℝ => p.2) 2 ρ → ∫ p, p.1 ∂ρ = 0 → ∫ p, p.2 ∂ρ = 0 →
      ∀ ri rj : ℝ, Unit01 ri → Unit01 rj → ∀ θbar : ℝ, 0 < θbar → ∀ a a' : ℕ → ℝ,
      TruthfulLimitPartition (concMsgLoss ri rj ρ) θbar a a' →
      infoLoss θbar a a' = uniformVar θbar * (1 / (3 * (rj * (1 - ri) / (1 - rj)) + 4))) ∧
    (∀ r₁ r₂ μ₂ : ℝ, Unit01 r₁ → Unit01 r₂ →
      Function.Injective fun θ₁ : ℝ => (1 - γ r₁ r₂) * θ₁ + γ r₁ r₂ * μ₂) ∧
    Tendsto (fun φ : ℝ => 1 / (3 * φ + 4)) atTop (𝓝 0) := by
  have hV : ∀ φ : ℝ, 1 / (3 * φ + 4) = V φ := fun φ => by unfold V; ring_nf
  refine ⟨?_, ?_, fun r₁ r₂ μ₂ h₁ h₂ => leader_decision_injective h₁ h₂ μ₂, ?_⟩
  · intro ν₁ _ h1 h2 hm r₁ r₂ h₁ h₂ θbar hθ a a' ⟨ha0, ha'0, ha, ha', hl, hl', hi, hi'⟩
    rw [hV]; exact infoLoss_seq h1 h2 hm h₁ h₂ hθ ha0 ha'0 ha ha' hl hl' hi hi'
  · intro ρ _ hx hy hm1 hm2 ri rj hi hj θbar hθ a a' ⟨ha0, ha'0, ha, ha', hl, hl', hin, hin'⟩
    rw [hV]; exact infoLoss_conc hx hy hm1 hm2 hi hj hθ ha0 ha'0 ha ha' hl hl' hin hin'
  · simpa only [hV] using V_tendsto_zero

end WhoVsWhen
