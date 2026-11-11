import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# The model

Two units `i ∈ {1, 2}` have local conditions `θᵢ` and coordination weights `rᵢ ∈ (0, 1)`.
Unit `i`'s loss is equation (1) of the paper,

  `ℒᵢ(dᵢ, d₋ᵢ, θᵢ) = (1 - rᵢ)(θᵢ - dᵢ)² + rᵢ(d₋ᵢ - dᵢ)²`,

and the headquarters' loss is the sum of the two units' losses.

Most quantities depend on the pair of coordination weights in an asymmetric way. They are written
as functions of `(rᵢ, rⱼ)`, so the quantity for unit 2 is obtained by swapping the arguments.
-/

namespace WhoVsWhen

/-- Equation (1): the loss of a unit with coordination weight `r`, own decision `d`, other
unit's decision `d'`, and local condition `θ`. -/
def L (r d d' θ : ℝ) : ℝ := (1 - r) * (θ - d) ^ 2 + r * (d' - d) ^ 2

/-- `βᵢ = rᵢ (1 - rⱼ)²`. -/
def β (ri rj : ℝ) : ℝ := ri * (1 - rj) ^ 2

/-- `γᵢ = βᵢ / ((1 - rᵢ) + βᵢ)`, the leader's weight on its expectation of the follower's state
(Lemma 1). -/
noncomputable def γ (ri rj : ℝ) : ℝ := β ri rj / ((1 - ri) + β ri rj)

/-- `V(φ) = 1 / (4 + 3φ)` (Lemma 4). -/
noncomputable def V (φ : ℝ) : ℝ := 1 / (4 + 3 * φ)

/-- Lemma 2: `φ` for the follower's state under sequential decision-making, when the leader has
weight `rL` and the follower weight `rF`: `φ = β_L / (1 - r_L) = r_L (1 - r_F)² / (1 - r_L)`. -/
noncomputable def φSeq (rL rF : ℝ) : ℝ := β rL rF / (1 - rL)

/-- Lemma 2: `φ` for the state of unit `i` under concurrent decision-making,
`φ_{i,concurrent} = rⱼ (1 - rᵢ) / (1 - rⱼ) = βⱼ / ((1 - rᵢ)(1 - rⱼ))`. -/
noncomputable def φConc (ri rj : ℝ) : ℝ := rj * (1 - ri) / (1 - rj)

/-- The common denominator `1 - r₁ r₂`. -/
def Dn (ri rj : ℝ) : ℝ := 1 - ri * rj

/-- Concurrent equilibrium: coefficient of unit `i`'s decision on the posterior mean of its own
state, `rᵢ rⱼ (1 - rᵢ) / (1 - rᵢ rⱼ)`. -/
noncomputable def eOwn (ri rj : ℝ) : ℝ := ri * rj * (1 - ri) / Dn ri rj

/-- Concurrent equilibrium: coefficient of unit `i`'s decision on the posterior mean of the other
unit's state, `rᵢ (1 - rⱼ) / (1 - rᵢ rⱼ)`. -/
noncomputable def bOth (ri rj : ℝ) : ℝ := ri * (1 - rj) / Dn ri rj

/-- The coefficient `(1 - r₁)(1 - r₂) / (1 - r₁ r₂)` of the concurrent decision gap. -/
noncomputable def Kc (ri rj : ℝ) : ℝ := (1 - ri) * (1 - rj) / Dn ri rj

/-- Shorthand for the standing assumption `0 < r < 1`. -/
def Unit01 (r : ℝ) : Prop := 0 < r ∧ r < 1

section Positivity

variable {ri rj : ℝ}

lemma Dn_pos (hi : Unit01 ri) (hj : Unit01 rj) : 0 < Dn ri rj := by
  unfold Dn; nlinarith [hi.1, hi.2, hj.1, hj.2]

lemma β_pos (hi : Unit01 ri) (hj : Unit01 rj) : 0 < β ri rj := by
  unfold β; have := hj.2; have := hi.1; positivity

lemma den_γ_pos (hi : Unit01 ri) (hj : Unit01 rj) : 0 < (1 - ri) + β ri rj := by
  have := β_pos hi hj; linarith [hi.2]

lemma γ_pos (hi : Unit01 ri) (hj : Unit01 rj) : 0 < γ ri rj := by
  unfold γ; exact div_pos (β_pos hi hj) (den_γ_pos hi hj)

lemma γ_lt_one (hi : Unit01 ri) (hj : Unit01 rj) : γ ri rj < 1 := by
  unfold γ; rw [div_lt_one (den_γ_pos hi hj)]; linarith [hi.2]

lemma one_sub_γ (hi : Unit01 ri) (hj : Unit01 rj) :
    1 - γ ri rj = (1 - ri) / ((1 - ri) + β ri rj) := by
  have := den_γ_pos hi hj
  unfold γ; field_simp; ring

lemma φSeq_pos (hL : Unit01 ri) (hF : Unit01 rj) : 0 < φSeq ri rj := by
  unfold φSeq; exact div_pos (β_pos hL hF) (by linarith [hL.2])

lemma φConc_pos (hi : Unit01 ri) (hj : Unit01 rj) : 0 < φConc ri rj := by
  unfold φConc; have := hi.2; have := hj.2; have := hj.1
  exact div_pos (mul_pos hj.1 (by linarith)) (by linarith)

/-- `φ = γ / (1 - γ)`: the sequential `φ` in terms of the leader's weight `γ` (proof of
Lemma 2). -/
lemma φSeq_eq_γ (hL : Unit01 ri) (hF : Unit01 rj) :
    φSeq ri rj = γ ri rj / (1 - γ ri rj) := by
  have h1 := den_γ_pos hL hF
  have h2 : (1 - ri) ≠ 0 := by linarith [hL.2]
  rw [one_sub_γ hL hF]; unfold φSeq γ; field_simp

lemma V_pos {φ : ℝ} (hφ : 0 ≤ φ) : 0 < V φ := by unfold V; positivity

lemma V_lt_quarter {φ : ℝ} (hφ : 0 < φ) : V φ < 1 / 4 := by
  unfold V; apply one_div_lt_one_div_of_lt (by norm_num); linarith

lemma V_strictAnti {φ φ' : ℝ} (hφ : 0 ≤ φ) (h : φ < φ') : V φ' < V φ := by
  unfold V; apply one_div_lt_one_div_of_lt (by linarith); linarith

/-- The concurrent equilibrium coefficients solve the fixed-point equations
`eᵢ = rᵢ bⱼ` and `bᵢ = rᵢ (1 - rⱼ + eⱼ)` (proof of Lemma 1). -/
lemma eOwn_fixed (hi : Unit01 ri) (hj : Unit01 rj) : eOwn ri rj = ri * bOth rj ri := by
  have := Dn_pos hi hj
  have : Dn rj ri = Dn ri rj := by unfold Dn; ring
  unfold eOwn bOth; rw [this]; field_simp

lemma bOth_fixed (hi : Unit01 ri) (hj : Unit01 rj) :
    bOth ri rj = ri * (1 - rj + eOwn rj ri) := by
  have := Dn_pos hi hj
  have : Dn rj ri = Dn ri rj := by unfold Dn; ring
  unfold eOwn bOth; rw [this]; field_simp; unfold Dn; ring

end Positivity

end WhoVsWhen
