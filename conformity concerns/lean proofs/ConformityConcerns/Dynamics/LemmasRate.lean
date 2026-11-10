import ConformityConcerns.Dynamics.Lemmas
import ConformityConcerns.Dynamics.Accounting
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Helpers for the speed-of-learning results (Propositions A1 and A2)
-/

namespace CC

open Matrix Filter Topology Set

/-- Lemma A1's bound in the form used below. -/
lemma lemmaA1_bound (κ γ : ℕ → ℝ) (S₁ : M2) (hS : S₁.PosDef) (t : ℕ) :
    1 / ((S₁⁻¹).trace + revCount κ S₁ γ t) ≤ min (SigmaC κ S₁ γ t 0 0) (SigmaC κ S₁ γ t 1 1) :=
  (lemmaA1 κ γ S₁ hS t).2.2.2.2.2

lemma trace_inv_pos {S₁ : M2} (hS : S₁.PosDef) : 0 < (S₁⁻¹).trace := by
  obtain ⟨-, h0, hb⟩ := (pd_iff _).1 hS.inv
  rw [trace_fin_two]; nlinarith [sq_nonneg ((S₁⁻¹) 0 1)]

/-- From `c (L + N_t) ≤ ε t` and `min ≥ 1/(L + N_t)` to `c ≤ ε t min`. -/
lemma final_bound {L ε c : ℝ} {N : ℕ → ℕ} {m : ℕ → ℝ} (hL : 0 < L) (hε : 0 ≤ ε)
    (hm : ∀ t, 1 / (L + N t) ≤ m t) (hkey : ∀ᶠ t : ℕ in atTop, c * (L + N t) ≤ ε * t) :
    ∀ᶠ t : ℕ in atTop, c ≤ ε * t * m t := by
  filter_upwards [hkey] with t ht
  have hpos : 0 < L + N t := by positivity
  calc c ≤ ε * t / (L + N t) := by rw [le_div_iff₀ hpos]; linarith
    _ = ε * t * (1 / (L + N t)) := by ring
    _ ≤ ε * t * m t := mul_le_mul_of_nonneg_left (hm t) (by positivity)

/-- If `N_t ≤ M_t` eventually and `M_t / t → δ ≤ ε` with `ε > 0`, then for `c < 1`,
eventually `c (L + N_t) ≤ ε t`. -/
lemma key_of_le {L ε δ c : ℝ} {N : ℕ → ℕ} {M : ℕ → ℝ} (hε : 0 < ε) (hδ : δ ≤ ε) (hc : c < 1)
    (hNM : ∀ᶠ t : ℕ in atTop, (N t : ℝ) ≤ M t) (hM : Tendsto (fun t : ℕ => M t / t) atTop (𝓝 δ))
    (hL : 0 ≤ L) : ∀ᶠ t : ℕ in atTop, c * (L + N t) ≤ ε * t := by
  rcases le_or_gt c 0 with hc0 | hc0
  · exact Eventually.of_forall fun t => le_trans (mul_nonpos_of_nonpos_of_nonneg hc0
      (by positivity)) (by positivity)
  have hlim : Tendsto (fun t : ℕ => (L + M t) / t) atTop (𝓝 δ) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat L).add hM
    rw [zero_add] at h
    exact h.congr fun t => by rw [add_div]
  have hlt : δ < ε / c := by
    rw [lt_div_iff₀ hc0]; nlinarith
  filter_upwards [hlim.eventually (gt_mem_nhds hlt), eventually_gt_atTop 0, hNM] with t ht ht0 hN
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  rw [div_lt_div_iff₀ ht0' hc0] at ht
  nlinarith

/-- Uniform closeness of the sensitivity to one when `σ²_θ` and the covariance are small. -/
lemma sens_close {S : M2} (hP : PSDE S) {g γ : ℝ} (hg : 0 < g) (hγ0 : 0 ≤ γ) (hγg : γ ≤ g)
    (hb : |S 0 1| ≤ 1 / (4 * g)) : |1 - sensE S γ| ≤ 2 * g * (|S 0 1| + g * S 0 0) := by
  have h1 := sens_near_one hP hγ0
  have e1 : 2 * γ * |S 0 1| ≤ 1 / 2 := by
    have : γ * |S 0 1| ≤ g * (1 / (4 * g)) :=
      mul_le_mul hγg hb (abs_nonneg _) hg.le
    have e : g * (1 / (4 * g)) = 1 / 4 := by field_simp
    linarith
  have e2 : γ * (|S 0 1| + γ * S 0 0) ≤ g * (|S 0 1| + g * S 0 0) := by
    have := hP.1
    apply mul_le_mul hγg _ (by positivity) hg.le
    have : γ * S 0 0 ≤ g * S 0 0 := mul_le_mul_of_nonneg_right hγg hP.1
    linarith
  have hab := abs_nonneg (1 - sensE S γ)
  nlinarith

/-- `s² ≤ r` implies `(1 - r)/2 ≤ 1 - s`. -/
lemma one_sub_ge_of_sq_le {s r : ℝ} (h : s ^ 2 ≤ r) : (1 - r) / 2 ≤ 1 - s := by
  nlinarith [sq_nonneg (1 - s)]

/-- Entry limits from a matrix limit. -/
lemma tendsto_entry {f : ℕ → M2} {L : M2} (h : Tendsto f atTop (𝓝 L)) (i j : Fin 2) :
    Tendsto (fun t => f t i j) atTop (𝓝 (L i j)) :=
  ((continuous_id.matrix_elem i j).tendsto L).comp h

/-- Revealing dates and the criterion with a lower bound `κ₀ > 0` on the concern. -/
lemma sensE_sq_le {κ₀ κt : ℝ} {S : M2} {γ : ℝ} (hκ0 : 0 < κ₀) (hκ : κ₀ ≤ κt)
    (hs : S 1 0 = S 0 1) (hP : PSDE S) (h : revCrit κt S γ) :
    sensE S γ ^ 2 ≤ κck / κ₀ := by
  have h1 : κt * sens S γ ^ 2 ≤ κck := h
  rw [sens_eq_sensE hs (dE_ne hP)] at h1
  rw [le_div_iff₀ hκ0]
  nlinarith [sq_nonneg (sensE S γ)]

end CC
