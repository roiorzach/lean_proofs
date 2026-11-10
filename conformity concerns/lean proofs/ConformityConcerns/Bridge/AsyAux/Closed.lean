import ConformityConcerns.Bridge.AsyAux.Payoff
import ConformityConcerns.Bridge.Corollaries

/-!
# The second moments in closed form when `θ` is known (Corollary A2) and when `μ` is known and
`γ_t = 1` (Corollary A3)
-/

namespace CC.Bridge

open MeasureTheory ProbabilityTheory Filter Topology Matrix

set_option warn.classDefReducibility false

lemma rlam_def (κ : ℝ) (S₁ : M2) (γ : ℕ → ℝ) (t : ℕ) :
    rlam κ S₁ γ t = haveI := Classical.propDecidable (revP κ S₁ γ t)
      if revP κ S₁ γ t then lamF κ (SigP κ S₁ γ t) (γ t) else 0 := rfl

lemma revP_def (κ : ℝ) (S₁ : M2) (γ : ℕ → ℝ) (t : ℕ) :
    revP κ S₁ γ t = (κ * sens (SigP κ S₁ γ t) (γ t) ^ 2 ≤ κck) := rfl

lemma qf_diag (a b a0 a1 b0 b1 : ℝ) :
    qf !![a, 0; 0, b] a0 a1 b0 b1 = a * a0 ^ 2 + b * a1 ^ 2 + b0 ^ 2 + b1 ^ 2 := by
  simp [qf]; ring

lemma loadA_diag0 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (g : ℝ) :
    loadA !![a, 0; 0, b] g 0 = g * (a / (1 + a)) := by
  simp [loadA, gainK_diag a b ha hb]

lemma loadA_diag1 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (g : ℝ) :
    loadA !![a, 0; 0, b] g 1 = 1 := by
  simp [loadA, gainK_diag a b ha hb]

/-! ### Corollary A2: `Σ₁ = diag(0, σ²_μ)` -/

section A2

variable (σ : ℝ) (hσ : 0 < σ) (κ : ℝ) (hκ : 0 < κ)

/-- `σ²_{μ,t}` when `θ` is known. -/
noncomputable def yA2 (t : ℕ) : ℝ := if κ ≤ κck then σ / (1 + t * σ) else σ

include hσ in
lemma yA2_nonneg (t : ℕ) : 0 ≤ yA2 σ κ t := by
  unfold yA2; split_ifs <;> positivity

include hσ hκ in
lemma sigP_A2 (γ : ℕ → ℝ) (t : ℕ) :
    SigP κ !![0, 0; 0, σ] γ t = !![0, 0; 0, yA2 σ κ t] := by
  have hS : (!![0, 0; 0, σ] : M2).PosSemidef := psd_diag 0 σ le_rfl hσ.le
  show SigmaC (fun _ => κ) !![0, 0; 0, σ] γ t = _
  rw [← SigmaSeq_eq_SigmaC (fun _ => κ) (fun _ => hκ) _ hS γ]
  exact CorA2.seq_eq σ hσ κ hκ γ t

include hσ hκ in
lemma rlam_A2 (γ : ℕ → ℝ) (t : ℕ) :
    rlam κ !![0, 0; 0, σ] γ t = if κ ≤ κck then (1 + √(1 - 4 * κ)) / 2 else 0 := by
  have hy := yA2_nonneg σ hσ κ t
  have hsens : sens (SigP κ !![0, 0; 0, σ] γ t) (γ t) = 1 := by
    rw [sigP_A2 σ hσ κ hκ γ t, CorA2.sens_eq_one _ _ hy]
  have hrev : revP κ !![0, 0; 0, σ] γ t ↔ κ ≤ κck := by
    rw [revP_def, hsens, one_pow, mul_one]
  rw [rlam_def]
  by_cases h : κ ≤ κck
  · rw [ite_eq_left (hrev.2 h), ite_eq_left h]
    simp only [lamF, hsens, one_pow, mul_one]
  · rw [ite_eq_right (fun h' => h (hrev.1 h')), ite_eq_right h]

include hσ hκ in
lemma adaptQ_A2 (γ : ℕ → ℝ) (t : ℕ) :
    adaptQ κ !![0, 0; 0, σ] γ t =
      (if κ ≤ κck then ((1 - √(1 - 4 * κ)) / 2) ^ 2 else 1) * (1 + yA2 σ κ t) := by
  have hy := yA2_nonneg σ hσ κ t
  unfold adaptQ
  rw [rlam_A2 σ hσ κ hκ γ t, sigP_A2 σ hσ κ hκ γ t, loadA_diag0 le_rfl hy, loadA_diag1 le_rfl hy,
    qf_diag]
  split_ifs <;> ring

include hσ hκ in
lemma sigP11_A2 (γ : ℕ → ℝ) (t : ℕ) : SigP κ !![0, 0; 0, σ] γ t 1 1 = yA2 σ κ t := by
  rw [sigP_A2 σ hσ κ hκ γ t]; simp

end A2

/-! ### Corollary A3: `Σ₁ = diag(σ²_θ, 0)`, `γ_t = 1` -/

section A3

variable (σ : ℝ) (hσ : 0 < σ) (κ : ℝ) (hκ : 0 < κ)

include hσ hκ in
lemma sigP_A3 (t : ℕ) :
    SigP κ !![σ, 0; 0, 0] (fun _ => 1) t = !![(CorA3.stepA κ)^[t] σ, 0; 0, 0] := by
  have hS : (!![σ, 0; 0, 0] : M2).PosSemidef := psd_diag σ 0 hσ.le le_rfl
  show SigmaC (fun _ => κ) !![σ, 0; 0, 0] (fun _ => 1) t = _
  rw [← SigmaSeq_eq_SigmaC (fun _ => κ) (fun _ => hκ) _ hS (fun _ => 1)]
  exact CorA3.seq_eq σ hσ κ hκ t

include hσ hκ in
lemma rlam_A3 (t : ℕ) :
    rlam κ !![σ, 0; 0, 0] (fun _ => 1) t =
      if κ * CorA3.s3 ((CorA3.stepA κ)^[t] σ) ^ 2 ≤ κck then
        (1 + √(1 - 4 * κ * CorA3.s3 ((CorA3.stepA κ)^[t] σ) ^ 2)) / 2 else 0 := by
  have hx := CorA3.iterate_stepA_pos κ σ hσ t
  have hsens : sens (SigP κ !![σ, 0; 0, 0] (fun _ => 1) t) 1 =
      CorA3.s3 ((CorA3.stepA κ)^[t] σ) := by
    rw [sigP_A3 σ hσ κ hκ t]; exact CorA3.sens_eq _ hx.le
  have hrev : revP κ !![σ, 0; 0, 0] (fun _ => 1) t ↔
      κ * CorA3.s3 ((CorA3.stepA κ)^[t] σ) ^ 2 ≤ κck := by
    rw [revP_def]; simp only [hsens]
  rw [rlam_def]
  by_cases h : κ * CorA3.s3 ((CorA3.stepA κ)^[t] σ) ^ 2 ≤ κck
  · rw [ite_eq_left (hrev.2 h), ite_eq_left h]
    simp only [lamF, hsens]
  · rw [ite_eq_right (fun h' => h (hrev.1 h')), ite_eq_right h]

include hσ hκ in
lemma adaptQ_A3 (t : ℕ) :
    adaptQ κ !![σ, 0; 0, 0] (fun _ => 1) t =
      (if κ * CorA3.s3 ((CorA3.stepA κ)^[t] σ) ^ 2 ≤ κck then
          ((1 - √(1 - 4 * κ * CorA3.s3 ((CorA3.stepA κ)^[t] σ) ^ 2)) / 2) ^ 2 else 1) *
        (1 + ((CorA3.stepA κ)^[t] σ) ^ 2 / (1 + (CorA3.stepA κ)^[t] σ)) +
      (CorA3.stepA κ)^[t] σ / (1 + (CorA3.stepA κ)^[t] σ) := by
  have hx := CorA3.iterate_stepA_pos κ σ hσ t
  unfold adaptQ
  rw [rlam_A3 σ hσ κ hκ t, sigP_A3 σ hσ κ hκ t]
  simp only [loadA_diag0 hx.le le_rfl, loadA_diag1 hx.le le_rfl, qf_diag]
  generalize (CorA3.stepA κ)^[t] σ = x at hx ⊢
  have h1x : (1 + x) ≠ 0 := by positivity
  split_ifs
  · field_simp
    ring
  · field_simp
    ring

include hσ hκ in
lemma sigP11_A3 (t : ℕ) : SigP κ !![σ, 0; 0, 0] (fun _ => 1) t 1 1 = 0 := by
  rw [sigP_A3 σ hσ κ hκ t]; simp

end A3

end CC.Bridge
