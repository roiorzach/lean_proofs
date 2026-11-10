import ConformityConcerns.BridgeK.Defs

/-!
# The covariance process with disclosures, in terms of `SigmaC`

* without disclosures, `Σ_t` is the covariance process `SigmaC` of `Dynamics/Defs.lean` along the
  realised `(κ_t, γ_t)`;
* with one intervention at date `τ`, `Σ_t` is unchanged before `τ`, `Σ_τ` is the update of the
  no-intervention covariance by the disclosed signal (`observeTheta` / `observeMu`), and from `τ`
  on `Σ` follows `SigmaC` started from that updated covariance.
-/

namespace CC.BridgeK

/-- Without disclosures, `Σ_t` is `SigmaC` along `(κ_t, γ_t)`. -/
theorem SigK_noDisc (S₁ : M2) (w : ℕ → ℝ × ℝ) (t : ℕ) :
    SigK S₁ noDisc w t = SigmaC (fun s => (w s).1) S₁ (fun s => (w s).2) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change stepCov (w t).1 (w t).2 (discCov none (SigPre S₁ noDisc w t)) = _
    change discCov none (SigPre S₁ noDisc w t) = _ at ih
    rw [ih]; rfl

/-- Before and at the intervention date, the covariance before the disclosure is the
no-intervention one. -/
theorem SigPre_interventionAt_le (S₁ : M2) (w : ℕ → ℝ × ℝ) (τ : ℕ) (i : Fin 2) (n : ℝ) {t : ℕ}
    (ht : t ≤ τ) :
    SigPre S₁ (interventionAt τ i n) w t = SigmaC (fun s => (w s).1) S₁ (fun s => (w s).2) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : interventionAt τ i n t = none := by simp [interventionAt]; omega
    change stepCov (w t).1 (w t).2 (discCov (interventionAt τ i n t) (SigPre S₁ _ w t)) = _
    rw [h1, discCov, ih (by omega)]; rfl

/-- After an individual-oriented intervention at `τ`, `Σ_τ` is the update of the no-intervention
covariance by the signal `θ + √n ξ`. -/
theorem SigK_individualAt (S₁ : M2) (w : ℕ → ℝ × ℝ) (τ : ℕ) (n : ℝ) :
    SigK S₁ (individualAt τ n) w τ =
      observeTheta (SigmaC (fun s => (w s).1) S₁ (fun s => (w s).2) τ) n := by
  simp only [SigK, individualAt, SigPre_interventionAt_le S₁ w τ 0 n le_rfl]
  simp [interventionAt, discCov]

/-- After a peer-oriented intervention at `τ`, `Σ_τ` is the update of the no-intervention
covariance by the signal `μ + √n ξ`. -/
theorem SigK_peerAt (S₁ : M2) (w : ℕ → ℝ × ℝ) (τ : ℕ) (n : ℝ) :
    SigK S₁ (peerAt τ n) w τ = observeMu (SigmaC (fun s => (w s).1) S₁ (fun s => (w s).2) τ) n := by
  simp only [SigK, peerAt, SigPre_interventionAt_le S₁ w τ 1 n le_rfl]
  simp [interventionAt, discCov]

/-- From the intervention date on, `Σ` follows `SigmaC` started from the post-disclosure
covariance `Σ_τ`. -/
theorem SigK_interventionAt_after (S₁ : M2) (w : ℕ → ℝ × ℝ) (τ : ℕ) (i : Fin 2) (n : ℝ)
    (t : ℕ) :
    SigK S₁ (interventionAt τ i n) w (τ + t) =
      SigmaC (fun s => (w (τ + s)).1) (SigK S₁ (interventionAt τ i n) w τ)
        (fun s => (w (τ + s)).2) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : interventionAt τ i n (τ + (t + 1)) = none := by simp [interventionAt]
    change discCov (interventionAt τ i n (τ + (t + 1)))
      (stepCov (w (τ + t)).1 (w (τ + t)).2 (SigK S₁ (interventionAt τ i n) w (τ + t))) = _
    rw [h1, discCov, ih]; rfl

end CC.BridgeK
