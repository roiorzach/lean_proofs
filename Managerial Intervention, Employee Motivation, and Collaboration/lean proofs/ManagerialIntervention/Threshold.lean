import ManagerialIntervention.Formal

/-!
# Proposition 4 (choice of formal delegation) and Proposition B.1 (contractible authority)

The principal's ex-ante payoff in regime `r` is `e_a^r · Ũ_p^r`.  Holding the primitives
`(E v_a, E v_p, E(v_a 1_{v_a<0}), E(v_p 1_{v_p<0}), c_a, c_p)` fixed, the payoff under
centralization depends on the distribution only through `α_a`, and the payoff under
delegation only through `α_p`.  We record the primitives in `MI.Prim`, write the two payoffs
as functions of the alignment parameters, and obtain the threshold `α̂` from the generic
lemma `MI.threshold_exists`.

The paper states `α̂(·) < α̃(·)`.  This holds at every `α_p < 1`; at `α_p = 1` both
thresholds equal `1` (`prop4` records `α̂ 1 = 1`, and `MI.prop4_boundary` shows that no threshold
can satisfy the "iff" with `α̂ 1 < α̃ 1`).
-/

namespace MI

open Set

/-- **A monotone threshold.** If `f` is monotone and continuous, `g` is monotone and some
`α₀ ≤ 1` has `f α₀ ≤ g x` for all `x`, then there is a monotone `t` with
`g x < f α ↔ t x < α` for all `α ≤ 1`. -/
theorem threshold_exists {f g : ℝ → ℝ} (hf : Monotone f) (hfc : Continuous f) (hg : Monotone g)
    {α0 : ℝ} (hα0 : α0 ≤ 1) (hlow : ∀ x, f α0 ≤ g x) :
    ∃ t : ℝ → ℝ, Monotone t ∧ (∀ x, t x ≤ 1) ∧ ∀ x α, α ≤ 1 → (g x < f α ↔ t x < α) := by
  let S : ℝ → Set ℝ := fun x => {α | α ≤ 1 ∧ f α ≤ g x}
  have hne : ∀ x, (S x).Nonempty := fun x => ⟨α0, hα0, hlow x⟩
  have hbdd : ∀ x, BddAbove (S x) := fun x => ⟨1, fun α h => h.1⟩
  have hcl : ∀ x, IsClosed (S x) := fun x =>
    (isClosed_Iic (a := (1 : ℝ))).inter (isClosed_le hfc continuous_const)
  have hmem : ∀ x, sSup (S x) ∈ S x := fun x => (hcl x).csSup_mem (hne x) (hbdd x)
  refine ⟨fun x => sSup (S x), ?_, fun x => (hmem x).1, ?_⟩
  · intro x x' hxx'
    exact csSup_le_csSup (hbdd x') (hne x) fun α h => ⟨h.1, h.2.trans (hg hxx')⟩
  · intro x α hα
    show g x < f α ↔ sSup (S x) < α
    constructor
    · intro h
      by_contra h'
      push Not at h'
      have h1 := hf h'
      have h2 : f (sSup (S x)) ≤ g x := (hmem x).2
      linarith
    · intro h
      by_contra h'
      push Not at h'
      have := le_csSup (hbdd x) (show α ∈ S x from ⟨hα, h'⟩)
      linarith

/-- The primitives that are held fixed when the alignment parameters vary. -/
structure Prim where
  A : ℝ
  P : ℝ
  Na : ℝ
  Np : ℝ
  ca : Cost
  cp : Cost

/-- The paper's sign assumptions on the primitives. -/
structure Prim.Valid (π : Prim) : Prop where
  A_pos : 0 < π.A
  P_pos : 0 < π.P
  Na_neg : π.Na < 0
  Np_neg : π.Np < 0

namespace Prim

variable (π : Prim)

/-- principal effort under centralization -/
noncomputable def epC : ℝ := π.cp.br (-π.Np)
/-- principal interim payoff under centralization, `Ũ_p^c` -/
noncomputable def UC : ℝ := π.P + π.cp.val (-π.Np)
/-- agent's marginal benefit under centralization -/
noncomputable def mC (α : ℝ) : ℝ := π.A - α * π.epC * π.Na
/-- agent effort under centralization -/
noncomputable def eaC (α : ℝ) : ℝ := π.ca.br (π.mC α)
/-- principal's ex-ante payoff under centralization -/
noncomputable def PiC (α : ℝ) : ℝ := π.eaC α * π.UC
/-- principal effort under delegation -/
noncomputable def epD (x : ℝ) : ℝ := π.cp.br (-(max x 0) * π.Np)
/-- principal interim payoff under delegation, `Ũ_p^d` -/
noncomputable def UD (x : ℝ) : ℝ := π.P + π.cp.val (-x * π.Np)
/-- agent's marginal benefit under delegation -/
noncomputable def mD (x : ℝ) : ℝ := π.A - π.epD x * π.Na
/-- agent effort under delegation -/
noncomputable def eaD (x : ℝ) : ℝ := π.ca.br (π.mD x)
/-- principal's ex-ante payoff under delegation -/
noncomputable def PiD (x : ℝ) : ℝ := π.eaD x * π.UD x
/-- total surplus under centralization -/
noncomputable def WC (α : ℝ) : ℝ := π.ca.val (π.mC α) + π.PiC α
/-- total surplus under delegation -/
noncomputable def WD (x : ℝ) : ℝ := π.ca.val (π.mD x) + π.PiD x

variable {π}

lemma epC_pos (hπ : π.Valid) : 0 < π.epC := π.cp.br_pos (by linarith [hπ.Np_neg])

lemma UC_pos (hπ : π.Valid) : 0 < π.UC := by
  unfold UC; linarith [π.cp.val_nonneg (-π.Np), hπ.P_pos]

lemma UD_pos (hπ : π.Valid) (x : ℝ) : 0 < π.UD x := by
  unfold UD; linarith [π.cp.val_nonneg (-x * π.Np), hπ.P_pos]

lemma mC_mono (hπ : π.Valid) : Monotone π.mC := by
  intro α α' h
  unfold mC
  have h0 : 0 ≤ (α' - α) * (π.epC * -π.Na) :=
    mul_nonneg (by linarith) (mul_nonneg (epC_pos hπ).le (by linarith [hπ.Na_neg]))
  nlinarith [h0]

lemma mC_continuous : Continuous π.mC := by
  unfold mC; fun_prop

lemma PiC_mono (hπ : π.Valid) : Monotone π.PiC := by
  intro α α' h
  exact mul_le_mul_of_nonneg_right (π.ca.br_mono (mC_mono hπ h)) (UC_pos hπ).le

lemma PiC_continuous : Continuous π.PiC :=
  (π.ca.br_continuous.comp mC_continuous).mul continuous_const

lemma epD_mono (hπ : π.Valid) : Monotone π.epD := by
  intro x x' h
  apply π.cp.br_mono
  have : max x 0 ≤ max x' 0 := max_le_max h le_rfl
  nlinarith [hπ.Np_neg]

lemma epD_nonneg (x : ℝ) : 0 ≤ π.epD x := π.cp.br_nonneg _

lemma mD_mono (hπ : π.Valid) : Monotone π.mD := by
  intro x x' h
  unfold mD
  nlinarith [epD_mono hπ h, hπ.Na_neg]

lemma mD_pos (hπ : π.Valid) (x : ℝ) : 0 < π.mD x := by
  unfold mD; nlinarith [epD_nonneg (π := π) x, hπ.Na_neg, hπ.A_pos]

lemma UD_mono (hπ : π.Valid) : Monotone π.UD := by
  intro x x' h
  unfold UD
  have := π.cp.val_mono (show -x * π.Np ≤ -x' * π.Np by nlinarith [hπ.Np_neg])
  linarith

lemma PiD_nonneg (hπ : π.Valid) (x : ℝ) : 0 ≤ π.PiD x :=
  mul_nonneg (π.ca.br_nonneg _) (UD_pos hπ x).le

lemma PiD_mono (hπ : π.Valid) : Monotone π.PiD := by
  intro x x' h
  exact mul_le_mul (π.ca.br_mono (mD_mono hπ h)) (UD_mono hπ h) (UD_pos hπ x).le
    (π.ca.br_nonneg _)

lemma WC_mono (hπ : π.Valid) : Monotone π.WC := by
  intro α α' h
  unfold WC
  have := π.ca.val_mono (mC_mono hπ h)
  have := PiC_mono hπ h
  linarith

lemma WC_continuous : Continuous π.WC :=
  (π.ca.val_continuous.comp mC_continuous).add PiC_continuous

lemma WD_mono (hπ : π.Valid) : Monotone π.WD := by
  intro x x' h
  unfold WD
  have := π.ca.val_mono (mD_mono hπ h)
  have := PiD_mono hπ h
  linarith

/-- The alignment level at which the agent's effort under centralization hits zero. -/
noncomputable def α0 (π : Prim) : ℝ := π.A / (π.epC * π.Na)

lemma α0_le (hπ : π.Valid) : α0 π ≤ 1 := by
  unfold α0
  have : π.epC * π.Na < 0 := mul_neg_of_pos_of_neg (epC_pos hπ) hπ.Na_neg
  have : π.A / (π.epC * π.Na) < 0 := div_neg_of_pos_of_neg hπ.A_pos this
  linarith

lemma mC_α0 (hπ : π.Valid) : π.mC (α0 π) = 0 := by
  unfold mC α0
  have := (epC_pos hπ).ne'
  have := hπ.Na_neg.ne
  field_simp
  ring

lemma PiC_α0 (hπ : π.Valid) : π.PiC (α0 π) = 0 := by
  unfold PiC eaC; rw [mC_α0 hπ, π.ca.br_eq_zero_of_nonpos le_rfl, zero_mul]

lemma WC_α0 (hπ : π.Valid) : π.WC (α0 π) = 0 := by
  unfold WC; rw [PiC_α0 hπ, mC_α0 hπ, π.ca.val_eq_zero_of_nonpos le_rfl, add_zero]

/-- At `α_a = α̃(x)` the agent's incentives in the two regimes coincide. -/
lemma mC_alphaTilde (hπ : π.Valid) (x : ℝ) : π.mC (alphaTilde π.cp π.Np x) = π.mD x := by
  unfold mC mD alphaTilde epD
  have := (epC_pos hπ).ne'
  unfold epC at this ⊢
  field_simp

lemma UD_lt_UC (hπ : π.Valid) {x : ℝ} (hx : x < 1) : π.UD x < π.UC := by
  unfold UD UC
  have hN := hπ.Np_neg
  have := π.cp.val_strict (show -x * π.Np < -π.Np by nlinarith) (by linarith)
  linarith

lemma PiD_lt_PiC_alphaTilde (hπ : π.Valid) {x : ℝ} (hx : x < 1) :
    π.PiD x < π.PiC (alphaTilde π.cp π.Np x) := by
  unfold PiD PiC eaC
  rw [mC_alphaTilde hπ]
  exact mul_lt_mul_of_pos_left (UD_lt_UC hπ hx) (π.ca.br_pos (mD_pos hπ x))

lemma WD_lt_WC_alphaTilde (hπ : π.Valid) {x : ℝ} (hx : x < 1) :
    π.WD x < π.WC (alphaTilde π.cp π.Np x) := by
  unfold WD WC
  rw [mC_alphaTilde hπ]
  linarith [PiD_lt_PiC_alphaTilde hπ hx]

lemma PiC_one_eq_PiD_one (hπ : π.Valid) : π.PiC 1 = π.PiD 1 := by
  have h := mC_alphaTilde hπ 1
  rw [alphaTilde_one _ hπ.Np_neg] at h
  unfold PiC PiD eaC eaD UC UD
  rw [h]; ring_nf

lemma WC_one_eq_WD_one (hπ : π.Valid) : π.WC 1 = π.WD 1 := by
  have h := mC_alphaTilde hπ 1
  rw [alphaTilde_one _ hπ.Np_neg] at h
  unfold WC WD
  rw [h, PiC_one_eq_PiD_one hπ]

/-- The threshold construction shared by Propositions 4 and B.1. -/
theorem threshold_of {f g : ℝ → ℝ} (hπ : π.Valid) (hf : Monotone f) (hfc : Continuous f)
    (hg : Monotone g) (hlow : ∀ x, f (α0 π) ≤ g x)
    (hstrict : ∀ x < 1, g x < f (alphaTilde π.cp π.Np x)) (h1 : f 1 = g 1) :
    ∃ αhat : ℝ → ℝ, Monotone αhat ∧ (∀ x < 1, αhat x < alphaTilde π.cp π.Np x) ∧
      αhat 1 = 1 ∧ ∀ x α, α ≤ 1 → (g x < f α ↔ αhat x < α) := by
  obtain ⟨t, ht, hle1, hiff⟩ := threshold_exists hf hfc hg (α0_le hπ) hlow
  refine ⟨t, ht, fun x hx => ?_, ?_, hiff⟩
  · exact (hiff x _ (alphaTilde_le_one _ hπ.Np_neg hx.le)).1 (hstrict x hx)
  · apply le_antisymm (hle1 1)
    · by_contra h
      push Not at h
      obtain ⟨α, hα1, hα2⟩ := exists_between h
      have := (hiff 1 α hα2.le).2 hα1
      have := hf hα2.le
      linarith

end Prim

namespace Env

variable (E : Env)

/-- The primitives of an environment. -/
noncomputable def prim : Prim := ⟨E.A, E.P, E.Na, E.Np, E.ca, E.cp⟩

lemma prim_valid : E.prim.Valid := ⟨E.A_pos, E.P_pos, E.Na_neg, E.Np_neg⟩

lemma Up_cen_eq : E.Up .cen (E.ep .cen) = E.prim.UC := by
  rw [E.Up_eq]; simp only [mp, ep, prim, Prim.UC, Cost.val]; ring

lemma Up_del_eq : E.Up .del (E.ep .del) = E.prim.UD E.alphaP := by
  rw [E.Up_eq]
  simp only [mp, ep, prim, Prim.UD, Cost.val]
  rw [E.Xp_eq]; ring_nf

lemma Va_cen_eq : E.Va .cen (E.ep .cen) = E.prim.mC E.alphaA := by
  rw [E.Va_cen, E.Xa_eq]; simp only [prim, Prim.mC, Prim.epC, ep, mp]; ring

lemma Va_del_eq : E.Va .del (E.ep .del) = E.prim.mD E.alphaP := by
  rw [E.Va_del, E.ep_del_eq]; rfl

lemma ea_cen_prim : E.ea .cen = E.prim.eaC E.alphaA := by
  unfold ea; rw [E.Va_cen_eq]; rfl

lemma ea_del_prim : E.ea .del = E.prim.eaD E.alphaP := by
  unfold ea; rw [E.Va_del_eq]; rfl

/-- The principal's ex-ante payoff `e_a^r · Ũ_p^r` at the equilibrium. -/
lemma payoff_cen {ac pc : ℝ} (hc : E.IsEq .cen ac pc) :
    ac * E.Up .cen pc = E.prim.PiC E.alphaA := by
  rw [E.isEq_iff] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rw [E.Up_cen_eq, E.ea_cen_prim]; rfl

lemma payoff_del {ad pd : ℝ} (hd : E.IsEq .del ad pd) :
    ad * E.Up .del pd = E.prim.PiD E.alphaP := by
  rw [E.isEq_iff] at hd
  obtain ⟨rfl, rfl⟩ := hd
  rw [E.Up_del_eq, E.ea_del_prim]; rfl

/-- Total surplus (agent's plus principal's ex-ante payoff) at the equilibrium. -/
lemma surplus_cen {ac pc : ℝ} (hc : E.IsEq .cen ac pc) :
    E.Ua .cen pc ac + ac * E.Up .cen pc = E.prim.WC E.alphaA := by
  rw [E.payoff_cen hc]
  rw [E.isEq_iff] at hc
  obtain ⟨rfl, rfl⟩ := hc
  unfold Prim.WC Ua ea
  rw [E.Va_cen_eq]; rfl

lemma surplus_del {ad pd : ℝ} (hd : E.IsEq .del ad pd) :
    E.Ua .del pd ad + ad * E.Up .del pd = E.prim.WD E.alphaP := by
  rw [E.payoff_del hd]
  rw [E.isEq_iff] at hd
  obtain ⟨rfl, rfl⟩ := hd
  unfold Prim.WD Ua ea
  rw [E.Va_del_eq]; rfl

end Env

/-- **Proposition 4.** Fix the primitives `π`.  There is an increasing threshold `α̂` such that,
in every environment with these primitives, the principal strictly prefers to centralize iff
`α_a > α̂(α_p)`.  Moreover `α̂(x) < α̃(x)` for every `x < 1`, and `α̂(1) = α̃(1) = 1`. -/
theorem prop4 (π : Prim) (hπ : π.Valid) :
    ∃ αhat : ℝ → ℝ, Monotone αhat ∧ (∀ x < 1, αhat x < alphaTilde π.cp π.Np x) ∧
      αhat 1 = 1 ∧
      ∀ E : Env, E.prim = π → ∀ ac pc ad pd : ℝ, E.IsEq .cen ac pc → E.IsEq .del ad pd →
        (ad * E.Up .del pd < ac * E.Up .cen pc ↔ αhat E.alphaP < E.alphaA) := by
  obtain ⟨t, ht, hlt, h1, hiff⟩ := Prim.threshold_of hπ (Prim.PiC_mono hπ) Prim.PiC_continuous
    (Prim.PiD_mono hπ) (fun x => by rw [Prim.PiC_α0 hπ]; exact Prim.PiD_nonneg hπ x)
    (fun x hx => Prim.PiD_lt_PiC_alphaTilde hπ hx) (Prim.PiC_one_eq_PiD_one hπ)
  refine ⟨t, ht, hlt, h1, fun E hE ac pc ad pd hc hd => ?_⟩
  rw [E.payoff_cen hc, E.payoff_del hd, hE]
  exact hiff _ _ E.alphaA_le_one

/-- **Proposition B.1 (contractible authority).** If decision rights are allocated to maximise
total surplus, there is an increasing threshold `α̂^c` such that centralization is chosen
(strictly preferred) iff `α_a > α̂^c(α_p)`; moreover `α̂^c(x) < α̃(x)` for every `x < 1`, and
`α̂^c(1) = α̃(1) = 1`. -/
theorem propB1_contractible (π : Prim) (hπ : π.Valid) :
    ∃ αhat : ℝ → ℝ, Monotone αhat ∧ (∀ x < 1, αhat x < alphaTilde π.cp π.Np x) ∧
      αhat 1 = 1 ∧
      ∀ E : Env, E.prim = π → ∀ ac pc ad pd : ℝ, E.IsEq .cen ac pc → E.IsEq .del ad pd →
        (E.Ua .del pd ad + ad * E.Up .del pd < E.Ua .cen pc ac + ac * E.Up .cen pc ↔
          αhat E.alphaP < E.alphaA) := by
  obtain ⟨t, ht, hlt, h1, hiff⟩ := Prim.threshold_of hπ (Prim.WC_mono hπ) Prim.WC_continuous
    (Prim.WD_mono hπ)
    (fun x => by
      rw [Prim.WC_α0 hπ]
      exact add_nonneg (π.ca.val_nonneg _) (Prim.PiD_nonneg hπ x))
    (fun x hx => Prim.WD_lt_WC_alphaTilde hπ hx) (Prim.WC_one_eq_WD_one hπ)
  refine ⟨t, ht, hlt, h1, fun E hE ac pc ad pd hc hd => ?_⟩
  rw [E.surplus_cen hc, E.surplus_del hd, hE]
  exact hiff _ _ E.alphaA_le_one

end MI
