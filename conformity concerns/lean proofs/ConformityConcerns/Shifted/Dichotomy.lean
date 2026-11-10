import ConformityConcerns.Shifted.Bayes

/-!
# Shifted preferences: the linear dichotomy and revealing linear equilibria

* `Std.sh_lemma3_ne`: if `s̃ ≠ 0`, every linear equilibrium with shift `c` is pooling or
  revealing (the proof of `Std.lemma3_ne`, with `gstar α (β - c) p`).
* `Std.sh_rev_char`: in a revealing linear equilibrium with shift `c`, the posterior-mean slope
  `α` solves `(1 + κα²) s̃ = α` and `a = E Z + (Z - E Z)/(1 + κα²) + κ α c` a.s.
-/

namespace CC.LG

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Game

variable {G : Game Ω}

section Std

variable (hG : G.Std)
include hG

/-- **Lemma 3 with shift `c`, `s̃ ≠ 0`.** Every linear equilibrium is pooling or revealing. -/
theorem Std.sh_lemma3_ne (c : ℝ) (hs : G.sens ≠ 0) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsShLinearEq c a φ) : G.IsPooling a ∨ G.IsRevealing a := by
  have := hG.prob
  have := hE.1.markov
  by_cases hpool : G.IsPooling a
  · exact Or.inl hpool
  right
  obtain ⟨α, β, p, q, hlin⟩ := hE.2
  obtain ⟨x1, x2, hx1, hx2, hlt⟩ := two_support hE.1.meas hpool
  have hx1I : x1 ∈ G.actionHull a := support_subset_hull a hx1
  have hx2I : x2 ∈ G.actionHull a := support_subset_hull a hx2
  have hIcc : Icc x1 x2 ⊆ G.actionHull a := Icc_subset_hull hx1I hx2I hlt.le
  set D := 1 + G.κ * α ^ 2 with hDdef
  have hD : 0 < D := by have := hG.κ_pos; positivity
  set k := 1 / D with hkdef
  have hk : 0 < k := by positivity
  set c₁ := -(G.κ * p / 2 + G.κ * α * ((β - c) - G.norm)) / D with hcdef
  have hgs : ∀ z, G.gstar α (β - c) p z = k * z + c₁ := fun z =>
    gstar_eq α (β - c) p z hD.ne'
  have hnear := hG.sh_nearest c hE.1 hlin
  have hnear' : ∀ᵐ ω ∂G.P, a ω ∈ G.actionHull a ∧ ∀ y ∈ G.actionHull a,
      (a ω - (k * G.Z ω + c₁)) ^ 2 ≤ (y - (k * G.Z ω + c₁)) ^ 2 :=
    hnear.mono fun ω hω => by rw [← hgs]; exact hω
  -- interior: the action reveals `Z` on `(x1, x2)`
  have hint_ae : ∀ᵐ ω ∂G.P, (a ω ∈ Ioo x1 x2 ↔ k * G.Z ω + c₁ ∈ Ioo x1 x2) ∧
      (a ω ∈ Ioo x1 x2 → a ω = k * G.Z ω + c₁) := by
    filter_upwards [hnear'] with ω hω
    have hiff := np_Ioo hω.2 hx1I hx2I hIcc
    exact ⟨hiff, fun h => np_eq hω.2 (hIcc (Ioo_subset_Icc_self (hiff.1 h)))⟩
  have hpost := hG.sh_ae_eq_postK_on c hE.1 hk.ne' measurableSet_Ioo hint_ae
  have hUpos : 0 < G.P.map (fun ω => k * G.Z ω + c₁) (Ioo x1 x2) := by
    rw [hG.map_aff]
    exact gauss_pos_Ioo (hG.aff_var_ne hk.ne') hlt
  obtain ⟨e1, e2, e3, e4⟩ :=
    hG.ident hk.ne' hUpos hpost (fun x hx => hlin x (hIcc (Ioo_subset_Icc_self hx)))
  have hmeanall : ∀ x, G.sens * ((x - c₁) / k) + G.residMean = α * x + β := by
    intro x
    rw [e1, e2]
    field_simp
    ring
  have hν'g := hG.map_aff k c₁
  -- the support is unbounded above
  have hnab : ¬ BddAbove (G.P.map a).support := by
    intro hb
    set hi := sSup (G.P.map a).support
    have hhiS : hi ∈ (G.P.map a).support := Measure.isClosed_support.csSup_mem ⟨x1, hx1⟩ hb
    have hhiI : hi ∈ G.actionHull a := support_subset_hull a hhiS
    have hub : ∀ y ∈ G.actionHull a, y ≤ hi := fun y hy =>
      convexHull_min (fun s hs => le_csSup hb hs) (convex_Iic hi) hy
    have hx1hi : x1 < hi := lt_of_lt_of_le hlt (le_csSup hb hx2)
    have hIcc' : Icc x1 hi ⊆ G.actionHull a := Icc_subset_hull hx1I hhiI hx1hi.le
    have hae : ∀ᵐ ω ∂G.P, a ω = hi ↔ k * G.Z ω + c₁ ∈ Ici hi := by
      filter_upwards [hnear'] with ω hω
      exact np_top hω.2 hx1I hhiI hx1hi hIcc' hub hω.1
    refine hG.sh_atom_contra c hE.1 hk hmeanall hs (hlin hi hhiI).2.1 measurableSet_Ici hae ?_
    rw [hν'g]
    exact (gauss_setIntegral_Ici_pos (hG.aff_var_ne hk.ne') hi).ne'
  -- the support is unbounded below
  have hnbb : ¬ BddBelow (G.P.map a).support := by
    intro hb
    set lo := sInf (G.P.map a).support
    have hloS : lo ∈ (G.P.map a).support := Measure.isClosed_support.csInf_mem ⟨x1, hx1⟩ hb
    have hloI : lo ∈ G.actionHull a := support_subset_hull a hloS
    have hlb : ∀ y ∈ G.actionHull a, lo ≤ y := fun y hy =>
      convexHull_min (fun s hs => csInf_le hb hs) (convex_Ici lo) hy
    have hlox2 : lo < x2 := lt_of_le_of_lt (csInf_le hb hx1) hlt
    have hIcc' : Icc lo x2 ⊆ G.actionHull a := Icc_subset_hull hloI hx2I hlox2.le
    have hae : ∀ᵐ ω ∂G.P, a ω = lo ↔ k * G.Z ω + c₁ ∈ Iic lo := by
      filter_upwards [hnear'] with ω hω
      exact np_bot hω.2 hx2I hloI hlox2 hIcc' hlb hω.1
    refine hG.sh_atom_contra c hE.1 hk hmeanall hs (hlin lo hloI).2.1 measurableSet_Iic hae ?_
    rw [hν'g]
    exact (gauss_setIntegral_Iic_neg (hG.aff_var_ne hk.ne') lo).ne
  -- hence `I(h) = ℝ` and `a = k Z + c₁` a.s.
  have hIuniv : ∀ y, y ∈ G.actionHull a := by
    intro y
    obtain ⟨s1, hs1, hs1y⟩ := not_bddBelow_iff.1 hnbb y
    obtain ⟨s2, hs2, hs2y⟩ := not_bddAbove_iff.1 hnab y
    exact Icc_subset_hull (support_subset_hull a hs1) (support_subset_hull a hs2)
      (hs1y.le.trans hs2y.le) ⟨hs1y.le, hs2y.le⟩
  have ha : a =ᵐ[G.P] fun ω => k * G.Z ω + c₁ :=
    hnear'.mono fun ω hω => np_eq hω.2 (hIuniv _)
  exact ⟨k, c₁, hk, ha⟩

/-- **Revealing linear equilibria with shift `c`.** -/
theorem Std.sh_rev_char (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShLinearEq c a φ)
    (hR : G.IsRevealing a) :
    ∃ α : ℝ, (1 + G.κ * α ^ 2) * G.sens = α ∧
      a =ᵐ[G.P] (fun ω => G.meanZ + (G.Z ω - G.meanZ) / (1 + G.κ * α ^ 2) + G.κ * α * c) := by
  have := hG.prob
  have := hE.1.markov
  obtain ⟨k, b, hk, hab⟩ := hR
  have hmap : G.P.map a = G.P.map (fun ω => k * G.Z ω + b) := Measure.map_congr hab
  have hsupp : (G.P.map a).support = univ := by
    rw [hmap, hG.map_aff]
    exact gauss_support (hG.aff_var_ne hk.ne')
  have hI : G.actionHull a = univ := by
    unfold actionHull
    rw [hsupp, convexHull_univ]
  obtain ⟨α, β, p, q, hlin⟩ := hE.2
  have hlin' : G.LinOn φ univ α β p q := by rw [← hI]; exact hlin
  have hae := hG.sh_ae_eq_postK_on c hE.1 hk.ne' MeasurableSet.univ
    (hab.mono fun ω hω => ⟨by simp, fun _ => hω⟩)
  have hpos : 0 < G.P.map (fun ω => k * G.Z ω + b) univ := by simp
  obtain ⟨e1, e2, e3, e4⟩ := hG.ident hk.ne' hpos hae hlin'
  have hnear := hG.sh_nearest c hE.1 hlin
  set D := 1 + G.κ * α ^ 2 with hDdef
  have hD : 0 < D := by have := hG.κ_pos; positivity
  have hgs : ∀ z, G.gstar α (β - c) p z =
      (1 / D) * z + (-(G.κ * p / 2 + G.κ * α * ((β - c) - G.norm)) / D) := fun z =>
    gstar_eq α (β - c) p z hD.ne'
  have hae2 : ∀ᵐ ω ∂G.P, k * G.Z ω + b =
      (1 / D) * G.Z ω + (-(G.κ * p / 2 + G.κ * α * ((β - c) - G.norm)) / D) := by
    filter_upwards [hnear, hab] with ω hω hω2
    rw [← hω2, ← hgs]
    exact np_eq hω.2 (by rw [hI]; exact mem_univ _)
  obtain ⟨hk1, hb1⟩ := hG.affine_coeff_eq hae2
  have hm := hG.residMean_eq
  -- `s̃ = α k`, `k = 1/D`
  have hsk : G.sens = α * k := by rw [e1]; field_simp
  have hkD : k * D = 1 := by rw [hk1]; field_simp
  refine ⟨α, ?_, ?_⟩
  · rw [hsk]
    have : (1 + G.κ * α ^ 2) * (α * k) = α * (k * D) := by rw [hDdef]; ring
    rw [this, hkD, mul_one]
  · have hb2 : b * D = -(G.κ * α * ((β - c) - G.norm)) := by
      rw [hb1, e3]
      field_simp
      ring
    have hβ : β = G.norm - α * k * G.meanZ - α * b := by
      rw [e2, hm, hsk]
      field_simp
    have hbv : b = G.meanZ - G.meanZ * k + G.κ * α * c := by
      rw [hβ] at hb2
      have hDk : D - G.κ * α ^ 2 = 1 := by rw [hDdef]; ring
      have : b * (D - G.κ * α ^ 2) = G.κ * α ^ 2 * k * G.meanZ + G.κ * α * c := by
        linear_combination hb2
      rw [hDk, mul_one] at this
      rw [this]
      have : G.κ * α ^ 2 = D - 1 := by rw [hDdef]; ring
      rw [this]
      linear_combination G.meanZ * hkD
    filter_upwards [hab] with ω hω
    rw [hω, hbv, hk1, ← hDdef]
    field_simp
    ring

end Std

end Game

end CC.LG
