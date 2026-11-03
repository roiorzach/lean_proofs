import NoisyVD.Model

/-!
# Existence of symmetric equilibria (Lemma `lemma_symmetric_equilibrium_exists`)

The fixed point `q_ω := min {q : F(Δ_ω(q)⁻) ≤ q}` is selected, as in the paper.  The measurable
selection lemma `measurable_sInf_section` also gives the measurability of the smallest maximizer in
the proof of Statement 4 of Proposition `prop_general_failures`.
-/

open MeasureTheory Set Filter Topology Real

namespace NoisyVD

variable {A Ω : Type*}
  [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [Nonempty A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-- Measurable selection: the minimum of the sections of a closed subset of `Ω × [a, b]` is a
Borel function of the state. -/
theorem measurable_sInf_section {G : Set (Ω × ℝ)} (hG : IsClosed G) {a b : ℝ}
    (hGab : ∀ z ∈ G, z.2 ∈ Icc a b) (hne : ∀ ω, ∃ y, (ω, y) ∈ G) :
    (Measurable fun ω => sInf {y | (ω, y) ∈ G}) ∧ ∀ ω, (ω, sInf {y | (ω, y) ∈ G}) ∈ G ∧
      ∀ y, (ω, y) ∈ G → sInf {y | (ω, y) ∈ G} ≤ y := by
  have hbdd : ∀ ω, BddBelow {y | (ω, y) ∈ G} := fun ω => ⟨a, fun y hy => (hGab _ hy).1⟩
  have hsec : ∀ ω, IsClosed {y | (ω, y) ∈ G} := fun ω =>
    hG.preimage (Continuous.prodMk continuous_const continuous_id)
  have hmem : ∀ ω, (ω, sInf {y | (ω, y) ∈ G}) ∈ G := fun ω =>
    (hsec ω).csInf_mem (hne ω) (hbdd ω)
  refine ⟨?_, fun ω => ⟨hmem ω, fun y hy => csInf_le (hbdd ω) hy⟩⟩
  have hcomp : IsCompact G := by
    have hb : IsCompact ((univ : Set Ω) ×ˢ Icc a b) := isCompact_univ.prod isCompact_Icc
    refine hb.of_isClosed_subset hG fun z hz => ?_
    exact ⟨mem_univ _, hGab z hz⟩
  have hlsc : LowerSemicontinuous fun ω => sInf {y | (ω, y) ∈ G} := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    have heq : (fun ω => sInf {y | (ω, y) ∈ G}) ⁻¹' Iic c = Prod.fst '' (G ∩ (Prod.snd ⁻¹' Iic c)) := by
      ext ω
      constructor
      · intro h
        exact ⟨(ω, sInf {y | (ω, y) ∈ G}), ⟨hmem ω, h⟩, rfl⟩
      · rintro ⟨⟨ω', y⟩, ⟨h1, h2⟩, rfl⟩
        exact (csInf_le (hbdd ω') h1).trans h2
    rw [heq]
    have hclosed : IsClosed (G ∩ (Prod.snd ⁻¹' Iic c)) :=
      hG.inter (isClosed_Iic.preimage continuous_snd)
    exact ((hcomp.of_isClosed_subset hclosed inter_subset_left).image continuous_fst).isClosed
  exact hlsc.measurable

namespace Env

/-- Inner regularity of `Iio c`. -/
lemma exists_lt_Fm (E : Env A Ω) {c y : ℝ} (hy : y < E.Fm c) : ∃ c₀ < c, y < E.Fm c₀ := by
  let S : ℕ → Set ℝ := fun j => Iio (c - 1 / ((j : ℝ) + 1))
  have hmono : Monotone S := by
    intro i j hij
    apply Iio_subset_Iio
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le hi (by linarith)
    linarith
  have hU : ⋃ j, S j = Iio c := by
    ext x
    simp only [mem_iUnion, mem_Iio, S]
    constructor
    · rintro ⟨j, hj⟩
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨j, by linarith⟩
  have ht := tendsto_measure_iUnion_atTop (μ := (E.cost : Measure ℝ)) hmono
  rw [hU] at ht
  have ht' := (ENNReal.tendsto_toReal (measure_ne_top (E.cost : Measure ℝ) (Iio c))).comp ht
  have hev := (tendsto_order.1 ht').1 y hy
  obtain ⟨j, hj⟩ := hev.exists
  refine ⟨c - 1 / ((j : ℝ) + 1), ?_, hj⟩
  have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  linarith

/-- Inner regularity of `Ioi c`. -/
lemma exists_lt_Ioi (E : Env A Ω) {c y : ℝ} (hy : y < (E.cost : Measure ℝ).real (Ioi c)) :
    ∃ c₁ > c, y < (E.cost : Measure ℝ).real (Ioi c₁) := by
  let S : ℕ → Set ℝ := fun j => Ioi (c + 1 / ((j : ℝ) + 1))
  have hmono : Monotone S := by
    intro i j hij
    apply Ioi_subset_Ioi
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le hi (by linarith)
    linarith
  have hU : ⋃ j, S j = Ioi c := by
    ext x
    simp only [mem_iUnion, mem_Ioi, S]
    constructor
    · rintro ⟨j, hj⟩
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨j, by linarith⟩
  have ht := tendsto_measure_iUnion_atTop (μ := (E.cost : Measure ℝ)) hmono
  rw [hU] at ht
  have ht' := (ENNReal.tendsto_toReal (measure_ne_top (E.cost : Measure ℝ) (Ioi c))).comp ht
  have hev := (tendsto_order.1 ht').1 y hy
  obtain ⟨j, hj⟩ := hev.exists
  refine ⟨c + 1 / ((j : ℝ) + 1), ?_, hj⟩
  have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  linarith

/-- `c ↦ F(c⁻)` is lower semicontinuous. -/
lemma lowerSemicontinuous_Fm (E : Env A Ω) : LowerSemicontinuous E.Fm := by
  intro c y hy
  obtain ⟨c₀, hc₀, hy₀⟩ := E.exists_lt_Fm hy
  filter_upwards [Ioi_mem_nhds hc₀] with c' hc'
  exact lt_of_lt_of_le hy₀ (Fm_mono E (le_of_lt hc'))

/-- `c ↦ F(c)` is upper semicontinuous. -/
lemma upperSemicontinuous_F (E : Env A Ω) : UpperSemicontinuous E.F := by
  intro c y hy
  have h := E.F_add_Ioi c
  obtain ⟨c₁, hc₁, hy₁⟩ := E.exists_lt_Ioi (c := c) (y := 1 - y) (by linarith)
  filter_upwards [Iio_mem_nhds hc₁] with c' hc'
  have h2 := E.F_mono (le_of_lt hc')
  have h3 := E.F_add_Ioi c₁
  linarith

lemma measurable_F (E : Env A Ω) : Measurable E.F := (F_mono E).measurable

lemma measurable_Fm (E : Env A Ω) : Measurable E.Fm := (Fm_mono E).measurable

/-- The mass of an atom. -/
lemma real_singleton (E : Env A Ω) (c : ℝ) :
    (E.cost : Measure ℝ).real {c} = E.F c - E.Fm c := by
  have hdisj : Disjoint (Iio c) {c} := by
    rw [Set.disjoint_left]
    intro y hy hy'
    rw [mem_singleton_iff] at hy'
    rw [hy'] at hy
    exact lt_irrefl _ (mem_Iio.1 hy)
  have h := measureReal_union (μ := (E.cost : Measure ℝ)) hdisj (measurableSet_singleton c)
  rw [Iio_union_right] at h
  unfold F Fm
  linarith

/-- Given a measurable target probability `q` satisfying the consistency condition at the cutoff `c`,
the cutoff strategy with a mixing type at `c` induces `q`.  -/
theorem exists_cutoff_strategy (E : Env A Ω) {q c : Ω → ℝ} (hq : Measurable q) (hc : Measurable c)
    (hband : ∀ ω, E.Fm (c ω) ≤ q ω ∧ q ω ≤ E.F (c ω)) :
    ∃ s : Strat Ω, (∀ ω, E.rp s ω = q ω) ∧ (∀ ω x, x < c ω → s.σ ω x = 1) ∧
      (∀ ω x, c ω < x → s.σ ω x = 0) := by
  let α : Ω → ℝ := fun ω => (q ω - E.Fm (c ω)) / (E.F (c ω) - E.Fm (c ω))
  have hαm : Measurable α :=
    (hq.sub (E.measurable_Fm.comp hc)).div ((E.measurable_F.comp hc).sub (E.measurable_Fm.comp hc))
  have hα : ∀ ω, α ω ∈ Icc (0 : ℝ) 1 := by
    intro ω
    obtain ⟨h1, h2⟩ := hband ω
    constructor
    · exact div_nonneg (by linarith) (by linarith)
    · exact div_le_one_of_le₀ (by linarith) (by linarith)
  let σ : Ω → ℝ → ℝ := fun ω x => if x < c ω then 1 else if c ω < x then 0 else α ω
  have hm : Measurable (Function.uncurry σ) := by
    have h1 : MeasurableSet {z : Ω × ℝ | z.2 < c z.1} :=
      measurableSet_lt measurable_snd (hc.comp measurable_fst)
    have h2 : MeasurableSet {z : Ω × ℝ | c z.1 < z.2} :=
      measurableSet_lt (hc.comp measurable_fst) measurable_snd
    exact Measurable.ite h1 measurable_const
      (Measurable.ite h2 measurable_const (hαm.comp measurable_fst))
  let s : Strat Ω :=
    { σ := σ
      meas := hm
      mem := fun ω x => by
        simp only [σ]
        split_ifs
        · simp
        · simp
        · exact hα ω }
  refine ⟨s, fun ω => ?_, fun ω x hx => by simp [s, σ, hx],
    fun ω x hx => by simp [s, σ, hx, not_lt.2 hx.le]⟩
  have hdec : ∀ x, s.σ ω x = (Iio (c ω)).indicator (fun _ => (1 : ℝ)) x
      + ({c ω} : Set ℝ).indicator (fun _ => α ω) x := by
    intro x
    rcases lt_trichotomy x (c ω) with hx | hx | hx
    · rw [indicator_of_mem (mem_Iio.2 hx), indicator_of_notMem (by simpa using hx.ne)]
      simp [s, σ, hx]
    · rw [indicator_of_notMem (by simp [hx]), indicator_of_mem (by simp [hx])]
      simp [s, σ, hx]
    · rw [indicator_of_notMem (by simpa using hx.le), indicator_of_notMem (by simpa using hx.ne')]
      simp [s, σ, hx, not_lt.2 hx.le]
  unfold rp
  simp_rw [hdec]
  rw [integral_add ((integrable_const (1 : ℝ)).indicator measurableSet_Iio)
    ((integrable_const (α ω)).indicator (measurableSet_singleton _)),
    integral_indicator_const _ measurableSet_Iio,
    integral_indicator_const _ (measurableSet_singleton _), real_singleton]
  simp only [smul_eq_mul, mul_one]
  obtain ⟨h1, h2⟩ := hband ω
  by_cases hz : E.F (c ω) - E.Fm (c ω) = 0
  · have hq' : q ω = E.Fm (c ω) := by linarith
    rw [hq', hz]
    simp [Fm]
  · have : (E.F (c ω) - E.Fm (c ω)) * α ω = q ω - E.Fm (c ω) := by
      simp only [α]
      field_simp
    rw [this]
    simp [Fm]

/-- **Lemma `lemma_symmetric_equilibrium_exists`.** -/
theorem exists_equilibrium (E : Env A Ω) (n : ℕ) (d : Rule A) : ∃ s : Strat Ω, E.IsEq n d s := by
  let g : Ω × ℝ → ℝ := fun z => E.gross n d z.2 z.1
  have hg : Continuous g := E.continuous_gross n d
  let G : Set (Ω × ℝ) := {z | z.2 ∈ Icc (0 : ℝ) 1 ∧ E.Fm (g z) ≤ z.2}
  have hG : IsClosed G := by
    have h1 : IsClosed {z : Ω × ℝ | z.2 ∈ Icc (0 : ℝ) 1} := isClosed_Icc.preimage continuous_snd
    have hlsc : LowerSemicontinuous fun z => E.Fm (g z) := fun z y hy =>
      hg.continuousAt.eventually (E.lowerSemicontinuous_Fm (g z) y hy)
    have h2 : IsClosed {z : Ω × ℝ | E.Fm (g z) ≤ z.2} :=
      hlsc.isClosed_epigraph.preimage (continuous_id.prodMk continuous_snd)
    exact h1.inter h2
  have hne : ∀ ω, ∃ y, (ω, y) ∈ G := fun ω =>
    ⟨1, ⟨by simp, by exact measureReal_le_one⟩⟩
  obtain ⟨hqm, hqG⟩ := measurable_sInf_section hG (a := 0) (b := 1) (fun z hz => hz.1) hne
  set q : Ω → ℝ := fun ω => sInf {y | (ω, y) ∈ G} with hq
  let c : Ω → ℝ := fun ω => E.gross n d (q ω) ω
  have hcm : Measurable c := hg.measurable.comp (measurable_id.prodMk hqm)
  have hband : ∀ ω, E.Fm (c ω) ≤ q ω ∧ q ω ≤ E.F (c ω) := by
    intro ω
    obtain ⟨⟨hq01, hq2⟩, hqmin⟩ := hqG ω
    refine ⟨hq2, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨y', hy1, hy2⟩ := exists_between hcon
    -- usc of `F ∘ Δ_ω` at `q`
    have husc : ∀ᶠ y in 𝓝 (q ω), E.F (E.gross n d y ω) < y' := by
      have hcont : Continuous fun y => g (ω, y) := hg.comp (Continuous.prodMk continuous_const continuous_id)
      exact hcont.continuousAt.eventually (E.upperSemicontinuous_F _ y' hy1)
    have hF0 : 0 ≤ E.F (c ω) := E.F_nonneg _
    have hq0 : 0 ≤ y' := hF0.trans hy1.le
    have hlt : ∀ᶠ y in 𝓝[<] (q ω), y' < y := by
      filter_upwards [Ioo_mem_nhdsLT hy2] with y hy using hy.1
    have hlt2 : ∀ᶠ y in 𝓝[<] (q ω), y < q ω := eventually_mem_nhdsWithin
    obtain ⟨y, hy3, hy4, hy5⟩ := ((husc.filter_mono nhdsWithin_le_nhds).and (hlt.and hlt2)).exists
    -- `y ∉ G`, so `y < F(Δ⁻) ≤ F(Δ)`
    have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨hq0.trans hy4.le, hy5.le.trans hq01.2⟩
    have hnot : (ω, y) ∉ G := fun hmem => absurd (hqmin y hmem) (not_le.2 hy5)
    have hlt3 : y < E.Fm (g (ω, y)) := by
      by_contra h
      exact hnot ⟨hy01, not_lt.1 h⟩
    have := E.Fm_le_F (g (ω, y))
    have h' : E.F (g (ω, y)) < y' := hy3
    linarith
  obtain ⟨s, hrp, h1, h2⟩ := E.exists_cutoff_strategy hqm hcm hband
  refine ⟨s, fun ω x => ?_⟩
  rw [hrp ω]
  exact ⟨h1 ω x, h2 ω x⟩

end Env

end NoisyVD
