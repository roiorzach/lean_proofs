import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Elementary real inequalities and limit lemmas for the Claim of Proposition A5

* `gfun x = |x| · min(|x|, 1)`, with `|x| ≤ 1/(n+1) + (n+1) g(x)` and
  `min(|x|,1) ≤ 1/(n+1) + (n+1) g(x)`.
* For a monotone `f` whose increments on `[-R-1, R+1]` are at least `c` times the length,
  `c · g(y - m) ≤ (y - m)(f y - f m)` whenever `|m| ≤ R`.
* A mean value bound for `arctan`.
* The pointwise limit argument used at the end of the proof of the Claim.
-/

namespace CC.LearnTheta.ClaimAux

open Filter Topology

/-- `g(x) = |x| min(|x|, 1)`. -/
noncomputable def gfun (x : ℝ) : ℝ := |x| * min |x| 1

lemma gfun_nonneg (x : ℝ) : 0 ≤ gfun x :=
  mul_nonneg (abs_nonneg _) (le_min (abs_nonneg _) zero_le_one)

lemma gfun_le_abs (x : ℝ) : gfun x ≤ |x| :=
  mul_le_of_le_one_right (abs_nonneg x) (min_le_right _ _)

lemma continuous_gfun : Continuous gfun := by
  unfold gfun
  exact continuous_abs.mul (continuous_abs.min continuous_const)

lemma min_le_gfun (x : ℝ) (n : ℕ) : min |x| 1 ≤ 1 / ((n : ℝ) + 1) + ((n : ℝ) + 1) * gfun x := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  set u := min |x| 1 with hu
  have hu0 : 0 ≤ u := le_min (abs_nonneg _) zero_le_one
  have hux : u ≤ |x| := min_le_left _ _
  have hg : u * u ≤ gfun x := mul_le_mul_of_nonneg_right hux hu0
  have hpos : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  by_cases h : u ≤ 1 / ((n : ℝ) + 1)
  · have : 0 ≤ ((n : ℝ) + 1) * gfun x := mul_nonneg hn.le (gfun_nonneg x)
    linarith
  · rw [not_le] at h
    have h1 : 1 < ((n : ℝ) + 1) * u := by
      rw [div_lt_iff₀ hn] at h
      linarith
    have h2 : u ≤ ((n : ℝ) + 1) * (u * u) := by nlinarith
    have h3 : ((n : ℝ) + 1) * (u * u) ≤ ((n : ℝ) + 1) * gfun x :=
      mul_le_mul_of_nonneg_left hg hn.le
    linarith

lemma abs_le_gfun (x : ℝ) (n : ℕ) : |x| ≤ 1 / ((n : ℝ) + 1) + ((n : ℝ) + 1) * gfun x := by
  by_cases h : |x| ≤ 1
  · have e : min |x| 1 = |x| := min_eq_left h
    have := min_le_gfun x n
    rwa [e] at this
  · rw [not_le] at h
    have e : gfun x = |x| := by unfold gfun; rw [min_eq_right h.le, mul_one]
    rw [e]
    have hn : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have : |x| ≤ ((n : ℝ) + 1) * |x| := le_mul_of_one_le_left (abs_nonneg _) hn
    have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- `min(|θ - b|, 1) ≤ 1/(n+1) + (n+1) g(θ - a) + |b - a|`. -/
lemma min_abs_sub_le (θ a b : ℝ) (n : ℕ) :
    min |θ - b| 1 ≤ 1 / ((n : ℝ) + 1) + ((n : ℝ) + 1) * gfun (θ - a) + |b - a| := by
  have h1 : min |θ - b| 1 ≤ min |θ - a| 1 + |b - a| := by
    have : |θ - b| ≤ |θ - a| + |b - a| := by
      calc |θ - b| = |(θ - a) - (b - a)| := by ring_nf
        _ ≤ |θ - a| + |b - a| := abs_sub _ _
    rcases le_total |θ - a| 1 with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans this
    · rw [min_eq_right h]
      have := abs_nonneg (b - a)
      exact (min_le_right _ _).trans (by linarith)
  have h2 := min_le_gfun (θ - a) n
  linarith

/-- Monotone functions with a uniform lower bound on increments. -/
lemma mul_sub_ge_gfun {f : ℝ → ℝ} (hf : Monotone f) {c R m : ℝ}
    (hinc : ∀ a b, a ≤ b → |a| ≤ R + 1 → |b| ≤ R + 1 → c * (b - a) ≤ f b - f a)
    (hm : |m| ≤ R) (y : ℝ) : c * gfun (y - m) ≤ (y - m) * (f y - f m) := by
  have hmR : |m| ≤ R + 1 := by linarith
  obtain ⟨hm1, hm2⟩ := abs_le.1 hm
  rcases le_total m y with hmy | hym
  · set z := min y (m + 1) with hz
    have hz1 : m ≤ z := le_min hmy (by linarith)
    have hz2 : z ≤ m + 1 := min_le_right _ _
    have hzy : z ≤ y := min_le_left _ _
    have habs : |y - m| = y - m := abs_of_nonneg (by linarith)
    have hmin : min |y - m| 1 = z - m := by
      rw [habs, hz]
      rcases le_total y (m + 1) with h | h
      · rw [min_eq_left h, min_eq_left (by linarith)]
      · rw [min_eq_right h, min_eq_right (by linarith)]; ring
    have hzR : |z| ≤ R + 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have h1 := hinc m z hz1 hmR hzR
    have h2 : f z ≤ f y := hf hzy
    unfold gfun
    rw [hmin, habs]
    have : 0 ≤ y - m := by linarith
    calc c * ((y - m) * (z - m)) = (y - m) * (c * (z - m)) := by ring
      _ ≤ (y - m) * (f y - f m) := mul_le_mul_of_nonneg_left (by linarith) this
  · set z := max y (m - 1) with hz
    have hz1 : z ≤ m := max_le hym (by linarith)
    have hz2 : m - 1 ≤ z := le_max_right _ _
    have hzy : y ≤ z := le_max_left _ _
    have habs : |y - m| = m - y := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    have hmin : min |y - m| 1 = m - z := by
      rw [habs, hz]
      rcases le_total y (m - 1) with h | h
      · rw [max_eq_right h, min_eq_right (by linarith)]; ring
      · rw [max_eq_left h, min_eq_left (by linarith)]
    have hzR : |z| ≤ R + 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have h1 := hinc z m hz1 hzR hmR
    have h2 : f y ≤ f z := hf hzy
    unfold gfun
    rw [hmin, habs]
    have : 0 ≤ m - y := by linarith
    calc c * ((m - y) * (m - z)) = (m - y) * (c * (m - z)) := by ring
      _ ≤ (m - y) * (f m - f y) := mul_le_mul_of_nonneg_left (by linarith) this
      _ = (y - m) * (f y - f m) := by ring

/-- Mean value bound for `arctan`. -/
lemma arctan_sub_ge {a b M : ℝ} (hab : a ≤ b) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    (b - a) / (1 + M ^ 2) ≤ Real.arctan b - Real.arctan a := by
  have hD : Convex ℝ (Set.Icc (-M) M) := convex_Icc _ _
  have key := hD.mul_sub_le_image_sub_of_le_deriv (f := Real.arctan)
    Real.continuous_arctan.continuousOn Real.differentiable_arctan.differentiableOn
    (C := 1 / (1 + M ^ 2)) ?_ a (abs_le.1 ha) b (abs_le.1 hb) hab
  · calc (b - a) / (1 + M ^ 2) = 1 / (1 + M ^ 2) * (b - a) := by ring
      _ ≤ _ := key
  · intro x hx
    rw [interior_Icc] at hx
    rw [Real.deriv_arctan]
    apply one_div_le_one_div_of_le (by positivity)
    have : x ^ 2 ≤ M ^ 2 := by
      have h1 : |x| ≤ |M| := by
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2, le_abs_self M, neg_abs_le M]
      exact sq_le_sq.2 h1
    linarith

/-- If `0 ≤ x` and `x ≤ K/(n+1) + C n · y` for every `n` with `y → 0`, then `x → 0`. -/
lemma tendsto_zero_of_le_inv {ι : Type*} {F : Filter ι} {x y : ι → ℝ}
    (hx0 : ∀ᶠ t in F, 0 ≤ x t) (hy : Tendsto y F (𝓝 0)) (K : ℝ) (C : ℕ → ℝ)
    (hle : ∀ n : ℕ, ∀ᶠ t in F, x t ≤ K / ((n : ℝ) + 1) + C n * y t) :
    Tendsto x F (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => hx0.mono fun t ht => lt_of_lt_of_le ha ht, fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * |K| / a)
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hK : K / ((n : ℝ) + 1) < a / 2 := by
    have h1 : K / ((n : ℝ) + 1) ≤ |K| / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_right (le_abs_self K) hn1.le
    have h2 : |K| / ((n : ℝ) + 1) < a / 2 := by
      rw [div_lt_iff₀ hn1]
      rw [div_lt_iff₀ ha] at hn
      nlinarith [abs_nonneg K]
    linarith
  have hC : ∀ᶠ t in F, C n * y t < a / 2 := by
    have h := hy.const_mul (C n)
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hle n, hC] with t h1 h2
  linarith

/-- The pointwise argument at the end of the proof of the Claim. -/
lemma final_pointwise {Rev : ℕ → Prop} (hfreq : ∃ᶠ t in atTop, Rev t)
    {J M N L W D : ℕ → ℝ} {Winf K c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (hJ : ∀ t, Rev t → J t ≤ D t)
    (hM : ∀ t, c * M t ≤ J t) (hM0 : ∀ t, 0 ≤ M t)
    (hN : ∀ t (n : ℕ), N t ≤ K / ((n : ℝ) + 1) + K * ((n : ℝ) + 1) * M t)
    (hL : ∀ t, c' * L t ≤ N t) (hL0 : ∀ t, 0 ≤ L t)
    (hW : ∀ t (n : ℕ), W t ≤ 1 / ((n : ℝ) + 1) + ((n : ℝ) + 1) * L t + D t) (hW0 : ∀ t, 0 ≤ W t)
    (hD : Tendsto D atTop (𝓝 0)) (hD0 : ∀ t, 0 ≤ D t)
    (hWlim : Tendsto W atTop (𝓝 Winf)) : Winf = 0 := by
  set F := atTop ⊓ 𝓟 {t | Rev t} with hF
  have : F.NeBot := frequently_iff_neBot.1 hfreq
  have hFle : F ≤ atTop := inf_le_left
  have hRevF : ∀ᶠ t in F, Rev t := mem_inf_of_right (mem_principal_self _)
  have hDF : Tendsto D F (𝓝 0) := hD.mono_left hFle
  -- `M → 0` along `F`
  have hMF : Tendsto M F (𝓝 0) := by
    have hup : Tendsto (fun t => D t / c) F (𝓝 0) := by
      have := hDF.div_const c
      rwa [zero_div] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall hM0) ?_
    filter_upwards [hRevF] with t ht
    rw [le_div_iff₀ hc, mul_comm]
    exact (hM t).trans (hJ t ht)
  -- `L → 0` along `F`
  have hLF : Tendsto L F (𝓝 0) := by
    refine tendsto_zero_of_le_inv (Eventually.of_forall hL0) hMF (K / c')
      (fun n => K * ((n : ℝ) + 1) / c') (fun n => Eventually.of_forall fun t => ?_)
    have h1 := (hL t).trans (hN t n)
    rw [mul_comm, ← le_div_iff₀ hc'] at h1
    calc L t ≤ (K / ((n : ℝ) + 1) + K * ((n : ℝ) + 1) * M t) / c' := h1
      _ = K / c' / ((n : ℝ) + 1) + K * ((n : ℝ) + 1) / c' * M t := by ring
  -- `W → 0` along `F`
  have hWF : Tendsto W F (𝓝 0) := by
    have hy : Tendsto (fun t => L t + D t) F (𝓝 0) := by
      have := hLF.add hDF
      rwa [add_zero] at this
    refine tendsto_zero_of_le_inv (Eventually.of_forall hW0) hy 1 (fun n => (n : ℝ) + 1)
      (fun n => Eventually.of_forall fun t => ?_)
    have h1 := hW t n
    have h2 : D t ≤ ((n : ℝ) + 1) * D t := by
      have : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      exact le_mul_of_one_le_left (hD0 t) this
    calc W t ≤ 1 / ((n : ℝ) + 1) + ((n : ℝ) + 1) * L t + D t := h1
      _ ≤ 1 / ((n : ℝ) + 1) + ((n : ℝ) + 1) * (L t + D t) := by linarith
  exact tendsto_nhds_unique (hWlim.mono_left hFle) hWF

end CC.LearnTheta.ClaimAux
