import ConformityConcerns.Shifted.Defs
import ConformityConcerns.PeriodGame.Revealing
import ConformityConcerns.Shifted.Construct

/-!
# Shifted preferences: the period game (claims (i)–(iii) at a fixed history)

Online appendix, section "Shifted Preferences":

> One can see from Equation (eq_def_s) that the sensitivity is independent of `μ(h^t)`, and
> thus would also be independent of `c`. Therefore, by Lemma 1, whether an equilibrium with
> revelation exists is independent of `c`. In the baseline model, the Social Optimality
> refinement always selects a revealing equilibrium when one exists. For sufficiently large
> `|c|`, this is no longer the case. If one instead selects the payoff-maximizing revealing
> equilibrium whenever one exists, the learning results are as before.

Linear equilibria with shift `c` (the proof of Lemma 1 with `μ(h^t) + c` as target):

* revealing: `α` solves `(1 + κα²) s̃ = α` and `a_t = E Z + (Z - E Z)/(1 + κα²) + κ α c`;
  ex-ante loss `(κα²/(1+κα²))² Var Z + (κ α c)² + κ (Var v + c²)`;
* pooling on `p`: ex-ante loss `(p - E Z)² + Var Z + κ (Var v + c²)`.

The conformity part `κ (Var v + c²)` is the same in all linear equilibria, so Social
Optimality compares adaptation losses, and the revealing rule now carries the level
distortion `κ α c`. With `λ = 1/(1 + κα²)` for the root of smallest magnitude, revealing beats
pooling iff `κ² s̃² c² < λ³ (2 - λ) Var Z`.
-/

namespace CC.Shifted

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open CC.LG

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Revealing beats pooling iff `κ² s² c² < λ³ (2 - λ) V`. -/
lemma revL_lt_iff {κ s c V l : ℝ} (hl : 0 < l) :
    (1 - l) ^ 2 * V + (κ * s * c / l) ^ 2 < V ↔ κ ^ 2 * s ^ 2 * c ^ 2 < l ^ 3 * (2 - l) * V := by
  have hl2 : 0 < l ^ 2 := by positivity
  have e : ((1 - l) ^ 2 * V + (κ * s * c / l) ^ 2) * l ^ 2 =
      (1 - l) ^ 2 * V * l ^ 2 + κ ^ 2 * s ^ 2 * c ^ 2 := by
    field_simp
  have id : V * l ^ 2 - (1 - l) ^ 2 * V * l ^ 2 = l ^ 3 * (2 - l) * V := by ring
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h hl2
    rw [e] at this
    linarith
  · intro h
    refine lt_of_mul_lt_mul_right (a := l ^ 2) ?_ hl2.le
    rw [e]
    linarith

/-- Pooling beats revealing iff `λ³ (2 - λ) V < κ² s² c²`. -/
lemma lt_revL_iff {κ s c V l : ℝ} (hl : 0 < l) :
    V < (1 - l) ^ 2 * V + (κ * s * c / l) ^ 2 ↔ l ^ 3 * (2 - l) * V < κ ^ 2 * s ^ 2 * c ^ 2 := by
  have hl2 : 0 < l ^ 2 := by positivity
  have e : ((1 - l) ^ 2 * V + (κ * s * c / l) ^ 2) * l ^ 2 =
      (1 - l) ^ 2 * V * l ^ 2 + κ ^ 2 * s ^ 2 * c ^ 2 := by
    field_simp
  have id : V * l ^ 2 - (1 - l) ^ 2 * V * l ^ 2 = l ^ 3 * (2 - l) * V := by ring
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h hl2
    rw [e] at this
    linarith
  · intro h
    refine lt_of_mul_lt_mul_right (a := l ^ 2) ?_ hl2.le
    rw [e]
    linarith

/-! ### The baseline is the case `c = 0` -/

/-- With `c = 0` the shifted game is the baseline game. -/
theorem shifted_zero (G : Game Ω) :
    (∀ (φ : Kernel ℝ ℝ) (ω : Ω) (x : ℝ), G.shLoss 0 φ ω x = G.loss φ ω x) ∧
    (∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShLinearEq 0 a φ ↔ G.IsLinearEq a φ) ∧
    (∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.shExLoss 0 a φ = G.exLoss a φ) ∧
    (∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShSignalingEq 0 a φ ↔ G.IsSignalingEq a φ) := by
  have hl : ∀ (φ : Kernel ℝ ℝ) (ω : Ω) (x : ℝ), G.shLoss 0 φ ω x = G.loss φ ω x := by
    intro φ ω x
    simp only [Game.shLoss, Game.loss, Game.shConfLoss, Game.confLoss, sub_zero]
  have hp : ∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShPBE 0 a φ ↔ G.IsPBE a φ := by
    intro a φ
    constructor
    · intro h
      exact ⟨h.meas, h.markov, fun ω x => by rw [← hl, ← hl]; exact h.optimal ω x, h.bayes⟩
    · intro h
      exact ⟨h.meas, h.markov, fun ω x => by rw [hl, hl]; exact h.optimal ω x, h.bayes⟩
  have hlin : ∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShLinearEq 0 a φ ↔ G.IsLinearEq a φ :=
    fun a φ => by unfold Game.IsShLinearEq Game.IsLinearEq; rw [hp]
  have hex : ∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.shExLoss 0 a φ = G.exLoss a φ :=
    fun a φ => by unfold Game.shExLoss Game.exLoss; simp only [hl]
  refine ⟨hl, hlin, hex, fun a φ => ?_⟩
  unfold Game.IsShSignalingEq Game.IsSignalingEq
  simp only [hlin, hex]

/-! ### Linear equilibria with shift `c` -/

/-- **Lemma 3 with shift `c`** (`s̃ ≠ 0`): every linear equilibrium is pooling or revealing. -/
theorem lemma3_sh (G : Game Ω) (hG : G.Std) (c : ℝ) (hs : G.sens ≠ 0) {a : Ω → ℝ}
    {φ : Kernel ℝ ℝ} (hE : G.IsShLinearEq c a φ) : G.IsPooling a ∨ G.IsRevealing a := by
  exact hG.sh_lemma3_ne c hs hE

/-- **Revealing linear equilibria with shift `c`** (proof of Lemma 1 with the shift). In every
revealing linear equilibrium the slope `α` of the public's posterior mean solves the same
slope equation `(1 + κα²) s̃ = α` as in the baseline, the action is
`a_t = E Z + (Z - E Z)/(1 + κα²) + κ α c`, and the ex-ante loss is
`(κα²/(1 + κα²))² Var Z + (κ α c)² + κ (Var v + c²)`. -/
theorem revealing_char_sh (G : Game Ω) (hG : G.Std) (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsShLinearEq c a φ) (hR : G.IsRevealing a) :
    ∃ α : ℝ, (1 + G.κ * α ^ 2) * G.sens = α ∧
      a =ᵐ[G.P] (fun ω => G.meanZ + (G.Z ω - G.meanZ) / (1 + G.κ * α ^ 2) + G.κ * α * c) ∧
      G.shExLoss c a φ = ENNReal.ofReal
        ((G.κ * α ^ 2 / (1 + G.κ * α ^ 2)) ^ 2 * variance G.Z G.P + (G.κ * α * c) ^ 2 +
          G.κ * (variance G.v G.P + c ^ 2)) := by
  obtain ⟨α, hα, ha⟩ := hG.sh_rev_char c hE hR
  refine ⟨α, hα, ha, ?_⟩
  have hD : 0 < 1 + G.κ * α ^ 2 := by have := hG.κ_pos; positivity
  have ha' : a =ᵐ[G.P] fun ω =>
      G.meanZ + (1 / (1 + G.κ * α ^ 2)) * (G.Z ω - G.meanZ) + G.κ * α * c := by
    filter_upwards [ha] with ω hω
    rw [hω]
    ring
  rw [hG.sh_exLoss_affine c hE.1 ha']
  congr 1
  field_simp
  ring

/-- Conversely, every root `α` of the slope equation gives a revealing linear equilibrium with
shift `c`, `a_t = E Z + (Z - E Z)/(1 + κα²) + κ α c`. -/
theorem revealing_exists_sh (G : Game Ω) (hG : G.Std) (c : ℝ) {α : ℝ}
    (hα : (1 + G.κ * α ^ 2) * G.sens = α) :
    ∃ φ : Kernel ℝ ℝ, G.IsShLinearEq c
      (fun ω => G.meanZ + (G.Z ω - G.meanZ) / (1 + G.κ * α ^ 2) + G.κ * α * c) φ := by
  exact ⟨_, hG.sh_rev_isLinearEq c hα⟩

/-- Pooling on any `p` is a linear equilibrium with shift `c`, and pooling on `p` has ex-ante
loss `(p - E Z)² + Var Z + κ (Var v + c²)`. -/
theorem pooling_sh (G : Game Ω) (hG : G.Std) (c p : ℝ) :
    (∃ φ : Kernel ℝ ℝ, G.IsShLinearEq c (fun _ => p) φ) ∧
    ∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShLinearEq c a φ → (a =ᵐ[G.P] fun _ => p) →
      G.shExLoss c a φ = ENNReal.ofReal
        ((p - G.meanZ) ^ 2 + variance G.Z G.P + G.κ * (variance G.v G.P + c ^ 2)) := by
  exact ⟨⟨_, hG.sh_pool_isLinearEq c p⟩, fun a φ hE ha => hG.sh_exLoss_pool c p hE.1 ha⟩

/-! ### (i) Whether an equilibrium with revelation exists does not depend on `c` -/

/-- **Lemma 1 with shift `c`.** A revealing linear equilibrium exists iff some `α` solves
`(1 + κα²) s̃ = α`, with the baseline sensitivity `s̃` (which does not involve `c`). -/
theorem lemma1_sh (G : Game Ω) (hG : G.Std) (c : ℝ) :
    G.HasShRevealingEq c ↔ ∃ α : ℝ, (1 + G.κ * α ^ 2) * G.sens = α := by
  constructor
  · rintro ⟨a, φ, hE, hR⟩
    obtain ⟨α, hα, -⟩ := hG.sh_rev_char c hE hR
    exact ⟨α, hα⟩
  · rintro ⟨α, hα⟩
    refine ⟨_, _, hG.sh_rev_isLinearEq c hα, ?_⟩
    have hD : 0 < 1 + G.κ * α ^ 2 := by have := hG.κ_pos; positivity
    refine ⟨1 / (1 + G.κ * α ^ 2), G.meanZ - G.meanZ / (1 + G.κ * α ^ 2) + G.κ * α * c,
      by positivity, ae_of_all _ fun ω => ?_⟩
    field_simp
    ring

/-- **Corollary 1 with shift `c`.** A revealing linear equilibrium exists iff
`|s̃| ≤ √(κck/κ)`. -/
theorem corollary1_sh (G : Game Ω) (hG : G.Std) (c : ℝ) :
    G.HasShRevealingEq c ↔ |G.sens| ≤ √(κck / G.κ) := by
  rw [lemma1_sh G hG c]
  exact slope_root_iff _ _ hG.κ_pos

/-- **(i)** Whether an equilibrium with revelation exists is independent of `c`; it exists iff
the baseline signaling equilibrium is revealing. -/
theorem revelation_indep_c (G : Game Ω) (hG : G.Std) (c c' : ℝ) :
    (G.HasShRevealingEq c ↔ G.HasShRevealingEq c') ∧
    ∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsSignalingEq a φ →
      (G.HasShRevealingEq c ↔ G.IsRevealing a) := by
  refine ⟨by rw [lemma1_sh G hG c, lemma1_sh G hG c'], fun a φ hE => ?_⟩
  rw [lemma1_sh G hG c, ((lemma1 G hG).2 a φ hE).1]

/-! ### (ii) Social Optimality with shift `c` -/

/-- **(ii), baseline.** In the baseline model Social Optimality selects a revealing equilibrium
whenever a revealing linear equilibrium exists. -/
theorem baseline_selects_revealing (G : Game Ω) (hG : G.Std) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsSignalingEq a φ)
    (hex : ∃ (a' : Ω → ℝ) (φ' : Kernel ℝ ℝ), G.IsLinearEq a' φ' ∧ G.IsRevealing a') :
    G.IsRevealing a := by
  obtain ⟨a', φ', hE', hR'⟩ := hex
  have h0 : G.HasShRevealingEq 0 := ⟨a', φ', ((shifted_zero G).2.1 a' φ').2 hE', hR'⟩
  exact ((lemma1 G hG).2 a φ hE).1.2 ((lemma1_sh G hG 0).1 h0)

/-- A signaling equilibrium (Social Optimality) with shift `c` exists. -/
theorem signalingEq_exists_sh (G : Game Ω) (hG : G.Std) (c : ℝ) :
    ∃ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShSignalingEq c a φ := by
  obtain ⟨a, φ, hE, hloss⟩ := hG.sh_attained c
  exact ⟨a, φ, hE, fun a' φ' hE' => hloss ▸ hG.sh_lower_bound c hE'⟩

/-- **The signaling equilibrium with shift `c`, explicitly.** With `λ = (1 + √(1 - 4κs̃²))/2`:
if a revealing equilibrium exists and `κ² s̃² c² < λ³ (2 - λ) Var Z`, Social Optimality selects
the revealing rule `E Z + λ (Z - E Z) + κ (s̃/λ) c`; if no revealing equilibrium exists or
`κ² s̃² c² > λ³ (2 - λ) Var Z`, it selects pooling on `E Z`. The ex-ante loss is the smaller of
the two candidates' losses. -/
theorem signalingEq_char_sh (G : Game Ω) (hG : G.Std) (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsShSignalingEq c a φ) :
    (G.κ * G.sens ^ 2 ≤ κck →
      G.κ ^ 2 * G.sens ^ 2 * c ^ 2 < G.lam ^ 3 * (2 - G.lam) * variance G.Z G.P →
      a =ᵐ[G.P] fun ω => G.meanZ + G.lam * (G.Z ω - G.meanZ) + G.κ * (G.sens / G.lam) * c) ∧
    (κck < G.κ * G.sens ^ 2 ∨
        G.lam ^ 3 * (2 - G.lam) * variance G.Z G.P < G.κ ^ 2 * G.sens ^ 2 * c ^ 2 →
      a =ᵐ[G.P] fun _ => G.meanZ) ∧
    G.shExLoss c a φ = ENNReal.ofReal
      ((if G.κ * G.sens ^ 2 ≤ κck then
          min ((1 - G.lam) ^ 2 * variance G.Z G.P + (G.κ * G.sens * c / G.lam) ^ 2)
            (variance G.Z G.P)
        else variance G.Z G.P) + G.κ * (variance G.v G.P + c ^ 2)) := by
  have hV := hG.varZ_pos
  have hK := hG.shK_nonneg c
  have hloss : G.shExLoss c a φ =
      ENNReal.ofReal (G.shMin c + G.κ * (variance G.v G.P + c ^ 2)) := by
    obtain ⟨a₀, φ₀, hE₀, hl₀⟩ := hG.sh_attained c
    exact le_antisymm (hl₀ ▸ hE.2 a₀ φ₀ hE₀) (hG.sh_lower_bound c hE.1)
  have hrevL : 0 ≤ (1 - G.lam) ^ 2 * variance G.Z G.P + (G.κ * G.sens * c / G.lam) ^ 2 :=
    add_nonneg (mul_nonneg (sq_nonneg _) hV.le) (sq_nonneg _)
  have hmin0 : 0 ≤ G.shMin c := by
    unfold Game.shMin
    split_ifs
    · exact le_min hrevL hV.le
    · exact hV.le
  have hmV : G.shMin c ≤ variance G.Z G.P := by
    unfold Game.shMin
    split_ifs
    · exact min_le_right _ _
    · exact le_rfl
  have hlam1 : G.sens = 0 → G.lam = 1 := fun hs => by
    unfold Game.lam
    rw [hs]
    norm_num
  refine ⟨fun h4 hlt => ?_, fun hcase => ?_, hloss⟩
  · have hr : (1 - G.lam) ^ 2 * variance G.Z G.P + (G.κ * G.sens * c / G.lam) ^ 2 <
        variance G.Z G.P := (revL_lt_iff (lplus_pos _ _)).2 hlt
    have hm : G.shMin c =
        (1 - G.lam) ^ 2 * variance G.Z G.P + (G.κ * G.sens * c / G.lam) ^ 2 := by
      unfold Game.shMin
      rw [ite_eq_left h4, min_eq_left hr.le]
    by_cases hs : G.sens = 0
    · have hl1 := hlam1 hs
      rw [hm, hl1, hs] at hloss
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        mul_zero, zero_div, add_zero, zero_add] at hloss
      rw [hG.sh_exLoss_eq c hE.1.1, ENNReal.ofReal_mul hG.κ_pos.le] at hloss
      have hfin : ENNReal.ofReal G.κ * ENNReal.ofReal (variance G.v G.P + c ^ 2) ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      have h0 : ∫⁻ ω, ENNReal.ofReal ((a ω - G.Z ω) ^ 2) ∂G.P = 0 := by
        have := hloss.trans (zero_add _).symm
        exact (ENNReal.add_left_inj hfin).1 this
      rw [lintegral_eq_zero_iff' (by exact (ENNReal.measurable_ofReal.comp_aemeasurable
        ((hE.1.1.meas.aemeasurable.sub hG.aemZ).pow_const 2)))] at h0
      filter_upwards [h0] with ω hω
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω
      have : (a ω - G.Z ω) ^ 2 = 0 := le_antisymm hω (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      rw [hl1, hs]
      simp only [one_mul, zero_div, mul_zero, zero_mul, add_zero]
      linarith
    rcases hG.sh_lemma3_ne c hs hE.1 with ⟨p, hp⟩ | hR
    · exfalso
      rw [hG.sh_exLoss_pool c p hE.1.1 hp, hm,
        ENNReal.ofReal_eq_ofReal_iff (by positivity) (add_nonneg hrevL hK)] at hloss
      nlinarith [sq_nonneg (p - G.meanZ)]
    · obtain ⟨l, hl0, hl, ha, hl'⟩ := hG.sh_rev_loss c hE.1 hR
      rw [hl', hm, ENNReal.ofReal_eq_ofReal_iff (by positivity) (add_nonneg hrevL hK)] at hloss
      have hleq := (rev_cmp (c := c) hV hl0 hl).2 (by rw [← Game.lam_eq]; linarith)
      rw [hleq, ← Game.lam_eq] at ha
      exact ha
  · have hs : G.sens ≠ 0 := by
      intro hs
      rcases hcase with h | h
      · rw [hs] at h
        norm_num at h
        linarith [κck_pos]
      · rw [hlam1 hs, hs] at h
        norm_num at h
        linarith
    rcases hG.sh_lemma3_ne c hs hE.1 with ⟨p, hp⟩ | hR
    · rw [hG.sh_exLoss_pool c p hE.1.1 hp,
        ENNReal.ofReal_eq_ofReal_iff (by positivity) (add_nonneg hmin0 hK)] at hloss
      have : p = G.meanZ := by nlinarith [sq_nonneg (p - G.meanZ)]
      rw [← this]
      exact hp
    · exfalso
      obtain ⟨l, hl0, hl, ha, hl'⟩ := hG.sh_rev_loss c hE.1 hR
      have h4 : G.κ * G.sens ^ 2 ≤ κck :=
        le_kck_iff_four.2 ((slope_root_iff_four _ _).1 (root_of_slope hl0 hl))
      have hlt : G.lam ^ 3 * (2 - G.lam) * variance G.Z G.P <
          G.κ ^ 2 * G.sens ^ 2 * c ^ 2 := by
        rcases hcase with h | h
        · exact absurd h4 (not_le.2 h)
        · exact h
      have hr : variance G.Z G.P <
          (1 - G.lam) ^ 2 * variance G.Z G.P + (G.κ * G.sens * c / G.lam) ^ 2 :=
        (lt_revL_iff (lplus_pos _ _)).2 hlt
      have hm : G.shMin c = variance G.Z G.P := by
        unfold Game.shMin
        rw [ite_eq_left h4, min_eq_right hr.le]
      rw [hl', hm, ENNReal.ofReal_eq_ofReal_iff (by positivity) (add_nonneg hV.le hK)] at hloss
      have := (rev_cmp (c := c) hV hl0 hl).1
      rw [← Game.lam_eq] at this
      linarith

/-- When `s̃ = 0` the revealing rule carries no distortion, and Social Optimality selects
`a_t = Z_t` for every `c`. -/
theorem signalingEq_sens_zero_sh (G : Game Ω) (hG : G.Std) (hs : G.sens = 0) (c : ℝ)
    {a : Ω → ℝ} {φ : Kernel ℝ ℝ} (hE : G.IsShSignalingEq c a φ) : a =ᵐ[G.P] G.Z := by
  have hl1 : G.lam = 1 := by
    unfold Game.lam
    rw [hs]
    norm_num
  have h := (signalingEq_char_sh G hG c hE).1 (by rw [hs]; norm_num; exact κck_pos.le)
    (by rw [hl1, hs]; norm_num; exact hG.varZ_pos)
  filter_upwards [h] with ω hω
  rw [hω, hl1, hs]
  ring

/-- **(ii) "For sufficiently large `|c|`, this is no longer the case."** At every history where
a revealing equilibrium exists and `s̃ ≠ 0`, the threshold
`c̄ = λ √(λ (2 - λ) Var Z)/(κ |s̃|)` is positive and, for every `c`, a revealing linear
equilibrium exists; Social Optimality selects a revealing equilibrium if `|c| < c̄` and a
pooling one if `|c| > c̄`. -/
theorem large_c_threshold (G : Game Ω) (hG : G.Std) (hrev : G.κ * G.sens ^ 2 ≤ κck)
    (hs : G.sens ≠ 0) :
    0 < G.cbar ∧ ∀ c : ℝ, G.HasShRevealingEq c ∧
      (|c| < G.cbar → ∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShSignalingEq c a φ →
        G.IsRevealing a) ∧
      (G.cbar < |c| → ∀ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShSignalingEq c a φ →
        G.IsPooling a) := by
  have hV := hG.varZ_pos
  have hκ := hG.κ_pos
  have hl0 : 0 < G.lam := lplus_pos _ _
  have hl1 : G.lam ≤ 1 := by
    unfold Game.lam
    have : √(1 - 4 * G.κ * G.sens ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith [mul_nonneg hκ.le (sq_nonneg G.sens)]
    linarith
  have hW : 0 < G.lam * (2 - G.lam) * variance G.Z G.P := by
    have : 0 < 2 - G.lam := by linarith
    positivity
  have hden : 0 < G.κ * |G.sens| := mul_pos hκ (abs_pos.2 hs)
  have hsq : √(G.lam * (2 - G.lam) * variance G.Z G.P) ^ 2 =
      G.lam * (2 - G.lam) * variance G.Z G.P := Real.sq_sqrt hW.le
  have hsqrt0 : 0 < √(G.lam * (2 - G.lam) * variance G.Z G.P) := Real.sqrt_pos.2 hW
  have key2 : ∀ c : ℝ, (G.κ * |G.sens| * |c|) ^ 2 = G.κ ^ 2 * G.sens ^ 2 * c ^ 2 := by
    intro c
    rw [mul_pow, mul_pow, sq_abs, sq_abs]
  have key3 : (G.lam * √(G.lam * (2 - G.lam) * variance G.Z G.P)) ^ 2 =
      G.lam ^ 3 * (2 - G.lam) * variance G.Z G.P := by
    rw [mul_pow, hsq]
    ring
  have hcbar : ∀ c : ℝ, (|c| < G.cbar ↔
      G.κ * |G.sens| * |c| < G.lam * √(G.lam * (2 - G.lam) * variance G.Z G.P)) ∧
      (G.cbar < |c| ↔
      G.lam * √(G.lam * (2 - G.lam) * variance G.Z G.P) < G.κ * |G.sens| * |c|) := by
    intro c
    unfold Game.cbar
    constructor
    · rw [lt_div_iff₀ hden, mul_comm]
    · rw [div_lt_iff₀ hden, mul_comm |c|]
  refine ⟨div_pos (mul_pos hl0 hsqrt0) hden, fun c => ⟨?_, fun hc a φ hE => ?_, fun hc a φ hE => ?_⟩⟩
  · rw [corollary1_sh G hG c, abs_le_sqrt_iff_four hκ]
    exact le_kck_iff_four.1 hrev
  · have h1 := (hcbar c).1.1 hc
    have h2 : G.κ ^ 2 * G.sens ^ 2 * c ^ 2 < G.lam ^ 3 * (2 - G.lam) * variance G.Z G.P := by
      rw [← key2 c, ← key3]
      exact pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    have ha := (signalingEq_char_sh G hG c hE).1 hrev h2
    exact ⟨G.lam, (1 - G.lam) * G.meanZ + G.κ * (G.sens / G.lam) * c, hl0,
      ha.mono fun ω hω => by rw [hω]; ring⟩
  · have h1 := (hcbar c).2.1 hc
    have h2 : G.lam ^ 3 * (2 - G.lam) * variance G.Z G.P < G.κ ^ 2 * G.sens ^ 2 * c ^ 2 := by
      rw [← key2 c, ← key3]
      exact pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    exact ⟨_, (signalingEq_char_sh G hG c hE).2.1 (Or.inr h2)⟩

/-! ### (iii) The alternative selection -/

/-- An equilibrium under the alternative selection exists. -/
theorem altEq_exists (G : Game Ω) (hG : G.Std) (c : ℝ) :
    ∃ (a : Ω → ℝ) (φ : Kernel ℝ ℝ), G.IsShAltEq c a φ := by
  have hV := hG.varZ_pos
  by_cases h4 : G.κ * G.sens ^ 2 ≤ κck
  · obtain ⟨φ, hE, hloss⟩ := hG.sh_rev_lam c h4
    have hR : G.IsRevealing
        (fun ω => G.meanZ + G.lam * (G.Z ω - G.meanZ) + G.κ * (G.sens / G.lam) * c) :=
      ⟨G.lam, (1 - G.lam) * G.meanZ + G.κ * (G.sens / G.lam) * c, lplus_pos _ _,
        ae_of_all _ fun ω => by ring⟩
    refine ⟨_, φ, hE, fun _ => ⟨hR, fun a' φ' hE' hR' => ?_⟩,
      fun hno => absurd ⟨_, φ, hE, hR⟩ hno⟩
    obtain ⟨l, hl0, hl, -, hl'⟩ := hG.sh_rev_loss c hE' hR'
    rw [hloss, hl']
    apply ENNReal.ofReal_le_ofReal
    have := (rev_cmp (c := c) hV hl0 hl).1
    rw [← Game.lam_eq] at this
    linarith
  · obtain ⟨hE, hloss⟩ := hG.sh_pool_meanZ c
    have hno : ¬ G.HasShRevealingEq c := by
      rw [corollary1_sh G hG c, abs_le_sqrt_iff_four hG.κ_pos, ← le_kck_iff_four]
      exact h4
    refine ⟨_, _, hE, fun h => absurd h hno, fun _ a' φ' hE' => ?_⟩
    rw [hloss]
    have := hG.sh_lower_bound c hE'
    unfold Game.shMin at this
    rw [ite_eq_right h4] at this
    exact this

/-- **The alternative selection, explicitly.** If a revealing equilibrium exists, the selected
rule is `E Z + λ (Z - E Z) + κ (s̃/λ) c`; otherwise it is pooling on `E Z`. -/
theorem altEq_char (G : Game Ω) (hG : G.Std) (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsShAltEq c a φ) :
    (G.κ * G.sens ^ 2 ≤ κck →
      a =ᵐ[G.P] fun ω => G.meanZ + G.lam * (G.Z ω - G.meanZ) + G.κ * (G.sens / G.lam) * c) ∧
    (κck < G.κ * G.sens ^ 2 → a =ᵐ[G.P] fun _ => G.meanZ) := by
  have hV := hG.varZ_pos
  have hK := hG.shK_nonneg c
  refine ⟨fun h4 => ?_, fun h4 => ?_⟩
  · have hHas : G.HasShRevealingEq c :=
      (corollary1_sh G hG c).2 ((abs_le_sqrt_iff_four hG.κ_pos).2 (le_kck_iff_four.1 h4))
    obtain ⟨hR, hmin⟩ := hE.2.1 hHas
    obtain ⟨φ₀, hE₀, hloss₀⟩ := hG.sh_rev_lam c h4
    have hle := hmin _ φ₀ hE₀ ⟨G.lam, (1 - G.lam) * G.meanZ + G.κ * (G.sens / G.lam) * c,
      lplus_pos _ _, ae_of_all _ fun ω => by ring⟩
    obtain ⟨l, hl0, hl, ha, hl'⟩ := hG.sh_rev_loss c hE.1 hR
    rw [hl', hloss₀, ENNReal.ofReal_le_ofReal_iff (add_nonneg (add_nonneg
      (mul_nonneg (sq_nonneg _) hV.le) (sq_nonneg _)) hK)] at hle
    have hleq := (rev_cmp (c := c) hV hl0 hl).2 (by rw [← Game.lam_eq]; linarith)
    rw [hleq, ← Game.lam_eq] at ha
    exact ha
  · have hno : ¬ G.HasShRevealingEq c := by
      rw [corollary1_sh G hG c, abs_le_sqrt_iff_four hG.κ_pos, ← le_kck_iff_four]
      exact not_le.2 h4
    have hmin := hE.2.2 hno
    have hs : G.sens ≠ 0 := by
      intro hs
      rw [hs] at h4
      norm_num at h4
      linarith [κck_pos]
    rcases hG.sh_lemma3_ne c hs hE.1 with ⟨p, hp⟩ | hR
    · obtain ⟨hE₀, hloss₀⟩ := hG.sh_pool_meanZ c
      have hle := hmin _ _ hE₀
      rw [hG.sh_exLoss_pool c p hE.1.1 hp, hloss₀,
        ENNReal.ofReal_le_ofReal_iff (add_nonneg hV.le hK)] at hle
      have : p = G.meanZ := by nlinarith [sq_nonneg (p - G.meanZ)]
      rw [← this]
      exact hp
    · exact absurd ⟨a, φ, hE.1, hR⟩ hno

/-- **(iii), period game.** Under the alternative selection the period is revealing iff
`|s̃| ≤ √(κck/κ)` (Corollary 1's criterion, for every `c`), iff the baseline signaling
equilibrium is revealing; and the selected action differs from the baseline signaling
equilibrium's action by a constant, so it reveals the same information. -/
theorem altEq_revealing_iff (G : Game Ω) (hG : G.Std) (c : ℝ) {a : Ω → ℝ} {φ : Kernel ℝ ℝ}
    (hE : G.IsShAltEq c a φ) :
    (G.IsRevealing a ↔ |G.sens| ≤ √(κck / G.κ)) ∧
    ∀ (a' : Ω → ℝ) (φ' : Kernel ℝ ℝ), G.IsSignalingEq a' φ' →
      (G.IsRevealing a ↔ G.IsRevealing a') ∧ ∃ d : ℝ, a =ᵐ[G.P] fun ω => a' ω + d := by
  have hiff : G.κ * G.sens ^ 2 ≤ κck ↔ |G.sens| ≤ √(κck / G.κ) := by
    rw [abs_le_sqrt_iff_four hG.κ_pos, le_kck_iff_four]
  obtain ⟨h1, h2⟩ := altEq_char G hG c hE
  have hrev : G.IsRevealing a ↔ G.κ * G.sens ^ 2 ≤ κck := by
    constructor
    · intro hR
      by_contra h
      exact Game.not_revealing_and_pooling hG hR ⟨_, h2 (not_le.1 h)⟩
    · intro h
      exact ⟨G.lam, (1 - G.lam) * G.meanZ + G.κ * (G.sens / G.lam) * c, lplus_pos _ _,
        (h1 h).mono fun ω hω => by rw [hω]; ring⟩
  refine ⟨hrev.trans hiff, fun a' φ' hE' => ⟨?_, ?_⟩⟩
  · rw [hrev, hiff, corollary1 G hG hE']
  · obtain ⟨b1, b2, -⟩ := signalingEq_char G hG hE'
    by_cases h : G.κ * G.sens ^ 2 ≤ κck
    · refine ⟨G.κ * (G.sens / G.lam) * c, ?_⟩
      filter_upwards [h1 h, b1 h] with ω hω hω'
      rw [hω, hω']
      rfl
    · refine ⟨0, ?_⟩
      filter_upwards [h2 (not_le.1 h), b2 (not_le.1 h)] with ω hω hω'
      rw [hω, hω', add_zero]

end CC.Shifted
