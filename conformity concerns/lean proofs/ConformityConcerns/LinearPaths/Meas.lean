import ConformityConcerns.LinearPaths.Defs
import ConformityConcerns.Bridge.IndepTools

/-!
# Histories along a profile: measurability and structure

* `hist σ t` is measurable when the profile is;
* `hist σ (t+1) = extH (hist σ t) a_t γ_{t+1}`, and `restr` undoes `extH`;
* `hist σ t` depends only on `(θ, μ)`, the noises before `t` and the weights up to `t`:
  `hist σ t (trW t ω) = hist σ t ω`.
-/

namespace CC.LinearPaths

open MeasureTheory ProbabilityTheory
open CC.Bridge

variable {σ : Profile}

lemma measurable_priv (t : ℕ) : Measurable (priv t) :=
  measurable_fst.add ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd))

lemma measurable_snoc {α : Type*} [MeasurableSpace α] {n : ℕ} {f : α → Fin n → ℝ} {g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => (Fin.snoc (f x) (g x) : Fin (n + 1) → ℝ)) := by
  refine Measurable.of_eval fun i => ?_
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using hg
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp hf

lemma measurable_init {α : Type*} [MeasurableSpace α] {n : ℕ} {f : α → Fin (n + 1) → ℝ}
    (hf : Measurable f) : Measurable (fun x => (Fin.init (f x) : Fin n → ℝ)) :=
  Measurable.of_eval fun i => (measurable_pi_apply (Fin.castSucc i)).comp hf

lemma measurable_gams (t : ℕ) : Measurable (fun ω : Ωg => fun i : Fin (t + 1) => gam ω i) :=
  Measurable.of_eval fun i => measurable_gam_apply i

lemma measurable_acts (hσ : ∀ t, Measurable (Function.uncurry (σ t))) :
    ∀ t, Measurable (acts σ t)
  | 0 => by
    show Measurable (fun _ : Ωg => (Fin.elim0 : Fin 0 → ℝ))
    exact measurable_const
  | t + 1 => by
    have ih := measurable_acts hσ t
    have hh : Measurable (fun ω : Ωg => (((fun i : Fin (t + 1) => gam ω i), acts σ t ω) : Hist t)) :=
      (measurable_gams t).prodMk ih
    exact measurable_snoc ih ((hσ t).comp (hh.prodMk (measurable_priv t)))

lemma measurable_hist (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (t : ℕ) :
    Measurable (hist σ t) :=
  (measurable_gams t).prodMk (measurable_acts hσ t)

lemma measurable_act (hσ : ∀ t, Measurable (Function.uncurry (σ t))) (t : ℕ) :
    Measurable (act σ t) :=
  (hσ t).comp ((measurable_hist hσ t).prodMk (measurable_priv t))

/-- Extend a history of date `t` by the action `y` and the next weight `g`. -/
def extH {t : ℕ} (h : Hist t) (y g : ℝ) : Hist (t + 1) := (Fin.snoc h.1 g, Fin.snoc h.2 y)

/-- Restrict a history of date `t + 1` to date `t`. -/
def restr {t : ℕ} (h' : Hist (t + 1)) : Hist t := (Fin.init h'.1, Fin.init h'.2)

@[simp] lemma restr_extH {t : ℕ} (h : Hist t) (y g : ℝ) : restr (extH h y g) = h := by
  simp [restr, extH, Fin.init_snoc]

@[simp] lemma extH_last {t : ℕ} (h : Hist t) (y g : ℝ) : (extH h y g).2 (Fin.last t) = y := by
  simp [extH]

lemma measurable_extH (t : ℕ) :
    Measurable (fun q : Hist t × ℝ × ℝ => extH q.1 q.2.1 q.2.2) :=
  (measurable_snoc (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_snd)).prodMk
    (measurable_snoc (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_snd))

lemma measurable_restr (t : ℕ) : Measurable (restr : Hist (t + 1) → Hist t) :=
  (measurable_init measurable_fst).prodMk (measurable_init measurable_snd)

lemma hist_succ (t : ℕ) (ω : Ωg) :
    hist σ (t + 1) ω = extH (hist σ t ω) (act σ t ω) (gam ω (t + 1)) := by
  refine Prod.ext ?_ rfl
  funext i
  induction i using Fin.lastCases with
  | last => simp [hist, extH]
  | cast j => simp [hist, extH]

lemma restr_hist_succ (t : ℕ) (ω : Ωg) : restr (hist σ (t + 1) ω) = hist σ t ω := by
  rw [hist_succ, restr_extH]

/-! ### Dependence on the past only -/

/-- Keep `(θ, μ)`, the noises before `t` and the weights up to `t`; set the rest to `0`. -/
def trW (t : ℕ) (ω : Ωg) : Ωg :=
  (ω.1, ((fun i => if i < t then ω.2.1 i else 0), (fun i => if i < t + 1 then ω.2.2 i else 0)))

lemma measurable_trW (t : ℕ) : Measurable (trW t) := by
  refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
  · refine Measurable.of_eval fun i => ?_
    by_cases hi : i < t
    · simp only [hi, ↓reduceIte]
      exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
    · simp only [hi, ↓reduceIte]
      exact measurable_const
  · refine Measurable.of_eval fun i => ?_
    by_cases hi : i < t + 1
    · simp only [hi, ↓reduceIte]
      exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
    · simp only [hi, ↓reduceIte]
      exact measurable_const

lemma acts_congr : ∀ (t : ℕ) {ω ω' : Ωg}, ω.1 = ω'.1 → (∀ i < t, ω.2.1 i = ω'.2.1 i) →
    (∀ i < t, ω.2.2 i = ω'.2.2 i) → acts σ t ω = acts σ t ω'
  | 0, _, _, _, _, _ => by
    funext i
    exact i.elim0
  | t + 1, ω, ω', h1, h2, h3 => by
    have ih := acts_congr t h1 (fun i hi => h2 i (Nat.lt_succ_of_lt hi))
      (fun i hi => h3 i (Nat.lt_succ_of_lt hi))
    have hg : (fun i : Fin (t + 1) => gam ω i) = (fun i : Fin (t + 1) => gam ω' i) := by
      funext i
      exact h3 i i.2
    have hp : priv t ω = priv t ω' := by
      simp only [priv, h1, h2 t (Nat.lt_succ_self t)]
    show Fin.snoc (α := fun _ => ℝ) (acts σ t ω)
        (σ t ((fun i : Fin (t + 1) => gam ω i), acts σ t ω) (priv t ω)) =
      Fin.snoc (α := fun _ => ℝ) (acts σ t ω')
        (σ t ((fun i : Fin (t + 1) => gam ω' i), acts σ t ω') (priv t ω'))
    rw [ih, hg, hp]

lemma hist_trW (t : ℕ) (ω : Ωg) : hist σ t (trW t ω) = hist σ t ω := by
  refine Prod.ext ?_ ?_
  · funext i
    show (if (i : ℕ) < t + 1 then ω.2.2 i else 0) = ω.2.2 i
    simp only [i.2, ↓reduceIte]
  · exact acts_congr t rfl (fun i hi => by
      show (if i < t then ω.2.1 i else 0) = ω.2.1 i
      simp only [hi, ↓reduceIte]) (fun i hi => by
      show (if i < t + 1 then ω.2.2 i else 0) = ω.2.2 i
      simp only [Nat.lt_succ_of_lt hi, ↓reduceIte])

end CC.LinearPaths
