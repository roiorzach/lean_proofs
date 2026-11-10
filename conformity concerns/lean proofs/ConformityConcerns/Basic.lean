import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Common notation for the formalization of "Conformity Concerns: A Dynamic Perspective"

The common-knowledge cutoff `κck` is the paper's `κ^{c.k.}`. The proof of Proposition 1 shows
that it equals `1/4`; we use that value as its definition (Proposition 1 is then stated both as
"there exists a threshold" and with this explicit value).
-/

namespace CC

/-- The common-knowledge conformity cutoff `κ^{c.k.} = 1/4`. -/
noncomputable def κck : ℝ := 1 / 4

lemma κck_eq : κck = 1 / 4 := rfl

lemma κck_pos : 0 < κck := by norm_num [κck]

end CC
