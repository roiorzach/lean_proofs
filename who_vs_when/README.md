# Lean verification of "Who versus when: Designing decision processes in organizations"

This folder contains a machine-checked formalization of the results of [Orzach (2024), *International Journal of Industrial Organization* 97, 103111](https://doi.org/10.1016/j.ijindorg.2024.103111), in Lean 4 with Mathlib (v4.34.1). The library `WhoVsWhen` in [`lean proofs/`](lean%20proofs/) covers the model of Sections 2–3, Lemmas 1–4, Remark 1 and Propositions 1–2. Each result corresponds to exactly one Lean theorem. Section, result and equation numbers follow the published version. The proofs try to follow the paper's arguments.

**What has been checked**

- `lake build` completes with no errors, no warnings and no `sorry`.
- The seven results, and the examples below, rely only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). `lean proofs/Verify.lean` prints this audit.
- Every module passes an independent kernel replay (`lake env leanchecker WhoVsWhen.<Module>`).
- The paper's environment, with independent uniform states, is built in `Examples.lean`. It satisfies every assumption of the model. Each result is applied to it with concrete parameters, which shows its hypotheses can be met.

**To rebuild**, from `lean proofs/`: `lake exe cache get` (downloads prebuilt Mathlib), then `lake build`. `lake env lean Verify.lean` prints the axiom audit.

## Assumptions

All of the paper's assumptions are maintained. Two conventions are made explicit, and three lemmas are proved in more generality:

- **Made explicit.** In Proposition 1, "for a fixed information loss" is read as follows. Under every timing compared, the leader's state is known to both units (the paper's convention m₁ = θ₁), and the follower's state is communicated by the same message.
- **Made explicit.** Lemma 2 defines information loss on "the limit partition". Lean characterizes that partition as the only one that accumulates at 0 and satisfies every boundary type's indifference condition (`TruthfulLimitPartition`). Its information loss is computed cell by cell as Σ P(cell)·Var(θ | cell).
- **Generalized.** Lemmas 1, 3 and 4 do not use the uniform distribution. They hold for independent, mean-zero states with finite variance and for any messages that are functions of the sender's own state. The information loss is cᵢ = E(θᵢ − E(θᵢ | mᵢ))², with the conditional expectation taken in the model. Lemma 2 gives its value in the limit partition.

## Reading the tables

- **Typo in the result; the proof makes the correct deductions**: a formula printed in the statement is wrong, but the paper's proofs use the correct one. It appears that the code behind its figures does too. The result holds with the corrected formula.
- **Condition stated in the appendix, not in the result**: the result needs a condition that the paper's supporting analysis assumes but the statement omits. Lean proves the result with the condition.

## Main results

| Paper | Lean | Difference from the paper |
|---|---|---|
| Lemma 1 | `lemma1` | None |
| Lemma 2 | `lemma2` | Typo in the result; the proof makes the correct deductions (below) |
| Lemma 3 | `lemma3` | None |
| Lemma 4 | `lemma4` | Typos in the result; the computations make the correct deductions (below) |
| Remark 1 | `remark1` | Condition stated in the appendix, not in the result: equal volatilities (below) |
| Proposition 1 | `prop1` | None |
| Proposition 2 | `prop2` | None |

Each theorem states every part of its result as one conjunction:

- `lemma1`: the follower's decision; the leader's decision, for any posterior belief; the concurrent decision, for any belief about the other unit's decision; and the fact that the concurrent rules are best responses to each other.
- `lemma2`: the sequential and the concurrent information losses; and φ_{1,sequential} = ∞, meaning that the leader's decision reveals its state.
- `remark1`: public information; no communication; and no communication with equal volatilities.
- `prop1` and `prop2`: parts (i)–(ii) and (i)–(iii).

## Lemmas 2 and 4

Both typos are in the concurrent case. The manuscript does not derive that case: it takes it from Rantakari (2008), whose formulas are correct (checked against his January 2008 working paper). The sequential case, which the manuscript does derive, is correct. The corrections are:

- **φ_{i,concurrent}** is r_j(1 − r_i)/(1 − r_j) = β_j/((1 − r_i)(1 − r_j)). Lemma 2 prints r_j(1 − r_j)/(1 − r_j). Lemma 4 prints φ_i^{sim} = β_i/(1 − r_i), which is Lemma 2's sequential value for the other unit's state.
- **In Lemma 4**, the coefficient on σ₁²V(φ₁) has (1 − r₂)², not (1 − r₁)².

The rest of the paper uses the correct formulas:

- **Proofs.** The proof of Proposition 2(i) uses φ₁φ₂ = r₁r₂ and φ_concurrent > φ_sequential, and only the corrected φ satisfies both.
- **Figures.** It appears that the code used to make the figures had the correct formulas. Recomputing Figs. 2a, 2b, 3a and 4a with them reproduces the published figures except at region boundaries. The printed formulas do not reproduce them. For example, in Fig. 4a they would move the edge of the concurrent region along r₁ = 0.05 from the published r₂ ≈ 0.16 to 0.145. This check is numerical and outside Lean.

## Remark 1

Remark 1 states that, without communication, the unit that cares more about coordination should move second. It gives no condition on volatilities. The analysis behind it in Appendix A.5 refers to Fig. 7, whose caption specifies equal volatilities. `remark1` proves the statement under that condition, σ₁² = σ₂².

The condition matters. Without communication, the gain from letting a unit lead rather than deciding concurrently is proportional to that unit's volatility. When volatilities differ, the more volatile unit can therefore be the better leader even if it cares more about coordination.

The appendix's other conclusion needs no condition, and `remark1` proves it for all volatilities: without communication, concurrent decision-making is never optimal.

Without communication, cᵢ = σᵢ², and the expected losses follow from Lemmas 3 and 4. Appendix A.5 says to "plug in 0 for V(φ)", but the losses it then lists are the ones for V = 1, so its deductions are correct.

## Files

In `lean proofs/WhoVsWhen/`:

- `Basic.lean`: the loss function (1) and the quantities β, γ, V and φ.
- `Lemma1.lean`: Lemma 1.
- `Lemma2.lean`: Lemma 2, including the indifference conditions and the limit partition.
- `Model.lean`: the probability model (`Env`) and the expected losses used by Lemmas 3 and 4 and Proposition 1.
- `Lemma3.lean`, `Lemma4.lean`: Lemmas 3 and 4.
- `Remark1.lean`, `Prop1.lean`, `Prop2.lean`: Remark 1 and Propositions 1 and 2.
- `Examples.lean`: the paper's environment and the examples.

`lean proofs/Verify.lean` is the axiom audit.
