# Lean verification of "Managerial Intervention, Employee Motivation, and Collaboration"

This folder contains a machine-checked formalization of the results of [Orzach and Quist (2026), *Management Science* 72(11), 9421–9433](https://doi.org/10.1287/mnsc.2025.01366), in Lean 4 with Mathlib (v4.35.0). The library `ManagerialIntervention` in [`lean proofs/`](lean%20proofs/) covers the model of Sections 2–3, Lemmas 1–2, Propositions 3–6, Proposition B.1, and the extension to negative-valued projects in Appendix B.1. Section, result and equation numbers follow the published version.

**What has been checked**

- `lake build` completes with no errors and no `sorry`.
- The 99 results audited in `ManagerialIntervention/Audit.lean` rely only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Every module passes an independent kernel replay (`lake env leanchecker ManagerialIntervention.<Module>`).
- Each result in the tables below comes with concrete environments that satisfy its hypotheses (`Examples.lean`, `NonVacuity.lean`, `Prop5General.lean`, `Prop5LogConcave.lean`, `AppendixB1.lean`).

**To rebuild**, from `lean proofs/`: `lake exe cache get` (downloads prebuilt Mathlib), then `lake build`.

## Assumptions

All of the paper's assumptions are maintained. Two are made explicit and one regularity condition is added:

- **Made explicit.** "c_a(1) and c_p(1) are large enough" is stated as c_a′(1) ≥ E(v_a 1{v_a≥0}) and c_p′(1) ≥ −E(v_p 1{v_p<0}).
- **Made explicit.** The status quo μ_g is the unique minimizer of g, as in the paper's description that it is costly to adjust away from the status quo. Only the Appendix B.1 version of Proposition 6 uses this.
- **Added.** The cost of involvement g is continuous on (0, ∞). This is used only to show that an optimal involvement level exists (`MI.Env.muStar_nonempty`).

## Reading the tables

**\*** In a few places the manuscript states a comparison ("higher", "lower", "increasing", "decreasing", "<") where the two sides can be equal, or the quantity can be constant. Lean proves each such statement everywhere except at these ties, and the tables mark it "True subject to \*". In the main text the ties occur only at boundary values such as α = 1; in Appendix B.1 they also occur where the agent exerts no effort.

## Main results

| Paper | Lean | Difference from the paper |
|---|---|---|
| Definition 1 and the first-order conditions | `MI.Env.alphaA_le_one`, `MI.Env.alphaP_le_one`, `MI.Env.alphaA_neg_iff`, `MI.Env.foc_principal_cen`, `MI.Env.foc_principal_del`, `MI.Env.foc_agent_cen`, `MI.Env.foc_agent_del` | None |
| Lemma 1 | `MI.Env.lemma1` | None |
| Lemma 2 | `MI.Env.lemma2a`, `MI.Env.lemma2b` | None |
| Proposition 3 | `MI.Env.prop3`, `prop3a`, `prop3b_convex_strict`, `prop3b_concave_strict`, `prop3c_neg`, `prop3c_pos_strict` | True subject to \* |
| Proposition 4 | `MI.prop4` | True subject to \* |
| Proposition 5 | `MI.Env.prop5_logconcave` | False as written; holds under two added conditions (below) |
| Proposition 6 | `MI.Env.prop6`, `MI.Env.prop6_nonneg` | None |
| Proposition B.1 | `MI.propB1_contractible` | True subject to \* |

## Proposition 5

Proposition 5 is false as written. Lean proves that it holds with these two added conditions:

1. **The agent's marginal cost c_a′ is convex and log-concave.** This covers c_a(e) = k·eⁿ for every n ≥ 2, including quadratic costs (`MI.Cost.pow_d_convex`, `MI.Cost.pow_d_logconcave`). Convexity is used when alignment is negative, and log-concavity when it is positive.
2. **The agent exerts positive effort in equilibrium.** It is enough that the agent would work at the status-quo involvement level μ_g (`MI.Env.prop5_logconcave_statusQuo`).

The proof uses these conditions at the step where the cross-partial of the principal's objective takes the sign of ∂e_p/∂μ: condition 1 governs how the agent's effort responds to the value of an idea, and condition 2 keeps that effort away from zero.

Under these conditions, holding E(v_a), E(v_p), E(v_a 1{v_a<0}), E(v_p 1{v_p<0}), the costs and g fixed, μ\*(α_a) is weakly increasing in the strong set order (`MI.Env.prop5_logconcave`; pairwise form `MI.Env.prop5_logconcave_general`). Comparing an agent with α_a ≤ 0 to one with α_a ≥ 0 needs neither condition (`MI.Env.prop5_straddle`). Among agents who work in equilibrium, managerial involvement therefore rises with alignment and, by Proposition 6, exceeds μ_g whenever α_a ≥ 0. This is the basis for the three regions and the managerial styles discussed after Proposition 6.

Lean also proves Proposition 5 under alternative conditions: h_a = (c_a′)⁻¹ concave below E(v_a) and convex above it, with E(v_a 1{v_p≥0}) ≥ 0 (`MI.Env.prop5_curvature`); quadratic agent costs with the same inequality (`MI.Env.prop5_linear`); and convex h_a with α_a ≥ 0 (`MI.Env.prop5_convex`).

## Appendix B.1: negative-valued projects

The main-text assumptions are maintained, with E(v_a) and E(v_p) negative. The definitions of α_a^n and α_p^n implicitly require P(v_a > 0)·P(v_p > 0) > 0, which the formalization states explicitly.

| Claim in Appendix B.1 | Lean | Difference from the paper |
|---|---|---|
| Lemma 1 | `MI.EnvN.lemma1` | None |
| Lemma 2 | `MI.EnvN.lemma2_del`, `MI.EnvN.lemma2_cen`, `MI.EnvN.ea_cen_zero` | True subject to \* |
| The display before (B.8) and the left side of (B.8) | `MI.EnvN.effort_iff`, `MI.EnvN.effort_iff_h` | None |
| The equivalence in (B.8) | `MI.EnvN.effort_lt_iff_alpha`, `MI.EnvN.effort_iff_corrected` | True subject to \* |
| Proposition 3(a) | `MI.EnvN.prop3a_analogue` | None |
| Proposition 3(b) | `MI.EnvN.prop3b_convex_analogue`, `MI.EnvN.prop3b_concave_analogue` | True subject to \* |
| Proposition 3(c) | `MI.EnvN.prop3c_analogue_strict`, `MI.EnvN.prop3c_pos_analogue_strict`, `MI.EnvN.ea_zero_of_nonpos` | True subject to \* |
| Proposition 4 | `MI.prop4_analogue` | None |
| Proposition 5 | `MI.EnvN.prop5_analogue` | Holds under the same added condition as in the main text |
| Proposition 6 | `MI.EnvN.prop6_analogue`, `MI.EnvN.muStar_eq_singleton` | True subject to \* |

## Files

In `lean proofs/ManagerialIntervention/`:

- `Cost.lean`, `Model.lean`: effort costs, best responses and the model.
- `Formal.lean`: Lemmas 1–2 and Proposition 3.
- `Threshold.lean`: Propositions 4 and B.1.
- `Informal.lean`: the informal-delegation model of Section 3.2, Proposition 6, and Proposition 5 for convex h_a and for quadratic agent costs.
- `Prop5LogConcave.lean`: Proposition 5 and the Appendix B.1 versions of Propositions 5 and 6.
- `Prop5General.lean`: Proposition 5 under the curvature condition and the Appendix B.1 informal-delegation model.
- `Extensions.lean`, `AppendixB1.lean`: Appendix B.1, including the strict forms of the effort comparisons.
- `Examples.lean`, `NonVacuity.lean`, `Counterexamples.lean`: example environments.
- `Audit.lean`: the axiom audit.
