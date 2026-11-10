# Lean formalization of "Conformity Concerns: A Dynamic Perspective"

This folder contains a Lean 4 formalization of the paper and its online appendix. Every numbered
result has a complete, machine-checked proof: there is no `sorry`, and the only axioms used are
Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`).

The manuscript is on my [personal webpage](https://sites.google.com/view/roiorzach).

- Main text: Propositions 1–4, Lemmas 1–3 and Corollary 1.
- Online appendix: Propositions A1–A6, Lemmas A1–A3, Corollaries A1–A3 and Remark A1.
- Also formalized: the definitions these results use, the Shifted Preferences section, and the
  text's comparison of D1 with the modified refinement `D1^∞`.

Where the paper gives a proof, the LLM-generated Lean proof tries to follow its argument as
closely as possible. The social-learning results
for the Gaussian model (Propositions 2, 3(1) and A1 and Corollaries A2 and A3) are stated with the
paper's definition and hold in every signaling equilibrium of the dynamic game, and the Gaussian
updating formulas they use are proved from Bayes' rule.

The formalization applies to these results and to the claims from their proofs that the entries
below list. It does not cover other remarks in the text and footnotes. Lean checks the proofs;
whether a Lean statement says what the paper says is a matter of reading its definitions, so the
entries below name each Lean theorem and say how it relates to the paper's statement. Where the
two differ, the entry, the Conventions section or "How the model is set up" says how.

- Lean `v4.34.1`, Mathlib `v4.34.1`.
- `lean proofs/ConformityConcerns/MainResults.lean` imports every result below and runs
  `#print axioms` on each theorem, so the build output lists the axioms each one uses.
- File paths below are relative to `lean proofs/ConformityConcerns/`.

To build, from `lean proofs/`: `lake exe cache get` (downloads the compiled Mathlib), then
`lake build`.

This file goes through the paper in order. Notes marked **From the proof** are Lean theorems for
claims made in a proof or in the surrounding text rather than in the statement of a result.

## Conventions

- `CC.κck` is defined as `1/4`. Proposition 1 is proved both as "there exists a threshold" and
  with this value.
- Lean counts dates from `0`; Lean's date `0` is the paper's period 1.
- "liminf > 1" is stated as "for some ε > 0, eventually at least 1 + ε". "liminf ≥ 1" is stated
  as "for every c < 1, eventually at least c".
- Strategies are pure, as in Bernheim (1994) and as the online appendix assumes for general
  losses. In the Gaussian game this is without loss: under Linearity each type's objective on
  `I(h^t)` is strictly concave (first step of the proof of Lemma 3). Beliefs in the Gaussian game
  are measurable in the action.
- Strategies, beliefs and conditional expectations are only determined up to null sets, so some
  conclusions hold "for almost every type" or "almost surely" where the paper states them
  pointwise.
- The general-loss setting normalizes `g(0) = f(0) = 0`. Subtracting these constants changes every
  payoff by a constant and leaves the derivatives unchanged; `CC.Learning.propA6_unnormalized` is
  Proposition A6 for losses that are not normalized.

## How the model is set up in Lean

**The period game (main text).** `PeriodGame/Defs.lean`. Fix a period and a public history at
which public beliefs are Gaussian.

- Player t's private information is a point of a probability space. Two random variables
  matter: `Z = γ_t E(θ | h^t, s_t, v_t) + v_t` and the preference type `v_t`, which are jointly
  Gaussian.
- A strategy is a measurable function of the private information. The public's belief after
  action x is a probability measure on preference types (a Markov kernel).
- A perfect Bayesian equilibrium requires every type to best respond and beliefs to follow
  Bayes' rule on path: the joint law of (action, type) disintegrates through the belief kernel.
- Linearity and Social Optimality are as in the paper's definition of a signaling equilibrium
  (`Game.IsSignalingEq`).
- The standing assumptions (`Game.Std`) include that `Z` is measurable. This holds in the
  paper's model because `Z` is an affine function of `(s_t, v_t)`.
- Lemma 1, Corollary 1 and Lemma 3 are stated for any `Game` satisfying `Game.Std`.
  `CC.gameAt m S γ κ` (`PeriodGame/Instance.lean`) is the period game at a history with public
  beliefs `N(m, S)` and weight `γ`, and `CC.gameAt_std` shows that it satisfies `Game.Std`, so they
  apply at every Gaussian history.

The Gaussian formulas the model uses are proved to be Bayes' rule in `Gaussian/Conditioning.lean`:

- `CC.privInfo_law`: the law of `(s_t, v_t)` given the history.
- `CC.condExp_theta`: the formula for `E(θ | h^t, s_t, v_t)`.
- `CC.condExp_adaptation`: the expected adaptation loss equals `(x − Z)²` plus a constant.
- `CC.posterior_after_reveal`: after a revealing period the posterior of `(θ, μ)` is Gaussian,
  with the updated covariance.

**Belief dynamics.** `Dynamics/Defs.lean`. `SigmaC` is the posterior covariance process: a date
is revealing iff the criterion of Corollary 1 holds, and then the covariance is updated as after
observing `Z_t`. `CC.SigmaSeq_eq_SigmaC` and `CC.periodRevealing_iff` (`PeriodGame/Instance.lean`)
show that this is the covariance process of the signaling equilibrium.

**The dynamic game.** Definition 1 requires a signaling equilibrium at each history.
`LinearPaths.IsSignalingProfile` (`LinearPaths/Signaling.lean`) says that a measurable strategy
profile is, at almost every on-path history with public beliefs `N(m, S)`, a signaling equilibrium
of the period game at that history. `BridgeK.IsSignalingProfileK` (`BridgeK/Profile.lean`) is the
same with heterogeneous `κ_t` and public disclosures.

Lean constrains only on-path histories. Players are short-lived, so play at histories that are
never reached does not affect incentives on path, and a measurable profile satisfying Definition 1
at each history is in particular such a profile. The existence theorems give profiles with these
on-path properties.

- Such profiles exist (`CC.LinearPaths.exists_signalingProfile`,
  `CC.BridgeK.exists_signalingProfileK`).
- In every such profile, almost surely each action is the one used to state the results, `eqAct`
  (`CC.LinearPaths.signalingProfile_act`) or `eqActK` (`CC.BridgeK.signalingProfileK_act`), and the
  posterior means given the realised history are the ones used there
  (`CC.LinearPaths.signalingProfile_post_ae`, `CC.BridgeK.signalingProfileK_post_ae`).
- At the level of one history, `CC.LinearPaths.eqForm_signaling` shows that the rule behind `eqAct`
  is a signaling equilibrium of the period game, `CC.LinearPaths.signaling_ae_eqForm` shows that
  every signaling equilibrium plays it for almost every private information, and
  `CC.BridgeK.eqActK_signaling` states this along the path for `eqActK`.

The entries below name the version of each result stated for every such profile.

**Social learning.** The paper's definition is formalized in `Bridge/Defs.lean` (`SLOccurs`,
`SLFails`): for almost every realization `r` of `θ`, the posterior mean converges in probability
to `r` under the conditional law given `θ = r`. The results about social learning are proved with
this definition, with posterior means given the public history, except where the Shifted
Preferences entry says they are stated for posterior variances. Lean also proves the posterior
variance versions. The opening claim of the proof of Proposition 2 — social learning about `θ`
(about `μ`) occurs if and only if its posterior variance converges to zero almost surely — is
`CC.Bridge.socialLearning_theta_iff` and `CC.Bridge.socialLearning_mu_iff`
(`Bridge/Asymptotic.lean`), for any law of the weights and any positive semidefinite prior.
Propositions 3(1) and A1 use an extension of this model, in `BridgeK/`, in which the conformity
concerns `κ_t` are publicly observed weights and a signal can be disclosed at a given date.
Propositions A4 and A6 state the same definition on their own sample space
(`Learning/Defs.lean`: for almost every realization of `μ`, convergence in probability under the
law of the noise).

**General losses (online appendix, "Refinements and Central Pooling with General Losses" and
"Nonlinear Decisions").** `General/Defs.lean`. At a fixed history:

- The type distribution `F` has an everywhere positive continuous density.
- Beliefs after each action are probability measures on the extended reals `[−∞, +∞]`.
- The adaptation loss `g` is C², even and strictly convex, with `g(0) = 0`.
- The conformity loss is a C², strictly convex function `ℓ` minimized at the norm `μ` with
  `ℓ(μ) = 0`, and is `+∞` at `±∞`.
  - The paper's loss `f(b − μ)`, with `f` even, is a special case (`CC.General.confLoss_of_even`).
  - Using a general `ℓ` also covers the conformity loss `κ(m − min m)` of Proposition A5.
- Definitions:
  - `Setting.IsCPBE`: compactified perfect Bayesian equilibrium.
  - `Setting.D1Inf`: the refinement `D1^∞`; Definition A1.
  - `Setting.IsCentralPoolingWith`: central pooling, as defined in the online appendix. The
    differentiability outside the pool in the main-text definition is `Setting.TailODE`.
  - `Setting.TailODE`: the differential equation on the separating tails.

**Across histories (Propositions A4, A5 and A6).** A strategy profile gives player t's action
as a function of the public history and the player's type. "An equilibrium satisfying `D1^∞`"
means that at every history the period strategy is an equilibrium satisfying `D1^∞` of the
period game at that history. With `θ` known the weights `γ_t` do not affect payoffs, so
`Learning/Assembly.lean` leaves them out of the history; `Learning/Weights.lean` includes them.

## Main text

### Proposition 1 (Commonly Known Environment)

There is a threshold `κck` such that the unique signaling equilibrium has
`a(v) = (1 + √(1−4κ))/2 · v` and `u(v) = −(1 − √(1−4κ))/2 · v²` if `κ ≤ κck`, and
`a(v) = 0`, `u(v) = −v² − κ` if `κ > κck`.

- Lean: `CC.LG.prop1` (there is a threshold) and `CC.LG.prop1_threshold` (the threshold is `1/4`),
  in `PeriodGame/CommonKnowledge.lean`.
- Types are `v ~ N(0,1)`, with the norm normalized to 0. A signaling equilibrium exists, and every signaling
  equilibrium has the stated decision rule and utility for almost every type.

### Lemma 1

The signaling equilibrium is revealing at `h^t` iff some `α_t` solves the slope equation
`(1 + κ α_t²) s̃(h^t) = α_t`.

- Lean: `CC.LG.lemma1`, in `PeriodGame/Revealing.lean`. It also proves that a signaling
  equilibrium exists and that it is pooling when the equation has no solution.
- **From the proof:** `CC.LG.signalingEq_char` gives the equilibrium explicitly. When revealing,
  Social Optimality selects the root of smallest magnitude, so `a_t = E Z + λ(Z − E Z)` with
  `λ = (1 + √(1 − 4κ s̃²))/2`. When pooling, `a_t = E Z`. It also gives the ex-ante losses.

### Corollary 1

The signaling equilibrium is revealing at `h^t` iff `|s̃(h^t)| ≤ √(κck/κ)`.

- Lean: `CC.LG.corollary1`, in `PeriodGame/Revealing.lean`.
- **From the proof:** `CC.LG.slope_root_iff`, the quadratic-formula step.

### Proposition 2 (Characterization of Social Learning)

Suppose `Σ₁ ≻ 0`. If `κ < κck`, social learning about preferences and fundamentals occurs. If
`κ > κck`, there is a finite time after which the signaling equilibrium is pooling in every
period, and social learning fails.

- `γ_t` is i.i.d. with full support on `[0,1]`, as in the model.
- Lean, with the paper's definition of social learning: `CC.Bridge.prop2_socialLearning`, in
  `Bridge/Prop2.lean`.
- Lean, for the posterior variances: `CC.prop2` (`Dynamics/Equilibrium.lean`) and
  `CC.prop2_beliefs` (`Dynamics/LongRun.lean`).
  - If `κ < κck`, both posterior variances converge to zero almost surely.
  - If `κ > κck`, almost surely every period is pooling after some finite time, and the
    posterior covariance then stays constant and positive definite.
- In every signaling equilibrium of the dynamic game: `CC.LinearPaths.prop2_signalingProfile`,
  with the finite-time pooling and posterior means given the profile's realised history.
- **From the proof:** `CC.Bridge.histSigma_eq_info` shows, for any positive semidefinite prior,
  that the public history (weights and equilibrium actions) carries the same information as the
  weights and the informative part of each action. So the posterior means used in the proof are
  the posterior means given the history. `CC.Bridge.histSigma_eq` is the same under `Σ₁ ≻ 0`.
- **From the proof:** the first paragraph. Social learning about `θ` (about `μ`) occurs if and only
  if `σ²_θ,t → 0` (`σ²_μ,t → 0`) almost surely: `CC.Bridge.socialLearning_theta_iff` and
  `CC.Bridge.socialLearning_mu_iff`, in `Bridge/Asymptotic.lean`. Otherwise it fails:
  `CC.Bridge.socialLearning_theta_fails` and `CC.Bridge.socialLearning_mu_fails`, in
  `Bridge/AsyAux/SLFails.lean`.

### Proposition 3 (Fragility)

When `κ > κck`: (1) an individual-oriented (peer-oriented) intervention never results in social
learning about `μ` (`θ`); (2) at zero correlation, the equilibrium is never fragile to an
individual-oriented intervention but may be fragile to a peer-oriented one.

- An intervention is the public disclosure of a signal, as in the paper's definition of
  fragility: the signal's realization is disclosed in full. In Lean the signal is `θ + η`
  (individual-oriented) or `μ + η` (peer-oriented), where the noise `η` is Gaussian with variance
  `n ≥ 0`. The paper's definition of fragility is `n = 1`, a signal distributed like `s_t` or
  `v_t`, and `n = 0` is perfect revelation. File: `Interventions/Fragility.lean`.
- (1), with the paper's definition of social learning: `CC.BridgeK.prop3_1_socialLearning` and
  `CC.BridgeK.prop3_1_never`, in `BridgeK/Prop3.lean`.
  - The model (`BridgeK/Defs.lean`) is the dynamic Gaussian model of Proposition 2 with constant
    `κ > κck`, `Σ₁ ≻ 0` and `γ_t` i.i.d. with full support on `[0,1]`, plus a signal
    `θ + √n·ξ` (individual-oriented) or `μ + √n·ξ` (peer-oriented) disclosed at a date `τ`,
    with `ξ ~ N(0,1)` independent of everything. The signal becomes part of the public history
    from date `τ` on, and play is the signaling equilibrium given current public beliefs.
  - For every date `τ` and every noise variance `n ≥ 0` (the paper's signal is `n = 1`), social
    learning about `μ` (resp. `θ`) fails, so it does not occur.
- (1), for the posterior variances: `CC.prop3_1`, for any noise variance `n ≥ 0` and any later
  weights in `[0,1]`.
- (1), for every prior of the model: the theorems above assume `Σ₁ ≻ 0`. For `σ_θ, σ_μ ≥ 0` and
  `ρ ∈ (−1, 1)`, including priors with one zero variance, see `CC.BridgeK.prop3_1_socialLearning_prior`,
  `CC.BridgeK.prop3_1_never_prior` and `CC.prop3_1_prior`. Each conclusion assumes that the
  variable learned about has positive prior variance, as the definition of social learning does.
- (1), in every signaling equilibrium of the dynamic game and for every prior of the model:
  `CC.BridgeK.prop3_1_signalingProfile`.
- (2), individual-oriented: `CC.prop3_2_individual`. For all variances and every `γ`, a pooling
  period stays pooling after the intervention.
- (2), peer-oriented: `CC.prop3_2_peer`. "May be fragile" is shown as: for every `σ²_μ > 0` and
  `γ > 0` there is `σ²_θ > 0` such that the period is pooling before the intervention and
  revealing after it.

### Lemma 2

At zero correlation, the sensitivity is decreasing in `σ²_θ,t` and increasing in `σ²_μ,t`,
strictly so when `γ_t σ_θ,t > 0`.

- Lean: `CC.lemma2`, in `Interventions/Sensitivity.lean`.
- **From the proof:** `CC.sens_diag` is the closed form of the sensitivity at zero correlation.
  `CC.sensDiag_hasDerivAt` gives its derivatives.

### Proposition 4 (Effect of Interventions on Pooling Decision)

The formulas for `Δ(μ)` and `Δ(θ)`.

- Lean: `CC.prop4`, in `Interventions/PoolingShift.lean`.
- The setting is that of the paragraph before the proposition:
  - independent priors `θ ~ N(0, σ²_θ)` and `μ ~ N(0, σ²_μ)`, with noise `ε₁, ν₁ ~ N(0,1)`;
  - period 1 is revealing with `a₁ = λ_s s₁ + λ_v v₁` for any `λ_s, λ_v > 0`;
  - period 2 pools on `γ₂ E(θ | a₁) + E(μ | a₁)`;
  - the new pooling decision is the posterior expectation of `γ₂ θ + μ` given the new public
    information, as in the paper's proof: `γ₂ E(θ | a₁, μ) + μ` after `μ` is revealed and
    `γ₂ θ + E(μ | a₁, θ)` after `θ` is revealed. That a pooling signaling equilibrium plays this
    expectation is part of `CC.LG.signalingEq_char`; Lean does not re-derive the period-2
    equilibrium in this setting.
- Conditional expectations are Mathlib's, given the σ-algebra of the conditioning variables, so
  the two identities hold almost surely. The random variables are assumed measurable.

### D1 and the modified refinement (section "Extensions Beyond the Linear–Gaussian Model")

The text states that every equilibrium satisfying D1 has the same strategy as an equilibrium
satisfying the modified refinement (`D1^∞`).

- Lean: `CC.General.ordD1_strategy_D1Inf`, in `D1Compact/RealLine.lean`, in the general-loss
  setting with types on ℝ.
- An ordinary perfect Bayesian equilibrium has beliefs that are probability measures on ℝ
  (`Setting.IsOrdPBE`). Ordinary D1 (`Setting.OrdD1`) is the Cho–Kreps criterion: after an
  off-path action, beliefs are supported on the types that are not eliminated, where type `v` is
  eliminated if some other type gains strictly from the deviation under every belief under which
  `v` gains weakly. As usual, beliefs are unrestricted when every type is eliminated.
- The theorem: the strategy of every ordinary perfect Bayesian equilibrium satisfying D1 is the
  strategy of a compactified perfect Bayesian equilibrium satisfying `D1^∞`.

### Lemma 3 (Appendix A)

With Gaussian public beliefs at `h^t`, in any equilibrium satisfying Linearity (and Social
Optimality if `s̃(h^t) = 0`), `a_t` is either constant or strictly increasing and affine in
`Z_t`. In the latter case every action is on path and the beliefs are Gaussian with variance
independent of `a_t`. Public beliefs are Gaussian at every on-path history.

- Lean: `CC.LG.lemma3`, in `PeriodGame/Dichotomy.lean`.
  - "Every action is on path" is: the law of the action has full support.
  - The beliefs are Gaussian after almost every action.
- Last sentence: `CC.LinearPaths.beliefs_gaussian_of_linear`, in `LinearPaths/Beliefs.lean`.
  - The profile is any measurable strategy profile of the dynamic game that, at almost every
    on-path history where public beliefs are `N(m, Σ)`, is a linear equilibrium of the period
    game at that history, and a signaling equilibrium there if `s̃(h^t) = 0`
    (`LinearPaths.IsLinearProfile`). Whether a period pools or reveals may depend on the whole
    history.
  - Conclusion: at every date, the public posterior of `(θ, μ)` given the history is Gaussian at
    almost every on-path history.
  - `CC.LinearPaths.lemma3_onPath` adds that the period strategy pools or reveals at almost every
    on-path history. `CC.LinearPaths.beliefs_gaussian_of_linear_param` gives the posterior
    parameters explicitly: they are measurable in the history, unchanged after a pooling period,
    and updated as after observing `Z_t` after a revealing period.
- For the signaling equilibrium specifically: `CC.Bridge.beliefs_gaussian`, in
  `Bridge/Beliefs.lean`, with `CC.Bridge.histSigma_eq` showing that the information it
  conditions on is the public history.

## Online appendix

### Shifted Preferences

The section considers the conformity term `−κ ∫(b − μ(h^t) − c)² φ(db | h^t, a_t)`. Lean:
folder `Shifted/`. The period game with shift `c` is the linear–Gaussian period game with this
conformity loss (`Shifted/Defs.lean`); "an equilibrium with revelation" is a revealing linear
equilibrium.

- The sensitivity does not depend on `μ(h^t)` (`CC.Shifted.sens_indep_means`) or on `c`, so
  whether an equilibrium with revelation exists does not depend on `c`
  (`CC.Shifted.lemma1_sh`, `CC.Shifted.corollary1_sh`, `CC.Shifted.revelation_indep_c`).
- In the baseline, Social Optimality selects a revealing equilibrium whenever one exists
  (`CC.Shifted.baseline_selects_revealing`). With the shift, at a history with a revealing
  equilibrium and `s̃(h^t) ≠ 0` there is an explicit threshold `c̄(h^t) > 0`: Social Optimality
  reveals for `|c| < c̄(h^t)` and pools for `|c| > c̄(h^t)` (`CC.Shifted.large_c_threshold`,
  `CC.Shifted.signalingEq_char_sh`). Such histories exist in the model
  (`CC.Shifted.large_c_gameAt`, `CC.Shifted.large_c_model`).
- Selecting the payoff-maximizing revealing equilibrium whenever one exists
  (`Game.IsShAltEq`), a period is revealing exactly when it is in the baseline, and the action
  differs from the baseline action by a constant (`CC.Shifted.altEq_revealing_iff`). So the
  revealing dates and the covariance process are those of the baseline
  (`CC.Shifted.SigmaSeqAlt_eq`), and the learning results hold as before:
  - Proposition 2 with the paper's definition (`CC.Shifted.prop2_socialLearning_alt`) and for
    the posterior variances (`CC.Shifted.prop2_alt`);
  - Propositions A1 and A2 (`CC.Shifted.propA1_alt`, `CC.Shifted.propA2_alt`), for the posterior
    covariance process;
  - Proposition 3 (`CC.Shifted.prop3_1_alt`, `CC.Shifted.prop3_1_prior_alt`,
    `CC.Shifted.prop3_2_individual_alt`, `CC.Shifted.prop3_2_peer_alt`), with part (1) for the
    posterior variances;
  - the learning parts of Corollaries A2 and A3 (`CC.Shifted.corollaryA2_alt`,
    `CC.Shifted.corollaryA3_alt`), for the posterior variances.

### Lemma A1 (Information Accounting)

The precision update, the trace identity, and `min{σ²_θ,t, σ²_μ,t} ≥ 1/(tr Λ₁ + N_t)`.

- Lean: `CC.lemmaA1`, in `Dynamics/Accounting.lean`. It assumes `Σ₁ ≻ 0` and holds for any
  sequences of weights and conformity concerns.

### Proposition A1 (Heterogeneous Conformity Concerns)

- Lean: `CC.propA1`, in `Dynamics/Heterogeneous.lean`.
  - `κ_t` is i.i.d. with a law on `(0,∞)` with no atom at `κck`, independent of the weights.
  - If `Pr(κ_t < κck) > 0`, the posterior covariance converges to zero almost surely,
    `N_t/t → ε`, and the liminf bound holds.
  - "`inf Supp(κ_t) > κck`" is stated as `Pr(κ_t < κ₀) = 0` for some `κ₀ > κck`. Then almost
    surely, after a finite time every period is pooling and the covariance is constant and
    positive definite.
- `CC.propA1_equilibrium`, in `Dynamics/Equilibrium.lean`, shows that the covariance process
  used is that of the signaling equilibrium.
- With the paper's definition of social learning: `CC.BridgeK.propA1_socialLearning`, in
  `BridgeK/PropA1.lean`.
  - The model (`BridgeK/Defs.lean`) has public weights `(κ_t, γ_t)`, i.i.d. with law
    `G ⊗ Gγ`, so `κ_t` is publicly observed and independent of all other primitives; `Gγ` has
    full support on `[0,1]` and `Σ₁ ≻ 0`. Play is the signaling equilibrium with `κ_t` in place
    of `κ`, and posterior means are given the public history (`CC.BridgeK.histSigmaK_eq_info`).
  - If `Pr(κ_t < κck) > 0`, social learning about both `θ` and `μ` occurs; if
    `Pr(κ_t < κ₀) = 0` for some `κ₀ > κck`, it fails for both.
  - `CC.BridgeK.beliefsK_gaussian` shows that public beliefs are Gaussian with the covariance
    process used.
- In every signaling equilibrium of the dynamic game: `CC.BridgeK.propA1_signalingProfile`.
  `CC.BridgeK.propA1_path_signalingProfile` shows that in every such profile the public posterior
  has covariance `SigmaH`, and a period reveals exactly when the criterion holds, so the rates of
  `CC.propA1` apply.

### Proposition A2 (Unbounded Stakes)

- Lean: `CC.propA2` (`Dynamics/Unbounded.lean`) and `CC.propA2_equilibrium` (the same statement
  for the signaling-equilibrium process).
- `γ_t` is i.i.d. with support in `[0,∞)` and unbounded above; there is no bound `γ_t ≤ 1`.
- In every signaling equilibrium of the dynamic game: `CC.LinearPaths.propA2_signalingProfile`.

### Lemma A2 (Continuity of Equilibrium Payoffs)

- Lean: `CC.General.lemmaA2`, in `General/PayoffContinuity.lean`. It covers every compactified
  perfect Bayesian equilibrium of the general-loss setting.

### Definition A1 (D1^∞)

- Lean: `Setting.D1Inf`, in `General/Defs.lean`.
- The survivor set `S^∞(x)` is `Setting.survivors`: the minimizers over `[−∞, +∞]` of the clipped
  indifference index, extended to `±∞` by its liminf.
- The Note after Definition A1 (on a compact type space, `D1^∞` and ordinary D1 support the same
  equilibrium strategies): `CC.General.Compact.noteA1`, in `D1Compact/Note.lean`.
  - Types lie in a compact interval `[v̲, v̄]` with a positive continuous density there
    (`Compact.CSetting`); beliefs are probability measures on the interval.
  - `D1^∞` uses the same clipped index, minimized over the interval. Ordinary D1 is the
    Cho–Kreps criterion described in "D1 and the modified refinement" above, with beliefs
    unrestricted when every type is eliminated.
  - The theorem: a strategy is supported by a compactified perfect Bayesian equilibrium
    satisfying `D1^∞` if and only if it is supported by one satisfying ordinary D1.

### Proposition A3 (central pooling)

(i) Every pure compactified perfect Bayesian equilibrium satisfying `D1^∞` is central pooling,
and on each separating tail `a'(v) = f'(v−μ)/g'(v−a(v)) > 0`. (ii) Every fully pooling
strategy, with the stated beliefs, is such an equilibrium.

- Lean: in `General/CentralPooling.lean`.
  - `CC.General.propA3_i` is (i) for a general conformity loss `ℓ`, with `a' = ℓ'(v)/g'(v−a(v))`.
  - `CC.General.propA3_i_even` is (i) in the paper's form `ℓ(b) = f(b − μ)`.
  - `CC.General.propA3_ii` is (ii).

### Lemma A3 (Tail Solutions of the Differential Equation) and Corollary A1 (Left-Tail Solutions)

- Lean: `CC.ODE.lemmaA3_i` … `CC.ODE.lemmaA3_iv` (`ODE/Tail.lean`) and `CC.ODE.corollaryA1_i` …
  `CC.ODE.corollaryA1_iv` (`ODE/LeftTail.lean`).
- Right- and left-tail solutions are `IsRightTailSol` and `IsLeftTailSol`, in `ODE/Defs.lean`.
- The solution in (ii) is built in `ODE/Existence.lean`.

### Proposition A4 (General Distributions with θ known)

At a fixed history: if `κ ≤ κck` there is a fully revealing equilibrium satisfying `D1^∞`; if
`κ > κck` every such equilibrium is fully pooling. Hence an equilibrium satisfying `D1^∞` with
social learning about preferences exists iff `κ ≤ κck`.

- Fixed history: `CC.General.propA4_revealing` and `CC.General.propA4_pooling`, in
  `General/Quadratic.lean`.
  - **From the proof:** the revealing equilibrium has the form `a(v) = μ(h) + Φ(v − μ(h))`
    for a single strictly increasing `Φ`. The same `Φ` works at every history, whatever the norm
    and the type distribution.
- Across histories, as stated: `CC.Learning.propA4_learning_exact`, in `Learning/NoLearning.lean`,
  with the paper's definition of social learning.
  - Types are `v_t = μ + ν_t`, with `ν_t` i.i.d. with mean zero. `μ` has a finite mean and is not
    almost surely constant, which its positive prior variance gives.
  - If `κ ≤ κck` there is an equilibrium satisfying `D1^∞`, fully revealing at every history, in
    which social learning occurs. If `κ > κck` every equilibrium satisfying `D1^∞` is fully
    pooling at every history and social learning does not occur.
  - In the pooling direction the hypothesis allows any type distribution at each history.
  - In the revealing direction, Lean shows that the rule is an equilibrium of every period game
    with these losses, whatever the norm and the type distribution. The paper assumes that the
    distribution of `v_t` at each history has a positive continuous density and finite variance,
    so that each history gives such a period game.
- At each realized history: `CC.Learning.propA4_period_games`, in `Learning/PeriodGames.lean`. At
  every realized history where the paper's assumption holds, the rule is an equilibrium satisfying
  `D1^∞` of the period game with the conditional law of `v_t` given `h^t` as type distribution and
  `μ(h^t)` as norm, and social learning occurs.
  - The paper's assumption holds at almost every realized history when `ν_t` has a bounded,
    continuous, everywhere-positive density and `μ` and `ν_t` have finite variances
    (`CC.Learning.typeLaw_regular`), because the conditional law of `v_t = μ + ν_t` is the
    convolution of the posterior about `μ` with the law of `ν_t`. This covers the log-concave and
    Gaussian cases the paper mentions.
  - `CC.Learning.propA4_exists_density` and, in the Linear-Gaussian model,
    `CC.Learning.propA4_exists_gaussian` then give the equilibrium with no assumption left on the
    conditional laws.
- A stronger version, `CC.Learning.propA4_learning` (`Learning/Assembly.lean`), shows that for
  `κ > κck` social learning fails: for almost every realization, `μ(h^t)` does not converge to
  `μ`. This needs `μ ≠ E μ` almost surely, and it assumes that the law of `μ` is atomless.
- **From the proof:** `CC.Learning.learning_revealing`, `CC.Learning.not_learning_pooling` and
  `CC.Learning.learning_pooling`, in `Learning/Basic.lean` and `Learning/NoLearning.lean`.
  - If every period plays the revealing rule, the history reveals the past types and
    `μ(h^t) → μ` almost surely.
  - If every period pools, the history is uninformative: `μ(h^t) = E μ`, so social learning does
    not occur (and fails if `μ` is atomless).
- With the weights `γ_t` in the public history: `CC.Learning.propA4_weights`, in
  `Learning/Weights.lean`. Here strategies may condition on the weights, and in the revealing
  direction the norm is shown to be the posterior mean given the history including the weights.
  The pooling direction assumes the profile is jointly measurable, so that the posterior given
  the history is well defined.

### Remark A1

In the common-knowledge benchmark with `κ > κck`, every equilibrium satisfying `D1^∞` is fully
pooling.

- Lean: `CC.General.remarkA1`, in `General/Quadratic.lean`, for any type distribution with an
  everywhere-positive continuous density and the norm at 0.

### Corollary A2 (Signaling Equilibrium with θ known)

- Lean: `CC.corollaryA2`, in `Corollaries/KnownTheta.lean`, with prior covariance
  `diag(0, σ²_μ)`.
  - Social learning about preferences (`σ²_μ,t → 0`) occurs iff `κ ≤ κck`, whatever the weights.
  - If `κ > κck`, then `σ²_μ,t = σ²_μ` at every date.
  - Both asymptotic objects are given in closed form, with the formulas in the paper's proof:
    the adaptation loss is weakly decreasing in `κ` and the utility is strictly decreasing.
  - Along any sequence of period signaling equilibria, the expected adaptation payoff and the
    expected utility converge to these values.
- The asymptotic adaptation loss and utility as in Definition A2 (limits of unconditional
  expectations in the dynamic model): `CC.Bridge.corollaryA2_asymptotic`, in
  `Bridge/Asymptotic.lean`, for the expectations `CC.Bridge.expAdapt` and `CC.Bridge.expUtility`.
  As in Definition A2, the adaptation loss carries a negative sign. The expected conformity term
  uses the public's posterior about `v_t`, the conditional law of `v_t` given `(h^t, a_t)`.
- Social learning with the paper's definition: `CC.Bridge.corollaryA2_socialLearning`, in
  `Bridge/Corollaries.lean`, for any law of the weights. It occurs if `κ ≤ κck` and fails if
  `κ > κck`.
- In every signaling equilibrium of the dynamic game: `CC.LinearPaths.corollaryA2_signalingProfile`
  and `CC.LinearPaths.corollaryA2_asymptotic_profile`.

### Proposition A5 (General Distributions with μ known)

**The fixed-history statements.** `General/KnownMu.lean`.

- `CC.General.propA5_period`:
  - If `κ · m''/2 ≤ κck` everywhere (that is, `κ ≤ κck/m̄`), there is a fully revealing
    equilibrium satisfying `D1^∞`.
  - If `κ · m''/2 ≥ c` everywhere for some `c > κck` (that is, `κ > κck/m̲`), every equilibrium
    satisfying `D1^∞` is fully pooling.
  - The period game has type `ṽ_t`, quadratic adaptation loss, and conformity loss
    `κ(m − m(x*))`.
- **From the proof:** `CC.General.propA5_minimizer` shows that `m'(· | h^t)` has a unique zero
  `x*(h^t)`. It uses the symmetry and finite third moment of `v_t`, and that `ṽ_t` has a density.
  The footnote to the assumptions states that they imply this.

**The claims across histories** (the last two sentences of the proposition). Folder
`LearnTheta/`.

- The model is in `LearnTheta/Defs.lean`.
  - `θ`, the noises `ε_t` and the shocks `v_t` are independent coordinates of the sample space.
  - `Y_t = E(θ | h^t, s_t)` is Mathlib's conditional expectation.
  - The type is `ṽ_t = v_t + Y_t`.
- `CC.LearnTheta.propA5_revealing_every_history`: if `κ ≤ κck`, then at every history where
  `m(· | h^t)` is C² with `0 < m'' ≤ 2`, the period game has a fully revealing equilibrium
  satisfying `D1^∞`.
- `CC.LearnTheta.propA5_learning`: in every strategy profile that is fully revealing at every
  history, `θ(h^t) → θ` almost surely. `CC.LearnTheta.propA5_learning_def`
  (`LearnTheta/SocialLearning.lean`) states the same with the paper's definition of social
  learning: for almost every realization `r` of `θ`, `θ(h^t) → r` in probability conditional on
  `θ = r`.
- `CC.LearnTheta.propA5_pooling`: suppose `κ > κck` and the profile is an equilibrium satisfying
  `D1^∞` with `E((a_t − ṽ_t)² | h^t)` bounded. Then almost surely the probability given `h^t`
  that player t chooses the central pool's action converges to one. The theorem names, at each
  history, the period game, the cutoffs of its central pool and the pool's action
  (`Setting.IsCentralPoolingWith`).
  As in the manuscript, the result applies to profiles along which `m(· | h^t)` is regular: the
  hypothesis that the period game at each realized history is a `Setting` with conformity loss
  `κ(m − m(x*))` includes that `m(· | h^t)` is C² and strictly convex there.
- **From the proof:** the Claim is `CC.LearnTheta.propA5_claim`, in `LearnTheta/Assembly.lean`,
  stated as in the paper: almost surely, if `q_t^+` or `q_t^-` does not converge to zero, then
  `θ(h^t) → θ` and `Var(θ | h^t) → 0`. It holds for every measurable profile with monotone period
  strategies and central pools, so in every equilibrium satisfying `D1^∞`. The step from `q_t^±`
  to a fixed threshold is `frequently_reveal_hi` and `frequently_reveal_lo`. The core is
  `CC.LearnTheta.ClaimSetup.claim_upper` and `claim_lower`, in `LearnTheta/Claim.lean`, stated for
  an abstract filtration: when decisions infinitely often reveal whether `ṽ_t` lies above (or
  below) a fixed threshold, `θ(h^t) → θ` and `Var(θ | h^t) → 0` almost surely.

How these relate to the paper:

- "At every history" means at almost every realized history.
- The period game at `h^t` has the conditional law of `ṽ_t` given `h^t` as type distribution,
  and `κ(m(· | h^t) − min m)` as conformity loss.
- Lean writes `m` with Bayes' rule, as
  `m(x | h^t) = ∫(x−y)²ψ(x−y) dη(y) / ∫ψ(x−y) dη(y)` (`mfun`). Here `η` is the conditional law
  of `Y_t` given `h^t` and `ψ` is the density of `v_t`. `CC.LearnTheta.mfun_condExp`
  (`LearnTheta/MVersion.lean`) proves that this formula, evaluated at the realized history and
  type, equals `E(v_t² | h^t, ṽ_t)` almost surely.
- Assumptions used: `θ` has finite variance; `v_t` is symmetric with finite third moment and a
  positive, bounded, continuous density; the `ε_t` are i.i.d.
- The equilibrium of the first claim: `CC.LearnTheta.propA5_exists`, in `LearnTheta/Exists.lean`.
  There is a measurable strategy profile that, at almost every realized history, is a fully
  revealing equilibrium satisfying `D1^∞` of the period game at that history, and social
  learning about fundamentals occurs in it (paper's definition).
  - At each history it plays `revealSel κ ψ η` (`LearnTheta/Select.lean`), a fully revealing
    equilibrium chosen measurably in the public belief `η` about `Y_t`
    (`CC.LearnTheta.measurable_revealSel`, `CC.LearnTheta.revealSel_spec`). It is built from the
    explicit solution of the tail differential equation (Lemma A3(ii)).
  - The hypothesis `hm` is the paper's assumption that `m(· | h^t)` is regular along fully
    revealing play: it holds at almost every realized history of every measurable profile that is
    fully revealing before date `t`.
- In the Linear-Gaussian model (`θ ~ N(0, σ²)`, `ε_t, v_t ~ N(0, 1)`) that assumption is a theorem,
  so all the hypotheses of `propA5_exists` hold: `CC.LearnTheta.propA5_exists_gaussian`, in
  `LearnTheta/GaussianFilter.lean`. Along fully revealing play the public's belief about `Y_t` is
  Gaussian (`CC.LearnTheta.beliefY_gaussian`), so `m(· | h^t)` is quadratic with `0 < m'' ≤ 2`
  (`CC.LearnTheta.hm_gaussian`).

### Corollary A3 (Signaling Equilibrium with μ known)

- Lean: `CC.corollaryA3`, in `Corollaries/KnownMu.lean`, with prior covariance `diag(σ²_θ, 0)`
  and `γ_t = 1`.
  - Social learning about fundamentals (`σ²_θ,t → 0`) occurs iff `κ ≤ κck`.
  - For `κ > κck` the limit of `σ²_θ,t` is positive and weakly increasing in `κ`.
  - The asymptotic adaptation loss is weakly decreasing in `κ`, and the asymptotic utility is
    strictly decreasing. Both are the limits along any sequence of period signaling equilibria.
- The asymptotic adaptation loss and utility as limits of unconditional expectations in the
  dynamic model: `CC.Bridge.corollaryA3_asymptotic`, in `Bridge/Asymptotic.lean`.
- Social learning with the paper's definition: `CC.Bridge.corollaryA3_socialLearning`, in
  `Bridge/Corollaries.lean`. It occurs if `κ ≤ κck` and fails if `κ > κck`.
- In every signaling equilibrium of the dynamic game: `CC.LinearPaths.corollaryA3_signalingProfile`
  and `CC.LinearPaths.corollaryA3_asymptotic_profile`.
- **From the proof:** the closed form of `m` is `CC.LearnTheta.mfun_gaussian`, in
  `LearnTheta/GaussianM.lean`, and `CC.LearnTheta.m_closed_form` states it in the model with
  `θ(h^t)` as the center, along fully revealing play. Its second derivative is `2 s̃(h^t)²`
  (`CC.LearnTheta.mfun_gaussian_sens`), which is decreasing in `σ²_θ,t`
  (`CC.LearnTheta.secondDeriv_antitone`).

### Proposition A6 (Generalized Learning)

(i) Under the pooling condition, every equilibrium satisfying `D1^∞` is fully pooling at every
history and social learning about preferences fails. (ii) Under the revelation condition, there
is an equilibrium satisfying `D1^∞` with `μ(h^t) → μ` almost surely.

- Fixed history: `CC.General.propA6_i_period` and `CC.General.propA6_ii_period`, in
  `General/GeneralLoss.lean`.
  - **From the proof:** the equilibrium in (ii) has the form `μ(h) + Φ(v − μ(h))` for a single
    `Φ` that works at every history.
- Across histories: `CC.Learning.propA6`, in `Learning/Assembly.lean`.
  - `μ` has an atomless law with finite mean; the paper assumes finite variance, which Lean
    does not need.
  - `ν_t` has mean zero.
  - In (ii), as in Proposition A4, the rule is shown to be an equilibrium of every period game
    with these losses.
- At each realized history: `CC.Learning.propA6_period_games`, in `Learning/PeriodGames.lean`. At
  every realized history where the paper's assumptions hold, the rule in (ii) is an equilibrium
  satisfying `D1^∞` of the period game with the conditional law of `v_t` given `h^t` as type
  distribution and `μ(h^t)` as norm. `CC.Learning.typeLaw_regular` gives the density assumption
  when `ν_t` has a suitable density; that `f(v_t - μ(h^t))` has a finite expectation given `h^t`
  remains an assumption, as in the paper.
- With the weights `γ_t` in the public history: `CC.Learning.propA6_weights`, in
  `Learning/Weights.lean`.
- For losses not normalized at zero: `CC.Learning.propA6_unnormalized`, in
  `Learning/Normalization.lean`.

## Examples

`Examples/` and `CC.LearnTheta.propA5_exists_gaussian` check that the following hypotheses can be
met:

- The weights `γ_t` uniform on `[0,1]` have full support.
- There are laws of `κ_t` on each side of `κck` for Proposition A1, and `γ_t = |N(0,1)|` for
  Proposition A2.
- The quadratic environment with standard normal types is a valid general-loss setting.
- The common-knowledge game has both revealing and pooling signaling equilibria, depending on
  `κ`.
- There is a valid fixed-history environment for Proposition A5, and the Linear-Gaussian model
  meets every hypothesis of its across-history existence theorem. It also meets every assumption
  on the conditional laws in Proposition A4 (`CC.Learning.propA4_exists_gaussian`).
- Quadratic losses satisfy each of the two conditions of Proposition A6
  (`CC.Examples.propA6_pooling_example`, `CC.Examples.propA6_revealing_example`).
- The hypotheses of Proposition 4 can be met.
