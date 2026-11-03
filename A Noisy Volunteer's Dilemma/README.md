# Lean verification of "A Noisy Volunteer's Dilemma"

Machine-checked proofs, in Lean 4 with Mathlib, of the labelled results in the manuscript, including the Online Appendix. This README explains where each result is and how the Lean version differs from the manuscript.

**Bottom line.** No result had to be weakened or changed in substance. The Lean proofs follow the manuscript's routes. Section 4 lists the remaining differences, found by comparing each proof with the manuscript, and none is major.

| Item | Contents |
|---|---|
| [`current.pdf`](current.pdf) | The manuscript |
| [`lean proofs/`](lean%20proofs/) | One Lean project, with one library, `NoisyVD` |
| `lean proofs/NoisyVD/` | Main text and Appendices A–C. Statements are in [`Main.lean`](lean%20proofs/NoisyVD/Main.lean) |
| `lean proofs/NoisyVD/OnlineAppendix/` | Online Appendix. Statements are in [`OnlineAppendix/Main.lean`](lean%20proofs/NoisyVD/OnlineAppendix/Main.lean) |

## 1. Verification status

- There is no `sorry`, and no axioms are declared.
- Building the project prints an axiom audit of 66 theorems. Each depends only on `propext`, `Classical.choice` and `Quot.sound`, Lean's standard foundations.
- All 35 modules pass an independent replay through the Lean kernel (`leanchecker`).

To check a result, read its statement in one of the two `Main.lean` files and the definitions it uses (Section 3). Lean checks the proof, but a person still has to check that the statement says what the paper says.

## 2. Where each result is

Rebuild from the `lean proofs` folder, after installing [elan](https://github.com/leanprover/elan), the Lean toolchain manager:

```
export PATH="$HOME/.elan/bin:$PATH"     # the elan toolchain manager lives in ~/.elan
lake exe cache get                      # on a fresh checkout: downloads the prebuilt Mathlib
lake build                              # about 5 minutes from scratch; ends with the axiom audit
```

The toolchain is pinned to Lean 4.35.0 and Mathlib v4.35.0. For the kernel replay, run `lake env leanchecker NoisyVD.<Module>` one module at a time. Passing all modules in one call can run out of memory.

File names below are relative to `lean proofs/NoisyVD/`. Numbers are those in `current.pdf`. TeX labels are the manuscript's internal LaTeX labels, which the comments in the Lean code use to refer to results; `current.tex` in those comments is the manuscript's LaTeX source.

### Main text and Appendices A–C

Namespace `NoisyVD`; statements are in `Main.lean`.

| Paper | TeX label | Lean name | Proof file |
|---|---|---|---|
| Proposition 1 | `prop_no_clueless` | `Proposition1`, `Proposition1_limit`, `Proposition1_cutoff` | `Benchmarks`, `Fidelity` |
| Remark after Prop. 1 and Section 6: limit payoff `Π^FB - π ν̲` | | `BenchmarkPayoffLimit` | `Benchmarks` |
| Proposition 2 | `prop_noise_threshold` | `Proposition2`, `Proposition2_exists` | `Benchmarks`, `Fidelity` |
| Assumption 1 | `assumption_noise` | the definition `Env.Noise` | `Model` |
| Lemma 1 | `lemma_noise` | `Lemma1` | `Model` |
| Lemma 2 | `lemma_pivotal` | `Lemma2` | `Binomial`, `Model` |
| Equation (8) | `eq_derivative` | `EqDerivative` | `Main` |
| Proposition 3 | `prop_volunteers` | `Proposition3` | `Volunteer` |
| Proposition 4 | `prop_general_failures` | `Proposition4`, `Proposition4_real_subsets` | `GeneralUpper`, `FirstBest` |
| Lemma A1 | `lemma_threshold_value` | `LemmaThresholdValue` | `ThresholdAsymp`, `ThresholdUpper`, `ThresholdLower` |
| Lemma A2 | `lemma_threshold_cutoff` | `LemmaThresholdCutoff` | `Cutoff` |
| Proposition B1 | `prop_monotone` | `PropositionB1` | `Micro`, `Fidelity` |
| Remark 1 | `remark_ex_post` | `Remark1` | `Micro` |
| Proposition B2 | `prop_tie_breaking` | `PropositionB2` | `Micro`, `Fidelity` |
| Lemma C1 | `lemma_binomial_overlap` | `LemmaBinomialOverlap` | `Overlap` |
| Lemma C2 | `lemma_symmetric_equilibrium_exists` | `LemmaEquilibriumExists` | `Existence` |
| Lemma C3 | `lemma_local_binomial` | `LemmaLocalBinomial`, `LemmaLocalBinomial_massBound` | `BerryEsseen`, `LocalLimit`, `LocalBinomial` |
| Berry–Esseen Theorem, as cited in Lemma C3 | | `BerryEsseen` | `BerryEsseen` |
| Equation (34) | `eq_be` | `EqBe` | `BerryEsseen` |

Claims made in the prose of Appendix B are also proved.

| Claim | Lean name | File |
|---|---|---|
| Behavioral types imply Lemma 1 | `behavioral_noise` | `Micro` |
| Noisy communication implies Lemma 1; the `(2p-1)` scaling | `noisyComm_noise`, `noisyComm_incentive`, `noisyComm_band`, `noisyComm_zero_cost` | `Micro` |
| Both are the main model with `F̃(c) = w₁ + w F(g c)` near zero, with the same attainable payoffs | `Env.microPayoffs_eq`, `Env.mix_F` | `Transfer` |
| Hence the payoff results apply to them, without Assumption 1 on `F` | `Env.micro_prop` | `Transfer` |
| The threshold claim applies to them too, at `F̃` | `VD.micro_threshold_iff` | `Fidelity` |
| With biased individuals, the upper bounds hold over monotone rules and equilibria without weakly dominated actions | `VD.biased_upper` | `Biased` |

### Online Appendix

Namespace `NoisyVD.OA`; statements are in `OnlineAppendix/Main.lean`, and proof files are in `OnlineAppendix/`.

| Paper | TeX label | Lean name | Proof file |
|---|---|---|---|
| Proposition D1 | `prop_state_dependent` | `PropositionStateDependent` | `StateDependent` |
| Equation (D.1) | `eq_sd_band` | `EqSdBand` | `StateDependent` |
| Equation (D.2) | `def_worst_equilibrium_payoff` | the definitions `Env.PiW`, `Env.PiWT` | `WorstCase` |
| Proposition D2 | `prop_worst_equilibrium` | `PropositionWorstEquilibrium` | `WorstCase` |
| Equation (D.3) | `eq_worst_equilibrium_sandwich` | `EqWorstSandwich` | `WorstCase` |
| Equation (D.4) | `eq_vd_fixed_point` | `EqVdFixedPoint` | `WorstCase` |
| The limit `Π^SQ + J(t)` and the properties of `J`, in the proof of D2 | | `WorstCaseLimit`, `WorstCaseCutoff` | `WorstCase` |
| Proposition D3 | `prop_noisy_signals` | `PropositionNoisySignals` | `NoisySignals` |
| Equation (D.5) | `eq_noisy_signal_reporting_band` | `EqNoisySignalBand` | `NoisySignals` |
| Equations (D.6), (D.7) | `eq_general_message_utility`, `eq_general_message_payoff` | the definitions `MsgGame.netU`, `MsgGame.Pi` | `Messages` |
| Assumption 2 | `assumption_noisy_recording` | the structure `RecordingData` | `NoisyRecording` |
| Equation (D.8) | `general_message_upper_bound` | `EqGeneralMessageUpperBound` | `NoisyRecording` |
| Remark 2 | `remark_continuum_message_noise` | `RemarkContinuumTwoMessages`, `RemarkContinuumTwoEquilibrium`; a further result is `RemarkContinuumMessages` | `Remarks` |
| Remark 3 | `remark_finite_message_noise` | `RemarkFiniteMessages` | `Remarks` |
| Lemma D1 and equation (D.9) | `lemma_anonymous_influence`, `eq_anonymous_influence` | `LemmaAnonymousInfluence`, `AnonymousInfluenceMean` | `ProductMeasure`, `NoisyRecording` |
| The ratios `w_m` and `0 ≤ w_m ≤ Λ`, in that proof | | `LikelihoodRatios` | `NoisyRecording` |
| Equation (D.11) | `eq_background_bounds` | `EqBackgroundBounds` | `NoisyRecording` |
| Equations (D.12), (D.13) | `eq_mean_weight`, `eq_anonymous_reweighting` | steps `hw1`, `hW1`, `hUW` inside `anon_bound_of_density` | `ProductMeasure` |
| Equation (D.14) | `eq_rational_nonnull_message_bound` | `EqRationalNonnullBound` | `Messages` |
| Equation (D.15) | `eq_likelihood_ratio_bound` | `EqLikelihoodRatioBound`, an inequality between measures | `Messages` |
| Proposition D4 | `prop_general_message_upper_bounds` | `PropositionGeneralMessage` | `MessageBounds`, `NoisyRecording` |

Claims made in the prose of the Online Appendix are also proved.

| Claim | Lean name | File |
|---|---|---|
| If `s_i` is independent of `ω`, then `Π^G(n) = Π^SQ` for every `n`, so Statement 4 of Prop. 4 need not extend | `Signal.Pi_of_uninformative`, `Signal.not_tendsto_PiFB_of_uninformative` | `NoisySignals` |
| Assumption 2 is satisfied by a truncated-normal recording error | `Examples.truncatedNormal` | `Fidelity` |

## 3. How the model is written in Lean

Read these definitions when checking that a statement says what the paper says.

| Paper | Lean | File |
|---|---|---|
| `u^p`, the prior, the law of `ν_i` | the structure `Env A Ω` | `Model` |
| `F(x)`, `F(x⁻)` | `Env.F`, `Env.Fm` | `Model` |
| `B`, `ε_*`, `M = √2 B C` | `Env.B`, `Env.epsStar`, `Env.pivConst` | `Model` |
| Decision rule `d`; threshold rule | `Rule A`; `thresholdRule` | `Model` |
| Symmetric strategy `σ(ω, x)` | the structure `Strat Ω` | `Model` |
| `Pr(r_i = 1 ∣ ω)`, gross benefit `Δ` | `Env.rp`, `Env.gross` | `Model` |
| Symmetric Bayesian Nash equilibrium | `Env.IsEq` | `Model` |
| `E_{e,d}[u^p]`, `Π(n)`, `Π^T(n)`, `Π^SQ`, `Π^FB` | `Env.payoff`, `Env.Pi`, `Env.PiT`, `Env.PiSQ`, `Env.PiFB` | `Model` |
| `Pr(Bin(m,p) = k)`, `≤ y`, `≥ T`, the pivotal probability | `bpmf`, `bcdf`, `btail`, `rho` | `Binomial`, `BerryEsseen`, `ThresholdAsymp` |
| `φ`, `Φ` | `phi`, `Phi` | `Gaussian` |
| `V(t)`, `𝒰(t)`, `W`, `τ`, `F̄_0` | `Vval`, `feasible`, `Wval`, `tau`, `Fbar` | `Cutoff` |
| `H`, `L`, `π`, maintained assumptions of Section 4 | `VD.H`, `VD.L`, `VD.pr`, `VD.Assumptions` | `VD` |
| `p_n^±`, `β_n = 1 - TV` | `Env.pMinus`, `Env.pPlus`, `tv` | `GeneralUpper`, `Overlap` |
| State-dependent costs | the structure `SDEnv` | `OnlineAppendix/StateDependent` |
| `Π̲_n`, `Π̲^T_n`, `J`, `F̲_0` | `Env.PiW`, `Env.PiWT`, `Jfun`, `Fworst` | `OnlineAppendix/WorstCase` |
| Signals `G`, `Δ_n(s)`, `Π^G(n)` | a Markov kernel `G`, `Signal.interim`, `Signal.Pi` | `OnlineAppendix/NoisySignals` |
| Message game, `P_ω`, `P⁰`, `U_{n,ω}(m)`, `q_{n,ω}`, `Π^M(n)` | `MsgGame`, `MsgGame.obs`, `MsgGame.baseObs`, `MsgGame.U`, `MsgGame.q`, `MsgGame.Pi` | `OnlineAppendix/Messages` |
| The paper's `𝒳 = {∅} ∪ [0,1]`, `Λ`, `p_ω`, `w_m` | `NoisyModel`, `NoisyModel.Lam`, `NoisyModel.exists_obs_density`, `NoisyModel.wRatio` | `OnlineAppendix/NoisyRecording` |

The binomial formulas in these definitions are derived from the underlying game. [`Game.lean`](lean%20proofs/NoisyVD/Game.lean) proves that `IsEq` is exactly expected-utility best response against i.i.d. opponents (`Env.isEq_iff_bestResponse`), and that the payoff is the expectation over report profiles (`Env.payoff_eq_profile`). The same holds for the extensions (`SDEnv.isEq_iff_bestResponse`, `SDEnv.payoff_eq_profile`, `Signal.isEq_iff_bestResponse`, `Signal.payoff_eq_profile`).

Further cross-checks are in the two `Fidelity` files and in `Example`:

- `phi` and `Phi` are Mathlib's standard Gaussian (`phi_eq_gaussianPDFReal`, `Phi_eq_cdf`).
- `Fm` is the left limit of `F` (`Env.tendsto_F_left`), and `B` is an attained range (`Env.B_attained`).
- `Δ_n(s)` is the conditional expectation of `Δ_{n,ω}` given the signal (`Signal.integral_interim`).
- The hypotheses can be satisfied jointly (`Example.threshold_applies`, `Examples.sdCommon_F`, `Examples.sdDiff_F`).
- For one set of primitives, noisy recording gives `Π^M(n) = Π^SQ` for large `n`, while perfect recording gives `Π^M(n) ≥ Π^SQ + κ` for every `n ≥ 2` (`Examples.noisy_vs_perfect`).

## 4. Differences between the manuscript and the Lean proofs

### 4.1 How statements are written

None of these changes the substance of a result, and most cannot be removed because a formal statement has to be explicit where the paper uses standard shorthand.

| Manuscript | Lean | Why it does not matter |
|---|---|---|
| Prop. 1: "the unique symmetric equilibrium" | For `n ≥ 2` the cutoff is unique. The behavior of every type except the one exactly at the cutoff is pinned down in state 1, and every type with `x > 0` stays silent in state 0. | Types with zero probability can randomize freely, so literal uniqueness is false for any such model. These types do not affect any probability or payoff. |
| Prop. 2: costs have a density on `[ν̲, ν̄]` | Only `Pr(ν_i < ν̲) = 0` is assumed | This is weaker, so the theorem is stronger. |
| Equilibrium: best response | Every type in every state best responds, and strategies are jointly measurable, as Lemma C2 constructs. | Reading it as "almost every type in almost every state" leaves the attainable payoffs, and so `Π(n)`, unchanged (`Env.payoffs_ae_eq`). |
| Equilibrium with signals (Prop. D3) | Best response is required for almost every signal. | A posterior is unique only up to a null set of signals. This admits more equilibria, so the upper bounds are stronger, and the equilibrium attaining `Π^SQ` best responds at every signal. The band (D.5) then holds for almost every state. |
| Equilibrium with messages (Prop. D4) | A strategy is a Markov kernel, and in every state almost every cost type puts probability one on best replies. | Same reason. A rule is a Markov kernel invariant under permutations. |
| `A, Ω ⊆ ℝ` compact | `A` and `Ω` are nonempty compact Hausdorff second-countable spaces. | This is more general. `Proposition4_real_subsets` gives the literal case. It also implies `Ω` is standard Borel, which the posterior needs. |
| `d : {0,…,n} → Δ(A)` | `Rule A` is defined on all of `ℕ`. | Only values at `k ≤ n` affect anything. |
| `k_n(t)` with the integer floor | The natural-number floor | They agree for all large `n`. |
| `Π^FB > Π^SQ` maintained throughout | It is a stated hypothesis where used, including `Lemma2`, where it gives `B > 0` and so `M > 0`. In the Volunteer's Dilemma it follows from `VD.Assumptions`, which states `π > 0` directly; `VD.PiFB_sub_PiSQ` shows `Π^FB - Π^SQ = π H`. | These are equivalent encodings. |
| `F'_+(0)` | `HasDerivWithinAt F t (Ici 0) 0` | This is the definition of the right derivative. |
| `G(· ∣ ω)` | A Markov kernel, so measurable in `ω` | This is needed for the expectations to be defined. |
| Berry–Esseen with an unnamed universal constant `C_BE` | `C_BE = 52`, and only for Bernoulli sums | See Section 4.2. The formulas for `B_λ` and `C_λ` are the paper's. |
| Remark 2, qualitative: the two-message rule "effectively removes the noise and results in a non-noisy Volunteer's Dilemma with a threshold of two" | `RemarkContinuumTwoMessages`: when rational individuals send `m⋆` or `∅`, with `r = (1-ε) q_{n,ω}`, the payoff in state `ω` is `u(0,ω) + G(ω) Pr(Bin(n,r) ≥ 2)`, the gross benefit of `m⋆` is `G(ω) Pr(Bin(n-1,r) = 1)`, and other messages have the value of `∅` | These are the threshold-two formulas (`bexp_threshold`, `gross_threshold`), so this is one precise reading of the remark. `RemarkContinuumTwoEquilibrium` shows that an equilibrium of this form exists. |
| Remark 3 | Finite messages are modeled with no recording noise and a full-support mechanical law `χ`, and the property the remark names is `MsgGame.Dom`. | This is the case the remark describes. |

### 4.2 Where the proof routes still differ

Apart from the details below, the Lean proofs follow the manuscript's steps.

**Berry–Esseen (Lemma C3).** The paper cites the theorem, but Mathlib does not contain it, so `BerryEsseen.lean` proves it.

- It proves the case the paper uses, sums of i.i.d. Bernoulli variables, in the form `|Pr(X ≤ mp + zσ) - Φ(z)| ≤ C_BE E|ξ-p|³ / ((p(1-p))^{3/2} √m)`.
- The proof is Stein's method, specialized to the binomial. It uses an elementary ratio bound on the largest binomial mass, `bpmf_le_four_div_sqrt`, for the probability that `Bin(m-1,p)` lands in an interval of length one. Nothing else in the library uses that bound.
- Everything after the theorem is the paper's route. Equation (34) gives the mass bound with `C_λ = 1/√(2πλ(1-λ)) + 2B_λ`, by subtracting (34) at two adjacent points. It also gives the tail limit, by applying (34) at `z_n - 1/σ`.
- The local limit comes from Stirling's formula, as in the paper. Lean's Taylor bound `|(1+w) log(1+w) - w - w²/2| ≤ 4|w|³` has constant 4 rather than the paper's 1, and the proof needs no more.

**Uniform convergence (Lemmas A1, C3 and Prop. D2).** Where the paper says "uniformly", Lean often proves the uniform statement by contradiction along a sequence of violating parameters. This is the standard way to prove uniformity, and the estimates along the sequence are the paper's. `pivot_tail_uniform` is the uniform form of the paper's application of Lemma C3.

**Lemma A1.**
- *Upper bound:* the paper applies its argument to rules within `1/n` of `Π^T(n)` along a subsequence attaining the limsup. Lean takes a violating sequence for fixed `ε` and then makes the paper's extraction, in which `c_n` converges in the extended reals and both `y_{ω,n}` converge. The cases `c_n → ±∞` and `c_n → c ∈ ℝ` are the paper's. The rules "at least `T`" and "fewer than `T`" share one proof through a sign `g`, where the paper says the same proof works.
- *Lower bound:* the paper notes `Ψ_{ω,n} → f_ω` uniformly on a neighborhood. Lean proves pointwise convergence at the two endpoints of the IVT interval, which is all the IVT needs.
- *Density of regular pairs:* the paper uses that `f_1'` has finitely many zeros. Lean uses that `f'` cannot vanish on an interval, since then `u² = 1` on that interval.

**Prop. 2.** The paper bounds the benefit of a pivotal report by `H`. Lean does not assume `H > 0` or `L < 0`, so it uses `max(|H|, |L|) + 1`.

**Prop. 4, Statement 4.** The paper chooses any distinct `c_j` and `ρ` with disjoint intervals. Lean uses equally spaced `c_j` and `ρ = α/(10(K+1))`.

**Remark 1.** The paper separates the boundary cases, and says that when only one of `q¹` and `q⁰` lies in `{0,1}`, the likelihood ratio is weakly monotone on the on-path support. Lean has one single-crossing lemma that covers them (`single_crossing`), and its reason for that case is that a count with zero probability in one state reveals the other state. It reaches `q¹ < q⁰` by reflecting `k ↦ n - k`.

**Prop. D2.** `z_x(t)` is the value at `t x/σ²` of the inverse of `z ↦ z/φ(z)`, written `zz`, which is the bijection the paper names. Because `zz` is continuous at zero, Lean evaluates `J(0)` directly where the paper takes `t ↓ 0`.

**Prop. D4.**
- *Statement 3:* the paper says `F(0) = 0` and a finite right derivative give `q_{n,ω} ≤ C₁/√n`. Lean bounds `q_{n,ω}` by `F(M'/√n)` with `M' = M_G + 1`, and uses that `√n F(M'/√n)` converges.
- *The ratio `r_{n,ω}`:* it is obtained by Radon–Nikodym with the bound (D.15). The paper also only asserts its existence from that bound.
- *Two versions of Lemma D1:* `NoisyModel.anonymous_influence` uses the explicit `w_m`, as in the paper. `MsgGame.anon_influence` uses only `MsgGame.Dom`, which is what Remark 3 needs.

**Shared arguments.** The paper says that the proofs of Props. D1 and D3 reuse Statements 1–3 of Prop. 4 because they use only `p_{n,ω} ∈ [p_n^-, p_n^+]`. In Lean that reuse is the structure `BandFamily` in `GeneralUpper`, with the paper's endpoints in each case.

### 4.3 Some results hold under weaker hypotheses

`Main.lean` states the results as in the paper; the underlying theorems carry the weaker hypotheses.

- Statement 3 of Props. 3 and 4 uses only differentiability at zero, not `F'(0) > 0`.
- Statement 4 of Prop. 4 does not use Assumption 1 (`Env.prop_general_4`).
- Lemma A1 needs only that `F` is continuous near zero and differentiable at zero (`VD.Smooth`), not continuously differentiable. The same holds for `tendsto_worst_ceil` in Prop. D2.
- Prop. 1 allows `ν̲ = 0`.
- Prop. 2 does not use the upper end of the support, `H > ν̲`, or the prior inequality.
- Everything about message spaces uses one condition, `MsgGame.Dom Λ`: each recorded law is at most `Λ ε` times the law of the noise. The paper's `Λ` satisfies it (`NoisyModel.dom`), and so does `(ε χ̲)⁻¹` for finite messages (`finite_dom`).
- Statements 1 and 2 of Prop. D4 do not use `Π^FB > Π^SQ` (`MsgGame.statement1`, `MsgGame.statement2`).
- Statement 3 of Props. D2, D3 and D4 does not use a positive derivative at zero (`Env.worst_statement3`, `Signal.statement3`, `MsgGame.statement3`).
- Statements 1–3 of Prop. D2 hold in the general model, not only the Volunteer's Dilemma (`Env.worst_statement1`, `Env.worst_statement2`, `Env.worst_statement3`).
- `Signal.Pi_of_uninformative` does not use Assumption 1.

### 4.4 Not formalized

These are prose or numerics rather than stated results.

- The numerical example and Figure 1.
- The heuristic limit `eq_limit_probas`.
- Literature comparisons, the policy discussion, and footnote asides.
- The summary of extensions in Subsection `subsec_extensions_summary`, which restates results above.
- The sentence after Remark 2 about relying on common knowledge.

## 5. File map

Main text and Appendices A–C, in `lean proofs/NoisyVD/`:

| File | Contents |
|---|---|
| `Binomial` | Binomial mass function, mode, Lemma 2's summation by parts, Chebyshev, derivative identity |
| `Gaussian` | `φ` and `Φ` |
| `BerryEsseen` | Mills' ratio, the Stein solution, the Berry–Esseen Theorem, equation (34), the mass bound with `C_λ`, the tail estimate |
| `LocalLimit` | De Moivre–Laplace local limit from Stirling |
| `LocalBinomial` | Lemma C3 in the paper's form |
| `Overlap` | Total variation, affinity, Lemma C1 |
| `Model` | The model, Lemmas 1 and 2, the decomposition behind Prop. 4 |
| `Existence` | Measurable selection, Lemma C2 |
| `GeneralUpper`, `FirstBest` | Prop. 4 |
| `Cutoff` | Lemma A2 |
| `ThresholdAsymp`, `ThresholdUpper`, `ThresholdLower` | Lemma A1 |
| `VD`, `Volunteer` | The Volunteer's Dilemma, Prop. 3 |
| `Benchmarks` | Props. 1 and 2 |
| `Micro`, `Transfer`, `Biased` | Appendix B |
| `Game` | Bridge from the strategic-form game to the reduced form |
| `Example` | Satisfiability example |
| `Fidelity` | Cross-checks of definitions, almost-everywhere equilibrium, more direct forms of Props. 1, 2, B1, B2 |
| `Main` | Statements by paper label, axiom audit |

Online Appendix, in `lean proofs/NoisyVD/OnlineAppendix/`:

| File | Contents |
|---|---|
| `Common` | Reporting probabilities as strategies, cutoff bands, Chebyshev for separated reporting probabilities |
| `StateDependent` | The model with `F_ω`, Prop. D1 |
| `WorstCase` | The sandwich, `J` and `F̲_0`, the limit under `⌈ns⌉`, Prop. D2 |
| `NoisySignals` | The model with signals, the band, Prop. D3, uninformative signals |
| `ProductMeasure` | Densities, products of tilted measures, the anonymous-influence bound, second-moment and inverse-moment comparisons |
| `Messages` | `MsgGame`, the domination condition, the bound on `q`, the likelihood-ratio bound |
| `MessageBounds` | The three statements of Prop. D4 for any game satisfying the domination condition |
| `NoisyRecording` | The paper's `𝒳`, `RecordingData`, `Λ`, `p_ω`, `w_m`, Lemma D1 |
| `Remarks` | Remarks 2 and 3 |
| `Fidelity` | Bridges to the underlying games, conditional expectation, satisfiability examples, truncated normal |
| `Main` | Statements by paper label, axiom audit |
