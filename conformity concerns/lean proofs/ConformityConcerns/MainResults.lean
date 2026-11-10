import ConformityConcerns.PeriodGame.CommonKnowledge
import ConformityConcerns.PeriodGame.Instance
import ConformityConcerns.Dynamics.Equilibrium
import ConformityConcerns.Bridge.Prop2
import ConformityConcerns.Bridge.Beliefs
import ConformityConcerns.Interventions.Fragility
import ConformityConcerns.Interventions.PoolingShift
import ConformityConcerns.Corollaries.KnownTheta
import ConformityConcerns.Corollaries.KnownMu
import ConformityConcerns.General.CentralPooling
import ConformityConcerns.General.Quadratic
import ConformityConcerns.General.GeneralLoss
import ConformityConcerns.General.KnownMu
import ConformityConcerns.Learning.Assembly
import ConformityConcerns.LearnTheta.Assembly
import ConformityConcerns.LearnTheta.SocialLearning
import ConformityConcerns.LearnTheta.MVersion
import ConformityConcerns.Learning.NoLearning
import ConformityConcerns.Bridge.Corollaries
import ConformityConcerns.Gaussian.Conditioning
import ConformityConcerns.ODE.LeftTail
import ConformityConcerns.Examples.General
import ConformityConcerns.Examples.Dynamics
import ConformityConcerns.Examples.Interventions
import ConformityConcerns.Examples.Nonvacuity
import ConformityConcerns.BridgeK.PropA1
import ConformityConcerns.BridgeK.Prop3
import ConformityConcerns.BridgeK.Beliefs
import ConformityConcerns.BridgeK.Hist
import ConformityConcerns.LearnTheta.Exists
import ConformityConcerns.D1Compact.Note
import ConformityConcerns.D1Compact.RealLine
import ConformityConcerns.LinearPaths.Beliefs
import ConformityConcerns.Shifted.Period
import ConformityConcerns.Shifted.Dynamics
import ConformityConcerns.Shifted.Bridge
import ConformityConcerns.Shifted.Interventions
import ConformityConcerns.Bridge.Asymptotic
import ConformityConcerns.Interventions.PriorCov
import ConformityConcerns.BridgeK.Prop3Prior
import ConformityConcerns.BridgeK.Signaling
import ConformityConcerns.BridgeK.Profile
import ConformityConcerns.LinearPaths.Signaling
import ConformityConcerns.Bridge.AsyAux.SLFails
import ConformityConcerns.LearnTheta.GaussianM
import ConformityConcerns.LearnTheta.GaussianFilter
import ConformityConcerns.Learning.Weights
import ConformityConcerns.Learning.Normalization
import ConformityConcerns.Learning.PeriodGames

/-!
# Main results of "Conformity Concerns: A Dynamic Perspective": index and axiom check

| Paper | Lean |
|---|---|
| Proposition 1 (Commonly Known Environment) | `CC.LG.prop1`, `CC.LG.prop1_threshold` |
| Lemma 1 | `CC.LG.lemma1`, `CC.LG.signalingEq_char` |
| Corollary 1 | `CC.LG.corollary1`, `CC.LG.slope_root_iff` |
| Lemma 3 | `CC.LG.lemma3`; last claim (beliefs Gaussian on path): `CC.Bridge.beliefs_gaussian` |
| Lemma 3, last claim, any linear profile | `CC.LinearPaths.beliefs_gaussian_of_linear`, `CC.LinearPaths.lemma3_onPath`, `CC.LinearPaths.beliefs_gaussian_of_linear_param` |
| Proposition 2 (Characterization of Social Learning) | `CC.Bridge.prop2_socialLearning` (paper's definition), `CC.prop2` (posterior variances), `CC.Bridge.histSigma_eq` |
| Proposition 2, first paragraph of the proof | `CC.Bridge.socialLearning_theta_iff`, `CC.Bridge.socialLearning_mu_iff`, `CC.Bridge.socialLearning_theta_fails`, `CC.Bridge.socialLearning_mu_fails` |
| Signaling equilibrium of the dynamic game (Definition 1) | `CC.LinearPaths.IsSignalingProfile`, `CC.LinearPaths.exists_signalingProfile`, `CC.LinearPaths.signalingProfile_act`, `CC.LinearPaths.signalingProfile_post_ae`, `CC.LinearPaths.eqForm_signaling`, `CC.LinearPaths.signaling_ae_eqForm` |
| Same, with heterogeneous `κ_t` and disclosures | `CC.BridgeK.IsSignalingProfileK`, `CC.BridgeK.exists_signalingProfileK`, `CC.BridgeK.signalingProfileK_act`, `CC.BridgeK.signalingProfileK_post_ae`, `CC.BridgeK.eqActK_signaling` |
| Proposition 2 in every signaling equilibrium | `CC.LinearPaths.prop2_signalingProfile` |
| Proposition 3 (Fragility) | `CC.prop3_1`, `CC.prop3_2_individual`, `CC.prop3_2_peer` |
| Proposition 3 (1), paper's definition of social learning | `CC.BridgeK.prop3_1_socialLearning`, `CC.BridgeK.prop3_1_never` |
| Proposition 3 (1), every prior of the model and every signaling equilibrium | `CC.prop3_1_prior`, `CC.BridgeK.prop3_1_socialLearning_prior`, `CC.BridgeK.prop3_1_never_prior`, `CC.BridgeK.prop3_1_signalingProfile` |
| Lemma 2 | `CC.lemma2`, `CC.sens_diag`, `CC.sensDiag_hasDerivAt` |
| Proposition 4 | `CC.prop4` |
| Extensions section: D1 strategies are D1^∞ strategies | `CC.General.ordD1_strategy_D1Inf` |
| Lemma A1 (Information Accounting) | `CC.lemmaA1` |
| Proposition A1 (Heterogeneous Conformity Concerns) | `CC.propA1`, `CC.propA1_equilibrium` |
| Proposition A1, paper's definition of social learning | `CC.BridgeK.propA1_socialLearning`, `CC.BridgeK.histSigmaK_eq_info`, `CC.BridgeK.beliefsK_gaussian`, `CC.BridgeK.propA1_signalingProfile`, `CC.BridgeK.propA1_path_signalingProfile` |
| Proposition A2 (Unbounded Stakes) | `CC.propA2_equilibrium`, `CC.propA2`, `CC.LinearPaths.propA2_signalingProfile` |
| Lemma A2 (Continuity of Equilibrium Payoffs) | `CC.General.lemmaA2` |
| Proposition A3 (central pooling) | `CC.General.propA3_i`, `CC.General.propA3_i_even`, `CC.General.propA3_ii` |
| Note after Definition A1 (compact type space) | `CC.General.Compact.noteA1` |
| Lemma A3 (Tail Solutions) | `CC.ODE.lemmaA3_i` … `CC.ODE.lemmaA3_iv` |
| Corollary A1 (Left-Tail Solutions) | `CC.ODE.corollaryA1_i` … `CC.ODE.corollaryA1_iv` |
| Proposition A4 (General Distributions, θ known) | `CC.General.propA4_revealing`, `CC.General.propA4_pooling`, `CC.Learning.propA4_learning_exact` (as stated), `CC.Learning.propA4_learning` (learning fails, atomless `μ`), `CC.Learning.propA4_weights` (weights in the history) |
| Proposition A4, the period game at each realized history | `CC.Learning.propA4_period_games`, `CC.Learning.typeLaw_regular`, `CC.Learning.propA4_exists_density`, `CC.Learning.propA4_exists_gaussian` |
| Remark A1 | `CC.General.remarkA1` |
| Corollary A2 (θ known) | `CC.corollaryA2`; social learning (paper's definition): `CC.Bridge.corollaryA2_socialLearning` |
| Corollary A2, asymptotic payoffs as unconditional expectations | `CC.Bridge.corollaryA2_asymptotic`; every signaling equilibrium: `CC.LinearPaths.corollaryA2_signalingProfile`, `CC.LinearPaths.corollaryA2_asymptotic_profile` |
| Proposition A5 (General Distributions, μ known), fixed history | `CC.General.propA5_minimizer`, `CC.General.propA5_period` |
| Proposition A5, across histories (last sentence) | `CC.LearnTheta.propA5_revealing_every_history`, `CC.LearnTheta.propA5_learning`, `CC.LearnTheta.propA5_learning_def`, `CC.LearnTheta.propA5_pooling`, `CC.LearnTheta.mfun_condExp`; the Claim: `CC.LearnTheta.propA5_claim`, `CC.LearnTheta.ClaimSetup.claim_upper`, `CC.LearnTheta.ClaimSetup.claim_lower` |
| Proposition A5, an equilibrium fully revealing at every history | `CC.LearnTheta.propA5_exists`, `CC.LearnTheta.measurable_revealSel`, `CC.LearnTheta.revealSel_spec`; the Linear-Gaussian case: `CC.LearnTheta.propA5_exists_gaussian`, `CC.LearnTheta.beliefY_gaussian`, `CC.LearnTheta.hm_gaussian` |
| Corollary A3 (μ known) | `CC.corollaryA3`; social learning (paper's definition): `CC.Bridge.corollaryA3_socialLearning` |
| Corollary A3, asymptotic payoffs as unconditional expectations | `CC.Bridge.corollaryA3_asymptotic`; every signaling equilibrium: `CC.LinearPaths.corollaryA3_signalingProfile`, `CC.LinearPaths.corollaryA3_asymptotic_profile` |
| Corollary A3, closed form of `m` in the proof | `CC.LearnTheta.mfun_gaussian`, `CC.LearnTheta.mfun_gaussian_regular`, `CC.LearnTheta.mfun_gaussian_sens`, `CC.LearnTheta.secondDeriv_antitone`, `CC.LearnTheta.m_closed_form` |
| Proposition A6 (Generalized Learning) | `CC.General.propA6_i_period`, `CC.General.propA6_ii_period`, `CC.Learning.propA6`, `CC.Learning.propA6_weights`, `CC.Learning.propA6_unnormalized`, `CC.Learning.propA6_period_games` (the period game at each realized history) |
| Shifted Preferences (online appendix section) | `CC.Shifted.sens_indep_means`, `CC.Shifted.lemma1_sh`, `CC.Shifted.corollary1_sh`, `CC.Shifted.revelation_indep_c`, `CC.Shifted.baseline_selects_revealing`, `CC.Shifted.large_c_threshold`, `CC.Shifted.large_c_model`, `CC.Shifted.altEq_revealing_iff`, `CC.Shifted.SigmaSeqAlt_eq`, `CC.Shifted.prop2_socialLearning_alt`, `CC.Shifted.prop2_alt`, `CC.Shifted.propA1_alt`, `CC.Shifted.propA2_alt`, `CC.Shifted.prop3_1_alt`, `CC.Shifted.prop3_1_prior_alt`, `CC.Shifted.prop3_2_individual_alt`, `CC.Shifted.prop3_2_peer_alt`, `CC.Shifted.corollaryA2_alt`, `CC.Shifted.corollaryA3_alt` |
| Gaussian updating used by the model | `CC.privInfo_law`, `CC.condExp_theta`, `CC.condExp_adaptation`, `CC.posterior_after_reveal` |
| The period game at a Gaussian history satisfies the standing assumptions | `CC.gameAt_std` |

The formalization applies only to the named results in the manuscript and to the claims listed
above from their proofs.
-/

#print axioms CC.LG.prop1
#print axioms CC.LG.prop1_threshold
#print axioms CC.LG.lemma1
#print axioms CC.LG.signalingEq_char
#print axioms CC.LG.corollary1
#print axioms CC.LG.slope_root_iff
#print axioms CC.LG.lemma3
#print axioms CC.Bridge.beliefs_gaussian
#print axioms CC.Bridge.prop2_socialLearning
#print axioms CC.Bridge.histSigma_eq
#print axioms CC.prop2
#print axioms CC.prop2_beliefs
#print axioms CC.prop3_1
#print axioms CC.prop3_2_individual
#print axioms CC.prop3_2_peer
#print axioms CC.lemma2
#print axioms CC.sens_diag
#print axioms CC.sensDiag_hasDerivAt
#print axioms CC.prop4
#print axioms CC.lemmaA1
#print axioms CC.propA1
#print axioms CC.propA1_equilibrium
#print axioms CC.propA2
#print axioms CC.propA2_equilibrium
#print axioms CC.periodRevealing_iff
#print axioms CC.SigmaSeq_eq_SigmaC
#print axioms CC.General.lemmaA2
#print axioms CC.General.propA3_i
#print axioms CC.General.propA3_i_even
#print axioms CC.General.propA3_ii
#print axioms CC.ODE.lemmaA3_i
#print axioms CC.ODE.lemmaA3_ii
#print axioms CC.ODE.lemmaA3_iii
#print axioms CC.ODE.lemmaA3_iv
#print axioms CC.ODE.corollaryA1_i
#print axioms CC.ODE.corollaryA1_ii
#print axioms CC.ODE.corollaryA1_iii
#print axioms CC.ODE.corollaryA1_iv
#print axioms CC.General.propA4_revealing
#print axioms CC.General.propA4_pooling
#print axioms CC.Learning.propA4_learning
#print axioms CC.General.remarkA1
#print axioms CC.corollaryA2
#print axioms CC.General.propA5_minimizer
#print axioms CC.General.propA5_period
#print axioms CC.LearnTheta.propA5_revealing_every_history
#print axioms CC.LearnTheta.propA5_learning
#print axioms CC.LearnTheta.propA5_pooling
#print axioms CC.LearnTheta.propA5_learning_def
#print axioms CC.LearnTheta.mfun_condExp
#print axioms CC.Learning.propA4_learning_exact
#print axioms CC.Bridge.corollaryA2_socialLearning
#print axioms CC.Bridge.corollaryA3_socialLearning
#print axioms CC.LearnTheta.ClaimSetup.claim_upper
#print axioms CC.LearnTheta.ClaimSetup.claim_lower
#print axioms CC.corollaryA3
#print axioms CC.General.propA6_i_period
#print axioms CC.General.propA6_ii_period
#print axioms CC.Learning.propA6
#print axioms CC.Learning.learning_revealing
#print axioms CC.Learning.learning_pooling
#print axioms CC.privInfo_law
#print axioms CC.condExp_theta
#print axioms CC.condExp_adaptation
#print axioms CC.posterior_after_reveal
#print axioms CC.Examples.quadSetting
#print axioms CC.Examples.fullSupport_unif01
#print axioms CC.Examples.absGauss_hyp
#print axioms CC.Examples.prop4_hyp
#print axioms CC.Bridge.socialLearning_theta_iff
#print axioms CC.Bridge.socialLearning_mu_iff
#print axioms CC.BridgeK.prop3_1_socialLearning
#print axioms CC.BridgeK.prop3_1_never
#print axioms CC.General.ordD1_strategy_D1Inf
#print axioms CC.LinearPaths.beliefs_gaussian_of_linear
#print axioms CC.LinearPaths.lemma3_onPath
#print axioms CC.LinearPaths.beliefs_gaussian_of_linear_param
#print axioms CC.BridgeK.propA1_socialLearning
#print axioms CC.BridgeK.histSigmaK_eq_info
#print axioms CC.BridgeK.beliefsK_gaussian
#print axioms CC.General.Compact.noteA1
#print axioms CC.Bridge.corollaryA2_asymptotic
#print axioms CC.Bridge.corollaryA3_asymptotic
#print axioms CC.LearnTheta.propA5_exists
#print axioms CC.LearnTheta.measurable_revealSel
#print axioms CC.LearnTheta.revealSel_spec
#print axioms CC.Shifted.shifted_zero
#print axioms CC.Shifted.lemma3_sh
#print axioms CC.Shifted.revealing_char_sh
#print axioms CC.Shifted.revealing_exists_sh
#print axioms CC.Shifted.pooling_sh
#print axioms CC.Shifted.lemma1_sh
#print axioms CC.Shifted.corollary1_sh
#print axioms CC.Shifted.revelation_indep_c
#print axioms CC.Shifted.baseline_selects_revealing
#print axioms CC.Shifted.signalingEq_exists_sh
#print axioms CC.Shifted.signalingEq_char_sh
#print axioms CC.Shifted.signalingEq_sens_zero_sh
#print axioms CC.Shifted.large_c_threshold
#print axioms CC.Shifted.altEq_exists
#print axioms CC.Shifted.altEq_char
#print axioms CC.Shifted.altEq_revealing_iff
#print axioms CC.Shifted.sens_indep_means
#print axioms CC.Shifted.sens_gamma_zero
#print axioms CC.Shifted.large_c_gameAt
#print axioms CC.Shifted.large_c_model
#print axioms CC.Shifted.periodRevealingAlt_iff
#print axioms CC.Shifted.SigmaSeqAlt_eq
#print axioms CC.Shifted.prop2_alt
#print axioms CC.Shifted.propA1_alt
#print axioms CC.Shifted.propA2_alt
#print axioms CC.Shifted.histSigmaAlt_eq
#print axioms CC.Shifted.prop2_socialLearning_alt
#print axioms CC.Shifted.prop3_1_alt
#print axioms CC.Shifted.prop3_2_individual_alt
#print axioms CC.Shifted.prop3_2_peer_alt
#print axioms CC.Shifted.corollaryA2_alt
#print axioms CC.Shifted.corollaryA3_alt
#print axioms CC.General.confLoss_of_even
#print axioms CC.Learning.not_learning_pooling
#print axioms CC.prop3_1_prior
#print axioms CC.BridgeK.prop3_1_socialLearning_prior
#print axioms CC.BridgeK.prop3_1_never_prior
#print axioms CC.Shifted.prop3_1_prior_alt
#print axioms CC.Bridge.histSigma_eq_info
#print axioms CC.Bridge.socialLearning_theta_fails
#print axioms CC.Bridge.socialLearning_mu_fails
#print axioms CC.LinearPaths.eqForm_signaling
#print axioms CC.LinearPaths.signaling_ae_eqForm
#print axioms CC.LinearPaths.exists_signalingProfile
#print axioms CC.LinearPaths.signalingProfile_act
#print axioms CC.LinearPaths.signalingProfile_post_ae
#print axioms CC.LinearPaths.prop2_signalingProfile
#print axioms CC.LinearPaths.corollaryA2_signalingProfile
#print axioms CC.LinearPaths.corollaryA3_signalingProfile
#print axioms CC.BridgeK.eqActK_signaling
#print axioms CC.LearnTheta.mfun_gaussian
#print axioms CC.LearnTheta.mfun_gaussian_regular
#print axioms CC.LearnTheta.mfun_gaussian_sens
#print axioms CC.LearnTheta.secondDeriv_antitone
#print axioms CC.Learning.propA4_weights
#print axioms CC.Learning.propA6_weights
#print axioms CC.Learning.propA6_unnormalized
#print axioms CC.Examples.propA6_pooling_example
#print axioms CC.Examples.propA6_revealing_example
#print axioms CC.LearnTheta.beliefY_gaussian
#print axioms CC.LearnTheta.hm_gaussian
#print axioms CC.LearnTheta.post_of_inv
#print axioms CC.LearnTheta.m_closed_form
#print axioms CC.LearnTheta.propA5_exists_gaussian
#print axioms CC.LinearPaths.corollaryA2_asymptotic_profile
#print axioms CC.LinearPaths.corollaryA3_asymptotic_profile
#print axioms CC.LinearPaths.propA2_signalingProfile
#print axioms CC.BridgeK.exists_signalingProfileK
#print axioms CC.BridgeK.signalingProfileK_act
#print axioms CC.BridgeK.signalingProfileK_post_ae
#print axioms CC.BridgeK.propA1_signalingProfile
#print axioms CC.BridgeK.prop3_1_signalingProfile
#print axioms CC.BridgeK.propA1_path_signalingProfile
#print axioms CC.gameAt_std
#print axioms CC.LearnTheta.propA5_claim
#print axioms CC.Learning.propA4_period_games
#print axioms CC.Learning.propA6_period_games
#print axioms CC.Learning.typeLaw_regular
#print axioms CC.Learning.propA4_exists_density
#print axioms CC.Learning.propA4_exists_gaussian
