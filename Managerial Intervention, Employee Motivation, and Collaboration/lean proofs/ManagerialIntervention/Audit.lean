import ManagerialIntervention.AppendixB1

/-!
# Axiom audit

`#print axioms` for every main result.  Only `propext`, `Classical.choice` and `Quot.sound`
may appear.
-/

-- Section 2–3.1: model, alignment, first-order conditions
#print axioms MI.Cost.isBR_iff
#print axioms MI.Cost.d_br
#print axioms MI.Env.isEq_iff
#print axioms MI.Env.alphaA_le_one
#print axioms MI.Env.alphaP_le_one
#print axioms MI.Env.alphaA_neg_iff
#print axioms MI.Env.foc_principal_cen
#print axioms MI.Env.foc_principal_del
#print axioms MI.Env.foc_agent_cen
#print axioms MI.Env.foc_agent_del
-- Lemma 1, Lemma 2
#print axioms MI.Env.lemma1
#print axioms MI.Env.lemma2a
#print axioms MI.Env.lemma2b
-- Proposition 3
#print axioms MI.Env.prop3
#print axioms MI.Env.prop3_strict
#print axioms MI.Env.prop3a
#print axioms MI.Env.prop3b_convex
#print axioms MI.Env.prop3b_convex_strict
#print axioms MI.Env.prop3b_concave
#print axioms MI.Env.prop3b_concave_strict
#print axioms MI.Env.prop3c_neg
#print axioms MI.Env.prop3c_pos
-- Propositions 4 and B.1
#print axioms MI.prop4
#print axioms MI.propB1_contractible
-- Section 3.2: Propositions 5 and 6
#print axioms MI.Env.isEqMu_iff
#print axioms MI.Env.muStar_nonempty
#print axioms MI.Env.prop5_convex
#print axioms MI.Env.prop5_linear
#print axioms MI.Env.prop6
#print axioms MI.Env.prop6_nonneg
#print axioms MI.Env.informal_delegation_motivates
-- Counterexamples
#print axioms MI.prop5_counterexample
#print axioms MI.prop4_boundary
#print axioms MI.propB1_boundary
#print axioms MI.Env.ea_eq_of_alpha_one
#print axioms MI.prop3b_concave_equal
-- Non-vacuity
#print axioms MI.nonvacuous_prop3a
#print axioms MI.nonvacuous_prop3b_convex
#print axioms MI.nonvacuous_prop3b_concave
#print axioms MI.nonvacuous_prop3c_neg
#print axioms MI.nonvacuous_prop3c_pos
#print axioms MI.nonvacuous_prop4
#print axioms MI.nonvacuous_propB1
#print axioms MI.nonvacuous_prop5
#print axioms MI.nonvacuous_prop6
-- Appendix B.1
#print axioms MI.EnvN.lemma1
#print axioms MI.EnvN.lemma2_del
#print axioms MI.EnvN.lemma2_cen
#print axioms MI.EnvN.effort_iff
#print axioms MI.EnvN.effort_iff_h
#print axioms MI.EnvN.effort_iff_corrected
#print axioms MI.EnvN.simplification_fails
#print axioms MI.EnvN.prop3c_analogue_weak
#print axioms MI.EnvN.prop3c_analogue
-- Proposition 5 under α_a h_a'' ≥ 0
#print axioms MI.Env.prop5_general
#print axioms MI.Env.prop5_curvature
#print axioms MI.Env.prop5_straddle
#print axioms MI.Env.noquit_iff
#print axioms MI.prop5_counterexample_smooth
#print axioms MI.nonvacuous_prop5_curvature
-- Appendix B.1 with informal delegation
#print axioms MI.EnvN.isEqMu_iff
#print axioms MI.EnvN.eaMu_eq_zero
#print axioms MI.EnvN.mem_muStar_iff
#print axioms MI.EnvN.prop6_analogue_fails
-- Proposition 5 under a convex, log-concave marginal cost and positive equilibrium effort
#print axioms MI.Env.prop5_logconcave
#print axioms MI.Env.prop5_logconcave_general
#print axioms MI.Env.works_of_works_at_min
#print axioms MI.Env.prop5_logconcave_statusQuo
#print axioms MI.Cost.pow_d_convex
#print axioms MI.Cost.pow_d_logconcave
#print axioms MI.EnvN.prop5_analogue
#print axioms MI.nonvacuous_prop5_logconcave
#print axioms MI.EnvN.prop6_analogue
#print axioms MI.EnvN.muStar_nonempty
#print axioms MI.EnvN.nonvacuous_prop5_analogue
#print axioms MI.EnvN.nonvacuous_prop6_analogue
-- Appendix B.1: analogues of Propositions 3 and 4
#print axioms MI.EnvN.effort_lt_iff
#print axioms MI.EnvN.prop3a_analogue
#print axioms MI.EnvN.prop3b_convex_analogue
#print axioms MI.EnvN.prop3b_concave_analogue
#print axioms MI.EnvN.ea_eq_of_alpha_one
#print axioms MI.EnvN.prop3c_analogue_strict
#print axioms MI.prop4_analogue
#print axioms MI.EnvN.nonvacuous_prop3a_analogue
#print axioms MI.EnvN.nonvacuous_prop3b_convex_analogue
#print axioms MI.EnvN.nonvacuous_prop3b_concave_analogue
#print axioms MI.EnvN.nonvacuous_prop3c_analogue_strict
#print axioms MI.nonvacuous_prop4_analogue
-- Strict comparisons, boundaries and ties at zero effort
#print axioms MI.Env.prop3c_pos_strict
#print axioms MI.Env.ea_eq_of_alphaA_zero
#print axioms MI.Env.nonvacuous_prop3c_pos_strict
#print axioms MI.EnvN.effort_lt_iff_alpha
#print axioms MI.EnvN.ea_zero_of_nonpos
#print axioms MI.EnvN.ea_cen_zero
#print axioms MI.EnvN.prop3c_pos_analogue_strict
#print axioms MI.EnvN.muStar_eq_singleton
#print axioms MI.EnvN.nonvacuous_prop3c_pos_analogue_strict
#print axioms MI.EnvN.nonvacuous_ea_zero_of_nonpos
#print axioms MI.EnvN.nonvacuous_muStar_eq_singleton
