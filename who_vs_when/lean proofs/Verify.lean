import WhoVsWhen

/-! Axioms used by each result. Expected output for each: `propext`, `Classical.choice`,
`Quot.sound`. Run with `lake env lean Verify.lean`. -/

open WhoVsWhen

-- The paper's results, one theorem each
#print axioms lemma1
#print axioms lemma2
#print axioms lemma3
#print axioms lemma4
#print axioms remark1
#print axioms prop1
#print axioms prop2

-- The examples showing that the hypotheses can be met
#print axioms example_belief
#print axioms example_lemma2_seq
#print axioms example_lemma2_conc
#print axioms example_remark1_public
#print axioms example_remark1_noComm
#print axioms example_prop1_i
#print axioms example_prop1_ii
#print axioms example_prop2
