# My prompt for Lean proof of economic theory papers

There is a LaTeX manuscript in this folder. Build a Lean 4 formalization of its main results (theorems, propositions, lemmas, corollaries and remarks). Use Mathlib, and prove anything it is missing yourself.

STATEMENTS
- Small tweaks are fine, such as changing continuous to differentiable. Ask me before any larger tweak that changes the economic substance of a result, and keep working on the other results while you wait for my answer.
- The final results should have no sorrys, no added axioms and no unproved assumptions. Do not weaken a statement or build its conclusion into a definition to get a proof through.

WHEN A RESULT BREAKS
Results build on different things, so one result being broken, wrong or stuck is no reason to stop working on the others.
- Record the problem and keep going on everything that does not depend on it.
- Results that do depend on it can take it as an explicit hypothesis for now, so that work is not lost.
- If a result looks false, try to find a counterexample.
- At the end, tell me which results are fully proved, which are proved only conditional on something else, and which are unproved.

DO NOT OVERLOAD MY COMPUTER
This is a Mac with 24 GB of RAM, and each Lean process that loads Mathlib uses about 5 GB. Running out of memory freezes the whole machine.
- Download prebuilt Mathlib with `lake exe cache get`. Never compile Mathlib itself.
- Run one Lean command at a time, and do not start another until it finishes.
- Prefer specific Mathlib imports over `import Mathlib`.
- Delete `.lake/build` only once, for a final clean build.
- Check memory before long runs with `top -l 1 -n 0 | grep PhysMem` and `sysctl vm.swapusage`. If swap passes 20 GB or keeps climbing, stop what is running and change your approach.
- Exit code 137 means the process was killed, probably for running out of memory. Do not rerun the same command.

VERIFICATION
When the proofs are done:
1. Run `lake build` and confirm there are no errors or sorry warnings.
2. Run `#print axioms` on every main result. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
3. Replay the proofs through the kernel with `lake env leanchecker <Module>`, one module per command, waiting for each to finish. Never pass the root module, several modules at once, or a name with many modules beneath it: names match as prefixes and all matches run in parallel, which runs the machine out of memory. Never run `leanchecker --help`, because it starts a replay instead of printing help.
4. Read real exit codes by running `command > log 2>&1; echo $?`. In `command | tail`, the exit code you see belongs to `tail`.
5. Build a concrete example of each environment in the model, to show the definitions are satisfiable and the results are not vacuous.

README
Do not edit the .tex file. Create one README.md next to the manuscript, outside the Lean project, with targeted edits to the LaTeX in order of importance. For each edit, give:
- the exact current text, which must match the .tex exactly
- the replacement text
- a one-line reason
- the matching Lean theorem

Each edit should change a clause or a sentence, not a whole section. Leave out anything a careful reader would not object to. Tell me about any small tweaks you made in your final message, not in the README.
