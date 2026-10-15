#!/bin/zsh
# Build a self-contained Lean file: Rule30Jen.lean (core only) + MaskedJen theorems, compile with plain lean.
D=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-maskedjen-rigor
J=/Users/swish/src/wolfram/vibe-proof/ruliology-lean/Ruliology/CellularAutomata/Rule30Jen.lean
M=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/newideas/MaskedJenAx.lean
{ cat $J; echo; grep -v '^import ' $M; } > $D/SelfContained.lean
grep -n '^import' $D/SelfContained.lean
