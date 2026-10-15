#!/bin/zsh
# usage: ax.sh ModuleName thm1 thm2 ... -- print axioms of staged theorems (names relative to the module namespace)
M=$1; shift
BD=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/curation/build
F=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/curation/ax_$M.lean
echo "import Ruliology.CellularAutomata.$M" > $F
for t in "$@"; do echo "#print axioms Ruliology.CellularAutomata.$M.$t" >> $F; done
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean || exit 2
LEAN_PATH=$BD:/Users/swish/.elan/toolchains/leanprover--lean4---v4.30.0/lib/lean timeout 60 /Users/swish/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean $F 2>&1 | tr '\n' ' ' | sed 's/'"'"'Ruliology/\n'"'"'Ruliology/g'; echo
