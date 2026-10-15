#!/bin/zsh
# usage: mk.sh Module -- compile staging/Ruliology/CellularAutomata/Module.lean into writeup-r2/build (60 s cap)
ST=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/staging
WB=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/writeup-r2/build
CB=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/curation/build
LP=/Users/swish/.elan/toolchains/leanprover--lean4---v4.30.0/lib/lean
LEAN=/Users/swish/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
O=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/writeup-r2/ax/build_$1.txt
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean || exit 2
s=$(date +%s)
LEAN_PATH=$WB:$CB:$LP timeout 60 $LEAN --root=$ST -o $WB/Ruliology/CellularAutomata/$1.olean -i $WB/Ruliology/CellularAutomata/$1.ilean $ST/Ruliology/CellularAutomata/$1.lean > $O 2>&1
rc=$?
echo "$1 rc=$rc $(( $(date +%s) - s ))s" | tee -a /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/writeup-r2/ax/build_times.txt
grep -i "error" $O | head -5
