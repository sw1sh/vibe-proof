#!/bin/zsh
# usage: sb.sh ModuleName  -- compile staging/Ruliology/CellularAutomata/ModuleName.lean from
# ruliology-lean with a 60 s limit; staged oleans go to curation/build (on LEAN_PATH).
ST=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/staging
BD=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/curation/build
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean || exit 2
mkdir -p $BD/Ruliology/CellularAutomata
f=$ST/Ruliology/CellularAutomata/$1.lean
o=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/curation/out_$1.txt
LP=/Users/swish/.elan/toolchains/leanprover--lean4---v4.30.0/lib/lean
LEAN=/Users/swish/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
s=$(python3 -c 'import time; print(time.time())')
LEAN_PATH=$BD:$LP timeout 60 $LEAN --root=$ST -o $BD/Ruliology/CellularAutomata/$1.olean -i $BD/Ruliology/CellularAutomata/$1.ilean $f > $o 2>&1
rc=$?
e=$(python3 -c 'import time; print(time.time())')
python3 -c "print('$1: elapsed %.1f s, rc=$rc' % ($e - $s))"
head -c 12000 $o
