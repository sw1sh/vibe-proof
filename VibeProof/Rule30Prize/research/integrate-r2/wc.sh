#!/bin/zsh
# usage: wc.sh file.lean -- compile a scratch file against the staged build (curation/build on LEAN_PATH)
BD=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/curation/build
LP=/Users/swish/.elan/toolchains/leanprover--lean4---v4.30.0/lib/lean
LEAN=/Users/swish/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean || exit 2
s=$(python3 -c 'import time; print(time.time())')
LEAN_PATH=$BD:$LP timeout 60 $LEAN "$1" 2>&1 | head -c 15000
rc=${pipestatus[1]}
e=$(python3 -c 'import time; print(time.time())')
python3 -c "print('elapsed %.1f s, rc=$rc' % ($e - $s))"
