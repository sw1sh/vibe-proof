#!/bin/zsh
# usage: tc.sh file.lean  -- compile from ruliology-lean with a 60 s limit, print elapsed seconds
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean || exit 2
f="$1"
o=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/curation/out_$$.txt
s=$(python3 -c 'import time; print(time.time())')
timeout 60 lake env lean "$f" > "$o" 2>&1
rc=$?
e=$(python3 -c 'import time; print(time.time())')
python3 -c "print('elapsed %.1f s, rc=$rc' % ($e - $s))"
head -c 8000 "$o"
rm -f "$o"
