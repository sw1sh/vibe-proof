#!/bin/zsh
# usage: build.sh Module.Name ...   (compiles each module sequentially, one Lean process at a time)
B=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t4
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean
for M in "$@"; do
  F=$B/src/${M//.//}.lean
  O=$B/build/${M//.//}.olean
  mkdir -p $(dirname $O)
  S=$(date +%s.%N 2>/dev/null || python3 -c 'import time;print(time.time())')
  LEAN_PATH=$B/build /usr/bin/time -l timeout 60 lake env lean -j 1 -R $B/src -o $O $F > $B/logs/${M}.log 2>&1
  RC=$?
  echo "$M rc=$RC $(grep -E ' real ' $B/logs/${M}.log | awk '{print $1"s"}') $(grep 'maximum resident' $B/logs/${M}.log | awk '{printf "%.2fGB", $1/1e9}')"
  grep -E "error|sorry" $B/logs/${M}.log | head -5
  if [ $RC -ne 0 ]; then exit 1; fi
done
