#!/bin/zsh
# usage: build.sh Module.Name ...   (compiles each module sequentially, one Lean process at a time)
B=${0:A:h}   # this script's directory (the archived t1 folder)
L=$B/build/logs   # new logs go under build/ (git-ignored); logs/ keeps the original run's logs
mkdir -p $L
cd ${B:h:h:h}/kit/lean   # the kit's lean/, formerly the lean/ snapshot of the catalog (VibeProof/Rule30Prize/lean)
for M in "$@"; do
  F=$B/src/${M//.//}.lean
  O=$B/build/${M//.//}.olean
  mkdir -p $(dirname $O)
  S=$(date +%s.%N 2>/dev/null || python3 -c 'import time;print(time.time())')
  LEAN_PATH=$B/build /usr/bin/time -l timeout 60 lake env lean -j 1 -R $B/src -o $O $F > $L/${M}.log 2>&1
  RC=$?
  echo "$M rc=$RC $(grep -E ' real ' $L/${M}.log | awk '{print $1"s"}') $(grep 'maximum resident' $L/${M}.log | awk '{printf "%.2fGB", $1/1e9}')"
  grep -E "error|sorry" $L/${M}.log | head -5
  if [ $RC -ne 0 ]; then exit 1; fi
done
