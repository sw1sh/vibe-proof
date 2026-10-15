#!/bin/zsh
# Verifier build: compile modules from verify/src into verify/build, one Lean process at a time.
# usage: vbuild.sh Module.Name ...   (each module under its own `timeout 60`)
V=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/verify
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean
for M in "$@"; do
  F=$V/src/${M//.//}.lean
  O=$V/build/${M//.//}.olean
  mkdir -p $(dirname $O)
  LEAN_PATH=$V/build /usr/bin/time -l timeout 60 lake env lean -j 1 -R $V/src -o $O $F > $V/logs/${M}.log 2>&1
  RC=$?
  echo "$M rc=$RC $(grep -E ' real ' $V/logs/${M}.log | awk '{print $1"s"}') $(grep 'maximum resident' $V/logs/${M}.log | awk '{printf "%.2fGB", $1/1e9}')"
  grep -iE "error|sorry|warning" $V/logs/${M}.log | head -5
  if [ $RC -ne 0 ]; then echo "FAILED $M"; exit 1; fi
done
