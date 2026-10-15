#!/bin/zsh
# usage: b.sh Module ...   Builds Ruliology.CellularAutomata.<Module> one at a time (sequentially),
# each under `timeout 60 /usr/bin/time -l lake build`, logging time and peak RSS; stops at the first failure.
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean || exit 1
LOG=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/integrate-final/logs
mkdir -p $LOG
for M in "$@"; do
  F=${M//\//.}
  timeout 60 /usr/bin/time -l lake build Ruliology.CellularAutomata.$F > $LOG/$F.log 2>&1
  RC=$?
  T=$(grep -E ' real ' $LOG/$F.log | awk '{print $1}')
  R=$(grep 'maximum resident' $LOG/$F.log | awk '{printf "%.2f", $1/1e9}')
  B=$(grep -E 'Built Ruliology\.CellularAutomata\.'"$F"' ' $LOG/$F.log | sed -E 's/.*\(([^)]*)\).*/\1/')
  echo "$F rc=$RC real=${T}s lean=${B} peak=${R}GB"
  grep -E -i 'error|warning|sorry' $LOG/$F.log | head -10
  if [ $RC -ne 0 ]; then exit 1; fi
done
exit 0
