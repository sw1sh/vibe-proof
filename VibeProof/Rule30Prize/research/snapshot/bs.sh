#!/bin/zsh
# usage: bs.sh Module ...
# Builds Ruliology.CellularAutomata.<Module> of the Rule 30 snapshot one at a time, in the order
# given, each as `timeout 60 /usr/bin/time -l lake build <target>` run from the snapshot's lean/
# folder. Logs go to snapshot/logs/<Module>.log; one summary line per module is appended to
# snapshot/build_times.txt. Stops at the first failure. GNU timeout signals its whole process
# group, so a timed-out lake takes its lean child with it.
cd /Users/swish/src/wolfram/vibe-proof/VibeProof/Rule30Prize/lean || exit 2
S=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/snapshot
LOG=$S/logs
mkdir -p $LOG
for M in "$@"; do
  F=${M//\//.}
  # Never overlap with one of our own builds (a `lake build`, or lean compiling a file of this
  # snapshot): wait at most 20 s for it, else abort. Also wait at most 20 s for an outside
  # lean/lake process (not an editor server) to finish; if one is still running then, go ahead
  # only while memory_pressure reports at least 30% free, and log the overlap.
  W=0; NOTE=""
  while :; do
    ALL=$(ps -axo pid=,command= | grep -E '^ *[0-9]+ ([^ ]*/)?(lake|lean)( |$)' | grep -v -E ' --server| serve ')
    MINE=$(echo "$ALL" | grep -E 'lake build|Rule30Prize/lean/')
    [ -z "$ALL" ] && break
    if [ $W -ge 40 ]; then
      if [ -n "$MINE" ]; then echo "ABORT: an earlier build of this snapshot is still running:"; echo "$MINE" | cut -c1-200; exit 3; fi
      FREE=$(memory_pressure 2>/dev/null | awk -F': ' '/free percentage/ {gsub("%","",$2); print $2}')
      if [ -n "$FREE" ] && [ "$FREE" -ge 30 ]; then
        NOTE=" overlap=outside(${FREE}%free)"; echo "($F: an outside lean/lake process is running; memory ${FREE}% free, going ahead)"; break
      fi
      echo "ABORT: outside lean/lake process running and memory free is ${FREE:-unknown}%"; exit 3
    fi
    W=$((W+1)); sleep 0.5
  done
  [ $W -gt 0 ] && [ -z "$NOTE" ] && echo "($F: waited $((W/2)) s for an outside lean/lake process to finish)"
  SW0=$(sysctl -n vm.swapusage | awk '{print $6}')
  timeout 60 /usr/bin/time -l lake build Ruliology.CellularAutomata.$F > $LOG/$F.log 2>&1
  RC=$?
  SW1=$(sysctl -n vm.swapusage | awk '{print $6}')
  T=$(grep -E ' real ' $LOG/$F.log | awk '{print $1}')
  R=$(grep 'maximum resident' $LOG/$F.log | awk '{printf "%.2f", $1/1e9}')
  B=$(grep -E 'Built Ruliology\.CellularAutomata\.'"$F"' ' $LOG/$F.log | sed -E 's/.*\(([^)]*)\).*/\1/')
  J=$(grep -E -o 'Build completed successfully( \([0-9]+ jobs\))?' $LOG/$F.log)
  LINE="$F rc=$RC wall=${T}s lean=${B:-none} peakRSS=${R}GB swap_used=${SW0}->${SW1} [$J]$NOTE"
  echo "$LINE"
  echo "$LINE" >> $S/build_times.txt
  grep -E -i 'error|warning|sorry' $LOG/$F.log | head -10
  if [ $RC -ne 0 ]; then echo "STOP: $F failed (rc=$RC)"; tail -20 $LOG/$F.log; exit 1; fi
done
exit 0
