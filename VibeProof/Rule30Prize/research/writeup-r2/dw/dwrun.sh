#!/bin/zsh
# usage: dwrun.sh a nch c0 c1   -- run zt2 chunks c0..c1 (of nch) for width bound a in parallel, 55 s cap each
Z=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-reconmap/c/zt2
a=$1; nch=$2; c0=$3; c1=$4
for ((i=c0; i<=c1; i++)); do
  ( timeout 55 $Z $a 40 $nch $i > zt2_a${a}_n${nch}_c${i}.txt 2>&1 || echo "TIMEOUT/ERR rc=$?" >> zt2_a${a}_n${nch}_c${i}.txt ) &
done
wait
