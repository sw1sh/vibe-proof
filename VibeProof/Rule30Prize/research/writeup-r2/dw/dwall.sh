#!/bin/zsh
# run zt2 unchunked for a list of widths, 8 at a time
Z=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-reconmap/c/zt2
for a in "$@"; do
  ( timeout 55 $Z $a 40 1 0 > zt2_a${a}_n1_c0.txt 2>&1 || echo "TIMEOUT/ERR rc=$?" >> zt2_a${a}_n1_c0.txt ) &
done
wait
