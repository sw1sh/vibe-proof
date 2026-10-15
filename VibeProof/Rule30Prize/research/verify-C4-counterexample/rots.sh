#!/bin/bash
W=$1; shift
for w in "$@"; do
  p=${#w}; rots=""
  for ((r=0;r<p;r++)); do rots="$rots ${w:$r}${w:0:$r}"; done
  ./vreach $W 0 100000 $rots | awk -v w=$w '{c[$4]++; s=s" "$3} END {printf "%s rotations: ", w; for (k in c) printf "%s:%d ", k, c[k]; printf " |%s\n", s}'
done
