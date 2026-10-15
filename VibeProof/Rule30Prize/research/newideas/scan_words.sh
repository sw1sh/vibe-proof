#!/bin/zsh
# usage: scan_words.sh Pmax bmin bmax
Pmax=$1; bmin=$2; bmax=$3
python3 -I -c "
import itertools
for P in range(1, $Pmax + 1):
    for bits in itertools.product('01', repeat=P):
        w = ''.join(bits)
        if any(w == w[k:] + w[:k] for k in range(1, P) if P % k == 0): continue
        if w != min(w[k:] + w[:k] for k in range(P)): continue
        print(w)
" | while read w; do
  line="$w:"
  for b in $(seq $bmin 2 $bmax); do
    r=$(timeout 50 ./strip_scc_c $w $b | sed -E 's/.*bad=([0-9]+) \(bad nodes ([0-9]+)\).*/\1:\2/')
    line="$line b$b=$r"
  done
  echo $line
done
