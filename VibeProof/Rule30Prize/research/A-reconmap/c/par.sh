#!/bin/zsh
# usage: par.sh a d0 nchunks
a=$1; d0=$2; n=$3
for ((i=0; i<n; i++)); do
  ./zt2 $a $d0 $n $i > out_${a}_$i.txt &
done
wait
cat out_${a}_*.txt | awk -v a=$a '{for(i=1;i<=NF;i++) if ($i=="depth=") {}; } /deepest/ { split($0, p, "deepest surviving depth="); split(p[2], q, " "); if (q[1]+0 > m) m = q[1]+0; n++ } /inconclusive/ {bad=1} END { if (bad) print "a=" a " INCONCLUSIVE"; else print "a=" a " chunks=" n " all die by depth " m+1 }'
rm -f out_${a}_*.txt
