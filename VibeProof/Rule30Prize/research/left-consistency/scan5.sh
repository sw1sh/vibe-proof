#!/bin/zsh
out=$1; Tcap=$2; shift 2
for w in "$@"; do
  ones=$(echo -n $w | tr -cd '1' | wc -c | tr -d ' '); P=${#w}; zeros=$((P - ones))
  if [ $zeros -eq 0 ]; then Tmax=$Tcap; else Tmax=$(( 17 * P / zeros )); fi
  if [ $Tmax -gt $Tcap ]; then Tmax=$Tcap; fi
  timeout 20 ./lsurv $w 2 $Tmax 14 >> $out
done
