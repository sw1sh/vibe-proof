#!/bin/zsh
# usage: scan.sh outfile word...
out=$1; shift
for w in "$@"; do
  # density of ones
  ones=$(echo -n $w | tr -cd '1' | wc -c | tr -d ' '); P=${#w}
  # cap T so that 2^((1-rho)T) <= 2^19
  zeros=$((P - ones))
  if [ $zeros -eq 0 ]; then Tmax=40; else Tmax=$(( 19 * P / zeros )); fi
  if [ $Tmax -gt 40 ]; then Tmax=40; fi
  timeout 55 ./lsurv $w 2 $Tmax 14 >> $out
done
