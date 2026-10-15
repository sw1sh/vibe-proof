#!/bin/zsh
# Sequential build of the W=56 chunk files (one Lean process at a time, each under timeout 60).
# About 64 x 5.4 s = 6 minutes in total; needs the lean/ snapshot built (see VibeProof/Rule30Prize/lean/README.md).
B=${0:A:h}   # this script's directory (the archived t1 folder)
L=$B/build/logs   # new logs go under build/ (git-ignored); logs/ keeps the original run's logs
mkdir -p $L
cd $B
[ -f $B/build/KC/Q01Lanes.olean ] || ./build.sh KC.Q01Lanes >> $L/w56_progress.txt 2>&1 || { echo "FAILED Q01Lanes" >> $L/w56_progress.txt; exit 1; }
for i in $(seq 0 63); do
  if [ -f $B/build/KC/Q01W56/C$i.olean ] && [ $B/build/KC/Q01W56/C$i.olean -nt $B/src/KC/Q01W56/C$i.lean ]; then continue; fi
  ./build.sh KC.Q01W56.C$i >> $L/w56_progress.txt 2>&1 || { echo "FAILED C$i" >> $L/w56_progress.txt; exit 1; }
done
./build.sh KC.Q01W56 >> $L/w56_progress.txt 2>&1 || { echo "FAILED main" >> $L/w56_progress.txt; exit 1; }
echo "ALL DONE" >> $L/w56_progress.txt
