#!/bin/zsh
# usage: vmk.sh <dir> <Module> [noolean]
# compiles <dir>/<Module>.lean against Ruliology + verify/build ONLY (not the worker's lean/build);
# writes verify/build/<Module>.olean unless "noolean" is given.
V=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/verify
D=$1; M=$2
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean || exit 1
if [ "$3" = "noolean" ]; then
  OUT=""
else
  OUT="-o $V/build/$M.olean"
fi
/usr/bin/time -l timeout 60 lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$V/build\" lean -R $D $OUT $D/$M.lean" 2>&1 | grep -v "^ *[0-9]* *\(page\|block\|signals\|voluntary\|involuntary\|messages\|swaps\|instructions\|cycles\|average\|peak memory\)"
echo "pipestatus=${pipestatus[1]}"
