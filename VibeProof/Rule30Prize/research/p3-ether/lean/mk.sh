#!/bin/zsh
# usage: mk.sh Module   -- compiles lean/Module.lean against Ruliology + lean/build, writes build/Module.olean
L=/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean
cd /Users/swish/src/wolfram/vibe-proof/ruliology-lean || exit 1
/usr/bin/time -l timeout 60 lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$L/build\" lean -R $L -o $L/build/$1.olean -i $L/build/$1.ilean $L/$1.lean" 2>&1 | grep -v "^ *[0-9]* *\(page\|block\|signals\|voluntary\|involuntary\|messages\|swaps\|instructions\|cycles\|average\)"
