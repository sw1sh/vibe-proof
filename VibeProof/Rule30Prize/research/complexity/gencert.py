# Build the sorted-window certificate for the Lean complexity window from Rule30Window.centerBits.
import re, sys
sys.set_int_max_str_digits(0)
src = open('/Users/swish/src/wolfram/vibe-proof/ruliology-lean/Ruliology/CellularAutomata/Rule30Window.lean').read()
m = re.search(r'def centerBits : Nat := (\d+)', src)
B = int(m.group(1)); N = 16384; W = int(sys.argv[1]) if len(sys.argv) > 1 else 26
# cross-check with the data file
data = open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin','rb').read(N // 8)
bits = [(data[i >> 3] >> (7 - (i & 7))) & 1 for i in range(N)]
assert all(((B >> i) & 1) == bits[i] for i in range(N)), "centerBits disagrees with data"
M = N - W + 1
mask = (1 << W) - 1
win = [(B >> i) & mask for i in range(M)]
assert len(set(win)) == M, "windows not distinct"
perm = sorted(range(M), key=lambda i: win[i])
CH = 4096; KB = 14
chunks = []
for c0 in range(0, M, CH):
    v = 0
    for k, idx in enumerate(perm[c0:c0+CH]):
        v |= idx << (KB * k)
    chunks.append(v)
print(f"N={N} W={W} M={M} chunks={len(chunks)} digits={[len(str(c)) for c in chunks]}", file=sys.stderr)
out = []
for ci, v in enumerate(chunks):
    out.append(f"/-- Certificate chunk {ci}: indices `{ci*CH}`.. of the windows sorted by value, {KB} bits each. -/\ndef permChunk{ci} : Nat := {v}\n")
open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/complexity/lean/cert_chunks.lean.txt','w').write('\n'.join(out))
