import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/generalize-jen')
from rsim import true_rows, run
T = int(sys.argv[1]); w = sys.argv[2]; steps = int(sys.argv[3])
for t, rh, c in true_rows(T):
    if t == T: row = rh
wb = [int(ch) for ch in w]; P = len(wb)
# print spacetime of first 12 columns
for t in range(steps):
    c = wb[t % P]
    s = ''.join('#' if (row >> i) & 1 else '.' for i in range(24))
    print(f"{t:4d} c={c} |{s}")
    row = ((row << 1) | c) ^ (row | (row >> 1))
