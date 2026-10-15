# Independent cross-check of cert.c's successor table, using an explicit list-of-cells strip step that is
# itself validated against a direct rule-30 simulation (dict of cells, no bit tricks).
import sys, subprocess
W = int(sys.argv[1]); exe = sys.argv[2]

def rule30_rows(tmax):
    # rows[t] = dict position -> 0/1 (only black cells stored)
    row = {0: 1}
    rows = [row]
    for t in range(tmax):
        new = {}
        for q in range(-t - 1, t + 2):
            v = row.get(q - 1, 0) ^ (row.get(q, 0) | row.get(q + 1, 0))
            if v: new[q] = 1
        row = new; rows.append(row)
    return rows

def strip_step(cols, c, x):
    # cols: list, cols[i-1] = column i (i = 1..W); c = column 0; x = column W+1
    out = []
    for i in range(1, W + 1):
        left = c if i == 1 else cols[i - 2]
        ctr = cols[i - 1]
        right = x if i == W else cols[i]
        out.append(left ^ (ctr | right))
    return out

rows = rule30_rows(400)
cval = [rows[t].get(0, 0) for t in range(len(rows))]
assert cval[:20] == [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1], cval[:20]
for t in range(400):
    cols = [rows[t].get(i, 0) for i in range(1, W + 1)]
    nxt = [rows[t + 1].get(i, 0) for i in range(1, W + 1)]
    assert strip_step(cols, cval[t], rows[t].get(W + 1, 0)) == nxt, t
    assert rows[t].get(-1, 0) == cval[t + 1] ^ (cval[t] | rows[t].get(1, 0)), t
print('python strip step validated against direct rule 30 for t < 400, W =', W)

# Decode cert.c's encoding (column i <-> bit W-i) and compare the whole table.
out = subprocess.run([exe, 'dump', str(W)], capture_output=True, text=True, check=True).stdout.split('\n')
def dec(s): return [(s >> (W - i)) & 1 for i in range(1, W + 1)]
def enc(cols): return sum(b << (W - i) for i, b in enumerate(cols, start=1))
n = 0
for line in out:
    if not line: continue
    d, x, s, u = map(int, line.split())
    assert enc(strip_step(dec(s), d, x)) == u, (d, x, s, u)
    n += 1
assert n == 4 * (1 << W)
print('cert.c successor table agrees with python strip step on all', n, 'entries')
