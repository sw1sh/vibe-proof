# Sanity check of Theorem B' semantics on the driven right half (random initial rows):
# driver column 0 = (1^r u)^inf starting at a black run; column 1 should be P-periodic from time r.
import random, sys
def run(u, r, W, periods, seed):
    rnd = random.Random(seed)
    P = r + len(u)
    word = [1]*r + list(u)
    row = [rnd.randint(0,1) for _ in range(W)]   # columns 1..W
    T = P*periods
    col1 = []
    for t in range(T):
        col1.append(row[0])
        c0 = word[t % P]
        new = []
        for i in range(len(row)-1):
            l = c0 if i == 0 else row[i-1]
            new.append(l ^ (row[i] | row[i+1]))
        row = new
    # check P-periodicity of column 1 from time r
    return all(col1[t] == col1[t+P] for t in range(r, T-P))
tab = {}
for line in open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/absorb-right/j0_table.txt'):
    k, v = line.strip().split(':'); tab[k.strip()] = int(v)
bad = []
for s, j in tab.items():
    u = [int(ch) for ch in s]
    r = max(9, 9*j)
    P = r + len(u); periods = 6
    W = P*periods + 5
    for seed in range(3):
        if not run(u, r, W, periods, seed):
            bad.append((s, r, seed))
print("violations at r = 9*j0:", bad)
# how often does it fail one step below the bound (informative only)
fails = 0
for s, j in tab.items():
    u = [int(ch) for ch in s]; r = 9*j - 1; P = r + len(u)
    if not all(run(u, r, P*6+5, 6, seed) for seed in range(3)): fails += 1
print("blocks where P-periodicity from time r fails at r = 9*j0 - 1 (some seed):", fails, "of", len(tab))
