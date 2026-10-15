import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import reconstruct
def psi(fword, K):
    T = K + 2
    y = [1 if t % 2 == 0 else int(fword[(t // 2) % len(fword)]) for t in range(T)]
    return reconstruct(y, K)
def eventual_period(seq, start_max=200):
    n = len(seq)
    for p in range(1, n // 3):
        for s0 in range(0, start_max):
            if all(seq[i] == seq[i + p] for i in range(s0, n - p)):
                return s0, p
    return None
for fw in ['1', '0', '10', '01', '110', '100', '1110', '1100', '11010', '0111', '11110']:
    L = psi(fw, 600)
    ep = eventual_period(L, 300)
    print(f'f=({fw})^inf : x0[1..40] = {"".join(map(str, L[:40]))}  spatial eventual period (start, p) = {ep}')
