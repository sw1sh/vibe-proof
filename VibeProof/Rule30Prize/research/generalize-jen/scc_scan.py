# For Lyndon words of given lengths, run the C strip/SCC analyzer at increasing K; record the smallest K at which the
# e-criterion (sccE) and d-criterion (sccD) succeed.
import sys, subprocess
BIN = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/generalize-jen/c/strip_scc'
def lyndon(n):
    res = []
    for x in range(2**n):
        s = format(x, '0%db' % n)
        if all(s < s[i:] + s[:i] for i in range(1, n)): res.append(s)
    return res
def run(w, K):
    out = subprocess.run([BIN, w, str(K)], capture_output=True, text=True, timeout=55).stdout
    f = dict(kv.split('=') for kv in out.split()[1:] if '=' in kv)
    return f
nmin, nmax = int(sys.argv[1]), int(sys.argv[2]); Ks = [int(k) for k in sys.argv[3].split(',')]
for n in range(nmin, nmax + 1):
    tally = {'E&D': 0, 'E only': 0, 'none': 0}
    for w in lyndon(n):
        KE = KD = None; last = None
        for K in Ks:
            f = run(w, K); last = f
            if f['sccE'] == '1' and KE is None: KE = K
            if f['sccD'] == '1' and KD is None: KD = K
            if KE is not None and KD is not None: break
        tag = 'E&D' if KD is not None else ('E only' if KE is not None else 'none')
        tally[tag] += 1
        if tag != 'none':
            print(f"{w} {tag} KE={KE} KD={KD} col1={last['col1']}", flush=True)
    print('length', n, tally, flush=True)
