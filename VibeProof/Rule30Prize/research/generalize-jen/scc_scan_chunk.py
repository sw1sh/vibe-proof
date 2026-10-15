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
    return dict(kv.split('=') for kv in out.split()[1:] if '=' in kv)
n, chunk, nchunks = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); Ks = [int(k) for k in sys.argv[4].split(',')]
words = lyndon(n)[chunk::nchunks]
for w in words:
    KE = KD = None; last = None
    for K in Ks:
        f = run(w, K); last = f
        if f['sccE'] == '1' and KE is None: KE = K
        if f['sccD'] == '1' and KD is None: KD = K
        if KE is not None and KD is not None: break
    tag = 'E&D' if KD is not None else ('E only' if KE is not None else 'none')
    print(f"{w} {tag} KE={KE} KD={KD}", flush=True)
