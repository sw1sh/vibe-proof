import subprocess, sys
BIN = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/generalize-jen/c/strip_scc'
def run(w, K):
    out = subprocess.run([BIN, w, str(K)], capture_output=True, text=True, timeout=55).stdout
    return dict(kv.split('=') for kv in out.split()[1:] if '=' in kv)
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    rows = [l.split() for l in open(f's{n}.txt')] if n >= 11 else []
    tally = {}
    for r in rows:
        if r[1] == 'none': continue
        w = r[0]
        f = None
        for K in (8, 11, 14):
            f = run(w, K)
            if f['forcedE'] == '1': break
        key = ('forcedE' if f['forcedE'] == '1' else 'sccE-only', 'E&D' if r[1] == 'E&D' else 'E-only')
        tally[key] = tally.get(key, 0) + 1
    print(n, tally, flush=True)
