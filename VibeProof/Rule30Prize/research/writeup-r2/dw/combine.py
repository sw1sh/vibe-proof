#!/usr/bin/env python3
import re, glob, collections
R = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/'
zt = collections.defaultdict(list); nchunks = {}
bad = []
for fn in glob.glob('zt2_a*_n*_c*.txt'):
    a, n, c = map(int, re.match(r'zt2_a(\d+)_n(\d+)_c(\d+)\.txt', fn).groups())
    txt = open(fn).read()
    m = re.search(r'deepest surviving depth=(\d+) => all die by depth', txt)
    if not m or 'TIMEOUT' in txt or 'inconclusive' in txt: bad.append(fn); continue
    zt[a].append((n, c, int(m.group(1))))
D_zt = {}
for a, lst in zt.items():
    ns = {n for n, _, _ in lst}
    assert len(ns) == 1, (a, ns)
    n = ns.pop(); cs = sorted(c for _, c, _ in lst)
    assert cs == list(range(n)), (a, n, cs)
    D_zt[a - 1] = max(d for _, _, d in lst); nchunks[a - 1] = n
pa = {int(W): int(d) for W, d in re.findall(r'W=(\d+) best death time=(\d+)', open(R + 'progA-backdet/DW_table_phase0.txt').read())}
inv = {int(W): int(d) for W, d in re.findall(r'mode=0 W=(\d+) maxdeath=(\d+)', open(R + 'A-invsearch/best_mode0.txt').read())}
mono = {int(W): int(d) for W, d in re.findall(r'W=\s*(\d+)\s+maxprefix=\s*(\d+)', open('mono_dfs_1_40.txt').read())}
mono.update({50: 92, 56: 100, 58: 110})   # spot runs of A-monovariant/dfs in this pass (see log)
print('bad files:', bad)
print(' W  D(W) 2W+8 slack  progA  invsearch  monovariant  chunks')
viol = []; eq = []
for W in sorted(D_zt):
    d = D_zt[W]
    if d > 2 * W + 8: viol.append(W)
    if d == 2 * W + 8: eq.append(W)
    def cmp(tab):
        if W not in tab: return '   -'
        return f"{tab[W]:4d}" + ('' if tab[W] == d else ' MISMATCH')
    print(f"{W:2d} {d:5d} {2*W+8:4d} {2*W+8-d:5d}  {cmp(pa)}  {cmp(inv)}  {cmp(mono)}  {nchunks[W]}")
print('W range', min(D_zt), max(D_zt), '; violations of D(W) <= 2W+8:', viol, '; equality at W =', eq)
agree = all(pa[W] == D_zt[W] for W in pa if W in D_zt) and all(inv[W] == D_zt[W] for W in inv if W in D_zt) and all(mono[W] == D_zt[W] for W in mono if W in D_zt)
print('all overlapping values agree:', agree, '; overlaps: progA', len([W for W in pa if W in D_zt]), 'invsearch', len([W for W in inv if W in D_zt]), 'monovariant', len([W for W in mono if W in D_zt]))
mx = max(D_zt[W] / W for W in D_zt if W >= 10)
print('max D(W)/W for W>=10:', round(mx, 3))
