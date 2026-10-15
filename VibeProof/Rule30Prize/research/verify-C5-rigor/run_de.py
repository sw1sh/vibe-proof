import importlib.util, sys
spec = importlib.util.spec_from_file_location('m', '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-C5-rigor/check_abc.py')
src = open(spec.origin).read().split('# light cones:')[0]
ns = {}
exec(src, ns)
for name, f in [('d', ns['chk_d']), ('e', ns['chk_e'])]:
    n, bad = ns['run'](8, 7, f)
    print(f'({name}) K=8: rows with c(t..t+7) alternating = {n}, violations = {bad}')
