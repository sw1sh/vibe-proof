#!/usr/bin/env python3
"""Parse `#print axioms` output; report counts and any axiom outside {propext, Classical.choice, Quot.sound}."""
import re, sys
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for path in sys.argv[1:]:
    txt = open(path, encoding='utf-8').read()
    errs = [l for l in txt.split('\n') if ': error' in l or 'unknown constant' in l or 'unknown identifier' in l]
    txt2 = re.sub(r'\n\s+', ' ', txt)
    n = 0; bad = []; names = []
    for line in txt2.split('\n'):
        m = re.match(r"'(.+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", line)
        if m:
            n += 1
            names.append(m.group(1))
            axs = set(a.strip() for a in (m.group(3) or '').split(',') if a.strip())
            if not axs <= allowed:
                bad.append((m.group(1), sorted(axs)))
    print(f"{path}: {n} theorems checked; disallowed: {bad if bad else 'none'}; errors: {len(errs)}")
    for e in errs[:10]:
        print('   ', e)
