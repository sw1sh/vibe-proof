#!/usr/bin/env python3
"""Check that the generated catalog files differ from the scratch sources only in module docstrings,
imports and namespace/open/end lines. Also flag new lines longer than 100 characters.
usage: python3 -I check_equiv.py CATALOG_ROOT PER_MODULE
"""
import os
import re
import sys

J = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize'
T1 = f'{J}/kernel-certify-r2/t1/src/KC'
T2 = f'{J}/kernel-certify-r2/t2/src/KC'
T3 = f'{J}/kernel-certify-r2/t3/src/KC'
T4 = f'{J}/kernel-certify-r2/t4/src/KC'
P3 = f'{J}/p3-ether/lean'
ROOT = sys.argv[1]
PER = int(sys.argv[2])
CA = os.path.join(ROOT, 'Ruliology', 'CellularAutomata')


def read(p):
    with open(p, encoding='utf-8') as f:
        return f.read()


def code(text):
    text = re.sub(r'/-!.*?-/', '', text, flags=re.S)  # module docstrings only
    out = []
    for line in text.split('\n'):
        st = line.strip()
        if not st:
            continue
        if re.match(r'(import|namespace|end|open) ', st):
            continue
        out.append(line)
    return out


pairs = [
    ('Rule30ZeroBoundaryLanes.lean', [f'{T1}/Q01Lanes.lean']),
    ('Rule30ZeroBoundaryWidth52.lean', [f'{T1}/Q01W52.lean']),
    ('Rule30ZeroBoundaryStripeFront.lean', [f'{T2}/StripeFront.lean']),
    ('Rule30ZeroBoundaryStripeFamily.lean', [f'{T2}/StripeFamily.lean']),
    ('Rule30EtherTrap.lean', [f'{T3}/EtherTrap.lean']),
    ('Rule30EtherTrapWidth20.lean', [f'{T3}/EtherTrapMain.lean']),
    ('Rule30PeriodTwoLanguage.lean', [f'{T4}/PeriodTwoLang.lean']),
    ('Rule30PeriodTwoWidth5.lean', [f'{T4}/PeriodTwoW5.lean']),
    ('Rule30PeriodTwoWidth6.lean', [f'{T4}/PeriodTwoW6.lean']),
    ('Rule30EtherThree.lean', [f'{P3}/P3Ether.lean']),
    ('Rule30EtherThreeNoWall.lean', [f'{P3}/P3NoWall.lean']),
    ('Rule30EtherThreeTrap.lean', [f'{P3}/P3Trap001.lean']),
    ('Rule30EtherThreeReach.lean', [f'{P3}/P3Reach.lean']),
    ('Rule30EtherThreeLeft.lean', [f'{P3}/P3Left.lean']),
    ('Rule30EtherThreeSkeleton.lean', [f'{P3}/P3Skel.lean']),
]
for k in range(16 // PER):
    pairs.append((f'Rule30Certificates/ZeroBoundaryWidth52Chunks{k}.lean',
                  [f'{T1}/Q01W52/C{j}.lean' for j in range(k * PER, (k + 1) * PER)]))
for k in range(3):
    pairs.append((f'Rule30Certificates/ZeroBoundaryStripeCycles{k}.lean', [f'{T2}/StripeCycles{k}.lean']))
for k in range(6):
    pairs.append((f'Rule30Certificates/EtherTrap{k}.lean', [f'{T3}/EtherTrapCerts{k}.lean']))

bad = 0
for rel, srcs in pairs:
    new = read(os.path.join(CA, rel))
    old = ''.join(read(p) for p in srcs)
    a, b = code(old), code(new)
    same = a == b
    src_lines = set(old.split('\n'))
    long_new = [l for l in new.split('\n') if len(l) > 100 and l not in src_lines]
    nonascii_ws = [l for l in new.split('\n') if l != l.rstrip()]
    print(f"{'OK ' if same else 'DIFF'} {rel}: {len(b)} code lines; new long lines: {len(long_new)}; "
          f"trailing ws: {len(nonascii_ws)}")
    for l in long_new:
        print('   LONG:', len(l), l[:120])
    if not same:
        bad += 1
        import difflib
        for d in list(difflib.unified_diff(a, b, lineterm='', n=0))[:20]:
            print('   ', d[:160])
print('files with code differences:', bad)
