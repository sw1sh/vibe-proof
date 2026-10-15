"""Check that every theorem name cited in the README's module tables is declared in that module.

Usage: python3 -I check_readme.py <lean_dir>
"""
import os
import re
import sys

lean = sys.argv[1]
ca = os.path.join(lean, 'Ruliology', 'CellularAutomata')
text = open(os.path.join(lean, 'README.md'), encoding='utf-8').read()

rows = 0
cited = 0
missing = []
modules_seen = set()
for line in text.splitlines():
    if not line.startswith('| `'):
        continue
    cells = [c.strip() for c in line.strip().strip('|').split('|')]
    if len(cells) != 4:
        continue  # not a module table row (e.g. the build-cost table)
    mod = re.findall(r'`([^`]+)`', cells[0])
    if not mod:
        continue
    rows += 1
    m = mod[0]
    modules_seen.add(m)
    path = os.path.join(ca, m + '.lean')
    if not os.path.exists(path):
        if m.startswith('Rule30Certificates/'):
            continue  # family rows such as `Rule30Certificates/EtherTrap0`–`5`
        missing.append(('no module file', m))
        continue
    src = open(path, encoding='utf-8').read()
    for name in re.findall(r'`([^`]+)`', cells[3]):
        cited += 1
        base = name.split('.')[-1]
        pat = (r"^\s*(@\[[^\]]*\]\s*)?(private |protected )?"
               r"(theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_.']*\.)?"
               + re.escape(base) + r"\b")
        if not re.search(pat, src, re.M):
            missing.append((m, name))

print('table rows:', rows, 'theorem names cited:', cited)
print('missing:', missing if missing else 'none')
