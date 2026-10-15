"""Compute the import closure of the Rule30* modules imported by the catalog root.

Usage: python3 -I closure.py <catalog_root>
Prints: the 40 root Rule30* imports (in order), then the closure in a
topological (dependency-first) order, one module per line.
"""
import os
import re
import sys

root = sys.argv[1]
imp_re = re.compile(r'^\s*import\s+(\S+)')


def mod_path(m):
    return os.path.join(root, *m.split('.')) + '.lean'


def imports_of(m):
    out = []
    with open(mod_path(m), encoding='utf-8') as f:
        for line in f:
            mm = imp_re.match(line)
            if mm:
                out.append(mm.group(1))
            elif line.strip().startswith('/-') or line.strip() == '' or line.strip().startswith('--'):
                # imports must come first; tolerate comments/blank lines before them
                continue
            elif line.strip().startswith('module') or line.strip().startswith('prelude'):
                continue
            else:
                # first non-import line ends the header (good enough for these files)
                pass
    return out


with open(os.path.join(root, 'Ruliology.lean'), encoding='utf-8') as f:
    root_imports = [imp_re.match(l).group(1) for l in f if imp_re.match(l)]

r30 = [m for m in root_imports if m.split('.')[-1].startswith('Rule30')]

# DFS topological order
order = []
state = {}
ext = set()


def visit(m):
    if state.get(m) == 2:
        return
    if state.get(m) == 1:
        raise SystemExit('cycle at ' + m)
    state[m] = 1
    if not m.startswith('Ruliology.'):
        ext.add(m)
        state[m] = 2
        return
    for d in imports_of(m):
        visit(d)
    state[m] = 2
    order.append(m)


for m in r30:
    visit(m)

print('ROOT_R30', len(r30))
for m in r30:
    print('R', m)
print('CLOSURE', len(order))
for m in order:
    print('C', m)
print('EXTERNAL', sorted(ext))
