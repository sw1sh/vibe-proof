# Kernel checks Determined u j0(u) = true for the table values with |u| >= 5 and j0 < 4.
# Heavy cases (|u| = 7, j0 = 2: 2^13 tails) are split by a 3-bit prefix of the tail.
import itertools, os, sys

out = sys.argv[1]
table_path = sys.argv[2]
os.makedirs(out, exist_ok=True)

table = {}
for line in open(table_path):
    line = line.strip()
    if line:
        w, j = line.split(':')
        table[tuple(int(c) for c in w.strip())] = int(j)

def lit(u):
    return '[' + ', '.join('true' if b else 'false' for b in u) + ']'

def name(u):
    return ''.join(str(b) for b in u)

light, heavy = [], []
for u, j in sorted(table.items(), key=lambda x: (len(x[0]), x[0])):
    if len(u) <= 4 or j == 4:
        continue  # |u| <= 4: det_* in Standalone; j0 = 4: D4 modules
    (heavy if 2 ** (len(u) + 10 - 2 * j) > 4096 else light).append((u, j))
print('light', len(light), 'heavy', len(heavy))

mods = []
# light: budget ~ 2^13 tails-equivalents per module
cur, cost = [], 0
for u, j in light:
    c = 2 ** (len(u) + 10 - 2 * j) * (len(u) + 10) ** 2
    if cur and cost + c > 4096 * 17 ** 2:
        mods.append(cur); cur, cost = [], 0
    cur.append((u, j)); cost += c
if cur:
    mods.append(cur)
names = []
for i, chunk in enumerate(mods):
    m = f"T_{i:02d}"
    names.append(m)
    with open(os.path.join(out, m + '.lean'), 'w') as f:
        f.write('import Standalone\nopen AbsorbRight\n\n')
        for u, j in chunk:
            f.write(f"theorem T_{name(u)} : Determined {lit(u)} {j} = true := by decide +kernel\n")

# heavy: one module per (block, 3-bit prefix)
hnames = []
for u, j in heavy:
    n = len(u) + 10 - 2 * j
    for pre in itertools.product([0, 1], repeat=3):
        m = f"H_{name(u)}_{name(pre)}"
        hnames.append(m)
        with open(os.path.join(out, m + '.lean'), 'w') as f:
            f.write('import Standalone\nopen Ruliology.CellularAutomata.Rule30Jen\nopen AbsorbRight\n\n')
            f.write(f"theorem {m} : (allLists {n - 3}).all (fun rest => traceCol1 (drv {lit(u)}) "
                    f"(wbPattern {j} ++ ({lit(pre)} ++ rest)) == traceCol1 (drv {lit(u)}) "
                    f"(wbPattern {j} ++ List.replicate {n} false)) = true := by decide +kernel\n")
with open(os.path.join(out, 'mods.txt'), 'w') as f:
    f.write(' '.join(names) + '\n')
    f.write(' '.join(hnames) + '\n')
print(len(names), 'light modules,', len(hnames), 'heavy modules')
