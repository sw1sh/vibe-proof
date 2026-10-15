# Generate Lean files with one kernel `decide` per block (Determined u j) for the 64 short blocks.
import itertools, sys, os

out = sys.argv[1]
mode = sys.argv[2]          # "four" (j0 = 4 for every block) or "table" (j0 from the table)
table_path = sys.argv[3] if len(sys.argv) > 3 else None

blocks = []
for n in range(0, 8):
    for bits in itertools.product([0, 1], repeat=n):   # same order as allLists (false first)
        if n >= 1 and bits[0] == 0 and bits[-1] == 0:
            blocks.append(bits)
assert len(blocks) == 64

table = {}
if table_path:
    for line in open(table_path):
        line = line.strip()
        if line:
            w, j = line.split(':')
            table[tuple(int(c) for c in w.strip())] = int(j)

def lit(u):
    return '[' + ', '.join('true' if b else 'false' for b in u) + ']'

def name(u):
    return 'b' + ''.join(str(b) for b in u)

groups = {}
for u in blocks:
    j = 4 if mode == 'four' else table[u]
    # cost ~ 2^(|u|+10-2j) * (|u|+10)^2 ; group to keep each file small
    key = (len(u), j) if mode == 'table' else (len(u), 0)
    groups.setdefault(key, []).append((u, j))

prefix = 'D4' if mode == 'four' else 'DT'
mods = []
for key, items in sorted(groups.items()):
    # split heavy groups into chunks
    if mode == 'table':
        L, j = key
        cost = 2 ** (L + 10 - 2 * j)
        per = max(1, int(16 * 512 / cost))
    else:
        per = {7: 4, 6: 8}.get(key[0], 16)
    for ci in range(0, len(items), per):
        chunk = items[ci:ci + per]
        mod = f"{prefix}_{len(mods):02d}"
        mods.append((mod, chunk))
        with open(os.path.join(out, mod + '.lean'), 'w') as f:
            f.write('import Standalone\nopen AbsorbRight\n\n')
            for u, j in chunk:
                f.write(f"theorem {prefix}_{name(u)} : Determined {lit(u)} {j} = true := by decide +kernel\n")
with open(os.path.join(out, prefix + '_mods.txt'), 'w') as f:
    for mod, chunk in mods:
        f.write(mod + ' ' + ' '.join(name(u) + ':' + str(j) for u, j in chunk) + '\n')

# final file: assemble the 64 facts into a statement about every listed block
with open(os.path.join(out, prefix + '_All.lean'), 'w') as f:
    for mod, _ in mods:
        f.write(f"import {mod}\n")
    f.write('open Ruliology.CellularAutomata.Rule30Jen\nopen AbsorbRight\n\n')
    f.write('/-- All blocks of length 1..7 that start and end white. -/\n')
    f.write('def shortBlocks : List (List Bool) :=\n  ((List.range 8).flatMap allLists).filter fun u => u.head? == some false && u.getLast? == some false\n\n')
    f.write('theorem shortBlocks_eq : shortBlocks =\n  [' + ',\n   '.join(lit(u) for u in blocks) + '] := by decide +kernel\n\n')
    if mode == 'four':
        f.write('theorem det_all : ∀ u ∈ shortBlocks, Determined u 4 = true := by\n')
    else:
        f.write('def j0tab (u : List Bool) : Nat :=\n  match u with\n')
        for u in blocks:
            f.write(f"  | {lit(u)} => {table[u]}\n")
        f.write('  | _ => 0\n\n')
        f.write('theorem det_all : ∀ u ∈ shortBlocks, Determined u (j0tab u) = true := by\n')
    f.write('  rw [shortBlocks_eq]\n  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, implies_true, and_true]\n')
    f.write('  exact ⟨' + ', '.join(f"{prefix}_{name(u)}" for u in blocks) + '⟩\n\n')
    f.write('#print axioms det_all\n')
print(len(mods), 'modules')
