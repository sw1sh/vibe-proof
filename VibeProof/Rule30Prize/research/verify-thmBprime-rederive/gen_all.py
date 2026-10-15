# Generate kernel checks Determined v 4 = true for every word v of length 0..7 not already
# covered by the D4 modules (those start and end white), plus an assembly file.
import itertools, os, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)

def lit(u):
    return '[' + ', '.join('true' if b else 'false' for b in u) + ']'

def name(u):
    return 'w' + ''.join(str(b) for b in u) if u else 'wnil'

def white_bounded(u):
    return len(u) >= 1 and u[0] == 0 and u[-1] == 0

words = {n: list(itertools.product([0, 1], repeat=n)) for n in range(8)}
todo = [u for n in range(8) for u in words[n] if not white_bounded(u)]
assert len(todo) == 191, len(todo)

per_len = {7: 4, 6: 8}
mods = []
for n in range(8):
    items = [u for u in todo if len(u) == n]
    per = per_len.get(n, 32)
    for ci in range(0, len(items), per):
        chunk = items[ci:ci + per]
        mod = f"W_{len(mods):02d}"
        mods.append((mod, chunk))
        with open(os.path.join(out, mod + '.lean'), 'w') as f:
            f.write('import Standalone\nopen AbsorbRight\n\n')
            for u in chunk:
                f.write(f"theorem W_{name(u)} : Determined {lit(u)} 4 = true := by decide +kernel\n")
with open(os.path.join(out, 'W_mods.txt'), 'w') as f:
    for mod, chunk in mods:
        f.write(mod + ' ' + str(len(chunk)) + ' ' + ' '.join(map(lambda u: name(u), chunk)) + '\n')

def thm(u):
    return f"D4_b{''.join(map(str, u))}" if white_bounded(u) else f"W_{name(u)}"

with open(os.path.join(out, 'W_All.lean'), 'w') as f:
    for i in range(15):
        f.write(f"import D4_{i:02d}\n")
    for mod, _ in mods:
        f.write(f"import {mod}\n")
    f.write('open Ruliology.CellularAutomata.Rule30Jen\nopen AbsorbRight\n\n')
    for n in range(8):
        f.write(f"theorem allLists_{n}_eq : allLists {n} =\n  [" + ',\n   '.join(lit(u) for u in words[n]) + '] := by decide +kernel\n\n')
        f.write(f"theorem det4_len{n} : ∀ v ∈ allLists {n}, Determined v 4 = true := by\n")
        f.write(f"  rw [allLists_{n}_eq]\n  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]\n")
        f.write('  exact ⟨' + ', '.join(thm(u) for u in words[n]) + '⟩\n\n')
print(len(mods), 'modules;', sum(len(c) for _, c in mods), 'words')
