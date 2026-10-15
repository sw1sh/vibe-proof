# Generate a Lean file that re-checks the three exported traps by kernel `decide` and derives the
# no-entry consequence from masked Jen. Data comes from the newideas trap_*.txt files.
D = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/newideas/'
OUT = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-p4traps-rigor/P4Traps.lean'
traps = [('0001', 16, 'trap_0001_16.txt', [False, False, True, False]),
         ('0011', 16, 'trap_0011_16.txt', [False, True, False, False]),
         ('0111', 14, 'trap_0111_14.txt', [False, False, False, False])]
def lb(x): return 'true' if x else 'false'
parts = []
parts.append(open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-p4traps-rigor/P4Traps_head.lean').read())
for (w, b, fn, g) in traps:
    lines = [l.split() for l in open(D + fn).read().strip().split('\n')]
    assert lines[0] == [w, str(b), str(len(lines) - 1)]
    ents = []
    for ph, s, pos in lines[1:]:
        ph = int(ph); s = int(s)
        bits = [lb((s >> i) & 1) for i in range(b)]   # columns 1..b
        ents.append(f"({ph}, [{', '.join(bits)}])")
    parts.append(f"\n/-- Trap for w = {w}, strip width {b}, {len(ents)} states (from newideas/{fn}). -/\n")
    parts.append(f"def S{w} : List (Nat × List Bool) := [\n  " + ",\n  ".join(ents) + "]\n")
    parts.append(f"def w{w} (φ : Nat) : Bool := [{', '.join(lb(c == '1') for c in w)}].getD φ false\n")
    parts.append(f"def g{w} (φ : Nat) : Bool := [{', '.join(lb(x) for x in g)}].getD φ false\n")
    parts.append(f"theorem len{w} : S{w}.length = {len(ents)} := by decide +kernel\n")
    parts.append(f"theorem check{w} : checkTrap w{w} g{w} S{w} = true := by decide +kernel\n")
    parts.append(f"""
/-- If `c(t) = w{w}[(t+k) mod 4]` for all `t ≥ T`, the true strip (cells 1..{b}) is never in `S{w}`
at the matching phase at any time `T' ≥ T`. -/
theorem no_entry{w} (T k T' : Nat) (hc : ∀ t, T ≤ t → cell t 0 = w{w} ((t + k) % 4)) (hT : T ≤ T') :
    ((T' + k) % 4, col T' 1 {b}) ∉ S{w} :=
  fun hin => trap_sound {b} (by decide) w{w} g{w} S{w} check{w} T k T' hc hT hin
""")
parts.append("\nend P4TrapCheck\n\n")
for (w, b, fn, g) in traps:
    parts.append(f"#print axioms P4TrapCheck.no_entry{w}\n")
open(OUT, 'w').write(''.join(parts))
print('wrote', OUT)
