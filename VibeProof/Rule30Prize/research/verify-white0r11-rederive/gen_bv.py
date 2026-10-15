# Generate a Lean file proving, with bv_decide (LRAT-certified), that for the right half of rule 30
# driven by w^inf (phase 0), x(n,1) = x(n+Q,1) for every initial configuration.
# Row r_t : BitVec W, bit i = column i+1 at time t.  r_{t+1} = ((r_t <<< 1) ||| d_t) ^^^ (r_t ||| (r_t >>> 1)).
import sys
w = sys.argv[1]; Q = int(sys.argv[2]); ns = [int(x) for x in sys.argv[3].split(',')]; out = sys.argv[4]
P = len(w)
lines = ["import Std.Tactic.BVDecide", "", "set_option maxHeartbeats 0", ""]
for n in ns:
    N = n + Q; W = N + 1
    args = ' '.join(f"r{t}" for t in range(N + 1))
    hyps = []
    for t in range(N):
        d = w[t % P]
        hyps.append(f"(h{t + 1} : r{t + 1} = ((r{t} <<< 1) ||| {d}#{W}) ^^^ (r{t} ||| (r{t} >>> 1)))")
    lines.append(f"theorem forced_{w}_{Q}_{n} ({args} : BitVec {W})")
    for h in hyps: lines.append("    " + h)
    lines.append(f"    : r{n}.getLsbD 0 = r{N}.getLsbD 0 := by")
    lines.append("  bv_decide")
    lines.append("")
    lines.append(f"#print axioms forced_{w}_{Q}_{n}")
    lines.append("")
open(out, 'w').write('\n'.join(lines) + '\n')
