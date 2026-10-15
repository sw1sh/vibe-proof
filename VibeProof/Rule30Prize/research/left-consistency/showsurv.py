# list the edge-structured states at time T that satisfy forced constraints on [T, 2T-1], for word w,
# printed from cell -1 (left) to cell -T (right), with their first violation time.
import sys
sys.path.insert(0, '.')
from ref import first_violation
w = sys.argv[1]; T = int(sys.argv[2])
P = len(w)
rows = []
for s in range(1 << (T - 1)):
    st = s | (1 << (T - 1))
    fv = first_violation(st, T, w, 20 * T + 40)
    if fv is None or fv > 2 * T - 1:
        rows.append((fv, ''.join(str((st >> i) & 1) for i in range(T))))
rows.sort(reverse=True)
print("c from T:", ''.join(w[(t) % P] for t in range(3*T)))
for fv, r in rows[:12]:
    print(fv, fv - 2*T if fv else None, r)
print(len(rows), "states pass [T,2T-1]")
