import sys, time, io, contextlib
sys.path.insert(0, '.')
from family0 import verify, apply_u
budget = float(sys.argv[1]); us = sys.argv[2:]
t0 = time.time()
for u in us:
    if time.time() - t0 > budget: print(u, "SKIP"); continue
    k = len(u)
    # choose j minimal such that determined prefix after u contains a 1
    j = None
    for jj in range((k + 1) // 2, k + 8):
        after = apply_u([1] + [0, 1] * jj, [int(ch) for ch in u])
        if 1 in after: j = jj; break
    if j is None: print(u, "no lock prefix"); continue
    Z = k + 4; r0 = Z; L = 3 * k + 12
    f = io.StringIO()
    with contextlib.redirect_stdout(f):
        R = verify(u, j, Z, r0, L, verbose=True)
    out = f.getvalue().strip().splitlines()
    print(f"{u}: R={R}  [{out[0] if out else ''}]" + ("" if R else "  " + ' | '.join(out[1:])), flush=True)
