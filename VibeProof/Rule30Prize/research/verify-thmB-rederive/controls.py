import importlib.util
spec = importlib.util.spec_from_file_location("lib", "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-thmB-rederive/driven_end_to_end_lib.py")
lib = importlib.util.module_from_spec(spec); spec.loader.exec_module(lib)
rng = lib.rng
# Control 1: start the periodicity check at t1 (beginning of the black run) instead of e.
c1 = 0; n1 = 0
for _ in range(300):
    L = rng.randrange(0, 12); u = [rng.randrange(2) for _ in range(L)]
    r = 9 * lib.ceil_half(L + 9)
    n1 += 1
    if not lib.one_test(u, r, check_shift=r):
        c1 += 1
print(f"control 1 (check from t1 instead of e): fails {c1}/{n1}")
# Control 2: short black run r = 3 with long random u (theorem hypothesis badly violated).
c2 = 0; n2 = 0
for _ in range(200):
    L = rng.randrange(20, 40); u = [rng.randrange(2) for _ in range(L)]
    n2 += 1
    if not lib.one_test(u, 3, extra_periods=8):
        c2 += 1
print(f"control 2 (r=3, |u| in 20..39): fails {c2}/{n2}")
# Control 3: find the smallest r (for several u) at which periodicity-from-e holds in all trials,
# to see how conservative the threshold is.
for u in ([0], [0,0], [0,1,0], [0,1,1,0], [0]*7, [0,1]*4, [0,1,1,0,1,0,0,1,1,1,0,1]):
    thr = 9 * lib.ceil_half(len(u) + 9)
    best = None
    for r in range(1, thr + 1):
        if all(lib.one_test(u, r, extra_periods=8) for _ in range(40)):
            best = r; break
    print(f"u={''.join(map(str,u))}: theorem threshold r={thr}; empirical min r with periodic-from-e in 40/40: {best}")
