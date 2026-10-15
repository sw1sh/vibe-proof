exec(open('search2_free.py').read().split('maxd = int')[0])
def run_states(a, W, maxdepth):
    c = lambda t: (a + t) & 1
    states = {(0, 0, None)}
    hist = []
    for k in range(0, maxdepth):
        new = set()
        for (Dkm1, Dk, xl) in states:
            for xk in (0, 1):
                Dn = step(Dkm1, Dk, k, xk, c)
                if k + 1 > W and (Dn & 1): continue
                new.add((Dk, Dn, xk))
        states = new
        if not states: break
        ws = [bin(Dn).count('1') for (_, Dn, _) in states]
        # weight of the "fresh" part: cells j <= k-W (inside the zero zone's light cone)
        hist.append((k + 1, len(states), min(ws), max(ws)))
    return hist
for W in (10, 20):
    h = run_states(1, W, W + 60)
    print(f"a=1 W={W}: (depth, survivors, min weight, max weight) after W:")
    print("   ", [x for x in h if x[0] > W])
