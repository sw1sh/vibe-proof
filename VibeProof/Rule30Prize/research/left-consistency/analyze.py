import sys, re, collections
data = collections.defaultdict(dict)
for fn in sys.argv[1:]:
    for line in open(fn):
        m = re.match(r'w=(\S+) T=(\d+) leaves=(\d+) surv_to_H=(\d+) H=(\d+) maxfirstviol=(-?\d+)', line)
        if not m: continue
        w, T, leaves, surv, H, M = m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)), int(m.group(5)), int(m.group(6))
        data[w][T] = (leaves, surv, H, M)
def fit(xs, ys):
    n = len(xs); mx = sum(xs)/n; my = sum(ys)/n
    sxx = sum((x-mx)**2 for x in xs); sxy = sum((x-mx)*(y-my) for x, y in zip(xs, ys))
    b = sxy/sxx; return b, my - b*mx
print("word  rho   Trange  anySurvivorToH  fit M ~ a*T+b (T>=10, leaves>0)  heuristic (1+rho)/rho  max(M-2T)")
for w in sorted(data, key=lambda s: (len(s), s)):
    rho = w.count('1')/len(w)
    Ts = sorted(data[w]); pts = [(T, data[w][T][3]) for T in Ts if T >= 10 and data[w][T][0] > 0 and data[w][T][3] >= 0]
    anys = any(data[w][T][1] > 0 for T in Ts)
    if len(pts) >= 3:
        a, b = fit([p[0] for p in pts], [p[1] for p in pts])
        mexc = max(M - 2*T for T, M in pts)
        print(f"{w:8s} {rho:.3f} {Ts[0]}..{Ts[-1]}  {anys}  a={a:.3f} b={b:.1f}   {(1+rho)/rho:.3f}   {mexc}")
