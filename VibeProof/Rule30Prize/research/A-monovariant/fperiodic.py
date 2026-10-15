# For periodic f (period p), Theta(f) is spatially eventually periodic: compute preperiod, period, and tail pattern
# via the spatial recurrence on periodic columns (Z/2p).
import sys
def theta_tail(fper):
    p = len(fper)
    P = 2 * p
    X1 = tuple(1 if t % 2 == 0 else fper[(t // 2) % p] for t in range(P))
    X0 = tuple([0] * P)
    seen = {}
    pair = (X0, X1)
    seq = []
    k = 1
    while pair not in seen and k < 200000:
        seen[pair] = k
        seq.append(pair[1][0])   # X_k(0) = L(k)
        a, b = pair
        nxt = tuple(b[(t + 1) % P] ^ (b[t] | a[t]) for t in range(P))
        pair = (b, nxt)
        k += 1
    k0 = seen[pair]
    per = k - k0
    tail = seq[k0 - 1:]
    # minimal period of the L-sequence tail (could be smaller than the pair period)
    for d in range(1, per + 1):
        if per % d == 0 and all(tail[i] == tail[i % d] for i in range(per)):
            break
    return k0, per, d, seq
def canon(v):
    return min(v[i:] + v[:i] for i in range(len(v)))
res = {}
maxp = int(sys.argv[1]) if len(sys.argv) > 1 else 10
for p in range(1, maxp + 1):
    for m in range(1 << p):
        f = [(m >> i) & 1 for i in range(p)]
        # primitive
        if any(p % d == 0 and all(f[i] == f[i % d] for i in range(p)) for d in range(1, p)): continue
        k0, per, d, seq = theta_tail(f)
        tail = seq[k0 - 1:k0 - 1 + d]
        key = (d, canon(''.join(map(str, tail))))
        res.setdefault(key, []).append(''.join(map(str, f)))
for (d, v), fs in sorted(res.items()):
    w = v.count('1')
    print(f"L-tail period {d:4d}, weight {w:3d} ({w/d:.3f}): tail {v if d <= 40 else v[:40]+'...'}  from {len(fs)} primitive f, e.g. {fs[:4]}")
