# Deviation-front frame analysis for the family  x0 = S[1..m] . v . 0^inf  (S = stripe, |v| = L), all m >= 0.
# Ahead of the front (depths < f_t) the configuration is the stripe; the window W_t = x_t[f_t .. f_t+K) evolves
# autonomously (one-way rule): the new window [f-1, f-1+K) needs old cells f-2, f-1 (stripe) and f..f+K-1.
# f_0 = d = first depth where x0 differs from S; f_t = d - t. Arrival at time t_a = d - 1 (window starts at depth 1).
# Column -1 equals S(1)=1 before arrival; at arrival it is 0 (front cell differs from S).
# After arrival we simulate the ZBL from the window for K-1 steps (reliable horizon: column -1 at time t_a+s needs
# depths <= s+1).
# For each (v, m mod 2) the initial window depends only on (v, m mod 2); the orbit of the window under the
# autonomous map is eventually periodic, so all arrival windows (all m) are among finitely many states.
import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import step, death
def S(k): return k % 2  # stripe: black at odd depths (k >= 1); S(0) = 0 is the wall
def front_step(win, f, K):
    # win: list of K bits at depths f..f+K-1 ; returns window at depths f-1 .. f+K-2
    def old(k):
        if k < f: return S(k)
        return win[k - f]
    new = []
    for k in range(f - 1, f - 1 + K):
        # old(k+1) needed up to k+1 = f+K-1: inside the window
        new.append(old(k + 1) ^ (old(k) | old(k - 1)))
    return new
def analyse(v, mpar, K, verbose=False):
    L = len(v)
    # choose a representative m with the right parity, large enough (the window content does not depend on m)
    m = 2 * K + 10 + mpar
    x0 = [S(k) for k in range(1, m + 1)] + list(v)
    # depth of first deviation
    d = None
    for k in range(m + 1, m + L + 3):
        xv = x0[k - 1] if k <= m + L else 0
        if xv != S(k): d = k; break
    win0 = [(x0[k - 1] if k <= m + L else 0) for k in range(d, d + K)]
    delta = d - m
    # orbit of (window, f parity); f_t = d - t; we track t and window
    seen = {}
    orbit = []
    win = win0; t = 0
    while True:
        key = (tuple(win), (d - t) % 2)
        if key in seen: break
        seen[key] = t; orbit.append(win)
        win = front_step(win, d - t, K); t += 1
    T0 = seen[key]; P = t - T0
    return delta, orbit, T0, P, d
def post_arrival(win_at_arrival, ta, K):
    # configuration at time ta: depths 1..K from the window; deeper cells unknown -> simulate K-1 steps reliably
    x = sum(b << i for i, b in enumerate(win_at_arrival))
    for s in range(K - 1):
        t = ta + s
        if t % 2 == 0 and not (x & 1): return s          # death at time ta + s
        x = step(x) & ((1 << K) - 1)                       # cells beyond depth K are unknown: keep only reliable part
        # note: after s steps only depths <= K - s are reliable; column -1 at time ta+s+1 needs depth <= s+2 <= K
    return None
if __name__ == '__main__':
    L = int(sys.argv[1]); K = int(sys.argv[2])
    worst = 0; total_states = 0; maxorbit = 0; fail = []
    for vb in range(1 << L):
        v = [(vb >> i) & 1 for i in range(L)]
        for mpar in (0, 1):
            delta, orbit, T0, P, d = analyse(v, mpar, K)
            maxorbit = max(maxorbit, len(orbit))
            # arrival time ta = d - 1 for the actual m: ta = m + delta - 1; t index into orbit is ta (steps from 0)
            # the window at arrival is orbit[ta] if ta < len(orbit) else orbit[T0 + (ta - T0) % P]
            # all residues/states that can occur for m of parity mpar: ta ranges over m + delta - 1 with m = mpar mod 2
            for idx in range(len(orbit)):
                # time index idx corresponds to ta = idx; parity of ta must match (m + delta - 1) parity
                if (idx - (mpar + delta - 1)) % 2: continue
                # for idx >= T0 the state repeats for all larger ta in the same class; for idx < T0 only small m
                ta_par = idx % 2
                s = post_arrival(orbit[idx], ta_par, K)
                total_states += 1
                if s is None: fail.append((v, mpar, idx)); continue
                worst = max(worst, s)
    print(f'L={L} K={K}: arrival states checked {total_states}, max orbit length {maxorbit}, '
          f'max post-arrival survival {worst}, failures (no death within K-1) {len(fail)}')
    if fail[:3]: print('  examples:', fail[:3])
