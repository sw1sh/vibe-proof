#!/usr/bin/env python3
"""Randomized sanity checks of the quantitative statements in the MH-reformulation claim
for eventually periodic binary sequences f = x . v^infinity:
  (a) p_f(n) <= T + P for all n (any valid (T, P));
  (b) for n >= T + P no length-n factor is right-special;
  (c) the number of length-n factors occurring infinitely often equals the minimal period for n >= P
      (this is the count of length-n windows over X_f, which equals |X_f| = P_min);
  (d) u = f[T, T+P_min) has eventually constant return words, with occurrences >= T exactly T + k P_min;
  (e) Morse-Hedlund contrapositive data point: first n with p(n) <= n satisfies n <= T + P.
Also a strictness witness: Thue-Morse has bounded runs (<= 2) yet p(n) >= n + 1 on a long prefix."""
import random


def seq(prefix, v, length):
    out = list(prefix)
    while len(out) < length:
        out.extend(v)
    return out[:length]


def min_eventual(f_prefix_len, f, cap):
    """Minimal eventual period and minimal transient, valid since f is given far enough."""
    L = len(f)
    best = None
    for P in range(1, cap + 1):
        # smallest T such that f[t+P] == f[t] for all t in [T, L-P)
        T = L - P
        while T > 0 and f[T - 1 + P] == f[T - 1]:
            T -= 1
        if T <= f_prefix_len + cap:  # holds from a point within the generated region
            best = (T, P)
            break
    return best


def factors(f, n, starts):
    return {tuple(f[i:i + n]) for i in starts}


def check_one(rng):
    T = rng.randint(0, 14)
    P = rng.randint(1, 10)
    prefix = [rng.randint(0, 1) for _ in range(T)]
    v = [rng.randint(0, 1) for _ in range(P)]
    L = 6 * (T + P) + 200
    f = seq(prefix, v, L)
    Tm, Pm = min_eventual(T, f, P)
    assert Pm <= P and Tm <= T
    # periodicity sanity
    assert all(f[t + Pm] == f[t] for t in range(Tm, L - Pm))
    for (TT, PP) in ((T, P), (Tm, Pm)):
        for n in range(1, TT + PP + 12):
            if 2 * (TT + PP) + n + 2 > L:
                break
            # all factors of length n: they all start in [0, TT+PP) by the claim; check by brute force
            allf = factors(f, n, range(0, L - n - 2 * PP - 1))
            assert len(allf) <= TT + PP, ("bound fails", TT, PP, n)
            if n >= TT + PP:
                ext = {}
                for i in range(0, L - n - 2 * PP - 1):
                    u = tuple(f[i:i + n])
                    ext.setdefault(u, set()).add(f[i + n])
                assert all(len(s) == 1 for s in ext.values()), ("right-special", TT, PP, n)
    # (c) infinitely-often factors = factors of the periodic tail (positions >= Tm)
    for n in range(1, 3 * Pm + 3):
        inf_f = factors(f, n, range(Tm, Tm + Pm))
        if n >= Pm:
            assert len(inf_f) == Pm, ("X_f count", n, len(inf_f), Pm)
    # (d) return words of u = f[Tm, Tm+Pm)
    u = f[Tm:Tm + Pm]
    occ = [i for i in range(0, L - Pm) if f[i:i + Pm] == u]
    tail_occ = [i for i in occ if i >= Tm]
    assert tail_occ == list(range(Tm, L - Pm, Pm))[:len(tail_occ)], ("occurrences", Tm, Pm)
    assert all(b - a == Pm for a, b in zip(tail_occ, tail_occ[1:]))
    # (e) first n with p(n) <= n
    for n in range(1, Tm + Pm + 2):
        if len(factors(f, n, range(0, L - n - 2 * Pm - 1))) <= n:
            assert n <= Tm + Pm
            break
    else:
        raise AssertionError("no n <= T+P+1 with p(n) <= n")
    return Tm, Pm


def thue_morse(N):
    return [bin(i).count("1") & 1 for i in range(N)]


def main():
    rng = random.Random(20261015)
    seen = set()
    for _ in range(3000):
        seen.add(check_one(rng))
    print("random eventually periodic checks passed; distinct (Tmin,Pmin) pairs:", len(seen))
    tm = thue_morse(1 << 16)
    runs = []
    cur = 1
    for a, b in zip(tm, tm[1:]):
        if a == b:
            cur += 1
        else:
            runs.append(cur)
            cur = 1
    print("Thue-Morse max run length on 2^16 prefix:", max(runs))
    ok = all(len(factors(tm, n, range(0, len(tm) - n))) >= n + 1 for n in range(1, 41))
    print("Thue-Morse p(n) >= n+1 for n <= 40 on prefix:", ok)


if __name__ == "__main__":
    main()
