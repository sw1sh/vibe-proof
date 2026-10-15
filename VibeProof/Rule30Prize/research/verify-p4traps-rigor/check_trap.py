# Independent checker for exported trap files "phase state pos".
# Strip = columns 1..b of the right half; bit (p-1) of state = cell(t,p).
# Column 0 at phase ph is w[ph]; column b+1 is free (both values allowed).
# Rule 30 via Wolfram numbering: new = (30 >> (4*l + 2*c + r)) & 1, l = column p-1.
import sys

def rule30(l, c, r):
    return (30 >> (4 * l + 2 * c + r)) & 1

def load(fn):
    with open(fn) as f:
        lines = [ln for ln in f.read().split('\n') if ln.strip()]
    w, b, n = lines[0].split()
    b = int(b); n = int(n)
    ent = [tuple(map(int, ln.split())) for ln in lines[1:]]
    return w, b, n, ent

def succ(w, b, ph, s):
    P = len(w)
    row = [int(w[ph])] + [(s >> (p - 1)) & 1 for p in range(1, b + 1)]  # index 0..b
    out = set()
    for r in (0, 1):
        ext = row + [r]  # index b+1
        new = [rule30(ext[p - 1], ext[p], ext[p + 1]) for p in range(1, b + 1)]
        s2 = 0
        for p in range(1, b + 1):
            s2 |= new[p - 1] << (p - 1)
        out.add(((ph + 1) % P, s2))
    return out

def check(fn, u):
    w, b, n, ent = load(fn)
    P = len(w); m = len(u)
    S = {}
    for (ph, s, pos) in ent:
        assert 0 <= ph < P and 0 <= s < (1 << b), (ph, s)
        assert (ph, s) not in S, "duplicate"
        S[(ph, s)] = pos
    assert len(S) == n == len(ent), (len(S), n, len(ent))
    bad_closure = bad_label = bad_out = 0
    nedges = 0
    for (ph, s), pos in S.items():
        white = (w[ph] == '0')
        if white and (s & 1) != int(u[pos % m]):
            bad_out += 1
        for y in succ(w, b, ph, s):
            nedges += 1
            if y not in S:
                bad_closure += 1
            elif S[y] % m != (pos + (1 if white else 0)) % m:
                bad_label += 1
    phases = sorted(set(ph for (ph, s) in S))
    print(f"{fn.split('/')[-1]}: w={w} b={b} n={n} m={m} u={u} phases={phases} edges={nedges} "
          f"closure_violations={bad_closure} label_violations={bad_label} output_violations={bad_out}")
    return bad_closure == 0 and bad_label == 0 and bad_out == 0

if __name__ == '__main__':
    ok = check(sys.argv[1], sys.argv[2])
    print("PASS" if ok else "FAIL")
