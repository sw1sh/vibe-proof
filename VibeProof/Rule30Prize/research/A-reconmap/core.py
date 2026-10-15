# Core: ZBL (zero-boundary left half) in u-coordinates, u_t(k) = cell(T+t, -k), k >= 1.
#   forward:  u_{t+1}(k) = u_t(k+1) xor (u_t(k) or u_t(k-1)),  u_t(0) = 0
#   inverse:  u_t(k+1) = u_{t+1}(k) xor (u_t(k) or u_t(k-1))
# Period-2 constraint (phase c(T)=1): u_{2s}(1) = 1; free bits f_s = u_{2s+1}(1).
# L(k) = u_0(k).

def recon_y(y):
    """y: list of bits y_0..y_{n-1} (column k=1). Returns L(1..n) as list (index 0 -> k=1)."""
    n = len(y)
    col = 0
    for t, b in enumerate(y):
        if b: col |= 1 << t
    prev = 0
    L = [col & 1]
    for k in range(1, n):
        new = (col >> 1) ^ (col | prev)
        prev, col = col, new
        L.append(col & 1)
    return L

def y_of_f(f):
    y = []
    for b in f:
        y.append(1); y.append(b)
    y.append(1)
    return y

def L_of_f(f):
    """f: list of m free bits -> L(1..2m+1)."""
    return recon_y(y_of_f(f))

def forward(u, steps):
    """u: list, u[0] = u(1). Returns list of rows (each list), rows[0] = u. Width grows by 1 per step."""
    rows = [list(u)]
    cur = list(u)
    for _ in range(steps):
        n = len(cur)
        ext = [0] + cur + [0, 0]      # ext[k] = u(k), k=0..n+1
        new = [ext[k + 1] ^ (ext[k] | ext[k - 1]) for k in range(1, n + 2)]
        cur = new
        rows.append(cur)
    return rows

# Bit-sliced versions over all 2^m assignments of f_0..f_{m-1}
def var_mask(i, m):
    N = 1 << m
    blk = 1 << i
    pat = ((1 << blk) - 1) << blk
    x = pat; period = 2 * blk; reps = N // period; cur = 1
    while cur < reps:
        x |= x << (period * cur); cur *= 2
    return x & ((1 << N) - 1)

def L_sliced(m):
    """Returns (ALL, F, L) where F[i] is the truth table of f_i and L[k-1] truth table of L(k), k = 1..2m+1."""
    N = 1 << m
    ALL = (1 << N) - 1
    F = [var_mask(i, m) for i in range(m)]
    y = []
    for i in range(m):
        y.append(ALL); y.append(F[i])
    y.append(ALL)
    n = len(y)
    # columns as lists over t of truth tables
    prev = [0] * n
    col = y[:]
    L = [col[0]]
    for k in range(1, n):
        new = [col[t + 1] ^ (col[t] | prev[t]) for t in range(len(col) - 1)]
        prev, col = col[:len(new)], new
        L.append(col[0])
    return ALL, F, L

def L_sliced_even(m, extra_odd=True):
    """Bit-sliced over all 2^m assignments of E_0..E_{m-1} = L(2), L(4), ..., L(2m).
    Returns (ALL, E, Fs, L) with Fs[s] truth table of f_s, L[k-1] truth table of L(k) for k = 1..2m+1."""
    N = 1 << m
    ALL = (1 << N) - 1
    E = [var_mask(i, m) for i in range(m)]
    Dkm1 = []   # D_{k-1}
    Dk = []     # D_k  (D_0 = [])
    L = []
    Fs = []
    for k in range(0, 2 * m + 1):
        # compute S_k = XOR_{j=0}^{k-1} (D_k[j] | D_{k-1}[j])  (D_{k-1}[k-1] = 0)
        # and D_{k+1}
        if k % 2 == 0:
            yk = ALL
        else:
            S = 0
            for j in range(k):
                S ^= Dk[j] | (Dkm1[j] if j < len(Dkm1) else 0)
            s = k // 2
            yk = E[s] ^ S
            Fs.append(yk)
        Dn = [0] * (k + 1)
        Dn[k] = yk
        for j in range(k - 1, -1, -1):
            Dn[j] = Dn[j + 1] ^ (Dk[j] | (Dkm1[j] if j < len(Dkm1) else 0))
        L.append(Dn[0])
        Dkm1, Dk = Dk, Dn
    return ALL, E, Fs, L

def anf(tt, m):
    """Moebius transform of truth table (int with 2^m bits) -> set of monomials (bitmasks)."""
    N = 1 << m
    bits = [(tt >> i) & 1 for i in range(N)]
    for i in range(m):
        step = 1 << i
        for x in range(N):
            if x & step:
                bits[x] ^= bits[x ^ step]
    return [x for x in range(N) if bits[x]]

def mono_str(x, names):
    if x == 0: return '1'
    return ''.join(names[i] for i in range(len(names)) if (x >> i) & 1)
