import itertools, random
random.seed(12345)

def cyc_black_runs(w):
    n = len(w)
    if 0 not in w: return None
    i0 = w.index(0)
    r = w[i0:] + w[:i0]          # rotate so it starts with white
    runs, L = [], 0
    for x in r + [0]:
        if x == 1: L += 1
        else:
            if L: runs.append(L)
            L = 0
    return runs

def hrun_at(s, t):
    # Lean hypothesis at time t (s[t] white): exists k, k+10<=t, s[t-i]=0 for i<=k, s[t-k-9+j]=1 for j<9
    k = 0
    while t - k >= 0 and s[t - k] == 0:
        if k + 10 <= t and all(s[t - k - 9 + j] == 1 for j in range(9)):
            return True
        k += 1
    return False

# ---- 1) reduction check over all words of length <= 14 ----
good_words = bad_words = 0
red_fail = []
for n in range(1, 15):
    for w in itertools.product([0, 1], repeat=n):
        w = list(w)
        runs = cyc_black_runs(w)
        if runs is None or not runs:       # all-black or all-white blocks
            continue
        all_long = min(runs) >= 9
        for trial in range(3):
            tr = [random.getrandbits(1) for _ in range(random.randint(0, 25))]
            ph = random.randrange(n)
            s = tr + (w[ph:] + w[:ph]) * (8 + 60 // n)
            Tp = len(tr) + n + 10
            whites = [t for t in range(Tp, len(s)) if s[t] == 0]
            holds = all(hrun_at(s, t) for t in whites)
            if all_long and not holds: red_fail.append(('should hold', w, tr, ph))
            if (not all_long) and holds: red_fail.append(('should fail', w, tr, ph))
        good_words += all_long; bad_words += (not all_long)
print("1) words checked: all-runs>=9:", good_words, " others:", bad_words, " reduction mismatches:", len(red_fail))
print("   e.g.", red_fail[:3])

# ---- 2) driven right half from arbitrary states ----
def drive(s, row):
    # returns col1[t], col2[t] for t = 0..len(s)-1 ; row = cells 1..W at time 0
    col1, col2 = [], []
    for t in range(len(s)):
        col1.append(row[0]); col2.append(row[1])
        full = [s[t]] + row + [random.getrandbits(1)]   # arbitrary stuff entering from the far right
        row = [full[i] ^ (full[i + 1] | full[i + 2]) for i in range(len(full) - 2)]
    return col1, col2

fails_key = fails_per = tests = 0
words = []
for n in range(10, 40):
    for _ in range(40):
        # random block with all cyclic black runs >= 9 and at least one white
        while True:
            w = []
            while len(w) < n:
                w += [0] * random.randint(1, 3) + [1] * random.randint(9, 14)
            w = w[:n]
            r = cyc_black_runs(w)
            if r and min(r) >= 9: break
        words.append(w)
for w in words + [[0] + [1] * k for k in range(9, 30)] + [[0] * a + [1] * b for a in range(1, 6) for b in range(9, 14)]:
    n = len(w)
    tr = [random.getrandbits(1) for _ in range(random.randint(0, 40))]
    s = tr + w * (6 + 300 // n)
    row = [random.getrandbits(1) for _ in range(30)]
    col1, col2 = drive(s, row)
    Tp = len(tr) + n + 10
    tests += 1
    for t in range(Tp, len(s) - 1):
        if s[t] == 0 and col1[t] != 1 - s[t - 1]:
            fails_key += 1; break
    # column -1 from left permutivity; must be eventually n-periodic
    cm1 = [s[t + 1] ^ (s[t] | col1[t]) for t in range(len(s) - 1)]
    if any(cm1[t + n] != cm1[t] for t in range(Tp, len(cm1) - n)):
        fails_per += 1
print(f"2) driven tests: {tests}; key-identity failures: {fails_key}; column -1 not periodic: {fails_per}")

# ---- 3) contrast: blocks with a black run of length 8 (should NOT be covered) ----
cnt = 0
for _ in range(200):
    w = [0] + [1] * 8
    tr = [random.getrandbits(1) for _ in range(10)]
    s = tr + w * 40
    col1, _ = drive(s, [random.getrandbits(1) for _ in range(30)])
    Tp = len(tr) + 20
    if any(s[t] == 0 and col1[t] != 1 - s[t - 1] for t in range(Tp, len(s))): cnt += 1
print("3) block 0 1^8: random right-half states where key identity fails somewhere:", cnt, "/ 200")
