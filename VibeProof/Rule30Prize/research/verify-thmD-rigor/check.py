import random, itertools
def rule(a,b,c): return a ^ (b | c)

# Lemma A: column m black for 9 steps; 11 cells m+1..m+11 at time t determine (m+1, m+2) at t+9.
def run_black(row, k):
    for _ in range(k):
        row = [rule(1 if i == 0 else row[i-1], row[i], row[i+1]) for i in range(len(row)-1)]
    return row
bad = [b for b in itertools.product([0,1], repeat=11) if run_black(list(b), 9) != [0,1]]
print("Lemma A: rows failing =", len(bad))
# 8 black steps are not enough (sanity: Lemma A is sharp in the step count)
print("8 steps forces col m+1 white for all 10-cell rows?",
      all(run_black(list(b), 8)[0] == 0 for b in itertools.product([0,1], repeat=10)))

# Theorem D mechanism on the driven right half: arbitrary initial state, driver periodic from 0.
def sim_col1(driver, init, N):
    row = init[:]            # columns 1..W
    col1 = [row[0]]
    for t in range(N):
        left = driver[t]
        row = [rule(left if i == 0 else row[i-1], row[i], row[i+1]) for i in range(len(row)-1)]
        col1.append(row[0])
    return col1

def jneed(K): return (K + 9) // 2      # ceil((K+8)/2)
random.seed(1)
fails = 0; tests = 0
for trial in range(400):
    s = random.randint(9, 14)
    K = random.randint(0, 9)
    j = jneed(K)
    r = 9*j + 1 + random.choice([0, 0, 0, 1, 2])      # at or just above the threshold
    rest = [random.randint(0,1) for _ in range(K)]
    word = [1]*s + [0]*r + rest
    P = len(word)
    # driver: random transient of length Tt, then periodic with the word starting at t1 = Tt
    Tt = random.randint(0, 30)
    N = Tt + 5*P
    driver = [random.randint(0,1) for _ in range(Tt)] + word*6
    init = [random.randint(0,1) for _ in range(N + 3)]
    col1 = sim_col1(driver, init, N)
    e0 = Tt + s
    tests += 1
    ok = all(col1[e0 + i] == col1[e0 + q*P + i] for q in range(1, 4) for i in range(P) if e0 + q*P + i <= N)
    if not ok: fails += 1
print("Theorem D mechanism: tests", tests, "fails", fails)
