import sys, random
# Given free bits f, column-1 sequence a = (1, f0, 1, f1, ...); spatial recurrence gives L(k) = X_k(0).
def Lof(a):
    n = len(a)
    prev = [0]*(n+1)   # X_0
    cur = list(a)      # X_1
    L = [cur[0]]
    for k in range(1, n):
        nxt = [cur[t+1] ^ (cur[t] | prev[t]) for t in range(len(cur)-1)]
        prev, cur = cur, nxt
        L.append(cur[0])
    return L
def col(f):
    a = []
    for b in f: a += [1, b]
    return a
def s(v): return ''.join('1' if x else '0' for x in v)
if __name__ == '__main__':
    n = 60
    tests = {'1^inf': [1]*n, '0^inf': [0]*n, '(01)': [0,1]*(n//2), '(10)': [1,0]*(n//2), '(001)': [0,0,1]*(n//3), '(011)':[0,1,1]*(n//3), '(0111)':[0,1,1,1]*(n//4)}
    random.seed(1)
    for i in range(4): tests['rand%d'%i] = [random.getrandbits(1) for _ in range(n)]
    for name, f in tests.items():
        L = Lof(col(f))
        print(f"{name:8s} f={s(f[:30])}\n         L={s(L[:100])}")
