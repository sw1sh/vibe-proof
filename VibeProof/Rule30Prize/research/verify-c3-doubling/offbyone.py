import bisect
def seq(Pp, extra, K=40):
    s=[0]
    for _ in range(K): s.append(2*s[-1]+2*Pp+extra)
    return s
def good_ns(S, Pp, nmax):
    # n such that S misses [n-P', 2n)  (integer interval, lower end may be negative)
    out=[]
    for n in range(1, nmax):
        lo=n-Pp; hi=2*n
        i=bisect.bisect_left(S, lo)
        if i==len(S) or S[i]>=hi: out.append(n)
    return out
for Pp in range(1,8):
    A=seq(Pp,1)   # claim's threshold met at every gap: s_{k+1} = 2 s_k + 2P' + 1 > 2 s_k + 2P'
    B=seq(Pp,2)   # corrected threshold: s_{k+1} = 2 s_k + 2P' + 2
    assert all(A[k+1] > 2*A[k]+2*Pp for k in range(len(A)-1))
    ga=good_ns(A,Pp,200000); gb=good_ns(B,Pp,200000)
    print(f"P'={Pp}: claim-threshold S -> #good n<2e5 = {len(ga)}; corrected S -> #good n = {len(gb)}, first few {gb[:4]}")
