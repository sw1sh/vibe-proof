import sys
def center(n):
    d = open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin','rb').read((n+7)//8)
    return [ (d[i>>3] >> (7-(i&7))) & 1 for i in range(n)]
def bm(s):
    C=[1]; B=[1]; L=0; m=1; prof=[]
    for n in range(len(s)):
        d = s[n]
        for i in range(1, L+1):
            if i < len(C): d ^= C[i] & s[n-i]
        if d:
            T=C[:]
            if len(C) < len(B)+m: C += [0]*(len(B)+m-len(C))
            for i,b in enumerate(B): C[i+m] ^= b
            if 2*L <= n: L = n+1-L; B=T; m=1
            else: m+=1
        else: m+=1
        prof.append(L)
    return prof
N=int(sys.argv[1]); s=center(N); p=bm(s)
for n in [1,2,4,8,16,32,64,128,256,512,1024,2048,N]:
    if n<=N: print(n,p[n-1])
