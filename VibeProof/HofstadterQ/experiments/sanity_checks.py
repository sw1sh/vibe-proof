N = 10**6
# Conway's challenge sequence: last n with |a(n)/n - 1/2| >= 1/20; totality bound a(n) <= n; slow?
a = [0, 1, 1]
for n in range(3, N + 1):
    a.append(a[a[n-1]] + a[n - a[n-1]])
last = max(n for n in range(1, N + 1) if abs(a[n]/n - 0.5) >= 0.05)
print("Conway: last |a(n)/n-1/2|>=1/20 at n =", last,
      "| slow:", all(a[n+1]-a[n] in (0, 1) for n in range(1, N)))
# Hofstadter-Huber V: V(1..4)=1, V(n)=V(n-V(n-1))+V(n-V(n-4)); slow?
V = [0, 1, 1, 1, 1]
for n in range(5, N + 1):
    V.append(V[n - V[n-1]] + V[n - V[n-4]])
print("V-seq slow up to 1e6:", all(V[n+1]-V[n] in (0, 1) for n in range(1, N)))
# Golomb (3,2,1) initial conditions: closed form Q(3k+1)=3, Q(3k+2)=3k+2, Q(3k+3)=3k+1 (k>=1)?
G = [0, 3, 2, 1]
for n in range(4, 10**5):
    G.append(G[n - G[n-1]] + G[n - G[n-2]])
print("Golomb 3,2,1 closed form:", all(G[3*k+1]==3 and G[3*k+2]==3*k+2 and G[3*k+3]==3*k+1 for k in range(1, 3*10**4)))
# Parity-perturbed Q (Mantovanelli): Q(n)=Q(n-Q(n-1))+Q(n-Q(n-2))+(-1)^n
P = [0, 1, 1]; ok = True
for n in range(3, N + 1):
    i, j = n - P[n-1], n - P[n-2]
    if not (1 <= i < n and 1 <= j < n): ok = False; print("perturbed dies at", n); break
    P.append(P[i] + P[j] + (-1)**n)
print("perturbed defined to 1e6:", ok, "| first terms:", P[1:16], "| min lag n-max(Q(n-1),Q(n-2)):",
      min(n - max(P[n-1], P[n-2]) for n in range(3, N + 1)))
