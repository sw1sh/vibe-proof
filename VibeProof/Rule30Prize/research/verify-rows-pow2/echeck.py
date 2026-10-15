brief_e = list(map(int, "0 1 1 2 3 3 4 5 5 6 6 6 6 6 6 7 8 8 8 8 8 8 8 8 9 10 10 11 11 12 12 12 12 12 13 13 14 15 15 16 16 17 17 18 18 18 18 18 19 20 20 21 21 21 22 23 23 23 24 24 25 25 25 26 27 27 28 28 28 29 30 30 31 31 32".split()))
assert len(brief_e) == 75
J = list(map(int, "0 2 3 5 6 8 14 15 23 24 26 28 33 35 36 38 40 42 47 48 50 53 54 57 59 62 63 65 68 69 71 73 76 78 79 81 83 85".split()))
assert len(J) == 38
# my computed J (direct sim E<=20, window E<=37)
mine = [0,2,3,5,6,8,14,15,23,24,26,28,33,35,36,38,40,42,47,48,50,53,54,57,59,62,63,65,68,69,71,73,76,78,79,81,83,85]
print("claimed J == my J:", J == mine)
# e_j derived from J: e_j = min{E : J_E >= j}, defined for j <= J_37
e_from_J = [min(E for E in range(38) if J[E] >= j) for j in range(J[37]+1)]
print("e from J agrees with brief for j<=74:", e_from_J[:75] == brief_e)
print("e_75..e_85 from J:", e_from_J[75:86])
print("claimed:           ", [32,32,33,33,34,35,35,36,36,37,37])
# J from brief where determined (J_E determined by brief iff some e_j > E among j<=74)
for E in range(38):
    if any(e > E for e in brief_e):
        Jb = max(j for j in range(75) if brief_e[j] <= E)
        assert Jb == J[E], E
print("J_E determined by brief agree for E <=", max(E for E in range(38) if any(e > E for e in brief_e)))
# (d) J_k <= 2^{k+1}-2 and J_k >= k
print("(d) holds:", all(J[k] <= 2**(k+1)-2 for k in range(38)), " J_k>=k:", all(J[k] >= k for k in range(38)))
# monotone steps of e in {0,1}
print("steps in {0,1}:", all(e_from_J[j]-e_from_J[j-1] in (0,1) for j in range(1,86)))
