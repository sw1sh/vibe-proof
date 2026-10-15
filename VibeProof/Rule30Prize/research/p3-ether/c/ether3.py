# Verify the 12x3 rule-30 ether and list alignments of 001 and 011 (independent Python check).
E = ["001","001","011","110","010","010","110","101","100","100","101","011"]
N = len(E); P = 3
def rule(a,b,c): return a ^ (b | c)
ok = True
for ph in range(P):
    for j in range(N):
        new = rule(int(E[(j-1)%N][ph]), int(E[j][ph]), int(E[(j+1)%N][ph]))
        if new != int(E[j][(ph+1)%P]): ok = False; print("FAIL", j, ph)
print("ether is a rule-30 orbit:", ok)
for w in ["001","011"]:
    al = [(j,s) for j in range(N) for s in range(P) if all(E[j][(psi+s)%P]==w[psi] for psi in range(P))]
    print(w, "alignments (j0,s):", al)
# white phases of each column
for j in range(N):
    print(j, E[j], "white phases", [ph for ph in range(P) if E[j][ph]=='0'])
