# Number of rule 30's 3-state automaton in the Bondarenko et al. (3,2) classification,
# over all 24 symmetric variants (state renaming x letter swap x inversion).
from itertools import permutations
# state -> (root perm 0/1, section on letter 0, section on letter 1); states 0,1,2 = A,B,C
phi = {0: (0, 0, 1), 1: (1, 2, 1), 2: (1, 0, 1)}

def inverse(aut):
    # g = id(g0,g1) -> g^-1 = id(g0^-1, g1^-1);  g = s(g0,g1) -> g^-1 = s(g1^-1, g0^-1)
    return {s: (p, a, b) if p == 0 else (p, b, a) for s, (p, a, b) in aut.items()}

def swap_letters(aut):
    return {s: (p, b, a) for s, (p, a, b) in aut.items()}

def relabel(aut, perm):  # perm[old] = new
    return {perm[s]: (p, perm[a], perm[b]) for s, (p, a, b) in aut.items()}

def number(aut):
    a = {i + 1: (aut[i][0], aut[i][1] + 1, aut[i][2] + 1) for i in range(3)}
    return ((a[1][1] - 1) + 3 * (a[1][2] - 1) + 9 * (a[2][1] - 1) + 27 * (a[2][2] - 1)
            + 81 * (a[3][1] - 1) + 243 * (a[3][2] - 1)
            + 729 * (a[1][0] + 2 * a[2][0] + 4 * a[3][0]) + 1)

nums = set()
for inv in (False, True):
    for sw in (False, True):
        for perm in permutations(range(3)):
            aut = phi
            if inv: aut = inverse(aut)
            if sw: aut = swap_letters(aut)
            nums.add(number(relabel(aut, list(perm))))
print(sorted(nums))
