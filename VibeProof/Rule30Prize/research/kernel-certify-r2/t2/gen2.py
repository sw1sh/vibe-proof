# Generate cycle-segment files and the family theorem for the stripe-prefix family.
import os
K = 32; S = 31; MASK = (1 << K) - 1; SEG = 16384
def fstep(W, fp):
    s1 = 1 - fp; s2 = fp
    return (W ^ (((W << 1) | s1) | ((W << 2) | (s1 << 1) | s2))) & MASK
def stripe(k): return k % 2 == 1
def vget(b, i): return b[i] if 0 <= i < 3 else False
classes = {}
for q in range(2):
    for vb in range(8):
        b = [bool((vb >> i) & 1) for i in range(3)]
        delta = next(j for j in range(1, 6) if vget(b, j - 1) != stripe(q + j))
        W0 = sum(1 << i for i in range(K) if vget(b, delta - 1 + i))
        classes[(q, vb)] = (b, delta, W0, (q + delta) % 2)
cyc = {}
for (q, vb), (b, delta, W0, p0) in classes.items():
    if (W0, p0) in cyc: continue
    W, p = W0, p0; lam = 0; pts = [(0, W, p)]
    while True:
        W = fstep(W, p); p = 1 - p; lam += 1
        if lam % SEG == 0: pts.append((lam, W, p))
        if (W, p) == (W0, p0): break
    if pts[-1][0] != lam: pts.append((lam, W, p))
    cyc[(W0, p0)] = (lam, pts)
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'src', 'KC')
# file grouping: small cycles together; each 65536-cycle in its own file
groups = [[k for k in cyc if cyc[k][0] <= 16384]] + [[k] for k in cyc if cyc[k][0] > 16384]
mods = []
for gi, keys in enumerate(groups):
    name = f'StripeCycles{gi}'; mods.append(name)
    with open(os.path.join(base, name + '.lean'), 'w') as f:
        f.write('import KC.StripeFront\n\n')
        f.write('/-! Kernel-checked front-window cycles (window `32`, post-arrival horizon `31`). -/\n\n')
        f.write(f'namespace KC.StripeFront.{name}\nopen KC.StripeFront\n\n')
        for (W0, p0) in sorted(keys):
            lam, pts = cyc[(W0, p0)]; qq = 1 - p0
            segs = []
            for i in range(len(pts) - 1):
                r, W, p = pts[i]; r2, W2, p2 = pts[i + 1]
                nm = f'seg_{W0}_{p0}_{i}'
                f.write(f'theorem {nm} : seg {K} {S} {qq} {W2} {p2} {r2 - r} {r} {W} {p} = true := by decide +kernel\n')
                segs.append((nm, r, r2 - r, W, p, W2, p2))
            def term(i):
                nm, r, ln, W, p, W2, p2 = segs[i]
                return f'(seg_sound {K} {S} {qq} {W2} {p2} {ln} {r} {W} {p} {nm})'
            t = term(0)
            for i in range(1, len(segs)): t = f'(path_append {t} {term(i)})'
            f.write(f'\ntheorem cyc_{W0}_{p0} : Cycle {K} {S} {W0} {p0} {lam} :=\n  ⟨by decide, by decide, {t}⟩\n\n')
        f.write(f'end KC.StripeFront.{name}\n')
with open(os.path.join(base, 'StripeFamily.lean'), 'w') as f:
    for m in mods: f.write(f'import KC.{m}\n')
    f.write('''
/-!
# The stripe-prefix family `S[1..m] · v · 0^∞`, `|v| ≤ 3`: death within `31` steps of arrival

For every `m` and every word `v = b₀ b₁ b₂` (a shorter word is the same row padded with white), the
start `row3 m b₀ b₁ b₂` (the stripe at depths `1, …, m`, then `v`, then white) has its first
deviation from the stripe at some depth `d ≤ m + 5`, and depth `1` is white at some even time
`≤ d - 1 + 31`. The proof is `family_of_class` (front window, `KC.StripeFront`) with one of eight
kernel-checked periodic window orbits per class `(m mod 2, v)`.
-/

namespace KC.StripeFront
''')
    for m in mods: f.write(f'open KC.StripeFront.{m}\n')
    f.write('''open Ruliology.CellularAutomata Rule30ZeroBoundary

theorem cycle_congr {K S W0 W0' p0 p0' lam : Nat} (h1 : W0 = W0') (h2 : p0 = p0')
    (h : Cycle K S W0' p0' lam) : Cycle K S W0 p0 lam := by subst h1 h2; exact h

/-- **The stripe-prefix family dies.** For every `m` and `b₀ b₁ b₂`, the first deviation `d` of
`S[1..m] · b₀ b₁ b₂ · 0^∞` from the stripe satisfies `d ≤ m + 5`, and depth `1` is white at some even
time `t ≤ d - 1 + 31`. -/
theorem stripe_prefix_family (m : Nat) (b0 b1 b2 : Bool) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 5 ∧ (∀ k, 1 ≤ k → k < d → row3 m b0 b1 b2 k = stripe k) ∧
      row3 m b0 b1 b2 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row3 m b0 b1 b2) t 1 = false := by
  rcases Nat.mod_two_eq_zero_or_one m with hq | hq <;> cases b0 <;> cases b1 <;> cases b2
''')
    order = []
    for q in range(2):
        for b0 in (False, True):
            for b1 in (False, True):
                for b2 in (False, True):
                    order.append((q, b0, b1, b2))
    for (q, b0, b1, b2) in order:
        vb = int(b0) + 2 * int(b1) + 4 * int(b2)
        b, delta, W0, p0 = classes[(q, vb)]
        lam = cyc[(W0, p0)][0]
        bl = lambda z: 'true' if z else 'false'
        f.write(f'''  · obtain ⟨h1, h2, h3⟩ := family_of_class m {q} {delta} {lam} {bl(b0)} {bl(b1)} {bl(b2)} hq (by omega) (by decide)
      (cycle_congr (by decide) (by decide) cyc_{W0}_{p0})
    exact ⟨m + {delta}, by omega, by omega, h1, h2, h3⟩
''')
    f.write('''
/-- The same for a word given as a list of length `≤ 3`. -/
def rowV (m : Nat) (v : List Bool) (k : Nat) : Bool := if k ≤ m then stripe k else v.getD (k - m - 1) false

theorem rowV_eq (m : Nat) (v : List Bool) (hv : v.length ≤ 3) :
    rowV m v = row3 m (v.getD 0 false) (v.getD 1 false) (v.getD 2 false) := by
  funext k
  unfold rowV row3 vget
  by_cases hk : k ≤ m
  · simp [hk]
  · simp only [hk, if_false]
    rcases (show k - m - 1 = 0 ∨ k - m - 1 = 1 ∨ k - m - 1 = 2 ∨ 3 ≤ k - m - 1 by omega) with h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl

/-- **Stripe-prefix family, list form.** For every `m` and every word `v` with `|v| ≤ 3`, the start
`S[1..m] · v · 0^∞` deviates from the stripe first at some depth `d ≤ m + 5` and has a white cell
at depth `1` at some even time `≤ d - 1 + 31`. -/
theorem stripe_prefix_family_list (m : Nat) (v : List Bool) (hv : v.length ≤ 3) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 5 ∧ (∀ k, 1 ≤ k → k < d → rowV m v k = stripe k) ∧ rowV m v d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (rowV m v) t 1 = false := by
  rw [rowV_eq m v hv]
  exact stripe_prefix_family m _ _ _

end KC.StripeFront
''')
print('modules', mods)
for k, (lam, pts) in sorted(cyc.items()): print(k, lam, len(pts) - 1, 'segments')
