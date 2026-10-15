# Generate chunk files and the main file for q01 at width W.
# usage: gen.py W K n per_file
import sys, os
W, K, n, per = map(int, sys.argv[1:5])
nch = 1 << (W // 2 - n)
assert nch % per == 0
nfiles = nch // per
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'src', 'KC')
d = os.path.join(base, f'Q01W{W}')
os.makedirs(d, exist_ok=True)
def comb(lo, cnt, name):
    if cnt == 1: return f'(chunksOK_one {name}{lo})'
    h = cnt // 2
    return f'(chunksOK_append {comb(lo, h, name)} {comb(lo + h, cnt - h, name)})'
for j in range(nfiles):
    lo = j * per
    with open(os.path.join(d, f'C{j}.lean'), 'w') as f:
        f.write('import KC.Q01Lanes\n\n')
        f.write(f'/-! Kernel checks for `Q01` at width `{W}`: chunks `{lo}` to `{lo + per - 1}` of `{nch}` '
                f'(`2 ^ {n}` lanes each, `{K}` levels). -/\n\n')
        f.write(f'namespace KC.Q01W{W}.C{j}\nopen KC.Q01Lanes\n\n')
        for c in range(lo, lo + per):
            f.write(f'theorem c{c} : check {W} {K} {n} {c} = true := by decide +kernel\n')
        f.write(f'\ntheorem range : ChunksOK {W} {K} {n} {lo} {per} :=\n  {comb(lo, per, "c")}\n\n')
        f.write(f'end KC.Q01W{W}.C{j}\n')
with open(os.path.join(base, f'Q01W{W}.lean'), 'w') as f:
    for j in range(nfiles): f.write(f'import KC.Q01W{W}.C{j}\n')
    f.write(f'''
/-!
# `Q01` for every start of width at most `{W}` (kernel-checked)

Every start of the zero-boundary left half supported at depths `1, …, {W}` has a white cell at
depth `1` (column `-1`) at some even time `≤ {K - 1}`. The {nch} chunk checks are in
`KC.Q01W{W}.C0` – `KC.Q01W{W}.C{nfiles - 1}`; soundness is `KC.Q01Lanes.q01_of_chunks`.
-/

namespace KC.Q01W{W}
open KC.Q01Lanes Ruliology.CellularAutomata Rule30ZeroBoundary

theorem all_chunks : ChunksOK {W} {K} {n} 0 {nch} :=
''')
    def comb2(lo, cnt):
        if cnt == 1: return f'C{lo}.range'
        h = cnt // 2
        return f'(chunksOK_append {comb2(lo, h)} {comb2(lo + h, cnt - h)})'
    # file-level ranges: each covers `per` chunks
    def combF(j0, m):
        if m == 1: return f'C{j0}.range'
        h = m // 2
        return f'(chunksOK_append {combF(j0, h)} {combF(j0 + h, m - h)})'
    f.write(f'  {combF(0, nfiles)}\n\n')
    f.write(f'''/-- **`Q01` for widths `≤ {W}`**: every start supported at depths `≤ {W}` has a white cell at
depth `1` at some even time `≤ {K - 1}`. -/
theorem q01_width_le_{W} (x : Nat → Bool) (hx : ∀ k, {W} < k → x k = false) :
    ∃ t, t ≤ {K - 1} ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_of_chunks {W} {K} {n} (by decide) all_chunks x hx
  exact ⟨t, by omega, he, hz⟩

/-- The same with the bound `2 W + 8`. -/
theorem q01_width_le_{W}_linear (x : Nat → Bool) (hx : ∀ k, {W} < k → x k = false) :
    ∃ t, t ≤ 2 * {W} + 8 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_width_le_{W} x hx
  exact ⟨t, by omega, he, hz⟩

/-- **`Q01` restricted to widths `≤ {W}`**: no start supported at depths `≤ {W}` is constrained. -/
theorem not_inX_of_width_le_{W} (x : Nat → Bool) (hx : ∀ k, {W} < k → x k = false) : ¬ InX x := by
  intro hX
  obtain ⟨t, _, he, hz⟩ := q01_width_le_{W} x hx
  have := hX (t / 2)
  rw [show 2 * (t / 2) = t by omega, hz] at this
  exact absurd this (by decide)

end KC.Q01W{W}
''')
print('files', nfiles, 'chunks', nch)
