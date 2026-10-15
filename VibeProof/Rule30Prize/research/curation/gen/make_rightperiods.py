import sys
R = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/'
rp = open(R + 'diagonal/lean/RightPeriods.lean').read().split('\n')
ext = open(R + 'verify-rows-pow2/RP_ext.lean').read().split('\n')
ms = open(R + 'verify-monostep/MonoStep.lean').read().split('\n')
def L(lines, a, b):  # 1-indexed inclusive
    return '\n'.join(lines[a - 1:b])

header = r'''import Ruliology.CellularAutomata.Rule30Diagonals
import Ruliology.CellularAutomata.Rule30Window

/-!
# Rule 30: the periods of the right diagonals

`R j t = cell t (t - j)` is the `j`-th diagonal from the right edge. `Rule30Diagonals.R_periodic`
says it repeats with period `2^j`. Here the periods are pinned down much further. Write
`Per j p` for "`R j` repeats with period `p` from time `0`", and `e_j` for the least `e` with
`Per j (2^e)` (`IsE j e`; it exists by `exists_IsE`).

**Monotonicity and the doubling rule.**
* `per_mono_all`: if `R (j + 1)` repeats with some period `H`, so does every `R i`, `i ≤ j`.
  So `e_0 ≤ e_1 ≤ e_2 ≤ …` (`e_mono`). The proof descends from a white light-cone triangle that
  diagonal `j + 1` repeats at time `H`: two white diagonals force the two before them white
  (`Z_down`).
* `shift_formula`: if `R j` has period `H`, then `R (j+1) (t + H) = R (j+1) t xor R (j+1) H`.
* `e_step`: **`e_{j+1} = e_j + [R_{j+1}(2^{e_j}) = 1]`**: the period doubles exactly when the cell
  at time `2^{e_j}` on the next diagonal is black (`per_succ_iff`), and then a shift by half the
  new period complements the diagonal (`antiperiod`) and every window of one period is exactly
  half black (`half_black`).
* `S_rule`, `inp_least_period`: for `j ≥ 3` the input `R (j-1) || R (j-2)` of diagonal `j` has
  least period `2^{e_{j-1}}`, and `e_j - e_{j-1}` is the parity of the number of black input
  cells in one such period.
* `no_three`: the period never doubles three times in a row.

**Bounds.**
* `period_gt`: every period of `R j`, `j ≥ 1`, exceeds `⌈j / 2⌉`; `not_per_small`:
  `j < 2^(e_j + 1)`. So the periods are unbounded.
* `per_bound`: `j ≤ 2^(e_j + 1) - 2`, that is `e_j ≥ log₂ (j + 2) - 1`.
* `per_upper`: `e_j ≤ (2j + 1) / 3` for `j ≥ 2`.
* `per_14`, `per_23`, `not_half_lower`: `e_14 ≤ 6` and `e_23 ≤ 8` (kernel computation of rows
  `64` and `256`), so the guess `e_j ≥ ⌊j/2⌋` is false.

**Rows at powers of two.**
* `per_iff_gap`: `R n` has period `2^k` iff row `2^k` has `n` white cells left of its right
  edge.
* `rows_at_powers_of_two`: for every `k` there is `J` with `k ≤ J ≤ 2^(k+1) - 2` such that the
  diagonals of period `2^k` are exactly `R 0, …, R J`; every row `2^k u`, `u` odd, reads
  `1 0^J 1` leftwards from its right edge (`zero_gap_cell`); and row `2^k - 1` ends in `J + 1`
  black cells preceded by a white one (`last_one`, `last_white`).
* `restart`, `center_restart`, `column_continuity`: the pattern restarts at the right edge.
  Column `2^k u` repeats `c(0), …, c(J)`, and columns `p` and `p + 2^k u` agree `s` steps after
  the right edge reaches them whenever `R s` has period `2^k`.
* `center_black_lt`: a black center cell `c(t)` lies in the first period of its diagonal:
  `t < 2^{e_t}`.

None of this reaches the center column `c(t) = R t t`: by `center_black_lt` the center cell is
always in the first period of its own diagonal.

Sources: the Rule 30 Prize project (2026), right-diagonal analysis; the general-period
monotonicity, the exact doubling rule, the input periods and the rows at powers of two were
added by its independent verification passes. Wolfram (*A New Kind of Science*, 2002, and the
2019 prize announcement) notes that the right-side diagonal periods grow exponentially.
-/

namespace Ruliology.CellularAutomata
namespace Rule30RightPeriods

open Rule30Jen Rule30Diagonals
'''

out = [header]
# basic facts (RightPeriods 38-82) + mod2_add (MonoStep 44-54)
out.append(L(rp, 38, 82))
out.append('')
out.append(L(ms, 44, 54))
out.append('')
# periods (RightPeriods 84-124)
out.append(L(rp, 84, 124))
out.append('')
# PerF for general sequences (MonoStep 74-75, 80-84, 90-105)
out.append('/-! ### Periods of general sequences -/')
out.append('')
out.append(L(ms, 74, 75))
out.append('')
out.append(L(ms, 80, 84))
out.append('')
out.append(L(ms, 90, 105))
out.append('')
# accumulation (RightPeriods 126-141)
out.append(L(rp, 126, 141))
out.append('')
# halving: Z, Z_down, Z_iter, Z_mono (RightPeriods 143-173)
out.append(L(rp, 143, 173))
out.append('')
# MonoStep Z_bottom .. halve (170-239)
out.append(L(ms, 170, 239))
out.append('')
# per_mono_all (general), from MonoStep mono_all
mono = L(ms, 240, 252).replace('theorem mono_all {j H : Nat}', 'theorem per_mono_all {j H : Nat}')
mono = mono.replace('/-- (a) for every `j` and every `H`. -/',
    '/-- **Monotonicity**: if diagonal `j + 1` repeats with period `H`, so do all diagonals up to\n`j`. In particular `e_j ≤ e_{j+1}`. -/')
out.append(mono)
out.append('''
theorem per_mono {j H : Nat} (h : Per (j + 1) H) : Per j H :=
  per_mono_all h j (Nat.le_refl j)

theorem per_mono_le {i j H : Nat} (hij : i ≤ j) (h : Per j H) : Per i H := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact h
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact per_mono_all h i (by omega)
''')
# shift formula (MonoStep 254-271), general H
sf = L(ms, 254, 271).replace('mono_all h j (Nat.le_refl j)', 'per_mono_all h j (Nat.le_refl j)')
sf = sf.replace('/-! ### (b) shift formula -/', '/-! ### The shift formula and the doubling criterion -/\n\n/-- **Shift formula**: if diagonal `j` repeats with period `H`, a shift of `H` adds the\nconstant `R (j+1) H` to diagonal `j + 1`. -/')
out.append(sf)
out.append('''
/-- **Doubling criterion**: given period `H` on diagonal `j`, diagonal `j + 1` keeps the period
`H` exactly when its cell at time `H` is white. -/
theorem per_succ_iff {j H : Nat} (h : Per j H) :
    Per (j + 1) H ↔ R (j + 1) H = false := by
  constructor
  · intro hp
    have := hp 0
    rwa [Nat.zero_add, R_init (by omega)] at this
  · intro h0 t
    rw [shift_formula h t, h0]; cases R (j + 1) t <;> rfl

/-- When the cell at time `H` is black, a shift by `H` complements diagonal `j + 1`. -/
theorem antiperiod_of_black {j H : Nat} (h : Per j H) (hb : R (j + 1) H = true) :
    ∀ t, R (j + 1) (t + H) = !R (j + 1) t := by
  intro t; rw [shift_formula h t, hb]; cases R (j + 1) t <;> rfl

/-- When the period doubles, the diagonal is complemented by a shift of half its period. -/
theorem antiperiod {j H : Nat} (h : Per j H) (hn : ¬ Per (j + 1) H) :
    ∀ t, R (j + 1) (t + H) = !R (j + 1) t := by
  have h1 : R (j + 1) H = true := by
    cases h' : R (j + 1) H
    · exact absurd ((per_succ_iff h).2 h') hn
    · rfl
  exact antiperiod_of_black h h1
''')
# per_step (RightPeriods 307-312)
out.append(L(rp, 307, 312))
out.append('')
# RightPeriods 314-588 (zero_gap .. not_half_lower)
out.append(L(rp, 314, 588))
out.append('')
# period_gt (general)
out.append('''/-- **Every period of diagonal `j ≥ 1` exceeds `⌈j / 2⌉`**: the diagonal is white before time
`⌈j / 2⌉` and black at that time (the left edge). -/
theorem period_gt {j P : Nat} (hj : 1 ≤ j) (hP : 0 < P) (h : Per j P) : (j + 1) / 2 < P := by
  refine Nat.lt_of_not_le fun hle => ?_
  have e := h ((j + 1) / 2 - P)
  rw [show (j + 1) / 2 - P + P = (j + 1) / 2 by omega, R_half hj,
    R_lt (show 2 * ((j + 1) / 2 - P) < j by omega)] at e
  exact absurd e (by decide)
''')
# RP_ext additions 598-686 (inside our namespace already)
ext_block = L(ext, 598, 672)
out.append('/-! ### The last diagonal of period `2^k` -/')
out.append('')
out.append(ext_block)
out.append('')
# MonoStep (c) and (d): 273-455
mc = L(ms, 273, 448)
mc = mc.replace('/-! ### (c) the exponent `e_j` -/', '/-! ### The least exponent `e_j` -/')
mc = mc.replace('PerF.pow_mono hpk (by omega)', 'Per.pow_mono hpk (by omega)')
mc = mc.replace('he.le (mono_all he\'.1 j (Nat.le_refl j))', 'he.le (per_mono_all he\'.1 j (Nat.le_refl j))')
mc = mc.replace('mono_all (j := n + 1) h2 (n + 1) (Nat.le_refl _)', 'per_mono_all (j := n + 1) h2 (n + 1) (Nat.le_refl _)')
mc = mc.replace('/-! ### (d) the input `g` -/', '/-! ### The input of a diagonal -/')
anti = '''/-- When the period doubles, a shift by half the new period complements the diagonal. -/
theorem antiperiod {j e : Nat} (h : Per j (2 ^ e)) (hb : R (j + 1) (2 ^ e) = true) :
    ∀ t, R (j + 1) (t + 2 ^ e) = !R (j + 1) t := by
  intro t; rw [shift_formula h t, hb]; cases R (j + 1) t <;> rfl
'''
assert mc.count(anti) == 1
mc = mc.replace(anti, '')
mc = mc.replace('cnt_compl (antiperiod h hb) a (2 ^ e)', 'cnt_compl (antiperiod_of_black h hb) a (2 ^ e)')
out.append(mc)
out.append('')
out.append('end Rule30RightPeriods')
out.append('end Ruliology.CellularAutomata')
open(R + 'staging/Ruliology/CellularAutomata/Rule30RightPeriods.lean', 'w').write('\n'.join(out) + '\n')
print('written')

# --- docstring cleanup (verifier labels) ---
p = R + 'staging/Ruliology/CellularAutomata/Rule30RightPeriods.lean'
s = open(p).read()
reps = [
 ('/-- Step 3: from the white strip, every diagonal `i ≤ n + 2` has period `H`. -/',
  '/-- From the white strip, every diagonal `i ≤ n + 2` has period `H`. -/'),
 ('/-- Step 1: a period `H` of diagonal `n + 3` yields the white strip. -/',
  '/-- A period `H` of diagonal `n + 3` yields the white strip. -/'),
 ('/-- (a) for `j = n + 2 ≥ 2`, any `H`. -/',
  '/-- **Halving lemma**: a period `H` of diagonal `n + 3` is a period of every diagonal up to\n`n + 2`. -/'),
 ('/-- (c), second sentence: row `2^k - 1` has `J + 1` black cells at its right end (`R 0 … R J`),',
  '/-- Row `2^k - 1` has `J + 1` black cells at its right end (`R 0 … R J`),'),
 ('/-- (d): any diagonal with period `2^k` has index at most `2^(k+1) - 2`. -/',
  '/-- Any diagonal with period `2^k` has index at most `2^(k+1) - 2`. -/'),
 ('/-- (b) packaged with `J_k`: for every `k` there is `J ≥ k` with `J ≤ 2^(k+1) - 2` such that every',
  '/-- **Rows at powers of two.** For every `k` there is `J ≥ k` with `J ≤ 2^(k+1) - 2` such that every'),
 ('/-- (c) `e_{j+1} = e_j + [R_{j+1}(2^{e_j})]`. -/',
  '/-- **Doubling rule**: `e_{j+1} = e_j + [R_{j+1}(2^{e_j})]`. -/'),
 ("In the claim's notation `g_{j+2} = inp j`. -/", "Write `g_{j+2} = inp j`. -/"),
 ('/-- Step 1 under the weaker hypothesis that only the input `g_{n+3} = inp (n+1)` has period `H`. -/',
  '/-- The white strip, assuming only that the input `g_{n+3} = inp (n+1)` has period `H`. -/'),
 ("/-- (a') The halving lemma with the hypothesis on the input only (any `H`). -/",
  '/-- The halving lemma with the hypothesis on the input only (any `H`). -/'),
 ('/-- (d) Every period `p > 0` of the input `g_{n+3}` is a multiple of `2^{e_{n+2}}`; with',
  '/-- Every period `p > 0` of the input `g_{n+3}` is a multiple of `2^{e_{n+2}}`; with'),
 ('/-- (d) S-rule: for `j = n + 3`, `e_j = e_{j-1} + parity(g_j on [0, 2^{e_{j-1}}))`, where',
  '/-- **Parity rule**: for `j = n + 3`, `e_j = e_{j-1} + parity(g_j on [0, 2^{e_{j-1}}))`, where'),
]
for a, b in reps:
    assert s.count(a) == 1, a
    s = s.replace(a, b)
open(p, 'w').write(s)
print('cleaned')

s = open(p).read()
reps2 = [
 ('''None of this reaches the center column `c(t) = R t t`: by `center_black_lt` the center cell is
always in the first period of its own diagonal.''',
  '''None of this reaches the center column `c(t) = R t t`. It sits on diagonal `t` at time `t`, and
when it is black it lies inside the first period `2^{e_t}` of that diagonal (`center_black_lt`).
The proved bounds leave the growth of the period `2^{e_j}` between linear (`j + 2 ≤ 2^{e_j + 1}`)
and `2^{(2j+1)/3}`; numerically `e_j ≈ 0.43 j`.'''),
 ('''Sources: the Rule 30 Prize project (2026), right-diagonal analysis; the general-period
monotonicity, the exact doubling rule, the input periods and the rows at powers of two were
added by its independent verification passes. Wolfram (*A New Kind of Science*, 2002, and the
2019 prize announcement) notes that the right-side diagonal periods grow exponentially.''',
  '''Sources: the Rule 30 Prize project (2026), right-diagonal analysis; the general-period
monotonicity, the exact doubling rule, the input periods and the rows at powers of two were
added by its independent verification passes. The diagonals and their recurrence are in
`Rule30Diagonals`.'''),
]
for a, b in reps2:
    assert s.count(a) == 1, a
    s = s.replace(a, b)
open(p, 'w').write(s)
print('cleaned2')

s = open(p).read()
anchor = "/-- **A black center cell lies in the first period of its diagonal**"
add = '''/-- **Rows restart at the right edge**: if diagonal `J` has period `2^k`, the right end of row
`2^k + s` copies row `s`: `cell (2^k + s) (2^k + q) = cell s q` for `s - J ≤ q ≤ s`. When
`2s ≤ J` this covers all of row `s`, preceded by white cells. -/
theorem row_restart {J k : Nat} (hJ : Per J (2 ^ k)) (s : Nat) (q : Int)
    (hq0 : (s : Int) - J ≤ q) (hq1 : q ≤ s) :
    cell (2 ^ k + s) (((2 ^ k : Nat) : Int) + q) = cell s q := by
  obtain ⟨j, hj⟩ : ∃ j : Nat, (j : Int) = (s : Int) - q := ⟨((s : Int) - q).toNat, by omega⟩
  have hper : Per j (2 ^ k) := per_mono_le (by omega) hJ
  have e := hper s
  unfold R at e
  rw [show s + 2 ^ k = 2 ^ k + s by omega] at e
  rw [cell_congr (show ((2 ^ k + s : Nat) : Int) - (j : Int) = ((2 ^ k : Nat) : Int) + q by omega),
    cell_congr (show (s : Int) - (j : Int) = q by omega)] at e
  exact e

'''
assert s.count(anchor) == 1
s = s.replace(anchor, add + anchor)
old_doc = """* `restart`, `center_restart`, `column_continuity`: the pattern restarts at the right edge."""
new_doc = """* `restart`, `row_restart`, `center_restart`, `column_continuity`: the pattern restarts at the
  right edge. Row `2^k + s` ends with a copy of row `s` (for `2s ≤ J`, all of it)."""
assert s.count(old_doc) == 1
s = s.replace(old_doc, new_doc)
open(p, 'w').write(s)
print('row_restart added')
