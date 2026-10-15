R = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/'
sp = open(R + 'smallperiods/lean/PeriodTwo.lean').read().split('\n')
p2 = open(R + 'complexity/lean/Rule30Period2.lean').read().split('\n')
def L(lines, a, b):
    return '\n'.join(lines[a - 1:b])

header = r'''import Ruliology.CellularAutomata.Rule30BlackRuns
import Ruliology.CellularAutomata.Rule30DrivenLeft

/-!
# Rule 30: what an eventual period 2 of the center column would force

Period `1` is excluded (`Rule30Prize.center_not_eventually_constant`); period `2` is the first
open case. This module records the structure that an eventual period `2` would force and reduces
its exclusion to a question about the left half alone.

**Normal form.** `normalize`: if `c (t + 2) = c t` for all `t ≥ T₀`, then there is `T` with
`c (T + 2k) = 1` and `c (T + 2k + 1) = 0` for all `k` (the column is not eventually constant).

**The forced skeleton.** With `c` alternating from `T` as above, write `s k = cell (T+2k+1) (-1)`.
* `m1_even`: column `-1` is black at every time `T + 2k`.
* `p1_odd`: column `1` at time `T + 2k + 1` is `!s k`.
* `golden`: `s` never has two consecutive zeros, so the white cells of column `-1` are at least
  four steps apart.
* `m2_even`, `m2_odd`, `m3_even`, `m3_odd`: columns `-2`, `-3` are functions of `s`;
  `m4_odd`: column `-4` is white at every time `T + 2k + 1`.
* `no_AA`, `no_BB`, `no_ABAB`, `col4_white_of_alt`: the same kind of constraint from a finite
  window of alternation (white first): column `1` at four consecutive steps never reads `0000`
  or `0101`, at eight steps never `00010001`, and with `c = 0 1 0 1 0` on `[t, t + 4]` column
  `-4` is white at `t`. Finite checks over all window contents.

**Reduction to the zero-driven left half.** By the effective boundary
(`Rule30MaskedJen.effective_step`), the left half sees `c` only through `c t && c (t + 1)`,
which is white once `c` alternates (`effective_white`). So from time `T` on, columns `p < 0`
evolve as rule 30 on the half-line with column `0` held white (`left_half_zero_driven`), started
from a finite row whose leftmost black cell is at `-T`.
* `Q01`: **the open question.** No start of the zero-driven left half with a leftmost black
  cell keeps column `-1` black at every even step.
* `not_eventually_period_two_of_Q01`: **`Q01` implies that the center column is not eventually
  2-periodic**, for every transient.
* `stripe_fixed`, `stripe_col`: the infinite stripe (black exactly at the odd positions `< 0`)
  is fixed by the zero-driven left half and keeps column `-1` black at every step. So the
  finiteness hypothesis in `Q01` is essential.

`Q01` is not proved here. Exhaustive searches (Rule 30 Prize project) found that for every start
of support width at most `39`, column `-1` turns white at an even step within about `2W` steps.

Sources: the Rule 30 Prize project (2026), period-2 analysis; the effective boundary and the
reduction are from its left-half analysis.
-/

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwo

open Rule30Jen Rule30Prize Rule30MaskedJen Rule30BlackRuns Rule30DrivenLeft

/-! ### Normal form -/

theorem step' (t : Nat) (p a b d : Int) (ha : a = p - 1) (hb : b = p) (hd : d = p + 1) :
    cell (t + 1) p = rule (cell t a) (cell t b) (cell t d) := by
  subst ha hb hd; rfl
'''
out = [header]
# normalize (Rule30Period2 lines from '/-- Every eventual period 2' to before 'end R30Period2')
i = next(k for k, l in enumerate(p2) if l.startswith('/-- Every eventual period 2'))
j = next(k for k, l in enumerate(p2) if l.startswith('end R30Period2'))
out.append('\n'.join(p2[i:j]).rstrip())
out.append('')
out.append('/-! ### Finite windows of alternation -/')
out.append('')
col1 = r'''/-- Column-1 word of the right half: run the row with the given center values and record its
first cell before each step. -/
def col1 : List Bool → List Bool → List Bool
  | [], _ => []
  | c :: cs, l => l.headD false :: col1 cs (stepRow c l)

theorem col1_rowAt : ∀ (cs : List Bool) (t n : Nat),
    (∀ i, (h : i < cs.length) → cell (t + i) 0 = cs[i]) →
    col1 cs (rowAt t 1 (n + cs.length + 1)) =
      (List.range cs.length).map (fun i => cell (t + i) 1)
  | [], t, n, _ => rfl
  | c :: cs, t, n, h => by
    have h0 : cell t 0 = c := by simpa using h 0 (by simp)
    have hs : stepRow c (rowAt t 1 ((n + cs.length + 1) + 1)) =
        rowAt (t + 1) 1 (n + cs.length + 1) := by
      have := stepRow_rowAt t (n + cs.length + 1) 1
      rw [show (1 : Int) - 1 = 0 by rfl, h0] at this
      exact this
    have ih := col1_rowAt cs (t + 1) n (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show t + 1 + i = t + (i + 1) by omega]
      simpa using this)
    show (rowAt t 1 (n + (cs.length + 1) + 1)).headD false ::
        col1 cs (stepRow c (rowAt t 1 (n + (cs.length + 1) + 1)))
      = (List.range (cs.length + 1)).map (fun i => cell (t + i) 1)
    rw [show n + (cs.length + 1) + 1 = (n + cs.length + 1) + 1 by omega, hs, ih,
      List.range_succ_eq_map]
    simp only [rowAt, List.headD_cons, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [show t + 1 + i = t + (i + 1) by omega]
'''
out.append(col1)
blk = L(sp, 75, 133)
blk = blk.replace('(win t 1 (k + 2))', '(rowAt t 1 (k + 2))')
blk = blk.replace('col1_win (alt k) t 1 (alt_spec t k h)', 'col1_rowAt (alt k) t 1 (alt_spec t k h)')
blk = blk.replace('win t 1 (4 + 2)', 'rowAt t 1 (4 + 2)').replace('win t 1 (8 + 2)', 'rowAt t 1 (8 + 2)')
blk = blk.replace('rwa [win_length] at this', 'rwa [length_rowAt] at this')
out.append(blk)
out.append('')
out.append(L(sp, 145, 171))
out.append('')
out.append('/-! ### The skeleton forced by an alternating center -/')
out.append('')
# Rule30Period2 section: from 'section' to 'end' (before normalize)
a = next(k for k, l in enumerate(p2) if l.startswith('section'))
b = next(k for k, l in enumerate(p2) if l.strip() == 'end' and k > a)
sec = '\n'.join(p2[a:b + 1])
# replace m4_odd by a corollary of col4_white_of_alt
m4a = sec.index('/-- Column `-4` is white at every odd offset. -/')
m4b = sec.index('\nend', m4a)
m4new = r'''/-- Column `-4` is white at every odd offset (a case of `col4_white_of_alt`). -/
theorem m4_odd (k : Nat) : cell (T + 2 * k + 1) (-4) = false := by
  refine col4_white_of_alt (T + 2 * k + 1) (h k).2 ?_ ?_ ?_ ?_
  · have := (h (k + 1)).1
    rwa [show T + 2 * (k + 1) = T + 2 * k + 1 + 1 by omega] at this
  · have := (h (k + 1)).2
    rwa [show T + 2 * (k + 1) + 1 = T + 2 * k + 1 + 2 by omega] at this
  · have := (h (k + 2)).1
    rwa [show T + 2 * (k + 2) = T + 2 * k + 1 + 3 by omega] at this
  · have := (h (k + 2)).2
    rwa [show T + 2 * (k + 2) + 1 = T + 2 * k + 1 + 4 by omega] at this
'''
sec = sec[:m4a] + m4new + sec[m4b:]
out.append(sec)
out.append('')
red = r'''/-! ### Reduction to the zero-driven left half -/

/-- Under an alternating center the effective boundary `c t && c (t + 1)` is white. -/
theorem effective_white {T : Nat}
    (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false)
    (k : Nat) : (center (T + k) && center (T + k + 1)) = false := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
  · show (cell (T + 2 * j) 0 && cell (T + 2 * j + 1) 0) = false
    rw [(h j).2]; cases cell (T + 2 * j) 0 <;> rfl
  · show (cell (T + (2 * j + 1)) 0 && cell (T + (2 * j + 1) + 1) 0) = false
    rw [show T + (2 * j + 1) = T + 2 * j + 1 by omega, (h j).2]; rfl

/-- **The left half is the zero-driven left half.** Under an alternating center from `T`, the
columns `p < 0` evolve from the row at time `T` as rule 30 on `p < 0` with column `0` held
white. -/
theorem left_half_zero_driven {T : Nat}
    (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false) :
    ∀ k : Nat, ∀ p : Int, p < 0 → L (fun _ => false) (fun p => cell T p) k p = cell (T + k) p := by
  have hfun : (fun k => center (T + k) && center (T + k + 1)) = fun _ => false :=
    funext (effective_white h)
  intro k p hp
  have := cell_eq_L_effective T k p hp
  rwa [hfun] at this

/-- **`Q₀₁`.** No start of the zero-driven left half with a leftmost black cell (at `-m`,
`m ≥ 1`, white beyond) keeps column `-1` black at every even step. Open. -/
def Q01 : Prop :=
  ∀ (m : Nat) (s : Int → Bool), 0 < m → (∀ p : Int, p < -(m : Int) → s p = false) →
    s (-(m : Int)) = true → ¬ ∀ k, L (fun _ => false) s (2 * k) (-1) = true

/-- **`Q₀₁` excludes period `2`.** If `Q01` holds, the center column is not eventually
2-periodic, whatever the transient. -/
theorem not_eventually_period_two_of_Q01 (hQ : Q01) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t := by
  rintro ⟨T0, hp⟩
  obtain ⟨T, hT⟩ := normalize hp
  -- one period later the start time is at least `1`, so the start has a leftmost black cell
  have h' : ∀ k, cell (T + 2 + 2 * k) 0 = true ∧ cell (T + 2 + 2 * k + 1) 0 = false := by
    intro k
    have := hT (k + 1)
    rw [show T + 2 * (k + 1) = T + 2 + 2 * k by omega] at this
    exact this
  refine hQ (T + 2) (fun p => cell (T + 2) p) (by omega)
    (fun p hp => cell_eq_false_of_lt (T + 2) p hp) (cell_left_edge (T + 2)) (fun k => ?_)
  rw [left_half_zero_driven h' (2 * k) (-1) (by omega)]
  exact m1_even h' k

/-- The stripe: black exactly at the odd positions. -/
def stripe (p : Int) : Bool := decide (p % 2 = 1)

/-- The stripe is a fixed point of the zero-driven left half. -/
theorem stripe_fixed : ∀ t : Nat, ∀ p : Int, p < 0 → L (fun _ => false) stripe t p = stripe p := by
  intro t
  induction t with
  | zero => intro p hp; exact L_zero hp
  | succ t ih =>
    intro p hp
    rw [L_succ hp, ih (p - 1) (by omega), ih p hp]
    by_cases hq : p + 1 < 0
    · rw [ih (p + 1) hq]
      simp only [stripe, rule]
      have : p % 2 = 0 ∨ p % 2 = 1 := by omega
      rcases this with h | h
      · have h1 : (p - 1) % 2 = 1 := by omega
        have h2 : (p + 1) % 2 = 1 := by omega
        simp [h, h1, h2]
      · have h1 : (p - 1) % 2 = 0 := by omega
        have h2 : (p + 1) % 2 = 0 := by omega
        simp [h, h1, h2]
    · have hp1 : p = -1 := by omega
      subst hp1
      rw [show (-1 : Int) + 1 = 0 by rfl, L_col0]
      decide

/-- **Finiteness is essential in `Q01`**: from the (infinite) stripe, column `-1` of the
zero-driven left half is black at every step. -/
theorem stripe_col (t : Nat) : L (fun _ => false) stripe t (-1) = true := by
  rw [stripe_fixed t (-1) (by omega)]; decide
'''
out.append(red)
out.append('end Rule30PeriodTwo')
out.append('end Ruliology.CellularAutomata')
open(R + 'staging/Ruliology/CellularAutomata/Rule30PeriodTwo.lean', 'w').write('\n'.join(out) + '\n')
print('written')
