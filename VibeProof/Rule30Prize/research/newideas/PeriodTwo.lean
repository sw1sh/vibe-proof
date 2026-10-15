import Ruliology.CellularAutomata.Rule30Jen

/-!
# Rigid consequences of an eventually alternating center column

Hypothesis `Alt T`: from time `T` on the center column alternates `0, 1, 0, 1, ...`
(`cell (T + 2k) 0 = false`, `cell (T + 2k + 1) 0 = true`). (The other phase is `Alt (T + 1)`.)

Consequences proved here, for every `k`:
* `alt_left_one`  : column -1 is black at the odd offsets: `cell (T+2k+1) (-1) = true`;
* `alt_right_even`: column 1 at the even offsets is the complement of column -1;
* `alt_golden`    : column -1 at even offsets has no two consecutive zeros
                    (`cell (T+2k) (-1) = false → cell (T+2k+2) (-1) = true`) — golden-mean shift;
* `alt_col3_even`, `alt_col3_odd`: column -3 is "doubled": both equal `cell (T+2k+2) (-1)`;
* `alt_col4_even` : column -4 is white at every even offset: `cell (T+2k) (-4) = false`.

None of this yields a contradiction by itself (finite-strip relaxations admit aperiodic solutions), but it
records the rigid local structure any proof for period 2 must live with.
-/

namespace R30NewIdeas
open Ruliology.CellularAutomata.Rule30Jen

theorem step_eq (t : Nat) (p : Int) : cell (t + 1) p = xor (cell t (p - 1)) (cell t p || cell t (p + 1)) := rfl

theorem cell_congr' {t : Nat} {p q : Int} (h : p = q) : cell t p = cell t q := h ▸ rfl

/-- Left reconstruction at the named columns. -/
theorem rec_m1 (t : Nat) : cell t (-1) = xor (cell (t + 1) 0) (cell t 0 || cell t 1) := by
  have := cell_left t 0; simpa using this
theorem rec_m2 (t : Nat) : cell t (-2) = xor (cell (t + 1) (-1)) (cell t (-1) || cell t 0) := by
  have := cell_left t (-1)
  rw [cell_congr' (show (-1 : Int) - 1 = -2 by rfl), cell_congr' (show (-1 : Int) + 1 = 0 by rfl)] at this
  exact this
theorem rec_m3 (t : Nat) : cell t (-3) = xor (cell (t + 1) (-2)) (cell t (-2) || cell t (-1)) := by
  have := cell_left t (-2)
  rw [cell_congr' (show (-2 : Int) - 1 = -3 by rfl), cell_congr' (show (-2 : Int) + 1 = -1 by rfl)] at this
  exact this
theorem rec_m4 (t : Nat) : cell t (-4) = xor (cell (t + 1) (-3)) (cell t (-3) || cell t (-2)) := by
  have := cell_left t (-3)
  rw [cell_congr' (show (-3 : Int) - 1 = -4 by rfl), cell_congr' (show (-3 : Int) + 1 = -2 by rfl)] at this
  exact this
theorem step_c1 (t : Nat) : cell (t + 1) 1 = xor (cell t 0) (cell t 1 || cell t 2) := by
  rw [step_eq]; rfl

/-- The center column alternates from `T`: white at even offsets, black at odd offsets. -/
def Alt (T : Nat) : Prop := ∀ k : Nat, cell (T + 2 * k) 0 = false ∧ cell (T + 2 * k + 1) 0 = true

section
variable {T : Nat} (h : Alt T)
include h

theorem alt_left_one (k : Nat) : cell (T + 2 * k + 1) (-1) = true := by
  rw [rec_m1, (h k).2, show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, (h (k + 1)).1]; rfl

theorem alt_right_even (k : Nat) : cell (T + 2 * k) 1 = !cell (T + 2 * k) (-1) := by
  rw [rec_m1, (h k).1, show T + 2 * k + 1 = T + 2 * k + 1 from rfl, (h k).2]
  cases cell (T + 2 * k) 1 <;> rfl

theorem alt_golden (k : Nat) (hz : cell (T + 2 * k) (-1) = false) : cell (T + 2 * k + 2) (-1) = true := by
  have h1 : cell (T + 2 * k) 1 = true := by rw [alt_right_even h k, hz]; rfl
  have h2 : cell (T + 2 * k + 1) 1 = true := by rw [step_c1, (h k).1, h1]; rfl
  have h3 : cell (T + 2 * (k + 1)) 1 = false := by
    rw [show T + 2 * (k + 1) = (T + 2 * k + 1) + 1 by omega, step_c1, (h k).2, h2]; rfl
  rw [show T + 2 * k + 2 = T + 2 * (k + 1) by omega, rec_m1, (h (k + 1)).1, h3, (h (k + 1)).2]; rfl

theorem alt_col2_even (k : Nat) : cell (T + 2 * k) (-2) = !cell (T + 2 * k) (-1) := by
  rw [rec_m2, alt_left_one h k, (h k).1]; cases cell (T + 2 * k) (-1) <;> rfl

theorem alt_col2_odd (k : Nat) : cell (T + 2 * k + 1) (-2) = !cell (T + 2 * k + 2) (-1) := by
  rw [rec_m2, alt_left_one h k, show T + 2 * k + 1 + 1 = T + 2 * k + 2 by omega]
  cases cell (T + 2 * k + 2) (-1) <;> rfl

theorem alt_col3_even (k : Nat) : cell (T + 2 * k) (-3) = cell (T + 2 * k + 2) (-1) := by
  rw [rec_m3, alt_col2_odd h k, alt_col2_even h k]
  cases cell (T + 2 * k + 2) (-1) <;> cases cell (T + 2 * k) (-1) <;> rfl

theorem alt_col3_odd (k : Nat) : cell (T + 2 * k + 1) (-3) = cell (T + 2 * k + 2) (-1) := by
  rw [rec_m3, show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, alt_col2_even h (k + 1),
    alt_col2_odd h k, alt_left_one h k, show T + 2 * (k + 1) = T + 2 * k + 2 by omega]
  cases cell (T + 2 * k + 2) (-1) <;> rfl

theorem alt_col4_even (k : Nat) : cell (T + 2 * k) (-4) = false := by
  rw [rec_m4, alt_col3_odd h k, alt_col3_even h k, alt_col2_even h k]
  cases ha : cell (T + 2 * k + 2) (-1) with
  | true => cases cell (T + 2 * k) (-1) <;> rfl
  | false =>
    cases hb : cell (T + 2 * k) (-1) with
    | false => exact absurd (alt_golden h k hb) (by rw [ha]; decide)
    | true => rfl

end

end R30NewIdeas
