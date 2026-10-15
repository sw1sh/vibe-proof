import Ruliology.CellularAutomata.Rule30Jen

/-!
# Rule 30: consistency at a column and a refinement of Jen's adjacent-column theorem

Scratch file (left-half / column-0 consistency angle).

* `left_forced_of_black`: where column `i` is black at time `t`, column `i - 1` at time `t` is
  forced: `cell t (i - 1) = !cell (t + 1) i`.
* `not_periodic_on_white`: if column `i` is periodic from `T` with period `P`, then column `i + 1`
  is *not* `P`-periodic from `T` on the white times of column `i`.  (Otherwise column `i - 1`
  would be periodic too, contradicting `Rule30Jen.not_adjacent`.)
* `center_col1_not_periodic_on_white`: the case `i = 0`. If the center column is eventually
  periodic, then column `1`, restricted to the times where the center is white, is not eventually
  periodic with any period that is also a period of the center (from a common start).
-/

namespace Ruliology.CellularAutomata
namespace Rule30LeftConsistency

open Rule30Jen

/-- Where column `i` is black, column `i - 1` is forced by the next value of column `i`. -/
theorem left_forced_of_black (t : Nat) (i : Int) (h : cell t i = true) :
    cell t (i - 1) = !cell (t + 1) i := by
  rw [cell_left, h]
  cases cell (t + 1) i <;> rfl

/-- Where column `i` is white, column `i - 1` is `cell (t+1) i xor cell t (i+1)`. -/
theorem left_of_white (t : Nat) (i : Int) (h : cell t i = false) :
    cell t (i - 1) = xor (cell (t + 1) i) (cell t (i + 1)) := by
  rw [cell_left, h]
  rfl

/-- **Refined Jen.** If column `i` is periodic from `T` with period `P`, column `i + 1` is not
`P`-periodic from `T` on the white times of column `i`. -/
theorem not_periodic_on_white (i : Int) {T P : Nat} (hP : 0 < P)
    (h0 : ∀ t, T ≤ t → cell (t + P) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell t i = false → cell (t + P) (i + 1) = cell t (i + 1)) : False := by
  have hm1 : ∀ t, T ≤ t → cell (t + P) (i - 1) = cell t (i - 1) := by
    intro t ht
    rw [cell_left, cell_left t, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
      h0 t ht]
    cases hc : cell t i
    · rw [h1 t ht hc]
    · rfl
  refine not_adjacent (i - 1) ⟨T, P, hP, hm1⟩ ⟨T, P, hP, ?_⟩
  rw [show i - 1 + 1 = i by omega]
  exact h0

/-- The center-column case: an eventually periodic center column (from `T`, period `P`) forces
column `1`, on the white times of the center, to be non-periodic for that same `P` from every
start `T'`. -/
theorem center_col1_not_periodic_on_white {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (T' : Nat) :
    ¬ ∀ t, T' ≤ t → cell t 0 = false → cell (t + P) 1 = cell t 1 := by
  intro h1
  exact not_periodic_on_white 0 (T := max T T') hP (fun t ht => hc t (by omega))
    (fun t ht hw => h1 t (by omega) hw)

end Rule30LeftConsistency
end Ruliology.CellularAutomata

#print axioms Ruliology.CellularAutomata.Rule30LeftConsistency.not_periodic_on_white
#print axioms Ruliology.CellularAutomata.Rule30LeftConsistency.center_col1_not_periodic_on_white
#print axioms Ruliology.CellularAutomata.Rule30LeftConsistency.left_forced_of_black
