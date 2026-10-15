import Ruliology.CellularAutomata.Rule30Jen

/-!
# Masked Jen: a column and its right neighbour *restricted to the zeros of the column*

Rule 30 is `cell (t+1) i = cell t (i-1) xor (cell t i || cell t (i+1))`. When `cell t i = true` the
right neighbour does not matter, so column `i - 1` is determined by column `i` together with column
`i + 1` sampled only at the times where column `i` is white:

    cell t (i-1) = cell (t+1) i xor (cell t i || cell t (i+1)).

Hence if column `i` is eventually periodic and column `i+1` is eventually periodic *on the zero set of
column `i`* (with a common period), then column `i - 1` is eventually periodic, and Jen's adjacent-column
theorem gives a contradiction.

For the center column this is the sharp form of "absorption": if the center column `c` were eventually
periodic, then column 1 restricted to `{t : c t = false}` could not be eventually periodic.
-/

namespace R30NewIdeas
open Ruliology.CellularAutomata.Rule30Jen

/-- **Masked Jen.** Column `i` and column `i+1` restricted to the zeros of column `i` are never jointly
eventually periodic. -/
theorem masked_jen (i : Int) {T Q : Nat} (hQ : 0 < Q)
    (h0 : ∀ t, T ≤ t → cell (t + Q) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell t i = false → cell (t + Q) (i + 1) = cell t (i + 1)) : False := by
  have hm : ∀ t, T ≤ t → cell (t + Q) (i - 1) = cell t (i - 1) := by
    intro t ht
    rw [cell_left (t + Q) i, cell_left t i, show t + Q + 1 = (t + 1) + Q by omega,
      h0 (t + 1) (by omega), h0 t ht]
    cases hc : cell t i with
    | false => rw [h1 t ht hc]
    | true => rfl
  have e : i - 1 + 1 = i := by omega
  refine not_adjacent (i - 1) ⟨T, Q, hQ, hm⟩ ?_
  rw [e]
  exact ⟨T, Q, hQ, h0⟩

/-- The masked pair `(c t, !c t && col₁ t)` of the center column is not eventually periodic.
Equivalently: if the center column is eventually periodic, column 1 restricted to the zeros of the
center column is not eventually periodic (for any common period). -/
theorem center_masked_not_eventually_periodic :
    ¬ ∃ T Q : Nat, 0 < Q ∧ ∀ t, T ≤ t →
      cell (t + Q) 0 = cell t 0 ∧ (cell t 0 = false → cell (t + Q) 1 = cell t 1) := by
  rintro ⟨T, Q, hQ, h⟩
  exact masked_jen 0 hQ (fun t ht => (h t ht).1) (fun t ht hc => by simpa using (h t ht).2 hc)

/-- At a black center cell the left neighbour is forced: `c t = true → cell t (-1) = !c (t+1)`. -/
theorem left_of_black_center (t : Nat) (h : cell t 0 = true) : cell t (-1) = !cell (t + 1) 0 := by
  have := cell_left t 0
  simp only [h, Bool.true_or] at this
  rw [show (0 : Int) - 1 = -1 by rfl] at this
  rw [this]; cases cell (t + 1) 0 <;> rfl

end R30NewIdeas
