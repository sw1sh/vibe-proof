import KC.Q01W20.C0
import KC.Q01W20.C1

/-!
# `Q01` for every start of width at most `20` (kernel-checked)

Every start of the zero-boundary left half supported at depths `1, …, 20` has a white cell at
depth `1` (column `-1`) at some even time `≤ 38`. The 4 chunk checks are in
`KC.Q01W20.C0` – `KC.Q01W20.C1`; soundness is `KC.Q01Lanes.q01_of_chunks`.
-/

namespace KC.Q01W20
open KC.Q01Lanes Ruliology.CellularAutomata Rule30ZeroBoundary

theorem all_chunks : ChunksOK 20 39 8 0 4 :=
  (chunksOK_append C0.range C1.range)

/-- **`Q01` for widths `≤ 20`**: every start supported at depths `≤ 20` has a white cell at
depth `1` at some even time `≤ 38`. -/
theorem q01_width_le_20 (x : Nat → Bool) (hx : ∀ k, 20 < k → x k = false) :
    ∃ t, t ≤ 38 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_of_chunks 20 39 8 (by decide) all_chunks x hx
  exact ⟨t, by omega, he, hz⟩

/-- The same with the bound `2 W + 8`. -/
theorem q01_width_le_20_linear (x : Nat → Bool) (hx : ∀ k, 20 < k → x k = false) :
    ∃ t, t ≤ 2 * 20 + 8 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_width_le_20 x hx
  exact ⟨t, by omega, he, hz⟩

/-- **`Q01` restricted to widths `≤ 20`**: no start supported at depths `≤ 20` is constrained. -/
theorem not_inX_of_width_le_20 (x : Nat → Bool) (hx : ∀ k, 20 < k → x k = false) : ¬ InX x := by
  intro hX
  obtain ⟨t, _, he, hz⟩ := q01_width_le_20 x hx
  have := hX (t / 2)
  rw [show 2 * (t / 2) = t by omega, hz] at this
  exact absurd this (by decide)

end KC.Q01W20
