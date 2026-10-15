import KC.Q01W52.C0
import KC.Q01W52.C1
import KC.Q01W52.C2
import KC.Q01W52.C3
import KC.Q01W52.C4
import KC.Q01W52.C5
import KC.Q01W52.C6
import KC.Q01W52.C7
import KC.Q01W52.C8
import KC.Q01W52.C9
import KC.Q01W52.C10
import KC.Q01W52.C11
import KC.Q01W52.C12
import KC.Q01W52.C13
import KC.Q01W52.C14
import KC.Q01W52.C15

/-!
# `Q01` for every start of width at most `52` (kernel-checked)

Every start of the zero-boundary left half supported at depths `1, …, 52` has a white cell at
depth `1` (column `-1`) at some even time `≤ 96`. The 256 chunk checks are in
`KC.Q01W52.C0` – `KC.Q01W52.C15`; soundness is `KC.Q01Lanes.q01_of_chunks`.
-/

namespace KC.Q01W52
open KC.Q01Lanes Ruliology.CellularAutomata Rule30ZeroBoundary

theorem all_chunks : ChunksOK 52 97 18 0 256 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C0.range C1.range) (chunksOK_append C2.range C3.range)) (chunksOK_append (chunksOK_append C4.range C5.range) (chunksOK_append C6.range C7.range))) (chunksOK_append (chunksOK_append (chunksOK_append C8.range C9.range) (chunksOK_append C10.range C11.range)) (chunksOK_append (chunksOK_append C12.range C13.range) (chunksOK_append C14.range C15.range))))

/-- **`Q01` for widths `≤ 52`**: every start supported at depths `≤ 52` has a white cell at
depth `1` at some even time `≤ 96`. -/
theorem q01_width_le_52 (x : Nat → Bool) (hx : ∀ k, 52 < k → x k = false) :
    ∃ t, t ≤ 96 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_of_chunks 52 97 18 (by decide) all_chunks x hx
  exact ⟨t, by omega, he, hz⟩

/-- The same with the bound `2 W + 8`. -/
theorem q01_width_le_52_linear (x : Nat → Bool) (hx : ∀ k, 52 < k → x k = false) :
    ∃ t, t ≤ 2 * 52 + 8 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_width_le_52 x hx
  exact ⟨t, by omega, he, hz⟩

/-- **`Q01` restricted to widths `≤ 52`**: no start supported at depths `≤ 52` is constrained. -/
theorem not_inX_of_width_le_52 (x : Nat → Bool) (hx : ∀ k, 52 < k → x k = false) : ¬ InX x := by
  intro hX
  obtain ⟨t, _, he, hz⟩ := q01_width_le_52 x hx
  have := hX (t / 2)
  rw [show 2 * (t / 2) = t by omega, hz] at this
  exact absurd this (by decide)

end KC.Q01W52

-- verifier-appended checks
#print axioms KC.Q01W52.q01_width_le_52
#check @KC.Q01W52.q01_width_le_52
#print axioms KC.Q01W52.q01_width_le_52_linear
#check @KC.Q01W52.q01_width_le_52_linear
#print axioms KC.Q01W52.not_inX_of_width_le_52
#check @KC.Q01W52.not_inX_of_width_le_52
