import KC.Q01W56.C0
import KC.Q01W56.C1
import KC.Q01W56.C2
import KC.Q01W56.C3
import KC.Q01W56.C4
import KC.Q01W56.C5
import KC.Q01W56.C6
import KC.Q01W56.C7
import KC.Q01W56.C8
import KC.Q01W56.C9
import KC.Q01W56.C10
import KC.Q01W56.C11
import KC.Q01W56.C12
import KC.Q01W56.C13
import KC.Q01W56.C14
import KC.Q01W56.C15
import KC.Q01W56.C16
import KC.Q01W56.C17
import KC.Q01W56.C18
import KC.Q01W56.C19
import KC.Q01W56.C20
import KC.Q01W56.C21
import KC.Q01W56.C22
import KC.Q01W56.C23
import KC.Q01W56.C24
import KC.Q01W56.C25
import KC.Q01W56.C26
import KC.Q01W56.C27
import KC.Q01W56.C28
import KC.Q01W56.C29
import KC.Q01W56.C30
import KC.Q01W56.C31
import KC.Q01W56.C32
import KC.Q01W56.C33
import KC.Q01W56.C34
import KC.Q01W56.C35
import KC.Q01W56.C36
import KC.Q01W56.C37
import KC.Q01W56.C38
import KC.Q01W56.C39
import KC.Q01W56.C40
import KC.Q01W56.C41
import KC.Q01W56.C42
import KC.Q01W56.C43
import KC.Q01W56.C44
import KC.Q01W56.C45
import KC.Q01W56.C46
import KC.Q01W56.C47
import KC.Q01W56.C48
import KC.Q01W56.C49
import KC.Q01W56.C50
import KC.Q01W56.C51
import KC.Q01W56.C52
import KC.Q01W56.C53
import KC.Q01W56.C54
import KC.Q01W56.C55
import KC.Q01W56.C56
import KC.Q01W56.C57
import KC.Q01W56.C58
import KC.Q01W56.C59
import KC.Q01W56.C60
import KC.Q01W56.C61
import KC.Q01W56.C62
import KC.Q01W56.C63

/-!
# `Q01` for every start of width at most `56` (kernel-checked)

Every start of the zero-boundary left half supported at depths `1, …, 56` has a white cell at
depth `1` (column `-1`) at some even time `≤ 100`. The 1024 chunk checks are in
`KC.Q01W56.C0` – `KC.Q01W56.C63`; soundness is `KC.Q01Lanes.q01_of_chunks`.
-/

namespace KC.Q01W56
open KC.Q01Lanes Ruliology.CellularAutomata Rule30ZeroBoundary

theorem all_chunks : ChunksOK 56 101 18 0 1024 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C0.range C1.range) (chunksOK_append C2.range C3.range)) (chunksOK_append (chunksOK_append C4.range C5.range) (chunksOK_append C6.range C7.range))) (chunksOK_append (chunksOK_append (chunksOK_append C8.range C9.range) (chunksOK_append C10.range C11.range)) (chunksOK_append (chunksOK_append C12.range C13.range) (chunksOK_append C14.range C15.range)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C16.range C17.range) (chunksOK_append C18.range C19.range)) (chunksOK_append (chunksOK_append C20.range C21.range) (chunksOK_append C22.range C23.range))) (chunksOK_append (chunksOK_append (chunksOK_append C24.range C25.range) (chunksOK_append C26.range C27.range)) (chunksOK_append (chunksOK_append C28.range C29.range) (chunksOK_append C30.range C31.range))))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C32.range C33.range) (chunksOK_append C34.range C35.range)) (chunksOK_append (chunksOK_append C36.range C37.range) (chunksOK_append C38.range C39.range))) (chunksOK_append (chunksOK_append (chunksOK_append C40.range C41.range) (chunksOK_append C42.range C43.range)) (chunksOK_append (chunksOK_append C44.range C45.range) (chunksOK_append C46.range C47.range)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append C48.range C49.range) (chunksOK_append C50.range C51.range)) (chunksOK_append (chunksOK_append C52.range C53.range) (chunksOK_append C54.range C55.range))) (chunksOK_append (chunksOK_append (chunksOK_append C56.range C57.range) (chunksOK_append C58.range C59.range)) (chunksOK_append (chunksOK_append C60.range C61.range) (chunksOK_append C62.range C63.range))))))

/-- **`Q01` for widths `≤ 56`**: every start supported at depths `≤ 56` has a white cell at
depth `1` at some even time `≤ 100`. -/
theorem q01_width_le_56 (x : Nat → Bool) (hx : ∀ k, 56 < k → x k = false) :
    ∃ t, t ≤ 100 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_of_chunks 56 101 18 (by decide) all_chunks x hx
  exact ⟨t, by omega, he, hz⟩

/-- The same with the bound `2 W + 8`. -/
theorem q01_width_le_56_linear (x : Nat → Bool) (hx : ∀ k, 56 < k → x k = false) :
    ∃ t, t ≤ 2 * 56 + 8 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  obtain ⟨t, ht, he, hz⟩ := q01_width_le_56 x hx
  exact ⟨t, by omega, he, hz⟩

/-- **`Q01` restricted to widths `≤ 56`**: no start supported at depths `≤ 56` is constrained. -/
theorem not_inX_of_width_le_56 (x : Nat → Bool) (hx : ∀ k, 56 < k → x k = false) : ¬ InX x := by
  intro hX
  obtain ⟨t, _, he, hz⟩ := q01_width_le_56 x hx
  have := hX (t / 2)
  rw [show 2 * (t / 2) = t by omega, hz] at this
  exact absurd this (by decide)

end KC.Q01W56
