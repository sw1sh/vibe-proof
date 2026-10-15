import Standalone

open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize
open AbsorbRight

/-- All blocks of length 1..7 that start and end white. -/
def shortBlocks : List (List Bool) :=
  ((List.range 8).flatMap allLists).filter fun u => u.head? == some false && u.getLast? == some false

theorem shortBlocks_count : shortBlocks.length = 64 := by decide +kernel

theorem shortBlocks_shape : ∀ u ∈ shortBlocks,
    1 ≤ u.length ∧ u.length ≤ 7 ∧ u.head? = some false ∧ u.getLast? = some false := by
  decide +kernel

/-- Every block of length ≤ 7 that starts and ends white is in the list. -/
theorem shortBlocks_complete (u : List Bool) (h1 : 1 ≤ u.length) (h7 : u.length ≤ 7)
    (hh : u.head? = some false) (hl : u.getLast? = some false) : u ∈ shortBlocks := by
  simp only [shortBlocks, List.mem_filter, List.mem_flatMap, List.mem_range]
  refine ⟨⟨u.length, by omega, mem_allLists u⟩, by simp [hh, hl]⟩

/-- The finite check with `j0 = 4` for all 64 blocks. -/
theorem det4_all : ∀ u ∈ shortBlocks, Determined u 4 = true := by decide +kernel

/-- Corollary: a black run of length `r ≥ 36` followed by any block of length 1..7 that starts and
ends white cannot be the repeating word of an eventually periodic center column. -/
theorem no_black_run_short_block (u : List Bool) (h1 : 1 ≤ u.length) (h7 : u.length ≤ 7)
    (hh : u.head? = some false) (hl : u.getLast? = some false)
    (T r t1 : Nat) (hr : 36 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + u.length)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hu : ∀ i, i < u.length → center (t1 + r + i) = u.getD i false) : False :=
  no_black_run_block u 4 (det4_all u (shortBlocks_complete u h1 h7 hh hl)) (by omega)
    T r t1 hper ht1 (by omega) (by omega) hrun hu

#print axioms det4_all
#print axioms no_black_run_short_block
