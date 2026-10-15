import D4_00
import D4_01
import D4_02
import D4_03
import D4_04
import D4_05
import D4_06
import D4_07
import D4_08
import D4_09
import D4_10
import D4_11
import D4_12
import D4_13
import D4_14
open Ruliology.CellularAutomata.Rule30Jen
open AbsorbRight

/-- All blocks of length 1..7 that start and end white. -/
def shortBlocks : List (List Bool) :=
  ((List.range 8).flatMap allLists).filter fun u => u.head? == some false && u.getLast? == some false

theorem shortBlocks_eq : shortBlocks =
  [[false],
   [false, false],
   [false, false, false],
   [false, true, false],
   [false, false, false, false],
   [false, false, true, false],
   [false, true, false, false],
   [false, true, true, false],
   [false, false, false, false, false],
   [false, false, false, true, false],
   [false, false, true, false, false],
   [false, false, true, true, false],
   [false, true, false, false, false],
   [false, true, false, true, false],
   [false, true, true, false, false],
   [false, true, true, true, false],
   [false, false, false, false, false, false],
   [false, false, false, false, true, false],
   [false, false, false, true, false, false],
   [false, false, false, true, true, false],
   [false, false, true, false, false, false],
   [false, false, true, false, true, false],
   [false, false, true, true, false, false],
   [false, false, true, true, true, false],
   [false, true, false, false, false, false],
   [false, true, false, false, true, false],
   [false, true, false, true, false, false],
   [false, true, false, true, true, false],
   [false, true, true, false, false, false],
   [false, true, true, false, true, false],
   [false, true, true, true, false, false],
   [false, true, true, true, true, false],
   [false, false, false, false, false, false, false],
   [false, false, false, false, false, true, false],
   [false, false, false, false, true, false, false],
   [false, false, false, false, true, true, false],
   [false, false, false, true, false, false, false],
   [false, false, false, true, false, true, false],
   [false, false, false, true, true, false, false],
   [false, false, false, true, true, true, false],
   [false, false, true, false, false, false, false],
   [false, false, true, false, false, true, false],
   [false, false, true, false, true, false, false],
   [false, false, true, false, true, true, false],
   [false, false, true, true, false, false, false],
   [false, false, true, true, false, true, false],
   [false, false, true, true, true, false, false],
   [false, false, true, true, true, true, false],
   [false, true, false, false, false, false, false],
   [false, true, false, false, false, true, false],
   [false, true, false, false, true, false, false],
   [false, true, false, false, true, true, false],
   [false, true, false, true, false, false, false],
   [false, true, false, true, false, true, false],
   [false, true, false, true, true, false, false],
   [false, true, false, true, true, true, false],
   [false, true, true, false, false, false, false],
   [false, true, true, false, false, true, false],
   [false, true, true, false, true, false, false],
   [false, true, true, false, true, true, false],
   [false, true, true, true, false, false, false],
   [false, true, true, true, false, true, false],
   [false, true, true, true, true, false, false],
   [false, true, true, true, true, true, false]] := by decide +kernel

theorem det_all : ∀ u ∈ shortBlocks, Determined u 4 = true := by
  rw [shortBlocks_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, implies_true, and_true]
  exact ⟨D4_b0, D4_b00, D4_b000, D4_b010, D4_b0000, D4_b0010, D4_b0100, D4_b0110, D4_b00000, D4_b00010, D4_b00100, D4_b00110, D4_b01000, D4_b01010, D4_b01100, D4_b01110, D4_b000000, D4_b000010, D4_b000100, D4_b000110, D4_b001000, D4_b001010, D4_b001100, D4_b001110, D4_b010000, D4_b010010, D4_b010100, D4_b010110, D4_b011000, D4_b011010, D4_b011100, D4_b011110, D4_b0000000, D4_b0000010, D4_b0000100, D4_b0000110, D4_b0001000, D4_b0001010, D4_b0001100, D4_b0001110, D4_b0010000, D4_b0010010, D4_b0010100, D4_b0010110, D4_b0011000, D4_b0011010, D4_b0011100, D4_b0011110, D4_b0100000, D4_b0100010, D4_b0100100, D4_b0100110, D4_b0101000, D4_b0101010, D4_b0101100, D4_b0101110, D4_b0110000, D4_b0110010, D4_b0110100, D4_b0110110, D4_b0111000, D4_b0111010, D4_b0111100, D4_b0111110⟩


open Ruliology.CellularAutomata.Rule30Prize

/-- Every block of length 1..7 that starts and ends white is in the list. -/
theorem shortBlocks_complete (u : List Bool) (h1 : 1 ≤ u.length) (h7 : u.length ≤ 7)
    (hh : u.head? = some false) (hl : u.getLast? = some false) : u ∈ shortBlocks := by
  simp only [shortBlocks, List.mem_filter, List.mem_flatMap, List.mem_range]
  exact ⟨⟨u.length, by omega, mem_allLists u⟩, by simp [hh, hl]⟩

/-- Corollary of Theorem B′: a black run of length `r ≥ 36` followed by any block of length 1..7
that starts and ends white is never the repeating word of an eventually periodic center column. -/
theorem no_black_run_short_block (u : List Bool) (h1 : 1 ≤ u.length) (h7 : u.length ≤ 7)
    (hh : u.head? = some false) (hl : u.getLast? = some false)
    (T r t1 : Nat) (hr : 36 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + u.length)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hu : ∀ i, i < u.length → center (t1 + r + i) = u.getD i false) : False :=
  no_black_run_block u 4 (det_all u (shortBlocks_complete u h1 h7 hh hl)) (by omega)
    T r t1 hper ht1 (by omega) (by omega) hrun hu

#print axioms det_all
#print axioms no_black_run_short_block
