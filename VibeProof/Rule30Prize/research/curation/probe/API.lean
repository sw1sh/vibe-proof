import Ruliology.CellularAutomata.Rule30Diagonals
open Ruliology.CellularAutomata Rule30Jen
#check @Nat.lt_of_mul_lt_mul_left
#check @Nat.mul_le_mul_left
#check @Nat.mul_succ
theorem cell_right_edge (t : Nat) : cell t (t : Int) = true :=
  (Rule30Diagonals.cell_congr (by omega)).trans (Rule30Diagonals.R_zero t)
example (a b k : Nat) (h1 : (k + 1) * a = 10) (h2 : (k + 1) * b = 12) (h3 : (k+1) * a + (k + 1) ≤ (k+1) * b) (hk : 9 ≤ k) : False := by omega
