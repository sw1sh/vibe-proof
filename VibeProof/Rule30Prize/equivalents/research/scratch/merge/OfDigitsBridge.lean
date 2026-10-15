import Rule30Equivalents
import Mathlib.Analysis.Real.OfDigits

open Ruliology.CellularAutomata

namespace CatalogProofs

theorem ofDigits_eq (b : ℕ) [NeZero b] (hb : 2 ≤ b) :
    Real.ofDigits (b := b) (fun t => if Rule30Prize.center t then 1 else 0) =
      ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / (b : ℝ) ^ (t + 1) := by
  unfold Real.ofDigits Real.ofDigitsTerm
  congr 1
  funext t
  have h1 : 1 % b = 1 := Nat.one_mod_eq_one.mpr (by omega)
  cases hc : Rule30Prize.center t
  · simp [hc]
  · simp [hc, h1, div_eq_mul_inv]

/-- Problem 1 in Mathlib's `Real.ofDigits` vocabulary, every base `b ≥ 2`. -/
theorem problem1_iff_irrational_ofDigits (b : ℕ) [NeZero b] (hb : 2 ≤ b) :
    Rule30Prize.Problem1 ↔
      Irrational (Real.ofDigits (b := b) fun t => if Rule30Prize.center t then 1 else 0) := by
  rw [ofDigits_eq b hb]
  exact Rule30Equivalents.BinaryIrrational.problem1_iff_irrational_base hb

end CatalogProofs

#print axioms CatalogProofs.problem1_iff_irrational_ofDigits
