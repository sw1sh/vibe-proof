import Ruliology.CellularAutomata.Rule30Jen

/-! Verbatim copy of `AbsorbRight.cone_agree`, against the project's real `cell`. -/

namespace ConeCopy
open Ruliology.CellularAutomata.Rule30Jen

-- Sanity: the unfolding used by `show` is definitional.
example (t : Nat) (p : Int) : cell (t + 1) p = rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) := rfl
example (p : Int) : cell 0 p = decide (p = 0) := rfl
example (a b c : Bool) : rule a b c = xor a (b || c) := rfl

theorem cone_agree (t0 t1 n : Nat) (hdrv : ∀ s, cell (t0 + s) 0 = cell (t1 + s) 0)
    (hrow : ∀ p : Int, 1 ≤ p → p ≤ n → cell t0 p = cell t1 p) :
    ∀ s : Nat, ∀ p : Int, 1 ≤ p → p + s ≤ n → cell (t0 + s) p = cell (t1 + s) p
  | 0, p, h1, h2 => by simpa using hrow p h1 (by omega)
  | s + 1, p, h1, h2 => by
    show rule (cell (t0 + s) (p - 1)) (cell (t0 + s) p) (cell (t0 + s) (p + 1)) =
      rule (cell (t1 + s) (p - 1)) (cell (t1 + s) p) (cell (t1 + s) (p + 1))
    have hl : cell (t0 + s) (p - 1) = cell (t1 + s) (p - 1) := by
      by_cases hp : p = 1
      · rw [show p - 1 = 0 by omega]; exact hdrv s
      · exact cone_agree t0 t1 n hdrv hrow s (p - 1) (by omega) (by omega)
    rw [hl, cone_agree t0 t1 n hdrv hrow s p h1 (by omega),
      cone_agree t0 t1 n hdrv hrow s (p + 1) (by omega) (by omega)]

#print axioms cone_agree

-- The hypothesis on column 0 is only needed for s < n - 1; a weaker form also suffices.
theorem cone_agree_weak (t0 t1 n : Nat) (hdrv : ∀ s, s + 1 < n → cell (t0 + s) 0 = cell (t1 + s) 0)
    (hrow : ∀ p : Int, 1 ≤ p → p ≤ n → cell t0 p = cell t1 p) :
    ∀ s : Nat, ∀ p : Int, 1 ≤ p → p + s ≤ n → cell (t0 + s) p = cell (t1 + s) p
  | 0, p, h1, h2 => by simpa using hrow p h1 (by omega)
  | s + 1, p, h1, h2 => by
    show rule (cell (t0 + s) (p - 1)) (cell (t0 + s) p) (cell (t0 + s) (p + 1)) =
      rule (cell (t1 + s) (p - 1)) (cell (t1 + s) p) (cell (t1 + s) (p + 1))
    have hl : cell (t0 + s) (p - 1) = cell (t1 + s) (p - 1) := by
      by_cases hp : p = 1
      · rw [show p - 1 = 0 by omega]; exact hdrv s (by omega)
      · exact cone_agree_weak t0 t1 n hdrv hrow s (p - 1) (by omega) (by omega)
    rw [hl, cone_agree_weak t0 t1 n hdrv hrow s p h1 (by omega),
      cone_agree_weak t0 t1 n hdrv hrow s (p + 1) (by omega) (by omega)]

#print axioms cone_agree_weak

end ConeCopy
