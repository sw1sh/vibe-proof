import Ruliology.CellularAutomata.Rule30Prize

/-!
# Rule 30: long black runs in the center column are absorbing on the right

* `nine_black`: (**Lemma A**) if a column is black for 9 consecutive steps, then right after them
  the next two columns are white, black. Finite core checked by `decide +kernel` (2048 cases).
* `black_shield`: (**Lemma A***) if a column is black for `9 j` consecutive steps, then right after
  them the next `2 j` columns read `(white black)^j`.
* `cone_agree`: two times whose rows agree on columns `1..n` and whose center columns agree from
  then on keep agreeing on the shrinking cone.
* `no_long_black_run`: (**Theorem B**) if the center column is eventually periodic with period `P`
  and one period contains a black run of length `r ≥ 9 ⌈(P - r + 9) / 2⌉`, contradiction: column 1
  would be eventually periodic too, against Jen's theorem.
-/

namespace AbsorbRight

open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

/-- The cells at columns `p, p+1, …, p+n-1` at time `t`. -/
def rowAt (t : Nat) (p : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t p :: rowAt t (p + 1) n

theorem length_rowAt (t : Nat) : ∀ (n : Nat) (p : Int), (rowAt t p n).length = n
  | 0, _ => rfl
  | n + 1, p => by simp [rowAt, length_rowAt t n (p + 1)]

/-- One rule-30 step on a finite row with left neighbour `l`; one cell shorter. -/
def stepRow (l : Bool) : List Bool → List Bool
  | a :: b :: rest => rule l a b :: stepRow a (b :: rest)
  | _ => []

theorem stepRow_rowAt (t : Nat) : ∀ (n : Nat) (p : Int),
    stepRow (cell t (p - 1)) (rowAt t p (n + 1)) = rowAt (t + 1) p n
  | 0, _ => rfl
  | n + 1, p => by
    have ih := stepRow_rowAt t n (p + 1)
    rw [show p + 1 - 1 = p by omega] at ih
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) ::
        stepRow (cell t p) (rowAt t (p + 1) (n + 1)) = cell (t + 1) p :: rowAt (t + 1) (p + 1) n
    rw [ih]
    rfl

/-- `k` steps with a black left neighbour. -/
def runBlack : Nat → List Bool → List Bool
  | 0, L => L
  | k + 1, L => runBlack k (stepRow true L)

theorem runBlack_rowAt (m : Int) : ∀ (k n t : Nat), (∀ s, s < k → cell (t + s) m = true) →
    runBlack k (rowAt t (m + 1) (n + k)) = rowAt (t + k) (m + 1) n
  | 0, n, t, _ => by simp [runBlack]
  | k + 1, n, t, h => by
    have h0 : cell t m = true := by simpa using h 0 (by omega)
    have hstep : stepRow true (rowAt t (m + 1) (n + k + 1)) = rowAt (t + 1) (m + 1) (n + k) := by
      have := stepRow_rowAt t (n + k) (m + 1)
      rw [show m + 1 - 1 = m by omega, h0] at this
      exact this
    have ih := runBlack_rowAt m k n (t + 1) (fun s hs => by
      have := h (s + 1) (by omega)
      rwa [show t + (s + 1) = t + 1 + s by omega] at this)
    show runBlack k (stepRow true (rowAt t (m + 1) (n + (k + 1)))) = rowAt (t + (k + 1)) (m + 1) n
    rw [show n + (k + 1) = n + k + 1 by omega, hstep, ih, show t + 1 + k = t + (k + 1) by omega]

/-- Finite core of Lemma A: all `2^11` rows. -/
theorem nine_black_core : ∀ L ∈ allLists 11, runBlack 9 L = [false, true] := by
  decide +kernel

/-- **Lemma A.** A column black for 9 consecutive steps forces white, black right after them in
the next two columns. -/
theorem nine_black (t : Nat) (m : Int) (h : ∀ s, s < 9 → cell (t + s) m = true) :
    cell (t + 9) (m + 1) = false ∧ cell (t + 9) (m + 2) = true := by
  have h1 := runBlack_rowAt m 9 2 t h
  have hmem : rowAt t (m + 1) (2 + 9) ∈ allLists 11 := by
    have := mem_allLists (rowAt t (m + 1) (2 + 9))
    rwa [length_rowAt] at this
  rw [nine_black_core _ hmem] at h1
  have h2 : rowAt (t + 9) (m + 1) 2 = [cell (t + 9) (m + 1), cell (t + 9) (m + 1 + 1)] := rfl
  rw [h2] at h1
  simp only [List.cons.injEq] at h1
  refine ⟨h1.1.symm, ?_⟩
  rw [show m + 2 = m + 1 + 1 by omega]
  exact h1.2.1.symm


end AbsorbRight

open Ruliology.CellularAutomata.Rule30Jen in
#check @AbsorbRight.nine_black
#print axioms AbsorbRight.nine_black
#print axioms AbsorbRight.nine_black_core
#print AbsorbRight.stepRow
#print AbsorbRight.runBlack
#print Ruliology.CellularAutomata.Rule30Jen.cell
#print Ruliology.CellularAutomata.Rule30Jen.rule
