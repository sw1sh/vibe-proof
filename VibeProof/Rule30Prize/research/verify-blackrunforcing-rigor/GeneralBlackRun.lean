import Ruliology.CellularAutomata.Rule30Prize

/-! Independent re-check: the black-run lemma for EVERY rule-30 spacetime `x` (arbitrary initial
condition), plus the single-cell instance as a corollary, plus a sharpness count for 8 steps. -/

namespace VerifyBlackRunForcing
open Ruliology.CellularAutomata.Rule30Jen

/-- One rule-30 pass with column 0 fixed at `c0`: input row = cells 1..n, output = cells 1..n-2... -/
def pass : List Bool → List Bool
  | a :: b :: c :: rest => rule a b c :: pass (b :: c :: rest)
  | _ => []

def drive (c0 : Bool) : Nat → List Bool → List Bool
  | 0, row => row
  | k + 1, row => drive c0 k (pass (c0 :: row))

theorem check9 : ∀ b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
    drive true 9 [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] = [false, true] := by
  decide

/-- Cells `s+0, s+1, …, s+(n-1)` of row `t` of `x`. -/
def window (x : Nat → Int → Bool) (t : Nat) (s : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => x t s :: window x t (s + 1) n

/-- `x` is a rule-30 spacetime diagram (any initial row). -/
def IsR30 (x : Nat → Int → Bool) : Prop := ∀ t p, x (t + 1) p = rule (x t (p - 1)) (x t p) (x t (p + 1))

theorem pass_window (x : Nat → Int → Bool) (hx : IsR30 x) (t : Nat) :
    ∀ (m : Nat) (s : Int), pass (window x t s (m + 2)) = window x (t + 1) (s + 1) m
  | 0, s => rfl
  | m + 1, s => by
    show rule (x t s) (x t (s + 1)) (x t (s + 1 + 1)) :: pass (window x t (s + 1) (m + 2)) =
      x (t + 1) (s + 1) :: window x (t + 1) (s + 1 + 1) m
    rw [pass_window x hx t m (s + 1), hx t (s + 1), show s + 1 - 1 = s by omega]

theorem drive_window (x : Nat → Int → Bool) (hx : IsR30 x) :
    ∀ (k n t : Nat), (∀ j, j < k → x (t + j) 0 = true) →
      drive true k (window x t 1 (n + k)) = window x (t + k) 1 n
  | 0, n, t, _ => rfl
  | k + 1, n, t, h => by
    have h0 : x t 0 = true := by simpa using h 0 (by omega)
    have e1 : true :: window x t 1 (n + k + 1) = window x t 0 (n + k + 2) := by
      show true :: window x t 1 (n + k + 1) = x t 0 :: window x t (0 + 1) (n + k + 1)
      rw [h0]; rfl
    show drive true k (pass (true :: window x t 1 (n + k + 1))) = _
    rw [e1, pass_window x hx t (n + k) 0, show (0 : Int) + 1 = 1 by rfl,
      drive_window x hx k n (t + 1)
        (fun j hj => by rw [show t + 1 + j = t + (j + 1) by omega]; exact h (j + 1) (by omega)),
      show t + 1 + k = t + (k + 1) by omega]

/-- Black-run lemma for every rule-30 spacetime. -/
theorem black_run_general (x : Nat → Int → Bool) (hx : IsR30 x) (t : Nat)
    (h : ∀ j, j < 9 → x (t + j) 0 = true) : x (t + 9) 1 = false ∧ x (t + 9) 2 = true := by
  have e := drive_window x hx 9 2 t h
  have hrow : window x t 1 (2 + 9) = [x t 1, x t 2, x t 3, x t 4, x t 5, x t 6, x t 7, x t 8, x t 9,
      x t 10, x t 11] := rfl
  rw [hrow, check9] at e
  have hrow2 : window x (t + 9) 1 2 = [x (t + 9) 1, x (t + 9) 2] := rfl
  rw [hrow2] at e
  simp only [List.cons.injEq] at e
  exact ⟨e.1.symm, e.2.1.symm⟩

theorem cell_isR30 : IsR30 cell := fun _ _ => rfl

/-- The single-black-cell instance (the claim as stated for the prize pattern). -/
theorem black_run_cell (t : Nat) (h : ∀ j, j < 9 → cell (t + j) 0 = true) :
    cell (t + 9) 1 = false ∧ cell (t + 9) 2 = true :=
  black_run_general cell cell_isR30 t h

/-- Bits of `n` as an 11-cell row (cell 1 = bit 0). -/
def bitsRow (n : Nat) : List Bool := (List.range 11).map (fun i => n.testBit i)

/-- Sharpness count: rows (cells 1..11) where cell 1 is black after 8 black center steps. -/
def count8 : Nat := ((List.range 2048).filter (fun n => (drive true 8 (bitsRow n)).head? == some true)).length

end VerifyBlackRunForcing

#print axioms VerifyBlackRunForcing.check9
#print axioms VerifyBlackRunForcing.black_run_general
#print axioms VerifyBlackRunForcing.black_run_cell
#eval VerifyBlackRunForcing.count8
