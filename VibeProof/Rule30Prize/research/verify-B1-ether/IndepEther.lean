import Ruliology.CellularAutomata.Rule30Jen

/-!
Independent re-verification of claim B1-ether.

The ether is encoded here by ROWS (phase φ = 0..3, positions 0..6), i.e. transposed relative to
EtherWall.lean's column table, and it is defined on ℤ × ℤ via `Int.emod`. The update is the library
`Rule30Jen.rule` (left xor (center || right)), with left = j - 1 and right = j + 1 as integers.
-/

namespace VerifyB1Ether
open Ruliology.CellularAutomata.Rule30Jen

/-- Rows of the ether at phases 0,1,2,3 (positions 0..6). -/
def rowTab : Nat → List Bool
  | 0 => [false, false, true,  false, false, false, false]
  | 1 => [false, true,  true,  true,  false, false, false]
  | 2 => [true,  true,  false, false, true,  false, false]
  | _ => [true,  false, true,  true,  true,  true,  true]

def Er (a b : Nat) : Bool := (rowTab b).getD a false

/-- The ether on ℤ × ℤ. -/
def E (j φ : Int) : Bool := Er (j % 7).toNat (φ % 4).toNat

theorem small : ∀ a, a < 7 → ∀ b, b < 4 →
    Er a ((b + 1) % 4) = rule (Er ((a + 6) % 7) b) (Er a b) (Er ((a + 1) % 7) b) := by decide

/-- The ether is a rule-30 space-time solution on all of ℤ × ℤ. -/
theorem E_orbit (j φ : Int) : E j (φ + 1) = rule (E (j - 1) φ) (E j φ) (E (j + 1) φ) := by
  unfold E
  have e1 : ((j - 1) % 7).toNat = ((j % 7).toNat + 6) % 7 := by omega
  have e2 : ((j + 1) % 7).toNat = ((j % 7).toNat + 1) % 7 := by omega
  have e3 : ((φ + 1) % 4).toNat = ((φ % 4).toNat + 1) % 4 := by omega
  rw [e1, e2, e3]
  exact small _ (by omega) _ (by omega)

/-- Spatial period 7 and temporal period 4 (sanity). -/
theorem E_per (j φ : Int) : E (j + 7) φ = E j φ ∧ E j (φ + 4) = E j φ := by
  unfold E; constructor <;> congr 2 <;> omega

/-- Columns read off the rows agree with the claimed column words
B1=0011, B2=0110, B3=1101, B4=0101, B5=0011, c=0001, c=0001. -/
def colWords : List (List Bool) :=
  [[false, false, true, true], [false, true, true, false], [true, true, false, true],
   [false, true, false, true], [false, false, true, true], [false, false, false, true],
   [false, false, false, true]]

theorem columns_match : ∀ a, a < 7 → ∀ b, b < 4 → Er a b = (colWords.getD a []).getD b false := by
  decide

/-! ### Alignments, with exhaustiveness over all columns and all shifts -/

def alignedR (w : List Bool) (j s : Nat) : Bool :=
  (List.range 4).all fun ψ => Er j ((ψ + s) % 4) == w.getD ψ false

def w0001 : List Bool := [false, false, false, true]
def w0011 : List Bool := [false, false, true, true]
def w0111 : List Bool := [false, true, true, true]
def w0101 : List Bool := [false, true, false, true]

theorem align_0001 : ∀ j, j < 7 → ∀ s, s < 4 →
    (alignedR w0001 j s = true ↔ (j = 5 ∧ s = 0) ∨ (j = 6 ∧ s = 0)) := by decide
theorem align_0011 : ∀ j, j < 7 → ∀ s, s < 4 →
    (alignedR w0011 j s = true ↔ (j = 0 ∧ s = 0) ∨ (j = 1 ∧ s = 3) ∨ (j = 4 ∧ s = 0)) := by decide
theorem align_0111 : ∀ j, j < 7 → ∀ s, s < 4 →
    (alignedR w0111 j s = true ↔ (j = 2 ∧ s = 2)) := by decide
theorem align_0101 : ∀ j, j < 7 → ∀ s, s < 4 →
    (alignedR w0101 j s = true ↔ (j = 3 ∧ s = 0) ∨ (j = 3 ∧ s = 2)) := by decide

/-- Integer-time form of an alignment: `E j0 (ψ + s) = w[ψ mod 4]` for every integer `ψ`. -/
theorem aligned_int {w : List Bool} {j0 s : Nat} (hj : j0 < 7) (h : alignedR w j0 s = true)
    (ψ : Int) : E j0 (ψ + s) = w.getD (ψ % 4).toNat false := by
  have h1 := List.all_eq_true.1 h (ψ % 4).toNat (List.mem_range.2 (by omega))
  have e : ((ψ + (s : Int)) % 4).toNat = ((ψ % 4).toNat + s) % 4 := by omega
  have ej : ((j0 : Int) % 7).toNat = j0 := by omega
  unfold E; rw [e, ej]; exact beq_iff_eq.1 h1

/-! ### The claim's table (copied verbatim from EtherWall.lean) is the same object -/

namespace Theirs
def etherTable : List (List Bool) :=
  [[false, false, true, true],
   [false, true, true, false],
   [true, true, false, true],
   [false, true, false, true],
   [false, false, true, true],
   [false, false, false, true],
   [false, false, false, true]]
def ether (j φ : Nat) : Bool := (etherTable.getD (j % 7) []).getD (φ % 4) false
end Theirs

theorem small_eq : ∀ a, a < 7 → ∀ b, b < 4 → Theirs.ether a b = Er a b := by decide

theorem theirs_eq (j φ : Nat) : Theirs.ether j φ = E j φ := by
  have h := small_eq (j % 7) (Nat.mod_lt _ (by decide)) (φ % 4) (Nat.mod_lt _ (by decide))
  have e1 : Theirs.ether (j % 7) (φ % 4) = Theirs.ether j φ := by
    unfold Theirs.ether; rw [Nat.mod_mod, Nat.mod_mod]
  have e2 : ((j : Int) % 7).toNat = j % 7 := by omega
  have e3 : ((φ : Int) % 4).toNat = φ % 4 := by omega
  unfold E; rw [e2, e3, ← h, e1]

/-! ### A genuine full-line orbit: the periodic configuration evolves into itself under rule 30 -/

/-- One rule-30 step of a bi-infinite configuration. -/
def step (x : Int → Bool) : Int → Bool := fun p => rule (x (p - 1)) (x p) (x (p + 1))

def iter (x : Int → Bool) : Nat → Int → Bool
  | 0 => x
  | n + 1 => step (iter x n)

/-- Starting from the ether row at any phase `φ0` (any integer spatial offset `d`), `n` rule-30
steps give the ether row at phase `φ0 + n`. -/
theorem iter_ether (d φ0 : Int) : ∀ n : Nat,
    iter (fun p => E (p + d) φ0) n = fun p => E (p + d) (φ0 + n)
  | 0 => by funext p; simp [iter]
  | n + 1 => by
    funext p
    show step (iter (fun p => E (p + d) φ0) n) p = _
    rw [iter_ether d φ0 n]
    show rule (E (p - 1 + d) (φ0 + n)) (E (p + d) (φ0 + n)) (E (p + 1 + d) (φ0 + n)) = _
    rw [show φ0 + ((n + 1 : Nat) : Int) = (φ0 + n) + 1 by omega, E_orbit (p + d) (φ0 + n),
      show p + d - 1 = p - 1 + d by omega, show p + d + 1 = p + 1 + d by omega]

end VerifyB1Ether

#print axioms VerifyB1Ether.E_orbit
#print axioms VerifyB1Ether.columns_match
#print axioms VerifyB1Ether.align_0001
#print axioms VerifyB1Ether.align_0011
#print axioms VerifyB1Ether.align_0111
#print axioms VerifyB1Ether.align_0101
#print axioms VerifyB1Ether.aligned_int
#print axioms VerifyB1Ether.theirs_eq
#print axioms VerifyB1Ether.iter_ether
