import Ruliology.CellularAutomata.Rule30Prize

/-!
# Rule 30: the words `0^r 1 1` (`r ≥ 10`) are absorbing on the right

If the center column is eventually periodic with repeating word `0^r 1 1`, `r ≥ 10`, then column 1
is eventually periodic, which contradicts Jen's theorem.

* `cell_eq_false_of_gt`, `cell_right_edge`: the right edge of the pattern.
* `nine_black`: Lemma A (copied from `AbsorbRight.lean`): nine consecutive black cells in a column
  force a white cell in the next column right after them.
* `front_moves`: during a white run of the center column, the leftmost black cell of the right half
  moves left by one column per step.
* `black_stays`: during a white run, a black cell in column 1 stays black.
* One period of `0^r 1 1`, by the position `ℓ` of the first black cell at its start:
  `ℓ ≤ r - 8` locks (`period_lock`); the other cases put the first black cell at column `≤ 3`
  at the start of the next period, except `ℓ = r + 2`, where column 1 reads `0^{r+1} 1`.
-/

namespace AbsorbWhite

open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

/-! ### Lemma A (same proof as in `AbsorbRight.lean`) -/

def rowAt (t : Nat) (p : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t p :: rowAt t (p + 1) n

theorem length_rowAt (t : Nat) : ∀ (n : Nat) (p : Int), (rowAt t p n).length = n
  | 0, _ => rfl
  | n + 1, p => by simp [rowAt, length_rowAt t n (p + 1)]

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

theorem nine_black_core : ∀ L ∈ allLists 11, runBlack 9 L = [false, true] := by
  decide +kernel

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

/-! ### The right edge -/

theorem cell_eq_false_of_gt : ∀ (t : Nat) (p : Int), (t : Int) < p → cell t p = false
  | 0, p, h => by simp [cell]; omega
  | t + 1, p, h => by
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) = false
    rw [cell_eq_false_of_gt t (p - 1) (by omega), cell_eq_false_of_gt t p (by omega),
      cell_eq_false_of_gt t (p + 1) (by omega)]
    rfl

theorem cell_right_edge : ∀ t : Nat, cell t (t : Int) = true
  | 0 => rfl
  | t + 1 => by
    show rule (cell t (((t + 1 : Nat) : Int) - 1)) (cell t ((t + 1 : Nat) : Int))
      (cell t (((t + 1 : Nat) : Int) + 1)) = true
    rw [show ((t + 1 : Nat) : Int) - 1 = (t : Int) by omega, cell_right_edge t,
      cell_eq_false_of_gt t _ (by omega), cell_eq_false_of_gt t _ (by omega)]
    rfl

/-- The first black cell to the right of the center exists at every time `t ≥ 1`. -/
theorem first_black_aux (t : Nat) : ∀ n : Nat, (∀ p : Nat, 1 ≤ p → p ≤ n → cell t p = false) ∨
    ∃ ℓ, ℓ < n ∧ (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell t p = false) ∧ cell t ((ℓ + 1 : Nat) : Int) = true
  | 0 => Or.inl (fun p h1 h2 => by omega)
  | n + 1 => by
    rcases first_black_aux t n with hw | ⟨ℓ, hℓ, hw, hb⟩
    · by_cases hc : cell t ((n + 1 : Nat) : Int) = true
      · exact Or.inr ⟨n, by omega, hw, hc⟩
      · refine Or.inl (fun p h1 h2 => ?_)
        by_cases hp : p ≤ n
        · exact hw p h1 hp
        · have : p = n + 1 := by omega
          subst this
          simpa using hc
    · exact Or.inr ⟨ℓ, by omega, hw, hb⟩

theorem first_black (t : Nat) (ht : 1 ≤ t) :
    ∃ ℓ, (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell t p = false) ∧ cell t ((ℓ + 1 : Nat) : Int) = true := by
  rcases first_black_aux t t with hw | ⟨ℓ, _, hw, hb⟩
  · have := hw t ht (Nat.le_refl t)
    rw [cell_right_edge] at this
    exact absurd this (by decide)
  · exact ⟨ℓ, hw, hb⟩

/-! ### White runs of the center column -/

/-- During a white run, the first black cell moves one column to the left per step. -/
theorem front_moves (a ℓ n : Nat) (hc : ∀ i, i < n → cell (a + i) 0 = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    ∀ i, i ≤ n → i ≤ ℓ →
      (∀ p : Nat, 1 ≤ p → p ≤ ℓ - i → cell (a + i) p = false) ∧
        cell (a + i) ((ℓ - i + 1 : Nat) : Int) = true
  | 0, _, _ => ⟨fun p h1 h2 => by simpa using hw p h1 (by omega), by simpa using hb⟩
  | i + 1, hin, hil => by
    obtain ⟨ihw, ihb⟩ := front_moves a ℓ n hc hw hb i (by omega) (by omega)
    -- white in columns 0..ℓ-i at time a+i (column 0: the center)
    have wh : ∀ q : Int, 0 ≤ q → q ≤ ((ℓ - i : Nat) : Int) → cell (a + i) q = false := by
      intro q hq0 hq1
      by_cases hq : q = 0
      · subst hq; exact hc i (by omega)
      · have := ihw q.toNat (by omega) (by omega)
        rwa [show ((q.toNat : Nat) : Int) = q by omega] at this
    refine ⟨fun p h1 h2 => ?_, ?_⟩
    · show rule (cell (a + i) ((p : Int) - 1)) (cell (a + i) (p : Int)) (cell (a + i) ((p : Int) + 1)) = false
      rw [wh _ (by omega) (by omega), wh _ (by omega) (by omega), wh _ (by omega) (by omega)]
      rfl
    · show rule (cell (a + i) (((ℓ - (i + 1) + 1 : Nat) : Int) - 1))
        (cell (a + i) ((ℓ - (i + 1) + 1 : Nat) : Int)) (cell (a + i) (((ℓ - (i + 1) + 1 : Nat) : Int) + 1)) = true
      rw [wh _ (by omega) (by omega), wh _ (by omega) (by omega),
        show ((ℓ - (i + 1) + 1 : Nat) : Int) + 1 = ((ℓ - i + 1 : Nat) : Int) by omega, ihb]
      rfl

/-- During a white run, a black cell in column 1 stays black. -/
theorem black_stays (a n : Nat) (hc : ∀ i, i < n → cell (a + i) 0 = false) (h1 : cell a 1 = true) :
    ∀ i, i ≤ n → cell (a + i) 1 = true
  | 0, _ => by simpa using h1
  | i + 1, hi => by
    have ih := black_stays a n hc h1 i (by omega)
    show rule (cell (a + i) (1 - 1)) (cell (a + i) 1) (cell (a + i) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, hc i (by omega), ih]
    rfl

/-! ### One period of `0^r 1 1` -/

section Period
variable (a r : Nat)
  (hwr : ∀ i, i < r → cell (a + i) 0 = false)
  (hb1 : cell (a + r) 0 = true) (hb2 : cell (a + r + 1) 0 = true)
include hwr hb1 hb2

/-- First black cell at column `ℓ + 1 ≤ r - 7`: next period starts with a black cell in column 1. -/
theorem period_lock (hr : 8 ≤ r) (ℓ : Nat) (hℓ : ℓ ≤ r - 8)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    (∀ i, ℓ ≤ i → i ≤ r → cell (a + i) 1 = true) ∧ cell (a + r + 1) 1 = false ∧
      cell (a + r + 2) 1 = true := by
  have hfront := (front_moves a ℓ r hwr hw hb ℓ (by omega) (Nat.le_refl ℓ)).2
  rw [show ℓ - ℓ + 1 = 1 by omega] at hfront
  have hblk : ∀ i, ℓ ≤ i → i ≤ r → cell (a + i) 1 = true := by
    intro i h1 h2
    have := black_stays (a + ℓ) (r - ℓ) (fun j hj => by
      have := hwr (ℓ + j) (by omega); rwa [show a + (ℓ + j) = a + ℓ + j by omega] at this)
      (by simpa using hfront) (i - ℓ) (by omega)
    rwa [show a + ℓ + (i - ℓ) = a + i by omega] at this
  have hA := (nine_black (a + (r - 8)) 1 (fun s hs => by
    have := hblk (r - 8 + s) (by omega) (by omega)
    rwa [show a + (r - 8 + s) = a + (r - 8) + s by omega] at this)).1
  rw [show a + (r - 8) + 9 = a + r + 1 by omega, show (1 : Int) + 1 = 2 by rfl] at hA
  have c1 : cell (a + r + 1) 1 = false := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hb1, hblk r (by omega) (Nat.le_refl r)]
    rfl
  refine ⟨hblk, c1, ?_⟩
  show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = true
  rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, hA]
  rfl

/-- First black cell at column `ℓ + 1 ∈ [r - 6, r + 1]`: the next period's first black cell is in
column 1 or 2. -/
theorem period_late (ℓ : Nat) (hℓ : ℓ ≤ r)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = true ∨ (cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = true) := by
  have hfront := (front_moves a ℓ r hwr hw hb ℓ (by omega) (Nat.le_refl ℓ)).2
  rw [show ℓ - ℓ + 1 = 1 by omega] at hfront
  have hr1 : cell (a + r) 1 = true := by
    have := black_stays (a + ℓ) (r - ℓ) (fun j hj => by
      have := hwr (ℓ + j) (by omega); rwa [show a + (ℓ + j) = a + ℓ + j by omega] at this)
      (by simpa using hfront) (r - ℓ) (Nat.le_refl _)
    rwa [show a + ℓ + (r - ℓ) = a + r by omega] at this
  have c1 : cell (a + r + 1) 1 = false := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hb1, hr1]
    rfl
  cases h2 : cell (a + r + 1) 2
  · left
    show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, h2]
    rfl
  · right
    constructor
    · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
      rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, h2]
      rfl
    · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = true
      rw [show (2 : Int) - 1 = 1 by rfl, c1, h2]
      rfl

omit hb1 hb2 in
/-- The configuration at time `a + r` when the first black cell started at column `r + z + 1`. -/
theorem period_far (z : Nat) (hz : 1 ≤ z)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + z → cell a p = false) (hb : cell a ((r + z + 1 : Nat) : Int) = true) :
    (∀ p : Nat, 1 ≤ p → p ≤ z → cell (a + r) p = false) ∧ cell (a + r) ((z + 1 : Nat) : Int) = true := by
  have := front_moves a (r + z) r hwr hw hb r (Nat.le_refl r) (by omega)
  rw [show r + z - r = z by omega] at this
  exact this

theorem period_z1 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 1 → cell a p = false)
    (hb : cell a ((r + 1 + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = true := by
  obtain ⟨fw, fb⟩ := period_far a r hwr 1 (Nat.le_refl 1) hw hb
  have w1 : cell (a + r) 1 = false := by simpa using fw 1 (Nat.le_refl 1) (Nat.le_refl 1)
  have b2 : cell (a + r) 2 = true := by simpa using fb
  have c1 : cell (a + r + 1) 1 = false := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, b2]; rfl
  have c2 : cell (a + r + 1) 2 = true := by
    show rule (cell (a + r) (2 - 1)) (cell (a + r) 2) (cell (a + r) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, w1, b2]; rfl
  constructor
  · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, c1, c2]; rfl

omit hb2 in
theorem period_z2 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell a p = false)
    (hb : cell a ((r + 2 + 1 : Nat) : Int) = true) :
    (∀ i, i ≤ r → cell (a + i) 1 = false) ∧ cell (a + r + 1) 1 = true := by
  have hw' : ∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell a p = false := hw
  refine ⟨fun i hi => ?_, ?_⟩
  · have := (front_moves a (r + 2) r hwr hw hb i hi (by omega)).1 1 (Nat.le_refl 1) (by omega)
    simpa using this
  · obtain ⟨fw, _⟩ := period_far a r hwr 2 (by omega) hw hb
    have w1 : cell (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
    have w2 : cell (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl

theorem period_z3 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 3 → cell a p = false)
    (hb : cell a ((r + 3 + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = false ∧ cell (a + r + 2) 3 = true := by
  obtain ⟨fw, fb⟩ := period_far a r hwr 3 (by omega) hw hb
  have w1 : cell (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
  have w2 : cell (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
  have w3 : cell (a + r) 3 = false := by simpa using fw 3 (by omega) (by omega)
  have b4 : cell (a + r) 4 = true := by simpa using fb
  have c1 : cell (a + r + 1) 1 = true := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl
  have c2 : cell (a + r + 1) 2 = false := by
    show rule (cell (a + r) (2 - 1)) (cell (a + r) 2) (cell (a + r) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, w1, w2, w3]; rfl
  have c3 : cell (a + r + 1) 3 = true := by
    show rule (cell (a + r) (3 - 1)) (cell (a + r) 3) (cell (a + r) (3 + 1)) = true
    rw [show (3 : Int) - 1 = 2 by rfl, show (3 : Int) + 1 = 4 by rfl, w2, w3, b4]; rfl
  refine ⟨?_, ?_, ?_⟩
  · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, c1, c2, c3]; rfl
  · show rule (cell (a + r + 1) (3 - 1)) (cell (a + r + 1) 3) (cell (a + r + 1) (3 + 1)) = true
    rw [show (3 : Int) - 1 = 2 by rfl, c2, c3]; rfl

theorem period_z4 (z : Nat) (hz : 4 ≤ z) (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + z → cell a p = false)
    (hb : cell a ((r + z + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = true := by
  obtain ⟨fw, _⟩ := period_far a r hwr z (by omega) hw hb
  have w1 : cell (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
  have w2 : cell (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
  have w3 : cell (a + r) 3 = false := by simpa using fw 3 (by omega) (by omega)
  have w4 : cell (a + r) 4 = false := by simpa using fw 4 (by omega) (by omega)
  have c1 : cell (a + r + 1) 1 = true := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl
  have c2 : cell (a + r + 1) 2 = false := by
    show rule (cell (a + r) (2 - 1)) (cell (a + r) 2) (cell (a + r) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, w1, w2, w3]; rfl
  have c3 : cell (a + r + 1) 3 = false := by
    show rule (cell (a + r) (3 - 1)) (cell (a + r) 3) (cell (a + r) (3 + 1)) = false
    rw [show (3 : Int) - 1 = 2 by rfl, show (3 : Int) + 1 = 4 by rfl, w2, w3, w4]; rfl
  constructor
  · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, c1, c2, c3]; rfl

end Period

/-! ### Assembly -/

/-- Column 1 is eventually periodic if it repeats a fixed block from some time on. -/
theorem periodic_blocks (B Q : Nat) (hQ : 0 < Q) (g : Nat → Bool)
    (h : ∀ j i, i < Q → cell (B + j * Q + i) 1 = g i) :
    EventuallyPeriodic (fun t => cell t (0 + 1)) := by
  refine ⟨B, Q, hQ, fun t ht => ?_⟩
  show cell (t + Q) (0 + 1) = cell t (0 + 1)
  rw [show (0 : Int) + 1 = 1 by rfl]
  have hdm := Nat.div_add_mod (t - B) Q
  generalize (t - B) / Q = q at hdm
  have hmod := Nat.mod_lt (t - B) hQ
  generalize (t - B) % Q = s at hdm hmod
  have hq1 : (q + 1) * Q = q * Q + Q := Nat.succ_mul q Q
  have hcomm : Q * q = q * Q := Nat.mul_comm Q q
  have e1 := h q s hmod
  have e2 := h (q + 1) s hmod
  rw [hq1] at e2
  rw [show t + Q = B + (q * Q + Q) + s by omega, e2, ← e1, show B + q * Q + s = t by omega]

/-- **The words `0^r 1 1`, `r ≥ 10`, are excluded**: the center column of rule 30 is not
eventually periodic with repeating word `0^r 1 1`, whatever the transient. -/
theorem no_white_run_11 (T r t0 : Nat) (hr : 10 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 2)) = center t) (ht0 : T ≤ t0)
    (hw : ∀ i, i < r → center (t0 + i) = false) (hb1 : center (t0 + r) = true)
    (hb2 : center (t0 + r + 1) = true) : False := by
  generalize hQdef : r + 2 = Q at hper
  have hQ : 0 < Q := by omega
  have hperk : ∀ k t, T ≤ t → center (t + k * Q) = center t := periodic_mul hper
  -- start one period later so that the start time is ≥ 1
  generalize hAdef : t0 + Q = A
  have hMul : ∀ k, (k + 1) * Q = k * Q + Q := fun k => Nat.succ_mul k Q
  have drvw : ∀ k i, i < r → cell (A + k * Q + i) 0 = false := by
    intro k i hi
    have := hperk (k + 1) (t0 + i) (by omega)
    show center (A + k * Q + i) = false
    rw [hMul k, show t0 + i + (k * Q + Q) = A + k * Q + i by omega] at this
    rw [this]; exact hw i hi
  have drvb1 : ∀ k, cell (A + k * Q + r) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r) (by omega)
    show center (A + k * Q + r) = true
    rw [hMul k, show t0 + r + (k * Q + Q) = A + k * Q + r by omega] at this
    rw [this]; exact hb1
  have drvb2 : ∀ k, cell (A + k * Q + r + 1) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r + 1) (by omega)
    show center (A + k * Q + r + 1) = true
    rw [hMul k, show t0 + r + 1 + (k * Q + Q) = A + k * Q + r + 1 by omega] at this
    rw [this]; exact hb2
  have hnext : ∀ k, A + k * Q + r + 2 = A + (k + 1) * Q := by intro k; rw [hMul k]; omega
  -- a first black cell at column ℓ + 1 ≤ r - 7 locks the next period
  have early : ∀ k ℓ, ℓ ≤ r - 8 → (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell (A + k * Q) p = false) →
      cell (A + k * Q) ((ℓ + 1 : Nat) : Int) = true → cell (A + (k + 1) * Q) 1 = true := by
    intro k ℓ hℓ hwℓ hbℓ
    have := (period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (by omega) ℓ hℓ hwℓ hbℓ).2.2
    rwa [hnext k] at this
  have lock_step : ∀ k, cell (A + k * Q) 1 = true → cell (A + (k + 1) * Q) 1 = true := by
    intro k hk
    exact early k 0 (by omega) (fun p h1 h2 => by omega) (by simpa using hk)
  have lock_all : ∀ k, cell (A + k * Q) 1 = true → ∀ j, cell (A + (k + j) * Q) 1 = true := by
    intro k hk j
    induction j with
    | zero => simpa using hk
    | succ j ih => rw [show k + (j + 1) = (k + j) + 1 by omega]; exact lock_step _ ih
  -- the exceptional case: first black cell exactly at column r + 3
  let Z2 : Nat → Prop := fun k => (∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell (A + k * Q) p = false) ∧
    cell (A + k * Q) ((r + 2 + 1 : Nat) : Int) = true
  have two_lock : ∀ k, ¬ Z2 k → cell (A + (k + 2) * Q) 1 = true := by
    intro k hz
    have hA1 : 1 ≤ A + k * Q := by omega
    obtain ⟨ℓ, hwℓ, hbℓ⟩ := first_black (A + k * Q) hA1
    have via1 : cell (A + (k + 1) * Q) 1 = false → cell (A + (k + 1) * Q) 2 = true →
        cell (A + (k + 2) * Q) 1 = true := by
      intro h1 h2
      have := early (k + 1) 1 (by omega) (fun p hp1 hp2 => by
        have : p = 1 := by omega
        subst this; simpa using h1) (by simpa using h2)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    by_cases c1 : ℓ ≤ r - 8
    · have := lock_step _ (early k ℓ c1 hwℓ hbℓ)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    by_cases c2 : ℓ ≤ r
    · rcases period_late (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) ℓ c2 hwℓ hbℓ with h | ⟨h1, h2⟩
      · rw [hnext k] at h
        have := lock_step _ h
        rwa [show k + 1 + 1 = k + 2 by omega] at this
      · rw [hnext k] at h1 h2
        exact via1 h1 h2
    by_cases c3 : ℓ = r + 1
    · subst c3
      obtain ⟨h1, h2⟩ := period_z1 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2
      exact via1 h1 h2
    by_cases c4 : ℓ = r + 2
    · subst c4
      exact absurd ⟨hwℓ, hbℓ⟩ hz
    by_cases c5 : ℓ = r + 3
    · subst c5
      obtain ⟨h1, h2, h3⟩ := period_z3 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2 h3
      have := early (k + 1) 2 (by omega) (fun p hp1 hp2 => by
        by_cases hp : p = 1
        · subst hp; simpa using h1
        · have : p = 2 := by omega
          subst this; simpa using h2) (by simpa using h3)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    · have hz4 : 4 ≤ ℓ - r := by omega
      obtain ⟨h1, h2⟩ := period_z4 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (ℓ - r) hz4
        (fun p hp1 hp2 => hwℓ p hp1 (by omega)) (by rw [show r + (ℓ - r) + 1 = ℓ + 1 by omega]; exact hbℓ)
      rw [hnext k] at h1 h2
      exact via1 h1 h2
  -- column 1 over one period, in the lock and in the exceptional case
  have lock_pattern : ∀ k, cell (A + k * Q) 1 = true → ∀ i, i < Q →
      cell (A + k * Q + i) 1 = decide (i ≤ r) := by
    intro k hk i hi
    obtain ⟨hblk, c1, _⟩ := period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (by omega) 0
      (by omega) (fun p h1 h2 => by omega) (by simpa using hk)
    by_cases hir : i ≤ r
    · rw [hblk i (by omega) hir]; simp [hir]
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have z2_pattern : ∀ k, Z2 k → ∀ i, i < Q → cell (A + k * Q + i) 1 = decide (i = r + 1) := by
    intro k hk i hi
    obtain ⟨hw0, c1⟩ := period_z2 (A + k * Q) r (drvw k) (drvb1 k) hk.1 hk.2
    by_cases hir : i ≤ r
    · rw [hw0 i hir]; simp; omega
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    by_cases hall : ∀ k, Z2 k
    · exact periodic_blocks A Q hQ (fun i => decide (i = r + 1)) (fun j i hi => z2_pattern j (hall j) i hi)
    · have hex : ∃ k, ¬ Z2 k := Classical.byContradiction fun hne => hall fun k =>
        Classical.byContradiction fun hk => hne ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hex
      have hlock := two_lock k hk
      refine periodic_blocks (A + (k + 2) * Q) Q hQ (fun i => decide (i ≤ r)) (fun j i hi => ?_)
      have := lock_pattern (k + 2 + j) (lock_all (k + 2) hlock j) i hi
      have hm : (k + 2 + j) * Q = (k + 2) * Q + j * Q := Nat.add_mul (k + 2) j Q
      rwa [hm, show A + ((k + 2) * Q + j * Q) + i = A + (k + 2) * Q + j * Q + i by omega] at this
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, Q, hQ, hper⟩
  exact not_adjacent 0 h0 h1

end AbsorbWhite

#print axioms AbsorbWhite.no_white_run_11
#print axioms AbsorbWhite.nine_black
#print axioms Ruliology.CellularAutomata.Rule30Jen.not_adjacent
#check @AbsorbWhite.no_white_run_11
