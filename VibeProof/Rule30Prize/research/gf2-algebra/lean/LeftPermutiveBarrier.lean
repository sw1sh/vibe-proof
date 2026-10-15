/-!
# Barrier: left-permutive quiescent rules whose center column is eventually periodic

Rules `90 = l xor r`, `150 = l xor c xor r` and `210 = l xor (!c && r)` have the form
`l xor g(c, r)` with `g(0,0) = 0`, like rule 30 (`g = c || r`). They are left-permutive, their
single-seed light cone grows one cell per step on both sides (so Jen's argument applies to them),
and their right diagonals are periodic with 2-power periods. Yet their single-seed center columns
are eventually periodic. So no proof of the Rule 30 Prize Problem 1 can use only these features.

* `center90`: rule 90's center column is `1, 0, 0, …`.
* `center150`: rule 150's center column is constantly `1`.
* `cell210_eq_cell90`: rule 210's single-seed pattern equals rule 90's.
-/

namespace LeftPermutiveBarrier

/-- Rule 90 from a single black cell. -/
def cell90 : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => xor (cell90 t (p - 1)) (cell90 t (p + 1))

/-- Rule 150 from a single black cell. -/
def cell150 : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => xor (xor (cell150 t (p - 1)) (cell150 t p)) (cell150 t (p + 1))

/-- Rule 210 (`l xor (!c && r)`) from a single black cell. -/
def cell210 : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => xor (cell210 t (p - 1)) (!cell210 t p && cell210 t (p + 1))

theorem nat_parity (t : Nat) : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩

theorem cell90_congr {t : Nat} {p q : Int} (h : p = q) : cell90 t p = cell90 t q := h ▸ rfl
theorem cell150_congr {t : Nat} {p q : Int} (h : p = q) : cell150 t p = cell150 t q := h ▸ rfl

/-! ### Rule 90 -/

/-- Rule 90's pattern lives on the sublattice `t + p` even. -/
theorem cell90_odd : ∀ (t : Nat) (p : Int), ((t : Int) + p) % 2 = 1 → cell90 t p = false
  | 0, p, h => by simp [cell90]; omega
  | t + 1, p, h => by
    show xor (cell90 t (p - 1)) (cell90 t (p + 1)) = false
    rw [cell90_odd t (p - 1) (by omega), cell90_odd t (p + 1) (by omega)]; rfl

theorem cell90_two (t : Nat) (p : Int) :
    cell90 (t + 2) p = xor (cell90 t (p - 2)) (cell90 t (p + 2)) := by
  show xor (xor (cell90 t (p - 1 - 1)) (cell90 t (p - 1 + 1)))
      (xor (cell90 t (p + 1 - 1)) (cell90 t (p + 1 + 1))) = _
  rw [cell90_congr (show p - 1 - 1 = p - 2 by omega), cell90_congr (show p - 1 + 1 = p by omega),
    cell90_congr (show p + 1 - 1 = p by omega), cell90_congr (show p + 1 + 1 = p + 2 by omega)]
  cases cell90 t (p - 2) <;> cases cell90 t p <;> cases cell90 t (p + 2) <;> rfl

/-- Frobenius self-similarity of rule 90. -/
theorem cell90_double : ∀ (t : Nat) (p : Int), cell90 (2 * t) (2 * p) = cell90 t p
  | 0, p => by simp [cell90]; omega
  | t + 1, p => by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, cell90_two,
      cell90_congr (show 2 * p - 2 = 2 * (p - 1) by omega),
      cell90_congr (show 2 * p + 2 = 2 * (p + 1) by omega), cell90_double t (p - 1),
      cell90_double t (p + 1)]
    rfl

/-- **Rule 90's center column is `1, 0, 0, …`.** -/
theorem center90 : ∀ t : Nat, 1 ≤ t → cell90 t 0 = false := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    rcases nat_parity t with ⟨s, rfl | rfl⟩
    · have h := cell90_double s 0
      rw [show (2 : Int) * 0 = 0 by rfl] at h
      rw [h]; exact ih s (by omega) (by omega)
    · exact cell90_odd _ _ (by omega)

/-! ### Rule 150 -/

theorem cell150_two (t : Nat) (p : Int) :
    cell150 (t + 2) p = xor (xor (cell150 t (p - 2)) (cell150 t p)) (cell150 t (p + 2)) := by
  show xor (xor (xor (xor (cell150 t (p - 1 - 1)) (cell150 t (p - 1))) (cell150 t (p - 1 + 1)))
      (xor (xor (cell150 t (p - 1)) (cell150 t p)) (cell150 t (p + 1))))
      (xor (xor (cell150 t (p + 1 - 1)) (cell150 t (p + 1))) (cell150 t (p + 1 + 1))) = _
  rw [cell150_congr (show p - 1 - 1 = p - 2 by omega), cell150_congr (show p - 1 + 1 = p by omega),
    cell150_congr (show p + 1 - 1 = p by omega), cell150_congr (show p + 1 + 1 = p + 2 by omega)]
  cases cell150 t (p - 2) <;> cases cell150 t (p - 1) <;> cases cell150 t p <;>
    cases cell150 t (p + 1) <;> cases cell150 t (p + 2) <;> rfl

/-- Frobenius self-similarity of rule 150: at even times only even positions are black, and they
repeat the pattern at half the time. -/
theorem cell150_double : ∀ (t : Nat) (p : Int),
    cell150 (2 * t) (2 * p) = cell150 t p ∧ cell150 (2 * t) (2 * p + 1) = false
  | 0, p => by constructor <;> (simp [cell150]; omega)
  | t + 1, p => by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, cell150_two, cell150_two]
    constructor
    · rw [cell150_congr (show 2 * p - 2 = 2 * (p - 1) by omega),
        cell150_congr (show 2 * p + 2 = 2 * (p + 1) by omega), (cell150_double t (p - 1)).1,
        (cell150_double t p).1, (cell150_double t (p + 1)).1]
      rfl
    · rw [cell150_congr (show 2 * p + 1 - 2 = 2 * (p - 1) + 1 by omega),
        cell150_congr (show 2 * p + 1 + 2 = 2 * (p + 1) + 1 by omega), (cell150_double t (p - 1)).2,
        (cell150_double t p).2, (cell150_double t (p + 1)).2]
      rfl

/-- **Rule 150's center column is constantly black** (central trinomial coefficients are odd). -/
theorem center150 : ∀ t : Nat, cell150 t 0 = true := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    rcases nat_parity t with ⟨s, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos s with rfl | hs
      · rfl
      · have h := (cell150_double s 0).1
        rw [show (2 : Int) * 0 = 0 by rfl] at h
        rw [h]; exact ih s (by omega)
    · show xor (xor (cell150 (2 * s) (0 - 1)) (cell150 (2 * s) 0)) (cell150 (2 * s) (0 + 1)) = true
      rw [cell150_congr (show (0 : Int) - 1 = 2 * (-1) + 1 by omega),
        cell150_congr (show (0 : Int) + 1 = 2 * 0 + 1 by omega), (cell150_double s (-1)).2,
        (cell150_double s 0).2]
      have h := (cell150_double s 0).1
      rw [show (2 : Int) * 0 = 0 by rfl] at h
      rw [h]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · rfl
      · rw [ih s (by omega)]; rfl

/-! ### Rule 210 -/

/-- **Rule 210's single-seed pattern is rule 90's**: the two rules differ only when the center and
right cells are both black, which never happens on rule 90's checkerboard sublattice. -/
theorem cell210_eq_cell90 : ∀ (t : Nat) (p : Int), cell210 t p = cell90 t p
  | 0, p => rfl
  | t + 1, p => by
    show xor (cell210 t (p - 1)) (!cell210 t p && cell210 t (p + 1)) =
      xor (cell90 t (p - 1)) (cell90 t (p + 1))
    rw [cell210_eq_cell90 t (p - 1), cell210_eq_cell90 t p, cell210_eq_cell90 t (p + 1)]
    rcases (show ((t : Int) + p) % 2 = 0 ∨ ((t : Int) + p) % 2 = 1 by omega) with h | h
    · rw [cell90_odd t (p + 1) (by omega)]; cases cell90 t p <;> rfl
    · rw [cell90_odd t p h]; cases cell90 t (p + 1) <;> rfl

theorem center210 (t : Nat) (ht : 1 ≤ t) : cell210 t 0 = false := by
  rw [cell210_eq_cell90]; exact center90 t ht

end LeftPermutiveBarrier
