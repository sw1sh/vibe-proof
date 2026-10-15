import Ruliology.CellularAutomata.Rule30Jen

/-!
# Rule 135's center column is rule 30's column `-1`, complemented and delayed

Rule 135 (`!l xor (c && r)`) is the black-white conjugate of rule 30: complementing every cell
turns one rule into the other. From one black cell, rule 30 applied to the complemented seed
(all black except the origin) gives a single black cell at position `1` after one step. So rule
135's single-seed pattern is rule 30's, shifted one step in time and one cell in space, then
complemented:

* `cell135_succ`: `cell135 (t + 1) p = !cell t (p - 1)`.
* `center135_succ`: rule 135's center column at time `t + 1` is `!cell t (-1)`.
* `problem1_30_or_135`: by Jen's theorem (columns `0` and `-1` of rule 30 are not both eventually
  periodic), **the single-seed center column of rule 30 or that of rule 135 is not eventually
  periodic.** (Rule 149, the mirror image of rule 135, has the same center column as rule 135;
  rule 86, the mirror image of rule 30, has the same center column as rule 30.)
-/

namespace Ruliology.CellularAutomata
namespace Rule135Center

open Rule30Jen

/-- Rule 135: `!left xor (center && right)`. -/
def rule135 (a b c : Bool) : Bool := xor (!a) (b && c)

/-- Rule 135 from a single black cell at position `0`. -/
def cell135 : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule135 (cell135 t (p - 1)) (cell135 t p) (cell135 t (p + 1))

theorem cell_congr' {t : Nat} {p q : Int} (h : p = q) : cell t p = cell t q := h ▸ rfl

theorem cell135_succ : ∀ (t : Nat) (p : Int), cell135 (t + 1) p = !cell t (p - 1)
  | 0, p => by
    show rule135 (decide (p - 1 = 0)) (decide (p = 0)) (decide (p + 1 = 0)) = !decide (p - 1 = 0)
    rcases (show p = 1 ∨ p = 0 ∨ p = -1 ∨ (p ≠ 1 ∧ p ≠ 0 ∧ p ≠ -1) by omega) with
      h | h | h | ⟨h1, h2, h3⟩
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · have e1 : decide (p - 1 = 0) = false := decide_eq_false (by omega)
      have e2 : decide (p = 0) = false := decide_eq_false (by omega)
      have e3 : decide (p + 1 = 0) = false := decide_eq_false (by omega)
      rw [e1, e2, e3]; rfl
  | t + 1, p => by
    show rule135 (cell135 (t + 1) (p - 1)) (cell135 (t + 1) p) (cell135 (t + 1) (p + 1)) =
      !rule (cell t (p - 1 - 1)) (cell t (p - 1)) (cell t (p - 1 + 1))
    rw [cell135_succ t (p - 1), cell135_succ t p, cell135_succ t (p + 1),
      cell_congr' (show p + 1 - 1 = p by omega), cell_congr' (show p - 1 + 1 = p by omega)]
    cases cell t (p - 1 - 1) <;> cases cell t (p - 1) <;> cases cell t p <;> rfl

theorem center135_succ (t : Nat) : cell135 (t + 1) 0 = !cell t (-1) := by
  rw [cell135_succ]; rfl

/-- **The single-seed center columns of rule 30 and rule 135 are not both eventually
periodic.** -/
theorem problem1_30_or_135 :
    ¬ (EventuallyPeriodic (fun t => cell t 0) ∧ EventuallyPeriodic (fun t => cell135 t 0)) := by
  rintro ⟨h30, ⟨T, P, hP, h135⟩⟩
  have hm1 : EventuallyPeriodic (fun t => cell t (-1)) := by
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have e : cell135 ((t + P) + 1) 0 = cell135 (t + 1) 0 := by
      have h := h135 (t + 1) (by omega)
      simp only [] at h
      rw [show t + 1 + P = (t + P) + 1 by omega] at h
      exact h
    rw [center135_succ, center135_succ] at e
    show cell (t + P) (-1) = cell t (-1)
    revert e
    cases cell (t + P) (-1) <;> cases cell t (-1) <;> simp
  exact jen 0 (-1) (by omega) ⟨h30, hm1⟩


/-! ### The same statement inside rule 30: a single white cell on a black background -/

/-- Rule 30 from a single white cell at `0` on an all-black background. -/
def cellW : Nat → Int → Bool
  | 0, p => !decide (p = 0)
  | t + 1, p => rule (cellW t (p - 1)) (cellW t p) (cellW t (p + 1))

/-- After one step the white seed has become a single black cell at position `1`. -/
theorem cellW_succ : ∀ (t : Nat) (p : Int), cellW (t + 1) p = cell t (p - 1)
  | 0, p => by
    show rule (!decide (p - 1 = 0)) (!decide (p = 0)) (!decide (p + 1 = 0)) = decide (p - 1 = 0)
    rcases (show p = 1 ∨ p = 0 ∨ p = -1 ∨ (p ≠ 1 ∧ p ≠ 0 ∧ p ≠ -1) by omega) with
      h | h | h | ⟨h1, h2, h3⟩
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · have e1 : decide (p - 1 = 0) = false := decide_eq_false (by omega)
      have e2 : decide (p = 0) = false := decide_eq_false (by omega)
      have e3 : decide (p + 1 = 0) = false := decide_eq_false (by omega)
      rw [e1, e2, e3]; rfl
  | t + 1, p => by
    show rule (cellW (t + 1) (p - 1)) (cellW (t + 1) p) (cellW (t + 1) (p + 1)) =
      rule (cell t (p - 1 - 1)) (cell t (p - 1)) (cell t (p - 1 + 1))
    rw [cellW_succ t (p - 1), cellW_succ t p, cellW_succ t (p + 1),
      cell_congr' (show p + 1 - 1 = p by omega), cell_congr' (show p - 1 + 1 = p by omega)]

/-- **Rule 30's center column is not eventually periodic from a single black cell, or from a
single white cell on a black background (or both).** The white-seed center column is column `-1`
of the black-seed pattern, delayed one step; Jen's theorem forbids columns `0` and `-1` from both
being eventually periodic. -/
theorem problem1_black_or_white :
    ¬ (EventuallyPeriodic (fun t => cell t 0) ∧ EventuallyPeriodic (fun t => cellW t 0)) := by
  rintro ⟨h30, ⟨T, P, hP, hW⟩⟩
  have hm1 : EventuallyPeriodic (fun t => cell t (-1)) := by
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have h := hW (t + 1) (by omega)
    simp only [] at h
    rw [show t + 1 + P = (t + P) + 1 by omega, cellW_succ, cellW_succ] at h
    exact h
  exact jen 0 (-1) (by omega) ⟨h30, hm1⟩

end Rule135Center
end Ruliology.CellularAutomata
