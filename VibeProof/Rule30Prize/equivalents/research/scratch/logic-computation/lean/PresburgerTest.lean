import Mathlib.ModelTheory.Arithmetic.Presburger.Definability

/-! Scratch check (not part of any library): Problem 1 is equivalent to the set of black times
of the center column not being Presburger-definable, via Mathlib's
`FirstOrder.Language.presburger.definable₁_iff_ultimately_periodic`.
Definitions copied from `Ruliology.CellularAutomata.Rule30Jen` / `Rule30Prize`. -/

namespace R30Test

def rule (a b c : Bool) : Bool := xor a (b || c)

def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

def center (t : Nat) : Bool := cell t 0

def EventuallyPeriodic (f : Nat → Bool) : Prop :=
  ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

def Problem1 : Prop := ¬ EventuallyPeriodic center

/-- For any Boolean sequence: eventual periodicity is ultimate periodicity of its set of `true`
times, in the form used by Mathlib. -/
theorem eventuallyPeriodic_iff_ultimately_periodic (f : Nat → Bool) :
    EventuallyPeriodic f ↔ ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ {t | f t = true} ↔ x + p ∈ {t | f t = true} := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, fun x hx => by simp only [Set.mem_setOf_eq, h x hx]⟩
  · rintro ⟨k, p, hp, h⟩
    refine ⟨k, p, hp, fun t ht => ?_⟩
    have := h t ht
    simp only [Set.mem_setOf_eq] at this
    cases h1 : f t <;> cases h2 : f (t + p) <;> simp_all

open FirstOrder Language in
/-- **Problem 1 ⟺ the black times of the center column are not Presburger-definable**
(with any set of parameters `A`). -/
theorem problem1_iff_not_presburger (A : Set ℕ) :
    Problem1 ↔ ¬ A.Definable₁ presburger {t | center t = true} := by
  rw [presburger.definable₁_iff_ultimately_periodic, Problem1,
    eventuallyPeriodic_iff_ultimately_periodic]

end R30Test

#print axioms R30Test.problem1_iff_not_presburger
