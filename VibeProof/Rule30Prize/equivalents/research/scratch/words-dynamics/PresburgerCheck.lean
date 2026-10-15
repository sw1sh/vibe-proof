import Mathlib.ModelTheory.Arithmetic.Presburger.Definability

/-! Scratch check (words-dynamics agent): Problem 1 is equivalent to the set of black times of
the center column not being Presburger-definable. The definitions of `rule`, `cell`,
`EventuallyPeriodic`, `center` and `Problem1` are copied verbatim from
`Ruliology.CellularAutomata.Rule30Jen` / `Rule30Prize`. -/

namespace Scratch

def rule (a b c : Bool) : Bool := xor a (b || c)

def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

def EventuallyPeriodic (f : Nat → Bool) : Prop := ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

def center (t : Nat) : Bool := cell t 0

def Problem1 : Prop := ¬ EventuallyPeriodic center

/-- For any `f : ℕ → Bool`: not eventually periodic iff the set of times where `f` is `true` is
not Presburger-definable (Mathlib's `definable₁_iff_ultimately_periodic`, Ginsburg–Spanier). -/
theorem not_eventuallyPeriodic_iff_not_definable (f : Nat → Bool) (A : Set ℕ) :
    ¬ EventuallyPeriodic f ↔
      ¬ A.Definable₁ FirstOrder.Language.presburger {t | f t = true} := by
  rw [FirstOrder.Language.presburger.definable₁_iff_ultimately_periodic]
  apply not_congr
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, fun x hx => by simp [h x hx]⟩
  · rintro ⟨k, p, hp, h⟩
    refine ⟨k, p, hp, fun t ht => ?_⟩
    have := h t ht
    simp only [Set.mem_setOf_eq] at this
    cases h1 : f t <;> cases h2 : f (t + p) <;> simp_all

theorem problem1_iff_not_presburger :
    Problem1 ↔ ¬ (∅ : Set ℕ).Definable₁ FirstOrder.Language.presburger {t | center t = true} :=
  not_eventuallyPeriodic_iff_not_definable center ∅

end Scratch

#print axioms Scratch.problem1_iff_not_presburger
