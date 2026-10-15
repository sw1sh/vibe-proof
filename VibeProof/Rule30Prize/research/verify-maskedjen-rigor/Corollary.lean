import Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Jen

/-- Re-proved here independently (not reusing R30NewIdeas): masked Jen. -/
theorem mj (i : Int) {T Q : Nat} (hQ : 0 < Q)
    (h0 : ∀ t, T ≤ t → cell (t + Q) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell t i = false → cell (t + Q) (i + 1) = cell t (i + 1)) : False := by
  apply not_adjacent (i - 1)
  · refine ⟨T, Q, hQ, fun t ht => ?_⟩
    have a := cell_left (t + Q) i
    have b := cell_left t i
    have e1 := h0 (t + 1) (by omega)
    have e2 := h0 t ht
    rw [show t + Q + 1 = t + 1 + Q by omega, e1, e2] at a
    show cell (t + Q) (i - 1) = cell t (i - 1)
    rw [a, b]
    cases hc : cell t i
    · rw [h1 t ht hc]
    · rfl
  · refine ⟨T, Q, hQ, ?_⟩
    rw [show i - 1 + 1 = i by omega]; exact h0

/-- English corollary: if c is eventually P-periodic (from T0), then for every multiple Q = k*P (k > 0)
and every start T, column 1 restricted to the white times of c is not Q-periodic from T. -/
theorem center_white_not_periodic_multiple {T0 P : Nat} (hc : ∀ t, T0 ≤ t → cell (t + P) 0 = cell t 0)
    (k : Nat) (hkP : 0 < k * P) (T : Nat)
    (h1 : ∀ t, T ≤ t → cell t 0 = false → cell (t + k * P) 1 = cell t 1) : False :=
  mj 0 (T := max T T0) hkP
    (fun t ht => periodic_mul (f := fun t => cell t 0) hc k t (by omega))
    (fun t ht hw => by simpa using h1 t (by omega) hw)

/-- c(t) = 1 → cell(t,-1) = ¬ c(t+1), by direct computation from the definition. -/
theorem lbc (t : Nat) (h : cell t 0 = true) : cell t (-1) = !cell (t + 1) 0 := by
  show cell t (-1) = !(rule (cell t (0 - 1)) (cell t 0) (cell t (0 + 1)))
  simp only [rule, h, Bool.true_or]
  rw [show (0 : Int) - 1 = -1 by rfl]
  cases cell t (-1) <;> rfl

#print axioms mj
#print axioms center_white_not_periodic_multiple
#print axioms lbc
