import Ruliology

/-! Independent check for claim B (right-edge odometer), step "E_J → ∞":
the right diagonal `R (2k)` is zero before time `k` and black at time `k` (left edge), so no
period `P` of `R (2k)` satisfies `P ≤ k`. Uses only `cell_eq_false_of_lt` and `cell_left_edge`. -/

open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals

theorem R_even_at_half (k : Nat) : R (2 * k) k = true := by
  unfold R
  have h : ((k : Nat) : Int) - ((2 * k : Nat) : Int) = -((k : Nat) : Int) := by omega
  rw [h]
  exact cell_left_edge k

theorem R_even_zero_before (k t : Nat) (ht : t < k) : R (2 * k) t = false := by
  unfold R
  apply cell_eq_false_of_lt
  omega

/-- Every period of the diagonal `R (2k)` exceeds `k`. -/
theorem R_even_period_gt (k P : Nat) (hP : 0 < P)
    (h : ∀ t, R (2 * k) (t + P) = R (2 * k) t) : k < P := by
  match Nat.lt_or_ge k P with
  | .inl hlt => exact hlt
  | .inr hge =>
    have e := h (k - P)
    rw [show k - P + P = k by omega, R_even_at_half, R_even_zero_before k (k - P) (by omega)] at e
    exact absurd e (by decide)

/-- Hence the diagonals' periods are unbounded: no single `2^E` is a period of every `R j`. -/
theorem no_uniform_pow2_period (E : Nat) : ¬ ∀ j t, R j (t + 2 ^ E) = R j t := by
  intro h
  have := R_even_period_gt (2 ^ E) (2 ^ E) (Nat.two_pow_pos E) (h (2 * 2 ^ E))
  omega

#print axioms no_uniform_pow2_period
