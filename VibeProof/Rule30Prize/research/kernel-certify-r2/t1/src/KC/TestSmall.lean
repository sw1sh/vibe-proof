import KC.Q01Lanes
open KC.Q01Lanes Ruliology.CellularAutomata Rule30ZeroBoundary

theorem c0 : check 20 39 8 0 = true := by decide +kernel
theorem c1 : check 20 39 8 1 = true := by decide +kernel
theorem c2 : check 20 39 8 2 = true := by decide +kernel
theorem c3 : check 20 39 8 3 = true := by decide +kernel

theorem w20 (x : Nat → Bool) (hx : ∀ k, 20 < k → x k = false) :
    ∃ t, t < 39 ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  refine q01_of_checks 20 39 8 (by decide) (fun c hc => ?_) x hx
  have : c < 4 := by simpa using hc
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  · exact c0
  · exact c1
  · exact c2
  · exact c3

#print axioms w20
