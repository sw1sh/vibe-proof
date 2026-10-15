import KC.Q01Lanes
open KC.Q01Lanes
-- verifier: D(26) = 44, D(31) = 66, D(40) = 76 (round-2 table) pinned by the kernel checker
theorem v26_pass : check 26 45 13 0 = true := by decide +kernel
theorem v26_fail : check 26 44 13 0 = false := by decide +kernel
theorem v31_pass : check 31 67 15 0 = true := by decide +kernel
theorem v31_fail : check 31 66 15 0 = false := by decide +kernel
theorem v40_pass : check 40 77 18 0 = true ∧ check 40 77 18 1 = true ∧ check 40 77 18 2 = true ∧ check 40 77 18 3 = true := by decide +kernel
theorem v40_fail : [check 40 76 18 0, check 40 76 18 1, check 40 76 18 2, check 40 76 18 3].any (· == false) = true := by decide +kernel
