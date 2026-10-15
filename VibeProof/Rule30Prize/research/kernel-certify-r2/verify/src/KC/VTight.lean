import KC.Q01Lanes
open KC.Q01Lanes
-- verifier: tightness probes of the lane checker against brute-force D(12) = 30, D(20) = 38
theorem v12_pass : check 12 31 6 0 = true := by decide +kernel
theorem v12_fail : check 12 30 6 0 = false := by decide +kernel
theorem v20_pass0 : check 20 39 8 0 = true := by decide +kernel
theorem v20_pass1 : check 20 39 8 1 = true := by decide +kernel
theorem v20_pass2 : check 20 39 8 2 = true := by decide +kernel
theorem v20_pass3 : check 20 39 8 3 = true := by decide +kernel
theorem v20_fail_list : [check 20 38 8 0, check 20 38 8 1, check 20 38 8 2, check 20 38 8 3].any (· == false) = true := by decide +kernel
-- one level fewer at W = 11 (D(11) = 30, the 2W+8 equality case): n = 5 = W/2
theorem v11_pass : check 11 31 5 0 = true := by decide +kernel
theorem v11_fail : check 11 30 5 0 = false := by decide +kernel
