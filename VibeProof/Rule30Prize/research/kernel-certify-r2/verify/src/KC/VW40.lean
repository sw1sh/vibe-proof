import KC.Q01Lanes
open KC.Q01Lanes
-- verifier: W = 40 as a single chunk (2^20 lanes), K = D(40) + 1 = 77
theorem w40_one_chunk : check 40 77 20 0 = true := by decide +kernel
