import KC.VTight
open KC.Q01Lanes
-- verifier harness sanity: this one must FAIL (K = D(12) = 30 is not enough)
theorem bogus : check 12 30 6 0 = true := by decide +kernel
#print axioms v20_fail_list
#print axioms v12_fail
